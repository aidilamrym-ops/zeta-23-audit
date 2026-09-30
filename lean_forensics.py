#!/usr/bin/env python3
"""Static forensic audit of the Anthropic zeta-23 Lean 4 project (read-only).

Default target: upstream/zeta-23-lean/zeta23 -- a self-contained Lake project
whose repo README claims, verbatim:

  * "A project passes when `lake build` succeeds on its pinned toolchain with
     no `sorry` outside the trusted comparator statement files
     (Challenge.lean, Challenge/<Topic>.lean)";
  * the comparator "checks statement equality, that only the axioms
     propext, Classical.choice, Quot.sound are used, and replays the proofs
     through the kernel" (Challenge.lean header).

This tool NEVER invokes a Lean toolchain (no install, no build): it is a
static text audit plus an independent numerical audit of the constants that
Challenge.lean's own comments document.  What static analysis can and cannot
establish is stated in the project README (metaprogramming, string literals
containing code, and proof-term validity all require a kernel run).

Checks
  Z1  zone-aware sorry/admit scan.  Lean comments (nested /- -/, docstrings
      /-- -/, -- line comments) are blanked out BEFORE token search, because
      the Challenge module's own prose mentions the word "sorry".
      Zones follow the CI rule: statement zone = Challenge.lean + Challenge/**;
      every other .lean file under the target is proof zone.
  Z2  project-declared `axiom` inventory vs comparator permitted_axioms.
  Z3  trust-caveat tokens (native_decide / unsafe) -- reported, flagged.
  Z4  comparator consistency: each theorem name is declared in the statement
      zone AND proved somewhere in the proof zone.
  Z5  statement extraction: the bound constant of every Challenge theorem
      (2/3, 5/6, 2 - 1/cMT, 3/2 - cMT^-1/2) -- the "does it really state
      >= 67.2%" question, answered from the text of the statements.
  Z6  numerical audit of cMT with mpmath (50 dps): the documented decimals,
      the two closed-form identities written in the comments, the headline
      arithmetic 2 - 1/cMT > 2/3, and consistency with the published 67.2%.

Exit codes:
  0  scan completed, no finding contradicts the upstream claims
  1  findings present (see report)
  2  self-test / tool failure (audit untrusted)
"""

import argparse
import json
import os
import re
import sys
import time
from fractions import Fraction

__version__ = "1.0.0"

SOURCES = {
    "upstream": "https://github.com/anthropics/zeta-23-lean",
    "anthropic_post": "https://www.anthropic.com/research/riemann-zeta",
    "paper_via_readme": "arXiv:2608.13637 (Alpoge-Furman, per zeta23 README)",
}

DEFAULT_ROOT = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "upstream", "zeta-23-lean", "zeta23")
DEFAULT_OUT = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "results", "forensics_report.json")

TOKEN_RE = re.compile(r"\b(sorry|admit|admitted|native_decide|unsafe)\b")
AXIOM_RE = re.compile(r"(?m)^[ \t]*axioms?[ \t]+([^\s(:=]+)")
DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|scoped[ \t]+)*"
    r"(theorem|lemma|def|abbrev|instance|example)\s+([A-Za-z_][\w']*)")
THM_RE = re.compile(r"(?m)^[ \t]*theorem\s+([A-Za-z_][\w']*)")
BOUND_RE = re.compile(r"\(([^()]+?) - ε\)")

PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


# ---------------------------------------------------------------------------
# Comment stripping (positions preserved, nested block comments, strings)
# ---------------------------------------------------------------------------

_CHAR_LIT_RE = re.compile(r"'(?:[^'\\]|\\.)'")


def strip_lean_comments(src):
    """Blank out Lean comments in place (offsets and newlines preserved).

    Handled: nested /- -/ block comments, /-- -/ docstrings (they start with
    /-), -- line comments, and string/char literals (copied verbatim so a
    "--" inside a string does not swallow code).
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0:
            m = _CHAR_LIT_RE.match(src, i)
            if m:
                i = m.end()
                continue
            if src.startswith('"', i):
                j = i + 1
                while j < n:
                    if src[j] == "\\":
                        j += 2
                        continue
                    if src[j] == '"':
                        break
                    j += 1
                i = j + 1
                continue
            if src.startswith("--", i):
                j = src.find("\n", i)
                end = n if j < 0 else j
                for k in range(i, end):
                    out[k] = " "
                i = end
                continue
            if src.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth = 1
                i += 2
                continue
            i += 1
            continue
        # inside a block comment
        if src.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i):
            out[i] = out[i + 1] = " "
            depth -= 1
            i += 2
            continue
        if src[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def zone_of(rel_path):
    """CI rule: statement zone = Challenge.lean + Challenge/**, else proof."""
    p = rel_path.replace("\\", "/")
    if p == "Challenge.lean" or p.startswith("Challenge/"):
        return "statement"
    return "proof"


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def enclosing_decl(text, pos):
    """Last declaration (kind, name) starting at or before pos."""
    best = None
    for m in DECL_RE.finditer(text, 0, pos + 1):
        best = (m.group(1), m.group(2))
    return best


# ---------------------------------------------------------------------------
# Scans
# ---------------------------------------------------------------------------

def scan_file(path, rel):
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    stripped = strip_lean_comments(raw)
    zone = zone_of(rel)
    findings = []
    tokens = []
    for m in TOKEN_RE.finditer(stripped):
        tok = m.group(1)
        decl = enclosing_decl(stripped, m.start())
        tokens.append({
            "token": tok,
            "line": line_of(stripped, m.start()),
            "decl_kind": decl[0] if decl else None,
            "decl_name": decl[1] if decl else None,
        })
    axioms = [m.group(1) for m in AXIOM_RE.finditer(stripped)]
    theorems = []
    for m in THM_RE.finditer(stripped):
        name = m.group(1)
        eq = stripped.find(":=", m.end())
        stmt = stripped[m.end():eq] if eq > 0 else stripped[m.end():]
        bound = BOUND_RE.search(stmt)
        theorems.append({
            "name": name,
            "line": line_of(stripped, m.start()),
            "bound": re.sub(r"\s+", " ", bound.group(1)).strip() if bound else None,
        })
    return {
        "file": rel.replace("\\", "/"),
        "zone": zone,
        "tokens": tokens,
        "axioms": axioms,
        "theorems": theorems,
        "lines": raw.count("\n") + 1,
    }


def read_git_commit(root):
    """Best-effort: resolve .git/HEAD walking up from root."""
    d = os.path.abspath(root)
    while True:
        gitdir = os.path.join(d, ".git")
        if os.path.isdir(gitdir):
            break
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent
    else:
        return None
    try:
        head_path = os.path.join(gitdir, "HEAD")
        with open(head_path, encoding="utf-8") as fh:
            head = fh.read().strip()
        if not head.startswith("ref:"):
            return head
        ref = head.split(":", 1)[1].strip()
        ref_path = os.path.join(gitdir, ref.replace("/", os.sep))
        if os.path.exists(ref_path):
            with open(ref_path, encoding="utf-8") as fh:
                return fh.read().strip()
        packed = os.path.join(gitdir, "packed-refs")
        if os.path.exists(packed):
            with open(packed, encoding="utf-8") as fh:
                for line in fh:
                    if line.rstrip().endswith(" " + ref):
                        return line.split()[0]
    except Exception:
        return None
    return None


def prefix_interval_ok(value, prefix_str):
    """Truncation-prefix semantics for documented decimals.

    A comment writing '0.7532960...' claims the value lies in the interval
    [0.7532960, 0.7532960 + 1e-7) -- truncation, not rounding.  Returns
    (ok, diff, tol); caller must be inside mp.workdps.
    """
    import mpmath as mp
    prefix = mp.mpf(prefix_str)
    dp = len(prefix_str.split(".")[1]) if "." in prefix_str else 0
    tol = mp.mpf(10) ** (-dp)
    diff = value - prefix
    return (diff >= 0 and diff < tol), diff, tol


def numeric_audit():
    """Independent check of the cMT decimals/identities documented in
    Challenge.lean, and of the 67.2% headline arithmetic."""
    import mpmath as mp

    results = []

    def check(label, ok, detail):
        results.append({"check": label, "ok": bool(ok), "detail": detail})

    with mp.workdps(50):
        t = mp.tan(1 / mp.sqrt(2))                     # tan(1/sqrt2)
        c = mp.sqrt(2) * t / (1 + t / mp.sqrt(2))      # cMT closed form
        inv = 1 / c
        ident_inv = mp.mpf(1) / 2 + 1 / (mp.sqrt(2) * t)   # 1/2 + cot(1/sqrt2)/sqrt2
        two_minus = 2 - inv
        ident_two_minus = mp.mpf(3) / 2 - 1 / (mp.sqrt(2) * t)
        distinct = (3 - inv) / 2

        # Documented decimals use an ellipsis ("0.7532960..."), i.e.
        # truncation-prefix claims: value must lie in [prefix, prefix+1e-7).
        ok_c, _d, _t = prefix_interval_ok(c, "0.7532960")
        check("cMT in documented truncation interval [0.7532960, +1e-7)",
              ok_c, mp.nstr(c, 14))
        check("identity 1/cMT == 1/2 + cot(1/sqrt2)/sqrt2",
              abs(inv - ident_inv) < mp.mpf("1e-40"),
              "max-diff < 1e-40, 1/cMT = " + mp.nstr(inv, 14))
        check("identity 2-1/cMT == 3/2 - cot(1/sqrt2)/sqrt2",
              abs(two_minus - ident_two_minus) < mp.mpf("1e-40"),
              mp.nstr(two_minus, 14))
        alt_c = 2 * t / (mp.sqrt(2) + t)
        check("identity cMT == 2*tan(1/sqrt2)/(sqrt2 + tan(1/sqrt2))",
              abs(c - alt_c) < mp.mpf("1e-40"), mp.nstr(c, 14))
        ok_tm, _d, _t = prefix_interval_ok(two_minus, "0.67250")
        check("2-1/cMT in documented truncation interval [0.67250, +1e-5)",
              ok_tm, mp.nstr(two_minus, 14))
        ok_ds, _d, _t = prefix_interval_ok(distinct, "0.83625")
        check("(3-1/cMT)/2 in documented truncation interval [0.83625, +1e-5)",
              ok_ds, mp.nstr(distinct, 14))
        margin = two_minus - mp.mpf(2) / 3
        check("headline: 2-1/cMT > 2/3 (more than two thirds)",
              margin > 0,
              "margin = " + mp.nstr(margin, 10))
        pct = 100 * two_minus
        check("headline consistent with published 67.2% "
              "(67.2 <= 100*(2-1/cMT) < 67.3)",
              mp.mpf("67.2") <= pct < mp.mpf("67.3"),
              mp.nstr(pct, 12) + "%")

        # Cross-checks tying the published numbers together: arXiv:2608.13637
        # abstract ("previous unconditional records are 5/12 and 0.6603 ...
        # constants become 0.6725 and 0.8362") and the Anthropic research
        # post ("from 41.6% to 67.2%").
        ok_p67, _d, _t = prefix_interval_ok(two_minus, "0.6725")
        check("paper MT constant 0.6725 (truncation interval)",
              ok_p67, mp.nstr(two_minus, 14))
        ok_p83, _d, _t = prefix_interval_ok(distinct, "0.8362")
        check("paper MT constant 0.8362 (truncation interval)",
              ok_p83, mp.nstr(distinct, 14))
        prev_simple = 100 * mp.mpf(5) / 12
        check("prior record 5/12 reconciles with blog's 41.6% "
              "(41.6 <= x < 41.7, truncation to 1 dp)",
              mp.mpf("41.6") <= prev_simple < mp.mpf("41.7"),
              mp.nstr(prev_simple, 12) + "%")
        check("prior distinct record 0.6603 beaten by 5/6",
              mp.mpf(5) / 6 > mp.mpf("0.6603"),
              "5/6 - 0.6603 = "
              + mp.nstr(mp.mpf(5) / 6 - mp.mpf("0.6603"), 10))
        values = {
            "cMT": mp.nstr(c, 20),
            "inv_cMT": mp.nstr(inv, 20),
            "two_minus_inv_cMT": mp.nstr(two_minus, 20),
            "distinct_bound": mp.nstr(distinct, 20),
            "margin_over_two_thirds": mp.nstr(margin, 20),
        }
    return results, values


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def run_selftest():
    checks = []

    def ck(name, cond):
        checks.append((name, bool(cond)))

    # -- comment stripper ------------------------------------------------
    s = strip_lean_comments("foo /- sorry -/ bar")
    ck("block_comment_sorry_removed", "sorry" not in s)
    s = strip_lean_comments("foo /- a /- sorry -/ b -/ sorry")
    ck("nested_comment_inner_removed", s.count("sorry") == 1)
    s = strip_lean_comments("x := 1 -- sorry")
    ck("line_comment_sorry_removed", "sorry" not in s)
    s = strip_lean_comments("/-- docstring sorry -/ def f := 1")
    ck("docstring_sorry_removed", "sorry" not in s)
    s = strip_lean_comments('def s := "a -- b /- c -/" ++ t')
    ck("string_content_preserved", '"a -- b /- c -/"' in s)
    s = strip_lean_comments("def c := 'x' ++ sorry")
    ck("char_literal_not_string_open", s.count("sorry") == 1)
    orig = "/- a\nb -/\nsorry"
    ck("newlines_preserved",
       strip_lean_comments(orig).count("\n") == orig.count("\n"))
    ck("real_sorry_survives", "sorry" in strip_lean_comments("theorem t : P := by\n  sorry"))

    # -- zones -----------------------------------------------------------
    ck("zone_challenge_root", zone_of("Challenge.lean") == "statement")
    ck("zone_challenge_sub", zone_of("Challenge/Topic.lean") == "statement")
    ck("zone_challengedeps", zone_of("ChallengeDeps.lean") == "proof")
    ck("zone_solution", zone_of("Solution.lean") == "proof")
    ck("zone_library", zone_of("Zeta23/Deep.lean") == "proof")

    # -- declaration context ---------------------------------------------
    src = ("def poisoned : ℕ := sorry\n"
           "theorem ok : True := by sorry\n")
    toks = [t for t in TOKEN_RE.finditer(strip_lean_comments(src))]
    ck("token_scan_two_hits", len(toks) == 2)
    d0 = enclosing_decl(strip_lean_comments(src), toks[0].start())
    d1 = enclosing_decl(strip_lean_comments(src), toks[1].start())
    ck("enclosing_decl_def", d0 == ("def", "poisoned"))
    ck("enclosing_decl_theorem", d1 == ("theorem", "ok"))

    # -- theorem extraction ----------------------------------------------
    src = ("theorem two_thirds_on_critical_line\n"
           "    {q : ℕ} (chi : X) :\n"
           "    forall e > 0, exists T, (2 / 3 - \u03b5) * (N T) <= M := by\n"
           "  sorry\n")
    st = strip_lean_comments(src)
    m = THM_RE.search(st)
    ck("thm_name", m and m.group(1) == "two_thirds_on_critical_line")
    eq = st.find(":=", m.end())
    stmt = st[m.end():eq]
    b = BOUND_RE.search(stmt)
    ck("thm_bound_extract", b and b.group(1).strip() == "2 / 3")
    ck("bound_re_no_cross_paren",
       BOUND_RE.search("(chi : X) : forall e, (2 / 3 - \u03b5) * n <= m")
       is None
       or BOUND_RE.search("(chi : X) : forall e, (2 / 3 - \u03b5) * n <= m")
       .group(1) == "2 / 3")

    # -- truncation-prefix semantics of documented decimals ----------------
    import mpmath as mp
    ck("prefix_in_interval_pass",
       prefix_interval_ok(mp.mpf("0.75329606785607"), "0.7532960")[0])
    ck("prefix_below_interval_fail",
       not prefix_interval_ok(mp.mpf("0.7532959"), "0.7532960")[0])
    ck("prefix_at_upper_edge_fail",
       not prefix_interval_ok(mp.mpf("0.7532961"), "0.7532960")[0])

    # -- numerics ---------------------------------------------------------
    try:
        import mpmath  # noqa: F401
        ck("mpmath_available", True)
    except Exception:
        ck("mpmath_available", False)

    return checks


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Static forensic audit of a Lean 4 project (read-only).")
    ap.add_argument("--root", default=DEFAULT_ROOT,
                    help="project directory to scan (default: %(default)s)")
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--selftest", action="store_true",
                    help="run the self-test only")
    args = ap.parse_args(argv)

    t0 = time.time()
    print("lean_forensics %s (python %s)" % (__version__,
                                             sys.version.split()[0]))

    # ---- self-test ------------------------------------------------------
    st = run_selftest()
    failed = [n for n, ok in st if not ok]
    for name, ok in st:
        print("  [%s] selftest.%s" % ("OK" if ok else "FAIL", name))
    if failed:
        print("SELFTEST FAILED (%d/%d): %s"
              % (len(failed), len(st), ", ".join(failed)))
        print("verdict: TOOL_UNTRUSTED (exit 2)")
        return 2
    print("selftest passed (%d checks)" % len(st))
    if args.selftest:
        print("SELFTEST PASSED (exit 0)")
        return 0

    root = os.path.abspath(args.root)
    if not os.path.isdir(root):
        print("target not found: %s" % root)
        print("verdict: TOOL_UNTRUSTED (exit 2)")
        return 2

    # ---- enumerate Lean files -------------------------------------------
    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, root)
                lean_files.append((full, rel))
    lean_files.sort(key=lambda x: x[1])

    commit = read_git_commit(root)
    print("target: %s" % root)
    print("commit: %s" % (commit or "unknown"))

    scanned = [scan_file(full, rel) for full, rel in lean_files]
    n_stmt = sum(1 for f in scanned if f["zone"] == "statement")
    n_proof = len(scanned) - n_stmt
    print("scanned %d .lean files (statement zone: %d, proof zone: %d)"
          % (len(scanned), n_stmt, n_proof))

    findings = []
    warnings = []

    # ---- Z1: sorry / admit, zone-aware, position-aware -------------------
    sorry_stmt = sorry_proof = 0
    admit_hits = []
    poisoned = []
    for f in scanned:
        for t in f["tokens"]:
            if t["token"] == "sorry":
                if f["zone"] == "statement":
                    sorry_stmt += 1
                else:
                    sorry_proof += 1
                    findings.append(
                        "Z1 sorry in PROOF zone: %s:%d (enclosing %s %s)"
                        % (f["file"], t["line"], t["decl_kind"], t["decl_name"]))
                if t["decl_kind"] in ("def", "abbrev"):
                    poisoned.append(
                        "%s:%d (%s %s)" % (f["file"], t["line"],
                                           t["decl_kind"], t["decl_name"]))
                    findings.append(
                        "Z1 sorry inside a DEFINITION: %s:%d (%s %s) -- "
                        "statements depending on it would be poisoned"
                        % (f["file"], t["line"], t["decl_kind"], t["decl_name"]))
            elif t["token"] in ("admit", "admitted"):
                admit_hits.append("%s:%d" % (f["file"], t["line"]))
                findings.append("Z1 %s in %s zone: %s:%d"
                                % (t["token"], f["zone"], f["file"], t["line"]))
            elif t["token"] == "native_decide":
                findings.append(
                    "Z3 native_decide: %s:%d -- would extend the axiom base "
                    "beyond permitted_axioms; manual kernel review required"
                    % (f["file"], t["line"]))
            elif t["token"] == "unsafe":
                warnings.append("unsafe token: %s:%d" % (f["file"], t["line"]))

    print("sorry: statement zone = %d, proof zone = %d; admit = %d"
          % (sorry_stmt, sorry_proof, len(admit_hits)))

    # ---- Z2: axioms ------------------------------------------------------
    declared_axioms = sorted({a for f in scanned for a in f["axioms"]})
    for a in declared_axioms:
        findings.append("Z2 project-declared axiom: %s" % a)
    print("project-declared axioms: %s"
          % (", ".join(declared_axioms) if declared_axioms else "none"))

    # ---- Z4: comparator consistency (every comparator*.json config) ------
    comparator_cfgs = {}
    for fn in sorted(os.listdir(root)):
        if fn.startswith("comparator") and fn.endswith(".json"):
            with open(os.path.join(root, fn), encoding="utf-8") as fh:
                comparator_cfgs[fn] = json.load(fh)
    if not comparator_cfgs:
        findings.append("Z4 no comparator*.json found at %s" % root)

    comparator_names = []
    configs_meta = {}
    for fn, cfg in sorted(comparator_cfgs.items()):
        names = cfg.get("theorem_names", [])
        comparator_names.extend(names)
        permitted = cfg.get("permitted_axioms", PERMITTED_AXIOMS)
        if sorted(permitted) != sorted(PERMITTED_AXIOMS):
            warnings.append("%s permitted_axioms differ from the documented "
                            "set: %s" % (fn, permitted))
        configs_meta[fn] = {
            "challenge_module": cfg.get("challenge_module"),
            "solution_module": cfg.get("solution_module"),
            "theorem_count": len(names),
            "permitted_axioms": permitted,
        }
    dupes = sorted({n for n in comparator_names
                    if comparator_names.count(n) > 1})
    if dupes:
        findings.append("Z4 theorem listed in multiple comparator configs: %s"
                        % ", ".join(dupes))
    all_names = sorted(set(comparator_names))

    stmt_thms = {}
    for f in scanned:
        if f["zone"] == "statement":
            for t in f["theorems"]:
                stmt_thms[t["name"]] = (f["file"], t["line"], t["bound"])
    proof_thm_files = {}
    name_alt = {re.escape(n) for n in all_names}
    if name_alt:
        proof_re = re.compile(
            r"(?m)^[ \t]*(?:private[ \t]+|protected[ \t]+|"
            r"noncomputable[ \t]+)*theorem\s+(" + "|".join(sorted(name_alt))
            + r")\b")
        for f in scanned:
            if f["zone"] == "proof":
                with open(os.path.join(root, f["file"]), encoding="utf-8") as fh:
                    text = strip_lean_comments(fh.read())
                for m in proof_re.finditer(text):
                    proof_thm_files.setdefault(m.group(1), []).append(f["file"])

    theorem_table = []
    for name in all_names:
        in_stmt = name in stmt_thms
        in_proof = name in proof_thm_files
        bound = stmt_thms[name][2] if in_stmt else None
        theorem_table.append({
            "name": name,
            "configs": [fn for fn, cfg in sorted(comparator_cfgs.items())
                        if name in cfg.get("theorem_names", [])],
            "declared_in_statement_zone": in_stmt,
            "proved_in_proof_zone": in_proof,
            "proof_files": proof_thm_files.get(name, []),
            "bound": bound,
        })
        if not in_stmt:
            findings.append("Z4 comparator theorem missing from statement "
                            "zone: %s" % name)
        if not in_proof:
            findings.append("Z4 comparator theorem has no proof-side "
                            "declaration: %s" % name)

    # extra theorems on the statement side not listed by ANY comparator config
    extra_stmt = sorted(set(stmt_thms) - set(all_names))
    if extra_stmt:
        warnings.append(
            "statement-zone theorems not in any comparator config: %s"
            % ", ".join(extra_stmt))

    if sorry_stmt != len(all_names):
        warnings.append(
            "statement-zone sorry count (%d) != total comparator theorem "
            "count across configs (%d)" % (sorry_stmt, len(all_names)))

    print("comparator configs: %s"
          % ", ".join(sorted("%s=%d" % (fn, m["theorem_count"])
                             for fn, m in sorted(configs_meta.items()))))
    print("comparator theorems: %d listed, %d in statement zone, "
          "%d proved on proof side"
          % (len(all_names),
             sum(1 for t in theorem_table if t["declared_in_statement_zone"]),
             sum(1 for t in theorem_table if t["proved_in_proof_zone"])))

    # ---- Z5: constants in the statements ---------------------------------
    bounds = {}
    for t in theorem_table:
        if t["bound"]:
            bounds.setdefault(t["bound"], []).append(t["name"])
    print("bound constants found:")
    for b in sorted(bounds):
        print("  %-24s x%d  %s" % (b, len(bounds[b]), ", ".join(bounds[b])))

    # ---- Z6: numerics ----------------------------------------------------
    num_results, num_values = numeric_audit()
    print("numerics (mpmath 50 dps):")
    for r in num_results:
        print("  [%s] %s -> %s" % ("OK" if r["ok"] else "FAIL",
                                   r["check"], r["detail"]))
        if not r["ok"]:
            findings.append("Z6 numeric mismatch: %s (%s)"
                            % (r["check"], r["detail"]))
    for k in sorted(num_values):
        print("    %s = %s" % (k, num_values[k]))

    # ---- verdict ---------------------------------------------------------
    timing = time.time() - t0
    verdict = "STATIC_SCAN_CLEAN" if not findings else "FINDINGS_PRESENT"
    code = 0 if not findings else 1
    try:
        import mpmath
        mpmath_ver = mpmath.__version__
    except Exception:
        mpmath_ver = None

    report = {
        "tool": "lean_forensics.py",
        "version": __version__,
        "env": {"python": sys.version.split()[0],
                "mpmath": mpmath_ver},
        "sources": SOURCES,
        "target": root,
        "commit": commit,
        "files": {"total_lean": len(scanned),
                  "statement_zone": n_stmt,
                  "proof_zone": n_proof},
        "sorry": {"statement_zone": sorry_stmt, "proof_zone": sorry_proof},
        "admit_hits": admit_hits,
        "poisoned_definitions": poisoned,
        "project_declared_axioms": declared_axioms,
        "comparator": {
            "configs": configs_meta,
            "theorem_count": len(all_names),
        },
        "theorem_table": theorem_table,
        "bound_constants": {k: v for k, v in bounds.items()},
        "numerics": {"checks": num_results, "values": num_values},
        "findings": findings,
        "warnings": warnings,
        "verdict": verdict,
        "timing_s": round(timing, 3),
    }
    out_dir = os.path.dirname(args.out)
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)
        fh.write("\n")

    print("\n--- findings (%d) ---" % len(findings))
    for f in findings:
        print("  [FAIL] %s" % f)
    print("--- warnings (%d) ---" % len(warnings))
    for w in warnings:
        print("  [warn] %s" % w)
    print("\nverdict: %s (exit %d)" % (verdict, code))
    print("timing: %.3f s" % timing)
    print("written: %s" % args.out)
    return code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Exception as exc:
        import traceback
        traceback.print_exc()
        print("INTERNAL ERROR: %s" % exc)
        print("verdict: TOOL_UNTRUSTED (exit 2)")
        sys.exit(2)
