# zeta-23 audit — static forensic audit of Anthropic's Lean formalization
for the "more than two thirds" zeta-zeros result

Independent **static** audit of the Lean 4 project behind the August 2026
result that raised the unconditional lower bound on the fraction of
Riemann-zeta zeros that are simple and on the critical line from the
previous record to **67.2%**. This repo contains our tool and its report;
the audited code is *not* redistributed here (cloned read-only into the
gitignored `upstream/` directory, pinned by commit hash below).

**This is an audit, not a novel result.** The mathematics belongs to
Alpöge, Furman, and the earlier literature; the proof was discovered by a
research Claude (Anthropic) as documented in the sources.

## The claim, from primary sources

| Source | Pinned claim |
|---|---|
| Anthropic research post, 2026-08-10 (<https://www.anthropic.com/research/riemann-zeta>) | bound raised "from 41.6% to 67.2%"; validated by Alpöge & Furman (Anthropic), examined by **Brian Conrey** and Dan Goldston; Lean formalization "passes the standard validation tool comparator" |
| arXiv:2608.13637 (Alpöge, Furman; v1 2026-08-13, v2 2026-08-19) | "at least two thirds … simple and on the critical line, … at least five sixths are distinct; the previous unconditional records are 5/12 and 0.6603. With the Montgomery--Taylor window the constants become 0.6725 and 0.8362." Provenance note: "Proof discovered autonomously by Claude (Anthropic); verified and communicated by the listed authors." |
| github.com/anthropics/zeta-23-lean (README) | "no `sorry` outside the trusted comparator statement files (`Challenge.lean`, `Challenge/<Topic>.lean`)"; comparator "checks statement equality, that only the axioms `propext`, `Classical.choice`, `Quot.sound` are used, and replays the proofs through the kernel" |

Audited snapshot: commit **`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`**
(2026-09-05), 326 `.lean` files, toolchain pin
`leanprover/lean4:v4.33.0-rc2`, two comparator configs
(`comparator.json` = 17 theorems, `comparator-xiprime.json` = 6).

A secondary source (a YouTube clip transcript in our clippings) said the
examining expert was "Brian Conrad"; the primary source says **Brian
Conrey**. As in our Jacobian audit, the transcript is the unreliable layer.

## What "67.2%" is, exactly

The headline constant is the **Montgomery–Taylor window constant** of
Theorem D, written in `Challenge.lean` as `2 - 1 / cMT` with

```
cMT = √2·tan(1/√2) / (1 + tan(1/√2)/√2)      ( = 0.75329606785607067722… )
```

Five of the seventeen theorems state bounds with this constant (zeta:
dyadic, simple-dyadic, simple-cumulative; Dirichlet L: dyadic, simple),
in the ε-form `liminf ≥ c`. Our 50-dps mpmath evaluation:

```
2 - 1/cMT = 0.67250070367941164573  →  67.2500703679%  >  2/3   (margin +0.005834037013)
(3 - 1/cMT)/2 = 0.83625035183970582287
```

So the answer to "does the formalization really state ≥ 67.2%?" is **yes,
in five theorem statements**, and the exact constant exceeds two thirds by
+5.83e-3 (which is what justifies the paper title "More than two thirds").

### Every published number, reconciled (all exact / 50 dps)

| Published number | Source | Our value | Reconciliation |
|---|---|---|---|
| 41.6% (old bound) | Anthropic post | `5/12 = 41.6666666667%` | truncation to 1 dp |
| 67.2% (new bound) | Anthropic post | `2−1/cMT = 67.2500703679%` | truncation to 1 dp |
| 0.6725 | arXiv abstract (MT window) | `0.67250070367941164573` | truncation to 4 dp |
| 0.8362 | arXiv abstract (distinct, MT) | `0.83625035183970582287` | truncation to 4 dp |
| 0.6603 (prior distinct record) | arXiv abstract | `5/6 = 0.83333… > 0.6603` | beaten by +0.173 |
| `0.7532960…`, `0.67250…`, `0.83625…` | `Challenge.lean` comments | interval checks pass | truncation prefixes |
| identities `1/cMT = ½ + cot(1/√2)/√2`, `2−1/cMT = 3/2 − cot(1/√2)/√2`, `cMT = 2t/(√2+t)` | `Challenge.lean` comments | exact to < 1e-40 | identical |

## Method (anti-circularity)

`lean_forensics.py`, a self-contained static auditor (no Lean toolchain is
ever invoked — heavy installs are deferred to our own server by policy):

- **Zones** follow upstream's own CI rule: *statement zone* =
  `Challenge.lean` + `Challenge/*.lean` (sorry allowed there, by design),
  *proof zone* = all other 324 `.lean` files (sorry forbidden).
- **Comment stripping first.** Lean block comments nest; docstrings are
  block comments; the Challenge module's own prose mentions the word
  "sorry". A naive grep would report false positives. Our stripper blanks
  nested `/- -/`, `/-- -/`, `--` line comments while preserving offsets and
  line numbers, and skips string/char literals (self-test: 8 fixtures).
- **Position awareness.** Every `sorry` is attributed to its enclosing
  declaration; a sorry inside a `def`/`abbrev` would *poison* the statements
  depending on it and is a hard finding, not a statistic.
- **Three-way name matching**: every theorem in every `comparator*.json`
  must be declared in the statement zone *and* proved in the proof zone.
- **Numerics** in mpmath at 50 dps, with *truncation-prefix* semantics for
  documented decimals (`0.7532960…` claims the interval
  `[0.7532960, 0.7532961)`), not rounding.

## Results (2026-10-01, Python 3.14.4, mpmath 1.3.0)

Command: `python lean_forensics.py` — **exit 0**, verdict
`STATIC_SCAN_CLEAN`, self-test 23/23, 12/12 numeric checks, 0 findings,
0 warnings. Artifact: `results/forensics_report.json`.

| Check | Result |
|---|---|
| `sorry` in proof zone (324 files) | **0** ✓ |
| `sorry` in statement zone | 23 = 17 + 6, exactly the comparator statements ✓ |
| `admit` / project-declared `axiom` / `native_decide` / `unsafe` | 0 / 0 / 0 / 0 ✓ |
| 23/23 comparator theorems declared in statement zone | ✓ |
| 23/23 comparator theorems proved on proof side | ✓ |
| Bounds in statements | `2/3` ×6, `5/6` ×3, `2−1/cMT` ×5, `3/2−cMT⁻¹/2` ×3 |
| `2−1/cMT > 2/3`, consistent with 67.2% | ✓ (+5.83e-3; 67.25007%) |
| Comment-documented identities & decimals | ✓ (3 identities, 3 prefixes) |
| Prior-record reconciliation (5/12 → 41.6%) | ✓ |

Second comparator config (not part of the 67.2% headline): six theorems on
the zeros of `ξ′` stating 85.838% / 92.919% (standard window) and
86.864% / 93.432% (quartic window) simple-and-on-line / distinct. We
record the literals; we did **not** cross-check them against the paper
body.

### Development note: the gate caught our own bugs first

The first full run exited **1** with one finding and two warnings — all
three were *our* tool's defects, not upstream's: (1) a rounding-based
threshold rejected `cMT = 0.75329606785607` against the documented prefix
`0.7532960…` although the claim is true under truncation semantics;
(2) only `comparator.json` was read, so the six `xiPrime_*` theorems of
`comparator-xiprime.json` looked "unlisted". Fixed, and locked by three
regression fixtures (`prefix_in_interval_pass`,
`prefix_below_interval_fail`, `prefix_at_upper_edge_fail`) plus multi-config
reading. Fail-closed behavior (exit 1 → no claim pushed until resolved)
worked as designed.

## What this audit does NOT establish (honest bounds)

- **No Lean toolchain ran on this machine** (no `lake build`, no
  `leanprover/comparator`, no `nanoda` kernel replay, no `#print axioms`).
  We cannot confirm proof-term validity, statement equality across
  challenge/solution sides, or the axiom set as *seen by the kernel* —
  those are exactly what comparator does upstream, on their CI.
- Static text analysis cannot catch sorry-like behavior hidden behind
  metaprogramming, or code inside string literals; we scan tokens after
  comment stripping only.
- The paper's mathematics (the rank-trace inequality on a finite
  compression of Weil's form, Sylvester's law of inertia, the analytic
  inputs of Aryan and Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh,
  Bombieri 2000) is **not re-proved** here.
- The prior bound 5/12 and the expert validations (Conrey, Goldston,
  Alpöge, Furman) are taken from the pinned sources, not re-derived or
  re-confirmed independently.
- No claim about RH itself: two thirds on the line is not the Riemann
  hypothesis (100%), and upstream explicitly does not expect these
  techniques to prove RH.

## How to run

```
python lean_forensics.py --selftest    # self-test only
python lean_forensics.py               # full audit (default target: upstream/zeta-23-lean/zeta23)
python lean_forensics.py --root <dir>  # audit another checkout
```

Exit codes: `0` = no finding contradicts the upstream claims;
`1` = findings present (see report); `2` = self-test/tool failure (audit
untrusted, refuses to run).

Requirements: Python 3.10+ (run here: 3.14.4), mpmath (run here: 1.3.0).
No Lean, no network access needed at run time.

## Sources

- <https://www.anthropic.com/research/riemann-zeta>
- <https://arxiv.org/abs/2608.13637>
- <https://github.com/anthropics/zeta-23-lean> (commit `fbdc36bb`)
- Related, not used for claims here: Lean comparator
  (<https://github.com/leanprover/comparator>), Palomar registry template.

## License

MIT — see `LICENSE`. The audited repository is Apache-2.0 and is not
redistributed in this repo.
