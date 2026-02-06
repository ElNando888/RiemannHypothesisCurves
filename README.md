# The Riemann Hypothesis for curves, autoformalized

This is a formal Lean proof of the Riemann Hypothesis for hyperelliptic curves over finite fields. We follow the argument laid out in Chapter 11 of Iwaniec-Kowalski's classic text *Analytic Number Theory*, based on the Bombieri-Stepanov polynomial method.

Given a polynomial $f(x)$ of degree $m > 2$, let $F=\mathbb{F}_q$ be the finite field for the prime power $q > 6m$. Then the number of solutions to $y^2 = f(x)$ for $(x,y) \in F^2$ is bounded from the expected value of $q$ by at most $5m q^{1/2}$. This square-root cancellation is the analogue of the celebrated Riemann Hypothesis, for counting points on the hyperelliptic curve $y^2 = f(x)$.

The final Lean output is in `RiemannHypothesisCurves/RiemannHypothesisHEC.lean` (imported by
`RiemannHypothesisCurves/Main.lean`). The human-supplied blueprint is in `blueprint/src/content.tex`.

The initial statements, proofs, and documentation were created by Gauss, Math Inc's frontier
autoformalization agent; subsequent commits on this branch include human/AI-assisted refactors.

The blueprint dependency graph is generated as part of the blueprint web build:

```bash
uvx leanblueprint web
```

Then open `blueprint/dep_graph_document.html`.

---

## Highlights

- **Scope:** ≈3400 lines of Lean (tracked Lean LOC: 3431).
- **Workflow:** AI-generated formalization from a LaTeX blueprint with human scaffolding.
- **Result:** a complete Lean theorem establishing the Riemann Hypothesis for hyperelliptic curves over finite fields.

---

## Refactor progress (Lean LOC by commit on `refactor`)

Lean LOC is computed as the total number of lines across all git-tracked `*.lean` files at each commit (including comments/blank lines).

| Commit | Date | Message | Lean LOC before | Lean LOC after | Δ |
|---|---|---|---:|---:|---:|
| `c99880d` | 2026-01-16 | let there be light | — | 4016 | +4016 |
| `2993dab` | 2026-02-05 | Refactor: simplify StepanovSystem bounds | 4016 | 3979 | -37 |
| `fb5582a` | 2026-02-05 | Refactor: tighten dimension_inequality_nat setup | 3979 | 3969 | -10 |
| `c845f82` | 2026-02-05 | Refactor: compress constraint term bound | 3969 | 3959 | -10 |
| `c45445c` | 2026-02-05 | Refactor: simplify Bmax comparison algebra | 3959 | 3939 | -20 |
| `145e999` | 2026-02-05 | Refactor: use ker_ne_bot_of_finrank_lt | 3939 | 3931 | -8 |
| `86e39a9` | 2026-02-05 | Refactor: simplify m<q derivations | 3931 | 3924 | -7 |
| `9c63e29` | 2026-02-05 | Refactor: use LinearMap.mulRight for polyMulRightLinear | 3924 | 3918 | -6 |
| `3ff5e35` | 2026-02-05 | Refactor: use LinearMap.proj for piProj | 3918 | 3916 | -2 |
| `1d58860` | 2026-02-05 | Docs: add LOC-by-commit progress table | 3916 | 3916 | +0 |
| `237e8cc` | 2026-02-05 | Refactor: streamline sigma degree bound | 3916 | 3917 | +1 |
| `37ae41a` | 2026-02-05 | Refactor: simplify J-expression positivity | 3917 | 3913 | -4 |
| `1bb053e` | 2026-02-05 | Refactor: simplify Bmax bound arithmetic | 3913 | 3900 | -13 |
| `dea1919` | 2026-02-05 | Refactor: shorten q-cancellation step | 3900 | 3897 | -3 |
| `50568f4` | 2026-02-05 | Refactor: streamline A_real lower bound | 3897 | 3881 | -16 |
| `605a045` | 2026-02-05 | Refactor: streamline curve fiber bound | 3881 | 3869 | -12 |
| `37130e4` | 2026-02-05 | Refactor: simplify curve count lower bound | 3869 | 3843 | -26 |
| `1760642` | 2026-02-05 | Refactor: drop unused module; simplify bounds | 3843 | 2896 | -947 |
| `5bf539a` | 2026-02-05 | Fix imports: restore StepanovNonSquare and update dependencies | 2896 | 3771 | +875 |
| `cdac43b` | 2026-02-05 | Merge gpt52-shrink20 (shrink blueprint graph image) | 3771 | 3771 | +0 |
| `107212d` | 2026-02-05 | Refactor: shorten Stepanov bound algebra | 3771 | 3728 | -43 |
| `5481845` | 2026-02-05 | Chore: ignore work copies; document workflow | 3728 | 3728 | +0 |
| `33a151d` | 2026-02-05 | Docs: regenerate README table from origin/refactor | 3728 | 3728 | +0 |
| `12ba4d6` | 2026-02-05 | Docs: switch README LOC to Lean LOC | 3728 | 3728 | +0 |
| `5506065` | 2026-02-06 | Refactor: compress Stepanov/Hasse proofs | 3728 | 3439 | -289 |
| `44011d2` | 2026-02-06 | Refactor: shorten StepanovPolynomial inequalities | 3439 | 3431 | -8 |

To regenerate this table locally:

```bash
python3 - <<'PY'
import subprocess

def sh(*args):
    return subprocess.check_output(args, text=True)

def lean_loc_for_commit(commit: str) -> int:
    files = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', commit], text=True).splitlines()
    files = [f for f in files if f.endswith('.lean')]
    total = 0
    for f in files:
        content = subprocess.check_output(['git', 'cat-file', '-p', f'{commit}:{f}'])
        total += content.count(b'\n')
        if content and not content.endswith(b'\n'):
            total += 1
    return total

target = 'refactor'
commits = sh('git', 'rev-list', '--reverse', '--first-parent', target).splitlines()
rows = []
prev_loc = 0
for i, c in enumerate(commits):
    loc = lean_loc_for_commit(c)
    before = None if i == 0 else prev_loc
    delta = loc if before is None else loc - before
    date = sh('git', 'show', '-s', '--format=%cs', c).strip()
    subj = sh('git', 'show', '-s', '--format=%s', c).strip()
    rows.append((c[:7], date, subj, before, loc, delta))
    prev_loc = loc

print('| Commit | Date | Message | Lean LOC before | Lean LOC after | Δ |')
print('|---|---|---|---:|---:|---:|')
for h, d, m, b, a, delta in rows:
    btxt = '—' if b is None else str(b)
    print(f'| `{h}` | {d} | {m} | {btxt} | {a} | {delta:+d} |')
PY
```

## Links

- **Math Inc.:** <https://www.math.inc/>
- **Gauss (autoformalization agent):** <https://www.math.inc/gauss>

---

## Repository layout

- `RiemannHypothesisCurves/` – main Lean development of the proof.
- `RiemannHypothesisCurves.lean` – top-level Lean entry point.
- `blueprint/` – LaTeX blueprint + web/PDF build assets (the dependency graph is generated).
- `home_page/` – Jekyll-based landing page used for the project website.

## Collaboration workflow

When working on a shared filesystem, keep the repo buildable and avoid committing large work copies:

- Use a **work copy** while refactoring a file, then compile the copy, then swap it back.
- Put work copies under `wip/` (ignored by git) or outside the repo entirely.
- Avoid leaving `*.alex_work.lean`, `*.work*.lean`, or other backup `.lean` files in the tracked tree.

---

## Building

You will need:

- [Lean 4](https://lean-lang.org/) with `lake`
- [uv](https://docs.astral.sh/uv/getting-started/installation/) for the
  blueprint tools
- A LaTeX installation (e.g. TeX Live) for the PDF

### Lean development

```bash
lake exe cache get && lake build
```

### Blueprint (PDF)

```bash
uvx leanblueprint pdf
```

### Blueprint (web + local server)

```bash
uvx leanblueprint web
uvx leanblueprint serve
```

The generated site is served locally; by default the blueprint index is at
`http://localhost:8000/`.

---

## About

This repository is part of Math Inc.'s broader effort to apply AI-assisted
formal verification to fundamental problems in mathematics. Faster, lower-friction formalization can make complex mathematical
results easier to verify, extend, and trust.

For questions or collaborations, please reach out via
<https://www.math.inc/>.

---

## References

- Iwaniec, H., Kowalski, E., *Analytic Number Theory*, American Mathematical Society Colloquium Publications, vol. 53, 2004.
  <https://www.ams.org/books/coll/053/>
