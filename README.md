# The Riemann Hypothesis for curves, autoformalized

This is a formal Lean proof of the Riemann Hypothesis for hyperelliptic curves over finite fields. We follow the argument laid out in Chapter 11 of Iwaniec-Kowalski's classic text *Analytic Number Theory*, based on the Bombieri-Stepanov polynomial method.

Given a polynomial $f(x)$ of degree $m > 2$, let $F=\mathbb{F}_q$ be the finite field for the prime power $q > 6m$. Then the number of solutions to $y^2 = f(x)$ for $(x,y) \in F^2$ is bounded from the expected value of $q$ by at most $5m q^{1/2}$. This square-root cancellation is the analogue of the celebrated Riemann Hypothesis, for counting points on the hyperelliptic curve $y^2 = f(x)$.

The final Lean output is in `RiemannHypothesisHEC.lean`. The human-supplied blueprint is in `content.tex`.

All statements, proofs, and documentation were created by Gauss, Math Inc's frontier autoformalization agent.

![Blueprint dependency graph](images/blueprint_dep_graph.png)

---

## Highlights

- **Scope:** ≈4000 lines of Lean.
- **Workflow:** AI-generated formalization from a LaTeX blueprint with human scaffolding.
- **Result:** a complete Lean theorem establishing the Riemann Hypothesis for hyperelliptic curves over finite fields.

---

## Links

- **Math Inc.:** <https://www.math.inc/>
- **Gauss (autoformalization agent):** <https://www.math.inc/gauss>

---

## Repository layout

- `RiemannHypothesisCurves/` – main Lean development of the proof.
- `RiemannHypothesisCurves.lean` – top-level Lean entry point.
- `blueprint/` – LaTeX blueprint, including the dependency graph and web/PDF build assets.
- `home_page/` – Jekyll-based landing page used for the project website.

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
