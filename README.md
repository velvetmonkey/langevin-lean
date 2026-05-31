# langevin-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](LangevinLean)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20478206.svg)](https://doi.org/10.5281/zenodo.20478206)

**langevin-lean: Formal Proofs of Langevin Dynamics Convergence in Lean 4**

Lean 4 formal proofs for a deterministic bounded-noise model of Langevin dynamics. The development covers the Langevin setup, gradient-step contraction, one-step bounded-noise estimates, linear recurrence control, and convergence to a noise-dependent ball.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

The overdamped Langevin SDE for sampling from a distribution proportional to `exp(-f)` is:

```text
dX_t = -grad f(X_t) dt + sqrt(2) dW_t
```

The unadjusted Langevin algorithm discretises this process with step size `alpha`:

```text
x_{k+1} = x_k - alpha * grad f(x_k) + sqrt(2 alpha) * xi_k
```

Full stochastic convergence for Langevin dynamics requires stochastic calculus and measure-theoretic infrastructure such as Ito integration, Girsanov's theorem, and functional inequalities. This library formalises a deterministic proxy: the Gaussian perturbation is replaced by bounded noise, and the proof tracks squared distance to the minimiser through a contraction-plus-noise Lyapunov argument.

## Setting

A real inner product space `E`, a gradient map `grad_f : E -> E`, a minimiser `x_star`, smoothness constant `L`, strong convexity constant `m`, step size `alpha`, and noise bound `sigma`.

The assumptions are:

- `grad_f x_star = 0`
- `grad_f` is `L`-Lipschitz
- the gradient satisfies the `m`-strong monotonicity condition
- `0 < L`, `0 < m`, `0 < alpha`, `0 <= sigma`, and `m <= L`

The deterministic bounded-noise update is:

```text
step x xi = x - alpha * grad_f x + xi
```

with bounded perturbations:

```text
||xi_k|| <= alpha * sigma
```

## Main result

Under the contraction condition `rho < 1`, where:

```text
rho = 1 - 2 * alpha * m + alpha^2 * L^2
rho_eff = (1 + rho) / 2
noiseRadius = 4 * alpha^2 * sigma^2 * (2 - rho) / (1 - rho)^2
```

the main theorem proves:

```text
||iterate x0 noise k - x_star||^2
  <= rho_eff^k * ||x0 - x_star||^2 + noiseRadius
```

This is geometric convergence to a noise-dependent ball for the deterministic bounded-noise Langevin model.

## Project structure

```text
LangevinLean/
├── Defs.lean        — LangevinSetup, contraction parameters, step and iterate
├── StepBound.lean   — gradient norm, strong-convexity inner-product bound,
│                      gradient-step contraction, one-step noise bound
└── Convergence.lean — contraction condition, linear recurrence control,
                       Young inequality, convergence theorem
LangevinLean.lean    — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `grad_norm_bound` | `||grad_f x|| <= L * ||x - x_star||` |
| 2 | `inner_grad_lower_bound` | `m * ||x - x_star||^2 <= <grad_f x, x - x_star>` |
| 3 | `gradient_step_sq_bound` | `||(x - alpha • grad_f x) - x_star||^2 <= rho * ||x - x_star||^2` |
| 4 | `gradient_step_norm_le` | If `rho <= 1`, the deterministic gradient step does not increase distance to `x_star` |
| 5 | `langevin_step_bound` | If `||xi|| <= alpha * sigma` and `rho <= 1`, then `||step x xi - x_star||^2 <= rho * ||x - x_star||^2 + 2 * (alpha * sigma) * ||x - x_star|| + 2 * (alpha * sigma)^2` |
| 6 | `contraction_condition` | If `alpha < 2 * m / L^2`, then `rho < 1` |
| 7 | `rho_le_one` | If `alpha <= 2 * m / L^2`, then `rho <= 1` |
| 8 | `rho_nonneg` | `0 <= rho` |
| 9 | `linear_recurrence_bound` | If `a(n+1) <= rho * a(n) + c`, `0 <= rho < 1`, and `0 <= c`, then `a n <= rho^n * a 0 + c / (1 - rho)` |
| 10 | `scaled_young` | For `0 < epsilon`, `2 * a * b <= epsilon * a^2 + b^2 / epsilon` |
| 11 | `step_to_linear_recurrence` | Absorbs the one-step cross term into `rho_eff * ||x - x_star||^2 + c_linear` |
| 12 | `rho_eff_nonneg` | If `0 <= rho`, then `0 <= rho_eff` |
| 13 | `rho_eff_lt_one` | If `rho < 1`, then `rho_eff < 1` |
| 14 | `c_linear_nonneg` | If `rho < 1`, then `0 <= c_linear` |
| 15 | `noiseRadius_eq` | `noiseRadius = c_linear / (1 - rho_eff)` |
| 16 | `langevin_convergence` | `||iterate x0 noise k - x_star||^2 <= rho_eff^k * ||x0 - x_star||^2 + noiseRadius` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [sgd-lean](https://github.com/velvetmonkey/sgd-lean) — Lean 4 bounded-noise SGD convergence
- [frank-wolfe-lean](https://github.com/velvetmonkey/frank-wolfe-lean) — Lean 4 Frank-Wolfe convergence
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
