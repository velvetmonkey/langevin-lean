# langevin-lean: Formal Proofs of Bounded-Noise Langevin Convergence in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
DOI: 10.5281/zenodo.20478206  
2026-05-31

## Abstract

`langevin-lean` is a Lean 4 / Mathlib library formalising a deterministic bounded-noise convergence argument for Langevin dynamics. The library works over a real inner product space, packages an abstract gradient map with Lipschitz and strong-monotonicity hypotheses, and studies the noisy update `x_{k+1} = x_k - alpha grad_f(x_k) + xi_k`. It proves gradient-step contraction, a one-step contraction-plus-noise bound, a linear recurrence estimate, and geometric convergence to a noise-dependent ball. The formal development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

The overdamped Langevin stochastic differential equation is a basic model for sampling from densities proportional to `exp(-f)`. Its Euler discretisation, the unadjusted Langevin algorithm, combines a gradient drift term with Gaussian noise. Classical convergence results for this process are distributional: they are stated in Wasserstein distance, KL divergence, or total variation, and they rely on stochastic calculus and measure-theoretic functional inequalities.

`langevin-lean` formalises a deterministic proxy for that analysis. The Gaussian perturbation is replaced by a bounded disturbance, and the proof follows the squared distance to the minimiser. The resulting theorem is a contraction-plus-noise statement: the iterates converge geometrically to a ball whose radius is determined by the noise magnitude. This is not a full stochastic Langevin theorem, but it captures the finite-dimensional Lyapunov calculation that underlies many stability proofs for noisy gradient systems.

The repository is deliberately focused. It does not formalise Ito integration, Girsanov transformations, log-Sobolev inequalities, or distributional convergence. Instead, it gives a compact, importable Lean 4 proof of the deterministic recurrence argument under explicit smoothness, strong convexity, step-size, and bounded-noise hypotheses.

## 2. Library Overview

The project is organised into three implementation modules plus a root import file:

- `LangevinLean/Defs.lean` defines `LangevinSetup`, the contraction factor `rho`, the update `step`, the iterate sequence, the effective contraction `rho_eff`, the linear recurrence constant, and the final noise radius.
- `LangevinLean/StepBound.lean` proves the gradient norm bound, the strong-convexity inner-product bound, deterministic gradient-step contraction, and the one-step noisy bound.
- `LangevinLean/Convergence.lean` proves the contraction condition, non-negativity of `rho`, the linear recurrence estimate, Young's inequality, cross-term absorption, and the final convergence theorem.
- `LangevinLean.lean` is the root module importing the library.

The project depends on:

- Lean `v4.28.0`
- Mathlib `v4.28.0`

The formal development contains zero `sorry`, zero `admit`, and introduces no project-specific axioms. It is written against Lean 4 and Mathlib, using standard Lean/Mathlib axioms only.

The formal setting is a real inner product space:

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
```

A `LangevinSetup` packages:

```text
grad_f : E -> E
x_star : E
L, m, alpha, sigma : Real
```

with hypotheses

```text
0 < L, 0 < m, 0 < alpha, 0 <= sigma, m <= L
grad_f x_star = 0
||grad_f x - grad_f y|| <= L * ||x - y||
m * ||x - y||^2 <= <grad_f x - grad_f y, x - y>.
```

The repository is available at:

<https://github.com/velvetmonkey/langevin-lean>

## 3. Theorem Inventory

The source contains sixteen headline theorem-level results.

### Layer 1 - One-Step Geometry

1. `grad_norm_bound` proves that Lipschitzness and `grad_f x_star = 0` control the gradient norm:

```text
||grad_f x|| <= L * ||x - x_star||.
```

2. `inner_grad_lower_bound` derives the strong-convexity inner-product lower bound:

```text
m * ||x - x_star||^2 <= <grad_f x, x - x_star>.
```

3. `gradient_step_sq_bound` proves deterministic gradient-step contraction:

```text
||(x - alpha * grad_f x) - x_star||^2
  <= rho * ||x - x_star||^2.
```

4. `gradient_step_norm_le` proves that if `rho <= 1`, then the deterministic gradient step does not increase distance to the minimiser.

5. `langevin_step_bound` proves the one-step bounded-noise estimate:

```text
||step x xi - x_star||^2
  <= rho * ||x - x_star||^2
     + 2 * (alpha * sigma) * ||x - x_star||
     + 2 * (alpha * sigma)^2.
```

### Layer 2 - Contraction and Recurrences

6. `contraction_condition` proves the sufficient step-size condition:

```text
alpha < 2 * m / L^2 -> rho < 1.
```

7. `rho_le_one` proves the weak version:

```text
alpha <= 2 * m / L^2 -> rho <= 1.
```

8. `rho_nonneg` proves

```text
0 <= rho.
```

9. `linear_recurrence_bound` proves the general scalar recurrence theorem:

```text
a(n+1) <= rho * a(n) + c
  -> a(n) <= rho^n * a(0) + c / (1 - rho),
```

under `0 <= rho < 1` and `0 <= c`.

10. `scaled_young` proves the scaled Young inequality:

```text
2 * a * b <= epsilon * a^2 + b^2 / epsilon.
```

### Layer 3 - Convergence

11. `step_to_linear_recurrence` absorbs the cross term from `langevin_step_bound` into a linear recurrence:

```text
||step x xi - x_star||^2
  <= rho_eff * ||x - x_star||^2 + c_linear.
```

12. `rho_eff_nonneg` proves `0 <= rho_eff` when `0 <= rho`.

13. `rho_eff_lt_one` proves `rho_eff < 1` when `rho < 1`.

14. `c_linear_nonneg` proves `0 <= c_linear` under `rho < 1`.

15. `noiseRadius_eq` proves the algebraic identity:

```text
noiseRadius = c_linear / (1 - rho_eff).
```

16. `langevin_convergence` is the final theorem:

```text
||iterate x0 noise k - x_star||^2
  <= rho_eff^k * ||x0 - x_star||^2 + noiseRadius.
```

## 4. Main Theorems

### Gradient-Step Contraction

The theorem `gradient_step_sq_bound` expands the squared distance after the deterministic gradient step. The strong-convexity hypothesis controls the descent inner product, and the Lipschitz-gradient hypothesis controls the squared gradient norm. The result is the familiar factor

```text
rho = 1 - 2 * alpha * m + alpha^2 * L^2.
```

### One-Step Bounded-Noise Bound

The theorem `langevin_step_bound` adds a perturbation `xi` satisfying

```text
||xi|| <= alpha * sigma.
```

The proof expands the squared norm of the sum of the deterministic step displacement and the noise. Cauchy-Schwarz and the non-expansion result for `rho <= 1` control the cross term, giving the contraction-plus-noise inequality.

### Linearised Recurrence

The theorem `step_to_linear_recurrence` applies Young's inequality to the cross term

```text
2 * alpha * sigma * ||x - x_star||.
```

With `epsilon = (1 - rho) / 2`, this converts the nonlinear one-step estimate into

```text
a_{k+1} <= rho_eff * a_k + c_linear.
```

### Convergence to a Noise Ball

The theorem `langevin_convergence` assumes bounded noise at every step and `rho < 1`. It proves

```text
forall k,
  ||S.iterate x0 noise k - S.x_star||^2
    <= S.rho_eff^k * ||x0 - S.x_star||^2 + S.noiseRadius.
```

This is geometric convergence to a deterministic noise-dependent ball.

## 5. Proof Sketch

`LangevinLean/Defs.lean` sets up the abstract deterministic model. The stochastic Langevin update is represented by an arbitrary noise sequence, with stochastic assumptions replaced by the pointwise deterministic bound `||noise k|| <= alpha * sigma`.

`LangevinLean/StepBound.lean` proves the local calculation. Smoothness gives `grad_norm_bound`; strong convexity gives `inner_grad_lower_bound`. Expanding the squared distance after `x - alpha grad_f x` yields `gradient_step_sq_bound`. Adding noise and applying the real inner-product norm expansion yields `langevin_step_bound`.

`LangevinLean/Convergence.lean` proves the scalar facts needed to iterate the local estimate. The step-size condition implies `rho < 1`; the assumption `m <= L` gives `rho_nonneg`. Young's inequality absorbs the cross term, and induction on `k` proves the resulting linear recurrence. The identity `noiseRadius_eq` rewrites the steady-state term into the final displayed form.

## 6. Relation to Sibling Libraries

`langevin-lean` is closest to `gradient-descent-lean` and `sgd-lean`. `gradient-descent-lean` has DOI `10.5281/zenodo.20472996` and proves deterministic smooth convex descent. `sgd-lean` has DOI `10.5281/zenodo.20475583` and studies a bounded-noise oracle model for stochastic gradient descent. The present library uses a similar deterministic bounded-noise philosophy, but for the Langevin-style update and a strongly convex contraction analysis.

`contraction-lean` has DOI `10.5281/zenodo.20474762` and formalises convergence through metric contraction. The proof in `langevin-lean` is an affine contraction with an additive disturbance term. `mirror-descent-lean` has DOI `10.5281/zenodo.20475033` and uses a Bregman potential rather than Euclidean squared distance. Together these repositories cover several common proof patterns: exact descent, noisy descent, contraction, and geometric optimisation.

## 7. Conclusion

`langevin-lean` provides a compact Lean 4 / Mathlib formalisation of a bounded-noise Langevin convergence argument. It defines the deterministic proxy for Langevin dynamics, proves contraction of the gradient step, bounds the effect of bounded perturbations, converts the estimate into a linear recurrence, and proves geometric convergence to a noise-dependent ball.

Future work could connect this deterministic proxy to formal probability theory, stochastic processes, Wasserstein metrics, and log-Sobolev inequalities. Those ingredients would be needed for a full machine-checked theorem about stochastic Langevin sampling. The current repository supplies the checked contraction-plus-noise core.

## References

Roberts, G. O. and Tweedie, R. L. (1996). *Exponential convergence of Langevin distributions and their discrete approximations*. Bernoulli, 2(4), 341-363.

Dalalyan, A. S. (2017). *Theoretical guarantees for approximate sampling from smooth and log-concave densities*. Journal of the Royal Statistical Society: Series B, 79(3), 651-676.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *sgd-lean: Formal Proofs of Bounded-Noise SGD Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475583>

Cassie, B. (2026). *contraction-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20474762>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>
