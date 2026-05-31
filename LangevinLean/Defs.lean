/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Langevin Dynamics: Definitions

This module defines the setup for analysing the Unadjusted Langevin Algorithm (ULA)
using a deterministic bounded-noise model.

## Overview

The overdamped Langevin SDE for sampling from π ∝ exp(−f) is

  dX_t = −∇f(X_t) dt + √2 dW_t.

Discretised with step size α this yields the ULA update

  x_{k+1} = x_k − α · ∇f(x_k) + √(2α) · ξ_k,   ξ_k ∼ N(0, I).

## Design note — deterministic proxy

Full stochastic convergence (in KL divergence or Wasserstein distance) requires
measure-theory infrastructure that is not yet available in Mathlib, including:
- Itô integration and the Itô formula,
- Girsanov's theorem,
- Log-Sobolev or Poincaré inequalities.

As a formal proxy we replace the Gaussian noise ξ_k with a deterministic bounded
perturbation ‖ξ_k‖ ≤ α σ and prove convergence of the distance-to-minimiser
‖x_k − x*‖² (a Lyapunov argument) rather than distributional convergence.
This captures the essential contraction-plus-noise structure of ULA.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Langevin setup.**

Bundles an L-smooth, m-strongly convex objective function (represented via its
gradient), a minimiser x*, step size α, and noise bound σ.

The assumptions are:
- `grad_at_min`: ∇f(x*) = 0 (first-order optimality),
- `smooth`: ‖∇f(x) − ∇f(y)‖ ≤ L ‖x − y‖ (L-Lipschitz gradient),
- `strong_convex`: ⟨∇f(x) − ∇f(y), x − y⟩ ≥ m ‖x − y‖² (m-strong convexity). -/
structure LangevinSetup (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Gradient of the objective f. -/
  grad_f : E → E
  /-- Minimiser of f. -/
  x_star : E
  /-- Smoothness constant (Lipschitz constant of the gradient). -/
  L : ℝ
  /-- Strong convexity constant. -/
  m : ℝ
  /-- Step size. -/
  α : ℝ
  /-- Noise bound parameter. -/
  σ : ℝ
  /-- L is positive. -/
  hL_pos : 0 < L
  /-- m is positive. -/
  hm_pos : 0 < m
  /-- Step size is positive. -/
  hα_pos : 0 < α
  /-- Noise bound is nonnegative. -/
  hσ_nonneg : 0 ≤ σ
  /-- The condition number L/m is at least 1. -/
  hm_le_L : m ≤ L
  /-- Gradient vanishes at the minimiser (first-order optimality). -/
  grad_at_min : grad_f x_star = 0
  /-- L-smoothness: the gradient is L-Lipschitz. -/
  smooth : ∀ x y : E, ‖grad_f x - grad_f y‖ ≤ L * ‖x - y‖
  /-- m-strong convexity via the gradient monotonicity condition. -/
  strong_convex : ∀ x y : E, m * ‖x - y‖ ^ 2 ≤ ⟪grad_f x - grad_f y, x - y⟫_ℝ

namespace LangevinSetup

variable (S : LangevinSetup E)

/-- Contraction factor `ρ = 1 − 2αm + α²L²`. -/
noncomputable def ρ : ℝ := 1 - 2 * S.α * S.m + S.α ^ 2 * S.L ^ 2

/-- One step of the (noisy) Langevin algorithm: `x' = x − α ∇f(x) + ξ`. -/
def step (x ξ : E) : E := x - S.α • S.grad_f x + ξ

/-- Iterate the Langevin step with a noise sequence. -/
def iterate (x₀ : E) (noise : ℕ → E) : ℕ → E
  | 0 => x₀
  | n + 1 => S.step (iterate x₀ noise n) (noise n)

/-- Effective contraction rate after absorbing the cross-term via Young's inequality.
Equal to `(1 + ρ) / 2`. -/
noncomputable def ρ_eff : ℝ := (1 + S.ρ) / 2

/-- Per-step additive constant in the linearised recurrence. -/
noncomputable def c_linear : ℝ :=
  2 * S.α ^ 2 * S.σ ^ 2 * (2 - S.ρ) / (1 - S.ρ)

/-- Noise-dependent ball radius: the steady-state upper bound on ‖x_k − x*‖².
Equals `4 α² σ² (2 − ρ) / (1 − ρ)²`. -/
noncomputable def noiseRadius : ℝ :=
  4 * S.α ^ 2 * S.σ ^ 2 * (2 - S.ρ) / (1 - S.ρ) ^ 2

end LangevinSetup
