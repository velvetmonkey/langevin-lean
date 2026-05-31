/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LangevinLean.Defs

/-!
# Langevin Dynamics: One-Step Bound

We prove the one-step contraction-plus-noise bound for the Langevin iteration:

  ‖x_{k+1} − x*‖² ≤ ρ ‖x_k − x*‖² + 2ασ ‖x_k − x*‖ + 2α²σ²

where ρ = 1 − 2αm + α²L².

## Proof outline

1. **Gradient norm bound** (`grad_norm_bound`): from L-smoothness and ∇f(x*) = 0
   we get ‖∇f(x)‖ ≤ L ‖x − x*‖.

2. **Inner product bound** (`inner_grad_lower_bound`): from m-strong convexity
   and ∇f(x*) = 0 we get ⟨∇f(x), x − x*⟩ ≥ m ‖x − x*‖².

3. **Gradient-step contraction** (`gradient_step_sq_bound`): combining (1) and (2)
   yields ‖(x − α∇f(x)) − x*‖² ≤ ρ ‖x − x*‖².

4. **Full step bound** (`langevin_step_bound`): adding the bounded noise ξ with
   ‖ξ‖ ≤ ασ and using Cauchy–Schwarz produces the claimed bound.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LangevinSetup

variable (S : LangevinSetup E)

/-- The gradient norm is controlled by the distance to the minimiser, via
L-smoothness and ∇f(x*) = 0. -/
lemma grad_norm_bound (x : E) :
    ‖S.grad_f x‖ ≤ S.L * ‖x - S.x_star‖ := by
  have h := S.smooth x S.x_star
  rwa [S.grad_at_min, sub_zero] at h

/-- Strong convexity gives a lower bound on ⟨∇f(x), x − x*⟩. -/
lemma inner_grad_lower_bound (x : E) :
    S.m * ‖x - S.x_star‖ ^ 2 ≤ ⟪S.grad_f x, x - S.x_star⟫_ℝ := by
  have h := S.strong_convex x S.x_star
  rwa [S.grad_at_min, sub_zero] at h

/-
The deterministic gradient step contracts distances:
  ‖(x − α ∇f(x)) − x*‖² ≤ ρ ‖x − x*‖².
-/
theorem gradient_step_sq_bound (x : E) :
    ‖(x - S.α • S.grad_f x) - S.x_star‖ ^ 2 ≤ S.ρ * ‖x - S.x_star‖ ^ 2 := by
  rw [ LangevinSetup.ρ ];
  have := S.inner_grad_lower_bound x;
  have := S.smooth x S.x_star;
  simp_all +decide [ norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ];
  rw [ norm_smul, mul_pow, Real.norm_eq_abs ];
  have := norm_sub_sq_real ( S.grad_f x ) ( S.grad_f S.x_star ) ; simp_all +decide [ real_inner_comm ];
  rw [ S.grad_at_min ] at * ; simp_all +decide;
  have := pow_le_pow_left₀ ( norm_nonneg _ ) this 2;
  rw [ mul_pow, norm_sub_sq_real ] at this;
  nlinarith [ S.hα_pos, S.hm_pos, S.hL_pos, mul_le_mul_of_nonneg_left S.hm_le_L S.hα_pos.le, mul_le_mul_of_nonneg_left S.hm_le_L S.hm_pos.le, mul_le_mul_of_nonneg_left S.hm_le_L S.hL_pos.le ]

/-
When ρ ≤ 1 the gradient step does not increase the distance to x*.
-/
lemma gradient_step_norm_le (x : E) (hρ : S.ρ ≤ 1) :
    ‖(x - S.α • S.grad_f x) - S.x_star‖ ≤ ‖x - S.x_star‖ := by
  nlinarith [ S.gradient_step_sq_bound x, norm_nonneg ( x - S.α • S.grad_f x - S.x_star ), norm_nonneg ( x - S.x_star ) ]

/-
**One-step bound** for the noisy Langevin iteration.

If the noise satisfies ‖ξ‖ ≤ ασ and the contraction factor ρ ≤ 1, then

  ‖step x ξ − x*‖² ≤ ρ ‖x − x*‖² + 2ασ ‖x − x*‖ + 2α²σ².
-/
theorem langevin_step_bound (x ξ : E)
    (hξ : ‖ξ‖ ≤ S.α * S.σ) (hρ : S.ρ ≤ 1) :
    ‖S.step x ξ - S.x_star‖ ^ 2 ≤
      S.ρ * ‖x - S.x_star‖ ^ 2 +
        2 * (S.α * S.σ) * ‖x - S.x_star‖ +
        2 * (S.α * S.σ) ^ 2 := by
  -- Apply the norm_add_sq_real formula:v +‖² =v‖² + 2⟪v,⟫_ℝ +ξ‖².
  have h_norm_add_sq : ‖(x - S.α • S.grad_f x - S.x_star) + ξ‖ ^ 2 = ‖x - S.α • S.grad_f x - S.x_star‖ ^ 2 + 2 * ⟪x - S.α • S.grad_f x - S.x_star, ξ⟫_ℝ + ‖ξ‖ ^ 2 := by
    exact norm_add_pow_two_real (x - S.α • S.grad_f x - S.x_star) ξ
  refine le_trans ?_ ( h_norm_add_sq.le.trans ?_ );
  · rw [ show S.step x ξ - S.x_star = ( x - S.α • S.grad_f x - S.x_star ) + ξ by rw [ LangevinSetup.step ] ; abel1 ];
  · refine' add_le_add ( add_le_add _ _ ) _;
    · convert S.gradient_step_sq_bound x using 1;
    · refine' le_trans ( mul_le_mul_of_nonneg_left ( real_inner_le_norm _ _ ) zero_le_two ) _;
      simpa only [ mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( mul_le_mul ( gradient_step_norm_le S x hρ ) hξ ( by positivity ) ( by positivity ) ) zero_le_two;
    · exact le_trans ( pow_le_pow_left₀ ( norm_nonneg _ ) hξ 2 ) ( le_mul_of_one_le_left ( sq_nonneg _ ) ( by norm_num ) )

end LangevinSetup
