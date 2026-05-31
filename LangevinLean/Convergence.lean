/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LangevinLean.StepBound

/-!
# Langevin Dynamics: Convergence

We prove:

1. **Contraction condition** (`contraction_condition`):
   α < 2m/L² implies ρ < 1.

2. **ρ is nonneg** (`ρ_nonneg`):
   ρ = 1 − 2αm + α²L² ≥ 0 always (since m ≤ L).

3. **Linear recurrence bound** (`linear_recurrence_bound`):
   If a(n+1) ≤ ρ a(n) + c with 0 ≤ ρ < 1 and c ≥ 0, then
   a(n) ≤ ρⁿ a(0) + c/(1−ρ).

4. **Langevin convergence** (`langevin_convergence`):
   Under the contraction condition, the Langevin iterates satisfy

     ‖x_k − x*‖² ≤ ρ_eff^k · ‖x₀ − x*‖² + noiseRadius

   where ρ_eff = (1+ρ)/2 < 1 is the effective contraction rate and
   noiseRadius = 4α²σ²(2−ρ)/(1−ρ)² is the asymptotic noise ball.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LangevinSetup

variable (S : LangevinSetup E)

/-! ### Contraction condition -/

/-
If α < 2m/L² then the contraction factor ρ = 1 − 2αm + α²L² is strictly less than 1.
-/
theorem contraction_condition (hα : S.α < 2 * S.m / S.L ^ 2) : S.ρ < 1 := by
  unfold LangevinSetup.ρ at *;
  rw [ lt_div_iff₀ ] at hα <;> nlinarith [ S.hα_pos, S.hL_pos, S.hm_pos ]

/-
ρ ≤ 1 when α ≤ 2m/L².
-/
lemma ρ_le_one (hα : S.α ≤ 2 * S.m / S.L ^ 2) : S.ρ ≤ 1 := by
  rw [ le_div_iff₀ ( pow_pos S.hL_pos 2 ) ] at hα;
  unfold LangevinSetup.ρ; nlinarith [ S.hα_pos, S.hm_pos, S.hL_pos ] ;

/-
ρ = 1 − 2αm + α²L² ≥ 0 because m ≤ L.
Proof: ρ = (1 − αm)² + α²(L² − m²) ≥ 0.
-/
theorem ρ_nonneg : 0 ≤ S.ρ := by
  unfold LangevinSetup.ρ; nlinarith [ pow_two_nonneg ( S.α * S.L - 1 ), S.hL_pos, S.hm_pos, S.hα_pos, S.hσ_nonneg, S.hm_le_L ] ;

end LangevinSetup

/-! ### General linear-recurrence bound -/

/-
If a real sequence satisfies a(n+1) ≤ ρ·a(n) + c with 0 ≤ ρ < 1 and c ≥ 0,
then a(n) ≤ ρⁿ·a(0) + c/(1−ρ).
-/
theorem linear_recurrence_bound {ρ c : ℝ} {a : ℕ → ℝ}
    (hρ_nn : 0 ≤ ρ) (hρ_lt : ρ < 1) (hc_nn : 0 ≤ c)
    (_ha_nn : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) ≤ ρ * a n + c) :
    ∀ n, a n ≤ ρ ^ n * a 0 + c / (1 - ρ) := by
  intro n;
  induction' n with n ih;
  · exact le_add_of_le_of_nonneg ( by norm_num ) ( div_nonneg hc_nn ( by linarith ) );
  · convert le_trans ( hrec n ) ( add_le_add ( mul_le_mul_of_nonneg_left ih hρ_nn ) le_rfl ) using 1 ; ring_nf;
    grind

/-! ### Scaled Young's inequality -/

/-
Scaled Young's inequality: 2ab ≤ ε a² + b²/ε for ε > 0.
(Follows from (√ε · a − b/√ε)² ≥ 0.)
-/
lemma scaled_young {a b ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + b ^ 2 / ε := by
  rw [ add_div', le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( a * ε - b ) ]

/-! ### Main convergence theorem -/

namespace LangevinSetup

variable (S : LangevinSetup E)

/-
Absorbing the cross-term 2ασ‖x−x*‖ via Young's inequality converts the
quadratic step bound into a linear recurrence in ‖x−x*‖².
-/
lemma step_to_linear_recurrence (x ξ : E)
    (hξ : ‖ξ‖ ≤ S.α * S.σ) (hρ_lt : S.ρ < 1) (hρ_le : S.ρ ≤ 1) :
    ‖S.step x ξ - S.x_star‖ ^ 2 ≤
      S.ρ_eff * ‖x - S.x_star‖ ^ 2 + S.c_linear := by
  -- Apply scaled_young with a = ‖x - x*‖, b = ασ, ε = (1 - ρ) / 2.
  have h_young : 2 * ‖x - S.x_star‖ * (S.α * S.σ) ≤ ((1 - S.ρ) / 2) * ‖x - S.x_star‖ ^ 2 + 2 * (S.α * S.σ) ^ 2 / (1 - S.ρ) := by
    rw [ add_div', le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( ( 1 - S.ρ ) / 2 * ‖x - S.x_star‖ - S.α * S.σ ) ];
  convert le_trans ( LangevinSetup.langevin_step_bound S x ξ hξ hρ_le ) _ using 1;
  convert add_le_add_left h_young ( S.ρ * ‖x - S.x_star‖ ^ 2 + 2 * ( S.α * S.σ ) ^ 2 ) using 1 ; ring;
  unfold LangevinSetup.ρ_eff LangevinSetup.c_linear; ring_nf;
  nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 - S.ρ ) ≠ 0 ) ( S.α ^ 2 * S.σ ^ 2 ) ]

/-
ρ_eff is nonneg.
-/
lemma ρ_eff_nonneg (hρ_nn : 0 ≤ S.ρ) : 0 ≤ S.ρ_eff := by
  exact div_nonneg ( add_nonneg zero_le_one hρ_nn ) zero_le_two

/-
ρ_eff < 1 when ρ < 1.
-/
lemma ρ_eff_lt_one (hρ_lt : S.ρ < 1) : S.ρ_eff < 1 := by
  exact div_lt_one ( by linarith ) |>.2 ( by linarith )

/-
c_linear is nonneg.
-/
lemma c_linear_nonneg (hρ_lt : S.ρ < 1) : 0 ≤ S.c_linear := by
  refine' div_nonneg ( mul_nonneg _ _ ) ( sub_nonneg.2 hρ_lt.le );
  · positivity;
  · grind

/-
The noise radius equals c_linear / (1 − ρ_eff).
-/
lemma noiseRadius_eq (_hρ_lt : S.ρ < 1) :
    S.noiseRadius = S.c_linear / (1 - S.ρ_eff) := by
  unfold LangevinSetup.noiseRadius LangevinSetup.c_linear LangevinSetup.ρ_eff;
  grind

/-
**Langevin convergence.**

Under the contraction condition (ρ < 1), the Langevin iterates converge
geometrically to a noise-dependent ball:

  ‖x_k − x*‖² ≤ ρ_eff^k · ‖x₀ − x*‖² + noiseRadius

where ρ_eff = (1 + ρ)/2 and noiseRadius = 4α²σ²(2 − ρ)/(1 − ρ)².
-/
theorem langevin_convergence (x₀ : E) (noise : ℕ → E)
    (hnoise : ∀ k, ‖noise k‖ ≤ S.α * S.σ)
    (hρ_lt : S.ρ < 1) :
    ∀ k, ‖S.iterate x₀ noise k - S.x_star‖ ^ 2 ≤
      S.ρ_eff ^ k * ‖x₀ - S.x_star‖ ^ 2 + S.noiseRadius := by
  -- By the linear_recurrence_bound theorem, we have:
  have h_linear_recurrence : ∀ n, ‖S.iterate x₀ noise n - S.x_star‖ ^ 2 ≤ S.ρ_eff ^ n * ‖x₀ - S.x_star‖ ^ 2 + S.c_linear / (1 - S.ρ_eff) := by
    have h_linear_recurrence : ∀ n, ‖S.iterate x₀ noise (n + 1) - S.x_star‖ ^ 2 ≤ S.ρ_eff * ‖S.iterate x₀ noise n - S.x_star‖ ^ 2 + S.c_linear := by
      exact fun n => S.step_to_linear_recurrence _ _ ( hnoise n ) hρ_lt ( by linarith );
    intro n;
    induction' n with n ih;
    · simp +decide [ LangevinSetup.iterate ];
      exact div_nonneg ( LangevinSetup.c_linear_nonneg S hρ_lt ) ( sub_nonneg.2 ( LangevinSetup.ρ_eff_lt_one S hρ_lt |> le_of_lt ) );
    · convert le_trans ( h_linear_recurrence n ) ( add_le_add ( mul_le_mul_of_nonneg_left ih ( S.ρ_eff_nonneg ( S.ρ_nonneg ) ) ) le_rfl ) using 1 ; ring_nf;
      nlinarith [ inv_mul_cancel_left₀ ( show ( 1 - S.ρ_eff ) ≠ 0 by linarith [ S.ρ_eff_lt_one hρ_lt ] ) ( S.c_linear ) ];
  simpa only [ LangevinSetup.noiseRadius_eq S hρ_lt ] using h_linear_recurrence

end LangevinSetup
