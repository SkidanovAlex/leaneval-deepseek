/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions and elementary bounds for the `I₄` boundary term

This module owns the vocabulary of
`Work.FTS.EllipticEst.Honest.I4BoundaryVanish` (the vanishing of the `I₄` boundary term
`(sin θ/cos³θ)·P(θ)²·sin(2θ)^{-η}` of the honest `I₄` upper bound, `η = 99/100`).

* `s4 θ = sin(2θ)^{-η}` — the angular weight (alias of `AngSecond.sig`);
* `P4 ψ θ = cos²θ · ψ'(θ)` — the quantity whose square appears in the boundary term;
* `G4 ψ θ = ((P4 ψ)'(θ)/cos θ)² · s4 θ` — the honest square integrability of which is the
  hypothesis `hB` of the boundary lemma;
* `K4` — the explicit constant `(π/2)³·(4/π)^{-η}` of the coefficient bound `coef_le`.

The elementary bounds (`cos_ge_lin`, `cos_le_lin`, `sin_two_ge`, `cos_sq_mul_sin2_rpow_le`,
`coef_le`) are the pointwise inputs of the rate estimate and of the final assembly.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I4BV

set_option autoImplicit false

/-! ## Vocabulary -/

/-- The angular weight `s4 θ = sin(2θ)^{-η}`, `η = 99/100`. -/
def s4 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))

/-- The explicit constant `(π/2)³ · (4/π)^{-η}` of the coefficient bound. -/
def K4 : ℝ := (Real.pi / 2) ^ 3 * (4 / Real.pi) ^ (-(99 / 100 : ℝ))

/-- `P4 ψ θ = cos²θ · ψ'(θ)`. -/
def P4 (ψ : ℝ → ℝ) (θ : ℝ) : ℝ := (Real.cos θ) ^ 2 * deriv ψ θ

/-- `G4 ψ θ = (deriv (P4 ψ) θ / cos θ)² · s4 θ`, the integrand of the hypothesis `hB`. -/
def G4 (ψ : ℝ → ℝ) (θ : ℝ) : ℝ := (deriv (P4 ψ) θ / Real.cos θ) ^ 2 * s4 θ

theorem s4_eq (θ : ℝ) : s4 θ = (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := rfl

theorem P4_eq (ψ : ℝ → ℝ) (θ : ℝ) : P4 ψ θ = (Real.cos θ) ^ 2 * deriv ψ θ := rfl

theorem G4_eq (ψ : ℝ → ℝ) (θ : ℝ) :
    G4 ψ θ = (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') θ / Real.cos θ) ^ 2 * s4 θ := rfl

/-! ## Elementary pointwise facts -/

theorem s4_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < s4 θ := by
  rw [s4]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem s4_nonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 ≤ s4 θ := le_of_lt (s4_pos hθ)

/-- On the open angular interval the angular weight is at least `1`. -/
theorem one_le_s4 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ s4 θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hz : -(99 / 100 : ℝ) ≤ 0 := by norm_num
  have h := Real.rpow_le_rpow_of_nonpos hsin hle hz
  simpa [s4, Real.one_rpow] using h

/-- The linear lower bound `(2/π)(π/2-θ) ≤ cos θ` on `(0, π/2)`. -/
theorem cos_ge_lin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
  have hu0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
  have hu1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
  have h := Real.mul_le_sin hu0 hu1
  rwa [Real.sin_pi_div_two_sub] at h

/-- The linear upper bound `cos θ ≤ π/2 - θ` on `(0, π/2)`. -/
theorem cos_le_lin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have hu0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have h := Real.sin_le (le_of_lt hu0)
  rwa [Real.sin_pi_div_two_sub] at h

/-- The linear lower bound `(4/π)(π/2-θ) ≤ sin(2θ)` for `θ ∈ (π/4, π/2)`. -/
theorem sin_two_ge {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have hu0 : 0 ≤ 2 * (Real.pi / 2 - θ) := by linarith [hθ.2]
  have hu1 : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith [hθ.1]
  have h := Real.mul_le_sin hu0 hu1
  have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  rw [hsin] at h
  have heq : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = 4 / Real.pi * (Real.pi / 2 - θ) := by ring
  linarith [h, heq.symm.le, heq.le]

/-- **The elementary pointwise bound** `cos²θ·sin(2θ)^η ≤ 2^η (π/2-θ)^{2+η}` on `(0, π/2)`. -/
theorem cos_sq_mul_sin2_rpow_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)
      ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, hpi])
  have hτ : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  rw [Real.sin_two_mul]
  have hmul : (2 * Real.sin θ * Real.cos θ) ^ (99 / 100 : ℝ)
      = 2 ^ (99 / 100 : ℝ) * (Real.sin θ) ^ (99 / 100 : ℝ)
        * (Real.cos θ) ^ (99 / 100 : ℝ) := by
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hs) (le_of_lt hc),
        Real.mul_rpow (by norm_num) hs]
  rw [hmul]
  have hsplit : (Real.cos θ) ^ 2 * (Real.cos θ) ^ (99 / 100 : ℝ)
      = (Real.cos θ) ^ (2 + 99 / 100 : ℝ) := by
    rw [← Real.rpow_ofNat (Real.cos θ) 2, ← Real.rpow_add hc]
  have hstep1 : (Real.cos θ) ^ 2
        * (2 ^ (99 / 100 : ℝ) * (Real.sin θ) ^ (99 / 100 : ℝ)
          * (Real.cos θ) ^ (99 / 100 : ℝ))
      = 2 ^ (99 / 100 : ℝ) * (Real.sin θ) ^ (99 / 100 : ℝ)
        * (Real.cos θ) ^ (2 + 99 / 100 : ℝ) := by
    rw [← hsplit]; ring
  rw [hstep1]
  have hsinle : (Real.sin θ) ^ (99 / 100 : ℝ) ≤ 1 :=
    Real.rpow_le_one hs hsin1 (by norm_num)
  have hcosle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_lin hθ
  have hcospow : (Real.cos θ) ^ (2 + 99 / 100 : ℝ)
      ≤ (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt hc) hcosle (by norm_num)
  calc 2 ^ (99 / 100 : ℝ) * (Real.sin θ) ^ (99 / 100 : ℝ)
        * (Real.cos θ) ^ (2 + 99 / 100 : ℝ)
      ≤ 2 ^ (99 / 100 : ℝ) * 1 * (Real.cos θ) ^ (2 + 99 / 100 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hc) _)
        exact mul_le_mul_of_nonneg_left hsinle (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 ^ (99 / 100 : ℝ) * 1 * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hcospow
        positivity
    _ = 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) := by ring

/-- **The coefficient bound.**  For `θ ∈ (π/4, π/2)`,
`sin θ/cos³θ · sin(2θ)^{-η} ≤ K4 · (π/2-θ)^{-(3+η)}`. -/
theorem coef_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    Real.sin θ / (Real.cos θ) ^ 3 * s4 θ
      ≤ K4 * (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, hpi], hθ.2⟩
  have hcge : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := cos_ge_lin hI
  have hApos : 0 < (2 / Real.pi) * (Real.pi / 2 - θ) := by positivity
  have hs4pos : 0 < s4 θ := s4_pos hI
  have hs4 : s4 θ ≤ (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * (Real.pi / 2 - θ) ^ (-(99 / 100 : ℝ)) := by
    have h1 : s4 θ ≤ ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ (-(99 / 100 : ℝ)) := by
      rw [s4]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (sin_two_ge hθ) (by norm_num)
    rwa [Real.mul_rpow (by positivity) (le_of_lt hu)] at h1
  have hcinv : ((Real.cos θ) ^ 3)⁻¹ ≤ (Real.pi / 2) ^ 3 * (Real.pi / 2 - θ) ^ (-(3 : ℝ)) := by
    have h1 : ((Real.cos θ) ^ 3)⁻¹ ≤ (((2 / Real.pi) * (Real.pi / 2 - θ)) ^ 3)⁻¹ := by
      rw [inv_le_inv₀ (pow_pos hc 3) (pow_pos hApos 3)]
      exact pow_le_pow_left₀ (le_of_lt hApos) hcge 3
    have h2 : (((2 / Real.pi) * (Real.pi / 2 - θ)) ^ 3)⁻¹
        = (Real.pi / 2) ^ 3 * (Real.pi / 2 - θ) ^ (-(3 : ℝ)) := by
      have hb : (((2 / Real.pi) * (Real.pi / 2 - θ)) ^ (3 : ℝ))
          = ((2 / Real.pi) * (Real.pi / 2 - θ)) ^ 3 := Real.rpow_ofNat _ 3
      rw [← hb, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 / Real.pi) * (Real.pi / 2 - θ)) 3,
          Real.mul_rpow (by positivity) (le_of_lt hu)]
      congr 1
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← inv_pow, inv_div]
    linarith [h1, h2.le, h2.ge]
  calc Real.sin θ / (Real.cos θ) ^ 3 * s4 θ
      = Real.sin θ * ((Real.cos θ) ^ 3)⁻¹ * s4 θ := by rw [div_eq_mul_inv]
    _ ≤ 1 * ((Real.pi / 2) ^ 3 * (Real.pi / 2 - θ) ^ (-(3 : ℝ)))
          * ((4 / Real.pi) ^ (-(99 / 100 : ℝ)) * (Real.pi / 2 - θ) ^ (-(99 / 100 : ℝ))) := by
        apply mul_le_mul _ hs4 (le_of_lt hs4pos) (by positivity)
        exact mul_le_mul (Real.sin_le_one θ) hcinv (by positivity) (by norm_num)
    _ = ((Real.pi / 2) ^ 3 * (4 / Real.pi) ^ (-(99 / 100 : ℝ)))
          * ((Real.pi / 2 - θ) ^ (-(3 : ℝ)) * (Real.pi / 2 - θ) ^ (-(99 / 100 : ℝ))) := by ring
    _ = K4 * (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ)) := by
        rw [K4, ← Real.rpow_add hu]
        ring_nf

end Work.FTS.EllipticEst.I4BV
