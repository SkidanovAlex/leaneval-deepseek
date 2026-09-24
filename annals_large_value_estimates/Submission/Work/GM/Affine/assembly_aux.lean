import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Affine.setup

/-!
# GM §9: auxiliary lemmas for the assembly of `AffineStatement`

Elementary structural facts used when assembling the crude and fine cases of GM Proposition 9.1
into `Submission.GM.AffineStatement`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `SuppHyp` plus continuity gives compact support. -/
lemma hasCompactSupport_of_suppHyp {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ}
    (hsupp : SuppHyp C₀ f) : HasCompactSupport f := by
  have hsub : Function.support f ⊆ Set.Icc (1 / C₀) C₀ := fun u hu => hsupp u hu
  have h1 : 1 / C₀ ≤ C₀ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  refine HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub

/-- A continuous non-negative function with zero supremum vanishes identically. -/
lemma eq_zero_of_supf_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) (h0 : supf f = 0) : ∀ u, f u = 0 := by
  intro u
  have := le_supf hf hcs u
  rw [h0] at this
  exact le_antisymm this (hnn u)

/-- If the decay hypothesis holds at a point `ξ ≠ 0` for a function with positive supremum,
then the (real) constant `c j ε` is non-negative. -/
lemma decay_const_nonneg {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} {sup : ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * sup)
    (hT : 1 ≤ T) (hsup : 0 < sup) {j : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 ≤ c j ε := by
  have h := hdec j ε hε 1 one_ne_zero
  have hnorm : (0:ℝ) ≤ ‖Fhat f 1‖ := norm_nonneg _
  have hpos : 0 < T ^ ε * (T / |(1:ℝ)|) ^ j * sup := by
    have h1 : (0:ℝ) < T ^ ε := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0:ℝ) < (T / |(1:ℝ)|) ^ j := by
      apply pow_pos
      rw [abs_one, div_one]; linarith
    exact mul_pos (mul_pos h1 h2) hsup
  by_contra hneg
  push_neg at hneg
  have : c j ε * T ^ ε * (T / |(1:ℝ)|) ^ j * sup < 0 := by
    have : c j ε * (T ^ ε * (T / |(1:ℝ)|) ^ j * sup) < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    linarith [this]
  linarith [h, hnorm]

end

end Work.GM.Affine

namespace Work.GM.Affine

noncomputable section

/-- For `T ≥ 1` and `Mbig ≥ T^{3/2}` we have `T^12 ≤ Mbig^8`. -/
lemma rpow_twelve_le {T Mbig : ℝ} (hT : 1 ≤ T) (h : T ^ ((3:ℝ)/2) ≤ Mbig) :
    T ^ (12:ℝ) ≤ Mbig ^ (8:ℝ) := by
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  have hstep : (T ^ ((3:ℝ)/2)) ^ (8:ℕ) ≤ Mbig ^ (8:ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hT0 _) h 8
  have h1 : (T ^ ((3:ℝ)/2)) ^ (8:ℕ) = T ^ (12:ℝ) := by
    rw [← Real.rpow_natCast (T ^ ((3:ℝ)/2)) 8, ← Real.rpow_mul hT0]
    norm_num
  calc T ^ (12:ℝ) = (T ^ ((3:ℝ)/2)) ^ (8:ℕ) := h1.symm
    _ ≤ Mbig ^ (8:ℕ) := hstep
    _ = Mbig ^ (8:ℝ) := (Real.rpow_natCast Mbig 8).symm

/-- `1 ≤ T^δ` for `T ≥ 1`, `δ > 0`. -/
lemma one_le_rpow_of_one_le {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) : 1 ≤ T ^ δ :=
  Real.one_le_rpow hT hδ.le

/-- The crude bound's two terms are both dominated by `T^δ (Mbig^6 U^2 + Mbig^4 V)`. -/
lemma max_crude_le_target {T Mbig U V δ : ℝ} (hT : 1 ≤ T) (hMbig : 0 < Mbig)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 < δ) (h : T ^ ((3:ℝ)/2) ≤ Mbig) :
    max (Mbig ^ 6 * U ^ 2) (T ^ (12 + δ) * U ^ 2 * Mbig ^ (-2:ℝ))
      ≤ T ^ δ * (Mbig ^ 6 * U ^ 2 + Mbig ^ 4 * V) := by
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  have hTδ : (1:ℝ) ≤ T ^ δ := one_le_rpow_of_one_le hT hδ
  have hM2 : (0:ℝ) < Mbig ^ 2 := by positivity
  have h12 : T ^ (12:ℝ) ≤ Mbig ^ (8:ℝ) := rpow_twelve_le hT h
  have hmain : T ^ (12 + δ) * U ^ 2 * Mbig ^ (-2:ℝ) ≤ T ^ δ * (Mbig ^ 6 * U ^ 2) := by
    have hsplit : T ^ (12 + δ) = T ^ (12:ℝ) * T ^ δ :=
      Real.rpow_add (lt_of_lt_of_le zero_lt_one hT) 12 δ
    rw [hsplit]
    have hMneg : Mbig ^ (-2:ℝ) = (Mbig ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hMbig)]
      congr 1
      exact Real.rpow_natCast Mbig 2
    rw [hMneg]
    have hkey : T ^ (12:ℝ) * (Mbig ^ 2)⁻¹ ≤ Mbig ^ 6 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hM2]
      have h8 : Mbig ^ (8:ℝ) = Mbig ^ 6 * Mbig ^ 2 := by
        rw [← Real.rpow_natCast Mbig 6, ← Real.rpow_natCast Mbig 2,
          ← Real.rpow_add hMbig]
        norm_num
      rw [← h8]
      exact h12
    calc T ^ (12:ℝ) * T ^ δ * U ^ 2 * (Mbig ^ 2)⁻¹
        = T ^ δ * U ^ 2 * (T ^ (12:ℝ) * (Mbig ^ 2)⁻¹) := by ring
      _ ≤ T ^ δ * U ^ 2 * Mbig ^ 6 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = T ^ δ * (Mbig ^ 6 * U ^ 2) := by ring
  refine max_le ?_ ?_
  · have h1 : Mbig ^ 6 * U ^ 2 ≤ T ^ δ * (Mbig ^ 6 * U ^ 2) := by
      nth_rewrite 1 [← one_mul (Mbig ^ 6 * U ^ 2)]
      exact mul_le_mul_of_nonneg_right hTδ (by positivity)
    exact le_trans h1 (by
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hTδ)
      exact le_add_of_nonneg_right (by positivity))
  · exact le_trans hmain (by
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hTδ)
      exact le_add_of_nonneg_right (by positivity))

end

end Work.GM.Affine
