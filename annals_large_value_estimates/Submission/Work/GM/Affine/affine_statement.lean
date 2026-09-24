import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.crude_case
import Submission.Work.GM.Affine.fine_bridge
import Submission.Work.GM.Affine.ghat_T1_bound

/-! Guidance from the project lead (the requester):

This is a whole AREA (GM §9: Lemma 9.2 and Prop 9.1), self-contained Fourier analysis on ℝ.
See `NOTES.md` in this directory for the route, and `Submission/GM/Interfaces.lean` for the
statement. The proof splits into `crude_case` (Mbig ≳ T, elementary, via Poisson summation)
and `fine_case` (GM's Lemma 9.2 + the downward induction), glued here by a case split on
whether `Mbig ≥ T^{3/2}`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem affine_statement : Submission.GM.AffineStatement := by
  intro C₀ K hC₀ hK c δ hδ
  have hδ4 : (0:ℝ) < δ / 4 := by linarith
  have hδ0 : (0:ℝ) < δ := hδ
  obtain ⟨Cfine, hCfine_pos, hfine⟩ :=
    fine_bridge (fun C₀' K' T₀' hC₀' hK' hT₀' => ghat_T1_bound hC₀' hK' hT₀')
      (C₀ := C₀) (K := K) (T₀ := 1) hC₀ hK le_rfl c δ hδ
  set Ccr : ℝ := 2 ^ 22 * (1 + c 4 (δ / 4)) ^ 2 * (1 + c 2 (δ / 4)) ^ 2 * (C₀ + K + 1) with hCcr
  refine ⟨max Ccr Cfine + 1, by positivity, ?_⟩
  intro T hT f hf_cont hf_nn hsupp hdec Mbig M₁ M₂ M₃ hM₁ hM₁' hM₂ hM₂' hM₃ hM₃'
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  have hU : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hf_nn
  have hV : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  have hTδ1 : (1:ℝ) ≤ T ^ δ := one_le_rpow_of_one_le hT hδ
  have hRHS : (0:ℝ) ≤ max Ccr Cfine + 1 := by positivity
  have hRHS1 : (1:ℝ) ≤ max Ccr Cfine + 1 := by
    have := le_max_right Ccr Cfine
    linarith [hCfine_pos]
  by_cases hf0 : supf f = 0
  · have hfz : ∀ u, f u = 0 := eq_zero_of_supf_eq_zero hf_cont hcs hf_nn hf0
    have hzero : ∀ u, Submission.GM.affineSum K M₁ M₂ M₃ f u = 0 := by
      intro u
      simp [Submission.GM.affineSum, hfz]
    have hint : ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 = 0 := by
      simp [hzero]
    rw [hint]
    exact mul_nonneg (mul_nonneg hRHS (Real.rpow_nonneg hT0 δ))
      (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hV))
  · have hsup_pos : 0 < supf f := by
      rcases lt_or_eq_of_le (supf_nonneg hf_cont hcs hf_nn) with h | h
      · exact h
      · exact absurd h.symm hf0
    have hcj : 0 ≤ c 4 (δ / 4) :=
      decay_const_nonneg (f := f) (T := T) (sup := supf f)
        (fun j ε hε ξ hξ => hdec j ε hε ξ hξ) hT hsup_pos hδ4
    have hc2 : 0 ≤ c 2 (δ / 4) :=
      decay_const_nonneg (f := f) (T := T) (sup := supf f)
        (fun j ε hε ξ hξ => hdec j ε hε ξ hξ) hT hsup_pos hδ4
    have hCcr_nonneg : 0 ≤ Ccr := by rw [hCcr]; positivity
    by_cases hbig : T ^ ((3:ℝ)/2) ≤ Mbig
    · have hMbig1 : 1 ≤ Mbig := le_trans (Real.one_le_rpow hT (by norm_num)) hbig
      have hMbig_pos : 0 < Mbig := lt_of_lt_of_le zero_lt_one hMbig1
      have hcrude := crude_case (c := c) (K := K) (C₀ := C₀) (T := T) (Mbig := Mbig) (f := f)
        (j := 4) (ε := δ / 4) hC₀ hK (by norm_num) hδ4 hT0 hf_cont hf_nn hcs hsupp hdec
        hcj hc2 hM₁ hM₂ hM₃ hM₁' hM₂' hM₃' hMbig1
      have hexp : 4 + 4 * (δ / 4) + 2 * ((4:ℕ):ℝ) = 12 + δ := by ring
      have hexp2 : 6 - 2 * ((4:ℕ):ℝ) = (-2:ℝ) := by norm_num
      rw [hexp, hexp2] at hcrude
      have hmax := max_crude_le_target (T := T) (Mbig := Mbig)
        (U := ∫ u, f u) (V := ∫ u, (f u) ^ 2) (δ := δ) hT hMbig_pos hU hV hδ0 hbig
      refine le_trans hcrude ?_
      have hCle : Ccr ≤ max Ccr Cfine + 1 := by
        exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
      calc Ccr * max (Mbig ^ 6 * (∫ u, f u) ^ 2)
              (T ^ (12 + δ) * (∫ u, f u) ^ 2 * Mbig ^ (-2:ℝ))
          ≤ (max Ccr Cfine + 1) * (T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 +
              Mbig ^ 4 * ∫ u, (f u) ^ 2)) := by
            exact mul_le_mul hCle hmax (by positivity) hRHS
        _ = (max Ccr Cfine + 1) * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 +
              Mbig ^ 4 * ∫ u, (f u) ^ 2) := by ring
    · push_neg at hbig
      have hMle : Mbig ≤ T ^ 4 := by
        have h1 : T ^ ((3:ℝ)/2) ≤ T ^ (4:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
        have h4 : T ^ (4:ℝ) = T ^ 4 := Real.rpow_natCast T 4
        rw [h4] at h1
        exact le_trans (le_of_lt hbig) h1
      have hfin := hfine T hT f hf_cont hf_nn hsupp hdec Mbig M₁ M₂ M₃
        hM₁ hM₁' hM₂ hM₂' hM₃ hM₃' hMle
      refine le_trans hfin ?_
      have hCle : Cfine ≤ max Ccr Cfine + 1 := by
        exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
      have h2 : Cfine * T ^ δ ≤ (max Ccr Cfine + 1) * T ^ δ :=
        mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg hT0 δ)
      exact mul_le_mul_of_nonneg_right h2
        (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hV))



end

end Work.GM.Affine
