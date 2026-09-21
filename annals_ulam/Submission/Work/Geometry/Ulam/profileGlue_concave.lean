import Mathlib
import Submission.Work.Geometry.Ulam.profileGlue_continuous
import Submission.Work.Geometry.Ulam.concave_glue
import Submission.Work.Geometry.Ulam.right_profile_endpoint_deriv

namespace Commons.Geometry.Ulam

open Set
open scoped Topology ContDiff

noncomputable section

/-- The left-branch profile has the expected one-sided derivative at `0`,
by reflection of the right-branch statement. -/
lemma leftProfile_hasDerivWithinAt_zero
    (r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    HasDerivWithinAt (leftProfile r) (deriv r (Real.pi / 2) / r (Real.pi / 2))
      (Set.Icc (-(r 0)) 0) 0 := by
  have hright := rightProfile_hasDerivWithinAt_zero r hη hηsmall hδ hr_cont hr_nhds
    hr_pos hr_lower hr_deriv_bound
  have hneg : HasDerivWithinAt (fun t : ℝ => -t) (-1) (Set.Icc (-(r 0)) 0) 0 := by
    simpa using (hasDerivAt_neg 0).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc (-(r 0)) 0) (Set.Ici 0) := by
    intro t ht
    exact neg_nonneg.mpr ht.2
  have hright' : HasDerivWithinAt (rightProfile r)
      (- deriv r (Real.pi / 2) / r (Real.pi / 2)) (Set.Ici 0) (-0) := by
    simpa using hright
  have hcomp : HasDerivWithinAt (fun t : ℝ => rightProfile r (-t))
      ((- deriv r (Real.pi / 2) / r (Real.pi / 2)) * (-1)) (Set.Icc (-(r 0)) 0) 0 :=
    HasDerivWithinAt.comp (x := 0) (s' := Set.Ici 0) (s := Set.Icc (-(r 0)) 0)
      (h₂ := rightProfile r) (h := fun t : ℝ => -t)
      (h₂' := - deriv r (Real.pi / 2) / r (Real.pi / 2)) (h' := -1)
      hright' hneg hmaps
  change HasDerivWithinAt (fun t : ℝ => rightProfile r (-t))
    (deriv r (Real.pi / 2) / r (Real.pi / 2)) (Set.Icc (-(r 0)) 0) 0
  convert hcomp using 1
  ring

lemma profileGlue_concaveOn_corrected
    (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8) (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2))
    (hseam : 0 ≤ deriv r (Real.pi / 2) / r (Real.pi / 2) +
      deriv R (Real.pi / 2) / R (Real.pi / 2)) :
    ConcaveOn ℝ (Set.Icc (-(r 0)) (R 0)) (profileGlue R r) := by
  have hleft_conc : ConcaveOn ℝ (Set.Icc (-(r 0)) 0) (profileGlue R r) :=
    (leftProfile_concaveOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      hr_second_bound).congr (by
        intro t ht
        exact (profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
          hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end ht).symm)
  have hright_conc : ConcaveOn ℝ (Set.Icc 0 (R 0)) (profileGlue R r) :=
    (rightProfile_concaveOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      hR_second_bound).congr (by
        intro t ht
        exact (profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower
          hR_deriv_bound ht).symm)
  have hcont := profileGlue_continuousOn R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
    hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end
  have hleft_diff : DifferentiableWithinAt ℝ (profileGlue R r) (Set.Icc (-(r 0)) 0) 0 := by
    have hraw := leftProfile_hasDerivWithinAt_zero r hη hηsmall hδ hr_cont hr_nhds
      hr_pos hr_lower hr_deriv_bound
    have hdiff := hraw.differentiableWithinAt
    refine hdiff.congr ?_ ?_
    · intro t ht
      exact (profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
        hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end ht)
    · have hmem0 : (0 : ℝ) ∈ Set.Icc (-(r 0)) 0 :=
        ⟨neg_nonpos.mpr (le_of_lt (left_zero_pos r hr_pos)), le_rfl⟩
      exact (profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
        hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end hmem0)
  have hright_diff : DifferentiableWithinAt ℝ (profileGlue R r) (Set.Icc 0 (R 0)) 0 := by
    have hraw := rightProfile_hasDerivWithinAt_zero R hη hηsmall hδ hR_cont hR_nhds
      hR_pos hR_lower hR_deriv_bound
    have hmono := hraw.mono (Set.Icc_subset_Ici_self (a := R 0) (b := 0))
    have hdiff := hmono.differentiableWithinAt
    refine hdiff.congr ?_ ?_
    · intro t ht
      exact (profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower
        hR_deriv_bound ht)
    · have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (R 0) :=
        ⟨le_rfl, le_of_lt (right_zero_pos R hR_pos)⟩
      exact (profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower
        hR_deriv_bound hmem0)
  have hseam_order := profileGlue_seam_inequality R r hη hηsmall hδ hR_cont hr_cont
    hR_nhds hr_nhds hR_pos hr_pos hR_lower hr_lower hR_deriv_bound hr_deriv_bound hseam
  have hRderiv : derivWithin (profileGlue R r) (Set.Icc 0 (R 0)) 0 =
      derivWithin (rightProfile R) (Set.Icc 0 (R 0)) 0 := by
    apply derivWithin_congr
    · intro t ht
      exact profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
    · have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (R 0) :=
        ⟨le_rfl, le_of_lt (right_zero_pos R hR_pos)⟩
      exact profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hmem0
  have hLderiv : derivWithin (profileGlue R r) (Set.Icc (-(r 0)) 0) 0 =
      derivWithin (leftProfile r) (Set.Icc (-(r 0)) 0) 0 := by
    apply derivWithin_congr
    · intro t ht
      exact profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
        hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end ht
    · have hmem0 : (0 : ℝ) ∈ Set.Icc (-(r 0)) 0 :=
        ⟨neg_nonpos.mpr (le_of_lt (left_zero_pos r hr_pos)), le_rfl⟩
      exact profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
        hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end hmem0
  have hseam_order' : derivWithin (profileGlue R r) (Set.Icc 0 (R 0)) 0 ≤
      derivWithin (profileGlue R r) (Set.Icc (-(r 0)) 0) 0 := by
    rw [hRderiv, hLderiv]
    exact hseam_order
  exact concaveOn_Icc_of_concaveOn_left_right_of_seam
    (neg_lt_zero.mpr (left_zero_pos r hr_pos)) (right_zero_pos R hR_pos)
    hcont hleft_conc hright_conc hleft_diff hright_diff hseam_order'

end

end Commons.Geometry.Ulam
