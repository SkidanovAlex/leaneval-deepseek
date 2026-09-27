import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Surf.exists_smooth_approx_C1
import Submission.Work.Surf.transfer_hypotheses
import Submission.Work.Surf.ncard_zeros_persist
import Submission.Work.Surf.ncard_rayMeet_persist

/-!
# The smooth reduction, assembled from its four ingredients

`Work.Surf.smooth_reduction_alt` is the same statement as `Work.Surf.smooth_reduction` (a `C¹` map
satisfying the cut/ray hypotheses can be replaced by a smooth map with the same two counts), proved by
assembling the four ingredients that are proved separately:

* `Work.Surf.exists_smooth_approx_C1` — the `C¹` map is approximated, with its derivative, by a smooth
  map on the compact square;
* `Work.Surf.transfer_hypotheses` — the hypotheses persist under a small `C¹` perturbation;
* `Work.Surf.ncard_zeros_persist` — the number of zeros is unchanged;
* `Work.Surf.ncard_rayMeet_persist` — the number of boundary ray-meeting points is unchanged (and the
  new ray-meeting set is finite).
-/

namespace Work.Surf

open Set

noncomputable section

/-- The unit square is compact. -/
lemma isCompact_sqBox'' : IsCompact sqBox := by
  have h : sqBox = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [sqBox, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i; fin_cases i
      · exact h.1
      · exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr (isCompact_univ_pi fun _ => isCompact_Icc)

/-- **Approximation of a `C¹` map by a smooth one without changing the two counts** (assembled
version). -/
theorem smooth_reduction_alt
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBdry, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (hfin : (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).Finite) :
    ∃ F' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F' ∧
      (∀ x ∈ Work.Surf.sqBdry, F' x ≠ 0) ∧
      (∀ x ∈ Work.Surf.sqBox, F' x = 0 → Function.Surjective (fderiv ℝ F' x)) ∧
      (∀ x ∈ Work.Surf.sqBdry, ‖F' x‖ < ‖v‖) ∧
      (∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F' x = r • v) →
        ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1))) ∧
      (∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F' x = r • v) →
        ((x 1 = 0 ∨ x 1 = 1) →
          Work.Drive.det2 (fderiv ℝ F' x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
        ((x 0 = 0 ∨ x 0 = 1) →
          Work.Drive.det2 (fderiv ℝ F' x (EuclideanSpace.single 1 1)) v ≠ 0)) ∧
      (Work.Surf.rayMeet F' v ∩ Work.Surf.sqBdry).Finite ∧
      ({x ∈ Work.Surf.sqBox | F x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard =
        ({x ∈ Work.Surf.sqBox | F' x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard ∧
      (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard =
        (Work.Surf.rayMeet F' v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    transfer_hypotheses F hF hbdry hreg hv hbig hcorner htrans_bdry hfin
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := ncard_zeros_persist F hF hbdry hreg
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ :=
    ncard_rayMeet_persist F hF hbdry hv hbig hcorner htrans_bdry hfin
  set m : ℝ := min (min δ₁ δ₂) δ₃ with hmdef
  have hmpos : 0 < m := lt_min (lt_min hδ₁pos hδ₂pos) hδ₃pos
  -- the approximation, at scale `m / 2`
  obtain ⟨F', hF'sm, happrox⟩ :=
    exists_smooth_approx_C1 F hF isCompact_sqBox'' (by linarith : (0 : ℝ) < m / 2)
  have hclo : ∀ x ∈ sqBox, ‖F' x - F x‖ < m := by
    intro x hx
    have h := (happrox x hx).1
    linarith
  have hclod : ∀ x ∈ sqBox, ‖fderiv ℝ F' x - fderiv ℝ F x‖ < m := by
    intro x hx
    have h := (happrox x hx).2
    linarith
  have hm₁ : m ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hm₂ : m ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm₃ : m ≤ δ₃ := min_le_right _ _
  have hF'1 : ContDiff ℝ 1 F' := hF'sm.of_le (by simp)
  obtain ⟨hb', hr', hbig', hc', ht', hfi'⟩ := hδ₁ F' hF'1
    (fun x hx => lt_of_lt_of_le (hclo x hx) hm₁) (fun x hx => lt_of_lt_of_le (hclod x hx) hm₁)
  obtain ⟨hZfin, hZnc⟩ := hδ₂ F' hF'1
    (fun x hx => lt_of_lt_of_le (hclo x hx) hm₂) (fun x hx => lt_of_lt_of_le (hclod x hx) hm₂)
  obtain ⟨hRfin, hRnc⟩ := hδ₃ F' hF'1
    (fun x hx => lt_of_lt_of_le (hclo x hx) hm₃) (fun x hx => lt_of_lt_of_le (hclod x hx) hm₃)
  exact ⟨F', hF'sm, hb', hr', hbig', hc', ht', hfi', hZnc.symm, hRnc.symm⟩

end

end Work.Surf
