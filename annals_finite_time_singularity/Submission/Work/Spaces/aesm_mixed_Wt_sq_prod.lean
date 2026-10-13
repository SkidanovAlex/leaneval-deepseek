import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-! ## The open quadrant on which the integrand is jointly continuous

`(D_z^j D_θ^i g · W)²` is jointly continuous on the open quadrant `(0,∞) × (0,π/2)`:
the mixed derivative is smooth there because `g` is smooth on a neighbourhood of the
closed quadrant, and the weight `W = w · w_θ` is continuous there because both
`z ↦ (1+z)²/z²` and `θ ↦ sin(2θ)^{-γ/2}` are continuous away from their singularities.
The complement of the open quadrant inside `[0,∞) × [0,π/2]` is a finite union of
segments, hence null; this is what lets us discard it. -/

/-- The open set `(0,∞) × (0,π/2)`. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma Qd_subset_nbhU : Qd ⊆ nbhU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- `sin (2θ)` is positive for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

private lemma contOn_uncurry_sinpow_Qd (p : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => (Real.sin (2 * y.2)) ^ p) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _y hy => Or.inl (ne_of_gt (sin_two_pos_Qd hy.2)))

private lemma contOn_uncurry_w_Qd : ContinuousOn (fun y : ℝ × ℝ => w y.1) Qd := by
  simp only [w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun y hy => ?_)
  exact pow_ne_zero 2 (ne_of_gt hy.1)

private lemma contOn_uncurry_Wt_Qd (α : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => Wt α y.1 y.2) Qd := by
  simp only [Wt, wTheta]
  exact contOn_uncurry_w_Qd.mul (contOn_uncurry_sinpow_Qd (-(gam α / 2)))

/-! ## `[0,∞)` and `[0,π/2]` have the same measure as their interiors -/

private lemma restrict_Iz_eq_aesm :
    volume.restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

private lemma restrict_Iθ_eq_aesm :
    volume.restrict Iθ = volume.restrict (Set.Ioo 0 (π/2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-! ## The requested a.e. strong measurability -/

theorem aesm_mixed_Wt_sq_prod (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j i : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- Joint continuity on the open quadrant.
  have hcont : ContinuousOn
      (fun y : ℝ × ℝ => (mixed j i g y.1 y.2 * Wt α y.1 y.2) ^ 2) Qd :=
    ((((SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm i) j).continuousOn).mono
        Qd_subset_nbhU).mul (contOn_uncurry_Wt_Qd α)).pow 2
  -- Replace the closed intervals by their interiors.
  rw [restrict_Iz_eq_aesm, restrict_Iθ_eq_aesm]
  -- The complement of the open quadrant is null for the product measure.
  have hQc : ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))) Qdᶜ = 0 := by
    rw [Measure.prod_restrict, Measure.restrict_apply (isOpen_Qd.measurableSet.compl)]
    change (volume.prod volume) (Qdᶜ ∩ Qd) = 0
    rw [Set.compl_inter_self, measure_empty]
  have hae : ∀ᵐ y ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))), y ∈ Qd := by
    rw [ae_iff]
    exact hQc
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact hcont.aestronglyMeasurable isOpen_Qd.measurableSet

end Work.Spaces
