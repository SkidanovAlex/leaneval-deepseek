import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false

/-! Independent copies (renamed with a prime) of the two lemmas of `Pieces/rowsAux.lean` that
the `N₄` row proofs use, so that they do not have to import `rowsAux` (which imports the rows). -/

private lemma ite_sq_nonneg' {c : Prop} [Decidable c] (a : ℝ) :
    0 ≤ (if c then a ^ 2 else (0 : ℝ)) := by
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

theorem aesm_weighted_energy_of_continuousOn' {f : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hsq : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
    exact hc.pow 2
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hsq
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hslice.mono_measure hmono
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
      (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2).aestronglyMeasurable measurableSet_Ioi
  exact h1.mul hw


theorem slot_z_le_HkIntegrand' (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (n : ℕ) (hn : n ≤ k) :
    (Work.Spaces.DzIter n F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1), if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ite_sq_nonneg' _))
  rw [Work.Spaces.HkIntegrand]
  exact le_trans (Finset.single_le_sum
    (f := fun i => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun i _ => sq_nonneg _) hmem) (le_add_of_nonneg_right h2)

theorem continuousOn_uncurry_of_smoothQuad' {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h' := h
  rw [Work.FTS.LocData.SmoothQuad] at h'
  exact h'.continuousOn.mono (fun p hp => by
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

end Work.FTS.Nonlinear.Pieces
