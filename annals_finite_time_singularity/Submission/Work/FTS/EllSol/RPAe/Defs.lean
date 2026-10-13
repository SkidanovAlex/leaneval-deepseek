/-
# `Work.FTS.EllSol.RPAe` — shared vocabulary for the level-`4` angular Poincaré estimate

This module fixes the constant of the level-`4` angular Poincaré estimate `ropPoincareAe` in the
form needed by the per-`z` comparison lemmas
(`Submission/Work/FTS/EllSol/RPAe/groupBoundF.lean`, `.../groupBoundP.lean`): it is the sum of the
five constants of the two single-slice estimates of the `VopAux` chapter,

* `VopAux.sliceF_le_sliceV K`  (`sliceF K α u ≤ C · sliceF K α u''`),
* `VopAux.sliceF_deriv_le_sliceV K` (`sliceF K α u' ≤ C · sliceF K α u''`),

for `K = 0,…,4`, plus one.  The lemmas below record positivity and domination of each individual
constant by `sliceCs`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllSol.VopAux.sliceF_le_sliceV
import Submission.Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.RPAe

set_option autoImplicit false

/-- The constant of the level-`4` angular Poincaré estimate: the sum of the ten single-slice
constants of the levels `0 ≤ K ≤ 4` (both the `∂_θ²`- and the `∂_θ`-case) plus one. -/
def sliceCs : ℝ :=
  (∑ K ∈ Finset.range 5,
      (Classical.choose (VopAux.sliceF_le_sliceV K)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV K))) + 1

theorem sliceCs_pos : 0 < sliceCs := by
  have h1 : 0 < ∑ K ∈ Finset.range 5,
      (Classical.choose (VopAux.sliceF_le_sliceV K)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV K)) := by
    refine Finset.sum_pos (fun K _ => ?_) ⟨0, Finset.mem_range.mpr (by norm_num)⟩
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).1
    linarith
  rw [sliceCs]; linarith

theorem one_le_sliceCs : (1 : ℝ) ≤ sliceCs := by
  have h0 : 0 ≤ ∑ K ∈ Finset.range 5,
      (Classical.choose (VopAux.sliceF_le_sliceV K)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV K)) :=
    Finset.sum_nonneg fun K _ => by
      have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).1
      have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).1
      linarith
  rw [sliceCs]; linarith

theorem le_sliceCs_F (K : ℕ) (hK : K ≤ 4) :
    Classical.choose (VopAux.sliceF_le_sliceV K) ≤ sliceCs := by
  have hmem : K ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ i ∈ Finset.range 5,
      0 ≤ Classical.choose (VopAux.sliceF_le_sliceV i)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV i) := fun i _ => by
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV i)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV i)).1
    linarith
  have hsingle : Classical.choose (VopAux.sliceF_le_sliceV K)
      ≤ ∑ i ∈ Finset.range 5, (Classical.choose (VopAux.sliceF_le_sliceV i)
          + Classical.choose (VopAux.sliceF_deriv_le_sliceV i)) := by
    refine le_trans ?_ (Finset.single_le_sum hnonneg hmem)
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).1
    linarith
  rw [sliceCs]
  linarith

theorem le_sliceCs_D (K : ℕ) (hK : K ≤ 4) :
    Classical.choose (VopAux.sliceF_deriv_le_sliceV K) ≤ sliceCs := by
  have hmem : K ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ i ∈ Finset.range 5,
      0 ≤ Classical.choose (VopAux.sliceF_le_sliceV i)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV i) := fun i _ => by
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV i)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV i)).1
    linarith
  have hsingle : Classical.choose (VopAux.sliceF_deriv_le_sliceV K)
      ≤ ∑ i ∈ Finset.range 5, (Classical.choose (VopAux.sliceF_le_sliceV i)
          + Classical.choose (VopAux.sliceF_deriv_le_sliceV i)) := by
    refine le_trans ?_ (Finset.single_le_sum hnonneg hmem)
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).1
    linarith
  rw [sliceCs]
  linarith

/-- The `VopAux` single-slice `∂_θ²`-estimate, in the form used by the per-`z` comparison. -/
theorem sliceF_le_sliceV_apply (K : ℕ) (α : ℝ) (u : ℝ → ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hintV : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hintVm : ∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      VopAux.sliceF K α u
        ≤ Classical.choose (VopAux.sliceF_le_sliceV K)
          * VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
  (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).2 α u hα0 hα1 hu hlim0 hlim1 hintV hintVm

/-- The `VopAux` single-slice `∂_θ`-estimate, in the form used by the per-`z` comparison. -/
theorem sliceF_deriv_le_sliceV_apply (K : ℕ) (α : ℝ) (u : ℝ → ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hintV : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hintVm : ∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
      VopAux.sliceF K α (deriv u)
        ≤ Classical.choose (VopAux.sliceF_deriv_le_sliceV K)
          * VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
  (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).2 α u hα0 hα1 hu hlim0 hlim1 hintV hintVm

end Work.FTS.EllSol.RPAe
