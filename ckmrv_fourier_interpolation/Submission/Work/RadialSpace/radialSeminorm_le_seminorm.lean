import Mathlib
import Submission.Work.RadialSpace.RadialSeminorm

/-!
# The radial seminorm is bounded by the Schwartz seminorm

For a (not necessarily radial) Schwartz function `G` on `R^n`, the `k`-th radial
seminorm of order `l`, defined through the derivatives of the profile of `G`
along the coordinate axis, is bounded by the ordinary `(k, l)` Schwartz seminorm.

The key point is that the `l`-th derivative of the profile of `G` at `r` is the
`l`-th Fréchet derivative of `G` at `realIncl r` evaluated on the `l`-tuple
`(realIncl 1, …, realIncl 1)`, and `realIncl 1` is a unit vector.  Hence the
directional derivative along the axis is controlled by the operator norm of the
full iterated Fréchet derivative, which is what the Schwartz seminorm bounds.
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation

variable {n : ℕ} [NeZero n]

/-- The `l`-th derivative of the profile of `G` at `r` is the `l`-th Fréchet
derivative of `G` at `realIncl r` applied to the `l`-tuple of copies of the unit
vector `realIncl 1`. -/
lemma iteratedDeriv_profile_eq_iteratedFDeriv {n : ℕ} [NeZero n]
    (G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (l : ℕ) (r : ℝ) :
    iteratedDeriv l (profile (⇑G)) r =
      (iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)) (fun _ : Fin l => realIncl (n := n) 1) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hcomp : profile (⇑G) = (⇑G) ∘ (⇑(realInclCLM n)) := by
    funext s; rw [Function.comp_apply, realInclCLM_apply]; rfl
  rw [hcomp]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (realInclCLM n) (G.smooth (l : ℕ∞)) r le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, realInclCLM_apply]

/-- The `l`-th radial derivative of a Schwartz function at `r` is bounded by the
operator norm of its `l`-th Fréchet derivative at `realIncl r`. -/
lemma norm_iteratedDeriv_profile_le {n : ℕ} [NeZero n]
    (G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (l : ℕ) (r : ℝ) :
    ‖iteratedDeriv l (profile (⇑G)) r‖ ≤ ‖iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)‖ := by
  rw [iteratedDeriv_profile_eq_iteratedFDeriv]
  calc ‖(iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)) (fun _ : Fin l => realIncl (n := n) 1)‖
      ≤ ‖iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)‖ * ∏ i : Fin l, ‖realIncl (n := n) 1‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)‖ * 1 ^ l := by
        rw [Finset.prod_const, Finset.card_fin, Work.Sampling.realIncl_norm_one]
    _ = ‖iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) r)‖ := by rw [one_pow, mul_one]

theorem radialSeminorm_le_seminorm {n : ℕ} [NeZero n] (G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (k l : ℕ) :
    Work.RadialSpace.radialSeminorm k l (⇑G) ≤
      ENNReal.ofReal ((SchwartzMap.seminorm ℂ k l) G) := by
  unfold radialSeminorm
  refine iSup_le fun x => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm : ‖realIncl (n := n) ‖x‖‖ = ‖x‖ := by
    rw [Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg x)]
  calc ‖x‖ ^ k * ‖iteratedDeriv l (profile (⇑G)) ‖x‖‖
      ≤ ‖realIncl (n := n) ‖x‖‖ ^ k * ‖iteratedFDeriv ℝ l (⇑G) (realIncl (n := n) ‖x‖)‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_profile_le G l ‖x‖)
          (pow_nonneg (norm_nonneg x) k)
    _ ≤ SchwartzMap.seminorm ℂ k l G := SchwartzMap.le_seminorm ℂ k l G _

end Work.RadialSpace
