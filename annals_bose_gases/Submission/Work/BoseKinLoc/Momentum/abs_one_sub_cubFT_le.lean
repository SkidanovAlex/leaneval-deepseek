import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The momentum bound `|1 − cubFT v| ≤ min 2 (3‖v‖²/8)`

`cubFT v = ∫_{acube 1} cos⟪v,x⟫ dx`, so `1 − cubFT v = ∫_{acube 1}(1 − cos⟪v,x⟫) ≥ 0`.
On the unit cube `‖x‖² ≤ 3/4`, and `1 − cos t ≤ t²/2`, so the integrand is at most
`‖v‖²‖x‖²/2 ≤ 3‖v‖²/8`; integrating over the cube of volume `1` gives the claimed
`3‖v‖²/8`.  The bound `2` is `abs_one_sub_cubFT_le_two`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- On the unit cube, `‖z‖² ≤ 3/4`. -/
private lemma norm_sq_le_three_quarters_of_mem_acube_one {z : ℝ³} (hz : z ∈ acube 1) :
    ‖z‖ ^ 2 ≤ 3 / 4 := by
  rw [EuclideanSpace.norm_sq_eq]
  have h : ∀ m : Fin 3, ‖z.ofLp m‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    intro m
    have hm := (mem_acube_iff 1 z).mp hz m
    rw [Set.mem_Icc] at hm
    have h1 : ‖z.ofLp m‖ ≤ 1 / 2 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    nlinarith [h1, norm_nonneg (z.ofLp m)]
  calc ∑ m : Fin 3, ‖z.ofLp m‖ ^ 2 ≤ ∑ _m : Fin 3, (1 / 4 : ℝ) :=
        Finset.sum_le_sum (fun m _ => h m)
    _ = 3 / 4 := by norm_num

/-- Pointwise cosine bound on the unit cube: `1 − cos⟪Q,z⟫ ≤ 3‖Q‖²/8` for `z ∈ acube 1`. -/
private lemma one_sub_cos_inner_le_of_mem {Q z : ℝ³} (hz : z ∈ acube 1) :
    1 - Real.cos (inner ℝ Q z) ≤ 3 * ‖Q‖ ^ 2 / 8 := by
  have hz' : ‖z‖ ^ 2 ≤ 3 / 4 := norm_sq_le_three_quarters_of_mem_acube_one hz
  have hcos : 1 - Real.cos (inner ℝ Q z) ≤ (inner ℝ Q z) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := inner ℝ Q z)]
  have hinner : |inner ℝ Q z| ≤ ‖Q‖ * ‖z‖ := by
    refine abs_le.mpr ⟨?_, real_inner_le_norm Q z⟩
    have h := real_inner_le_norm (-Q) z
    rw [inner_neg_left, norm_neg] at h
    linarith
  have h2 : (inner ℝ Q z) ^ 2 ≤ 3 * ‖Q‖ ^ 2 / 4 := by
    have hb := abs_le.mp hinner
    nlinarith [hb.1, hb.2, hz', sq_nonneg ‖Q‖, norm_nonneg Q, norm_nonneg z]
  linarith

/-- **The momentum bound** `|1 − cubFT v| ≤ min 2 (3‖v‖²/8)`. -/
theorem abs_one_sub_cubFT_le (v : EuclideanSpace ℝ (Fin 3)) :
    |1 - cubFT v| ≤ min 2 (3 * ‖v‖ ^ 2 / 8) := by
  refine le_min (abs_one_sub_cubFT_le_two v) ?_
  rw [abs_of_nonneg (one_sub_cubFT_nonneg v), one_sub_cubFT_eq]
  have hfin : (volume : Measure ℝ³) (acube 1) ≠ ⊤ := by
    rw [volume_acube_one]; exact ENNReal.one_ne_top
  have hconst : IntegrableOn (fun _ : ℝ³ => (1 : ℝ)) (acube 1) volume :=
    integrableOn_const (μ := (volume : Measure ℝ³)) hfin
  have hcos : IntegrableOn (fun z : ℝ³ => Real.cos (inner ℝ v z)) (acube 1) volume :=
    integrableOn_cos v
  have hmono : (∫ z in acube 1, (1 - Real.cos (inner ℝ v z)))
      ≤ ∫ z in acube 1, (3 * ‖v‖ ^ 2 / 8 : ℝ) :=
    setIntegral_mono_on (hconst.sub hcos) (integrableOn_const (μ := (volume : Measure ℝ³)) hfin)
      (acube_measurable 1) (fun z hz => one_sub_cos_inner_le_of_mem hz)
  calc ∫ z in acube 1, (1 - Real.cos (inner ℝ v z))
      ≤ ∫ z in acube 1, (3 * ‖v‖ ^ 2 / 8 : ℝ) := hmono
    _ = 3 * ‖v‖ ^ 2 / 8 := by rw [setIntegral_const, real_volume_acube_one, one_smul]

end Work.BoseKinLoc.Momentum
