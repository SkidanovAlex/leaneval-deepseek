import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB1B.bornGap
import Submission.Work.BoseFixB3.CS.Reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.v_w0_pos_sq` — positivity of `∫ v ω` and `∫ v ω²`

For a nonnegative radial `L¹` potential `v` with compact support, a radial scattering
solution `w = ω` and `0 < a v`, both weighted masses of the scattering profile are
strictly positive:

`0 < ∫ x, v x · ω x`   and   `0 < ∫ x, v x · ω x²`.

## Route

* the first integral is the strict Born gap: `∫ v ω = ∫ v − ∫ v(1−ω) = ∫ v − 8π a v > 0`
  (`Work.BoseFixB1B.integral_mul_chosen_pos`, itself `bornGap` plus `g0_integral`);
* the second is *not* a consequence of the first by monotonicity (`ω² ≤ ω` on `[0,1]`
  goes the wrong way) but it follows from it by a **support** argument: `v·ω ≥ 0`
  everywhere, so `{v·ω ≠ 0}` has positive measure; on that set `v > 0` and `ω ≠ 0`,
  hence `v·ω² ≠ 0`.  Both functions are a.e. nonnegative and integrable
  (`v·ω² ≤ v·ω` a.e. by the a.e. bound `0 ≤ ω ≤ 1` of
  `Submission.BoseGases.scattering_bounds_ae`), so
  `MeasureTheory.integral_pos_iff_support_of_nonneg_ae` converts the support
  inclusion into the strict inequality.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixB3.CS.Pieces

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- **Support criterion for a strictly positive integral.**  If `f ≥ 0` a.e. has strictly
positive integral and `Function.support f ⊆ Function.support g`, with `g ≥ 0` a.e. and both
integrable, then `∫ g > 0`. -/
private lemma integral_pos_of_support_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hfpos : 0 < ∫ x, f x ∂μ) (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ)
    (hg : 0 ≤ᵐ[μ] g) (hgi : Integrable g μ) (hsub : Function.support f ⊆ Function.support g) :
    0 < ∫ x, g x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hg hgi]
  exact lt_of_lt_of_le ((integral_pos_iff_support_of_nonneg_ae hf hfi).mp hfpos)
    (measure_mono hsub)

theorem v_w0_pos_sq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    0 < (∫ x : EuclideanSpace ℝ (Fin 3), v x * Classical.choose h x) ∧
      0 < (∫ x : EuclideanSpace ℝ (Fin 3), v x * (Classical.choose h x) ^ 2) := by
  classical
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  -- the first conjunct: the strict Born gap
  have h1 : 0 < ∫ x : ℝ³, v x * Classical.choose h x :=
    Work.BoseFixB1B.integral_mul_chosen_pos hR hv hv1 hvrad hv_supp h hav
  refine ⟨h1, ?_⟩
  -- a.e. bounds on the scattering solution
  obtain ⟨hw0, hw1⟩ := scattering_bounds_ae hR hv hvrad hv_supp hrad hw
  -- integrability of `v·ω`
  have hv_int : Integrable v := memLp_one_iff_integrable.mp hv1
  have hg0_int : Integrable (fun x : ℝ³ => v x * (1 - Classical.choose h x)) :=
    scatG_integrable hv_supp hw
  have hf_int : Integrable (fun x : ℝ³ => v x * Classical.choose h x) := by
    rw [show (fun x : ℝ³ => v x * Classical.choose h x)
        = fun x : ℝ³ => v x - v x * (1 - Classical.choose h x) from by
      funext x; ring]
    exact hv_int.sub hg0_int
  -- integrability of `v·ω²` by domination with `v·ω`
  have hw_asm : AEStronglyMeasurable (Classical.choose h) :=
    hw.lhs_integrable.aestronglyMeasurable
  have hg_int : Integrable (fun x : ℝ³ => v x * (Classical.choose h x) ^ 2) := by
    refine hf_int.mono' (hv1.aestronglyMeasurable.mul (hw_asm.pow 2)) ?_
    filter_upwards [hw0, hw1] with x hx0 hx1
    have hsq : (Classical.choose h x) ^ 2 ≤ Classical.choose h x := by
      simpa [pow_two] using mul_le_of_le_one_left hx0 hx1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hv x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hsq (hv x)
  -- nonnegativity and support inclusion
  have hf_nn : 0 ≤ᵐ[volume] (fun x : ℝ³ => v x * Classical.choose h x) :=
    hw0.mono fun x hx => mul_nonneg (hv x) hx
  have hg_nn : 0 ≤ᵐ[volume] (fun x : ℝ³ => v x * (Classical.choose h x) ^ 2) :=
    Eventually.of_forall fun x => mul_nonneg (hv x) (sq_nonneg _)
  have hsub : Function.support (fun x : ℝ³ => v x * Classical.choose h x)
      ⊆ Function.support (fun x : ℝ³ => v x * (Classical.choose h x) ^ 2) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    have hwne : Classical.choose h x ≠ 0 := by
      intro h0
      exact hx (by rw [h0, mul_zero])
    rw [show v x * (Classical.choose h x) ^ 2
        = (v x * Classical.choose h x) * Classical.choose h x by ring]
    exact mul_ne_zero hx hwne
  exact integral_pos_of_support_subset h1 hf_nn hf_int hg_nn hg_int hsub

end Work.BoseFixB3.CS.Pieces
