import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Convex.deriv2_nonneg_of_convexOn_real

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- Derivative of `x ↦ exp (-(V x)) / V' x` where `V' x ≠ 0`. -/
lemma hasDerivAt_exp_neg_div_deriv (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {x : ℝ}
    (hx : deriv V x ≠ 0) :
    HasDerivAt (fun y => Real.exp (-(V y)) / deriv V y)
      (-(Real.exp (-(V x))) -
        deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) x := by
  have hV_at : HasDerivAt V (deriv V x) x :=
    (hV.differentiable (by norm_num) x).hasDerivAt
  have hneg : HasDerivAt (fun y => -(V y)) (-(deriv V x)) x := hV_at.neg
  have hexp : HasDerivAt (fun y => Real.exp (-(V y)))
      (Real.exp (-(V x)) * (-(deriv V x))) x := hneg.exp
  have hdV : HasDerivAt (deriv V) (deriv (deriv V) x) x :=
    (hV.differentiable_deriv_two x).hasDerivAt
  have hdVinv : HasDerivAt (fun y => (deriv V y)⁻¹)
      (-(deriv (deriv V) x) / (deriv V x) ^ 2) x := hdV.inv hx
  have h := hexp.mul hdVinv
  rw [show ((fun y => Real.exp (-(V y))) * (fun y => (deriv V y)⁻¹))
        = (fun y => Real.exp (-(V y)) / deriv V y) from
        funext (fun y => by rw [Pi.mul_apply, div_eq_mul_inv])] at h
  refine h.congr_deriv ?_
  field_simp
  ring

/-- Improper integrability at `+∞` of `V'' e^{-V} / (V')²` when `V` is convex, `C²` and
`V' ≥ c > 0` on the half-line. -/
theorem integrableOn_deriv2_exp_neg_div_sq_Ici (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V)
    (hVc : ConvexOn ℝ Set.univ V) {b c : ℝ} (hc : 0 < c)
    (hVb : ∀ x, b ≤ x → c ≤ deriv V x) :
    IntegrableOn (fun x => deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2)
      (Set.Ici b) volume := by
  set f : ℝ → ℝ :=
    fun x => deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2 with hf_def
  set g : ℝ → ℝ := fun x => Real.exp (-(V x)) / deriv V x with hg_def
  set gp : ℝ → ℝ :=
    fun x => -(Real.exp (-(V x))) -
      deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2 with hgp_def
  -- smoothness facts
  have hVdiff : ∀ x, DifferentiableAt ℝ V x := fun x => hV.differentiable (by norm_num) x
  have h2nonneg : ∀ x, 0 ≤ deriv (deriv V) x :=
    Commons.Analysis.Convex.deriv2_nonneg_of_convexOn_real hVc hVdiff
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    rw [hf_def]
    exact div_nonneg (mul_nonneg (h2nonneg x) (Real.exp_nonneg _)) (sq_nonneg _)
  have hdd : Continuous (deriv (deriv V)) := by
    have h : Continuous (iteratedDeriv 2 V) := hV.continuous_iteratedDeriv 2 (by norm_num)
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one] at h
    exact h
  have hdV_cont : Continuous (deriv V) := hV.continuous_deriv (by norm_num)
  have hexp_cont : Continuous (fun x => Real.exp (-(V x))) :=
    Real.continuous_exp.comp hV.continuous.neg
  have hderiv_pos : ∀ x, b ≤ x → 0 < deriv V x :=
    fun x hx => lt_of_lt_of_le hc (hVb x hx)
  have hf_contOn : ContinuousOn f (Ici b) := by
    have hnum : ContinuousOn (fun x => deriv (deriv V) x * Real.exp (-(V x))) (Ici b) :=
      hdd.continuousOn.mul hexp_cont.continuousOn
    have hden : ContinuousOn (fun x => (deriv V x) ^ 2) (Ici b) :=
      hdV_cont.continuousOn.pow 2
    have hne : ∀ x ∈ Ici b, (deriv V x) ^ 2 ≠ 0 := by
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hderiv_pos x hx))
    have h := hnum.div hden hne
    rw [show ((fun x => deriv (deriv V) x * Real.exp (-(V x))) / (fun x => (deriv V x) ^ 2))
          = (fun x => deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) from
          funext (fun x => by rw [Pi.div_apply])] at h
    simpa only [hf_def] using h
  have hgp_contOn : ContinuousOn gp (Ici b) := by
    rw [hgp_def]
    exact hexp_cont.continuousOn.neg.sub hf_contOn
  -- integral bound
  have hbound : ∀ N, b ≤ N → ∫ x in b..N, f x ≤ g b := by
    intro N hN
    have hderiv : ∀ x ∈ uIcc b N, HasDerivAt g (gp x) x := by
      intro x hx
      rw [uIcc_of_le hN] at hx
      have hxne : deriv V x ≠ 0 := ne_of_gt (hderiv_pos x hx.1)
      have h := hasDerivAt_exp_neg_div_deriv V hV hxne
      rw [hg_def, hgp_def]
      simpa only [] using h
    have hint_gp : IntervalIntegrable gp volume b N := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hN]
      exact hgp_contOn.mono Icc_subset_Ici_self
    have hFTC : ∫ x in b..N, gp x = g N - g b :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_gp
    have hf_eq : ∀ x ∈ Icc b N, f x = -gp x - Real.exp (-(V x)) := by
      intro x hx
      simp only [hf_def, hgp_def]
      ring
    have hcongr : ∫ x in b..N, f x = ∫ x in b..N, (-gp x - Real.exp (-(V x))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hN] at hx
      exact hf_eq x hx
    have hsplit :
        ∫ x in b..N, (-gp x - Real.exp (-(V x)))
          = -(∫ x in b..N, gp x) - (∫ x in b..N, Real.exp (-(V x))) := by
      rw [intervalIntegral.integral_sub (f := fun x => -gp x)
            (g := fun x => Real.exp (-(V x))) hint_gp.neg
            (hexp_cont.intervalIntegrable b N), intervalIntegral.integral_neg]
    have hgN : 0 ≤ g N := by
      rw [hg_def]
      exact div_nonneg (Real.exp_nonneg _) (le_of_lt (hderiv_pos N hN))
    have hI : 0 ≤ ∫ x in b..N, Real.exp (-(V x)) :=
      intervalIntegral.integral_nonneg_of_forall hN (fun x => Real.exp_nonneg _)
    calc ∫ x in b..N, f x
        = ∫ x in b..N, (-gp x - Real.exp (-(V x))) := hcongr
      _ = -(∫ x in b..N, gp x) - (∫ x in b..N, Real.exp (-(V x))) := hsplit
      _ = -((g N) - (g b)) - (∫ x in b..N, Real.exp (-(V x))) := by rw [hFTC]
      _ ≤ g b := by linarith
  -- assemble
  have hmain : IntegrableOn f (Ioi b) volume := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
      (μ := volume) (b := fun i : ℕ => b + (i : ℝ)) (f := f) (g b) b ?_ ?_ ?_
    · intro i
      have hbi : b ≤ b + (i : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg i)
      have hcont : ContinuousOn f (Icc b (b + (i : ℝ))) := hf_contOn.mono Icc_subset_Ici_self
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    · exact tendsto_atTop_add_const_left atTop b tendsto_natCast_atTop_atTop
    · refine Filter.Eventually.of_forall (fun i => ?_)
      have hbi : b ≤ b + (i : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg i)
      have h1 : ∫ x in b..b + (i : ℝ), ‖f x‖ = ∫ x in b..b + (i : ℝ), f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact Real.norm_of_nonneg (hf_nonneg x)
      rw [h1]
      exact hbound (b + (i : ℝ)) hbi
  exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume) (f := f) (b := b)).mpr hmain

end Commons.Analysis.Convex