import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Commons.Topology.Curve

theorem argument_lift_of_close
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1)
    {p : ℂ} (hp : p ∉ Set.range f) {θ : ℝ → ℝ} (hθc : Continuous θ)
    (hθper : ∀ t, θ (t + 1) = θ t)
    (hθrep : ∀ t, f t - p = (‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    {q : ℂ} (hq : ‖q - p‖ < Metric.infDist p (Set.range f) / 2) :
    ∃ θ' : ℝ → ℝ, Continuous θ' ∧ (∀ t, θ' (t + 1) = θ' t) ∧
      ∀ t, f t - q = (‖f t - q‖ : ℂ) * Complex.exp ((θ' t : ℂ) * Complex.I) := by
  -- q is strictly closer to p than half the distance from p to the curve, hence `f t - q`
  -- is a positive multiple (real part `> 0`) of `f t - p` at every `t`.
  have hbound : ∀ t, ‖q - p‖ < ‖f t - p‖ / 2 := by
    intro t
    have h1 : Metric.infDist p (Set.range f) ≤ ‖f t - p‖ := by
      have h := Metric.infDist_le_dist_of_mem (x := p) (s := Set.range f)
        (y := f t) (Set.mem_range_self t)
      rw [dist_eq_norm, norm_sub_rev] at h
      exact h
    linarith [hq]
  have hne : ∀ t, f t - p ≠ 0 := by
    intro t
    have hpos : 0 < ‖f t - p‖ := by
      have hb := hbound t
      have hnn : (0 : ℝ) ≤ ‖q - p‖ := norm_nonneg _
      linarith
    exact norm_pos_iff.mp hpos
  -- the correction factor relating the two arguments
  set W : ℝ → ℂ := fun t => (f t - q) / (f t - p) with hW
  have hWapply : ∀ t, W t = (f t - q) / (f t - p) := fun t => by simp [hW]
  have hWcont : Continuous W := by
    rw [hW]
    exact (hf.sub continuous_const).div (hf.sub continuous_const) hne
  have hWre : ∀ t, 0 < (W t).re := by
    intro t
    rw [hWapply t]
    have hfp : f t - p ≠ 0 := hne t
    have hnormfp : 0 < ‖f t - p‖ := norm_pos_iff.mpr hfp
    have hc : ‖(q - p) / (f t - p)‖ < 1 / 2 := by
      rw [norm_div, div_lt_iff₀ hnormfp]
      have hb := hbound t
      nlinarith
    have hre : ((q - p) / (f t - p)).re ≤ ‖(q - p) / (f t - p)‖ := Complex.re_le_norm _
    have hsub : (f t - q) / (f t - p) = 1 - (q - p) / (f t - p) := by
      have h1 : f t - q = (f t - p) - (q - p) := by ring
      rw [h1, sub_div, div_self hfp]
    rw [hsub, Complex.sub_re, Complex.one_re]
    linarith
  have hWper : ∀ t, W (t + 1) = W t := by
    intro t
    rw [hWapply, hWapply, hper t]
  have hWmul : ∀ t, (f t - p) * W t = f t - q := by
    intro t
    rw [hWapply t]
    exact mul_div_cancel₀ (f t - q) (hne t)
  have hWexp : ∀ t, (‖W t‖ : ℂ) * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I) = W t :=
    fun t => Complex.norm_mul_exp_arg_mul_I (W t)
  refine ⟨fun t => θ t + Complex.arg (W t), ?_, ?_, ?_⟩
  · -- continuity of the corrected argument
    refine Continuous.add hθc ?_
    rw [continuous_iff_continuousAt]
    intro t
    exact (Complex.continuousAt_arg (Or.inl (hWre t))).comp hWcont.continuousAt
  · -- periodicity
    intro t
    simp only [hθper t, hWper t]
  · -- the representation identity
    intro t
    have hnorm : (‖f t - q‖ : ℂ) = (‖f t - p‖ : ℂ) * (‖W t‖ : ℂ) := by
      rw [← hWmul t, norm_mul, Complex.ofReal_mul]
    have hexp : Complex.exp (((θ t + Complex.arg (W t) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((θ t : ℂ) * Complex.I)
          * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    calc f t - q
        = (f t - p) * W t := (hWmul t).symm
      _ = ((‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) * W t := by
            conv_lhs => rw [hθrep t]
      _ = ((‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
            * ((‖W t‖ : ℂ) * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := by
            conv_lhs => rw [← hWexp t]
      _ = ((‖f t - p‖ : ℂ) * (‖W t‖ : ℂ))
            * (Complex.exp ((θ t : ℂ) * Complex.I)
                * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := by ring
      _ = (‖f t - q‖ : ℂ) * Complex.exp (((θ t + Complex.arg (W t) : ℝ) : ℂ) * Complex.I) := by
            conv_rhs => rw [hnorm, hexp]

end Commons.Topology.Curve