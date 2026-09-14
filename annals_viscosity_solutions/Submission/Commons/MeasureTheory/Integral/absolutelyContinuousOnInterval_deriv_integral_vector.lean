import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open Filter Set MeasureTheory
open scoped Topology

namespace Commons.MeasureTheory.Integral

/-- If `f : ℝ → X` is absolutely continuous on `uIcc a b` and `g : X → Y` satisfies a Lipschitz
bound with constant `K` (with respect to the distances), then `g ∘ f` is absolutely continuous on
`uIcc a b`. -/
theorem absolutelyContinuousOnInterval_comp_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : ℝ → X} {g : X → Y} {a b : ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ x y, dist (g x) (g y) ≤ K * dist x y)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδpos, fun E hE hlt => ?_⟩
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, K * dist (f (E.2 i).1) (f (E.2 i).2) :=
        Finset.sum_le_sum fun i _ => hg _ _
    _ = K * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (K + 1) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
        gcongr; linarith
    _ < (K + 1) * (ε / (K + 1)) :=
        mul_lt_mul_of_pos_left (hδ E hE hlt) (by positivity)
    _ = ε := by field_simp

/-- If `f : ℝ → F` is absolutely continuous on `uIcc a b`, then so is `x ↦ ⟪v, f x⟫` for any
`v : F`. -/
theorem absolutelyContinuousOnInterval_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : ℝ → F} {a b : ℝ} {v : F}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => inner ℝ v (f x)) a b := by
  refine absolutelyContinuousOnInterval_comp_of_dist_le (g := fun y => inner ℝ v y)
    (K := ‖v‖) (norm_nonneg v) ?_ hf
  intro x y
  rw [Real.dist_eq, ← inner_sub_right, dist_eq_norm]
  exact abs_real_inner_le_norm v (x - y)

theorem absolutelyContinuousOnInterval_deriv_integral_vector {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e := stdOrthonormalBasis ℝ F
  let c : Fin (Module.finrank ℝ F) → ℝ → ℝ := fun i x => inner ℝ (e i) (f x)
  have hc : ∀ i, AbsolutelyContinuousOnInterval (c i) a b := fun i =>
    absolutelyContinuousOnInterval_inner (v := e i) hf
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc a b →
      deriv f x = ∑ i, (deriv (c i) x) • e i := by
    filter_upwards [BoundedVariationOn.ae_differentiableAt_of_mem_uIcc hf.boundedVariationOn]
      with x hx hxIoc
    have hxIcc : x ∈ uIcc a b := uIoc_subset_uIcc hxIoc
    have hdx : HasDerivAt f (deriv f x) x := (hx hxIcc).hasDerivAt
    have key : ∀ i, deriv (c i) x = inner ℝ (e i) (deriv f x) := fun i => by
      have h1 : HasDerivAt (fun y => inner ℝ (e i) (f y))
          (inner ℝ (e i) (deriv f x) + inner ℝ (0 : F) (f x)) x :=
        HasDerivAt.inner ℝ (hasDerivAt_const x (e i)) hdx
      rw [show (inner ℝ (e i) (deriv f x) + inner ℝ (0 : F) (f x))
            = inner ℝ (e i) (deriv f x) by simp] at h1
      exact h1.deriv
    simp_rw [key]
    exact (e.sum_repr' (deriv f x)).symm
  have hint : ∀ i, IntervalIntegrable (deriv (c i)) volume a b := fun i =>
    AbsolutelyContinuousOnInterval.intervalIntegrable_deriv (hc i)
  have hscaled : ∀ i, IntervalIntegrable (fun x => (deriv (c i) x) • e i) volume a b :=
    fun i => intervalIntegrable_iff.mpr ((hint i).def'.smul_const (e i))
  have hInt : (∫ x in a..b, ∑ i, (deriv (c i) x) • e i)
      = ∑ i, (∫ x in a..b, deriv (c i) x) • e i := by
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun i x => (deriv (c i) x) • e i) (fun i _ => hscaled i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h2 := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.toSpanSingleton ℝ (e i)) (hint i)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply] using h2
  rw [intervalIntegral.integral_congr_ae hderiv, hInt]
  have hFTC : ∀ i, ∫ x in a..b, deriv (c i) x = c i b - c i a := fun i =>
    AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (hc i)
  simp_rw [hFTC]
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib]
  rw [e.sum_repr' (f b), e.sum_repr' (f a)]

end Commons.MeasureTheory.Integral