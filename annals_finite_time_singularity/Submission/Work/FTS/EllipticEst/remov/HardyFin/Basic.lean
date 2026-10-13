import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.DivQ.primIntegrable
import Submission.Work.FTS.H2.DivQ.primitiveDerivData
import Submission.Work.FTS.H2.DivQ.hardyIter_tendsto_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Finite-order calculus on `(0,x₁]`

This file redevelops the elementary calculus API of `Submission/Work/FTS/H2/DivQ/vanishAux.lean`
and the first two results of the `DivQ` Hardy-development (`primIntegrable`, `primitiveDerivData`)
with a **finite** smoothness hypothesis `ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)` instead of the
`C^∞` hypothesis `ContDiffOn ℝ ⊤ f (Ioc 0 x₁)` used there.

All statements are of the form "for `j ≤ N`", so that they can be instantiated at `N = k + 2`
in the finite-order Hardy division `Work.FTS.EllipticEst.remov.hardyDiv_fin`.
-/

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Filter Set
open scoped Topology

/-- For `f` of class `C^N` on the open interval `(0,x₁)` and `j ≤ N`, the `j`-th iterated
derivative `iteratedDeriv j f` is continuous on `(0,x₁)`.  (This is the version that applies to
`f/y`, which is only smooth on the open interval.) -/
lemma continuousOn_iteratedDeriv_Ioo_fin' {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁)) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : ContinuousOn (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- For `f` of class `C^N` on the half-open interval `(0,x₁]` and `j ≤ N`, the `j`-th iterated
derivative `iteratedDeriv j f` is continuous on the open interval `(0,x₁)`. -/
lemma continuousOn_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (iteratedDeriv j f) (Set.Ioo 0 x₁) :=
  continuousOn_iteratedDeriv_Ioo_fin' (hf.mono Set.Ioo_subset_Ioc_self) hj

/-- For `f` of class `C^N` on the open interval `(0,x₁)` and `j < N`, the `j`-th iterated
derivative is differentiable there. -/
lemma differentiableOn_iteratedDeriv_Ioo_fin' {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁)) {j : ℕ} (hj : j < N) :
    DifferentiableOn ℝ (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- For `f` of class `C^N` on `(0,x₁]` and `j < N`, the `j`-th iterated derivative is
differentiable on the open interval `(0,x₁)`. -/
lemma differentiableOn_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j < N) :
    DifferentiableOn ℝ (iteratedDeriv j f) (Set.Ioo 0 x₁) :=
  differentiableOn_iteratedDeriv_Ioo_fin' (hf.mono Set.Ioo_subset_Ioc_self) hj

/-- At an interior point of `(0,x₁)`, the `j`-th iterated derivative of a `C^N` function
(with `j + 1 ≤ N`) has derivative the `(j+1)`-st iterated derivative. -/
lemma hasDerivAt_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j + 1 ≤ N)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 x₁) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j f) x :=
    (differentiableOn_iteratedDeriv_Ioo_fin hf (by omega)).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- Continuity of the iterated derivatives on a compact subinterval `[a,b] ⊆ (0,x₁)`. -/
lemma continuousOn_iteratedDeriv_Icc_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j ≤ N)
    {a b : ℝ} (ha : 0 < a) (hb : b < x₁) :
    ContinuousOn (iteratedDeriv j f) (Set.Icc a b) :=
  (continuousOn_iteratedDeriv_Ioo_fin hf hj).mono
    fun _ hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩

/-- **The fundamental theorem of calculus for the iterated derivatives**, on a compact
subinterval `[a,b]` with `0 < a` and `b < x₁`, for `f` of class `C^{j+1}` on `(0,x₁]`:

`∫_a^b f^{(j+1)} = f^{(j)}(b) − f^{(j)}(a)`. -/
theorem intervalIntegral_iteratedDeriv_succ_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j + 1 ≤ N)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < x₁) :
    ∫ s in a..b, iteratedDeriv (j + 1) f s = iteratedDeriv j f b - iteratedDeriv j f a := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x :=
    fun x hx =>
      hasDerivAt_iteratedDeriv_Ioo_fin hf hj
        ⟨lt_trans ha hx.1, lt_of_lt_of_le hx.2 (le_of_lt hb)⟩
  have hint : IntervalIntegrable (iteratedDeriv (j + 1) f) volume a b :=
    (continuousOn_iteratedDeriv_Icc_fin hf (by omega) ha hb).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_iteratedDeriv_Icc_fin hf (by omega) ha hb) hderiv hint

/-! ## Integrability and the primitive -/

/-- Finite-order version of `Work.FTS.H2.DivQ.primIntegrable`: `s ↦ s^k f^{(k+1)}(s)` is
integrable on `(0,x₁]` as soon as `f` is of class `C^{k+1}` there and the weighted square of
`f^{(k+1)}` is integrable. -/
theorem primIntegrable_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (f : ℝ → ℝ) (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hN : k + 1 ≤ N)
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (Set.Ioc 0 x₁) := by
  have hcψ : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul (continuousOn_iteratedDeriv_Ioo_fin hf hN)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := hcψ.aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at h
  have h1 : MeasureTheory.Integrable (fun s : ℝ => s ^ γ) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := x₁) (r := γ) hγ
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁.le] at h
    exact h
  have h2 : MeasureTheory.Integrable
      (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := hint
  have hInt : MeasureTheory.Integrable
      (fun s : ℝ => s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := h1.add h2
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 x₁)),
      ‖s ^ k * iteratedDeriv (k + 1) f s‖ ≤
        s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs0.le k)]
    have hpos : 0 ≤ s ^ k * |iteratedDeriv (k + 1) f s| :=
      mul_nonneg (pow_nonneg hs0.le k) (abs_nonneg _)
    linarith [Work.FTS.H2.DivQ.two_mul_pow_mul_abs_le_amgm k γ s (iteratedDeriv (k + 1) f s) hs0]
  exact MeasureTheory.Integrable.mono' hInt hmeas hbound

/-- Finite-order version of `Work.FTS.H2.DivQ.primitiveDerivData`. -/
theorem primitiveDerivData_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (f : ℝ → ℝ) (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hN : k + 1 ≤ N)
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Ioc 0 x₁) ∧
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Icc 0 x₁) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (t ^ k * iteratedDeriv (k + 1) f t) t) := by
  have hc : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) :=
    continuousOn_iteratedDeriv_Ioo_fin hf hN
  have hcont : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul hc
  have hIoc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) :=
    primIntegrable_fin k γ x₁ hx₁ hγ f hf hN hint
  have hIcc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Icc 0 x₁) :=
    hIoc.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := x₁)).symm
  refine ⟨hIoc, ?_, ?_⟩
  · have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := x₁)
      (μ := volume) (f := fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (by rwa [Set.uIcc_of_le hx₁.le])
    simpa [Set.uIcc_of_le hx₁.le] using h
  · intro t ht
    have ht0 : 0 < t := ht.1
    have htx : t < x₁ := ht.2
    have hII : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume 0 t := by
      refine ⟨hIoc.mono_set (Set.Ioc_subset_Ioc_right htx.le), ?_⟩
      refine MeasureTheory.IntegrableOn.of_measure_zero ?_
      rw [Set.Ioc_eq_empty (not_lt.mpr ht0.le)]
      exact measure_empty
    have hcat : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) t :=
      ((continuous_pow k).continuousAt).mul
        (hc.continuousAt (isOpen_Ioo.mem_nhds ⟨ht0, htx⟩))
    have hsl : StronglyMeasurableAtFilter (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (nhds t) volume := by
      refine ⟨Set.Ioo (t / 2) ((t + x₁) / 2), ?_, ?_⟩
      · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
      · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioo
        intro y hy
        exact ⟨by linarith [hy.1, ht0], by linarith [hy.2, htx]⟩
    exact intervalIntegral.integral_hasDerivAt_right hII hsl hcat

end Work.FTS.EllipticEst.remov.HardyFin
