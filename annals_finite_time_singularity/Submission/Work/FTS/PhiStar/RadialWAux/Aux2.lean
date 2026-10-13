import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadialWAux.Aux2` — differentiation under the integral sign for the `Φ`-kernel, and the tail
tools

* `hasDerivAt_radPhiKernel_aux`, `radPhi_iteratedDeriv_hasDerivAt`: the `HasDerivAt` facts for the
  iterated derivatives of `Φ = radPhi α m c` (the parametric differentiation over the fixed
  interval `(0,1)`).
* `continuousOn_iteratedDeriv_of`, `integrableOn_Ioi_of_le_rpow`: two tools for the tail.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false



set_option autoImplicit false

/-! ### A. Differentiation under the integral sign for the `Φ`-kernel -/

/-- The `k`-th differentiated kernel of `radPhi`. -/
private def radPhiKernelAux (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1)

private lemma aux_differentiableAt_iteratedDeriv {c : ℝ → ℝ} (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    {k : ℕ} (hk : k < 22) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk)) ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

private lemma aux_aestronglyMeasurable_kernel {c : ℝ → ℝ} (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    {q : ℝ} {k : ℕ} (hk : k ≤ 22) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
  have hw : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  have hmaps : Set.MapsTo (fun u : ℝ => x * u) (Set.Ioo 0 1) (Set.Ioi 0) :=
    fun u hu => mul_pos hx hu.1
  have h1 : ContinuousOn (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u))
      (Set.Ioo 0 1) :=
    hw.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have h2 : Set.EqOn (fun u : ℝ => iteratedDeriv k c (x * u))
      (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u)) (Set.Ioo 0 1) := by
    intro u hu
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds (hmaps hu))).of_le (by exact_mod_cast hk))
      (hmaps hu)).symm
  have h3 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioo 0 1) := h1.congr h2
  have h4 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) (Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (ne_of_gt hu.1))
  have h5 : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (h3.mul h4).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [show (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
    (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc).symm]

private lemma aux_integrableOn_kernel {c : ℝ → ℝ} {K q : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) {k : ℕ} (hk : k ≤ 22) {x : ℝ} (hx : 0 < x)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1))) :
    IntegrableOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (Set.Ioc 0 1) volume := by
  have hr : (-1 : ℝ) < (k : ℝ) + q - 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hg : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' hr
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at h1
    exact h1.const_mul K
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
  exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
    (Real.rpow_nonneg (le_of_lt hu0) _)

private lemma hasDerivAt_radPhiKernel_aux {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) {k : ℕ} (hk : k + 1 ≤ 22) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (radPhiKernelAux α m c k) (radPhiKernelAux α m c (k + 1) z) z := by
  have hq : 0 < radQ α m := radQ_pos hα m
  have hkle : k ≤ 22 := by omega
  have hklt : k < 22 := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + radQ α m - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aux_aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact aux_integrableOn_kernel hK hq hb hkle hz (aux_aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aux_aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + radQ α m - 1))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (aux_differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + radQ α m - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + radQ α m - 1) = ((k : ℝ) + radQ α m - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + radQ α m - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

/-- `HasDerivAt` for the iterated derivatives of `Φ`. -/
theorem radPhi_iteratedDeriv_hasDerivAt {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 21 → ∀ z : ℝ, 0 < z →
      HasDerivAt (iteratedDeriv k (radPhi α m c)) (iteratedDeriv (k + 1) (radPhi α m c) z) z := by
  intro k hk z hz
  have hker := hasDerivAt_radPhiKernel_aux hα m hK hc hb (k := k) (by omega) hz
  have hev : iteratedDeriv k (radPhi α m c) =ᶠ[𝓝 z] radPhiKernelAux α m c k := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact radPhi_iteratedDeriv hα m hK hc hb k (by omega) y hy
  have h1 : HasDerivAt (iteratedDeriv k (radPhi α m c))
      (∫ u in (0 : ℝ)..1, iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)) z :=
    hker.congr_of_eventuallyEq hev
  have hval : (∫ u in (0 : ℝ)..1, iteratedDeriv (k + 1) c (z * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
      = iteratedDeriv (k + 1) (radPhi α m c) z :=
    (radPhi_iteratedDeriv hα m hK hc hb (k + 1) (by omega) z hz).symm
  rwa [hval] at h1

/-! ### B. Tools for the tail -/

/-- `iteratedDeriv j c` is continuous on `(0,∞)` for `j ≤ n`, from `ContDiffOn ℝ n c (Ioi 0)`. -/
lemma continuousOn_iteratedDeriv_of {c : ℝ → ℝ} {n j : ℕ} (hc : ContDiffOn ℝ n c (Set.Ioi 0))
    (hj : j ≤ n) : ContinuousOn (iteratedDeriv j c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin j c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Ioi 0)
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- A continuous function on `(1,∞)` dominated by `C·u^t` with `t < -1` is integrable there. -/
lemma integrableOn_Ioi_of_le_rpow {g : ℝ → ℝ} {C t : ℝ} (ht : t < -1) (hC : 0 ≤ C)
    (hg : ContinuousOn g (Set.Ioi 1)) (hle : ∀ u ∈ Set.Ioi 1, |g u| ≤ C * u ^ t) :
    IntegrableOn g (Set.Ioi 1) := by
  have hdom : IntegrableOn (fun u : ℝ => C * u ^ t) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ht zero_lt_one).const_mul C
  refine Integrable.mono' hdom (hg.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs]
  exact hle u hu

end Work.FTS.PhiStar.RadialWAux
