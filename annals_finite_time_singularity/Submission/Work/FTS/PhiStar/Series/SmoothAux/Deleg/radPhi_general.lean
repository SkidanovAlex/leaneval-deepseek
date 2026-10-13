import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radPhi_general` — the `z`-derivatives of `radPhi` at an arbitrary order bound

`radPhi α m c = fun z => ∫ u in (0)..1, c (z * u) * u ^ (radQ α m - 1)`.  The sibling module
`RadialWAux/radPhi_iteratedDeriv.lean` proves, for a source `c` that is `C^22` on `(0,∞)` with
`|c^{(j)}| ≤ K` up to order `22`, that

  `(d/dz)^k (radPhi α m c) z = ∫ u in (0)..1, c^{(k)}(z u) u^{k + radQ α m - 1}`  (`k ≤ 22`),

together with the accompanying bound `≤ K/(k + radQ α m)`.

Here the numerical restriction `22` is replaced by an arbitrary order bound `N`, and in addition
the operator identity — that the derivative of the `k`-th iterated derivative of `radPhi` is the
kernel of order `k + 1` — is recorded whenever `k + 1 ≤ N`.

The proof is the verbatim adaptation of the order-`22` argument: differentiability of the `k`-th
iterated derivative of `c` on `(0,∞)` for `k < N` (from `ContDiffOn ℝ N c`), the chain rule and
`iteratedDeriv_succ` for the pointwise `z`-derivative of the integrand, domination of the
differentiated integrand by `K u^{k+1+radQ-1}` (integrable on `(0,1]` since `k + radQ > 0`), and
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.SmoothAux.Deleg

set_option autoImplicit false

/-- The `k`-th differentiated kernel of `radPhi α m c`, i.e. the parametric integral
`z ↦ ∫ u in (0)..1, c^{(k)}(z * u) * u^{k + q - 1}` (`q = radQ α m`).  `radPhi` itself is the
case `k = 0`. -/
private def radPhiKernel (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u)
    * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)

/-- On `Ioi 0`, where `c` is `C^N`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < N`. -/
private lemma differentiableAt_iteratedDeriv {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {k : ℕ} (hk : k < N) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk))
      ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- The kernel integrand `u ↦ c^{(k)}(x u) u^{k + q - 1}` is a.e. strongly measurable on `(0,1]`
for `x > 0`, `k ≤ N`.  (Measurability only fails at the single point `u = 0`, where `c` is only
known to be `C^N` on `(0,∞)` and where `u^{k+q-1}` may blow up.) -/
private lemma aestronglyMeasurable_kernel {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {q : ℝ} {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
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

/-- The kernel integrand is integrable on `(0,1]`, dominated by `K u^{k+q-1}`. -/
private lemma integrableOn_kernel {N : ℕ} {c : ℝ → ℝ} {K q : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (hb : Work.FTS.PhiStar.BddDeriv N c K) {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x)
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

/-- Differentiation under the integral sign for the kernel of `radPhi`: passing from the `k`-th to
the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_radPhiKernel {α : ℝ} (hα : 0 < α) (m : ℕ) {N : ℕ} {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) {k : ℕ} (hk : k + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (radPhiKernel α m c k) (radPhiKernel α m c (k + 1) z) z := by
  have hq : 0 < Work.FTS.PhiStar.RadialWAux.radQ α m :=
    Work.FTS.PhiStar.RadialWAux.radQ_pos hα m
  have hkle : k ≤ N := by omega
  have hklt : k < N := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u)
        * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u)
        * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact integrableOn_kernel hK hq hb hkle hz (aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t)
          * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t)
          * t ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        (iteratedDeriv (k + 1) c (x * t)
          * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
        = ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u)
      * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ =>
      K * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

/-- `iteratedDeriv k (radPhi α m c)` is the `k`-th kernel, for every `k ≤ N`. -/
private lemma iteratedDeriv_radPhi_eq_kernel {α : ℝ} (hα : 0 < α) (m : ℕ) {N : ℕ} {c : ℝ → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z = radPhiKernel α m c k z := by
  intro k
  induction k with
  | zero =>
    intro _ z _
    simp only [radPhiKernel, Work.FTS.PhiStar.RadialWAux.radPhi, iteratedDeriv_zero,
      Nat.cast_zero, zero_add]
  | succ n ih =>
    intro hn z hz
    have hnle : n ≤ N := by omega
    have h1 : deriv (iteratedDeriv n (Work.FTS.PhiStar.RadialWAux.radPhi α m c)) z
        = deriv (radPhiKernel α m c n) z := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih hnle y hy
    have h2 : deriv (radPhiKernel α m c n) z = radPhiKernel α m c (n + 1) z :=
      (hasDerivAt_radPhiKernel hα m hK hc hb hn hz).deriv
    rw [iteratedDeriv_succ, h1, h2]

theorem radPhi_general {α : ℝ} (hα : 0 < α) (m : ℕ) (N : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z
          = ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      ∧ |iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z|
          ≤ K / ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m)
      ∧ (k + 1 ≤ N → HasDerivAt (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c))
          (∫ u in (0 : ℝ)..1, iteratedDeriv (k + 1) c (z * u)
              * u ^ ((k : ℝ) + 1 + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) z) := by
  have hq : 0 < Work.FTS.PhiStar.RadialWAux.radQ α m :=
    Work.FTS.PhiStar.RadialWAux.radQ_pos hα m
  intro k hk z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k hk z hz]
    rfl
  · -- the bound `K / (k + q)`
    have hkq : 0 < (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m := by
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
      linarith
    have hr : (-1 : ℝ) < (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by linarith
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    have hg_int : IntervalIntegrable
        (fun u : ℝ => iteratedDeriv k c (z * u)
          * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        volume (0 : ℝ) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact integrableOn_kernel hK hq hb hk hz (aestronglyMeasurable_kernel hc hk hz)
    have hK_int : IntervalIntegrable
        (fun u : ℝ => K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        volume (0 : ℝ) 1 :=
      (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
    have hae : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        |iteratedDeriv k c (z * u)
            * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
          ≤ K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
      rw [show (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
          = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
        (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Icc).symm]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hu0 : 0 < u := hu.1
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      exact mul_le_mul_of_nonneg_right (hb k hk (z * u) (mul_pos hz hu0))
        (Real.rpow_nonneg hu0.le _)
    have h1 : |iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z|
        ≤ ∫ u in (0 : ℝ)..1,
            |iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)| := by
      rw [iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k hk z hz]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ u in (0 : ℝ)..1,
          |iteratedDeriv k c (z * u)
            * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|)
        ≤ ∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) :=
      intervalIntegral.integral_mono_ae_restrict hab hg_int.abs hK_int hae
    have h3 : (∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        = K / ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), Real.one_rpow,
        Real.zero_rpow (by linarith : (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 + 1 ≠ 0),
        sub_zero,
        show (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 + 1
          = (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m from by ring]
      ring
    linarith
  · -- the derivative identity
    intro hk1
    have hder : HasDerivAt (radPhiKernel α m c k) (radPhiKernel α m c (k + 1) z) z :=
      hasDerivAt_radPhiKernel hα m hK hc hb hk1 hz
    have hev : (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c))
        =ᶠ[𝓝 z] radPhiKernel α m c k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k (by omega) y hy
    have hfin := hder.congr_of_eventuallyEq hev
    simpa only [radPhiKernel, Nat.cast_add, Nat.cast_one] using hfin

end Work.FTS.PhiStar.Series.SmoothAux.Deleg
