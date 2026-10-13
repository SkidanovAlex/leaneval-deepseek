import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.PhiPsiDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phiKernel_hasDerivAt` — differentiation under the integral sign for the `Φ`-kernel

The `Φ`-piece of the rescaled radial Green function is the parametric integral

  `Φ z = ∫ u in (0)..1, c (z * u) * u ^ (Q - 1)`

over the *fixed* interval `(0,1)` (exponent `Q > 0`).  For a source `c` of class `C^14` on
`(0,∞)` whose first `14` derivatives are bounded by `K`, the `k`-th `z`-derivative of the kernel

  `phiKernelAux Q c k z = ∫ u in (0)..1, c^{(k)} (z * u) * u ^ (k + Q - 1)`

is obtained by differentiating under the integral sign, and passing from the `k`-th to the
`(k+1)`-st kernel is precisely the statement proved here:

`HasDerivAt (fun x => ∫ u in (0)..1, c^{(k)}(x*u) * u^(k+Q-1))
  (∫ u in (0)..1, c^{(k+1)}(z*u) * u^(k+1+Q-1)) z`   for `z > 0`, `k + 1 ≤ 14`.

The ingredients are (i) differentiability of `iteratedDeriv k c` on `(0,∞)` with derivative
`iteratedDeriv (k+1) c` (from `ContDiffOn ℝ 14 c (Ioi 0)`), and (ii) domination of the
differentiated integrand by `K u^{k+Q-1}` on `(0,1]` (integrable because `k + Q > 0`), followed
by `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

This is the general-`Q` analogue of the private helper `hasDerivAt_PhiKernel` of
`RadialWAux/PhiPsiGeneralQ.lean`, restated for an arbitrary source `h` and exponent `Q`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- The `k`-th differentiated kernel of the `Φ`-piece with general exponent `Q > 0`, i.e. the
parametric integral `z ↦ ∫ u in (0)..1, c^{(k)}(z * u) * u^{k + Q - 1}`. -/
private def phiKernelAux (Q : ℝ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + Q - 1)

/-- On `Ioi 0`, where `c` is `C^14`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < 14`. -/
private lemma phiAux_differentiableAt_iteratedDeriv {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 14 c (Set.Ioi 0)) {k : ℕ} (hk : k < 14) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk))
      ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- The `Φ`-kernel integrand `u ↦ c^{(k)}(x u) u^{k + Q - 1}` is a.e. strongly measurable on
`(0,1]` for `x > 0`, `k ≤ 14`.  (Measurability only fails at the single point `u = 0`, where `c`
is only known to be `C^14` on `(0,∞)` and where `u^{k+Q-1}` may blow up.) -/
private lemma phiAux_aestronglyMeasurable_kernel {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 14 c (Set.Ioi 0)) {Q : ℝ} {k : ℕ} (hk : k ≤ 14) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
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
  have h4 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + Q - 1)) (Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (ne_of_gt hu.1))
  have h5 : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (h3.mul h4).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [show (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
    (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc).symm]

/-- The `Φ`-kernel integrand is integrable on `(0,1]`, dominated by `K u^{k+Q-1}`. -/
private lemma phiAux_integrableOn_kernel {c : ℝ → ℝ} {K Q : ℝ} (hK : 0 ≤ K) (hQ : 0 < Q)
    (hb : Work.FTS.PhiStar.BddDeriv 14 c K) {k : ℕ} (hk : k ≤ 14) {x : ℝ} (hx : 0 < x)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioc 0 1))) :
    IntegrableOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (Set.Ioc 0 1) volume := by
  have hr : (-1 : ℝ) < (k : ℝ) + Q - 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hg : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + Q - 1)) volume (0 : ℝ) 1 :=
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

/-- Differentiation under the integral sign for the kernel of the `Φ`-piece: passing from the
`k`-th to the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_phiKernelAux {Q : ℝ} (hQ : 0 < Q) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 14 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 14 c K) {k : ℕ} (hk : k + 1 ≤ 14) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (phiKernelAux Q c k) (phiKernelAux Q c (k + 1) z) z := by
  have hkle : k ≤ 14 := by omega
  have hklt : k < 14 := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + Q - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + Q - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_integrableOn_kernel hK hQ hb hkle hz
      (phiAux_aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + Q - 1))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (phiAux_differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + Q - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + Q - 1) = ((k : ℝ) + Q - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

theorem phiKernel_hasDerivAt {Q B : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 14 h B)
    {j : ℕ} (hj : j + 1 ≤ 14) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..1,
        iteratedDeriv j h (x * u) * u ^ ((j : ℝ) + Q - 1))
      (∫ u in (0 : ℝ)..1,
        iteratedDeriv (j + 1) h (z * u) * u ^ (((j + 1 : ℕ) : ℝ) + Q - 1)) z :=
  hasDerivAt_phiKernelAux hQ hB hh hb hj hz

end Work.FTS.PhiStar.RadialWAux
