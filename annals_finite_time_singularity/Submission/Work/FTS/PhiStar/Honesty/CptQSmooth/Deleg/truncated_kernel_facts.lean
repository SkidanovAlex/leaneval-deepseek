import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncated_kernel_facts` — derivatives and bounds of the truncated kernel

For a source `c : ℝ → ℝ` that is `C^N` on `(0,∞)` with `|c^{(k)}| ≤ K` there (`k ≤ N`), the
parametric integral

  `x ↦ ∫ u in (1)..U, c (x * u) * u ^ s`     (`1 ≤ U`, `s ≤ 0`)

has `k`-th iterated derivative `x ↦ ∫ u in (1)..U, c^{(k)} (x * u) * u ^ (k + s)` for every
`k ≤ N` and `x > 0`, and that derivative is bounded by `K * (max 1 U) ^ (N + 1)`.

The proof is the truncated-interval analogue of `Series.SmoothAux.Deleg.radPhi_general`: the
integration variable runs over `[1, U]` with `1 ≤ U`, so no endpoint singularity is present
and integrability/measurability is plain continuity, while the exponent `k + s` is bounded by
`k ≤ N` on the interval (as `u ≥ 1` and `s ≤ 0`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg

set_option autoImplicit false

/-- The `k`-th differentiated truncated kernel, i.e. the parametric integral
`x ↦ ∫ u in (1)..U, c^{(k)} (x * u) * u ^ (k + s)`. -/
private def truncKernel (c : ℝ → ℝ) (U s : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x => ∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)

/-- On `Ioi 0`, where `c` is `C^N`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < N`. -/
private lemma differentiableAt_iteratedDeriv_trunc {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) {k : ℕ} (hk : k < N) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk)) ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- On `Ioi 0` the `k`-th iterated derivative of a `C^N` function is continuous, `k ≤ N`. -/
private lemma continuousOn_iteratedDeriv_trunc {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ N) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast hk)) ht).symm
  exact (hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk)
    (uniqueDiffOn_Ioi 0)).congr hEq

/-- The truncated kernel integrand `u ↦ c^{(k)}(x u) u^{k+s}` is continuous on `Ici a` whenever
`x > 0` and `a > 0` — in particular no endpoint singularity is present. -/
private lemma continuousOn_trunc_integrand {N : ℕ} {c : ℝ → ℝ} {s : ℝ} {k : ℕ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)) (Set.Ici a) := by
  have h1 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ici a) :=
    (continuousOn_iteratedDeriv_trunc hc hk).comp
      ((continuous_const.mul continuous_id).continuousOn)
      (fun u hu => mul_pos hx (lt_of_lt_of_le ha hu))
  have h2 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + s)) (Set.Ici a) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le ha hu)))
  exact h1.mul h2

/-- On `Ici a` with `a > 0` the function `u ↦ u ^ t` is continuous, for every real `t`. -/
private lemma continuousOn_rpow_Ici {t : ℝ} {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => u ^ t) (Set.Ici a) :=
  ContinuousOn.rpow_const continuousOn_id
    (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le ha hu)))

/-- The truncated kernel integrand is a.e. strongly measurable on `Ι 1 U` for `x > 0`. -/
private lemma aestronglyMeasurable_trunc {N : ℕ} {c : ℝ → ℝ} {U s : ℝ} (hU : 1 ≤ U)
    {k : ℕ} (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) := by
  rw [Set.uIoc_of_le hU]
  exact ((continuousOn_trunc_integrand hc hk hx zero_lt_one).mono
    (fun u hu => le_of_lt hu.1)).aestronglyMeasurable measurableSet_Ioc

/-- The truncated kernel integrand is interval integrable on `1..U` for `x > 0`, `1 ≤ U`. -/
private lemma intervalIntegrable_trunc {N : ℕ} {c : ℝ → ℝ} {U s : ℝ} (hU : 1 ≤ U)
    {k : ℕ} (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      volume (1 : ℝ) U := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hU]
  exact (continuousOn_trunc_integrand hc hk hx zero_lt_one).mono (fun u hu => hu.1)

/-- Differentiation under the integral sign for the truncated kernel: passing from the `k`-th
to the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_truncKernel {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hk : k + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (truncKernel c U s k) (truncKernel c U s (k + 1) z) z := by
  have hkle : k ≤ N := by omega
  have hklt : k < N := by omega
  have hneigh : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) := by
    filter_upwards [hneigh] with x hx
    exact aestronglyMeasurable_trunc hU hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    intervalIntegrable_trunc hU hc hkle hz
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) :=
    aestronglyMeasurable_trunc hU hc hk hz
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + s)) volume (1 : ℝ) U := by
    have hr : IntervalIntegrable (fun u : ℝ => u ^ (((k + 1 : ℕ) : ℝ) + s)) volume (1 : ℝ) U := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hU]
      exact (continuousOn_rpow_Ici (t := (((k + 1 : ℕ) : ℝ) + s)) zero_lt_one).mono
        (fun u hu => hu.1)
    exact hr.const_mul K
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1 : ℝ) U → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + s)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + s) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hU] at ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg ht0.le _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1 : ℝ) U → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + s))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + s)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hU] at ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (differentiableAt_iteratedDeriv_trunc hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + s))
    refine hmul.congr_deriv ?_
    have hcast : (((k + 1 : ℕ)) : ℝ) + s = ((k : ℝ) + s) + 1 := by push_cast; ring
    have hrpow : t ^ (((k : ℝ) + s) + 1) = t ^ ((k : ℝ) + s) * t := by
      rw [Real.rpow_add ht0, Real.rpow_one]
    rw [hcast, hrpow]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u) * u ^ (((k + 1 : ℕ) : ℝ) + s))
    (x₀ := z) (s := Set.Ioi 0) (a := (1 : ℝ)) (b := U) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + s))
    hneigh hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

/-- `iteratedDeriv k` of the truncated kernel is the `k`-th truncated kernel, for every `k ≤ N`. -/
private lemma iteratedDeriv_trunc_eq {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x
        = truncKernel c U s k x := by
  intro k
  induction k with
  | zero =>
    intro _ x _
    simp only [truncKernel, iteratedDeriv_zero, Nat.cast_zero, zero_add]
  | succ n ih =>
    intro hn x hx
    have hnle : n ≤ N := by omega
    have h1 : deriv (iteratedDeriv n (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s)) x
        = deriv (truncKernel c U s n) x := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih hnle y hy
    have h2 : deriv (truncKernel c U s n) x = truncKernel c U s (n + 1) x :=
      (hasDerivAt_truncKernel hK hU hc hb hn (z := x) hx).deriv
    rw [iteratedDeriv_succ, h1, h2]

/-- The bound on the truncated kernel: `|∫_1^U c^{(k)}(x u) u^{k+s} du| ≤ K (max 1 U)^{N+1}`. -/
private lemma truncKernel_bound {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hs : s ≤ 0) (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    |truncKernel c U s k x| ≤ K * (max 1 U) ^ (N + 1) := by
  have hmax : max 1 U = U := max_eq_right hU
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le zero_lt_one hU
  have hf_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    intervalIntegrable_trunc hU hc hk hx
  have h1 : |∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|
      ≤ ∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| :=
    intervalIntegral.abs_integral_le_integral_abs hU
  have hr : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + s)) volume (1 : ℝ) U := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hU]
    exact (continuousOn_rpow_Ici (t := (k : ℝ) + s) zero_lt_one).mono (fun u hu => hu.1)
  have hdom_int : IntervalIntegrable (fun u : ℝ => K * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    hr.const_mul K
  have hae : (fun u : ℝ => |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|)
      ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) U)] (fun u : ℝ => K * u ^ ((k : ℝ) + s)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
      (Real.rpow_nonneg hu0.le _)
  have h2 : (∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|)
      ≤ ∫ u in (1 : ℝ)..U, K * u ^ ((k : ℝ) + s) :=
    intervalIntegral.integral_mono_ae_restrict hU hf_int.abs hdom_int hae
  have hrN : (k : ℝ) + s ≤ (N : ℝ) := by
    have h : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    linarith
  have h4 : (∫ u in (1 : ℝ)..U, u ^ ((k : ℝ) + s))
      ≤ ∫ u in (1 : ℝ)..U, (U : ℝ) ^ N := by
    refine intervalIntegral.integral_mono_on hU hr intervalIntegrable_const (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    calc u ^ ((k : ℝ) + s) ≤ u ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hu.1 hrN
      _ = (u : ℝ) ^ N := Real.rpow_natCast u N
      _ ≤ (U : ℝ) ^ N := pow_le_pow_left₀ hu0.le hu.2 N
  calc |truncKernel c U s k x|
      = |∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| := by
        simp only [truncKernel]
    _ ≤ ∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| := h1
    _ ≤ ∫ u in (1 : ℝ)..U, K * u ^ ((k : ℝ) + s) := h2
    _ = K * ∫ u in (1 : ℝ)..U, u ^ ((k : ℝ) + s) :=
        intervalIntegral.integral_const_mul K _
    _ ≤ K * ∫ u in (1 : ℝ)..U, (U : ℝ) ^ N := mul_le_mul_of_nonneg_left h4 hK
    _ = K * ((U - 1) * (U : ℝ) ^ N) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ K * ((U : ℝ) ^ N * U) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        calc (U - 1) * (U : ℝ) ^ N ≤ U * (U : ℝ) ^ N := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hU0.le N)
              linarith
          _ = (U : ℝ) ^ N * U := by ring
    _ = K * (U : ℝ) ^ (N + 1) := by rw [pow_succ]
    _ = K * (max 1 U) ^ (N + 1) := by rw [hmax]

theorem truncated_kernel_facts {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hs : s ≤ 0) (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x
          = ∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)
        ∧ |iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x|
            ≤ K * (max 1 U) ^ (N + 1) := by
  intro k hk x hx
  refine ⟨?_, ?_⟩
  · rw [iteratedDeriv_trunc_eq hK hU hc hb k hk x hx]
    simp only [truncKernel]
  · rw [iteratedDeriv_trunc_eq hK hU hc hb k hk x hx]
    exact truncKernel_bound hK hU hs hc hb hk hx

end Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg
