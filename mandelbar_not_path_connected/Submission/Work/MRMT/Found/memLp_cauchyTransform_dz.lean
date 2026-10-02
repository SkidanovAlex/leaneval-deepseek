/-
Work.MRMT.Found — `C(∂u) ∈ L²` for `u` of class `C¹` with compact support.

This is the `L²`-statement needed for the Beurling/Wirtinger bookkeeping of the principal
solution: the Cauchy transform of the Wirtinger derivative `∂u = dz u` is square integrable.

Route.  `ω := dz u` is continuous with compact support and has zero mean (`∫ ∂u = 0`,
`Work.MRMT.Beltrami.integral_dz_eq_zero_of_contDiff`).  The general analytic fact proved here is

`Work.MRMT.Cauchy.memLp_cauchyTransform_of_zero_mean`:
if `ω` is continuous with compact support and `∫ ω = 0`, then `Cω ∈ L²(ℂ)`.

The proof splits `∫⁻ ‖Cω‖²` at a ball of radius `s`:
* on `Metric.ball 0 s` the bound is the local `L²` estimate
  `Work.MRMT.Found.cauchyTransform_memLp_ball`;
* on the complement `{s ≤ ‖z‖}` one uses the sharpened (mean-zero) decay
  `‖Cω z‖ ≤ 2R/π · ‖ω‖_{L¹} / ‖z‖²`  (`decay_zero_mean`), which makes the integrand
  dominated by a constant times `‖z‖⁻⁴`; the exterior integral
  `∫⁻_{s ≤ ‖z‖} ofReal (c ‖z‖⁻⁴)` is finite (`lintegral_ofReal_mul_norm_rpow_neg_four_exterior_lt_top`),
  obtained from `Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le` at exponent `-3`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.Cauchy.aestronglyMeasurable_cauchyTransform
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball
import Submission.Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-! ## The Wirtinger derivative of a compactly supported function has compact support -/

/-- If `u` has compact support then so does `∂u = dz u`: `∂u` vanishes off `tsupport u`. -/
lemma hasCompactSupport_dz {u : ℂ → ℂ} (hs : HasCompactSupport u) :
    HasCompactSupport (dz u) := by
  refine (hs.isCompact).of_isClosed_subset (isClosed_tsupport (dz u)) ?_
  refine closure_minimal ?_ (isClosed_tsupport u)
  intro z hz
  by_contra hzc
  have hzero : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hzc] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hfd : fderiv ℝ u z = 0 := by
    rw [hzero.fderiv_eq]
    simp
  have hz0 : dz u z = 0 := by simp [dz, hfd]
  exact (Function.mem_support.mp hz) hz0

/-! ## The mean-zero decay of the Cauchy transform -/

/-- **Sharpened decay of the Cauchy transform of a mean-zero function.**
If `ω` is integrable, supported in the closed ball of radius `R > 0` around the origin, and
`∫ ω = 0`, then for `‖z‖ ≥ 2R` the Cauchy transform decays like `‖z‖⁻²`:
`‖Cω z‖ ≤ 2R/π · ‖ω‖_{L¹} / ‖z‖²`.

Indeed `1/(ζ-z) = -1/z + ζ/(z(ζ-z))`, so `∫ ω(ζ)/(ζ-z) dζ = (1/z) ∫ ω(ζ) ζ/(ζ-z) dζ`
(the mean-zero term drops out), and on the support `‖ζ‖ ≤ R`, `‖ζ-z‖ ≥ ‖z‖/2`. -/
theorem decay_zero_mean {ω : ℂ → ℂ}
    (hint : Integrable ω (volume : Measure ℂ)) (h0 : ∫ z, ω z = 0)
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ ζ : ℂ, ω ζ ≠ 0 → ‖ζ‖ ≤ R)
    {z : ℂ} (hz : 2 * R ≤ ‖z‖) :
    ‖cauchyTransform ω z‖ ≤
      2 * R / Real.pi * (∫ ζ, ‖ω ζ‖) / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hker : ∀ ζ : ℂ, ‖ω ζ * (ζ / (z * (ζ - z)))‖ ≤ ‖ω ζ‖ * (2 * R / ‖z‖ ^ 2) := by
    intro ζ
    by_cases hω : ω ζ = 0
    · simp [hω]
    · have hζ : ‖ζ‖ ≤ R := hsupp ζ hω
      have hden : ‖z‖ / 2 ≤ ‖ζ - z‖ := by
        have h1 : ‖z‖ - ‖ζ‖ ≤ ‖ζ - z‖ := by
          have h2 := norm_sub_norm_le z ζ
          rwa [norm_sub_rev] at h2
        linarith
      calc ‖ω ζ * (ζ / (z * (ζ - z)))‖ = ‖ω ζ‖ * (‖ζ‖ / (‖z‖ * ‖ζ - z‖)) := by
            rw [norm_mul, norm_div, norm_mul]
        _ ≤ ‖ω ζ‖ * (R / (‖z‖ * ‖ζ - z‖)) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact div_le_div_of_nonneg_right hζ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ ‖ω ζ‖ * (R / (‖z‖ * (‖z‖ / 2))) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            refine div_le_div_of_nonneg_left hR.le (by positivity) ?_
            exact mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖ω ζ‖ * (2 * R / ‖z‖ ^ 2) := by
            congr 1
            field_simp
  have hIntA : Integrable (fun ζ : ℂ => ω ζ * (ζ / (z * (ζ - z)))) := by
    refine Integrable.mono' ((hint.norm).mul_const (2 * R / ‖z‖ ^ 2)) ?_ ?_
    · exact hint.aestronglyMeasurable.mul
        ((measurable_id.div (measurable_const.mul (measurable_id.sub measurable_const))).aestronglyMeasurable)
    · filter_upwards with ζ; exact hker ζ
  have hIntB : Integrable (fun ζ : ℂ => ω ζ * z⁻¹) := hint.mul_const _
  have hpt : ∀ ζ : ℂ, ω ζ / (ζ - z) = ω ζ * (ζ / (z * (ζ - z))) - ω ζ * z⁻¹ := by
    intro ζ
    by_cases hω : ω ζ = 0
    · rw [hω, zero_div, zero_mul, zero_mul, sub_zero]
    · have hζ : ‖ζ‖ ≤ R := hsupp ζ hω
      have hne : ζ - z ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; rw [h] at hζ; linarith
      have hz0 : z ≠ 0 := by simpa [norm_eq_zero] using hzpos.ne'
      field_simp
      ring
  have hkey : ∫ ζ, ω ζ / (ζ - z) = ∫ ζ, ω ζ * (ζ / (z * (ζ - z))) := by
    have h1 : ∫ ζ, ω ζ / (ζ - z)
        = ∫ ζ, (ω ζ * (ζ / (z * (ζ - z))) - ω ζ * z⁻¹) := by
      apply integral_congr_ae; filter_upwards with ζ; exact hpt ζ
    rw [h1]
    rw [integral_sub (f := fun ζ : ℂ => ω ζ * (ζ / (z * (ζ - z))))
      (g := fun ζ : ℂ => ω ζ * z⁻¹) hIntA hIntB]
    rw [integral_mul_const (z⁻¹) (fun ζ : ℂ => ω ζ)]
    simp only [h0, zero_mul, sub_zero]
  have hbd : ‖∫ ζ, ω ζ * (ζ / (z * (ζ - z)))‖ ≤ (∫ ζ, ‖ω ζ‖) * (2 * R / ‖z‖ ^ 2) := by
    have h1 := norm_integral_le_of_norm_le ((hint.norm).mul_const _)
      (Filter.Eventually.of_forall hker)
    rw [integral_mul_const (2 * R / ‖z‖ ^ 2) (fun ζ : ℂ => ‖ω ζ‖)] at h1
    exact h1
  have hcn : ‖cauchyConst‖ = Real.pi⁻¹ := by
    rw [cauchyConst, norm_neg, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  calc ‖cauchyTransform ω z‖
      = ‖cauchyConst‖ * ‖∫ ζ, ω ζ / (ζ - z)‖ := by
        rw [cauchyTransform, norm_mul]
    _ = Real.pi⁻¹ * ‖∫ ζ, ω ζ * (ζ / (z * (ζ - z)))‖ := by rw [hcn, hkey]
    _ ≤ Real.pi⁻¹ * ((∫ ζ, ‖ω ζ‖) * (2 * R / ‖z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 2 * R / Real.pi * (∫ ζ, ‖ω ζ‖) / ‖z‖ ^ 2 := by field_simp

/-! ## Integrability of `‖z‖⁻⁴` outside a disc -/

/-- For `c ≥ 0` and `s > 0`, the exterior integral of `c ‖z‖⁻⁴` is finite.  On `{s ≤ ‖z‖}`
one has `‖z‖⁻⁴ ≤ s⁻¹ ‖z‖⁻³`, and `Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le`
(with `q = 3/2`) computes `∫⁻_{s ≤ ‖z‖} ‖z‖⁻³ = 2π/s`. -/
theorem lintegral_ofReal_mul_norm_rpow_neg_four_exterior_lt_top {c s : ℝ} (hc : 0 ≤ c)
    (hs : 0 < s) :
    ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ENNReal.ofReal (c * ‖z‖ ^ (-4 : ℝ)) < ⊤ := by
  have hSm : MeasurableSet {z : ℂ | s ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hexp : ((-(2 * (3 / 2)) : ℝ) = (-3 : ℝ)) := by norm_num
  have hbase : ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-3 : ℝ)) < ⊤ := by
    have h := Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le (0 : ℂ) (q := 3 / 2) (t := s)
      (by norm_num) (by norm_num) hs
    have h2 : ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-3 : ℝ))
        = ∫⁻ z in {z : ℂ | s ≤ ‖z - 0‖}, ‖z - 0‖ₑ ^ ((-(2 * (3 / 2))) : ℝ) := by
      simp only [sub_zero]
      refine setLIntegral_congr_fun hSm ?_
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hs hz
      have hE : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by simp [enorm_eq_nnnorm]
      simp only [hexp, hE]
      exact (ENNReal.ofReal_rpow_of_pos hzpos).symm
    rw [h2, h]
    exact ENNReal.ofReal_lt_top
  have hpoint : ∀ z ∈ {z : ℂ | s ≤ ‖z‖},
      ENNReal.ofReal (c * ‖z‖ ^ (-4 : ℝ))
        ≤ ENNReal.ofReal (c * s⁻¹) * ENNReal.ofReal (‖z‖ ^ (-3 : ℝ)) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hs hz
    have hcs : 0 ≤ c * s⁻¹ := mul_nonneg hc (inv_nonneg.mpr hs.le)
    rw [← ENNReal.ofReal_mul hcs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hz3 : 0 ≤ ‖z‖ ^ (-3 : ℝ) := Real.rpow_nonneg hzpos.le _
    have hinv : ‖z‖⁻¹ ≤ s⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hs hz
    calc c * ‖z‖ ^ (-4 : ℝ) = c * (‖z‖ ^ (-3 : ℝ) * ‖z‖ ^ (-1 : ℝ)) := by
          rw [← Real.rpow_add hzpos]; norm_num
      _ = c * (‖z‖ ^ (-3 : ℝ) * ‖z‖⁻¹) := by rw [Real.rpow_neg_one]
      _ = c * ‖z‖ ^ (-3 : ℝ) * ‖z‖⁻¹ := by ring
      _ ≤ c * ‖z‖ ^ (-3 : ℝ) * s⁻¹ := mul_le_mul_of_nonneg_left hinv (mul_nonneg hc hz3)
      _ = c * s⁻¹ * ‖z‖ ^ (-3 : ℝ) := by ring
  calc ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ENNReal.ofReal (c * ‖z‖ ^ (-4 : ℝ))
      ≤ ∫⁻ z in {z : ℂ | s ≤ ‖z‖},
          ENNReal.ofReal (c * s⁻¹) * ENNReal.ofReal (‖z‖ ^ (-3 : ℝ)) :=
        setLIntegral_mono' hSm hpoint
    _ = ENNReal.ofReal (c * s⁻¹)
          * ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-3 : ℝ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase

/-! ## The Cauchy transform of a mean-zero compactly supported function is in `L²` -/

/-- **`Cω ∈ L²` for `ω` continuous with compact support and `∫ ω = 0`.**

The proof splits `∫⁻ ‖Cω‖²` into the piece over `Metric.ball 0 s` (bounded by the local
`L²` estimate `cauchyTransform_memLp_ball`) and the piece over `{s ≤ ‖z‖}`, where the
mean-zero decay `decay_zero_mean` bounds the integrand by `const · ‖z‖⁻⁴`, whose exterior
integral is finite. -/
theorem memLp_cauchyTransform_of_zero_mean {ω : ℂ → ℂ} (hω : Continuous ω)
    (hs : HasCompactSupport ω) (h0 : ∫ z, ω z = 0) :
    MemLp (cauchyTransform ω) 2 (volume : Measure ℂ) := by
  have hint : Integrable ω volume := hω.integrable_of_hasCompactSupport hs
  have hae : AEStronglyMeasurable (cauchyTransform ω) volume :=
    Work.MRMT.Cauchy.aestronglyMeasurable_cauchyTransform ω hint
  obtain ⟨R₀, -, hR₀⟩ := Work.MRMT.Beltrami.decay_exists_support_radius ω hs
  set R : ℝ := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ ζ : ℂ, ω ζ ≠ 0 → ‖ζ‖ ≤ R := fun ζ hζ =>
    le_trans (hR₀ ζ hζ) (le_max_left _ _)
  set s : ℝ := max (2 * R) 1 with hsdef
  have hspos : 0 < s := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hs2R : 2 * R ≤ s := le_max_left _ _
  have hω2 : MemLp ω 2 volume := hω.memLp_of_hasCompactSupport hs
  have hsupp_ball : Function.support ω ⊆ Metric.ball 0 (R + 1) := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_zero_right]
    have h := hsupp ζ (Function.mem_support.mp hζ)
    linarith
  have hSm : MeasurableSet {z : ℂ | s ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  -- the bound on the ball `ball 0 s`
  have hlocal : ∫⁻ z in Metric.ball 0 s, ‖cauchyTransform ω z‖ₑ ^ 2 < ⊤ := by
    obtain ⟨hball, -⟩ := cauchyTransform_memLp_ball (h := ω) (R := R + 1) (R' := s)
      (by linarith) hspos hω2 hsupp_ball
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
      (by norm_num) hball.aestronglyMeasurable).mp (memLp_iff.mpr hball)
    simpa [ENNReal.rpow_two] using h1
  -- the bound outside
  have htail : ∫⁻ z in (Metric.ball 0 s)ᶜ, ‖cauchyTransform ω z‖ₑ ^ 2 < ⊤ := by
    have hset : (Metric.ball (0 : ℂ) s)ᶜ = {z : ℂ | s ≤ ‖z‖} := by
      ext z; simp [Metric.mem_ball, not_lt]
    rw [hset]
    have hpoint : ∀ z ∈ {z : ℂ | s ≤ ‖z‖},
        ‖cauchyTransform ω z‖ₑ ^ 2
          ≤ ENNReal.ofReal ((2 * R / Real.pi * (∫ ζ, ‖ω ζ‖)) ^ 2 * ‖z‖ ^ (-4 : ℝ)) := by
      intro z hz
      have hzR : 2 * R ≤ ‖z‖ := le_trans hs2R hz
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hspos hz
      have hdec := decay_zero_mean hint h0 hRpos hsupp hzR
      have h2 : ‖cauchyTransform ω z‖ ^ 2
          ≤ (2 * R / Real.pi * (∫ ζ, ‖ω ζ‖) / ‖z‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdec 2
      have h3 : (2 * R / Real.pi * (∫ ζ, ‖ω ζ‖) / ‖z‖ ^ 2) ^ 2
          = (2 * R / Real.pi * (∫ ζ, ‖ω ζ‖)) ^ 2 * ‖z‖ ^ (-4 : ℝ) := by
        have hzpow : (‖z‖ ^ 2 : ℝ) ^ 2 = ‖z‖ ^ (4 : ℕ) := by ring
        rw [div_pow, hzpow, div_eq_mul_inv, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg hzpos.le, Real.rpow_natCast]
      have h4 : ‖cauchyTransform ω z‖ₑ ^ 2
          = ENNReal.ofReal (‖cauchyTransform ω z‖ ^ 2) := by
        rw [show ‖cauchyTransform ω z‖ₑ = ENNReal.ofReal ‖cauchyTransform ω z‖ by
          simp [enorm_eq_nnnorm]]
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
      rw [h4]
      exact ENNReal.ofReal_le_ofReal (le_trans h2 h3.le)
    calc ∫⁻ z in {z : ℂ | s ≤ ‖z‖}, ‖cauchyTransform ω z‖ₑ ^ 2
        ≤ ∫⁻ z in {z : ℂ | s ≤ ‖z‖},
            ENNReal.ofReal ((2 * R / Real.pi * (∫ ζ, ‖ω ζ‖)) ^ 2 * ‖z‖ ^ (-4 : ℝ)) :=
          setLIntegral_mono' hSm hpoint
      _ < ⊤ := lintegral_ofReal_mul_norm_rpow_neg_four_exterior_lt_top (sq_nonneg _) hspos
  rw [memLp_iff]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)
    hae).mpr ?_
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← lintegral_add_compl (fun z : ℂ => ‖cauchyTransform ω z‖ₑ ^ 2)
    (A := Metric.ball (0 : ℂ) s) measurableSet_ball]
  exact ENNReal.add_lt_top.mpr ⟨hlocal, htail⟩

/-! ## The target -/

theorem memLp_cauchyTransform_dz {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    MeasureTheory.MemLp (cauchyTransform (fun z => dz u z)) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
  memLp_cauchyTransform_of_zero_mean
    (Work.MRMT.Beltrami.continuous_dz_of_contDiff u (by norm_num) hc)
    (hasCompactSupport_dz hs)
    (Work.MRMT.Beltrami.integral_dz_eq_zero_of_contDiff u (n := 1) (by norm_num) hc hs)

end Work.MRMT.Found
