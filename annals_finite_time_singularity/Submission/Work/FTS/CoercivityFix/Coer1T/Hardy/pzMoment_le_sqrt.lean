/-
Work module for the Elgindi finite-time singularity project.

# The `∂_z`-moment of a slice against the profile `sinθcos²θ`

This file proves `pzMoment_le_sqrt`:

`|∫_{Iθ} ∂_z f(s,θ)·sinθcos²θ dθ| ≤ √(π/2) · √(∫_{Iθ} HkIntegrand α 4 f s θ dθ)`  for `s > 0`,

an elementary Cauchy–Schwarz estimate for the `θ`-slice of the radial derivative of a
profile `f` in the localised-data class (`SmoothQuad f`, `HkMem α 4 f`).

The proof is the sharp weighted Cauchy–Schwarz step:

* on the open interval `(0,π/2)` (the two endpoints are null), write
  `∂_z f·sinθcos²θ = (1/s)·(z∂_z f)·sinθcos²θ` and split the second factor by the weight
  `sin(2θ)^{-η/2}` into the two `L²` factors
  `U θ = z∂_z f(s,θ)·w(s)/sin(2θ)^{η/2}` and `V θ = sin(2θ)^{η/2}·sinθcos²θ / w(s)`;
* `U θ ^ 2` is *literally* the `i = 1` summand of `HkIntegrand α 4 f s θ`
  (`Work.Spaces.sq_le_HkIntegrand_z`), so `√(∫ U²) ≤ √(∫ HkIntegrand)`;
* `V θ ^ 2 ≤ 1/w(s)²` because `sin(2θ)^{η/2} ≤ 1` and `|sinθcos²θ| ≤ 1` on the interval, so
  `√(∫ V²) ≤ √(π/2)/w(s)`;
* `s·w(s) = (1+s)²/s ≥ 1` absorbs the remaining factor.

Everything is elementary; the content is the choice of the two factors and the bookkeeping
of the weight `w(z) = (1+z)²/z²`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the radial weight `w` -/

/-- The radial weight `w(z) = (1+z)²/z²` is positive for `z > 0`. -/
theorem w_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Work.Spaces.w s := by
  rw [Work.Spaces.w]
  positivity

/-- `s·w(s) = (1+s)²/s ≥ 1` for `s > 0`: the factor by which the Cauchy–Schwarz step
overcounts is bounded by `1`. -/
theorem one_le_mul_w {s : ℝ} (hs : 0 < s) : 1 ≤ s * Work.Spaces.w s := by
  have hsw : s * Work.Spaces.w s = (1 + s) ^ 2 / s := by
    rw [Work.Spaces.w]
    field_simp
  rw [hsw, le_div_iff₀ hs]
  nlinarith [sq_nonneg s]

/-! ## Cauchy–Schwarz in square-root form -/

/-- The Cauchy–Schwarz inequality for the Bochner integral in its `√`-form. -/
theorem abs_setIntegral_mul_le_sqrt {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MemLp u 2 (volume.restrict s)) (hv : MemLp v 2 (volume.restrict s)) :
    |∫ x in s, u x * v x| ≤ Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
  have hcs := Work.Spaces.cs_integral hu hv
  have hA : 0 ≤ ∫ x in s, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  calc |∫ x in s, u x * v x| = Real.sqrt ((∫ x in s, u x * v x) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x in s, u x ^ 2) * (∫ x in s, v x ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := Real.sqrt_mul hA _

/-! ## The two Cauchy–Schwarz factors -/

/-- The `L²`-factor carrying `D_z f = z ∂_z f`; its square is a summand of `HkIntegrand`. -/
def slU (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun θ => Work.Spaces.DzIter 1 f s θ
    * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

/-- The dual `L²`-factor, carrying the profile `sinθcos²θ` and the reciprocal weight. -/
def slV (_f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ
    / Work.Spaces.w s

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On the open interval the two factors multiply back to `D_z f · sinθcos²θ`. -/
theorem slU_mul_slV {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    slU f s θ * slV f s θ = Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ := by
  have hx : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _)
  have hW : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos_of_pos hs)
  have hcancel : (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w s) = 1 := by
    field_simp
  calc slU f s θ * slV f s θ
      = (Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ)
        * ((Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w s)) := by
        simp only [slU, slV]; ring
    _ = Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ := by rw [hcancel, mul_one]

/-- The dual factor is bounded by `1/w(s)` in absolute value on the open interval:
`sin(2θ)^{η/2} ≤ 1` and `|sinθcos²θ| ≤ 1`. -/
theorem slV_sq_le {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (slV f s θ) ^ 2 ≤ (1 / Work.Spaces.w s) ^ 2 := by
  have hx : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hsp : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hx) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hc : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
    Work.FTS.EllipticEst.abs_sinCos2_le_one ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hprod : |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx) _)]
    simpa using mul_le_mul hsp hc (abs_nonneg _) zero_le_one
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      * Work.Elliptic.sinCos2 θ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hprod
  have hW2 : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (w_pos_of_pos hs) 2
  simp only [slV, div_pow, one_pow]
  exact div_le_div_of_nonneg_right hsq (le_of_lt hW2)

/-! ## Continuity of the two factors on the open interval -/

theorem continuousOn_slice_DzIter_div_sin {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) {s : ℝ} (hs : 0 < s) (i : ℕ) :
    ContinuousOn (fun θ => Work.Spaces.DzIter i f s θ
      * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsl : ContinuousOn (fun θ => Work.Spaces.DzIter i f s θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.LocData.contDiffOn_slice_θ
      (Work.FTS.LocData.contDiffOn_DzIter (isOpen_Ioi.prod isOpen_Ioo) hsm i)
      (show s ∈ Set.Ioi (-1) by simp only [Set.mem_Ioi]; linarith)).continuousOn
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
  exact hsl.mul (continuousOn_const.div hrpow (fun θ hθ =>
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _)))

theorem continuousOn_slU {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {s : ℝ} (hs : 0 < s) : ContinuousOn (slU f s) (Set.Ioo 0 (Real.pi / 2)) :=
  continuousOn_slice_DzIter_div_sin hsm hs 1

theorem continuousOn_slV (f : ℝ → ℝ → ℝ) (s : ℝ) :
    ContinuousOn (slV f s) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
  have hcos : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      Real.continuous_sin.continuousOn.mul ((Real.continuous_cos.continuousOn).pow 2)
    exact h.congr (fun θ _ => rfl)
  exact (hrpow.mul hcos).div_const (Work.Spaces.w s)

/-! ## The moment bound -/

theorem pzMoment_le_sqrt (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s →
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
        ≤ Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
  intro s hs
  -- ## The open interval carries all the measure
  have hIoo_sub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hIoo_meas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hms : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (Real.pi / 2) from rfl,
        Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
      rw [Set.insert_eq]
      exact measure_union_null (measure_singleton 0) (measure_singleton _)
    · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (Real.pi / 2) from rfl,
        Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  -- ## Integrability of the `ℋ⁴`-integrand
  have hHmem : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
    hmem.1 s (le_of_lt hs)
  have hHmem_oo : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hHmem.mono_set hIoo_sub
  -- ## The two `L²` factors
  have hcontU : ContinuousOn (slU f s) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slU hsm hs
  have hcontV : ContinuousOn (slV f s) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slV f s
  have hUaesm : AEStronglyMeasurable (slU f s)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontU.aestronglyMeasurable hIoo_meas
  have hVaesm : AEStronglyMeasurable (slV f s)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontV.aestronglyMeasurable hIoo_meas
  -- the square of `slU` is the `i = 1` summand of `HkIntegrand`
  have hU2int : Integrable (fun θ => (slU f s θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    Integrable.mono' hHmem_oo ((hcontU.pow 2).aestronglyMeasurable hIoo_meas)
      (Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num))
  have hUm : MemLp (slU f s) 2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (memLp_two_iff_integrable_sq hUaesm).mpr hU2int
  -- the square of `slV` is bounded by the constant `(1/w(s))²`
  have hV2int : Integrable (fun θ => (slV f s θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    Integrable.mono' (integrable_const ((1 / Work.Spaces.w s) ^ 2))
      ((hcontV.pow 2).aestronglyMeasurable hIoo_meas)
      (by
        filter_upwards [ae_restrict_mem hIoo_meas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact slV_sq_le hs hθ)
  have hVm : MemLp (slV f s) 2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (memLp_two_iff_integrable_sq hVaesm).mpr hV2int
  -- ## Cauchy–Schwarz
  have hcs : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ|
      ≤ Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slU f s θ) ^ 2)
        * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slV f s θ) ^ 2) :=
    abs_setIntegral_mul_le_sqrt hUm hVm
  have hUV : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ :=
    setIntegral_congr_fun hIoo_meas fun θ hθ => slU_mul_slV hs hθ
  -- ## The key identity: the moment is `1/s` times the Cauchy–Schwarz integral
  have h1 : ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ
      = s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun hIθ_meas (fun θ _ => ?_)
    show s * Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ
      = s * (Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ)
    ring
  have h2 : ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
    rw [hms]
    exact setIntegral_congr_fun hIoo_meas fun θ hθ => (slU_mul_slV hs hθ).symm
  have hkey : ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ
      = (1 / s) * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
    have h3 : s * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ := by
      rw [← h1, h2]
    rw [← h3, ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hs), one_mul]
  -- ## Abbreviations for the four scalar quantities of the final estimate
  set AU := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slU f s θ) ^ 2 with hAU
  set AV := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (slV f s θ) ^ 2 with hAV
  set HH := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ with hHH
  set W := Work.Spaces.w s with hW
  set A := Real.sqrt AU with hA
  set VV := Real.sqrt AV with hVV
  set B := Real.sqrt (Real.pi / 2) with hB
  set H := Real.sqrt HH with hH
  -- ## The two square-root bounds
  have hU2sqrt : A ≤ H := by
    apply Real.sqrt_le_sqrt
    rw [hHH, hms]
    exact integral_mono hU2int hHmem_oo.integrable
      (fun θ => Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 1 (by norm_num))
  have hV2_le : AV ≤ (1 / W) ^ 2 * (Real.pi / 2) := by
    rw [hAV, hW]
    have hvol : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
      (f := fun θ => (slV f s θ) ^ 2) (C := (1 / Work.Spaces.w s) ^ 2) hvol
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact slV_sq_le hs hθ)
    rwa [Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0), sub_zero,
      Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)] at h
  have hV2sqrt : VV ≤ B * (1 / W) := by
    have hstep : Real.sqrt AV ≤ Real.sqrt ((1 / W) ^ 2 * (Real.pi / 2)) :=
      Real.sqrt_le_sqrt hV2_le
    have hrew : Real.sqrt ((1 / W) ^ 2 * (Real.pi / 2)) = B * (1 / W) := by
      rw [hB, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (le_of_lt (one_div_pos.mpr (w_pos_of_pos hs))), mul_comm]
    rw [hrew] at hstep
    exact hstep
  -- ## The numerical core
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hWpos : 0 < W := w_pos_of_pos hs
  have hSW : 1 ≤ s * W := one_le_mul_w hs
  have hSWpos : 0 < s * W := lt_of_lt_of_le zero_lt_one hSW
  have hfin : (1 / s) * (A * (B * (1 / W))) ≤ B * H := by
    have hB1W : 0 ≤ B * (1 / W) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (one_div_pos.mpr hWpos))
    have hmul : A * (B * (1 / W)) ≤ H * (B * (1 / W)) :=
      mul_le_mul_of_nonneg_right hU2sqrt hB1W
    have hmain : (1 / s) * (H * (B * (1 / W))) = (H * B) / (s * W) := by
      field_simp
    have h2le : (H * B) / (s * W) ≤ B * H := by
      rw [div_le_iff₀ hSWpos]
      calc H * B ≤ H * B * (s * W) :=
            le_mul_of_one_le_right (mul_nonneg hH0 (Real.sqrt_nonneg _)) hSW
        _ = (B * H) * (s * W) := by ring
    calc (1 / s) * (A * (B * (1 / W))) ≤ (1 / s) * (H * (B * (1 / W))) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt (one_div_pos.mpr hs))
      _ = (H * B) / (s * W) := hmain
      _ ≤ B * H := h2le
  -- ## Assembly
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
      = (1 / s) * |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), slU f s θ * slV f s θ| := by
        rw [hkey, abs_mul, abs_of_pos (one_div_pos.mpr hs)]
    _ ≤ (1 / s) * (A * VV) :=
        mul_le_mul_of_nonneg_left hcs (le_of_lt (one_div_pos.mpr hs))
    _ ≤ (1 / s) * (A * (B * (1 / W))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr hs))
        exact mul_le_mul_of_nonneg_left hV2sqrt (Real.sqrt_nonneg _)
    _ ≤ B * H := hfin

end Work.FTS.CoercivityFix.Coer1T.Hardy
