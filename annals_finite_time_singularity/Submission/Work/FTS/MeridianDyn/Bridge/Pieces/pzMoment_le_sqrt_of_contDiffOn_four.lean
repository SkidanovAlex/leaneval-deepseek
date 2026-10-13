/-
# The `∂_z`-moment of a slice, with only finitely many derivatives

This is the finite-order version of `Work.FTS.CoercivityFix.Coer1T.Hardy.pzMoment_le_sqrt`.
The latter assumes `Work.FTS.LocData.SmoothQuad f` (`C^∞` on the open quadrant); here the
same estimate is derived from the much weaker hypothesis that `f` is only *four* times
continuously differentiable on the open quadrant `Q0 = (0,∞) × (0,π/2)`, together with the
weighted-square integrability `Work.Spaces.HkMem α 4 f`.

Mathematically nothing changes: the proof is the sharp weighted Cauchy–Schwarz step
`∂_z f · sinθcos²θ = (1/z)·(z∂_z f)·sinθcos²θ` with the second factor split by the weight
`sin(2θ)^{-η/2}`.  Only one ingredient of that proof used smoothness, namely continuity on
the open interval of the angular slice `θ ↦ D_z f(z,θ)`, which is obtained here from
`ContDiffOn ℝ 4 (uncurry f) Q0` via `Work.Spaces.uncurry_partial_c1` (the `z`-partial of a
`C²` function is `C¹`).  Everything else — the measure-theoretic identity
`volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`, the term bound
`Work.Spaces.sq_le_HkIntegrand_z`, the elementary factor bounds — is copied verbatim from
the smooth version.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzMoment_le_sqrt
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.CoercivityFix.Coer1T.Hardy (slU slV slU_mul_slV slV_sq_le
  abs_setIntegral_mul_le_sqrt w_pos_of_pos one_le_mul_w sin_two_pos_of_mem_Ioo continuousOn_slV)

/-! ## Continuity of the first Cauchy–Schwarz factor from `C⁴`-smoothness -/

/-- The angular slice `θ ↦ D_z f(z,θ)·w(z)/sin(2θ)^{η/2}` is continuous on the open
interval, for `f` of class `C⁴` on the open quadrant and `z > 0`.

This is the only place where the smoothness hypothesis of `pzMoment_le_sqrt` is used: the
slice continuity there follows from `SmoothQuad`, and here from `ContDiffOn ℝ 4 … Q0`
through `Work.Spaces.uncurry_partial_c1` applied to the `C²`-reduction of `hC`. -/
theorem continuousOn_slU_of_contDiffOn_four {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {s : ℝ} (hs : 0 < s) :
    ContinuousOn (slU f s) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `f` is `C²`, hence `∂_z f` is `C¹` on the open quadrant
  have h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hC.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz f))
      Work.FTS.EllipticEst.Q0 :=
    (Work.Spaces.uncurry_partial_c1 Work.FTS.EllipticEst.isOpen_Q0 h2).1
  -- the angular slice of `∂_z f` at `s > 0`
  have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.pz f s θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hcomp : ContinuousOn
        ((Function.uncurry (Work.Spaces.pz f)) ∘ (fun θ : ℝ => (s, θ)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContinuousOn.comp' (g := Function.uncurry (Work.Spaces.pz f))
        (f := fun θ : ℝ => (s, θ)) hpz.continuousOn
        ((continuous_const.prodMk continuous_id).continuousOn)
        (fun θ hθ => ⟨hs, hθ⟩)
    have hslice_eq : (fun θ : ℝ => Work.Spaces.pz f s θ)
        = (Function.uncurry (Work.Spaces.pz f)) ∘ (fun θ : ℝ => (s, θ)) := rfl
    rwa [hslice_eq]
  -- `D_z f = z ∂_z f`
  have hDz1 : Work.Spaces.DzIter 1 f = Work.Spaces.Dz f := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hDz : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 1 f s θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hDz1]
    exact continuousOn_const.mul hslice
  -- the angular weight `w(s)/sin(2θ)^{η/2}`
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
  have hdiv : ContinuousOn (fun θ : ℝ => Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_const.div hrpow (fun θ hθ =>
      ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _))
  exact hDz.mul hdiv

/-! ## The moment bound -/

theorem pzMoment_le_sqrt_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
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
    continuousOn_slU_of_contDiffOn_four hC hs
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

end Work.FTS.MeridianDyn.Bridge.Pieces
