import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.L12ZeroQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

open Work.FTS.CoercivityFix.Coer1T (B4 B4_nonneg B4_integrableOn B4_tail_tendsto)

set_option maxHeartbeats 800000

/-! ## The open-class prerequisites of the large-`z` estimate for `L₁₂`

`Work.FTS.CoercivityFix.Coer1T.L12f_bdTop` is proved from the large-`z` bound
`L12f_abs_le_large`, whose proof uses `SmoothQuad` only through

* the a.e. strong measurability of `s ↦ √(B4 α f s)` on `(z,∞)` (via `B4_sqrt_aesm_mono`),
  which in the open class comes from `SmoothOpen.continuousOn_HkIntegrand` +
  `Work.Spaces.aesm_of_continuousOn_Qd`;
* the density bound `dens_abs_le`, whose proof uses `SmoothQuad` only through the
  slice-square integrability `l12q_slice_sq_integrableOn`, i.e. through joint continuity of
  `(z,θ) ↦ (f z θ)²` on the open quadrant.

Both uses are replaced below by their `SmoothOpen` analogues.  Everything else in the chain
(`B4_integrableOn`, `dens`-domination by `HkIntegrand`, Cauchy–Schwarz, `B4_tail_tendsto`,
`integral_Ioi_inv_sq`, `inv_memLp_Ioi`) is hypothesis-free apart from `HkMem α 4 f`, so those
lemmas are re-used as they are. -/

/-- Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant, from `SmoothOpen f`. -/
theorem bdTop_continuousOn_quad_sq {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 := by
  rw [show (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      = (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) from by funext p; rfl]
  exact ((hF.forall 0).continuousOn).pow 2

/-- The squared angular slice is integrable on `Iθ` for `z > 0`, from `SmoothOpen f` and
`HkMem α 4 f` (the open-class analogue of `Work.FTS.H2.l12q_slice_sq_integrableOn`). -/
theorem bdTop_slice_sq_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (bdTop_continuousOn_quad_sq hF) hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- A.e. strong measurability of `B4 α f = ∫_θ HkIntegrand α 4 f` on `Iz`, from `SmoothOpen f`
(open analogue of `B4_aesm`). -/
theorem bdTop_B4_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (B4 α f) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (hF.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- A.e. strong measurability of `s ↦ √(B4 α f s)` on `Iz`, from `SmoothOpen f`. -/
theorem bdTop_B4_sqrt_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (bdTop_B4_aesm α hF)

theorem bdTop_B4_sqrt_aesm_mono (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s))
      (MeasureTheory.volume.restrict u) :=
  (bdTop_B4_sqrt_aesm α hF).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

theorem bdTop_sqrt_B4_memLp_Ioi (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => Real.sqrt (B4 α f s)) 2 (volume.restrict (Set.Ioi z)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (bdTop_B4_sqrt_aesm_mono α hF (fun t ht => le_of_lt (lt_trans hz ht)))).mpr ?_
  refine ((B4_integrableOn α f hmem).mono_set
    (fun t ht => lt_trans hz ht)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Real.sq_sqrt (B4_nonneg α f s)).symm

/-- The majorant `s ↦ s⁻¹ √(B4 α f s)` is integrable on `(z,∞)` for `z > 0`. -/
theorem bdTop_inv_mul_sqrt_B4_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
  (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz).integrable_mul
    (bdTop_sqrt_B4_memLp_Ioi α hF hmem hz)

/-- The `L₁₂`-density obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`;
open-class version of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`. -/
theorem bdTop_dens_abs_le (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {s : ℝ} (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    bdTop_slice_sq_integrableOn α hF hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ =>
        Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (B4 α f s / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hint
      _ = Real.sqrt (B4 α f s) / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (B4_nonneg α f s) _
      _ = Real.sqrt (B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3 * (Real.sqrt (B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-- `|L12f f z| ≤ √3 · √(1/z) · √(∫_{s>z} B4 α f s)` for `z ≥ 1`; open-class version of
`Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_large`. -/
theorem bdTop_L12f_abs_le_large (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz1 : 1 ≤ z) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
    bdTop_inv_mul_sqrt_B4_integrableOn α hF hmem hz
  have h1 : |Work.Coercivity.L12f f z| ≤ ∫ s in Set.Ioi z, |G s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (f := G)
      (μ := volume.restrict (Set.Ioi z))
    rw [Work.Coercivity.L12f, Work.FM.L12]
    simpa [G, Real.norm_eq_abs] using h
  have h2 : ∫ s in Set.Ioi z, |G s|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (hmaj_int.const_mul (Real.sqrt 3)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hz hs
    have hb := bdTop_dens_abs_le α hF hmem hs0
    have hle : s / (1 + s) ^ 2 ≤ s⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [le_of_lt hs0]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := hb
      _ ≤ Real.sqrt 3 * s⁻¹ * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s⁻¹ * Real.sqrt (B4 α f s)) := by ring
  have hcs := Work.Spaces.cs_integral (u := fun s : ℝ => s⁻¹)
    (v := fun s : ℝ => Real.sqrt (B4 α f s)) (s := Set.Ioi z)
    (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz)
    (bdTop_sqrt_B4_memLp_Ioi α hF hmem hz)
  have hv2 : ∫ s in Set.Ioi z, (Real.sqrt (B4 α f s)) ^ 2 = ∫ s in Set.Ioi z, B4 α f s := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    exact Real.sq_sqrt (B4_nonneg α f s)
  rw [Work.FTS.CoercivityFix.Coer1T.integral_Ioi_inv_sq hz, hv2] at hcs
  have hC : 0 ≤ (1 / z) * ∫ s in Set.Ioi z, B4 α f s := by
    have : (0 : ℝ) ≤ ∫ s in Set.Ioi z, B4 α f s :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
    positivity
  have hsqrt : ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)
      ≤ Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
    have hsq : (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)) ^ 2
        ≤ (Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s)) ^ 2 := by
      rw [Real.sq_sqrt hC]
      exact hcs
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))
  have hfinal : Real.sqrt 3 * (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s))
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 3)
    refine le_trans hsqrt (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
  linarith [h1, h2, hfinal]

/-- `bdTop` of `HardyHyp` in the *open* class: the two boundary terms `(L₁₂ f)²/z^{2j-1}` and `w z·(L₁₂ f)²` vanish as `z → ∞` (any `j`), from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_bdTop` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), which squeezes both terms against `3·∫_{(z,∞)} B4 α f` (resp. `12·`) using the large-`z` estimate `|L₁₂ f z| ≤ √3·√(1/z)·√(∫_{(z,∞)} B4 α f)` for `1 ≤ z` and `B4_tail_tendsto` (both hypothesis-free apart from `HkMem`).  The large-`z` estimate is the open-class adaptation of `L12f_abs_le_large`/`inv_mul_sqrt_B4_integrableOn`/`sqrt_B4_memLp_Ioi` (helper lemmas may be proved inside the same file), whose only `SmoothQuad` use is the a.e. strong measurability of `s ↦ √(B4 α f s)` (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (open version from `Work.Spaces.sq_le_HkIntegrand_z`). -/
theorem L12f_bdTop_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        Filter.atTop (nhds 0) := by
  have hT : Filter.Tendsto (fun z => ∫ s in Set.Ioi z, B4 α f s) Filter.atTop (𝓝 0) :=
    B4_tail_tendsto α f
  have hmem1 : Set.Ici (1 : ℝ) ∈ Filter.atTop := Filter.Ici_mem_atTop 1
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 3)
    · filter_upwards [hmem1] with z hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz0 _))
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := bdTop_L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have habs := abs_le.mp hX
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) * z := by
        have h2j : (-1 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
          have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
          linarith
        have h3 : z ^ (-1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hz1 h2j
        rw [Real.rpow_neg_one] at h3
        have := mul_le_mul_of_nonneg_right h3 hz0.le
        rw [inv_mul_cancel₀ (ne_of_gt hz0)] at this
        linarith
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by
        have hz_inv : 1 / z ≤ z ^ (2 * (j : ℝ) - 1) := (div_le_iff₀ hz0).mpr hzj
        have hstep2 : 3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)
            ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) * z ^ (2 * (j : ℝ) - 1) := by
          have h3T : (0 : ℝ) ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by linarith
          have := mul_le_mul_of_nonneg_right hz_inv h3T
          nlinarith [this]
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hz0 (2 * (j : ℝ) - 1))]
        linarith [hsq', hstep2]
      exact hstep
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := bdTop_L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have habs := abs_le.mp hX
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 * z ^ 2 := by nlinarith [hz1, sq_nonneg z, sq_nonneg (z - 1)]
      have hz2 : (0 : ℝ) < z ^ 2 := by positivity
      have hstep2 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
        have h5 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
            ≤ 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)) :=
          mul_le_mul h4 hsq' (sq_nonneg _) (by positivity)
        have h6 : 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s))
            = 12 * (∫ s in Set.Ioi z, B4 α f s) * z := by
          field_simp
          ring
        rw [h6] at h5
        have h7 : 12 * (∫ s in Set.Ioi z, B4 α f s) * z
            ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
          have := mul_le_mul_of_nonneg_left hz1
            (by linarith : (0:ℝ) ≤ 12 * (∫ s in Set.Ioi z, B4 α f s))
          nlinarith [this]
        linarith [h5, h7]
      rw [hw, div_mul_eq_mul_div, div_le_iff₀ hz2]
      linarith [hstep2]

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
