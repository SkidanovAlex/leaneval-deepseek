/-
# `intA` of `HardyHyp` on `(1,∞)` in the open class

This file proves `Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_sq_div_large_open`: for a datum
which is merely `C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`) and honestly
in the weighted space `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), the tail integral
`(L₁₂ f z)²/z^{2j}` is integrable on `(1,∞)` for every `j`.

It is the verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_large`
(`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`) from the interior class
`Work.FTS.LocData.SmoothQuad f` to `SmoothOpen f`.  The helpers of that chain are re-proved
here, in the sub-namespace `LargeAux` (so that they cannot clash with the sibling files
`L12f_bd0_open`, `L12f_bdTop_open`, `L12f_sq_div_small_open`, which re-prove some of the same
auxiliary facts in the plain namespace):

* `LargeAux.slice_sq_integrableOn_open` — the angular slice `θ ↦ f z θ²` is integrable, from
  the pointwise domination `sq_le_HkIntegrand_z` plus a.e. strong measurability of the slice
  by continuity of the datum on the open quadrant (`aesm_slice_of_continuousOn_Qd`);
* `LargeAux.L12dens_abs_le_open` — the density bound
  `|L₁₂dens K f s| ≤ √3 (s/(1+s)²) √(B4 α f s)`;
* `LargeAux.B4_aesm_open`, `LargeAux.B4_sqrt_aesm_open`, `LargeAux.B4_sqrt_aesm_mono_open`,
  `LargeAux.sqrt_B4_memLp_Ioi_open`, `LargeAux.inv_mul_sqrt_B4_integrableOn_open`,
  `LargeAux.L12f_abs_le_large_open` — the a.e. strong measurability of `√(B4 α f ·)` on
  `Iz = [0,∞)`, from `SmoothOpen.continuousOn_HkIntegrand` + `aesm_of_continuousOn_Qd`;
* `LargeAux.G_sq_mul_sq_integrableOn_open`, `LargeAux.L12f_sq_integrableOn_Ioi_one_open`.

The inputs `L12f_eq_neg_prim`, `L12f_continuousOn`, `L12f_aesm_mono`, `B4_integrableOn`,
`B4_tail_tendsto`, `integral_Ioi_inv_sq`, `inv_memLp_Ioi` and `Hardy.Ioi_tail_sq_integrable`
need no smoothness at all and are used as they stand.
-/
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

namespace LargeAux

/-! ## The angular slice and the density bound -/

/-- The squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`, for a datum
which is `C^∞` on the open quadrant and in `ℋ⁴`.  This is
`Work.FTS.H2.l12q_slice_sq_integrableOn` with its smoothness hypothesis weakened from
`SmoothQuad f` to `SmoothOpen f` (the only use of `SmoothQuad` there is the a.e. strong
measurability of the slice). -/
theorem slice_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd ((Function.uncurry f) ^ 2)
      (hsm.continuousOn.pow 2) hz
    simpa only [Function.uncurry, Pi.pow_apply] using h
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

/-- The `L₁₂`-density obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`:
the open-class version of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`. -/
theorem L12dens_abs_le_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
        * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_integrableOn_open α hsm hmem hs
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
      (fun θ hθ => Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq
        α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2) :=
          Real.sqrt_le_sqrt hint
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
            / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s) _
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
        * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3
            * (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2)
            * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-! ## The radial density `B4` and its square root -/

/-- A.e. strong measurability of `B4 α f` on `Iz`, from the joint continuity of the
`ℋ⁴`-integrand on the open quadrant. -/
theorem B4_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn_HkIntegrand α 4
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- A.e. strong measurability of `s ↦ √(B4 α f s)` on `Iz`. -/
theorem B4_sqrt_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (B4_aesm_open α hsm)

/-- The a.e. strong measurability of `s ↦ √(B4 α f s)` restricted to any `u ⊆ Iz`. -/
theorem B4_sqrt_aesm_mono_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (volume.restrict u) :=
  (B4_sqrt_aesm_open α hsm).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- `√(B4 α f ·) ∈ L²((z,∞))` for `z > 0`. -/
theorem sqrt_B4_memLp_Ioi_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) 2
      (volume.restrict (Set.Ioi z)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (B4_sqrt_aesm_mono_open α hsm (fun t ht => le_of_lt (lt_trans hz ht)))).mpr ?_
  refine ((Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set
    (fun t ht => lt_trans hz ht)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Real.sq_sqrt (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s)).symm

/-- The majorant `s ↦ s⁻¹ √(B4 α f s)` is integrable on `(z,∞)` for `z > 0`. -/
theorem inv_mul_sqrt_B4_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun s => s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) (Set.Ioi z) :=
  (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz).integrable_mul
    (sqrt_B4_memLp_Ioi_open α hsm hmem hz)

/-- `|L12f f z| ≤ √3 · √(1/z) · √(∫_{s>z} B4 α f s)` for `z ≥ 1`, in the open class. -/
theorem L12f_abs_le_large_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ}
    (hz1 : 1 ≤ z) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z)
        * Real.sqrt (∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s => s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) (Set.Ioi z) :=
    inv_mul_sqrt_B4_integrableOn_open α hsm hmem hz
  have h1 : |Work.Coercivity.L12f f z| ≤ ∫ s in Set.Ioi z, |G s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (f := G)
      (μ := volume.restrict (Set.Ioi z))
    rw [Work.Coercivity.L12f, Work.FM.L12]
    simpa [G, Real.norm_eq_abs] using h
  have h2 : ∫ s in Set.Ioi z, |G s|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioi z,
          s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (hmaj_int.const_mul (Real.sqrt 3)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hz hs
    have hb := L12dens_abs_le_open α hsm hmem hs0
    have hle : s / (1 + s) ^ 2 ≤ s⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [le_of_lt hs0]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
            * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := hb
      _ ≤ Real.sqrt 3 * s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by ring
  have hcs := Work.Spaces.cs_integral (u := fun s : ℝ => s⁻¹)
    (v := fun s : ℝ => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) (s := Set.Ioi z)
    (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz)
    (sqrt_B4_memLp_Ioi_open α hsm hmem hz)
  have hv2 : ∫ s in Set.Ioi z, (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2
      = ∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    exact Real.sq_sqrt (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s)
  rw [Work.FTS.CoercivityFix.Coer1T.integral_Ioi_inv_sq hz, hv2] at hcs
  have hC : 0 ≤ (1 / z) * ∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s := by
    have : (0 : ℝ) ≤ ∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        (fun s _ => Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s)
    positivity
  have hsqrt : ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
      ≤ Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    have hsq : (∫ s in Set.Ioi z,
          s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2
        ≤ (Real.sqrt ((1 / z)
            * ∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2 := by
      rw [Real.sq_sqrt hC]
      exact hcs
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))
  have hfinal : Real.sqrt 3 * (∫ s in Set.Ioi z,
        s⁻¹ * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z)
        * Real.sqrt (∫ s in Set.Ioi z, Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 3)
    refine le_trans hsqrt (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
  linarith [h1, h2, hfinal]

/-! ## The `L¹`-integrability of the density tail -/

/-- `s ↦ (L12dens K f s)² · s²` is integrable on `(1,∞)`. -/
theorem G_sq_mul_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.FM.L12dens Work.Spaces.K f s) ^ 2 * s ^ 2) (Set.Ioi 1) := by
  have hG : AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12dens_aesm_Ioi hcont
  have hmaj : MeasureTheory.IntegrableOn
      (fun s => 3 * Work.FTS.CoercivityFix.Coer1T.B4 α f s) (Set.Ioi 1) :=
    ((Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)).const_mul 3
  refine hmaj.mono' ((hG.pow 2).mul (continuous_pow 2).aestronglyMeasurable) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hb := L12dens_abs_le_open α hsm hmem hs0
  have hB : 0 ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s :=
    Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s
  have habs := abs_le.mp hb
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hsq : (Work.FM.L12dens Work.Spaces.K f s) ^ 2
      ≤ (Real.sqrt 3 * (s / (1 + s) ^ 2)
          * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2 := by
    nlinarith [habs.1, habs.2]
  refine le_trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg s)) ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt hB]
  rw [div_pow]
  have h4 : s ^ 4 ≤ (1 + s) ^ 4 := by
    have h2 : s ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
    nlinarith [h2, sq_nonneg s, sq_nonneg (s ^ 2)]
  rw [show ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 by ring]
  rw [show 3 * (s ^ 2 / (1 + s) ^ 4) * Work.FTS.CoercivityFix.Coer1T.B4 α f s * s ^ 2
      = 3 * ((s ^ 2 * s ^ 2) / (1 + s) ^ 4) * Work.FTS.CoercivityFix.Coer1T.B4 α f s by ring]
  rw [show s ^ 2 * s ^ 2 = s ^ 4 by ring]
  have h1 : s ^ 4 / (1 + s) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h4
  nlinarith [h1, hB]

/-- `(L12f f z)²` is integrable on `(1,∞)`, in the open class. -/
theorem L12f_sq_integrableOn_Ioi_one_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2) (Set.Ioi 1) := by
  have hG_int := G_sq_mul_sq_integrableOn_open α hsm hmem hcont
  have hGmem : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 1) :=
    hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioi_tail_sq_integrable
    (Work.FM.L12dens Work.Spaces.K f) hG_int hGmem).1
  simpa [Work.Coercivity.L12f, Work.FM.L12] using h

end LargeAux

/-- `intA` of `HardyHyp` on `(1,∞)` in the *open* class: `(L₁₂ f)²/z^{2j} ∈ L¹((1,∞))` for any `j`, from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_large` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`) together with its helpers `L12f_sq_integrableOn_Ioi_one`, `G_sq_mul_sq_integrableOn`, `L12f_abs_le_large`, `inv_mul_sqrt_B4_integrableOn`, `sqrt_B4_memLp_Ioi` re-proved in the open class (put them in the same file); the only uses of `SmoothQuad` in that chain are the a.e. strong measurability of `s ↦ √(B4 α f s)` (from `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (whose open version follows from `Work.Spaces.sq_le_HkIntegrand_z` plus continuity of the angular slice, `Work.Spaces.aesm_slice_of_continuousOn_Qd`).  The inputs `L12f_eq_neg_prim`, `L12f_continuousOn`, `L12f_aesm_mono`, `B4_integrableOn`, `B4_tail_tendsto`, `integral_Ioi_inv_sq`, `inv_memLp_Ioi` and `Hardy.Ioi_tail_sq_integrable` need no smoothness at all. -/
theorem L12f_sq_div_large_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioi 1) := by
  have h1 := LargeAux.L12f_sq_integrableOn_Ioi_one_open α hsm hmem hint hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (Set.Ioi_subset_Ioi zero_le_one)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioi 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (Set.Ioi_subset_Ioi zero_le_one))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h1.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hz1 : 1 ≤ z := le_of_lt hz
  have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ)) := by
    have h2j : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact one_le_pow₀ hz1
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg _) one_pos hzj
    _ = _ := by ring

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
