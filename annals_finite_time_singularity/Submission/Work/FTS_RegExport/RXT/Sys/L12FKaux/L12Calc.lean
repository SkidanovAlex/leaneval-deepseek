import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.L12_Fstar_add_c4
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.majorant_tail
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.L12Calc` — the `L₁₂`-calculus for the profile `F(τ) = F_* + slice g τ`

* `dens_Fstar`, `abs_Fstar_le` — the density of the reference profile and its pointwise bound;
* `dens_add` — `L₁₂dens (F_* + u) = L₁₂dens F_* + L₁₂dens u` for `u` in the standing class;
* `abs_L12_le_majorant` — `|L₁₂ u z| ≤ 3(π/2) C₀ · 3` for `u` in the standing class;
* `abs_L12_Fstar_add_le` — the same for `F_* + u`;
* `dens_tendsto`, `L12_tendsto` — the convergence of the density and of `L₁₂` along the
  approximating families of `LimApprox` (dominated convergence in `θ`, then in `s`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The density of the reference profile -/

/-- `SW s / s = s^{1/2}/(1+s)²`. -/
theorem SW_div (s : ℝ) (hs : 0 < s) : SW s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h := Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs
  simpa only [SW, Work.FTS_RegExport.RXT.L12Iter.Rwt] using h

/-- `|F_*(z,θ)| ≤ 20β z/(1+z)²` for `θ ∈ Iθ`, `z > 0`. -/
theorem abs_Fstar_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar β z θ| ≤ 20 * β * (z / (1 + z) ^ 2) := by
  have hc := (Work.Spaces.c_bounds β hβ hβ1).1
  have hg := Work.Spaces.Gam_bounds β θ hβ hθ
  have hcpos : 0 < Work.Spaces.c β := by linarith
  have hrad : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
  have h1 : |Work.Spaces.Gam β θ / Work.Spaces.c β| ≤ 10 := by
    rw [abs_of_nonneg (div_nonneg hg.1 hcpos.le), div_le_iff₀ hcpos]
    nlinarith [hg.2, hc]
  rw [Work.Construction.Fstar, Work.FM.Fstar, abs_mul, abs_mul,
    abs_of_pos hβ, abs_of_nonneg hrad]
  calc β * |Work.Spaces.Gam β θ / Work.Spaces.c β| * (2 * z / (1 + z) ^ 2)
      ≤ β * 10 * (2 * z / (1 + z) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hβ.le) hrad
    _ = 20 * β * (z / (1 + z) ^ 2) := by ring

/-- The density of the reference profile. -/
theorem dens_Fstar {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (Work.Construction.Fstar β) s = 2 * β / (1 + s) ^ 2 := by
  have hcne : Work.Spaces.c β ≠ 0 := by
    have h := (Work.Spaces.c_bounds β hβ hβ1).1
    intro h0; rw [h0] at h; norm_num at h
  have hsne : s ≠ 0 := ne_of_gt hs
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hc : (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * Work.Spaces.Gam β θ)
      = Work.Spaces.c β := by
    rw [Work.Spaces.c]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar β s θ / s
      = (Work.Spaces.K θ * Work.Spaces.Gam β θ)
          * (β * (2 * s / (1 + s) ^ 2) / s / Work.Spaces.c β) := by
    intro θ; rw [Work.Construction.Fstar, Work.FM.Fstar]; ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.integral_mul_const, hc]
  field_simp

/-! ## §2 Additivity of the density for `F_* + u` -/

/-- **Additivity of the `L₁₂`-density on `F_* + u`**, for `u` in the standing class. -/
theorem dens_add {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (fun z θ => Work.Construction.Fstar β z θ + u z θ) s
      = 2 * β / (1 + s) ^ 2 + Work.Construction.L12dens u s := by
  have hFstar_cont : ContinuousOn (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1).continuousOn
  have hu_cont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0 := h4.continuousOn
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  -- integrability of the reference part
  have hintF : Integrable (fun θ => Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
      (volume.restrict (Icc 0 (Real.pi / 2))) := by
    refine Integrable.mono' (integrable_const (3 * (20 * β * (1 / (1 + s) ^ 2)))) ?_ ?_
    · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
        (g := fun x θ => Work.Spaces.K θ * Work.Construction.Fstar β x θ / s) ?_ hs
      have hfun : Function.uncurry
          (fun x θ => Work.Spaces.K θ * Work.Construction.Fstar β x θ / s)
          = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Construction.Fstar β p.1 p.2 / s := rfl
      rw [hfun]
      exact (hK_cont.mul hFstar_cont).div_const s
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hK0 : Work.Spaces.K 0 = 0 := by
          rw [Work.Spaces.K, Real.sin_zero]; ring
        rw [hK0, zero_mul, zero_div, norm_zero]
        positivity
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
          rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
        rw [hK1, zero_mul, zero_div, norm_zero]
        positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
      have hF := abs_Fstar_le (β := β) (z := s) (θ := θ) hβ hβ1 hs
        ⟨h0.le, h1.le⟩
      have hK := abs_K_le_three θ
      have hprod : |Work.Spaces.K θ| * |Work.Construction.Fstar β s θ|
          ≤ 3 * (20 * β * (s / (1 + s) ^ 2)) :=
        mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      calc |Work.Spaces.K θ| * |Work.Construction.Fstar β s θ| / s
          ≤ 3 * (20 * β * (s / (1 + s) ^ 2)) / s :=
            div_le_div_of_nonneg_right hprod hs.le
        _ = 3 * (20 * β * (1 / (1 + s) ^ 2)) := by
            field_simp
  -- integrability of the `u` part
  have hintU : Integrable (fun θ => Work.Spaces.K θ * u s θ / s)
      (volume.restrict (Icc 0 (Real.pi / 2))) := by
    have hbound : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.K θ * u s θ / s| ≤ 3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
      intro θ hθ0 hθ1
      rw [abs_div, abs_of_pos hs, abs_mul]
      have hF := hbd 0 (by norm_num) s θ hs hθ0 hθ1
      have hK := abs_K_le_three θ
      have hprod : |Work.Spaces.K θ| * |u s θ| ≤ 3 * (C0 * SW s) :=
        mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      refine le_trans (div_le_div_of_nonneg_right hprod hs.le) (le_of_eq ?_)
      calc 3 * (C0 * SW s) / s = 3 * C0 * (SW s / s) := by field_simp
        _ = 3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
            rw [SW_div s hs]; ring
    refine Integrable.mono' (integrable_const (3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))))
      ?_ ?_
    · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
        (g := fun x θ => Work.Spaces.K θ * u x θ / s) ?_ hs
      have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * u x θ / s)
          = fun p : ℝ × ℝ => Work.Spaces.K p.2 * u p.1 p.2 / s := rfl
      rw [hfun]
      exact (hK_cont.mul hu_cont).div_const s
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hK0 : Work.Spaces.K 0 = 0 := by
          rw [Work.Spaces.K, Real.sin_zero]; ring
        rw [hK0, zero_mul, zero_div, norm_zero]
        positivity
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
          rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
        rw [hK1, zero_mul, zero_div, norm_zero]
        positivity
      exact hbound θ h0 h1
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Construction.L12dens,
    Work.FM.L12dens]
  have hFs : (∫ θ in Icc 0 (Real.pi / 2),
        Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
      = 2 * β / (1 + s) ^ 2 := dens_Fstar hβ hβ1 hs
  have hcongr : (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ
        * (Work.Construction.Fstar β s θ + u s θ) / s)
      = (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
        + (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * u s θ / s) := by
    rw [← MeasureTheory.integral_add hintF hintU]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  rw [hcongr, hFs]

/-! ## §3 Bounds for `L₁₂` -/

/-- **The `L₁₂`-bound for a datum of the standing class.** -/
theorem abs_L12_le_majorant {u : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 u z| ≤ 3 * (Real.pi / 2) * C0 * 3 := by
  obtain ⟨hmajint, hmajbd⟩ := majorant_tail hz
  have hInt : Integrable (Work.FM.L12dens Work.Spaces.K u) (volume.restrict (Set.Ioi z)) :=
    Work.FTS_RegExport.RXT.L12Iter.L12dens_integrableOn hC0 h4 hbd hz
  have hbd' : ∀ s ∈ Set.Ioi z,
      |Work.FM.L12dens Work.Spaces.K u s|
        ≤ 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
    fun s hs => Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hC0 h4 hbd (lt_trans hz hs)
  have h1 : |Work.Construction.L12 u z|
      ≤ ∫ s in Set.Ioi z, |Work.FM.L12dens Work.Spaces.K u s| := by
    rw [Work.Construction.L12, Work.FM.L12]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.FM.L12dens Work.Spaces.K u s))
  have hmajint' : Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (volume.restrict (Set.Ioi z)) := hmajint.const_mul _
  have h2 : ∫ s in Set.Ioi z, |Work.FM.L12dens Work.Spaces.K u s|
      ≤ ∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    refine MeasureTheory.integral_mono_ae hInt.abs hmajint' ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hbd' s hs
  have h3 : ∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      = 3 * (Real.pi / 2) * C0
          * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  have h4' : 3 * (Real.pi / 2) * C0 * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
      ≤ 3 * (Real.pi / 2) * C0 * 3 := by
    refine mul_le_mul_of_nonneg_left hmajbd ?_
    positivity
  linarith [h1, h2, le_of_eq h3, h4']

/-- **The `L₁₂`-bound for `F_* + u`**, `u` in the standing class. -/
theorem abs_L12_Fstar_add_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ}
    {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hHk : Work.Spaces.HkMem β 4 u)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 (fun z θ => Work.Construction.Fstar β z θ + u z θ) z|
      ≤ 2 * β + 3 * (Real.pi / 2) * C0 * 3 := by
  rw [Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hβ hβ1 h4 hHk hz.le]
  have hFs : Work.Construction.L12 (Work.Construction.Fstar β) z = 2 * β / (1 + z) :=
    Work.Construction.L12_Fstar_eq hβ hβ1 hz.le
  have h1 : 2 * β / (1 + z) ≤ 2 * β := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + z)]
    nlinarith [hβ]
  have h2 := abs_L12_le_majorant hC0 h4 hbd hz
  calc |Work.Construction.L12 (Work.Construction.Fstar β) z
        + Work.Construction.L12 u z|
      ≤ |Work.Construction.L12 (Work.Construction.Fstar β) z|
          + |Work.Construction.L12 u z| := abs_add_le _ _
    _ ≤ 2 * β + 3 * (Real.pi / 2) * C0 * 3 := by
        rw [hFs, abs_of_pos (by positivity : (0 : ℝ) < 2 * β / (1 + z))]
        linarith


/-! ## §4 Convergence of the density and of `L₁₂` along the approximating families -/

/-- **Dominated convergence in `θ`**: the `L₁₂`-density of `F(n) = F_* + slice (gn n) τ`
converges to that of `F = F_* + slice h τ`. -/
theorem dens_tendsto {β Cw : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hCw : 0 ≤ Cw)
    {gn : ℕ → Fam} {h : Fam} {τ : ℝ}
    (h4 : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop (𝓝 (slice h τ z θ)))
    {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun n => Work.Construction.L12dens (Work.Construction.Ftau β (gn n) τ) s)
      Filter.atTop (𝓝 (Work.Construction.L12dens (Work.Construction.Ftau β h τ) s)) := by
  have hFstar_cont : ContinuousOn (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1).continuousOn
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hMn : 0 ≤ 20 * β * (1 / (1 + s) ^ 2) + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    positivity
  have hFtau_eq : ∀ (n : ℕ) (x θ : ℝ),
      Work.Construction.Ftau β (gn n) τ x θ
        = Work.Construction.Fstar β x θ + slice (gn n) τ x θ := fun n x θ => rfl
  have hFtau_eq' : ∀ (x θ : ℝ),
      Work.Construction.Ftau β h τ x θ
        = Work.Construction.Fstar β x θ + slice h τ x θ := fun x θ => rfl
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc 0 (Real.pi / 2)))
    (F := fun n a => Work.Spaces.K a * Work.Construction.Ftau β (gn n) τ s a / s)
    (f := fun a => Work.Spaces.K a * Work.Construction.Ftau β h τ s a / s)
    (bound := fun _ => 3 * (20 * β * (1 / (1 + s) ^ 2)
      + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
    ?_ ?_ ?_ ?_
  · -- measurability
    intro n
    refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => Work.Spaces.K θ * Work.Construction.Ftau β (gn n) τ x θ / s) ?_ hs
    have hfun : Function.uncurry
        (fun x θ => Work.Spaces.K θ * Work.Construction.Ftau β (gn n) τ x θ / s)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2
            * Work.Construction.Ftau β (gn n) τ p.1 p.2 / s := rfl
    rw [hfun]
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.Ftau β (gn n) τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Construction.Ftau β (gn n) τ p.1 p.2)
          = fun p : ℝ × ℝ =>
              Work.Construction.Fstar β p.1 p.2 + slice (gn n) τ p.1 p.2 := by
        funext p; rw [hFtau_eq]
      rw [hfun2]
      exact hFstar_cont.add (h4 n).continuousOn
    exact (hK_cont.mul hcont).div_const s
  · -- integrability of the constant bound
    exact MeasureTheory.integrable_const _
  · -- the a.e. domination
    intro n
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun a ha => ?_)
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      rw [hK0, zero_mul, zero_div, norm_zero]
      positivity
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hK1, zero_mul, zero_div, norm_zero]
      positivity
    have hcongr : Work.Spaces.K a * Work.Construction.Ftau β (gn n) τ s a / s
        = Work.Spaces.K a * (Work.Construction.Fstar β s a + slice (gn n) τ s a) / s := by
      rw [hFtau_eq n s a]
    rw [Real.norm_eq_abs, hcongr, abs_div, abs_of_pos hs, abs_mul]
    have hFs := abs_Fstar_le (β := β) (z := s) (θ := a) hβ hβ1 hs ⟨h0.le, h1.le⟩
    have hu := hbd n 0 (by norm_num) s a hs h0 h1
    have hsum : |Work.Construction.Fstar β s a + slice (gn n) τ s a|
        ≤ 20 * β * (s / (1 + s) ^ 2) + Cw * SW s := by
      refine le_trans (abs_add_le _ _) (add_le_add hFs hu)
    have hK := abs_K_le_three a
    have hprod : |Work.Spaces.K a| * |Work.Construction.Fstar β s a + slice (gn n) τ s a|
        ≤ 3 * (20 * β * (s / (1 + s) ^ 2) + Cw * SW s) :=
      mul_le_mul hK hsum (abs_nonneg _) (by norm_num)
    refine le_trans (div_le_div_of_nonneg_right hprod hs.le) (le_of_eq ?_)
    calc 3 * (20 * β * (s / (1 + s) ^ 2) + Cw * SW s) / s
        = 3 * (20 * β * (1 / (1 + s) ^ 2) + Cw * (SW s / s)) := by field_simp
      _ = 3 * (20 * β * (1 / (1 + s) ^ 2)
            + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by rw [SW_div s hs]
  · -- the a.e. convergence of the integrands
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun a ha => ?_)
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul, zero_div]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul, zero_div]
      exact tendsto_const_nhds
    have ht := hconv s a ⟨hs, h0, h1⟩
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.add ht)).div_const s

/-- **The `L₁₂`-convergence along the approximating families.** -/
theorem L12_tendsto {β Cw : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hCw : 0 ≤ Cw)
    {gn : ℕ → Fam} {h : Fam} {τ : ℝ}
    (h4 : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop (𝓝 (slice h τ z θ)))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n => Work.Construction.L12 (Work.Construction.Ftau β (gn n) τ) z)
      Filter.atTop (𝓝 (Work.Construction.L12 (Work.Construction.Ftau β h τ) z)) := by
  have hz0 : 0 ≤ z := hz.le
  have hp2 : Integrable (fun s : ℝ => (s ^ 2)⁻¹) (volume.restrict (Set.Ioi z)) := by
    have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) hz
    refine hp.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_two]
  have hmaj : Integrable
      (fun s : ℝ => 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
        * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) (volume.restrict (Set.Ioi z)) :=
    (hp2.const_mul _).add ((majorant_tail hz).1.const_mul _)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi z))
    (F := fun n s => Work.FM.L12dens Work.Spaces.K
      (Work.Construction.Ftau β (gn n) τ) s)
    (f := fun s => Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β h τ) s)
    (bound := fun s => 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
      * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
    ?_ hmaj ?_ ?_
  · -- measurability of the densities
    intro n
    have hcont : ContinuousOn
        (fun s : ℝ => 2 * β / (1 + s) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s) (Set.Ioi 0) := by
      have h1 : ContinuousOn (fun s : ℝ => 2 * β / (1 + s) ^ 2) (Set.Ioi 0) :=
        continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
          (fun s hs => pow_ne_zero 2
            (ne_of_gt (by have hs' : (0 : ℝ) < s := hs; linarith)))
      exact h1.add (Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCw (h4 n)
        (hbd n))
    have haesm : AEStronglyMeasurable
        (fun s : ℝ => 2 * β / (1 + s) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (volume.restrict (Set.Ioi z)) :=
      (hcont.mono (Set.Ioi_subset_Ioi hz0)).aestronglyMeasurable measurableSet_Ioi
    refine haesm.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    have h := dens_add (β := β) hβ hβ1 hCw (h4 n) (hbd n) (u := slice (gn n) τ) hs0
    exact h.symm
  · -- domination
    intro n
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    have h := dens_add (β := β) hβ hβ1 hCw (h4 n) (hbd n) (u := slice (gn n) τ) hs0
    have hle : |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s|
        ≤ 3 * (Real.pi / 2) * Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hCw (h4 n) (hbd n) hs0
    have hFs : 2 * β / (1 + s) ^ 2 ≤ 2 * β * (s ^ 2)⁻¹ := by
      have hspos : (0 : ℝ) < s ^ 2 := by positivity
      have hle1 : 1 / (1 + s) ^ 2 ≤ 1 / s ^ 2 :=
        one_div_le_one_div_of_le hspos
          (by have h1 : (0 : ℝ) ≤ 1 + 2 * s := by linarith
              nlinarith [h1])
      calc 2 * β / (1 + s) ^ 2 = 2 * β * (1 / (1 + s) ^ 2) := by ring
        _ ≤ 2 * β * (1 / s ^ 2) := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = 2 * β * (s ^ 2)⁻¹ := by rw [one_div]
    have hEq : Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β (gn n) τ) s
        = 2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s := h
    have hkey : |Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β (gn n) τ) s|
        ≤ 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
          * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
      rw [hEq]
      calc |2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s|
          ≤ |2 * β / (1 + s) ^ 2|
              + |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s| := abs_add_le _ _
        _ ≤ 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
              * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
            refine add_le_add ?_ hle
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β / (1 + s) ^ 2)]
            exact hFs
    rw [Real.norm_eq_abs]
    exact hkey
  · -- a.e. convergence
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact dens_tendsto (β := β) hβ hβ1 hCw h4 hbd hconv (lt_trans hz hs)

end Work.FTS_RegExport.RXT.Sys.L12FKaux
