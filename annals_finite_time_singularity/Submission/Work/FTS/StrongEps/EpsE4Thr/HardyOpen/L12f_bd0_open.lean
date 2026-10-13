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

open Work.FTS.CoercivityFix.Coer1T

/-! ## Private open-class helpers

The `L¹`/`L²` bookkeeping of `Work.FTS.CoercivityFix.Coer1T.L12f_bd0`
(`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`) is re-proved here in the *open*
smoothness class `Work.FTS.EllipticEst.SmoothOpen f` (`C^∞` on the open quadrant
`(0,∞) × (0,π/2)`), for use in the boundary estimate below:

* `bd0_sliceSq` — the squared angular slice `θ ↦ (f s θ)²` is `L¹` on `Iθ` for `s > 0`;
* `bd0_B4_aesm`, `bd0_B4_sqrt_aesm_mono` — a.e. strong measurability of `s ↦ √(B4 α f s)`;
* `bd0_dens_abs_le` — the density bound `|L₁₂dens(K,f,s)| ≤ √3·s/(1+s)²·√(B4 α f s)`;
* `bd0_L12f_abs_le_prim` — `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s√(B4 α f s)` for `0 < z ≤ 1`;
* `bd0_L12f_sq_le_small` — `(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1`.

The only `SmoothQuad` inputs of the original chain are the joint continuity of the
`ℋ⁴`-integrand (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) and the angular
slice integrability of `f²`; everything else already needs no smoothness hypothesis.  The
helpers are `private` because the open-class analogues are also being produced by the sibling
tasks of this directory. -/

/-- The squared angular slice `θ ↦ (f s θ)²` is integrable on `Iθ` for `s > 0`, for a datum
that is continuous on the *open* quadrant and lies in `ℋ⁴`.

For a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w s ≥ 1`, so
`(f s θ)² ≤ (f s θ·(w s/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f s θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`,
and the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd`. -/
private theorem bd0_sliceSq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := hC
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hs
  refine MeasureTheory.Integrable.mono' (hmem.1 s (le_of_lt hs)) haesm ?_
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
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hs]
  have hkey : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f s θ) ^ 2 ≤ (f s θ * (Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f s θ) ^ 2 = (f s θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f s θ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f s θ * (Work.Spaces.w s
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f s θ) ^ 2‖ = (f s θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f s θ * (Work.Spaces.w s
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)

/-- A.e. strong measurability of `s ↦ B4 α f s = ∫_θ HkIntegrand α 4 f s θ` on `Iz`, from
`C^∞` on the open quadrant: the joint integrand is continuous there
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) hence a.e. strongly measurable
(`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini gives the measurability of the partial
integral. -/
private theorem bd0_B4_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (B4 α f) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    (hsm.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- The restriction of `bd0_B4_aesm` to subsets of `Iz` (the open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm_mono`). -/
private theorem bd0_B4_sqrt_aesm_mono (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s)) (MeasureTheory.volume.restrict u) :=
  (Real.continuous_sqrt.comp_aestronglyMeasurable (bd0_B4_aesm α hsm)).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The `L₁₂`-density bound in the open class: for `s > 0`,
`|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)`
(the open-class analogue of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`). -/
private theorem bd0_dens_abs_le (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    bd0_sliceSq hsm.continuousOn hmem hs
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
      (fun θ hθ => slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2 ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
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

/-- `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s √(B4 α f s)` for `0 < z ≤ 1`, in the open class
(the analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_prim`). -/
private theorem bd0_L12f_abs_le_prim (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hrepr : Work.Coercivity.L12f f z = -(∫ s in Set.Ioc 0 z, G s) := by
    rw [L12f_eq_neg_prim hint hl12 hz, intervalIntegral.integral_of_le hz.le]
  rw [hrepr, abs_neg]
  -- the majorant `maj s = √3 * (s * √(B4 s))`
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hmaj_aesm : AEStronglyMeasurable
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s)))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((continuous_id.aestronglyMeasurable.mul (bd0_B4_sqrt_aesm_mono α hsm hu)).const_mul
      (Real.sqrt 3))
  -- the majorant is integrable
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmaj_bound : ∀ s ∈ Set.Ioc 0 z,
      Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) ≤ (Real.sqrt 3 / 2) * (1 + B4 α f s) := by
    intro s hs
    have hBs : 0 ≤ B4 α f s := B4_nonneg α f s
    have hle1 : s ≤ 1 := le_trans hs.2 hz1
    have hs0 : 0 < s := hs.1
    have hsqrt_le : Real.sqrt (B4 α f s) ≤ (1 + B4 α f s) / 2 := by
      nlinarith [Real.sq_sqrt hBs, sq_nonneg (Real.sqrt (B4 α f s) - 1)]
    have hsle : s * Real.sqrt (B4 α f s) ≤ Real.sqrt (B4 α f s) := by
      nlinarith [hle1, hs0, Real.sqrt_nonneg (B4 α f s)]
    nlinarith [hsqrt_le, hsle, Real.sqrt_nonneg 3]
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s))) (Set.Ioc 0 z) :=
    ((hconst.add hBint).const_mul (Real.sqrt 3 / 2)).mono' hmaj_aesm
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
        rw [Real.norm_of_nonneg (by
          have hx0 : 0 < x := hx.1
          positivity)]
        exact hmaj_bound x hx))
  -- the pointwise domination of `G`
  have hG_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 z)), ‖G s‖
      ≤ Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have h1 := bd0_dens_abs_le α hsm hmem hs0
    have h2 : s / (1 + s) ^ 2 ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg s, le_of_lt hs0]
    rw [Real.norm_eq_abs]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := h1
      _ ≤ Real.sqrt 3 * s * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by ring
  have hbd := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hG_bd
  rw [Real.norm_eq_abs] at hbd
  calc |∫ s in Set.Ioc 0 z, G s|
      ≤ ∫ s in Set.Ioc 0 z, Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := hbd
    _ = Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
        rw [MeasureTheory.integral_const_mul]

/-- Near the origin the tail of the density grows at most like `z^{3/2}`:
`(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1`, in the open class
(the analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_le_small`). -/
private theorem bd0_L12f_sq_le_small (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (B4 α f s) with hΨdef
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hΨ_aesm : AEStronglyMeasurable Ψ (volume.restrict (Set.Ioc 0 z)) :=
    continuous_id.aestronglyMeasurable.mul (bd0_B4_sqrt_aesm_mono α hsm hu)
  have hΨ2_eq : ∀ s, (Ψ s) ^ 2 = s ^ 2 * B4 α f s := by
    intro s
    rw [hΨdef]
    simp only
    rw [mul_pow, Real.sq_sqrt (B4_nonneg α f s)]
  have hΨ2_int : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2) (Set.Ioc 0 z) := by
    refine (hBint.const_mul (z ^ 2)).mono' (hΨ_aesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hΨmem : MemLp Ψ 2 (volume.restrict (Set.Ioc 0 z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΨ_aesm).mpr hΨ2_int
  have hcs := cs_one hz hΨmem
  have hΨ2_le : ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 ≤ z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _)
      (hBint.const_mul (z ^ 2)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    show Ψ s ^ 2 ≤ z ^ 2 * B4 α f s
    rw [hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have h1 := bd0_L12f_abs_le_prim α hsm hmem hint hl12 hz hz1
  have habs := abs_le.mp h1
  have key : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  calc (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := key
    _ ≤ 3 * (z * ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2) := by linarith [hcs]
    _ ≤ 3 * (z * (z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s)) := by
        have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
        have := mul_le_mul_of_nonneg_left hΨ2_le hz0
        linarith
    _ = 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by ring

/-- `bd0` of `HardyHyp` in the *open* class: the two boundary terms `(L₁₂ f)²/z^{2j-1}` and `w z·(L₁₂ f)²` vanish as `z → 0⁺` (`j ≤ 2`), from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_bd0` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), which squeezes both terms against `3·∫_{(0,z]} B4 α f` (resp. `12·`) using the small-`z` estimate `(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1` and `Ioc_B4_tendsto_zero` (both hypothesis-free apart from `HkMem`).  The small-`z` estimate is the open-class adaptation of `L12f_sq_le_small`/`L12f_abs_le_prim` (helper lemmas may be proved inside the same file), whose only `SmoothQuad` use is the a.e. strong measurability of `s ↦ √(B4 α f s)` (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (open version from `Work.Spaces.sq_le_HkIntegrand_z`). -/
theorem L12f_bd0_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) (j : ℕ) (hj : j ≤ 2) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hmem1 : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
  have hβ : Filter.Tendsto (fun z => ∫ s in Set.Ioc 0 z, B4 α f s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Ioc_B4_tendsto_zero α hmem
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have h2 : 2 * j ≤ 4 := by omega
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast h2
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 3)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz _))
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := bd0_L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hzpow : z ^ (3 : ℕ) ≤ z ^ (2 * (j : ℝ) - 1) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hz hz1.2
          (show (2 * (j : ℝ) - 1) ≤ 3 by linarith)
        simpa using h
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz 3) hzpow
      have hstep2 : (Work.Coercivity.L12f f z) ^ 2 / z ^ 3
          ≤ 3 * (∫ s in Set.Ioc 0 z, B4 α f s) := by
        rw [div_le_iff₀ (pow_pos hz 3)]
        nlinarith [hX]
      exact le_trans hstep hstep2
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := bd0_L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hβnn : 0 ≤ ∫ s in Set.Ioc 0 z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun s _ => B4_nonneg α f s)
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 := by
        have h5 : 1 + z ≤ 2 := by linarith [hz1.2]
        have hz0 : (0 : ℝ) < z := hz
        have h6 : (0 : ℝ) ≤ 1 + z := by linarith
        calc (1 + z) ^ 2 = (1 + z) * (1 + z) := by ring
          _ ≤ 2 * 2 := mul_le_mul h5 h5 h6 (by linarith)
          _ = 4 := by norm_num
      rw [hw]
      have hz0 : (0 : ℝ) < z := hz
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hz0 2)]
      have h1 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s) :=
        mul_le_mul h4 hX (sq_nonneg _) (by norm_num)
      have h2 : 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s)
          ≤ 12 * (∫ s in Set.Ioc 0 z, B4 α f s) * z ^ 2 := by
        nlinarith [hβnn, hz0, hz1.2, sq_nonneg z, pow_pos hz0 2,
          mul_le_mul_of_nonneg_left hz1.2 (mul_nonneg (show (0:ℝ) ≤ 12 by norm_num) hβnn)]
      linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
