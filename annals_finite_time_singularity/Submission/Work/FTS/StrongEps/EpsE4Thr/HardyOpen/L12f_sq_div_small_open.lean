import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
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

/-! ## The open-class helpers of `L12f_sq_div_small`

This file re-proves, in the *open* smoothness class `Work.FTS.EllipticEst.SmoothOpen f`
(`C^∞` on the open quadrant `(0,∞) × (0,π/2)`), the chain of
`Work.FTS.CoercivityFix.Coer1T` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`)
that yields `intA` of `HardyHyp` on `(0,1]`:

* `slice_sq_integrableOn_open` — the squared angular slice is `L¹` on `Iθ`;
* `B4_sqrt_aesm_open`, `B4_sqrt_aesm_mono_open` — a.e. strong measurability of `s ↦ √(B4 α f s)`;
* `dens_abs_le_open` — the pointwise density bound `|L₁₂dens(K,f,s)| ≤ √3·s/(1+s)²·√(B4 α f s)`;
* `L12f_abs_le_prim_open` — `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s√(B4 α f s)` for `0 < z ≤ 1`;
* `L12f_sq_div_z4_integrableOn_Ioc_open` — `(L₁₂ f z)²/z⁴ ∈ L¹((0,1])`;
* `L12f_sq_div_small_open` — `(L₁₂ f z)²/z^{2j} ∈ L¹((0,1])` for `j ≤ 2`.

The only `SmoothQuad` inputs of the original chain are the joint continuity of the
`ℋ⁴`-integrand (here `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) and the
density bound; everything else already needs no smoothness hypothesis. -/

/-- The squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`, for a datum
`f` that is `C^∞` on the open quadrant and lies in `ℋ⁴`.

This is the open-class analogue of `Work.FTS.H2.l12q_slice_sq_integrableOn` (equivalently of
the private `Work.FTS.MeridianDyn.Bridge.Pieces.slice_sq_integrableOn`).  For a.e. `θ ∈ Iθ`
(all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w z ≥ 1`, so
`(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`. -/
theorem slice_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      hsm.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hz
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

/-- A.e. strong measurability of `s ↦ B4 α f s = ∫_θ HkIntegrand α 4 f s θ` on `Iz`, from
`C^∞` on the open quadrant: the joint integrand is continuous there
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) hence a.e. strongly measurable
(`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini gives the measurability of the partial
integral.  The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_aesm`. -/
theorem B4_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    (hsm.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm`. -/
theorem B4_sqrt_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (B4_aesm_open α hsm)

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm_mono`. -/
theorem B4_sqrt_aesm_mono_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (MeasureTheory.volume.restrict u) :=
  (B4_sqrt_aesm_open α hsm).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`: the `L₁₂`-density
obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`, from `SmoothOpen f`. -/
theorem dens_abs_le_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
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
      (fun θ hθ => Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
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
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
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

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_prim`:
`|L₁₂ f z| ≤ √3 ∫_{(0,z]} s √(B4 α f s)` for `0 < z ≤ 1`. -/
theorem L12f_abs_le_prim_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3
        * ∫ s in Set.Ioc 0 z, s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hrepr : Work.Coercivity.L12f f z = -(∫ s in Set.Ioc 0 z, G s) := by
    rw [Work.FTS.CoercivityFix.Coer1T.L12f_eq_neg_prim hint hl12 hz,
      intervalIntegral.integral_of_le hz.le]
  rw [hrepr, abs_neg]
  -- the majorant `maj s = √3 * (s * √(B4 s))`
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hmaj_aesm : AEStronglyMeasurable
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((continuous_id.aestronglyMeasurable.mul (B4_sqrt_aesm_mono_open α hsm hu)).const_mul
      (Real.sqrt 3))
  -- the majorant is integrable
  have hBint : MeasureTheory.IntegrableOn (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (Set.Ioc 0 z) :=
    (Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmaj_bound : ∀ s ∈ Set.Ioc 0 z,
      Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      ≤ (Real.sqrt 3 / 2) * (1 + Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    intro s hs
    have hBs : 0 ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s :=
      Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s
    have hle1 : s ≤ 1 := le_trans hs.2 hz1
    have hs0 : 0 < s := hs.1
    have hsqrt_le : Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
        ≤ (1 + Work.FTS.CoercivityFix.Coer1T.B4 α f s) / 2 := by
      nlinarith [Real.sq_sqrt hBs, sq_nonneg (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) - 1)]
    have hsle : s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
        ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
      nlinarith [hle1, hs0, Real.sqrt_nonneg (Work.FTS.CoercivityFix.Coer1T.B4 α f s)]
    nlinarith [hsqrt_le, hsle, Real.sqrt_nonneg 3]
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)))
      (Set.Ioc 0 z) :=
    ((hconst.add hBint).const_mul (Real.sqrt 3 / 2)).mono' hmaj_aesm
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
        rw [Real.norm_of_nonneg (by
          have hx0 : 0 < x := hx.1
          positivity)]
        exact hmaj_bound x hx))
  -- the pointwise domination of `G`
  have hG_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 z)), ‖G s‖
      ≤ Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have h1 := dens_abs_le_open α hsm hmem hs0
    have h2 : s / (1 + s) ^ 2 ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg s, le_of_lt hs0]
    rw [Real.norm_eq_abs]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
          * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := h1
      _ ≤ Real.sqrt 3 * s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by ring
  have hbd := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hG_bd
  rw [Real.norm_eq_abs] at hbd
  calc |∫ s in Set.Ioc 0 z, G s|
      ≤ ∫ s in Set.Ioc 0 z,
          Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := hbd
    _ = Real.sqrt 3
          * ∫ s in Set.Ioc 0 z, s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
        rw [MeasureTheory.integral_const_mul]

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_z4_integrableOn_Ioc`:
`(L₁₂ f z)²/z⁴` is integrable on `(0,1]`. -/
theorem L12f_sq_div_z4_integrableOn_Ioc_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4)
      (Set.Ioc 0 1) := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) with hΨdef
  have hPsi : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Set.Ioc 0 1) := by
    refine ((Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set
      (fun t ht => ht.1)).congr_fun (fun s hs => ?_) measurableSet_Ioc
    have hs0 : s ≠ 0 := ne_of_gt hs.1
    show Work.FTS.CoercivityFix.Coer1T.B4 α f s
      = (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2 / s ^ 2
    rw [mul_pow, Real.sq_sqrt (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s)]
    field_simp
  have hHT := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable Ψ hPsi).1
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹) (volume.restrict (Set.Ioc 0 1)) := by
    have hmeas : Measurable (fun z : ℝ => (z ^ 4)⁻¹) :=
      (continuous_pow 4).measurable.inv
    exact hmeas.aestronglyMeasurable.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
      (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4) (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  have hHT3 : MeasureTheory.IntegrableOn
      (fun z => 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)) (Set.Ioc 0 1) := hHT.const_mul 3
  refine hHT3.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h1 := L12f_abs_le_prim_open α hsm hmem hint hl12 hz.1 hz1
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have hkey : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have habs := abs_le.mp h1
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ 4
      ≤ 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4) := by
        rw [show 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)
            = (3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2) / z ^ 4 by ring]
        exact div_le_div_of_nonneg_right hkey (by positivity)

/-- `intA` of `HardyHyp` on `(0,1]` in the *open* class: `(L₁₂ f)²/z^{2j} ∈ L¹((0,1])` for `j ≤ 2`, from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_small` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), together with its private helpers `L12f_sq_div_z4_integrableOn_Ioc` and `L12f_abs_le_prim` re-proved in the open class (put them in the same file); the only uses of `SmoothQuad` in that chain are the a.e. strong measurability of `s ↦ √(B4 α f s)` (from `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le`, whose open version follows from the slice `L²`-domination by `HkIntegrand` (`Work.Spaces.sq_le_HkIntegrand_z`) and continuity of the slice on the open interval (`Work.Spaces.aesm_slice_of_continuousOn_Qd`; cf. the private `slice_sq_integrableOn` of `MeridianDyn/Bridge/Pieces/sliceK_integrableOn_of_continuousOn.lean`).  The Hardy-type input `Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable`, `cs_one`, `L12f_eq_neg_prim`, `L12f_aesm_mono` need no smoothness. -/
theorem L12f_sq_div_small_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioc 0 1) := by
  have h4 := L12f_sq_div_z4_integrableOn_Ioc_open α hsm hmem hint hl12 hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioc 0 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h4.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have : ((2 * j : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) := by
      have h2 : 2 * j ≤ 4 := by omega
      exact_mod_cast h2
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact this
  have hzj : z ^ 4 ≤ z ^ (2 * (j : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz1 h2j
  have hpos : 0 < z ^ (2 * (j : ℝ)) := Real.rpow_pos_of_pos hz.1 _
  have hpos4 : 0 < z ^ 4 := pow_pos hz.1 4
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hpos))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 4 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hpos4 hzj
    _ = _ := rfl

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
