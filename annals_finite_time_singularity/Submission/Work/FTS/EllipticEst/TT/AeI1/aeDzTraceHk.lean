import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z`

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate,
with the two extra `ℋ⁰`-honesties `HkMem α 0 (z ∂_zu)` and `HkMem α 0 (∂_θ(z∂_zu))`, the
angular slice `θ ↦ z ∂_zu(z,θ)` tends to `0` at `0⁺` and at `(π/2)⁻` for almost every `z > 0`.

The route is the one recorded in `H2W/InterpOpenAux/NOTES_trace_DzV_zero_FALSE.md` §3–5, with
`V = u`:

* `sliceBoundaryLimit` applied to the slice `f z := θ ↦ z ∂_zu(z,θ)` (whose derivative is
  `z ∂_θ∂_zu = Dz (∂_θu)` by Clairaut) gives both one-sided limits `c₀(z)`, `c₁(z)` and the
  quadratic bounds `(f z θ - c₀ z)² ≤ 2θ^{1+η}·Φ(z)` resp. `≤ 2(π/2-θ)^{1+η}·Φ(z)`, where `Φ` is
  the `σ`-weighted slice energy of `Dz (∂_θu)`; `HkMem α 0 (∂_θ(z∂_zu))` makes `Φ` honest;
* the `z`-FTC, `u(z+h,θ)-u(z,θ) = ∫_{(z,z+h)}∂_zu(s,θ)ds`, is passed to the limit `θ → 0⁺`
  resp. `θ → (π/2)⁻` by dominated convergence (the domination comes from the FTC in `θ` and
  `∫w²Φ < ∞`); the left/right traces of `u` itself vanish a.e. in `z` / for every `z`
  (`H2W.AeLeftClean.sliceLeftTendstoClean`, `H2W.AeProof.AeSliceRightTendsto`);
* hence `∫_{(z,z+h)}c₀(s)/s ds = 0` for a.e. `(z,h)` (left) and for all `z,h>0` (right), i.e. the
  primitives of `c₀/s` resp. `c₁/s` are (a.e.) locally constant;
* the Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`) then gives
  `c₀ = 0` and `c₁ = 0` almost everywhere.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.AeI1

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## 1. The `σ`-weighted slice energy of `z ∂_z u` -/

/-- `Φ u z = ∫_θ (∂_θ(z ∂_z u)(z,θ))² σ(θ) dθ`, the `σ`-weighted angular energy of the slice
`θ ↦ z ∂_zu(z,θ)` (`σ θ = sin(2θ)^{-η}`). -/
def sliceEnergy (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem sliceEnergy_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceEnergy u z :=
  setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

theorem sliceEnergy_eq_Ioo (u : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceEnergy u z = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm

/-- The `k = 0` weighted integrand is `(f · w · sin(2θ)^{-η/2})² = f² w² σ`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    simp [Work.Spaces.HkIntegrand]]
  have hs : 0 ≤ Real.sin (2 * θ) := by
    have h1 : 0 ≤ 2 * θ := by have := hθ.1; linarith
    have h2 : 2 * θ ≤ Real.pi := by have := hθ.2; linarith [Real.pi_pos]
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  rw [Work.FTS.EllipticEst.sEta]
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    simp
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
      congr 1
      ring
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos)]
    ring

theorem w_eq_zero_at_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hz)

/-- The explicit lower bound for the radial weight on `(a,b)`, `0 ≤ a < b`. -/
theorem w_sq_ge_of_mem_Ioo {a b z : ℝ} (ha : 0 ≤ a) (hz : z ∈ Set.Ioo a b) :
    1 ≤ (b / (1 + a)) ^ 4 * (Work.Spaces.w z) ^ 2 := by
  have hzpos : 0 < z := lt_of_le_of_lt ha hz.1
  have hbpos : 0 < b := lt_trans hzpos hz.2
  have hratio : (1 + a) / b ≤ (1 + z) / z := by
    rw [div_le_div_iff₀ hbpos hzpos]
    nlinarith [hz.1, hz.2]
  have hsq : ((1 + a) / b) ^ 2 ≤ Work.Spaces.w z := by
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + a) / b) hratio 2
    rw [Work.Spaces.w]
    simpa only [div_pow] using h2
  have h4 : ((1 + a) / b) ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((1 + a) / b) ^ 2) hsq 2
    calc ((1 + a) / b) ^ 4 = (((1 + a) / b) ^ 2) ^ 2 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 := h
  have hmul := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ (b / (1 + a)) ^ 4)
  have heq : (b / (1 + a)) ^ 4 * ((1 + a) / b) ^ 4 = 1 := by
    rw [← mul_pow]
    have : b / (1 + a) * ((1 + a) / b) = 1 := by field_simp
    rw [this]; norm_num
  linarith [hmul, heq]

/-- Clairaut in the `σ`-weighted square: on the domain, `z ∂_θ∂_zu` and `∂_θ(z∂_zu)` have the
same weighted square. -/
theorem clairaut_sq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.sEta, hsin,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · by_cases hz0 : z = 0
    · subst hz0
      simp [Work.Spaces.Dz]
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hne0 : θ ≠ 0 := by intro hh; exact hsin (by subst hh; norm_num)
      have hne1 : θ ≠ Real.pi / 2 := by
        intro hh
        exact hsin (by rw [hh]; rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
      have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (Ne.symm hne0), lt_of_le_of_ne hθ.2 hne1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
        (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ'.1, hθ'.2⟩))
      have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
      simp only [Work.Spaces.Dz]
      rw [hcl]

/-- Clairaut in the `σ`-weighted square, with the radial weight kept. -/
theorem clairaut_sq_w {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ := by
  rw [show (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = ((z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * (Work.Spaces.w z) ^ 2 from by ring,
    clairaut_sq hS hz hθ]
  ring

/-- The per-slice `σ`-honesty of the slice energy, from `HkMem` of `z ∂_θ∂_zu`. -/
theorem integrableOn_sliceEnergy_energy {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    ∀ z ∈ Iz, MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Iθ := by
  intro z hz
  set F₁ : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ with hF₁
  have h0 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 F₁ z θ) Iθ := hMix.1 z hz
  have hA : (fun θ => Work.Spaces.HkIntegrand α 0 F₁ z θ)
      =ᵐ[volume.restrict Iθ]
      (fun θ => (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact HkIntegrand_zero_eq α F₁ hθ
  have h1 := h0.congr hA
  have hB : (fun θ => (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[volume.restrict Iθ]
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [hF₁]
    exact clairaut_sq_w hS hz hθ
  have h2 := h1.congr hB
  by_cases hz0 : z = 0
  · subst hz0
    refine (MeasureTheory.integrable_zero ℝ ℝ (volume.restrict Iθ)).congr ?_
    filter_upwards with θ
    simp [Work.Spaces.Dz]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hzpos))
    refine MeasureTheory.Integrable.congr (h2.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_
    filter_upwards with θ
    rw [show (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        from by ring]
    exact inv_mul_cancel_left₀ hw _

/-- The outer `z`-integrability of `w² · Φ`, straight from `HkMem` of `z ∂_θ∂_zu`. -/
theorem integrableOn_w2_sliceEnergy {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z) Iz := by
  set F₁ : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ with hF₁
  have h0 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 F₁ z θ) Iz := hMix.2
  refine MeasureTheory.Integrable.congr h0 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have h1 : (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 F₁ z θ)
      = ∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_zero_eq α F₁ hθ)
  have h2 : (∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Iθ, (F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    rw [show (∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Iθ, (Work.Spaces.w z) ^ 2 * ((F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have h3 : (∫ θ in Iθ, (F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by simp only [hF₁]; exact clairaut_sq hS hz hθ)
  rw [h1, h2, h3]
  rfl

/-- Continuity of the radial weight on `(a,b)` with `0 ≤ a`. -/
theorem continuousOn_w {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioo a b) := by
  rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_of_le_of_lt ha hz.1))

/-- A.e.-measurability of `Φ` on subintervals of `(0,∞)`. -/
theorem aemeasurable_sliceEnergy_Ioo {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo a b)) := by
  have hsub : Set.Ioo a b ⊆ Iz := fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (Set.Ioo a b) := (integrableOn_w2_sliceEnergy hS hMix).mono_set hsub
  have h1m : AEMeasurable (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (volume.restrict (Set.Ioo a b)) := h1.aemeasurable
  have hwm : AEMeasurable (fun z => ((Work.Spaces.w z) ^ 2)⁻¹)
      (volume.restrict (Set.Ioo a b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact ((continuousOn_w ha).pow 2).inv₀
      (fun z hz => pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1))))
  refine (hwm.mul h1m).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1)))
  exact inv_mul_cancel_left₀ hw _

/-- Local integrability of `Φ` on subintervals of `(0,∞)`. -/
theorem integrableOn_sliceEnergy_Ioo {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.IntegrableOn (sliceEnergy u) (Set.Ioo a b) := by
  have hsub : Set.Ioo a b ⊆ Iz := fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (Set.Ioo a b) := (integrableOn_w2_sliceEnergy hS hMix).mono_set hsub
  have hmeas := aemeasurable_sliceEnergy_Ioo hS hMix ha hab
  refine MeasureTheory.Integrable.mono' (h1.abs.const_mul ((b / (1 + a)) ^ 4))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hw := w_sq_ge_of_mem_Ioo ha hz
  have hΦ := sliceEnergy_nonneg u z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hΦ, abs_of_nonneg (mul_nonneg hw2 hΦ)]
  calc sliceEnergy u z = 1 * sliceEnergy u z := (one_mul _).symm
    _ ≤ ((b / (1 + a)) ^ 4 * (Work.Spaces.w z) ^ 2) * sliceEnergy u z :=
        mul_le_mul_of_nonneg_right hw hΦ
    _ = (b / (1 + a)) ^ 4 * ((Work.Spaces.w z) ^ 2 * sliceEnergy u z) := by ring

/-- `Φ/s⁴` is locally integrable on `(0,∞)` (dominated by `w²Φ`). -/
theorem integrableOn_sliceEnergy_div_pow_four {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => sliceEnergy u s / s ^ 4) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (Set.Ioo 0 b) :=
    (integrableOn_w2_sliceEnergy hS hMix).mono_set (fun x hx => le_of_lt hx.1)
  have hΦm : AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo 0 b)) :=
    aemeasurable_sliceEnergy_Ioo hS hMix le_rfl hb
  have h4inv : AEMeasurable (fun s : ℝ => (s ^ 4)⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact (continuousOn_id.pow 4).inv₀ (fun z hz => pow_ne_zero 4 (ne_of_gt hz.1))
  refine MeasureTheory.Integrable.mono' h1.abs ?_ ?_
  · refine ((hΦm.mul h4inv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
    have hzpos : 0 < z := hz.1
    have hΦ := sliceEnergy_nonneg u z
    have hw4 : (1:ℝ) / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
      have h1z : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
      have hz4 : (0:ℝ) ≤ z ^ 4 := by positivity
      have hkey : (1:ℝ) * z ^ 4 ≤ (1 + z) ^ 4 * z ^ 4 :=
        mul_le_mul_of_nonneg_right h1z hz4
      rw [Work.Spaces.w]
      simp only [div_pow]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < z ^ 4)
        (by positivity : (0:ℝ) < (z ^ 2) ^ 2)]
      calc (1:ℝ) * (z ^ 2) ^ 2 = 1 * z ^ 4 := by ring
        _ ≤ (1 + z) ^ 4 * z ^ 4 := hkey
        _ = ((1 + z) ^ 2) ^ 2 * z ^ 4 := by ring
    have hdiff : sliceEnergy u z / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * sliceEnergy u z := by
      calc sliceEnergy u z / z ^ 4 = (1 / z ^ 4) * sliceEnergy u z := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * sliceEnergy u z := mul_le_mul_of_nonneg_right hw4 hΦ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΦ (by positivity)),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hΦ)]
    exact hdiff

/-- AM–GM for the square root. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h1 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha hb)
  have h2 : ((a + b) / 2) ^ 2 = (a + b) ^ 2 / 4 := by ring
  have hs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have ht : 0 ≤ (a + b) / 2 := by linarith
  nlinarith [h1, h2, sq_nonneg (a - b), hs, ht]

/-- `√Φ/s` is locally integrable near `0`, by AM–GM applied to `Φ/s⁴` and `s²`. -/
theorem integrableOn_sqrt_sliceEnergy_div {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun s => sliceEnergy u s / s ^ 4) (Set.Ioo 0 b) :=
    integrableOn_sliceEnergy_div_pow_four hS hMix hb
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2) (Set.Ioo 0 b) :=
    (continuous_id.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hdom : MeasureTheory.IntegrableOn
      (fun s => (sliceEnergy u s / s ^ 4 + s ^ 2) / 2) (Set.Ioo 0 b) := by
    refine MeasureTheory.Integrable.congr ((h1.add h2).const_mul (1/2)) ?_
    filter_upwards with s
    show (1/2 : ℝ) * (sliceEnergy u s / s ^ 4 + s ^ 2) = (sliceEnergy u s / s ^ 4 + s ^ 2) / 2
    ring
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hΦm : AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo 0 b)) :=
      aemeasurable_sliceEnergy_Ioo hS hMix le_rfl hb
    have hsqrt : AEMeasurable (fun s => Real.sqrt (sliceEnergy u s))
        (volume.restrict (Set.Ioo 0 b)) :=
      (Real.continuous_sqrt.measurable).comp_aemeasurable hΦm
    have hinv : AEMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
      refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
      exact continuousOn_id.inv₀ (fun z hz => ne_of_gt hz.1)
    refine ((hsqrt.mul hinv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    have hspos : 0 < s := hs.1
    have hΦ := sliceEnergy_nonneg u s
    have hkey : Real.sqrt (sliceEnergy u s) / s = Real.sqrt (sliceEnergy u s / s ^ 2) := by
      rw [Real.sqrt_div hΦ, Real.sqrt_sq (le_of_lt hspos)]
    have hsplit : sliceEnergy u s / s ^ 2 = (sliceEnergy u s / s ^ 4) * s ^ 2 := by
      field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hspos)),
      hkey, hsplit]
    exact sqrt_mul_le_add_div_two (div_nonneg hΦ (by positivity)) (sq_nonneg s)

/-! ## 2. Two generic real-analysis lemmas -/

/-- **A locally integrable function whose integrals over all small intervals vanish a.e. is
zero a.e.**  (The Lebesgue differentiation theorem applied to the primitive.) -/
theorem aeZeroOfIntervalIntegralZero {F : ℝ → ℝ}
    (hF : MeasureTheory.LocallyIntegrable F volume)
    (hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), (∫ x in z..(z + t), F x) = 0) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), F z = 0 := by
  have hLDT : ∀ᵐ z ∂volume, ∀ c, HasDerivAt (fun x => ∫ t in c..x, F t) (F z) z :=
    LocallyIntegrable.ae_hasDerivAt_integral hF
  filter_upwards [MeasureTheory.ae_restrict_of_ae hLDT,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi, hint] with z hder hzpos hh
  set K : ℝ → ℝ := fun x => ∫ t in z..x, F t with hK
  have hderz : HasDerivAt K (F z) z := by
    rw [hK]; exact hder z
  have hnull : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), t⁻¹ * (K (z + t) - K z) = 0 := by
    filter_upwards [hh] with t ht
    have hval : K (z + t) - K z = ∫ x in z..(z + t), F x := by
      rw [hK]
      simp [intervalIntegral.integral_same]
    rw [hval, ht, mul_zero]
  have hsetnull : volume {t : ℝ | 0 < t ∧ t⁻¹ * (K (z + t) - K z) ≠ 0} = 0 := by
    have h2 := MeasureTheory.ae_iff.mp hnull
    have h3 : (volume.restrict (Set.Ioi 0))
        {t : ℝ | 0 < t ∧ t⁻¹ * (K (z + t) - K z) ≠ 0} = 0 :=
      MeasureTheory.measure_mono_null (fun t ht => ht.2) h2
    rwa [MeasureTheory.Measure.restrict_eq_self volume (fun t ht => ht.1)] at h3
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo 0 (1 / ((n : ℝ) + 1)) ∧
      t⁻¹ * (K (z + t) - K z) = 0 := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Ioo 0 (1 / ((n : ℝ) + 1)) ⊆
        {t : ℝ | 0 < t ∧ t⁻¹ * (K (z + t) - K z) ≠ 0} :=
      fun t ht => ⟨ht.1, hcon t ht⟩
    have hle : volume (Set.Ioo 0 (1 / ((n : ℝ) + 1))) ≤
        volume {t : ℝ | 0 < t ∧ t⁻¹ * (K (z + t) - K z) ≠ 0} :=
      MeasureTheory.measure_mono hsub
    rw [hsetnull, le_zero_iff, Real.volume_Ioo] at hle
    have hle0 : (1 / ((n : ℝ) + 1)) ≤ 0 := by simpa using ENNReal.ofReal_eq_zero.mp hle
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose t ht using hseq
  have htend0 : Tendsto t atTop (nhds (0:ℝ)) := by
    have hdiv : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun n => le_of_lt (ht n).1.1) (fun n => le_of_lt (ht n).1.2)
  have htend : Tendsto t atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    rw [nhdsWithin, tendsto_inf, tendsto_principal]
    exact ⟨htend0, Eventually.of_forall fun n => (ht n).1.1⟩
  have hcomp := hderz.tendsto_slope_zero_right.comp htend
  have hzero : Tendsto (fun n => (t n)⁻¹ * (K (z + t n) - K z)) atTop (nhds (0:ℝ)) := by
    have : (fun n => (t n)⁻¹ * (K (z + t n) - K z)) = fun _ => (0:ℝ) :=
      funext fun n => (ht n).2
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hzero

/-- **Dominated convergence for the `θ`-slices of `∂_zu`**, in the `z`-integrated form. -/
theorem tendsto_setIntegral_pz {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {l : Filter ℝ} [l.IsCountablyGenerated] {c g : ℝ → ℝ} {z h : ℝ}
    (hz : 0 < z) (hh : 0 < h)
    (hθl : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hlim : ∀ s, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ) l (nhds (c s)))
    (hbound : ∀ᶠ θ in l, ∀ s ∈ Set.Ioo z (z + h), ‖Work.Spaces.pz u s θ‖ ≤ g s)
    (hgi : MeasureTheory.IntegrableOn g (Set.Ioo z (z + h))) :
    Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + h), Work.Spaces.pz u s θ) l
      (nhds (∫ s in Set.Ioo z (z + h), c s)) := by
  have hmain : Filter.Tendsto
      (fun θ => ∫ s, Work.Spaces.pz u s θ ∂(volume.restrict (Set.Ioo z (z + h)))) l
      (nhds (∫ s, c s ∂(volume.restrict (Set.Ioo z (z + h))))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgi ?_
    · filter_upwards [hθl] with θ hθ
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun s : ℝ => Work.Spaces.pz u s θ) (Set.Ioo z (z + h)) :=
        (Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ).mono
            (fun s hs => lt_trans hz hs.1)
      exact (hslice.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards [hbound] with θ hθ
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact hθ s hs
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact hlim s (lt_trans hz hs.1)
  exact hmain

/-! ## 3. The two endpoint traces as `limsup`-defined functions -/

/-- The left trace of the slice `θ ↦ ∂_z u(·,θ)` at `0⁺`, taken along the diagonal sequence
`θ_n = 1/(n+1)`; it is `a.e.`-measurable by construction and agrees with the honest limit
whenever the latter exists (see `dzTrace0_eq_of_tendsto`). -/
def dzTrace0 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (1 / ((n : ℝ) + 1))) atTop

/-- The right trace of the slice `θ ↦ ∂_z u(·,θ)` at `(π/2)⁻`. -/
def dzTrace1 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (Real.pi / 2 - 1 / ((n : ℝ) + 1))) atTop

/-- The diagonal sequence `θ_n = 1/(n+1)` lies in `(0,π/2)` and tends to `0` within `(0,∞)`. -/
theorem tendsto_theta0 : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop
    (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · filter_upwards with n
    exact one_div_pos.mpr (by positivity : (0:ℝ) < (n : ℝ) + 1)

/-- The diagonal sequence `θ_n = π/2 - 1/(n+1)` tends to `π/2` within `(0,π/2)`. -/
theorem tendsto_theta1 : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) atTop
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hc : Tendsto (fun _ : ℕ => Real.pi / 2) atTop (nhds (Real.pi / 2)) := tendsto_const_nhds
    have h1 : Tendsto (fun n : ℕ => Real.pi / 2 - (1:ℝ) / ((n : ℝ) + 1)) atTop
        (nhds (Real.pi / 2 - 0)) := hc.sub h0
    simpa using h1
  · filter_upwards with n
    have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact sub_lt_self _ this

theorem theta0_mem {n : ℕ} : (1:ℝ) / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · exact div_pos one_pos (by positivity)
  · have h1 : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith

theorem theta1_mem {n : ℕ} : Real.pi / 2 - 1 / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · have h : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith
  · exact sub_lt_self _ (by positivity)

/-- The `z`-slice of `∂_zu` at a fixed interior angle is a.e. strongly measurable. -/
theorem aeStronglyMeasurable_zslice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    AEStronglyMeasurable (fun z => Work.Spaces.pz u z θ) (volume.restrict (Set.Ioi 0)) := by
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Spaces.pz u z θ)
      (Set.Ioi 0) :=
    Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
      (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ
  exact (hslice.continuousOn.aemeasurable measurableSet_Ioi).aestronglyMeasurable

theorem aemeasurable_dzTrace0 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace0 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta0_mem).aemeasurable

theorem aemeasurable_dzTrace1 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace1 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta1_mem).aemeasurable

theorem dzTrace0_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c z))) :
    dzTrace0 u z = c z := by
  exact (h.comp tendsto_theta0).limsup_eq

theorem dzTrace1_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c z))) :
    dzTrace1 u z = c z := by
  exact (h.comp tendsto_theta1).limsup_eq

/-- **Localized Lebesgue-differentiation lemma.**  If `∫_z^{z+t} F = 0` for a.e. `z ∈ A` and a.e.
`t > 0`, then `F = 0` a.e. on `A` (for `F` locally integrable). -/
theorem aeZeroOn_of_intervalIntegralZero {F : ℝ → ℝ} {A : Set ℝ}
    (hF : MeasureTheory.LocallyIntegrable F volume)
    (hint : ∀ᵐ z ∂(volume.restrict A),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), (∫ x in z..(z + t), F x) = 0) :
    ∀ᵐ z ∂(volume.restrict A), F z = 0 := by
  have hLDT : ∀ᵐ z ∂volume, ∀ c, HasDerivAt (fun x => ∫ t in c..x, F t) (F z) z :=
    LocallyIntegrable.ae_hasDerivAt_integral hF
  filter_upwards [MeasureTheory.ae_restrict_of_ae hLDT, hint] with z hder hh
  set K' : ℝ → ℝ := fun x => ∫ t in z..x, F t with hK'
  have hderz : HasDerivAt K' (F z) z := by rw [hK']; exact hder z
  have hnull : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), t⁻¹ * (K' (z + t) - K' z) = 0 := by
    filter_upwards [hh] with t ht
    have hval : K' (z + t) - K' z = ∫ x in z..(z + t), F x := by
      rw [hK']
      simp [intervalIntegral.integral_same]
    rw [hval, ht, mul_zero]
  have hsetnull : volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 := by
    have h2 := MeasureTheory.ae_iff.mp hnull
    have h3 : (volume.restrict (Set.Ioi 0))
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 :=
      MeasureTheory.measure_mono_null (fun t ht => ht.2) h2
    rwa [MeasureTheory.Measure.restrict_eq_self volume (fun t ht => ht.1)] at h3
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo 0 (1 / ((n : ℝ) + 1)) ∧
      t⁻¹ * (K' (z + t) - K' z) = 0 := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Ioo 0 (1 / ((n : ℝ) + 1)) ⊆
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      fun t ht => ⟨ht.1, hcon t ht⟩
    have hle : volume (Set.Ioo 0 (1 / ((n : ℝ) + 1))) ≤
        volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      MeasureTheory.measure_mono hsub
    rw [hsetnull, le_zero_iff, Real.volume_Ioo] at hle
    have hle0 : (1 / ((n : ℝ) + 1)) ≤ 0 := by simpa using ENNReal.ofReal_eq_zero.mp hle
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose t ht using hseq
  have htend0 : Tendsto t atTop (nhds (0:ℝ)) := by
    have hdiv : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun n => le_of_lt (ht n).1.1) (fun n => le_of_lt (ht n).1.2)
  have htend : Tendsto t atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    rw [nhdsWithin, tendsto_inf, tendsto_principal]
    exact ⟨htend0, Eventually.of_forall fun n => (ht n).1.1⟩
  have hcomp := hderz.tendsto_slope_zero_right.comp htend
  have hzero : Tendsto (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) atTop (nhds (0:ℝ)) := by
    have : (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) = fun _ => (0:ℝ) :=
      funext fun n => (ht n).2
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hzero

/-- **Cut-off local integrability.**  A function which vanishes below `ε > 0` and is integrable on
every compact subinterval of `(ε,∞)` is locally integrable. -/
theorem locallyIntegrable_indicator_Ioi {F : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ a b : ℝ, ε ≤ a → a < b → MeasureTheory.IntegrableOn F (Set.Ioo a b)) :
    MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) F) volume := by
  have hInt : ∀ a b : ℝ, a < b → MeasureTheory.IntegrableOn
      (Set.indicator (Set.Ioi ε) F) (Set.Ioo a b) := by
    intro a b hab
    rcases le_or_gt b ε with hb | hb
    · refine MeasureTheory.IntegrableOn.congr_fun
        (MeasureTheory.integrable_zero ℝ ℝ _) ?_ measurableSet_Ioo
      intro s hs
      have hmem : s ∉ Set.Ioi ε := not_lt.mpr (le_trans (le_of_lt hs.2) hb)
      exact (Set.indicator_of_notMem hmem F).symm
    · have hbase : MeasureTheory.IntegrableOn F (Set.Ioo (max a ε) b) := by
        rcases lt_or_ge (max a ε) b with hlt | hge
        · exact h (max a ε) b (le_max_right _ _) hlt
        · rw [show Set.Ioo (max a ε) b = ∅ from
            Set.eq_empty_iff_forall_notMem.mpr
              (fun s hs => absurd hs.1 (not_lt.mpr (le_trans (le_of_lt hs.2) hge)))]
          exact MeasureTheory.integrableOn_empty
      have h2 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b ∩ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (hbase.mono_set (fun s hs => ⟨max_lt hs.1.1 hs.2, hs.1.2⟩))
          (fun s hs => (Set.indicator_of_mem hs.2 F).symm)
          (measurableSet_Ioo.inter measurableSet_Ioi)
      have h3 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b \ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (MeasureTheory.integrable_zero ℝ ℝ _)
          (fun s hs => (Set.indicator_of_notMem hs.2 F).symm)
          (measurableSet_Ioo.diff measurableSet_Ioi)
      refine (h2.union h3).mono_set ?_
      intro s hs
      by_cases hmem : ε < s
      · exact Set.mem_union_left _ ⟨hs, hmem⟩
      · exact Set.mem_union_right _ ⟨hs, hmem⟩
  intro x
  rcases le_or_gt x (ε / 2) with hx | hx
  · exact ⟨Set.Ioo (x - 1) (ε / 2 + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩
  · exact ⟨Set.Ioo (ε / 2) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩

theorem aeDzTraceHk (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  classical
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpi4 : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4mem : (Real.pi / 4) ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨hpi4, by linarith [Real.pi_pos]⟩
  have heta1 : (0:ℝ) < 1 + Work.Spaces.eta := by
    have := Work.Spaces.eta_nonneg; linarith
  -- (A) the derivative of the slice
  have hslice_deriv : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      deriv (fun θ' => Work.Spaces.Dz u z θ') θ = Work.Spaces.Dz (Work.Spaces.pth u) z θ := by
    intro z θ hz hθ
    have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
      (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
    have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
    have h1 : deriv (fun θ' => Work.Spaces.Dz u z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
      simp only [Work.Spaces.Dz, Work.Spaces.pth, deriv_const_mul_field]
    rw [h1]
    show z * Work.Spaces.pth (Work.Spaces.pz u) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
    exact congrArg (fun t => z * t) hcl.symm
  have hthEta : ∀ θ : ℝ, Work.FTS.EllipticEst.thEta θ = Work.FTS.EllipticEst.sEta θ :=
    fun θ => rfl
  -- (B) integrability of the weighted derivative
  have hslice_int : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ :=
      integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)
    refine ((hbase.mono_set Set.Ioo_subset_Icc_self)).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    simpa only [hslice_deriv z θ hz hθ, hthEta θ]
  -- (C) the two endpoint parameters
  obtain ⟨K, hKpos, hSBL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hsliceC1 : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 1
      (fun θ => Work.Spaces.Dz u z θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    intro z hz
    refine (hS.Dz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hleft : ∀ z : ℝ, ∃ c : ℝ, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := by
    intro z
    by_cases hz : 0 < z
    · obtain ⟨c, hlim, hbd⟩ := (hSBL (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
        (hslice_int z hz)).1
      refine ⟨c, fun _ => ⟨hlim, fun θ hθ => ?_⟩⟩
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        (integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)).mono_set
          Set.Ioo_subset_Icc_self
      have hEq1 : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
          = ∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => by
            simpa only [hslice_deriv z t hz ⟨ht.1, lt_trans ht.2 hθ.2⟩, hthEta t])
      have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t) = sliceEnergy u z :=
        (sliceEnergy_eq_Ioo u z).symm
      have hmono : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
          * Work.FTS.EllipticEst.thEta t) ≤ sliceEnergy u z := by
        rw [hEq1, ← hEq2]
        exact MeasureTheory.setIntegral_mono_set hA
          (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
          (by
            filter_upwards with t ht
            exact ⟨ht.1, lt_trans ht.2 hθ.2⟩)
      exact le_trans (hbd θ hθ)
        (mul_le_mul_of_nonneg_left hmono (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)))
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  have hright : ∀ z : ℝ, ∃ c : ℝ, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := by
    intro z
    by_cases hz : 0 < z
    · obtain ⟨c, hlim, hbd⟩ := (hSBL (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
        (hslice_int z hz)).2
      refine ⟨c, fun _ => ⟨hlim, fun θ hθ => ?_⟩⟩
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        (integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)).mono_set
          Set.Ioo_subset_Icc_self
      have hEq1 : (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          = ∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => by
            simpa only [hslice_deriv z t hz ⟨lt_trans hθ.1 ht.1, ht.2⟩, hthEta t])
      have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t) = sliceEnergy u z :=
        (sliceEnergy_eq_Ioo u z).symm
      have hmono : (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          ≤ sliceEnergy u z := by
        rw [hEq1, ← hEq2]
        exact MeasureTheory.setIntegral_mono_set hA
          (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
          (by
            filter_upwards with t ht
            exact ⟨lt_trans hθ.1 ht.1, ht.2⟩)
      exact le_trans (hbd θ hθ)
        (mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hKpos.le (Real.rpow_nonneg (by linarith [hθ.2]) _)))
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  choose c0 hc0 using hleft
  choose c1 hc1 using hright
  -- (D) the traces
  have hlim0 : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c0 s / s)) := by
    intro s hs
    have h1 : Filter.Tendsto (fun θ => s * Work.Spaces.pz u s θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c0 s)) := by
      simpa only [Work.Spaces.Dz] using (hc0 s hs).1
    have h3 : (fun θ => s * Work.Spaces.pz u s θ / s) = fun θ => Work.Spaces.pz u s θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hs)
    rw [← h3]
    exact h1.div_const s
  have hlim1 : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s / s)) := by
    intro s hs
    have h1 : Filter.Tendsto (fun θ => s * Work.Spaces.pz u s θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) := by
      simpa only [Work.Spaces.Dz] using (hc1 s hs).1
    have h3 : (fun θ => s * Work.Spaces.pz u s θ / s) = fun θ => Work.Spaces.pz u s θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hs)
    rw [← h3]
    exact h1.div_const s
  have htr0 : ∀ z : ℝ, 0 < z → dzTrace0 u z = c0 z / z := by
    intro z hz
    exact dzTrace0_eq_of_tendsto (hlim0 z hz)
  have htr1 : ∀ z : ℝ, 0 < z → dzTrace1 u z = c1 z / z := by
    intro z hz
    exact dzTrace1_eq_of_tendsto (hlim1 z hz)
  -- (E) the pointwise bounds
  have hc0bd : ∀ z : ℝ, 0 < z → |c0 z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
    intro z hz
    have hb := (hc0 z hz).2 (Real.pi / 4) hpi4mem
    have h1 : |c0 z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c0 z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c0 z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c0 z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c0 z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c0 z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c0 z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c0 z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c0 z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
          linarith [h1]
  have hc1bd : ∀ z : ℝ, 0 < z → |c1 z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
    intro z hz
    have hb := (hc1 z hz).2 (Real.pi / 4) hpi4mem
    have hb' : (Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2
        ≤ K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z := by
      have hpi : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      simpa only [hpi] using hb
    have h1 : |c1 z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c1 z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) :=
            Real.sqrt_le_sqrt hb'
        _ = Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c1 z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c1 z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c1 z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c1 z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c1 z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
          linarith [h1]
  have hslicebd : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceEnergy u z) := by
    intro z θ hz hθ
    have hb := (hc0 z hz).2 θ hθ
    have h1 : |Work.Spaces.Dz u z θ - c0 z|
        ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
          * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((Work.Spaces.Dz u z θ - c0 z) ^ 2)
          ≤ Real.sqrt (K * θ ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * θ ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)) _
        _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
            refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hθ.1.le hθ.2.le heta1.le) hKpos.le
    have h2 : |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z θ - c0 z| + |c0 z| := by
      have h3 : |Work.Spaces.Dz u z θ| = |(Work.Spaces.Dz u z θ - c0 z) + c0 z| := by
        congr 1
        ring
      rw [h3]
      exact abs_add_le _ _
    have h4 := hc0bd z hz
    calc |Work.Spaces.Dz u z θ|
        ≤ |Work.Spaces.Dz u z θ - c0 z| + |c0 z| := h2
      _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z)
            + (|Work.Spaces.Dz u z (Real.pi / 4)|
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
                * Real.sqrt (sliceEnergy u z)) := by linarith [h1, h4]
      _ = |Work.Spaces.Dz u z (Real.pi / 4)|
            + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
              * Real.sqrt (sliceEnergy u z) := by ring
  -- (F) the FTC in `z`
  have hftc : ∀ z t θ : ℝ, 0 < z → 0 < t → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      (∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) = u (z + t) θ - u z θ := by
    intro z t θ hz ht hθ
    have hderiv : ∀ x ∈ Set.uIcc z (z + t), HasDerivAt (fun s : ℝ => u s θ)
        (Work.Spaces.pz u x θ) x := by
      intro x hx
      have hx' := Set.mem_uIcc.mp hx
      rcases hx' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le hz h1)
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s θ) (Set.uIcc z (z + t)) :=
      ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
        (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hθ).continuousOn).mono
          (fun s hs => by
            have hs' := Set.mem_uIcc.mp hs
            rcases hs' with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact lt_of_lt_of_le hz h1
            · exact lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [← hmain, intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- (G) the good set for the left trace
  set S : Set ℝ := {z : ℝ | Filter.Tendsto (fun θ => u z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)} ∪ {z : ℝ | z ≤ 0} with hSdef
  have hScomp : Sᶜ ⊆ Set.Ioi (0:ℝ) := by
    intro z hz
    by_contra hcon
    have hlt : ¬ (0:ℝ) < z := fun h => hcon (by simpa using h)
    exact hz (Or.inr (not_lt.mp hlt))
  have hSnull : volume Sᶜ = 0 := by
    have h1 : (volume.restrict (Set.Ioi 0)) Sᶜ = 0 := by
      refine MeasureTheory.ae_iff.mp ?_
      filter_upwards [Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h]
        with z hz
      exact Or.inl hz
    rwa [MeasureTheory.Measure.restrict_eq_self volume hScomp] at h1
  have hStrace : ∀ z ∈ S, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro z hz hzpos
    rcases hz with h | h
    · exact h
    · exact absurd h (not_le.mpr hzpos)
  have hSaet : ∀ z : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), z + t ∈ S := by
    intro z
    have hnull : volume ((fun t : ℝ => z + t) ⁻¹' Sᶜ) = 0 := by
      rw [MeasureTheory.measure_preimage_add]
      exact hSnull
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro t ht
    exact ht.1
  -- (H) the limit filters
  have hθl0 : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioo (-1:ℝ) (Real.pi / 2) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Filter.mem_inf_of_left
        (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
          (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem
        (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0)) h2) ?_
    intro x hx
    exact ⟨hx.1, hx.2.2⟩
  have hθl1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioi (0:ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      Filter.mem_inf_of_left
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem h2
        (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈
          nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))) ?_
    intro x hx
    exact ⟨hx.1, hx.2⟩
  -- (I) the a.e. vanishing of the interval integrals, left endpoint
  have hdct0 : ∀ z t : ℝ, 0 < z → 0 < t → z ∈ S → z + t ∈ S →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x) = 0 := by
    intro z t hz ht hzS hztS
    have htrz : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hStrace z hzS hz
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hStrace (z + t) hztS (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_sliceEnergy_div hS hMix (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hDCT := tendsto_setIntegral_pz hS (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (c := dzTrace0 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceEnergy u s) / s)) hz ht hθl0
      (fun s hs => by rw [htr0 s hs]; exact hlim0 s hs) ?_ hGint
    · have heq : (fun θ => u (z + t) θ - u z θ)
          =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
          (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
        filter_upwards [hθl0] with θ hθ
        exact (hftc z t θ hz ht hθ).symm
      have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using htrzt.sub htrz
      have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.congr' heq htr
      have huniq := tendsto_nhds_unique hDCT htr'
      have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
          = ∫ x in Set.Ioo z (z + t), dzTrace0 u x :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
      exact huniq
    · filter_upwards [hθl0] with θ hθ
      intro s hs
      have hs0 : 0 < s := lt_trans hz hs.1
      have hb := hslicebd s θ hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * Real.sqrt (sliceEnergy u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * (Real.sqrt (sliceEnergy u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
  -- (J) the right endpoint: the interval integrals for all `z, t`
  have hdct1 : ∀ z t : ℝ, 0 < z → 0 < t →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x) = 0 := by
    intro z t hz ht
    have htrz : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h (z + t)
        (by linarith)).1
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_sliceEnergy_div hS hMix (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hDCT := tendsto_setIntegral_pz hS
      (l := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (c := dzTrace1 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceEnergy u s) / s)) hz ht hθl1
      (fun s hs => by rw [htr1 s hs]; exact hlim1 s hs) ?_ hGint
    · have heq : (fun θ => u (z + t) θ - u z θ)
          =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
          (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
        filter_upwards [hθl1] with θ hθ
        exact (hftc z t θ hz ht hθ).symm
      have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using htrzt.sub htrz
      have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
        Filter.Tendsto.congr' heq htr
      have huniq := tendsto_nhds_unique hDCT htr'
      have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
          = ∫ x in Set.Ioo z (z + t), dzTrace1 u x :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
      exact huniq
    · filter_upwards [hθl1] with θ hθ
      intro s hs
      have hs0 : 0 < s := lt_trans hz hs.1
      have hb := hslicebd s θ hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * Real.sqrt (sliceEnergy u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * (Real.sqrt (sliceEnergy u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
  -- (K) the trace functions are locally integrable on `(0,∞)`
  have htrbd : ∀ s : ℝ, 0 < s → |dzTrace0 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
        * (Real.sqrt (sliceEnergy u s) / s) := by
    intro s hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr0 s hs, abs_div, abs_of_pos hs]
    calc |c0 s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * Real.sqrt (sliceEnergy u s)) / s :=
        div_le_div_of_nonneg_right (hc0bd s hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * (Real.sqrt (sliceEnergy u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  have htr1bd : ∀ s : ℝ, 0 < s → |dzTrace1 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
        * (Real.sqrt (sliceEnergy u s) / s) := by
    intro s hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr1 s hs, abs_div, abs_of_pos hs]
    calc |c1 s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * Real.sqrt (sliceEnergy u s)) / s :=
        div_le_div_of_nonneg_right (hc1bd s hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * (Real.sqrt (sliceEnergy u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  have hTrInt : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace0 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
          * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_sliceEnergy_div hS hMix (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace0 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs]
      exact htrbd s (lt_trans ha hs.1)
  have hTr1Int : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace1 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
          * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_sliceEnergy_div hS hMix (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace1 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs]
      exact htr1bd s (lt_trans ha hs.1)
  -- (L) the cut-off functions have vanishing interval integrals
  have hcut0 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z → z ∈ S → z + t ∈ S →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
    intro ε hε z t hz ht hεz hzS hztS
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace0 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace0 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct0 z t hz ht hzS hztS
  have hcut1 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
    intro ε hε z t hz ht hεz
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace1 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace1 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct1 z t hz ht
  -- (M) measurable full-measure good set and the two `D2` applications
  obtain ⟨N, hSN, hNmeas, hNnull⟩ := MeasureTheory.exists_measurable_superset_of_null hSnull
  have hS1meas : MeasurableSet Nᶜ := hNmeas.compl
  have hS1sub : Nᶜ ⊆ S := fun z hz => by
    by_contra hzs
    exact hz (hSN hzs)
  have hS1null : volume (Nᶜ)ᶜ = 0 := by simpa using hNnull
  have hS1trace : ∀ z ∈ Nᶜ, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    fun z hz hzpos => hStrace z (hS1sub hz) hzpos
  have hS1aet : ∀ z : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), z + t ∈ Nᶜ := by
    intro z
    have hnull : volume ((fun t : ℝ => z + t) ⁻¹' (Nᶜ)ᶜ) = 0 := by
      rw [MeasureTheory.measure_preimage_add]
      exact hS1null
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro t ht
    exact ht.1
  have hper0 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace0 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace0 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTrInt a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε ∩ Nᶜ)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi.inter hS1meas)]
        with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hS1aet z]
        with t ht hN
      exact hcut0 ε hεpos z t (lt_trans hεpos hz.1) ht hz.1
        (hS1sub hz.2) (hS1sub hN)
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    have hae : Set.Ioi ε ∩ Nᶜ =ᵐ[volume] Set.Ioi ε := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · rw [show (Set.Ioi ε ∩ Nᶜ) \ Set.Ioi ε = ∅ from Set.diff_eq_empty.mpr Set.inter_subset_left]
        simp
      · refine MeasureTheory.measure_mono_null ?_ hNnull
        intro z hz
        by_contra hzN
        exact hz.2 ⟨hz.1, hzN⟩
    rw [MeasureTheory.Measure.restrict_congr_set hae] at hmain
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace0 u)] at hz
  have hper1 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace1 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace1 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTr1Int a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hcut1 ε hεpos z t (lt_trans hεpos hz) ht hz
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace1 u)] at hz
  have hzero0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace0 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper0 n))
  have hzero1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace1 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper1 n))
  -- (N) conclusion
  have hconv0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [hzero0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hlim0 z hzpos
      rw [← htr0 z hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  have hconv1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    filter_upwards [hzero1, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := hlim1 z hzpos
      rw [← htr1 z hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  filter_upwards [hconv0, hconv1] with z h0 h1
  exact ⟨h0, h1⟩
end Work.FTS.EllipticEst.TT.AeI1
