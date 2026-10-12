import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.Fourier.gauss_translate_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Measure Set Filter
open scoped ENNReal

noncomputable section

namespace Commons.Analysis.Fourier

private abbrev V := EuclideanSpace ℝ (Fin 3)

/-- For `0 < s`, `C ≥ 0` and integrable, measurable `u`, the two-point Gaussian weight
`(x, y) ↦ |u x| * C * s^(−3/2) * exp(−π‖x − y‖²/s)` is integrable on `V × V`, and its
integral equals `C * ∫ |u|`. -/
lemma heat_W_integrable_value (u : V → ℝ) (hmu : Measurable u) (hui : MeasureTheory.Integrable u)
    {C : ℝ} (hC0 : 0 ≤ C) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable
        (fun p : V × V =>
          (|u p.1| * (C * s ^ (-(3 / 2 : ℝ)))) *
            Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))
        ((volume : Measure V).prod (volume : Measure V)) ∧
      (∫ p : V × V,
          (|u p.1| * (C * s ^ (-(3 / 2 : ℝ)))) *
            Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)
        ∂((volume : Measure V).prod (volume : Measure V)))
        = C * (∫ x : V, |u x| ∂(volume : Measure V)) := by
  let W : V × V → ℝ := fun p =>
    (|u p.1| * (C * s ^ (-(3 / 2 : ℝ)))) *
      Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)
  have hWnonneg : ∀ p : V × V, 0 ≤ W p := by
    intro p
    dsimp [W]
    have hs' : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hs) _
    positivity
  have hWmeas : Measurable W := by
    dsimp [W]
    fun_prop
  have hWsm : AEStronglyMeasurable W ((volume : Measure V).prod (volume : Measure V)) :=
    hWmeas.aestronglyMeasurable
  have hWint : MeasureTheory.Integrable W ((volume : Measure V).prod (volume : Measure V)) := by
    have hWiff := (integrable_prod_iff (μ := (volume : Measure V)) (ν := (volume : Measure V))
      (f := W) hWsm)
    rw [hWiff]
    constructor
    · filter_upwards with x
      have hker := Commons.Analysis.Fourier.gauss_translate_integrable hs x
      have hcx : MeasureTheory.Integrable
          (fun y : V => (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) *
            Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)) (volume : Measure V) := by
        simpa using (hker.1.const_mul (|u x| * (C * s ^ (-(3 / 2 : ℝ)))))
      exact hcx
    · have hQval : ∀ x : V, (∫ y : V, ‖W (x, y)‖ ∂(volume : Measure V)) = C * |u x| := by
        intro x
        calc
          (∫ y : V, ‖W (x, y)‖ ∂(volume : Measure V)) = ∫ y : V, W (x, y) ∂(volume : Measure V) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun y => by
              change ‖W (x, y)‖ = W (x, y)
              rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg (x, y))])
          _ = (∫ y : V, (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) *
              Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) ∂(volume : Measure V)) := by
            rfl
          _ = (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) *
              (∫ y : V, Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) ∂(volume : Measure V)) := by
            rw [integral_const_mul]
          _ = (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) * s ^ (3 / 2 : ℝ) := by
            rw [Commons.Analysis.Fourier.gauss_translate_integrable hs x |>.2]
          _ = C * |u x| := by
            have hsadd : s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) = 1 := by
              rw [← Real.rpow_add hs]
              norm_num
            calc
              (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) * s ^ (3 / 2 : ℝ)
                  = |u x| * (C * (s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ))) := by ring
              _ = |u x| * (C * 1) := by rw [hsadd]
              _ = C * |u x| := by ring
      have hQint : MeasureTheory.Integrable (fun x : V => C * |u x|) (volume : Measure V) := by
        exact hui.abs.const_mul C
      refine hQint.congr ?_
      exact Eventually.of_forall (fun x => (hQval x).symm)
  have hvalW : ∀ x : V, (∫ y : V, W (x, y) ∂(volume : Measure V)) = C * |u x| := by
    intro x
    calc
      (∫ y : V, W (x, y) ∂(volume : Measure V)) = ∫ y : V, ‖W (x, y)‖ ∂(volume : Measure V) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by
          change W (x, y) = ‖W (x, y)‖
          rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg (x, y))])
      _ = C * |u x| := by
        have hker := Commons.Analysis.Fourier.gauss_translate_integrable hs x
        calc
          (∫ y : V, ‖W (x, y)‖ ∂(volume : Measure V)) = ∫ y : V, W (x, y) ∂(volume : Measure V) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun y => by
              change ‖W (x, y)‖ = W (x, y)
              rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg (x, y))])
          _ = (∫ y : V, (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) *
              Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) ∂(volume : Measure V)) := by rfl
          _ = (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) *
              (∫ y : V, Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) ∂(volume : Measure V)) := by
            rw [integral_const_mul]
          _ = (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) * s ^ (3 / 2 : ℝ) := by
            rw [hker.2]
          _ = C * |u x| := by
            have hsadd : s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) = 1 := by
              rw [← Real.rpow_add hs]
              norm_num
            calc
              (|u x| * (C * s ^ (-(3 / 2 : ℝ)))) * s ^ (3 / 2 : ℝ)
                  = |u x| * (C * (s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ))) := by ring
              _ = |u x| * (C * 1) := by rw [hsadd]
              _ = C * |u x| := by ring
  constructor
  · exact hWint
  · calc
      (∫ p : V × V, W p ∂((volume : Measure V).prod (volume : Measure V)))
          = ∫ x : V, (∫ y : V, W (x, y) ∂(volume : Measure V)) ∂(volume : Measure V) := by
            exact integral_prod (μ := (volume : Measure V)) (ν := (volume : Measure V))
              (f := fun z : V × V => W z) hWint
      _ = ∫ x : V, C * |u x| ∂(volume : Measure V) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun x => hvalW x)
      _ = C * (∫ x : V, |u x| ∂(volume : Measure V)) := by
            rw [integral_const_mul]

/-- For `0 < s`, an integrable, measurable `u` bounded by `C`, the fibre
`(x, y) ↦ u x * (u y * (s^(−3/2) * exp(−π‖x − y‖²/s)))` is integrable on `V × V`. -/
lemma heat_fiber_integrable_of_bound (u : V → ℝ) (hmu : Measurable u)
    (hui : MeasureTheory.Integrable u) {C : ℝ} (hC : ∀ x : V, |u x| ≤ C) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable
        (fun p : V × V =>
          u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
            Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))))
        ((volume : Measure V).prod (volume : Measure V)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (u 0)) (hC 0)
  let Fp : V × V → ℝ := fun p =>
    u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)))
  let W : V × V → ℝ := fun p =>
    (|u p.1| * (C * s ^ (-(3 / 2 : ℝ)))) *
      Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)
  have hW := heat_W_integrable_value u hmu hui hC0 hs
  have hA0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hs) _
  have hbnd : ∀ p : V × V, ‖Fp p‖ ≤ W p := by
    intro p
    rw [Real.norm_eq_abs]
    have he0 : 0 ≤ Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s) := Real.exp_nonneg _
    have hAe0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s) :=
      mul_nonneg hA0 he0
    calc
      |Fp p| = |u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)))| := by rfl
      _ = |u p.1| * (|u p.2| * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))) := by
            rw [abs_mul (u p.1) (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))),
              abs_mul (u p.2) (s ^ (-(3 / 2 : ℝ)) *
                Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)),
              abs_of_nonneg hAe0]
      _ ≤ |u p.1| * (C * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hC p.2) hAe0) (abs_nonneg (u p.1))
      _ = W p := by
            dsimp [W]
            ring
  have hFmeas : Measurable Fp := by
    dsimp [Fp]
    fun_prop
  exact hW.1.mono' hFmeas.aestronglyMeasurable (Eventually.of_forall hbnd)

/-- For `0 < s`, integrable, measurable `u` bounded by `C`, the fibre norm-integral is
bounded by `C * ∫|u|`. -/
lemma heat_fiber_norm_bound_of_bound (u : V → ℝ) (hmu : Measurable u)
    (hui : MeasureTheory.Integrable u) {C : ℝ} (hC : ∀ x : V, |u x| ≤ C) {s : ℝ} (hs : 0 < s) :
    (∫ p : V × V,
        ‖u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)))‖
        ∂((volume : Measure V).prod (volume : Measure V)))
      ≤ C * (∫ x : V, |u x| ∂(volume : Measure V)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (u 0)) (hC 0)
  let Fp : V × V → ℝ := fun p =>
    u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)))
  let W : V × V → ℝ := fun p =>
    (|u p.1| * (C * s ^ (-(3 / 2 : ℝ)))) *
      Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)
  have hW := heat_W_integrable_value u hmu hui hC0 hs
  have hA0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hs) _
  have hbnd : ∀ p : V × V, ‖Fp p‖ ≤ W p := by
    intro p
    rw [Real.norm_eq_abs]
    have he0 : 0 ≤ Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s) := Real.exp_nonneg _
    have hAe0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s) :=
      mul_nonneg hA0 he0
    calc
      |Fp p| = |u p.1 * (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)))| := by rfl
      _ = |u p.1| * (|u p.2| * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))) := by
            rw [abs_mul (u p.1) (u p.2 * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))),
              abs_mul (u p.2) (s ^ (-(3 / 2 : ℝ)) *
                Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s)),
              abs_of_nonneg hAe0]
      _ ≤ |u p.1| * (C * (s ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(Real.pi * ‖p.1 - p.2‖ ^ 2) / s))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hC p.2) hAe0) (abs_nonneg (u p.1))
      _ = W p := by
            dsimp [W]
            ring
  have hFmeas : Measurable Fp := by
    dsimp [Fp]
    fun_prop
  have hFint : MeasureTheory.Integrable Fp ((volume : Measure V).prod (volume : Measure V)) := by
    exact hW.1.mono' hFmeas.aestronglyMeasurable (Eventually.of_forall hbnd)
  calc
    (∫ p : V × V, ‖Fp p‖ ∂((volume : Measure V).prod (volume : Measure V)))
        ≤ ∫ p : V × V, W p ∂((volume : Measure V).prod (volume : Measure V)) := by
          exact integral_mono hFint.norm hW.1 (fun p => hbnd p)
    _ = C * (∫ x : V, |u x| ∂(volume : Measure V)) := hW.2

/-- Integrability of the heat-triple integrand restricted to the `0 < s ≤ 1` region:
for a measurable, bounded, integrable real `u` on `V = EuclideanSpace ℝ (Fin 3)`, the function
`(p, s) ↦ u p.1 * (u p.2 * s^(−3/2)·exp(−π‖p.1 − p.2‖²/s))` on `(V × V) × ℝ` is integrable
w.r.t. `(volume.prod volume).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))`.
Strategy: bound `|u(p.2)| ≤ M` and for each `0 < s ≤ 1` integrate the `p.2` Gaussian first
(translation invariance and `GaussianFourier.integral_rexp_neg_mul_sq_norm` give
`∫_y exp(−π‖x − y‖²/s) dy = s^(3/2)`), so the contribution is bounded by `M·∫|u|` times a
function of `s` with finite measure on `(0,1]`; use Tonelli /
`MeasureTheory.integrable_prod_iff` / `MeasureTheory.hasFiniteIntegral_prod_iff'` to reduce
`(V × V) × ℝ` to iterated integrals. -/
theorem heat_triple_integrable_small (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hmu : Measurable u)
    (hu_bdd : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), |u x| ≤ C)
    (hui : MeasureTheory.Integrable u) :
    MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2))))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
  classical
  rcases hu_bdd with ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (u 0)) (hC 0)
  let ρ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let F : (V × V) × ℝ → ℝ := fun z =>
    u z.1.1 * (u z.1.2 * (z.2 ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2)))
  change MeasureTheory.Integrable F
    (((volume : Measure V).prod (volume : Measure V)).prod ρ)
  have hFmeas : Measurable F := by
    dsimp [F]
    fun_prop
  have hFsm : AEStronglyMeasurable F
      (((volume : Measure V).prod (volume : Measure V)).prod ρ) := hFmeas.aestronglyMeasurable
  rw [integrable_prod_iff' (μ := (volume : Measure V).prod (volume : Measure V)) (ν := ρ)
    (f := F) hFsm]
  constructor
  · dsimp [ρ]
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall ?_
    intro s hs
    simpa [F] using heat_fiber_integrable_of_bound u hmu hui hC hs.1
  · let A : ℝ := C * (∫ x : V, |u x| ∂(volume : Measure V))
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hC0 (integral_nonneg (fun x => abs_nonneg (u x)))
    let h : ℝ → ℝ := fun s => ∫ p : V × V,
        ‖F (p, s)‖ ∂((volume : Measure V).prod (volume : Measure V))
    have hb : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → ‖h s‖ ≤ A := by
      intro s hs
      have hle : h s ≤ A := by
        dsimp [h, A]
        change (∫ p : V × V, ‖F (p, s)‖
            ∂((volume : Measure V).prod (volume : Measure V)))
          ≤ C * (∫ x : V, |u x| ∂(volume : Measure V))
        simpa [F] using heat_fiber_norm_bound_of_bound u hmu hui hC hs.1
      have hnonneg : 0 ≤ h s := by
        dsimp [h]
        exact integral_nonneg (μ := (volume : Measure V).prod (volume : Measure V))
          (f := fun p : V × V => ‖F (p, s)‖) (by intro p; exact norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
    have hb_ae : ∀ᵐ s : ℝ ∂ρ, ‖h s‖ ≤ A := by
      dsimp [ρ]
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall (fun s hs => hb s hs)
    have hnsm : AEStronglyMeasurable (fun z : (V × V) × ℝ => ‖F z‖)
        (((volume : Measure V).prod (volume : Measure V)).prod ρ) := hFsm.norm
    have hhsm : AEStronglyMeasurable h ρ := by
      have hsw : AEStronglyMeasurable (fun z : ℝ × (V × V) => ‖F z.swap‖)
          (ρ.prod ((volume : Measure V).prod (volume : Measure V))) :=
        hnsm.prod_swap
      have htmp := hsw.integral_prod_right' (μ := ρ)
        (ν := (volume : Measure V).prod (volume : Measure V))
      simpa [h] using htmp
    have hvol : (volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) < ∞ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hhfi : HasFiniteIntegral h ρ := by
      dsimp [ρ]
      exact HasFiniteIntegral.restrict_of_bounded (μ := (volume : Measure ℝ))
        (s := Set.Ioc (0 : ℝ) 1) (C := A) hvol hb_ae
    exact ⟨hhsm, hhfi⟩

end Commons.Analysis.Fourier