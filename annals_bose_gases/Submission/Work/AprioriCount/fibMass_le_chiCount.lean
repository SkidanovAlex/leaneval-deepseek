import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.Defs
import Submission.Work.AprioriCount.wScaledChiScaleIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.fibMass_le_chiCount` — the chemical (`g₀`) mass against the χ-mass

The frozen target (D1 of `FINDING_flatLeChi.md` §3) is the **unguarded, exact** form of the
chemical-mass / χ-mass bound: for every continuous `Φ` on the `n`-particle box of side `ℓ` in the
dilute regime `R ≤ ℓ·chiR0`,

    M₁ := ∫_{abox n ℓ} Φ² · Σᵢ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y dy
        ≤ fsqC1(a v) · chiCount ℓ Φ ,
    chiCount ℓ Φ := ∫_{abox n ℓ} Φ² · Σᵢ χ_ℓ(xᵢ) ,
    fsqC1(a v) = chiSup²·2·(8π a v) ,   chiSup = (∫χ_base²)^{-1/2} .

## The mathematics

The localised chemical kernel **factorises through the particle's own window**: with
`wLoc ℓ g u x y = χ_u(x)·W(x−y)·χ_u(y)` and `W = wScaled ℓ g`,

    wLoc ℓ g 0 x y = χ_ℓ(x)·W(x−y)·χ_ℓ(y) ,

so that, for fixed `a = xᵢ` (and writing `potBr ℓ g u a = ∫_y wLoc ℓ g u a y`),

    potBr ℓ g₀ 0 a = χ_ℓ(a) · ∫_y W(a−y)·χ_ℓ(y) dy .

The second factor is bounded by `2·chiSup·∫|g₀|` uniformly in `a` (the *one*-χ-factor bound:
`|W| ≤ 2|g₀|` on the support of `g₀` in the dilute regime — `abs_wScaled_le` — and
`|χ_ℓ| ≤ chiSup`).  Since `0 ≤ χ_ℓ`,

    potBr ℓ g₀ 0 a ≤ χ_ℓ(a) · 2·chiSup·∫|g₀| ≤ χ_ℓ(a) · fsqC1(a v) ,

the last step being `2·chiSup·∫|g₀| ≤ chiSup²·2·(8π a v)`: `∫|g₀| = ∫g₀ = 8π a v ≥ 0`
(`g0_integral`, `g0_nonneg_ae`) and `chiSup ≤ chiSup²`, i.e. `1 ≤ chiSup`, which holds because
`∫χ_base² ≤ vol(ball 0 (1/2)) = π/6 < 1` (`Work.UBBInputs9.B.chiSup_sq_ge`).  Summing over `i`,
multiplying by `Φ² ≥ 0` and integrating over the box gives the claim.

Note the factor `χ_ℓ(xᵢ)` is *extracted*, not bounded by `chiSup`: a state concentrated near a face
of the box, where `χ_ℓ` is small, has a correspondingly small chemical mass.

## Contents

* `wScaledChiScaleIntegral` (delegated, in `Submission/Work/AprioriCount/wScaledChiScaleIntegral.lean`)
  — the uniform bound on the inner window integral;
* `g0mass_eq_eight_pi_a` — `∫|g₀| = 8π a v`;
* `one_le_chiSup` — `1 ≤ chiSup`;
* `potBr_le_fsqC1` — the pointwise fibre bound with the sharp χ-factor;
* `fibMass_le_chiCount` — the frozen target.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ### The uniform bound on the inner window integral

The analytic brick (the *one*-χ-factor fibre domination, delegated and proved as
`Work.AprioriCount.wScaledChiScaleIntegral` in
`Submission/Work/AprioriCount/wScaledChiScaleIntegral.lean`):

    |∫_y (g(a−y)/(χ⋆χ)((a−y)/ℓ))·χ_ℓ(y) dy| ≤ 2·chiSup·∫|g| ,

uniformly in `a`, for an integrable `g` supported in `ball 0 R` in the dilute regime
`R ≤ ℓ·r₀` (`(χ⋆χ) ≥ 1/2` on `ball 0 r₀`).  It is the content of `abs_wScaled_le` plus
`|χ_ℓ| ≤ chiSup`. -/

/-! ### The elementary constant facts -/

/-- `∫|g₀| = 8π·a v` (`g₀ ≥ 0` a.e. and `∫g₀ = 8π a v`). -/
theorem g0mass_eq_eight_pi_a {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    Work.BoseBox.g0mass v h = 8 * Real.pi * _root_.BoseGases.a v := by
  have hnn := Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have h1 : (∫ y : E3, |Submission.BoseGases.g0 v h y|)
      = ∫ y : E3, Submission.BoseGases.g0 v h y := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hnn] with y hy
    exact abs_of_nonneg hy
  rw [Work.BoseBox.g0mass, h1, Submission.BoseGases.g0_integral hR hv_supp h]

/-- `1 ≤ chiSup`, from `χ_base ≤ 1` with support in `ball 0 (1/2)` (`chiSup² ≥ 1 + 1/1000`). -/
theorem one_le_chiSup : 1 ≤ Submission.BoseGases.chiSup := by
  have h := Work.UBBInputs9.B.chiSup_sq_ge
  have hp := Submission.BoseGases.chiSup_pos
  nlinarith [h, hp]

/-! ### The pointwise fibre bound with the sharp window factor -/

/-- **The pointwise fibre bound.**  Extracting the window factor `χ_ℓ(a)` of the localised
chemical kernel, the remaining integral is bounded uniformly in `a`, and the constant is inflated
to the frozen one `fsqC1 (a v) = chiSup²·2·(8π a v)`:

    ∫_y wLoc ℓ (g₀ v h) 0 a y dy ≤ fsqC1 (a v) · χ_ℓ(a) . -/
private theorem potBr_le_fsqC1 {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (a : E3) :
    Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 a
      ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) * Submission.BoseGases.chiScale ℓ a := by
  have hfac : Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 a
      = Submission.BoseGases.chiScale ℓ a
        * ∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
            * Submission.BoseGases.chiScale ℓ y := by
    rw [Work.BoseBox.potBr]
    simp only [Submission.BoseGases.wLoc, Submission.BoseGases.chiU, Submission.BoseGases.chiScale,
      sub_zero]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  have hgm : Work.BoseBox.g0mass v h = 8 * Real.pi * _root_.BoseGases.a v :=
    g0mass_eq_eight_pi_a hR hv hvrad hv_supp
  have ha0 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by
    rw [← hgm, Work.BoseBox.g0mass]
    exact MeasureTheory.integral_nonneg (fun z => abs_nonneg _)
  have hb : |∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
        * Submission.BoseGases.chiScale ℓ y|
      ≤ 2 * Submission.BoseGases.chiSup * Work.BoseBox.g0mass v h := by
    rw [Work.BoseBox.g0mass]
    exact wScaledChiScaleIntegral (g := Submission.BoseGases.g0 v h) hℓ
      (Submission.BoseGases.g0_integrable hR hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hRℓ
      (fun z hz => Submission.BoseGases.chiR0_half z hz) a
  have hkey : 2 * Submission.BoseGases.chiSup * Work.BoseBox.g0mass v h
      ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) := by
    rw [hgm]
    have hc1 : 1 ≤ Submission.BoseGases.chiSup := one_le_chiSup
    have hc0 : 0 ≤ Submission.BoseGases.chiSup := le_of_lt Submission.BoseGases.chiSup_pos
    have hcSq : Submission.BoseGases.chiSup ≤ Submission.BoseGases.chiSup ^ 2 := by nlinarith
    have h2 : (0 : ℝ) ≤ 2 * (8 * Real.pi * _root_.BoseGases.a v) := by linarith
    have h3 := mul_le_mul_of_nonneg_right hcSq h2
    simp only [Submission.BoseGases.fsqC1]
    linarith
  have hI : ∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
      * Submission.BoseGases.chiScale ℓ y ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) :=
    le_trans (le_abs_self _) (le_trans hb hkey)
  calc Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 a
      = Submission.BoseGases.chiScale ℓ a
        * ∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
            * Submission.BoseGases.chiScale ℓ y := hfac
    _ ≤ Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left hI (Submission.BoseGases.chiScale_nonneg ℓ a)
    _ = Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
        * Submission.BoseGases.chiScale ℓ a := by ring

theorem fibMass_le_chiCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
          * Work.AprioriCount.chiCount ℓ Φ := by
  have hgm : Work.BoseBox.g0mass v h = 8 * Real.pi * _root_.BoseGases.a v :=
    g0mass_eq_eight_pi_a hR hv hvrad hv_supp
  have ha0 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by
    rw [← hgm, Work.BoseBox.g0mass]
    exact MeasureTheory.integral_nonneg (fun z => abs_nonneg _)
  have hK0 : 0 ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) := by
    simp only [Submission.BoseGases.fsqC1]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by norm_num)) ha0
  -- the pointwise comparison of the two integrands
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y
        ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
    intro x
    have h1 : (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ ∑ i : Fin n, Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * Submission.BoseGases.chiScale ℓ (x i) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      simpa only [Work.BoseBox.potBr] using potBr_le_fsqC1 hR hv hvrad hv_supp hℓ hRℓ (x i)
    have h2 : (∑ i : Fin n, Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
          * Submission.BoseGases.chiScale ℓ (x i))
        = Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
          * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) := by
      rw [Finset.mul_sum]
    rw [h2] at h1
    calc (Φ x) ^ 2 * (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ (Φ x) ^ 2 * (Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
          * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by ring
  -- the χ-side integrand is continuous, hence integrable on the (compact) box
  have hGcont : Continuous (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
    refine (hΦc.pow 2).mul ?_
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)
  have hGnn : ∀ x : Submission.BoseGases.X n,
      0 ≤ (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) := by
    intro x
    exact mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun i _ => Submission.BoseGases.chiScale_nonneg ℓ (x i)))
  have hGint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      hGcont.continuousOn
  by_cases hF : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))
  · have hKG : MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
      hGint.const_mul _
    have hmono := MeasureTheory.integral_mono hF hKG hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    simpa only [chiCount] using hmono
  · rw [MeasureTheory.integral_undef hF]
    simp only [chiCount]
    exact mul_nonneg hK0 (MeasureTheory.integral_nonneg hGnn)

end Work.AprioriCount
