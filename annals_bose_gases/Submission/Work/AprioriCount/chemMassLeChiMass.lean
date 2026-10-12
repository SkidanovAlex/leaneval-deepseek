import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.Defs
import Submission.Work.BoseFixGlue.Pot.ellB_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.AprioriCount.chemMassLeChiMass` — the one-body (chemical) mass is controlled by the
χ-mass

This module proves the elementary half of the reduction described in
`Submission/Work/AprioriCount/FINDING_cubeCountWindow.md` §2: the one-body mass of a box state
against the chemical kernel `w₁ = wLoc ℓ (g₀ v h) 0` is dominated by the **χ-mass** of the state,

    M₁ := ∫_{abox n ℓ} Φ² · Σᵢ ∫_y w₁(xᵢ,y) dy  ≤  K₀ · chiCount ℓ Φ ,
    chiCount ℓ Φ := ∫_{abox n ℓ} Φ² · Σᵢ χ_ℓ(xᵢ)      (K₀ := 2·chiSup·∫|g₀|).

## The mathematics

The localised kernel **factorises through the particle's own window**:

    wLoc ℓ g 0 x y = χ_ℓ(x) · W(x−y) · χ_ℓ(y) ,        W := wScaled ℓ g ,

so that for fixed `a = xᵢ`

    ∫_y wLoc ℓ g 0 a y dy = χ_ℓ(a) · ∫_y W(a−y)·χ_ℓ(y) dy .

The second factor is bounded by `2·chiSup·∫|g|` **uniformly in `a`** (in the dilute regime
`R ≤ ℓ·chiR0`): on the support of the numerator `|W| ≤ 2|g|` (`abs_wScaled_le`, since
`(χ⋆χ)(z/ℓ) ≥ 1/2` there), `|χ_ℓ| ≤ chiSup` pointwise, and translation invariance gives
`∫|g(a−y)| dy = ∫|g|`.  Hence, pointwise in the configuration,

    Φ²·Σᵢ ∫_y wLoc ℓ (g₀) 0 (xᵢ) y dy ≤ K₀ · Φ²·Σᵢ χ_ℓ(xᵢ) ,

and integrating over the box `abox n ℓ` gives the claim.  Note the χ factor at `xᵢ` is *extracted*
(not bounded by `chiSup`): this is what makes the bound sharp enough to be useful — a state
concentrated near a face of the box, where `χ_ℓ` is small, has a correspondingly small chemical
mass.

## Structure

* `wScaled_chiScale_integral_abs_le` — the uniform bound on the inner integral (measure theory:
  `Integrable.mono'`, `integral_mono`, translation invariance);
* `potBr_zero_le_aux` — the factorisation + the uniform bound, i.e. the pointwise fibre bound;
* `chemMassCore` — the box assembly, with the pointwise bound applied to each slot (the outer
  comparison uses `integral_mono` when the LHS is integrable and the (vacuous) `integral_undef`
  branch otherwise, so no measurability of the LHS integrand is needed);
* `chemMassLeChiMass` — the frozen statement, with `ε₀` supplied by `Work.BoseFixGlue.Pot.ellB_ge`
  (which produces the dilute-regime condition `R ≤ sideAt μ (a v)·chiR0` for all small `μ a³`).
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The uniform bound on the inner window integral.**  In the dilute regime (`0 < ℓ`,
`R ≤ ℓ·chiR0`, numerator `g` supported in `ball 0 R`, `(χ⋆χ) ≥ 1/2` on `ball 0 r₀`),

    |∫_y (g(a−y)/(χ⋆χ)((a−y)/ℓ))·χ_ℓ(y) dy| ≤ 2·chiSup·∫|g| ,

uniformly in `a`.  Proof: `|wScaled| ≤ 2|g|` on the support of `g`, `|χ_ℓ| ≤ chiSup`, then
`abs_integral_le_integral_abs` + `integral_mono` + translation invariance. -/
private theorem wScaled_chiScale_integral_abs_le {g : E3 → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hi : MeasureTheory.Integrable g) (hgsupp : ∀ z : E3, R ≤ ‖z‖ → g z = 0)
    (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ z : E3, ‖z‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z)
    (a : E3) :
    |∫ y : E3, Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y|
      ≤ 2 * Work.BoseBox.chiSup * (∫ z : E3, |g z|) := by
  -- the window factor is bounded by `chiSup`
  have hchi : ∀ y : E3, |Submission.BoseGases.chiScale ℓ y| ≤ Work.BoseBox.chiSup := by
    intro y
    simpa [Submission.BoseGases.chiScale] using Work.BoseBox.abs_chi_le_chiSup ((ℓ⁻¹) • y)
  -- pointwise domination of the integrand
  have hpt : ∀ y : E3,
      |Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y|
        ≤ 2 * Work.BoseBox.chiSup * |g (a - y)| := by
    intro y
    have h1 : |Submission.BoseGases.wScaled ℓ g (a - y)| ≤ 2 * |g (a - y)| :=
      Submission.BoseGases.abs_wScaled_le hℓ hgsupp hRℓ hC (a - y)
    have h3 : 0 ≤ (2 : ℝ) * |g (a - y)| := by positivity
    have h4 : 0 ≤ |Submission.BoseGases.chiScale ℓ y| := abs_nonneg _
    calc |Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y|
        = |Submission.BoseGases.wScaled ℓ g (a - y)| * |Submission.BoseGases.chiScale ℓ y| :=
          abs_mul _ _
      _ ≤ (2 * |g (a - y)|) * Work.BoseBox.chiSup := mul_le_mul h1 (hchi y) h4 h3
      _ = 2 * Work.BoseBox.chiSup * |g (a - y)| := by ring
  -- the majorant is integrable
  have hdom : MeasureTheory.Integrable
      (fun y : E3 => 2 * Work.BoseBox.chiSup * |g (a - y)|) :=
    (Submission.BoseGases.km_integrable_comp_sub_left hi.abs a).const_mul (2 * Work.BoseBox.chiSup)
  -- a.e. strong measurability of the integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : E3 => Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y)
      MeasureTheory.volume := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun y : E3 => g (a - y))
        MeasureTheory.volume :=
      Submission.BoseGases.km_aestronglyMeasurable_comp_sub_left hi.aestronglyMeasurable a
    have hcs : Continuous (fun y : E3 => Submission.BoseGases.convScale ℓ (a - y)) :=
      (Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun y : E3 => Submission.BoseGases.wScaled ℓ g (a - y)) MeasureTheory.volume := by
      have hEq : (fun y : E3 => Submission.BoseGases.wScaled ℓ g (a - y))
          = fun y => g (a - y) * (Submission.BoseGases.convScale ℓ (a - y))⁻¹ := by
        funext y; dsimp [Submission.BoseGases.wScaled]; rw [div_eq_mul_inv]
      rw [hEq]
      exact h1.mul
        ((by fun_prop : Measurable fun t : ℝ => t⁻¹).comp hcs.measurable).aestronglyMeasurable
    exact h2.mul (Submission.BoseGases.chiScale_continuous ℓ).aestronglyMeasurable
  have hint : MeasureTheory.Integrable
      (fun y : E3 => Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y)
      MeasureTheory.volume :=
    MeasureTheory.Integrable.mono' hdom hmeas (by
      filter_upwards with y
      rw [Real.norm_eq_abs]
      exact hpt y)
  calc |∫ y : E3, Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y| ≤
        ∫ y : E3, |Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ y : E3, 2 * Work.BoseBox.chiSup * |g (a - y)| :=
        MeasureTheory.integral_mono hint.abs hdom (fun y => hpt y)
    _ = 2 * Work.BoseBox.chiSup * ∫ y : E3, |g (a - y)| := by
        rw [MeasureTheory.integral_const_mul]
    _ = 2 * Work.BoseBox.chiSup * ∫ z : E3, |g z| := by
        rw [show (∫ y : E3, |g (a - y)|) = ∫ z : E3, |g z| from
          Submission.BoseGases.integral_comp_sub_left (fun z => |g z|) a]

/-- **The pointwise fibre bound**: extracting the window factor `χ_ℓ(a)` of the localised chemical
kernel, the remaining integral is bounded uniformly in `a`:

    ∫_y w₁(a,y) dy ≤ (2·chiSup·∫|g₀|)·χ_ℓ(a) .

This is the sharp form (strictly stronger than the corpus's `Work.BoseBox.abs_potBr_le`, which
gives the `a`-independent bound `2·chiSup²·∫|g₀|`): the factor `χ_ℓ(a)` is *not* estimated by
`chiSup`. -/
private theorem potBr_zero_le_aux {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (a : E3) :
    Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 a
      ≤ (2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h) * Submission.BoseGases.chiScale ℓ a := by
  -- the factorisation of the fibre integral through the window at `a`
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
  -- the uniform bound on the remaining integral
  have hb : |∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
        * Submission.BoseGases.chiScale ℓ y|
      ≤ 2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h :=
    wScaled_chiScale_integral_abs_le hℓ
      (Submission.BoseGases.g0_integrable hR hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hRℓ
      (fun z hz => Submission.BoseGases.chiR0_half z hz) a
  rw [hfac]
  have hchi : 0 ≤ Submission.BoseGases.chiScale ℓ a := Submission.BoseGases.chi_nonneg _
  calc Submission.BoseGases.chiScale ℓ a
        * ∫ y : E3, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (a - y)
            * Submission.BoseGases.chiScale ℓ y
      ≤ Submission.BoseGases.chiScale ℓ a
          * (2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h) :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hb) hchi
    _ = (2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h)
          * Submission.BoseGases.chiScale ℓ a := by ring

/-- **The box assembly at a general side `ℓ`.**  For every box state `Φ` of the `n`-particle box of
side `ℓ` in the dilute regime `R ≤ ℓ·chiR0`, the chemical mass is bounded by the χ-mass with the
fixed constant `K₀ = 2·chiSup·∫|g₀|`.

The outer comparison is the pointwise bound `potBr_zero_le_aux`, applied slot by slot, and then one
monotone integral comparison: in the (vacuous if `K₀ ≥ 0`) non-integrable case the left integral
is `0` by `integral_undef`, so no measurability of the left integrand is required. -/
private theorem chemMassCore {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 *
          ∑ i : Fin n,
            ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ≤ (2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h)
          * chiCount ℓ (Φ : Submission.BoseGases.X n → ℝ) := by
  set K₀ : ℝ := 2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h with hK₀def
  have hchiNN : ∀ a : E3, 0 ≤ Submission.BoseGases.chiScale ℓ a :=
    fun a => Submission.BoseGases.chi_nonneg _
  have hK₀ : 0 ≤ K₀ := by
    rw [hK₀def]
    have h1 : 0 ≤ Work.BoseBox.chiSup := le_of_lt Submission.BoseGases.chiSup_pos
    have h2 : 0 ≤ Work.BoseBox.g0mass v h := by
      rw [Work.BoseBox.g0mass]
      exact MeasureTheory.integral_nonneg (fun z => abs_nonneg _)
    positivity
  -- the pointwise comparison of the two integrands
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 *
          ∑ i : Fin n,
            ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y
        ≤ K₀ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
    intro x
    have h1 : (∑ i : Fin n,
            ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ ∑ i : Fin n, K₀ * Submission.BoseGases.chiScale ℓ (x i) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact potBr_zero_le_aux hR hv_supp hℓ hRℓ (x i)
    have h2 : (∑ i : Fin n, K₀ * Submission.BoseGases.chiScale ℓ (x i))
        = K₀ * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) := by
      rw [Finset.mul_sum]
    rw [h2] at h1
    calc (Φ x) ^ 2 * (∑ i : Fin n,
            ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ (Φ x) ^ 2 * (K₀ * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = K₀ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by ring
  -- the χ-side integrand is continuous, hence integrable on the (compact) box
  have hGcont : Continuous (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) := by
    have hΦc : Continuous (fun x : Submission.BoseGases.X n => (Φ x)) := Φ.contDiff.continuous
    refine (hΦc.pow 2).mul ?_
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)
  have hGnn : ∀ x : Submission.BoseGases.X n,
      0 ≤ (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) := by
    intro x
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => hchiNN (x i)))
  have hGint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      hGcont.continuousOn
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ≤ K₀ * ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) := by
    by_cases hF : MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n =>
          (Φ x) ^ 2 * ∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
    · have hKG : MeasureTheory.Integrable
          (fun x : Submission.BoseGases.X n =>
            K₀ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) :=
        hGint.const_mul K₀
      have hmono := MeasureTheory.integral_mono hF hKG hpt
      rwa [MeasureTheory.integral_const_mul] at hmono
    · rw [MeasureTheory.integral_undef hF]
      exact mul_nonneg hK₀ (MeasureTheory.integral_nonneg hGnn)
  simpa only [chiCount] using hmain

theorem chemMassLeChiMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.AprioriCount.ChemMassLeChiMass v h R := by
  -- the diluteness threshold at which the box side dominates `R / chiR0`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Work.BoseFixGlue.Pot.ellB_ge hav hR
  refine ⟨2 * Work.BoseBox.chiSup * Work.BoseBox.g0mass v h, ε₁, ?_, hε₁pos, ?_⟩
  · have h1 : 0 ≤ Work.BoseBox.chiSup := le_of_lt Submission.BoseGases.chiSup_pos
    have h2 : 0 ≤ Work.BoseBox.g0mass v h := by
      rw [Work.BoseBox.g0mass]
      exact MeasureTheory.integral_nonneg (fun z => abs_nonneg _)
    positivity
  · intro μ hAdm J hJ _ n Φ _
    have hμpos : 0 < μ := hAdm.1
    have hμa3 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ := hAdm.2.1
    obtain ⟨hℓpos, hRℓ⟩ := hε₁ μ hμpos hμa3
    exact chemMassCore hR hv_supp hℓpos hRℓ n Φ

end Work.AprioriCount
