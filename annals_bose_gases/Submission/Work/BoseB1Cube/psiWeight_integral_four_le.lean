import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.nomRouteCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.psiWeight_integral_four_le`

FS's `eq:badset` arithmetic in **integrated** form: the a-priori remainder weight `ψ` read at the
**doubled** chemical-potential slot `4μ` is dominated by four times the weight at the slot `μ`
plus the constant `12μ²`, *uniformly in the state* `Φ` and in the box:

    ∫_{abox n ℓ} Φ²·ψ(1, 4μ, n_{B(u)}/|B(u)|)
      ≤ 4 ∫_{abox n ℓ} Φ²·ψ(1, μ, n_{B(u)}/|B(u)|) + 12 μ² ∫_{abox n ℓ} Φ² ,

where `n_{B(u)}(x) = boxIndCount ℓ d u x` is the indicator count of the sliding box and
`|B(u)| = boxMass ℓ d u` its volume (`0 < boxMass` is the standing non-degeneracy hypothesis).

The pointwise core `ψ(1,4μ,t) ≤ 4ψ(1,μ,t) + 12μ²` for `t ≥ 0` is the PROVED
`Work.BoseB1Cube.psiWeight_four_le` (`nomRouteCube.lean`; after clearing the positive denominators
`(t+μ)(t+4μ)` the difference is exactly `3t² ≥ 0`).  Here we lift it to the integral against
`Φ² ≥ 0` over the (finite-measure, compact) configuration box: the local density
`t x = boxIndCount ℓ d u x / boxMass ℓ d u` is nonnegative and bounded by `n/|B(u)|`, which makes
every term occurring below integrable, so the monotonicity and linearity of the Bochner integral
apply.

The only non-elementary inputs are
* `boxIndCount_nonneg` and the card bound `boxIndCount ≤ n` (the count of a box in `n` particles),
* measurability of the count (the indicator of the measurable set `dlBox ℓ d u`, composed with a
  coordinate projection),
* `abox_compact`/`abox_lt_top` (the configuration box is compact, hence of finite measure),
* the mass bound `ψ(1,μ,t) ≤ μ t + μ²` for `t ≥ 0`, which bounds the whole integrand by the
  constant `C²(μ n/|B(u)| + μ²)` on `abox n ℓ`.

This is the elementary analytic input of the slot doubling in `nomRouteCube.lean`'s
`PerBoxFNomSlots`/`perBoxFNom_slots_of_row` (`PsiWeightFourIntegral`).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The elementary facts about the indicator count -/

/-- The indicator count of the sliding box is measurable (it is a sum of indicators of the
measurable set `dlBox ℓ d u`, evaluated at the coordinates). -/
private lemma measurable_boxIndCount {n : ℕ} (ℓ d : ℝ) (u : E3) :
    Measurable fun x : X n => boxIndCount ℓ d u x := by
  change Measurable fun x : X n =>
    ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_const.indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)).comp
      (measurable_pi_apply i)

/-- The indicator count is at most the particle number. -/
private lemma boxIndCount_le_card {n : ℕ} (ℓ d : ℝ) (u : E3) (x : X n) :
    boxIndCount ℓ d u x ≤ (n : ℝ) := by
  rw [boxIndCount]
  calc (∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : x i ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; norm_num
    _ = (n : ℝ) := by simp

/-- `Work.SmallBoxSliding.psiWeight` is measurable as a function of its third argument. -/
private lemma measurable_psiWeight_one (μ : ℝ) :
    Measurable fun t : ℝ => Work.SmallBoxSliding.psiWeight 1 μ t := by
  unfold Work.SmallBoxSliding.psiWeight
  fun_prop

/-- The mass bound `ψ(1,μ,t) ≤ μ t + μ²` on the physical range `t ≥ 0`. -/
private lemma psiWeight_one_le_mu_add' {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * t + μ ^ 2 := by
  have hden2 : (0 : ℝ) < 1 + t * μ⁻¹ := by
    have h2 : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  rw [div_le_iff₀ hden2]
  field_simp
  nlinarith [mul_nonneg ht hμ.le, sq_nonneg μ]

/-! ## 2. The integral form at a general (measurable) count -/

/-- **The integrated `4μ`-comparison at an abstract nonnegative bounded count.**  For a continuous
state `Φ`, a measure-theoretic count `t = count/M` with `0 ≤ count ≤ n` and `M > 0`,

    ∫_{abox n ℓ} Φ²·ψ(1,4μ)(count/M)
      ≤ 4 ∫_{abox n ℓ} Φ²·ψ(1,μ)(count/M) + 12 μ² ∫_{abox n ℓ} Φ² .

The proof is the pointwise inequality `psiWeight_four_le` against `Φ² ≥ 0`, monotonicity of the
integral (legitimate because the majorant is bounded by `C²(4(μ t + μ²) + 12μ²)` on the compact
box), and the linearity identity
`Φ²(4ψ + 12μ²) = 4(Φ²ψ) + 12μ²Φ²`. -/
private lemma integral_psiWeight_four_le_aux {n : ℕ} {ℓ μ M : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hV : 0 < M) {Φ : X n → ℝ} (hΦm : Measurable Φ)
    {count : X n → ℝ} (hcountm : Measurable count)
    (hcount0 : ∀ x, 0 ≤ count x) (hcountle : ∀ x, count x ≤ (n : ℝ))
    {C : ℝ} (hC0 : 0 ≤ C) (hCb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 (4 * μ) (count x / M))
      ≤ 4 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              Work.SmallBoxSliding.psiWeight 1 μ (count x / M))
        + 12 * μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  set t : X n → ℝ := fun x => count x / M with ht
  have ht0 : ∀ x, 0 ≤ t x := fun x => by
    simp only [ht]; exact div_nonneg (hcount0 x) hV.le
  have htle : ∀ x, t x ≤ (n : ℝ) / M := fun x => by
    simp only [ht]; exact div_le_div_of_nonneg_right (hcountle x) hV.le
  have htmeas : Measurable t := by
    simp only [ht]; exact hcountm.div_const M
  have hθ0 : (0 : ℝ) < 4 * μ := by linarith
  have hnM0 : 0 ≤ (n : ℝ) / M := div_nonneg (Nat.cast_nonneg n) hV.le
  -- integrability of `Φ²`
  have hF2int : IntegrableOn (fun x : X n => (Φ x) ^ 2) (Submission.BoseGases.abox n ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hΦm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact Filter.Eventually.of_forall fun x hx => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hCb x hx) 2)
  -- integrability of `Φ²·ψ_μ(t)`
  have hpsiInt : IntegrableOn
      (fun x : X n => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
      (Submission.BoseGases.abox n ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      ((hΦm.pow_const 2).mul ((measurable_psiWeight_one μ).comp htmeas)).aestronglyMeasurable
      (C ^ 2 * (μ * ((n : ℝ) / M) + μ ^ 2))
      (by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        refine Filter.Eventually.of_forall fun x hx => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (psiWeight_nonneg' hμ (ht0 x))]
        have h1 : |Φ x| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCb x hx) 2
        have h2 : Work.SmallBoxSliding.psiWeight 1 μ (t x) ≤ μ * ((n : ℝ) / M) + μ ^ 2 := by
          have h3 := psiWeight_one_le_mu_add' hμ (ht0 x)
          have h4 : μ * t x ≤ μ * ((n : ℝ) / M) := mul_le_mul_of_nonneg_left (htle x) hμ.le
          linarith
        exact mul_le_mul h1 h2 (psiWeight_nonneg' hμ (ht0 x))
          (by nlinarith [mul_nonneg hμ.le hnM0, sq_nonneg μ]))
  -- integrability of the majorant `Φ²·(4ψ_μ(t) + 12μ²)`
  have hgInt : IntegrableOn
      (fun x : X n => (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x) + 12 * μ ^ 2))
      (Submission.BoseGases.abox n ℓ) volume := by
    have h : (fun x : X n => (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x)
          + 12 * μ ^ 2))
        = fun x => 4 * ((Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
            + 12 * μ ^ 2 * ((Φ x) ^ 2) := by
      funext x; ring
    rw [h]
    exact (hpsiInt.const_mul 4).add (hF2int.const_mul (12 * μ ^ 2))
  -- the monotone step
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 (4 * μ) (t x))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x) + 12 * μ ^ 2) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (psiWeight_nonneg' hθ0 (ht0 x)))
      hgInt
      (Filter.Eventually.of_forall fun x =>
        mul_le_mul_of_nonneg_left (psiWeight_four_le hμ (ht0 x)) (sq_nonneg _))
  -- linearity of the majorant
  have hsplit : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x) + 12 * μ ^ 2))
      = 4 * (∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
        + 12 * μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x) + 12 * μ ^ 2))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (4 * ((Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
              + 12 * μ ^ 2 * ((Φ x) ^ 2)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
    rw [integral_add (hpsiInt.const_mul 4) (hF2int.const_mul (12 * μ ^ 2)),
      integral_const_mul, integral_const_mul]
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 (4 * μ) (t x))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (4 * Work.SmallBoxSliding.psiWeight 1 μ (t x) + 12 * μ ^ 2) := hmono
    _ = 4 * (∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
        + 12 * μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := hsplit

/-! ## 3. The target -/

theorem psiWeight_integral_four_le {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 (4 * μ)
          (Work.BoseB1Cube.boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      ≤ 4 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              Work.SmallBoxSliding.psiWeight 1 μ
                (Work.BoseB1Cube.boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
        + 12 * μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := Φ) hΦ.continuousOn
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC _ (Submission.BoseGases.zero_mem_abox (N := n) hℓ.le))
  have hCb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  exact integral_psiWeight_four_le_aux (ℓ := ℓ) (μ := μ)
    (M := Work.SmallBoxSliding.boxMass ℓ d u) hℓ hμ hV hΦ.measurable
    (measurable_boxIndCount ℓ d u) (fun x => boxIndCount_nonneg ℓ d u x)
    (fun x => boxIndCount_le_card ℓ d u x) hC0 hCb

end Work.BoseB1Cube
