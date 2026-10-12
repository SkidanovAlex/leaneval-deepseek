import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.aestronglyMeasurable_nomBoxInner
import Submission.Work.BoseB1Cube.nomBoxInner_le_const
import Submission.Work.BoseFixB1.WB.aestronglyMeasurable_wbMass
import Submission.Work.BoseFixB1.WB.integrableOn_wbMass_interior
import Submission.Work.BoseFixB1S.chiMass_le_const_mul_boxMass
import Submission.Work.SmallBoxSliding.boxMassLeCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.integrableOnWbMassMulNomDens`

`u ↦ wbMass v h μ u · nomDens h μ Φ u` is integrable on the sliding interior `I₋`.

## The mathematics

The nominal density is

    nomDens h μ Φ u = (∫_{abox n ℓ} Φ²·n(u)) / (‖Φ‖²·|B(u)|) ,

`n(u) = Σᵢ1_{B(u)}(xᵢ)` the sharp box count and `|B(u)| = boxMass ℓ d u` the true box
volume.  Two facts make the product integrable:

* **`nomDens` is uniformly bounded in `u`.**  Because `boxMass` is the *sharp* box volume,
  the division by it **cancels exactly** against the box counting measure: with the
  pointwise bound `Φ² ≤ P` on the box and the one-slot peel
  `∫_{abox} Φ²·1_{B(u)}(xᵢ) ≤ P·(ℓ³)^{n-1}·|B(u)|` one gets

      ∫_{abox} Φ²·(n(u)/|B(u)|) ≤ n·P·(ℓ³)^{n-1} .

  No lower bound on `|B(u)|` is needed: the degenerate case `|B(u)| = 0` is harmless in
  Lean's division convention (`x/0 = 0`), and `n(u)/|B(u)| ≤ n` is *false*, so the sharp
  count must be peeled slot by slot (the `hInt_le` computation of `nomBoxInner_le_const`,
  isolated here as `nomCnt_div_boxMass_integral_le`).  This is the *sharp-count* twin of
  `Work.BoseFixB1.WB.integrable_w1MassB_mul_dens`.

* **`wbMass` pays for everything.**  `wbMass` is nonnegative (`wbMass_nonneg`) and integrable
  on `I₋` (`WB.integrableOn_wbMass_interior`), so the constant `K` times `wbMass` dominates
  the product and `Integrable.mono'` finishes.

Note that no `χ_{B(u)}`-mass comparison is used and the hypothesis `hmassU` of the statement
is not needed by this route — the bound is against `wbMass` itself.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The exact cancellation of the box volume

The one-slot peel `∫_{abox} Φ²·1_{B(u)}(xᵢ) ≤ P·(ℓ³)^{n-1}·|B(u)|` (the indicator is
supported in `dlBox ⊆ acube`) is summed over the slots and divided by `|B(u)|`; the ratio
`|B(u)|/|B(u)|` is at most `1` for **every** real `|B(u)|` (`div_self_le_one`), which is why
the degenerate box `|B(u)| = 0` needs no separate treatment. -/

/-- **The sharp-count box-volume cancellation.**  For a continuous state whose square is
bounded by `P` on the box,

    `∫_{abox n ℓ} Φ²·(n(u)/|B(u)|) ≤ n·P·(ℓ³)^{n-1}`,

uniformly in the sliding parameter `u` (and in `d`).  This is the `hInt_le` computation
inside `nomBox_integral_le`, isolated. -/
lemma nomCnt_div_boxMass_integral_le {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (Ψ : X n → ℝ) (hΨ : Continuous Ψ) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ x ∈ Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 ≤ P) (u : E3) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      ≤ (n : ℝ) * P * (ℓ ^ 3) ^ (n - 1) := by
  classical
  have hbmeas : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    isFiniteMeasure_restrict.2 (by
      rw [Submission.BoseGases.abox_volume n ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top)
  have hs0 : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := boxMass_nonneg' ℓ d u
  have hnn : 0 ≤ (n : ℝ) * P * (ℓ ^ 3) ^ (n - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hP0) (pow_nonneg (pow_nonneg hℓ.le 3) _)
  -- integrability of `Φ²`
  have hΨ2int : IntegrableOn (fun x : X n => (Ψ x) ^ 2) (Submission.BoseGases.abox n ℓ) := by
    refine Integrable.of_bound ((hΨ.pow 2).aestronglyMeasurable) P ?_
    rw [ae_restrict_iff' hbmeas]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hP x hx)
  -- integrability of one slot of the indicator
  have hbint : ∀ i : Fin n,
      IntegrableOn (fun x : X n => Work.SmallBoxSliding.boxInd ℓ d u (x i))
        (Submission.BoseGases.abox n ℓ) := by
    intro i
    refine Integrable.of_bound
      (((measurable_boxInd' ℓ d u).comp (measurable_eval' i)).aestronglyMeasurable) 1 ?_
    rw [ae_restrict_iff' hbmeas]
    exact Filter.Eventually.of_forall (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (boxInd_nonneg' ℓ d u (x i))]
      exact boxInd_le_one' ℓ d u (x i))
  -- integrability of one slot of `Φ²·indicator`
  have hint_i : ∀ i : Fin n,
      IntegrableOn (fun x : X n => (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        (Submission.BoseGases.abox n ℓ) := by
    intro i
    refine Integrable.of_bound (((hΨ.pow 2).measurable.mul
      ((measurable_boxInd' ℓ d u).comp (measurable_eval' i))).aestronglyMeasurable) P ?_
    rw [ae_restrict_iff' hbmeas]
    exact Filter.Eventually.of_forall (fun x hx => by
      have hb0 : 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u (x i) := boxInd_nonneg' ℓ d u (x i)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hb0)]
      calc (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
          ≤ P * Work.SmallBoxSliding.boxInd ℓ d u (x i) :=
            mul_le_mul_of_nonneg_right (hP x hx) hb0
        _ ≤ P * 1 := mul_le_mul_of_nonneg_left (boxInd_le_one' ℓ d u (x i)) hP0
        _ = P := mul_one P)
  -- the split of the density into the single-slot indicators
  have hsplit : (fun x : X n => (Ψ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      = fun x : X n => ∑ i : Fin n,
          (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
            / Work.SmallBoxSliding.boxMass ℓ d u := by
    funext x
    rw [nomCnt, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (mul_div_assoc _ _ _).symm)
  -- integrability of the density-weighted `Φ²`
  have hint_t : IntegrableOn (fun x : X n => (Ψ x) ^ 2 *
      (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      (Submission.BoseGases.abox n ℓ) := by
    rw [hsplit]
    exact integrable_finsetSum _ (fun i _ =>
      (hint_i i).div_const (Work.SmallBoxSliding.boxMass ℓ d u))
  -- the exact value of the density-weighted integral
  have hint_eq : (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        / Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [hsplit, integral_finsetSum _ (fun i _ =>
      (hint_i i).div_const (Work.SmallBoxSliding.boxMass ℓ d u))]
    simp only [integral_div]
    rw [← Finset.sum_div]
  -- the single-slot bound
  have hone : ∀ i : Fin n, (∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
      ≤ P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u) := by
    intro i
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        ≤ ∫ x in Submission.BoseGases.abox n ℓ,
            P * Work.SmallBoxSliding.boxInd ℓ d u (x i) := by
          refine integral_mono_ae (hint_i i) ((hbint i).const_mul P) ?_
          have hae : ∀ᵐ x ∂(volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ),
              (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
                ≤ P * Work.SmallBoxSliding.boxInd ℓ d u (x i) := by
            rw [ae_restrict_iff' hbmeas]
            exact Filter.Eventually.of_forall (fun x hx =>
              mul_le_mul_of_nonneg_right (hP x hx) (boxInd_nonneg' ℓ d u (x i)))
          exact hae
      _ = P * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.SmallBoxSliding.boxInd ℓ d u (x i)) := by
          rw [MeasureTheory.integral_const_mul]
      _ = P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u) := by
          rw [integral_abox_boxInd hℓ.le u i]
  -- the sum bound
  have hsum_le : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
      ≤ (n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)) := by
    calc (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        ≤ ∑ _i : Fin n, P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u) :=
          Finset.sum_le_sum (fun i _ => hone i)
      _ = (n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the conclusion of the cancellation
  rw [hint_eq]
  have h1 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        / Work.SmallBoxSliding.boxMass ℓ d u
      ≤ ((n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)))
        / Work.SmallBoxSliding.boxMass ℓ d u :=
    div_le_div_of_nonneg_right hsum_le hs0
  have h2 : ((n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)))
        / Work.SmallBoxSliding.boxMass ℓ d u
      = ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1))
        * (Work.SmallBoxSliding.boxMass ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) := by
    rw [show (n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u))
          = ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1)) * Work.SmallBoxSliding.boxMass ℓ d u by ring,
      mul_div_assoc]
  calc (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        / Work.SmallBoxSliding.boxMass ℓ d u
      ≤ ((n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)))
          / Work.SmallBoxSliding.boxMass ℓ d u := h1
    _ = ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1))
          * (Work.SmallBoxSliding.boxMass ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) := h2
    _ ≤ ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1)) * 1 :=
        mul_le_mul_of_nonneg_left (div_self_le_one _) hnn
    _ = (n : ℝ) * P * (ℓ ^ 3) ^ (n - 1) := mul_one _

/-! ## 2. `nomDens` in the "cancelled" form -/

/-- **The nominal density as one integral divided by the norm.**  The box-volume division
inside the integral and the division by `‖Φ‖²` factor out exactly:
`(∫Φ²·n)/(‖Φ‖²·|B|) = (∫Φ²·(n/|B|))/‖Φ‖²`.  Valid for every real `|B|`
(Lean's `x/0 = 0` makes the degenerate case true as well). -/
lemma nomDens_eq_aux {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Ψ : X n → ℝ) (u : E3) :
    nomDens h μ Ψ u
      = (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Ψ x) ^ 2 * (nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
            / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
        / Work.BoseBoxFix.normB v μ n Ψ := by
  rw [nomDens, div_mul_eq_div_div_swap]
  congr 1
  rw [← MeasureTheory.integral_div]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun x => mul_div_assoc _ _ _))

/-! ## 3. The uniform bound on the nominal density -/

/-- **`nomDens` is bounded uniformly in the sliding parameter.**  With `Φ² ≤ P` on the box
and `‖Φ‖² > 0`,

    `nomDens h μ Φ u ≤ n·P·(ℓ³)^{n-1} / ‖Φ‖²`  for every `u`. -/
lemma nomDens_le_const {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : X n → ℝ) x) ^ 2 ≤ P)
    (hN : 0 < Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) (u : E3) :
    nomDens h μ (Φ : X n → ℝ) u
      ≤ ((n : ℝ) * P * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) ^ (n - 1))
        / Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
  rw [nomDens_eq_aux h μ (Φ : X n → ℝ) u]
  exact div_le_div_of_nonneg_right
    (nomCnt_div_boxMass_integral_le hℓ (Φ : X n → ℝ) Φ.contDiff.continuous P hP0 hP u) hN.le

/-! ## 4. Measurability of the nominal density -/

/-- **`u ↦ nomDens h μ Φ u` is a.e. strongly measurable.**  The numerator is the `u`-section
integral of the jointly measurable integrand `(u,x) ↦ Φ(x)²·n(u)`, the denominator is the
product of the constant `‖Φ‖²` with the measurable box volume.  This is the sharp-count twin
of `Work.BoseFixB1.WB.wbDens_aeStronglyMeasurable_gen`. -/
theorem aestronglyMeasurable_nomDens {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : E3 => nomDens h μ (Φ : X n → ℝ) u) (volume : Measure E3) := by
  have hjoint : Measurable (fun p : E3 × X n => ((Φ : X n → ℝ) p.2) ^ 2 *
      nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2) :=
    (((Φ.contDiff.continuous.measurable).comp measurable_snd).pow_const 2).mul
      (measurable_nomCnt_joint _ _ n)
  have hAESM : MeasureTheory.AEStronglyMeasurable (fun p : E3 × X n =>
        ((Φ : X n → ℝ) p.2) ^ 2 *
          nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2)
      ((volume : Measure E3).prod
        ((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    hjoint.aemeasurable.aestronglyMeasurable
  have hnum : MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : X n → ℝ) x) ^ 2 *
          nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x) (volume : Measure E3) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hAESM
  have hden : Measurable (fun u : E3 => Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) *
      Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    measurable_const.mul (measurable_boxMass_cube _ _)
  exact (hnum.aemeasurable.div hden.aemeasurable).aestronglyMeasurable

/-! ## 5. The target -/

theorem integrableOnWbMassMulNomDens {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :
    MeasureTheory.IntegrableOn
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.wbMass v h μ u
        * Work.BoseB1Cube.nomDens h μ (Φ : Submission.BoseGases.X n → ℝ) u)
      (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)
      MeasureTheory.volume := by
  obtain ⟨P, hP0, hP⟩ := Work.BoseFixB1.WB.boxState_sq_bound Φ
  -- the uniform bound on the density
  set K : ℝ := ((n : ℝ) * P * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) ^ (n - 1))
      / Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hKdef
  have hKnn : 0 ≤ K :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hP0)
      (pow_nonneg (pow_nonneg hℓ.le 3) _)) hN.le
  have hdens_le : ∀ u : E3, nomDens h μ (Φ : X n → ℝ) u ≤ K := by
    intro u
    rw [hKdef]
    exact nomDens_le_const hℓ Φ P hP0 hP hN u
  have hdens_nn : ∀ u : E3, 0 ≤ nomDens h μ (Φ : X n → ℝ) u :=
    fun u => nomDens_nonneg (Φ : X n → ℝ) u
  have hwb_nn : ∀ u : E3, 0 ≤ Work.BoseFixB1.wbMass v h μ u :=
    fun u => Work.BoseFixB1.wbMass_nonneg (h := h) hv hvrad hv_supp hR hM hℓ hd u
  -- the integrable majorant `K · wbMass`, and measurability
  have hIntOn : MeasureTheory.IntegrableOn (fun u : E3 => Work.BoseFixB1.wbMass v h μ u)
      (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    Work.BoseFixB1.WB.integrableOn_wbMass_interior (h := h) hv hvrad hv_supp hR hμ hav hM hℓ hd
  have haesm : MeasureTheory.AEStronglyMeasurable (fun u : E3 => Work.BoseFixB1.wbMass v h μ u
      * nomDens h μ (Φ : X n → ℝ) u)
      ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)) :=
    ((Work.BoseFixB1.WB.aestronglyMeasurable_wbMass (v := v) (h := h) (μ := μ)).mul
      (aestronglyMeasurable_nomDens Φ)).restrict
  exact MeasureTheory.Integrable.mono' (hIntOn.const_mul K) haesm (by
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwb_nn u) (hdens_nn u))]
    calc Work.BoseFixB1.wbMass v h μ u * nomDens h μ (Φ : X n → ℝ) u
        ≤ Work.BoseFixB1.wbMass v h μ u * K :=
          mul_le_mul_of_nonneg_left (hdens_le u) (hwb_nn u)
      _ = K * Work.BoseFixB1.wbMass v h μ u := by ring)

end Work.BoseB1Cube
