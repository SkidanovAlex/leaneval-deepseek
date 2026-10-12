import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.NomDefs
import Submission.Work.BoseFixB1.WB.boxState_sq_bound
import Submission.Work.BoseFixB1.WB.ji_helpers
import Submission.Work.BoseFixB1.WB.psiWeight_le_affine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomBoxInner_le_const`

The `u`-uniform bound on the per-box configuration integral of the `R_Ψ`-weight at the
**nominal (indicator-count)** density (the sharp-count twin of
`Work.BoseFixB1.WB.boxInner_le_const`, whose proof is the template here).

FS's step-4 remainder localises the big box into the sliding family `B(u) = dlBox ℓ d u`; the
per-`u` configuration integral of a box state `Φ` against the weight `F(t(u))`, `F = psiWeight 1 μ`,
is what is bounded here:

  `∃ M ≥ 0, ∀ u, ∫_{abox n ℓ} Φ² · F(n(u)/|B(u)|) ≤ M`,

`M` depending on the state and the parameters but **not** on `u`.

## The mathematics

`F(t) = (t-μ)²/(1+tμ⁻¹) ≤ μ² + μt` for `t ≥ 0` (`Work.BoseFixB1.WB.psiWeight_le_affine`), so the
estimate reduces to a bound on `∫_{abox n ℓ} Φ²·n(u)/|B(u)|`, uniform in `u`.  Bounding `Φ²` by its
supremum `P` over the compact box and peeling one coordinate at a time
(`Work.UBBInputs8.A.integral_abox_comp_apply`) gives

  `∫_{abox n ℓ} n(u) ≤ n (ℓ³)^{n-1} |B(u)|`,

because the indicator `1_{B(u)}` is supported in `acube ℓ`; dividing by `|B(u)| ≥ 0` cancels the
`u`-dependent factor **exactly**, and the degenerate case `|B(u)| = 0` is harmless (`x/0 = 0` in
Lean, and the resulting integrand is `Φ²·F(0) = μ²Φ²`).  Unlike the smooth-count twin, no lower
bound on `|B(u)|` is needed: the cancellation is exact in Lean's division convention.

The helper lemmas `measurable_boxInd'`, `integrableOn_boxInd_acube`, `integral_acube_boxInd`,
`integral_abox_boxInd`, `measurable_psiWeight'`, `measurable_nomCnt'` and `nomBox_integral_le`
are the indicator-count analogues of the pieces of `Submission/Work/BoseFixB1/WB/`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary one-slot facts about the box indicator -/

/-- The box indicator `1_{B(u)}` is Borel measurable (it is the indicator of the closed set
`dlBox ℓ d u`). -/
lemma measurable_boxInd' (ℓ d : ℝ) (u : E3) :
    Measurable (Work.SmallBoxSliding.boxInd ℓ d u) := by
  have hunfold : Work.SmallBoxSliding.boxInd ℓ d u
      = (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) := rfl
  rw [hunfold]
  exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)

/-- The `i`-th coordinate projection on the configuration space is measurable. -/
lemma measurable_eval' {n : ℕ} (i : Fin n) : Measurable (fun x : X n => x i) :=
  measurable_pi_apply i

/-- The box indicator is integrable on the big cube `acube ℓ` (bounded by `1`, finite volume). -/
lemma integrableOn_boxInd_acube {ℓ d : ℝ} (hℓ : 0 ≤ ℓ) (u : E3) :
    IntegrableOn (Work.SmallBoxSliding.boxInd ℓ d u) (Submission.BoseGases.acube ℓ) := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    isFiniteMeasure_restrict.2 (by
      rw [Submission.BoseGases.acube_volume ℓ hℓ]
      exact ENNReal.ofReal_ne_top)
  refine Integrable.of_bound ((measurable_boxInd' ℓ d u).aestronglyMeasurable) 1 ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (boxInd_nonneg' ℓ d u x)]
  exact boxInd_le_one' ℓ d u x

/-- **The `acube ℓ`-integral of the box indicator is the box mass.**  The indicator is supported
in `dlBox ℓ d u ⊆ acube ℓ`, so the cube integral is the full-space integral defining `boxMass`. -/
lemma integral_acube_boxInd {ℓ d : ℝ} (u : E3) :
    (∫ y in Submission.BoseGases.acube ℓ, Work.SmallBoxSliding.boxInd ℓ d u y)
      = Work.SmallBoxSliding.boxMass ℓ d u := by
  have hsupp : ∀ y ∉ Submission.BoseGases.acube ℓ,
      Work.SmallBoxSliding.boxInd ℓ d u y = 0 := by
    intro y hy
    rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem]
    exact fun hmem => hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem)
  rw [Work.SmallBoxSliding.boxMass]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hsupp

/-- **The one-coordinate peel**: the box integral of the `i`-th slot indicator is the mass of the
other `n - 1` slots, `(ℓ³)^{n-1}`, times the box mass `|B(u)|`. -/
lemma integral_abox_boxInd {n : ℕ} {ℓ d : ℝ} (hℓ : 0 ≤ ℓ) (u : E3) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.SmallBoxSliding.boxInd ℓ d u (x i))
      = (ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.UBBInputs8.A.integral_abox_comp_apply hℓ i
      (integrableOn_boxInd_acube (d := d) hℓ u),
    integral_acube_boxInd u]

/-- `psiWeight c μ` is measurable in its last argument. -/
lemma measurable_psiWeight' (c μ : ℝ) : Measurable (Work.SmallBoxSliding.psiWeight c μ) := by
  unfold Work.SmallBoxSliding.psiWeight
  fun_prop

/-- The nominal box count is measurable in the configuration. -/
lemma measurable_nomCnt' (ℓ d : ℝ) (u : E3) {n : ℕ} : Measurable (nomCnt ℓ d u : X n → ℝ) := by
  unfold nomCnt
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_boxInd' ℓ d u).comp (measurable_eval' i))

/-! ## The core `u`-uniform estimate -/

/-- **The core `u`-uniform estimate at the nominal density.**  For a continuous state on the box
whose square is bounded by `P` on the box, the `R_Ψ`-weight integral at the indicator density
`n(u)/|B(u)|` is bounded by `μ²∫Φ² + μ P n ℓ^{3(n-1)}`, uniformly in the small-box centre `u`. -/
theorem nomBox_integral_le {n : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (Φ : X n → ℝ) (hΦ : Continuous Φ) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ x ∈ Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 ≤ P) (u : E3) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      ≤ μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        + μ * P * (n : ℝ) * (ℓ ^ 3) ^ (n - 1) := by
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
  have hΦ2int : IntegrableOn (fun x : X n => (Φ x) ^ 2) (Submission.BoseGases.abox n ℓ) := by
    refine Integrable.of_bound ((hΦ.pow 2).aestronglyMeasurable) P ?_
    rw [ae_restrict_iff' hbmeas]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hP x hx)
  -- integrability of one slot of the count
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
  -- integrability of one slot of `Φ²·count`
  have hint_i : ∀ i : Fin n,
      IntegrableOn (fun x : X n => (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        (Submission.BoseGases.abox n ℓ) := by
    intro i
    refine Integrable.of_bound (((hΦ.pow 2).measurable.mul
      ((measurable_boxInd' ℓ d u).comp (measurable_eval' i))).aestronglyMeasurable) P ?_
    rw [ae_restrict_iff' hbmeas]
    exact Filter.Eventually.of_forall (fun x hx => by
      have hb0 : 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u (x i) := boxInd_nonneg' ℓ d u (x i)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hb0)]
      calc (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
          ≤ P * Work.SmallBoxSliding.boxInd ℓ d u (x i) :=
            mul_le_mul_of_nonneg_right (hP x hx) hb0
        _ ≤ P * 1 := mul_le_mul_of_nonneg_left (boxInd_le_one' ℓ d u (x i)) hP0
        _ = P := mul_one P)
  -- the split of the density into the single-slot indicators
  have hsplit : (fun x : X n => (Φ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      = fun x : X n => ∑ i : Fin n,
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
            / Work.SmallBoxSliding.boxMass ℓ d u := by
    funext x
    rw [nomCnt, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (mul_div_assoc _ _ _).symm)
  -- integrability of the density-weighted `Φ²`
  have hint_t : IntegrableOn (fun x : X n => (Φ x) ^ 2 *
      (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      (Submission.BoseGases.abox n ℓ) := by
    rw [hsplit]
    exact integrable_finsetSum _ (fun i _ =>
      (hint_i i).div_const (Work.SmallBoxSliding.boxMass ℓ d u))
  -- the exact value of the density-weighted integral
  have hint_eq : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        / Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [hsplit, integral_finsetSum _ (fun i _ =>
      (hint_i i).div_const (Work.SmallBoxSliding.boxMass ℓ d u))]
    simp only [integral_div]
    rw [← Finset.sum_div]
  -- the single-slot bound
  have hone : ∀ i : Fin n, (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
      ≤ P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u) := by
    intro i
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        ≤ ∫ x in Submission.BoseGases.abox n ℓ,
            P * Work.SmallBoxSliding.boxInd ℓ d u (x i) := by
          refine integral_mono_ae (hint_i i) ((hbint i).const_mul P) ?_
          have hae : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
              (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i)
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
        (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
      ≤ (n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)) := by
    calc (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
        ≤ ∑ _i : Fin n, P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u) :=
          Finset.sum_le_sum (fun i _ => hone i)
      _ = (n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the conclusion of the cancellation
  have hInt_le : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      ≤ (n : ℝ) * P * (ℓ ^ 3) ^ (n - 1) := by
    rw [hint_eq]
    have h1 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
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
          (Φ x) ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u (x i))
          / Work.SmallBoxSliding.boxMass ℓ d u
        ≤ ((n : ℝ) * (P * ((ℓ ^ 3) ^ (n - 1) * Work.SmallBoxSliding.boxMass ℓ d u)))
            / Work.SmallBoxSliding.boxMass ℓ d u := h1
      _ = ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1))
            * (Work.SmallBoxSliding.boxMass ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) := h2
      _ ≤ ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1)) * 1 :=
          mul_le_mul_of_nonneg_left (div_self_le_one _) hnn
      _ = (n : ℝ) * P * (ℓ ^ 3) ^ (n - 1) := mul_one _
  -- the affine domination of `F`
  have hdom : IntegrableOn (fun x : X n => μ ^ 2 * (Φ x) ^ 2
      + μ * ((Φ x) ^ 2 * (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)))
      (Submission.BoseGases.abox n ℓ) :=
    (hΦ2int.const_mul (μ ^ 2)).add (hint_t.const_mul μ)
  have hpt : ∀ x : X n, (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)
      ≤ μ ^ 2 * (Φ x) ^ 2
        + μ * ((Φ x) ^ 2 * (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)) := by
    intro x
    have ht0 : 0 ≤ nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u :=
      div_nonneg (nomCnt_nonneg ℓ d u x) hs0
    have h1 := Work.BoseFixB1.WB.psiWeight_le_affine (μ := μ)
      (t := nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u) hμ ht0
    calc (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)
        ≤ (Φ x) ^ 2 * (μ ^ 2 + μ * (nomCnt ℓ d u x
            / Work.SmallBoxSliding.boxMass ℓ d u)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = μ ^ 2 * (Φ x) ^ 2
            + μ * ((Φ x) ^ 2 * (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)) := by ring
  have hlhs : IntegrableOn (fun x : X n => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      (Submission.BoseGases.abox n ℓ) := by
    refine Integrable.mono' hdom ?_ ?_
    · refine ((hΦ.pow 2).measurable.mul ?_).aestronglyMeasurable
      exact (measurable_psiWeight' 1 μ).comp ((measurable_nomCnt' ℓ d u).div_const _)
    · rw [ae_restrict_iff' hbmeas]
      exact Filter.Eventually.of_forall (fun x _ => by
        have ht0 : 0 ≤ nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u :=
          div_nonneg (nomCnt_nonneg ℓ d u x) hs0
        have h2 : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ
            (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u) :=
          Work.BoseFixB1.WB.psiWeight_one_nonneg_local hμ ht0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
        exact hpt x)
  calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (μ ^ 2 * (Φ x) ^ 2
          + μ * ((Φ x) ^ 2 * (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))) := by
        refine integral_mono_ae hlhs hdom ?_
        have hae : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
            (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
                (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)
              ≤ μ ^ 2 * (Φ x) ^ 2
                + μ * ((Φ x) ^ 2 * (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)) := by
          rw [ae_restrict_iff' hbmeas]
          exact Filter.Eventually.of_forall (fun x _ => hpt x)
        exact hae
    _ = μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          + μ * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              (nomCnt ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)) := by
        rw [MeasureTheory.integral_add (hΦ2int.const_mul (μ ^ 2)) (hint_t.const_mul μ),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          + μ * ((n : ℝ) * P * (ℓ ^ 3) ^ (n - 1)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hInt_le hμ.le)
    _ = μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          + μ * P * (n : ℝ) * (ℓ ^ 3) ^ (n - 1) := by ring

/-! ## The target -/

theorem nomBoxInner_le_const {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (hμ : 0 < μ) (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseB1Cube.nomBoxInner h μ (Φ : Submission.BoseGases.X n → ℝ) u ≤ M := by
  obtain ⟨P, hP0, hP⟩ := Work.BoseFixB1.WB.boxState_sq_bound Φ
  refine ⟨μ ^ 2 * (∫ x in Submission.BoseGases.abox n
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
      + μ * P * (n : ℝ) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) ^ (n - 1), ?_, ?_⟩
  · have h1 : 0 ≤ ∫ x in Submission.BoseGases.abox n
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : 0 ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) ^ (n - 1) :=
      pow_nonneg (pow_nonneg hℓ.le 3) _
    exact add_nonneg (mul_nonneg (sq_nonneg μ) h1)
      (mul_nonneg (mul_nonneg (mul_nonneg hμ.le hP0) h2) h3)
  · intro u
    exact nomBox_integral_le (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hμ
      (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff.continuous P hP0 hP u

end Work.BoseB1Cube
