import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WB.Lead
import Submission.Work.BoseFixB1.WB.cs_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.cs_apply`

FS step 4 of `thm:aprioriHLambda`: the Cauchy–Schwarz particle window applied to the
state-averaged density `t = wbDens` and the localised one-body mass `g = wbMass`.

The mathematical content is the weighted Cauchy–Schwarz inequality
(`WB.cs_weight`) for the split

  `(t − μ)·g = [(t − μ)/√(1 + t/μ)]·[√(1 + t/μ)]·g`,

together with the two integral identities

  `wbSig − μ·wbW = ∫_{I₋} (t − μ)·g`,   `wbW + wbSig/μ = ∫_{I₋} (1 + t/μ)·g`

(which follow from `wbSig = ∫ t·g`, `wbW = ∫ g` by linearity of the integral: hence they
need the *integrability* of `g` and of `t·g` on `I₋`).

The integrability inputs are supplied by the hypothesis `hmassU` (the localised mass is
dominated by a multiple of the cutoff mass, which is integrable —
`SmallBoxSliding.integrable_chiSmallB_mass`) and by the pointwise bound
`t = (∫ Φ²·nCountB)/(‖Φ‖²·χ) ≤ n·C²` on the numerator; together these bound `g` by an
integrable multiple of `χ` and `g·t` by a constant, supported off the ball in which the
small box misses the big box.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Elementary pointwise bounds -/

/-- `ψ_μ(t) = (t−μ)²/(1+t/μ) ≥ 0` for `t ≥ 0`, `μ > 0`. -/
lemma psiWeight_one_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  refine div_nonneg (sq_nonneg _) ?_
  have h : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
  linarith

/-- `ψ_μ(t) = (t−μ)²/(1+t/μ) ≤ μ² + μ·t` for `t ≥ 0`, `μ > 0`. -/
lemma psiWeight_one_le {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    psiWeight 1 μ t ≤ μ ^ 2 + μ * t := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hpos : 0 < 1 + t * μ⁻¹ := by
    have h : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
    linarith
  rw [div_le_iff₀ hpos]
  have hkey : (μ ^ 2 + μ * t) * (1 + t * μ⁻¹) = (t + μ) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  nlinarith [mul_nonneg hμ.le ht]

/-- `t ↦ ψ_μ(t)` is measurable (a quotient of measurable functions).
(Uniquely named: `WB/boxInner_le_const` declares the same fact under a name that
is visible in `WB/`'s common import closure, and both modules are imported by
`windowBridge_holds`.) -/
lemma measurable_psiWeight_cs (c μ : ℝ) :
    Measurable (fun t : ℝ => psiWeight c μ t) := by
  unfold Work.SmallBoxSliding.psiWeight
  exact (measurable_const.mul (((continuous_id.sub continuous_const).pow 2).measurable)).div
    (measurable_const.add (measurable_id.mul measurable_const))

/-- `‖Φ‖² ≥ 0`. -/
lemma sqNormB_nonneg (n : ℕ) (ℓ : ℝ) (Φ : X n → ℝ) :
    0 ≤ Work.BoseKinLoc.sqNormB n ℓ Φ := by
  rw [Work.BoseKinLoc.sqNormB]
  exact integral_nonneg (fun x => sq_nonneg _)

/-! ## 1b. Measurability of the two state-dependent weights -/

/-- `y ↦ x - y` preserves Lebesgue measure on `ℝ³`. -/
lemma measurePreserving_sub_left_local (x : ℝ³) :
    MeasurePreserving (fun y : ℝ³ => x - y) (volume : Measure ℝ³) volume := by
  have h1 : MeasurePreserving (fun z : ℝ³ => -z) (volume : Measure ℝ³) volume :=
    Measure.measurePreserving_neg volume
  have h2 : MeasurePreserving (fun z : ℝ³ => x + z) (volume : Measure ℝ³) volume :=
    measurePreserving_add_left volume x
  have h3 : (fun y : ℝ³ => x - y) = (fun z : ℝ³ => x + z) ∘ (fun z : ℝ³ => -z) := by
    funext y; simp [sub_eq_add_neg]
  rw [h3]
  exact h2.comp h1

/-- Slice form of the a.e. lifting under `y ↦ x - y`. -/
lemma ae_eq_comp_sub_left_slice {h g : ℝ³ → ℝ} (hg : h =ᵐ[volume] g) (x : ℝ³) :
    (fun y : ℝ³ => h (x - y)) =ᵐ[volume] fun y : ℝ³ => g (x - y) :=
  (measurePreserving_sub_left_local x).quasiMeasurePreserving.ae_eq_comp hg

/-- Joint continuity of the two-factor cutoff in `(u,x)`. -/
lemma continuous_chiSmallB_pair_cs {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
  have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
    (chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    (chiSmall_continuous hM).comp ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
      = fun p => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
  rw [heq]
  exact h1.mul h2

/-- **Measurability of the localised one-body mass** `u ↦ ∬ w_{1,B(u)}`.

The numerator `g₀ = v(1−w₀)` is only *a.e.* measurable (obtained here from
`g0_integrable`), so the proof replaces it by its strongly measurable
representative `g'`; the two iterated integrals agree pointwise because for fixed
`x` the two kernels agree for a.e. `y` (`y ↦ x - y` preserves Lebesgue measure). -/
theorem w1MassB_aeStronglyMeasurable_local {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    (M : ℕ) (hM : 1 ≤ M) (ℓ d : ℝ) :
    AEStronglyMeasurable (fun u : ℝ³ => Work.BoseFixB1.w1MassB h M ℓ d u) volume := by
  have hg0int : Integrable (g0 v h) volume := Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hh : AEStronglyMeasurable (g0 v h) volume := hg0int.aestronglyMeasurable
  set g' : ℝ³ → ℝ := AEStronglyMeasurable.mk (g0 v h) hh with hg'def
  have hg'm : Measurable g' := hh.stronglyMeasurable_mk.measurable
  have hg'eq : g' =ᵐ[volume] g0 v h := hh.ae_eq_mk.symm
  have hjoint : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => wSmallPair M ℓ d p.1.1 g' p.1.2 p.2) := by
    have hXB : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.1.2) := by
      have hcont : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.1.2) := by
        have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => chiScale ℓ p.1.2) :=
          (chiScale_continuous ℓ).comp (continuous_snd.comp continuous_fst)
        have h2 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
            chiSmall M ((ℓ * d)⁻¹ • p.1.2 - p.1.1)) :=
          (chiSmall_continuous hM).comp
            (((continuous_snd.comp continuous_fst).const_smul ((ℓ * d)⁻¹)).sub
              (continuous_fst.comp continuous_fst))
        have heq : (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.1.2)
            = fun p => chiScale ℓ p.1.2 * chiSmall M ((ℓ * d)⁻¹ • p.1.2 - p.1.1) := rfl
        rw [heq]
        exact h1.mul h2
      exact hcont.measurable
    have hYB : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.2) := by
      have hcont : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.2) := by
        have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => chiScale ℓ p.2) :=
          (chiScale_continuous ℓ).comp continuous_snd
        have h2 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
            chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1.1)) :=
          (chiSmall_continuous hM).comp
            ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub (continuous_fst.comp continuous_fst))
        have heq : (fun p : (ℝ³ × ℝ³) × ℝ³ => chiSmallB M ℓ d p.1.1 p.2)
            = fun p => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1.1) := rfl
        rw [heq]
        exact h1.mul h2
      exact hcont.measurable
    have hz : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => p.1.2 - p.2) :=
      (continuous_snd.comp continuous_fst).sub continuous_snd
    have hnum : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => g' (p.1.2 - p.2)) :=
      hg'm.comp hz.measurable
    have hden1 : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => convScaleSmall M (ℓ * d) (p.1.2 - p.2)) :=
      (((conv3Small_continuous hM).comp
        (continuous_id.const_smul ((ℓ * d)⁻¹))).comp hz).measurable
    have hscaled : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        wSmallScaled M (ℓ * d) g' (p.1.2 - p.2)) := by
      have heq : (fun p : (ℝ³ × ℝ³) × ℝ³ => wSmallScaled M (ℓ * d) g' (p.1.2 - p.2))
          = fun p => g' (p.1.2 - p.2) / convScaleSmall M (ℓ * d) (p.1.2 - p.2) := rfl
      rw [heq]
      exact hnum.div hden1
    have hden2 : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => convScale ℓ (p.1.2 - p.2)) :=
      ((convScale_continuous ℓ).comp hz).measurable
    have heq : (fun p : (ℝ³ × ℝ³) × ℝ³ => wSmallPair M ℓ d p.1.1 g' p.1.2 p.2)
        = fun p => chiSmallB M ℓ d p.1.1 p.1.2 *
            (wSmallScaled M (ℓ * d) g' (p.1.2 - p.2) / convScale ℓ (p.1.2 - p.2)) *
            chiSmallB M ℓ d p.1.1 p.2 := rfl
    rw [heq]
    exact (hXB.mul (hscaled.div hden2)).mul hYB
  have hstep1 : StronglyMeasurable (fun q : ℝ³ × ℝ³ => ∫ y : ℝ³, wSmallPair M ℓ d q.1 g' q.2 y) :=
    StronglyMeasurable.integral_prod_right
      (f := fun (q : ℝ³ × ℝ³) (y : ℝ³) => wSmallPair M ℓ d q.1 g' q.2 y)
      ((stronglyMeasurable_iff_measurable).mpr hjoint)
  have hstep2 : StronglyMeasurable
      (fun u : ℝ³ => ∫ x : ℝ³, ∫ y : ℝ³, wSmallPair M ℓ d u g' x y) := by
    refine StronglyMeasurable.integral_prod_right
      (f := fun (u : ℝ³) (x : ℝ³) => ∫ y : ℝ³, wSmallPair M ℓ d u g' x y) ?_
    exact hstep1
  have heq : (fun u : ℝ³ => ∫ x : ℝ³, ∫ y : ℝ³, wSmallPair M ℓ d u (g0 v h) x y)
      = fun u : ℝ³ => ∫ x : ℝ³, ∫ y : ℝ³, wSmallPair M ℓ d u g' x y := by
    funext u
    refine integral_congr_ae ?_
    filter_upwards with x
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_sub_left_local x).quasiMeasurePreserving.ae_eq_comp hg'eq]
      with y hy
    have hy' : g' (x - y) = g0 v h (x - y) := hy
    simp only [wSmallPair, wSmallScaled, hy']
  have hgoal : AEStronglyMeasurable
      (fun u : ℝ³ => ∫ x : ℝ³, ∫ y : ℝ³, wSmallPair M ℓ d u (g0 v h) x y) volume :=
    hstep2.aestronglyMeasurable.congr (Eventually.of_forall (fun u => (congrFun heq u).symm))
  simpa only [Work.BoseFixB1.w1MassB, wSmall1Pair] using hgoal

/-- **Measurability of the averaged local density** `u ↦ wbDens u` (generic form). -/
theorem wbDens_aeStronglyMeasurable_gen {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    {Φ : X n → ℝ} {M : ℕ} {ℓ d : ℝ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun u : ℝ³ =>
      (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
        / (normB v μ n Φ * chiMass M ℓ d u)) volume := by
  have hjoint : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) :=
    continuous_chiSmallB_pair_cs hM ℓ d
  have hchi : StronglyMeasurable (fun u : ℝ³ => chiMass M ℓ d u) := by
    have hsm : StronglyMeasurable (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) :=
      StronglyMeasurable.integral_prod_right
        (f := fun (u : ℝ³) (x : ℝ³) => (chiSmallB M ℓ d u x) ^ 2)
        (by
          show StronglyMeasurable (fun p : ℝ³ × ℝ³ => (chiSmallB M ℓ d p.1 p.2) ^ 2)
          exact ((hjoint.pow 2).measurable).stronglyMeasurable)
    simpa only [chiMass] using hsm
  have hcount : Measurable (fun p : ℝ³ × X n => nCountB M ℓ d p.1 p.2) := by
    have heq : (fun p : ℝ³ × X n => nCountB M ℓ d p.1 p.2)
        = fun p => ∑ i : Fin n, (chiSmallB M ℓ d p.1 (p.2 i)) ^ 2 := rfl
    rw [heq]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have hx : Continuous (fun p : ℝ³ × X n => p.2 i) := (continuous_apply i).comp continuous_snd
    have h1 : Continuous (fun p : ℝ³ × X n => chiScale ℓ (p.2 i)) :=
      (chiScale_continuous ℓ).comp hx
    have h2 : Continuous (fun p : ℝ³ × X n =>
        chiSmall M ((ℓ * d)⁻¹ • (p.2 i) - p.1)) :=
      (chiSmall_continuous hM).comp ((hx.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
    have hsq : Continuous (fun p : ℝ³ × X n =>
        (chiSmallB M ℓ d p.1 (p.2 i)) ^ 2) := by
      have heq2 : (fun p : ℝ³ × X n => (chiSmallB M ℓ d p.1 (p.2 i)) ^ 2)
          = fun p => (chiScale ℓ (p.2 i) * chiSmall M ((ℓ * d)⁻¹ • (p.2 i) - p.1)) ^ 2 := rfl
      rw [heq2]
      exact (h1.mul h2).pow 2
    exact hsq.measurable
  have hprod : Measurable (fun p : ℝ³ × X n =>
      (Φ p.2) ^ 2 * nCountB M ℓ d p.1 p.2) :=
    ((hΦ.pow 2).measurable.comp measurable_snd).mul hcount
  have hnum : StronglyMeasurable (fun u : ℝ³ =>
      ∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x) :=
    StronglyMeasurable.integral_prod_right
      (f := fun (u : ℝ³) (x : X n) => (Φ x) ^ 2 * nCountB M ℓ d u x)
      (by
        show StronglyMeasurable (fun p : ℝ³ × X n => (Φ p.2) ^ 2 * nCountB M ℓ d p.1 p.2)
        exact hprod.stronglyMeasurable)
  exact (hnum.measurable.div (measurable_const.mul hchi.measurable)).aestronglyMeasurable

/-- The per-configuration cutoff-count is bounded by `n·C²`,
`C = chiSupAbs·chiSmallDecay M`. -/
lemma nCountB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : ℝ³) {n : ℕ} (x : X n) :
    nCountB M ℓ d u x ≤ (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 := by
  have hterm : ∀ i : Fin n, (chiSmallB M ℓ d u (x i)) ^ 2 ≤ (chiSupAbs * chiSmallDecay M) ^ 2 := by
    intro i
    have h1 : |chiSmallB M ℓ d u (x i)| ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • (x i) - u) :=
      Work.SmallBoxSliding.abs_chiSmallB_le hM u (x i)
    have h2 : chiSmall M ((ℓ * d)⁻¹ • (x i) - u) ≤ chiSmallDecay M := by
      have h := chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • (x i) - u)
      rwa [abs_of_nonneg (chiSmall_nonneg M _)] at h
    have h3 : |chiSmallB M ℓ d u (x i)| ≤ chiSupAbs * chiSmallDecay M :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 chiSupAbs_nonneg)
    have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    simpa only [sq_abs] using h4
  calc nCountB M ℓ d u x = ∑ i : Fin n, (chiSmallB M ℓ d u (x i)) ^ 2 := rfl
    _ ≤ ∑ _i : Fin n, (chiSupAbs * chiSmallDecay M) ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The configurational bound: `∫_{abox} Φ²·nCountB ≤ n·C²·‖Φ‖²`. -/
lemma integral_PhiSq_nCountB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hΦint : Integrable (fun x => (Φ x) ^ 2) (volume.restrict (abox n ℓ))) (u : ℝ³) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 * Work.BoseKinLoc.sqNormB n ℓ Φ := by
  have hdom : Integrable (fun x => ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) * (Φ x) ^ 2)
      (volume.restrict (abox n ℓ)) := hΦint.const_mul _
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) * (Φ x) ^ 2 := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (nCountB_nonneg _ _ _ _ x)))
      hdom (Eventually.of_forall (fun x => ?_))
    calc (Φ x) ^ 2 * nCountB M ℓ d u x
        ≤ (Φ x) ^ 2 * ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) :=
          mul_le_mul_of_nonneg_left (nCountB_le hM u x) (sq_nonneg _)
      _ = ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) * (Φ x) ^ 2 := by ring
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) * (Φ x) ^ 2 := hmono
    _ = ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) * (∫ x in abox n ℓ, (Φ x) ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ = (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 * Work.BoseKinLoc.sqNormB n ℓ Φ := by
        rw [Work.BoseKinLoc.sqNormB]

/-! ## 2. The weighted pointwise bound on `wbMass · wbDens` -/

/-- **The weighted product bound.**  Combining the domination `wMass ≤ C₁·a·χ` with the
configurational bound `∫Φ²nCountB ≤ nC²‖Φ‖²` gives the uniform bound
`wMass·dens ≤ max(C₁a)0·nC²`. -/
lemma w1MassB_mul_dens_le {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {n : ℕ} {M : ℕ} {ℓ d C₁ : ℝ}
    (hM : 1 ≤ M) (hC₁ : 0 < C₁)
    (hmassU : ∀ u : ℝ³, w1MassB h M ℓ d u ≤ C₁ * _root_.BoseGases.a v * chiMass M ℓ d u)
    {Φ : X n → ℝ} (hN : 0 < Work.BoseKinLoc.sqNormB n ℓ Φ) (u : ℝ³) :
    w1MassB h M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))
      ≤ max (C₁ * _root_.BoseGases.a v) 0 * ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) := by
  have hχnn : 0 ≤ chiMass M ℓ d u := chiMass_nonneg M ℓ d u
  have hNunn : 0 ≤ ∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (nCountB_nonneg _ _ _ _ x))
  have hΦint : Integrable (fun x => (Φ x) ^ 2) (volume.restrict (abox n ℓ)) := by
    by_contra hcon
    have hz : Work.BoseKinLoc.sqNormB n ℓ Φ = 0 := by
      rw [Work.BoseKinLoc.sqNormB]
      exact integral_undef hcon
    rw [hz] at hN
    exact lt_irrefl _ hN
  have hNub : (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 * Work.BoseKinLoc.sqNormB n ℓ Φ :=
    integral_PhiSq_nCountB_le hM hΦint u
  have hstep : w1MassB h M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))
      ≤ (C₁ * _root_.BoseGases.a v * chiMass M ℓ d u)
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u)) :=
    mul_le_mul_of_nonneg_right (hmassU u)
      (div_nonneg hNunn (mul_nonneg (sqNormB_nonneg n ℓ Φ) hχnn))
  rcases eq_or_ne (chiMass M ℓ d u) 0 with hχ0 | hχne
  · rw [hχ0] at hstep ⊢
    refine le_trans hstep ?_
    have hz : (C₁ * _root_.BoseGases.a v * 0)
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * 0)) = 0 := by ring
    rw [hz]
    exact mul_nonneg (le_max_right _ _)
      (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
  · have hkey : chiMass M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))
        = (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
          / Work.BoseKinLoc.sqNormB n ℓ Φ := by
      field_simp
      try ring
    have h1 : (C₁ * _root_.BoseGases.a v * chiMass M ℓ d u)
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))
        = (C₁ * _root_.BoseGases.a v)
          * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
              / Work.BoseKinLoc.sqNormB n ℓ Φ) := by
      rw [← hkey]; ring
    have h2 : (C₁ * _root_.BoseGases.a v)
          * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
              / Work.BoseKinLoc.sqNormB n ℓ Φ)
        ≤ max (C₁ * _root_.BoseGases.a v) 0
          * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
              / Work.BoseKinLoc.sqNormB n ℓ Φ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (div_nonneg hNunn (sqNormB_nonneg n ℓ Φ))
    have h3 : (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
          / Work.BoseKinLoc.sqNormB n ℓ Φ
        ≤ (n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2 := by
      rw [div_le_iff₀ hN]
      exact hNub
    have h4 : max (C₁ * _root_.BoseGases.a v) 0
          * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
              / Work.BoseKinLoc.sqNormB n ℓ Φ)
        ≤ max (C₁ * _root_.BoseGases.a v) 0
          * ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    exact le_trans hstep (le_trans (le_of_eq h1) (le_trans h2 h4))

/-! ## 3. Integrability of the localised mass and of the density-weighted mass -/

/-- **Integrability of the localised one-body mass**, from its domination by the
integrable cutoff mass. -/
lemma integrable_w1MassB {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {ℓ d C₁ : ℝ}
    (haesm : AEStronglyMeasurable (fun u : ℝ³ => w1MassB h M ℓ d u) volume)
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hmassL : ∀ u : ℝ³, 0 ≤ w1MassB h M ℓ d u)
    (hmassU : ∀ u : ℝ³, w1MassB h M ℓ d u ≤ C₁ * _root_.BoseGases.a v * chiMass M ℓ d u) :
    Integrable (fun u : ℝ³ => w1MassB h M ℓ d u) volume := by
  have hchi : Integrable (fun u : ℝ³ => chiMass M ℓ d u) volume := by
    simpa only [chiMass] using Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd
  refine Integrable.mono' (hchi.const_mul (max (C₁ * _root_.BoseGases.a v) 0)) haesm ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (hmassL u)]
  calc w1MassB h M ℓ d u ≤ C₁ * _root_.BoseGases.a v * chiMass M ℓ d u := hmassU u
    _ ≤ max (C₁ * _root_.BoseGases.a v) 0 * chiMass M ℓ d u :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (chiMass_nonneg M ℓ d u)

/-- **Integrability of `wbMass · wbDens`**: the product is bounded by the constant
`max(C₁a)0·nC²` and vanishes off the ball in which the small box meets the big box. -/
lemma integrable_w1MassB_mul_dens {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {n : ℕ}
    {M : ℕ} {ℓ d C₁ : ℝ} {Φ : X n → ℝ}
    (haesm : AEStronglyMeasurable (fun u : ℝ³ => w1MassB h M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))) volume)
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hC₁ : 0 < C₁)
    (hmassL : ∀ u : ℝ³, 0 ≤ w1MassB h M ℓ d u)
    (hmassU : ∀ u : ℝ³, w1MassB h M ℓ d u ≤ C₁ * _root_.BoseGases.a v * chiMass M ℓ d u)
    (hN : 0 < Work.BoseKinLoc.sqNormB n ℓ Φ) :
    Integrable (fun u : ℝ³ => w1MassB h M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u))) volume := by
  have hK0 : 0 ≤ max (C₁ * _root_.BoseGases.a v) 0
      * ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2) :=
    mul_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
  have hfin : (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³)
      (Real.sqrt 3 * (ℓ / 2 + ℓ * d / 2) / (ℓ * d))) ≠ ⊤ :=
    ne_of_lt (isCompact_closedBall (0 : ℝ³) _).measure_lt_top
  have hDint : Integrable (fun u : ℝ³ => (max (C₁ * _root_.BoseGases.a v) 0
      * ((n : ℝ) * (chiSupAbs * chiSmallDecay M) ^ 2))
        * (Metric.closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2 + ℓ * d / 2) / (ℓ * d))).indicator
            (fun _ => (1 : ℝ)) u) volume :=
    (((integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const hfin))).const_mul _
  refine Integrable.mono' hDint haesm ?_
  filter_upwards with u
  by_cases hu : ‖u‖ ≤ Real.sqrt 3 * (ℓ / 2 + ℓ * d / 2) / (ℓ * d)
  · have hmem : u ∈ Metric.closedBall (0 : ℝ³)
        (Real.sqrt 3 * (ℓ / 2 + ℓ * d / 2) / (ℓ * d)) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hu
    have hprod0 : 0 ≤ w1MassB h M ℓ d u
        * ((∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
            / (Work.BoseKinLoc.sqNormB n ℓ Φ * chiMass M ℓ d u)) :=
      mul_nonneg (hmassL u) (div_nonneg
        (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (nCountB_nonneg _ _ _ _ x)))
        (mul_nonneg (sqNormB_nonneg n ℓ Φ) (chiMass_nonneg M ℓ d u)))
    rw [Real.norm_eq_abs, abs_of_nonneg hprod0, Set.indicator_of_mem hmem, mul_one]
    exact w1MassB_mul_dens_le hM hC₁ hmassU hN u
  · push_neg at hu
    have hχ0 : chiMass M ℓ d u = 0 := by
      by_contra hne
      exact absurd (Work.SmallBoxSliding.norm_le_of_integral_chiSmallB_sq_ne_zero hM hℓ hd
        (by simpa only [chiMass] using hne)) (not_le.mpr hu)
    have hg0 : w1MassB h M ℓ d u = 0 := wbMass_eq_zero_of_chiMass_eq_zero hM hℓ hd hχ0
    rw [hg0, zero_mul, norm_zero]
    exact mul_nonneg hK0 (Set.indicator_nonneg (fun _ _ => zero_le_one) u)

/-! ## 4. The general Cauchy–Schwarz window -/

/-- **The Cauchy–Schwarz window, abstract form.**  Given the two mass identities
`W = ∫_G g`, `Sig = ∫_G g·t` and the integrability of `g`, `g·t` and `g·ψ_μ(t)` on `G`,
with `t, g ≥ 0` on `G` and `μ > 0`,

  `|Sig − μ·W| ≤ √(∫_G g·ψ_μ(t)) · √(W + Sig/μ)`.

This is `cs_weight` after the two linearity identities
`Sig − μW = ∫_G (t−μ)g` and `W + Sig/μ = ∫_G (1 + t/μ)g`. -/
theorem cs_window_general {G : Set ℝ³} {t g : ℝ³ → ℝ} {μ W Sig : ℝ}
    (hμ : 0 < μ) (hmeas : MeasurableSet G)
    (ht : ∀ u ∈ G, 0 ≤ t u) (hg : ∀ u ∈ G, 0 ≤ g u)
    (hW : W = ∫ u in G, g u) (hSig : Sig = ∫ u in G, g u * t u)
    (hIg : IntegrableOn g G) (hIgt : IntegrableOn (fun u => g u * t u) G)
    (hIpsi : IntegrableOn (fun u => g u * psiWeight 1 μ (t u)) G) :
    |Sig - μ * W|
      ≤ Real.sqrt (∫ u in G, g u * psiWeight 1 μ (t u)) * Real.sqrt (W + Sig / μ) := by
  have htg : IntegrableOn (fun u => t u * g u) G :=
    hIgt.congr (Eventually.of_forall (fun u => by
      show g u * t u = t u * g u
      exact mul_comm _ _))
  have hmg : IntegrableOn (fun u => μ * g u) G := hIg.const_mul μ
  have hImu : IntegrableOn (fun u => (t u - μ) * g u) G := by
    refine (htg.sub hmg).congr (Eventually.of_forall (fun u => ?_))
    show t u * g u - μ * g u = (t u - μ) * g u
    ring
  have hdiv : IntegrableOn (fun u => g u * t u / μ) G := hIgt.div_const μ
  have hIone : IntegrableOn (fun u => (1 + t u / μ) * g u) G := by
    refine (hIg.add hdiv).congr (Eventually.of_forall (fun u => ?_))
    show g u + g u * t u / μ = (1 + t u / μ) * g u
    ring
  have hIpsi' : IntegrableOn (fun u => (t u - μ) ^ 2 / (1 + t u / μ) * g u) G := by
    refine hIpsi.congr (Eventually.of_forall (fun u => ?_))
    show g u * (1 * (t u - μ) ^ 2 / (1 + t u * μ⁻¹))
      = (t u - μ) ^ 2 / (1 + t u / μ) * g u
    ring
  have hIpsi_eq : (∫ u in G, (t u - μ) ^ 2 / (1 + t u / μ) * g u)
      = ∫ u in G, g u * psiWeight 1 μ (t u) :=
    setIntegral_congr_fun hmeas (fun u _ => by
      show (t u - μ) ^ 2 / (1 + t u / μ) * g u
        = g u * (1 * (t u - μ) ^ 2 / (1 + t u * μ⁻¹))
      ring)
  have hA : Sig - μ * W = ∫ u in G, (t u - μ) * g u := by
    have key : (∫ u in G, (t u - μ) * g u) = ∫ u in G, (t u * g u - μ * g u) :=
      setIntegral_congr_fun hmeas (fun u _ => by
        show (t u - μ) * g u = t u * g u - μ * g u
        ring)
    have hgt_eq : (∫ u in G, t u * g u) = ∫ u in G, g u * t u :=
      setIntegral_congr_fun hmeas (fun u _ => by
        show t u * g u = g u * t u
        exact mul_comm _ _)
    rw [key, MeasureTheory.integral_sub htg hmg, MeasureTheory.integral_const_mul,
      hgt_eq, hSig, hW]
  have hB : W + Sig / μ = ∫ u in G, (1 + t u / μ) * g u := by
    have key : (∫ u in G, (1 + t u / μ) * g u) = ∫ u in G, (g u + g u * t u / μ) :=
      setIntegral_congr_fun hmeas (fun u _ => by
        show (1 + t u / μ) * g u = g u + g u * t u / μ
        ring)
    rw [key, MeasureTheory.integral_add hIg hdiv, MeasureTheory.integral_div,
      hSig, hW]
  calc |Sig - μ * W| = |∫ u in G, (t u - μ) * g u| := by rw [hA]
    _ ≤ Real.sqrt (∫ u in G, (t u - μ) ^ 2 / (1 + t u / μ) * g u)
        * Real.sqrt (∫ u in G, (1 + t u / μ) * g u) :=
        cs_weight hμ hmeas ht hg hIpsi' hIone hImu
    _ = Real.sqrt (∫ u in G, g u * psiWeight 1 μ (t u)) * Real.sqrt (W + Sig / μ) := by
        rw [hIpsi_eq, hB]

/-! ## 5. The target lemma -/

theorem cs_apply {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
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
    (htotal : 8 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (3 / 4)
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :
    |Work.BoseFixB1.wbSig v h μ n (Φ : Submission.BoseGases.X n → ℝ)
        - μ * Work.BoseFixB1.wbW v h μ|
      ≤ Real.sqrt (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.BoseFixB1.wbMass v h μ u
            * Work.SmallBoxSliding.psiWeight 1 μ
                (Work.BoseFixB1.wbDens v h μ n (Φ : Submission.BoseGases.X n → ℝ) u))
        * Real.sqrt (Work.BoseFixB1.wbW v h μ
            + Work.BoseFixB1.wbSig v h μ n (Φ : Submission.BoseGases.X n → ℝ) / μ) := by
  have hmassL : ∀ u : ℝ³, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg hv hvrad hv_supp hR0 hM hℓ hd u
  have haesm_g : AEStronglyMeasurable (fun u : ℝ³ => wbMass v h μ u) volume :=
    w1MassB_aeStronglyMeasurable_local hR0 hv_supp (paramsAt μ (a v)).M hM
      (sideAt μ (a v)) (paramsAt μ (a v)).d
  have haesm_t : AEStronglyMeasurable
      (fun u : ℝ³ => wbDens v h μ n (Φ : X n → ℝ) u) volume :=
    wbDens_aeStronglyMeasurable_gen (h := h) hM hℓ hd (Φ.contDiff.continuous)
  have haesm_gt : AEStronglyMeasurable
      (fun u : ℝ³ => wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u) volume :=
    haesm_g.mul haesm_t
  have hIg : IntegrableOn (fun u : ℝ³ => wbMass v h μ u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    (integrable_w1MassB haesm_g hM hℓ hd hmassL hmassU).integrableOn
  have hIgt : IntegrableOn
      (fun u : ℝ³ => wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    (integrable_w1MassB_mul_dens (Φ := (Φ : X n → ℝ)) haesm_gt
      hM hℓ hd hC₁ hmassL hmassU hN).integrableOn
  have haesm_psi : AEStronglyMeasurable
      (fun u : ℝ³ => wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)) volume :=
    haesm_g.mul (((measurable_psiWeight_cs 1 μ).comp_aemeasurable haesm_t.aemeasurable)).aestronglyMeasurable
  have hIpsi : IntegrableOn
      (fun u : ℝ³ => wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u))
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := by
    have hdom : IntegrableOn (fun u : ℝ³ => μ ^ 2 * wbMass v h μ u
        + μ * (wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u))
        (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
      (hIg.const_mul (μ ^ 2)).add (hIgt.const_mul μ)
    refine hdom.mono' (haesm_psi.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with u
    have ht0 : 0 ≤ wbDens v h μ n (Φ : X n → ℝ) u := wbDens_nonneg _ u
    have hpsi0 : 0 ≤ psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u) :=
      psiWeight_one_nonneg hμ ht0
    have hpsile : psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)
        ≤ μ ^ 2 + μ * wbDens v h μ n (Φ : X n → ℝ) u := psiWeight_one_le hμ ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hmassL u) hpsi0)]
    calc wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)
        ≤ wbMass v h μ u * (μ ^ 2 + μ * wbDens v h μ n (Φ : X n → ℝ) u) :=
          mul_le_mul_of_nonneg_left hpsile (hmassL u)
      _ = μ ^ 2 * wbMass v h μ u
          + μ * (wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u) := by ring
  exact cs_window_general (G := interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
    (t := fun u => wbDens v h μ n (Φ : X n → ℝ) u)
    (g := fun u => wbMass v h μ u) (W := wbW v h μ) (Sig := wbSig v h μ n (Φ : X n → ℝ))
    hμ (measurableSet_interiorSet _ _ _) (fun u _ => wbDens_nonneg (Φ : X n → ℝ) u)
    (fun u _ => hmassL u) rfl rfl hIg hIgt hIpsi

end Work.BoseFixB1.WB
