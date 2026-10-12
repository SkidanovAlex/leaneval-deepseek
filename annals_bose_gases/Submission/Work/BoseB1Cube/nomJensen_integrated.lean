import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NomDefs
import Submission.Work.BoseFixB1.WB.boxState_sq_bound
import Submission.Work.BoseFixB1.WB.integrableOn_wbMass_interior
import Submission.Work.BoseFixB1.WB.ji_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomJensen_integrated`

FS step 4 of `thm:aprioriHLambda` at the **nominal** (indicator-count) density of
`NomDefs.lean`: integrating the pointwise Jensen inequality

  `‖Φ‖²·F(t(u)) ≤ ∫_{abox} Φ²·F(n(u)/|B(u)|)`

against the localised one-body mass `u ↦ ∬w_{1,B(u)}` over the interior set `I₋`
gives

  `‖Φ‖²·∫_{I₋} (∬w_{1,B(u)})·F(t(u)) du ≤ ∫_{I₋} (∬w_{1,B(u)})·∫_{abox} Φ²·F(n(u)/|B(u)|) du`,

i.e. `normB · <the weight> ≤ nomRPsi`.  This is the nominal twin of the proved
`Work.BoseFixB1.WB.jensen_integrated` (which reads the same inequality at the smooth
density `nCountB/chiMass`).

The structural inputs are

* the pointwise Jensen inequality `nomJensen_dens_aux` for the convex weight
  `F = psiWeight 1 μ` at the *indicator* count `nomCnt` and the *sharp* box volume
  `boxMass` (this is where `hBu : μ⁻¹ ≤ boxMass` is used: it keeps the nominal density
  bounded, cf. also the uniform bound below);
* the integrability of `u ↦ (∬w_{1,B(u)})·∫_{abox} Φ² F(n(u)/|B(u)|)` on `I₋`, obtained
  from the integrability of the localised mass (`integrableOn_wbMass_interior`, with **no**
  diluteness hypothesis) and a uniform bound on the inner `x`-integral.

The pointwise Jensen inequality is the abstract Cauchy–Schwarz form of Jensen
(`Work.BoseFixB1.WB.jd_jensen_core`): with `a = Φ²` (so `∫a = ‖Φ‖²`), `f = nomCnt`,
`C = boxMass` one has the exact identity `F(f/C) = (μ/C)(f−μC)²/(f+μC)` and hence
`‖Φ‖² F(∫af/(‖Φ‖²C)) ≤ ∫ a F(f/C)`.  The degenerate case `boxMass = 0` is harmless
because then Lean's `x/0 = 0` makes both sides equal to `μ²‖Φ‖²`.

All auxiliary lemmas below are `private`; they are the pieces of this proof.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Measurability of the nominal objects -/

/-- The box indicator `(u,x) ↦ 1_{B(u)}(x)` is jointly measurable. -/
private lemma measurable_boxInd_joint (ℓ d : ℝ) :
    Measurable (fun p : E3 × E3 => boxInd ℓ d p.1 p.2) := by
  have h : (fun p : E3 × E3 => boxInd ℓ d p.1 p.2)
      = {p : E3 × E3 | p.2 ∈ dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    obtain ⟨u, x⟩ := p
    rw [boxInd]
    by_cases hx : x ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show (u, x) ∈ {p : E3 × E3 | p.2 ∈ dlBox ℓ d p.1} from hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show (u, x) ∉ {p : E3 × E3 | p.2 ∈ dlBox ℓ d p.1} from hx)]
  rw [h]
  exact measurable_const.indicator (measurableSet_boxIndSet ℓ d)

/-- The sharp box count `(u,x) ↦ Σᵢ 1_{B(u)}(xᵢ)` is jointly measurable. -/
private lemma measurable_nomCnt_joint (ℓ d : ℝ) {n : ℕ} :
    Measurable (fun p : E3 × X n => nomCnt ℓ d p.1 p.2) := by
  have hpt : (fun p : E3 × X n => nomCnt ℓ d p.1 p.2)
      = fun p : E3 × X n => ∑ i : Fin n, boxInd ℓ d p.1 (p.2 i) := by
    funext p; simp only [nomCnt]
  rw [hpt]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hmap : Measurable (fun p : E3 × X n => (p.1, p.2 i)) := by fun_prop
  exact (measurable_const.indicator (measurableSet_boxIndSet ℓ d)).comp hmap

/-- The sharp box volume `u ↦ |B(u)|` is a.e. strongly measurable. -/
private lemma aemeasurable_boxMass (ℓ d : ℝ) :
    AEMeasurable (fun u : E3 => boxMass ℓ d u) (volume : Measure E3) := by
  have h : AEStronglyMeasurable (fun u : E3 => ∫ x : E3, boxInd ℓ d u x)
      (volume : Measure E3) :=
    (measurable_boxInd_joint ℓ d).aemeasurable.aestronglyMeasurable.integral_prod_right'
  simpa only [boxMass] using h.aemeasurable

/-- `u ↦ nomBoxInner … u` is a.e. strongly measurable: it is the `x`-integral over the fixed
box `abox n ℓ` of the jointly measurable integrand `(u,x) ↦ Φ(x)²·F(n(u,x)/|B(u)|)`. -/
private lemma aestronglyMeasurable_nomBoxInner_aux {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    AEStronglyMeasurable (fun u : E3 => nomBoxInner h μ (Φ : X n → ℝ) u)
      (volume : Measure E3) := by
  have hjoint : AEMeasurable (fun p : E3 × X n =>
      (Φ p.2) ^ 2 * psiWeight 1 μ
        (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d p.1 p.2
          / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d p.1))
      ((volume : Measure E3).prod (volume.restrict (abox n (sideAt μ (a v))))) := by
    refine AEMeasurable.mul ?_ ?_
    · exact ((Φ.contDiff.continuous.measurable.pow_const 2).comp measurable_snd).aemeasurable
    · have hpsi : Measurable (fun t : ℝ => psiWeight 1 μ t) := by
        simp only [psiWeight]
        fun_prop
      refine hpsi.comp_aemeasurable ?_
      exact (measurable_nomCnt_joint (sideAt μ (a v)) (paramsAt μ (a v)).d).aemeasurable.div
        ((aemeasurable_boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst)
  have h := hjoint.aestronglyMeasurable.integral_prod_right'
  simpa only [nomBoxInner] using h

/-! ## 2. A uniform bound on the inner `x`-integral -/

/-- `F(t) ≤ μ(t+μ)` for `t ≥ 0`, `F = psiWeight 1 μ`. -/
private lemma psiWeight_one_le_mu_mul_add_local {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    psiWeight 1 μ t ≤ μ * (t + μ) := by
  rw [psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by
    field_simp
    ring
  rw [h1]
  have h2 : μ * (t + μ) * ((t + μ) / μ) = (t + μ) ^ 2 := by
    field_simp
  rw [h2]
  nlinarith [sq_nonneg (t - μ), hμ, ht]

/-- The one-variable box indicator is measurable. -/
private lemma measurable_boxInd_slice {ℓ d : ℝ} (u : E3) :
    Measurable (fun z : E3 => boxInd ℓ d u z) := by
  have h : (fun z : E3 => boxInd ℓ d u z) = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) := by
    funext z; rw [boxInd]
  rw [h]
  exact measurable_const.indicator (measurableSet_dlBox ℓ d u)

/-- `x ↦ boxInd ℓ d u (x i)` is measurable. -/
private lemma measurable_boxInd_comp {ℓ d : ℝ} {n : ℕ} (i : Fin n) (u : E3) :
    Measurable (fun x : X n => boxInd ℓ d u (x i)) :=
  (measurable_boxInd_slice (d := d) u).comp (measurable_pi_apply i)

/-- `x ↦ n(u,x)` is measurable (a finite sum of indicators of the sliding box). -/
private lemma measurable_nomCnt {ℓ d : ℝ} {n : ℕ} (u : E3) :
    Measurable (fun x : X n => nomCnt ℓ d u x) := by
  have hpt : (fun x : X n => nomCnt ℓ d u x)
      = fun x : X n => ∑ i : Fin n, boxInd ℓ d u (x i) := by
    funext x; simp only [nomCnt]
  rw [hpt]
  exact Finset.measurable_sum _ (fun i _ => measurable_boxInd_comp i u)

/-- `boxInd ℓ d u` is integrable on `acube ℓ` (bounded by `1` on a set of finite measure). -/
private lemma integrableOn_boxInd_acube {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    IntegrableOn (boxInd ℓ d u) (acube ℓ) := by
  refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_ 1 ?_
  · exact (measurable_boxInd_slice (d := d) u).aemeasurable.aestronglyMeasurable
  · filter_upwards with z
    rw [boxInd]
    by_cases hz : z ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hz]; simp
    · rw [Set.indicator_of_notMem hz]; simp

/-- `boxInd ℓ d u` is (globally) integrable: it is the indicator of a set of finite measure. -/
private lemma integrable_boxInd {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    Integrable (boxInd ℓ d u) (volume : Measure E3) := by
  have hdl : MeasurableSet (dlBox ℓ d u) := measurableSet_dlBox ℓ d u
  have heq : boxInd ℓ d u = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) := by
    funext z; rw [boxInd]
  rw [heq, integrable_indicator_iff hdl]
  refine IntegrableOn.of_bound (volume_dlBox_lt_top hℓ d u) ?_ 1 ?_
  · exact aestronglyMeasurable_const
  · filter_upwards with z
    simp

/-- `x ↦ boxInd ℓ d u (x i)` is integrable on `abox n ℓ`. -/
private lemma integrableOn_abox_boxInd_comp {ℓ d : ℝ} {n : ℕ} (i : Fin n) (u : E3) :
    IntegrableOn (fun x : X n => boxInd ℓ d u (x i)) (abox n ℓ) := by
  refine IntegrableOn.of_bound
    ((Work.UBBInputs9.B.abox_isCompact n ℓ).measure_lt_top) ?_ 1 ?_
  · exact (measurable_boxInd_comp i u).aemeasurable.aestronglyMeasurable
  · filter_upwards with x
    rw [boxInd]
    by_cases hx : x i ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp

/-- **The exact peel of the sharp count**:
`∫_{abox n ℓ} n(u) = n·(ℓ³)^{n-1}·∫_{acube ℓ} 1_{B(u)}`. -/
private lemma integral_abox_nomCnt {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (u : E3) :
    (∫ x in abox n ℓ, nomCnt ℓ d u x)
      = (n : ℝ) * ((ℓ ^ 3) ^ (n - 1) * ∫ z in acube ℓ, boxInd ℓ d u z) := by
  rw [show (fun x : X n => nomCnt ℓ d u x)
      = fun x : X n => ∑ i : Fin n, boxInd ℓ d u (x i) from by
    funext x; rw [nomCnt]]
  rw [MeasureTheory.integral_finsetSum (Finset.univ)
    (fun i _ => integrableOn_abox_boxInd_comp i u)]
  rw [Finset.sum_congr rfl (fun i _ =>
        Work.UBBInputs8.A.integral_abox_comp_apply (N := n) (L := ℓ) hℓ.le i
          (integrableOn_boxInd_acube hℓ u)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `x ↦ n(u,x)` is integrable on `abox n ℓ` (bounded by `n`). -/
private lemma integrableOn_nomCnt {ℓ d : ℝ} {n : ℕ} (u : E3) :
    IntegrableOn (fun x : X n => nomCnt ℓ d u x) (abox n ℓ) := by
  refine IntegrableOn.of_bound
    ((Work.UBBInputs9.B.abox_isCompact n ℓ).measure_lt_top) ?_ (n : ℝ) ?_
  · exact (measurable_nomCnt (d := d) u).aemeasurable.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (nomCnt_nonneg ℓ d u x)]
    exact nomCnt_le_card ℓ d u x

/-- **The uniform bound** on `nomBoxInner`: with `P` bounding `Φ²` on the box,
`nomBoxInner h μ Φ u ≤ μ·P·n·(ℓ³)^{n−1} + μ²‖Φ‖²` for *every* `u`. -/
private lemma nomBoxInner_le_const_aux {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hμ : 0 < μ) (hℓ : 0 < sideAt μ (a v))
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : E3, nomBoxInner h μ (Φ : X n → ℝ) u ≤ M := by
  obtain ⟨P, hP0, hPb⟩ := Work.BoseFixB1.WB.boxState_sq_bound (ℓ := sideAt μ (a v)) Φ
  refine ⟨μ * P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))
      + μ ^ 2 * normB v μ n (Φ : X n → ℝ), ?_, ?_⟩
  · refine add_nonneg (mul_nonneg (mul_nonneg hμ.le hP0)
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (pow_nonneg hℓ.le 3) _)))
      (mul_nonneg (sq_nonneg μ) (normB_nonneg _))
  · intro u
    have hb : 0 ≤ boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := boxMass_nonneg' _ _ _
    have haboxmeas : MeasurableSet (abox n (sideAt μ (a v))) :=
      (Work.UBBInputs9.B.abox_isCompact n (sideAt μ (a v))).isClosed.measurableSet
    have hΦc : Continuous (fun x : X n => (Φ : X n → ℝ) x ^ 2) :=
      (Φ.contDiff.continuous).pow 2
    have hΦint : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2)
        (abox n (sideAt μ (a v))) :=
      Work.UBBInputs9.B.integrableOn_abox_of_continuous' hΦc
    have hNCint : IntegrableOn (fun x : X n =>
        nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        (abox n (sideAt μ (a v))) := integrableOn_nomCnt u
    have hNCmeas : Measurable (fun x : X n =>
        nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x) :=
      measurable_nomCnt (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d) u
    have hprodInt : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2
        * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        (abox n (sideAt μ (a v))) := by
      refine (hΦint.mul_const (n : ℝ)).mono' ?_ ?_
      · exact ((hΦc.measurable.mul hNCmeas).aemeasurable.aestronglyMeasurable)
      · filter_upwards with x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (nomCnt_nonneg _ _ _ x))]
        exact mul_le_mul_of_nonneg_left (nomCnt_le_card _ _ _ x) (sq_nonneg _)
    -- the comparison integrand is integrable
    have hintC : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2
        * (μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
        (abox n (sideAt μ (a v))) := by
      have h1 : IntegrableOn (fun x : X n =>
          (μ * (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)⁻¹)
            * ((Φ : X n → ℝ) x ^ 2
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x))
          (abox n (sideAt μ (a v))) := hprodInt.const_mul _
      have h2 : IntegrableOn (fun x : X n => (μ * μ) * (Φ : X n → ℝ) x ^ 2)
          (abox n (sideAt μ (a v))) := hΦint.const_mul _
      refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.add_apply, div_eq_mul_inv]
      ring
    have hstep1 : nomBoxInner h μ (Φ : X n → ℝ) u
        ≤ ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * (μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ) := by
      rw [nomBoxInner]
      refine integral_mono_of_nonneg ?_ hintC ?_
      · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
        intro x _
        exact mul_nonneg (sq_nonneg _)
          (Work.BoseFixB1.WB.psiWeight_one_nonneg_local hμ
            (div_nonneg (nomCnt_nonneg _ _ _ x) hb))
      · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
        intro x _
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have ht : 0 ≤ nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
          div_nonneg (nomCnt_nonneg _ _ _ x) hb
        have h := psiWeight_one_le_mu_mul_add_local (μ := μ) hμ ht
        calc psiWeight 1 μ (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            ≤ μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ) := h
          _ = μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ := by ring
    -- compute the comparison integral
    have hstep2 : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
          * (μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
        = μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by
      have hcongr : (fun x : X n => (Φ : X n → ℝ) x ^ 2
            * (μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
          = fun x : X n => (μ * ((Φ : X n → ℝ) x ^ 2
                * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u
              + μ ^ 2 * (Φ : X n → ℝ) x ^ 2) := by
        funext x; ring
      rw [hcongr, MeasureTheory.integral_add ((hprodInt.const_mul μ).div_const _)
        (hΦint.const_mul (μ ^ 2)), MeasureTheory.integral_div]
      have h2 : (∫ x in abox n (sideAt μ (a v)), μ * ((Φ : X n → ℝ) x ^ 2
            * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x))
          = μ * ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x := by
        rw [MeasureTheory.integral_const_mul]
      have h3 : (∫ x in abox n (sideAt μ (a v)), μ ^ 2 * (Φ : X n → ℝ) x ^ 2)
          = μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by
        rw [MeasureTheory.integral_const_mul, Work.BoseBoxFix.normB,
          Work.BoseKinLoc.sqNormB]
      rw [h2, h3]
    -- the sharp peel bound
    have hkey : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
          * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        ≤ P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
            * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
      have hle : (∫ z in acube (sideAt μ (a v)),
            boxInd (sideAt μ (a v)) (paramsAt μ (a v)).d u z)
          ≤ boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
        rw [boxMass]
        exact setIntegral_le_integral (integrable_boxInd hℓ u)
          (Filter.Eventually.of_forall (fun z => boxInd_nonneg' _ _ _ z))
      have hA : (∫ x in abox n (sideAt μ (a v)),
            nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          ≤ (n : ℝ) * ((sideAt μ (a v) ^ 3) ^ (n - 1)
              * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
        rw [integral_abox_nomCnt hℓ u]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (pow_nonneg (pow_nonneg hℓ.le 3) _))
          (Nat.cast_nonneg n)
      have hmono : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          ≤ ∫ x in abox n (sideAt μ (a v)), P
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x := by
        refine integral_mono_of_nonneg ?_ (hNCint.const_mul P) ?_
        · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
          intro x _
          exact mul_nonneg (sq_nonneg _) (nomCnt_nonneg _ _ _ x)
        · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
          intro x hx
          exact mul_le_mul_of_nonneg_right (hPb x hx) (nomCnt_nonneg _ _ _ x)
      rw [MeasureTheory.integral_const_mul] at hmono
      calc (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          ≤ P * (∫ x in abox n (sideAt μ (a v)),
              nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x) := hmono
        _ ≤ P * ((n : ℝ) * ((sideAt μ (a v) ^ 3) ^ (n - 1)
              * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)) :=
            mul_le_mul_of_nonneg_left hA hP0
        _ = P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
              * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by ring
    -- divide by the sharp box volume
    have hCdiv : μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u
        ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))) := by
      by_cases hC0 : boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u = 0
      · rw [hC0, div_zero]
        exact mul_nonneg hμ.le (mul_nonneg hP0
          (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (pow_nonneg hℓ.le 3) _)))
      · rw [div_le_iff₀ (lt_of_le_of_ne hb (Ne.symm hC0))]
        calc μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
                * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)) :=
              mul_le_mul_of_nonneg_left hkey hμ.le
          _ = (μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))))
                * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by ring
    calc nomBoxInner h μ (Φ : X n → ℝ) u
        ≤ (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * (μ * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ)) := hstep1
      _ = μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
              * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := hstep2
      _ ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)))
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by linarith [hCdiv]
      _ = μ * P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by ring

/-! ## 3. The pointwise Jensen inequality at the nominal density -/

private lemma nomJensen_dens_aux {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (hμ : 0 < μ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    normB v μ n (Φ : X n → ℝ) * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u)
      ≤ nomBoxInner h μ (Φ : X n → ℝ) u := by
  have hb : 0 ≤ boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := boxMass_nonneg' _ _ _
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- degenerate case: the sharp box volume vanishes, so both sides equal `μ²‖Φ‖²`
    have hzero : ∀ x : X n, nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u = 0 := fun x => by
      rw [← hb0, div_zero]
    rw [nomDens, ← hb0, mul_zero, div_zero, Work.BoseFixB1.WB.jd_psiWeight_zero, nomBoxInner]
    simp only [hzero, Work.BoseFixB1.WB.jd_psiWeight_zero]
    rw [MeasureTheory.integral_mul_const, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  · -- main case: the abstract Cauchy–Schwarz form of Jensen
    rw [nomDens, nomBoxInner, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    have hΦc : Continuous (fun x : X n => (Φ : X n → ℝ) x ^ 2) :=
      (Φ.contDiff.continuous).pow 2
    have hΦint : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2)
        (abox n (sideAt μ (a v))) :=
      Work.UBBInputs9.B.integrableOn_abox_of_continuous' hΦc
    have hNCmeas : Measurable (fun x : X n =>
        nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x) :=
      measurable_nomCnt (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d) u
    have hprodInt : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2
        * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        (abox n (sideAt μ (a v))) := by
      refine (hΦint.mul_const (n : ℝ)).mono' ?_ ?_
      · exact ((hΦc.measurable.mul hNCmeas).aemeasurable.aestronglyMeasurable)
      · filter_upwards with x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (nomCnt_nonneg _ _ _ x))]
        exact mul_le_mul_of_nonneg_left (nomCnt_le_card _ _ _ x) (sq_nonneg _)
    refine Work.BoseFixB1.WB.jd_jensen_core
      (ν := volume.restrict (abox n (sideAt μ (a v))))
      (a := fun x : X n => (Φ : X n → ℝ) x ^ 2)
      (f := fun x : X n => nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
      hμ hbpos (fun x => sq_nonneg _) (fun x => nomCnt_nonneg _ _ _ x)
      hΦint hprodInt ?_
    · -- `∫ Φ²·(n−μ|B|)²/(n+μ|B|)`, dominated by `∫ Φ²·(n+μ|B|)`
      have hNCint : IntegrableOn (fun x : X n =>
          nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          (abox n (sideAt μ (a v))) := integrableOn_nomCnt u
      have hFint : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2
          * (nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              + μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))
          (abox n (sideAt μ (a v))) :=
        (hprodInt.add (hΦint.const_mul
          (μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))).congr
          (Filter.Eventually.of_forall (fun x => by
            simp only [Pi.add_apply]; ring))
      refine hFint.mono' ?_ ?_
      · exact ((hΦc.measurable.mul (((hNCmeas.sub measurable_const).pow_const 2).div
          (hNCmeas.add measurable_const))).aemeasurable.aestronglyMeasurable)
      · filter_upwards with x
        have h1 : 0 ≤ nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x :=
          nomCnt_nonneg _ _ _ x
        have hbd : 0 < nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            + μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
          nlinarith [mul_pos hμ hbpos]
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hbd.le))]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [div_le_iff₀ hbd]
        nlinarith [mul_nonneg (le_of_lt (mul_pos hμ hbpos)) h1]

/-! ## 4. The integrated inequality -/

theorem nomJensen_integrated {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hBu : ∀ u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
      μ⁻¹ ≤ Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        * (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            Work.BoseFixB1.wbMass v h μ u
              * Work.SmallBoxSliding.psiWeight 1 μ
                  (Work.BoseB1Cube.nomDens h μ (Φ : Submission.BoseGases.X n → ℝ) u))
      ≤ Work.BoseB1Cube.nomRPsi h μ (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨M, hM0, hMb⟩ :=
    nomBoxInner_le_const_aux (v := v) (h := h) (μ := μ) (n := n) hμ hℓ Φ
  have hInt : IntegrableOn (fun u : E3 => wbMass v h μ u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    Work.BoseFixB1.WB.integrableOn_wbMass_interior (v := v) (h := h) (R0 := R)
      hv hvrad hv_supp hR hμ hav hM hℓ hd
  have hwb : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hM hℓ hd u
  have hglue : IntegrableOn
      (fun u : E3 => wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := by
    have hdom : IntegrableOn (fun u : E3 => M * wbMass v h μ u)
        (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := hInt.const_mul M
    refine hdom.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul hInt.aestronglyMeasurable ?_
      exact (aestronglyMeasurable_nomBoxInner_aux (v := v) (h := h) (μ := μ) (n := n) Φ
        ).mono_measure Measure.restrict_le_self
    · filter_upwards with u
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hwb u) (nomBoxInner_nonneg hμ (Φ : X n → ℝ) u))]
      calc wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u
          ≤ wbMass v h μ u * M := mul_le_mul_of_nonneg_left (hMb u) (hwb u)
        _ = M * wbMass v h μ u := by ring
  have hpt : ∀ u : E3, normB v μ n (Φ : X n → ℝ)
        * (wbMass v h μ u * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u))
      ≤ wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u := by
    intro u
    have hJ := nomJensen_dens_aux (v := v) (h := h) (μ := μ) (n := n) hμ Φ u
    calc normB v μ n (Φ : X n → ℝ)
          * (wbMass v h μ u * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u))
        = (normB v μ n (Φ : X n → ℝ)
            * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u)) * wbMass v h μ u := by ring
      _ ≤ nomBoxInner h μ (Φ : X n → ℝ) u * wbMass v h μ u :=
          mul_le_mul_of_nonneg_right hJ (hwb u)
      _ = wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u := by ring
  show normB v μ n (Φ : X n → ℝ)
      * (∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          wbMass v h μ u * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u))
      ≤ ∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hglue ?_
  · filter_upwards with u
    exact mul_nonneg (normB_nonneg _)
      (mul_nonneg (hwb u)
        (Work.BoseFixB1.WB.psiWeight_one_nonneg_local hμ
          (nomDens_nonneg (Φ : X n → ℝ) u)))
  · filter_upwards with u
    exact hpt u

end Work.BoseB1Cube
