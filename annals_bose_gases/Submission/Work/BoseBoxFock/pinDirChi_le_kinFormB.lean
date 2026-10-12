import ChallengeDeps
import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.chiSqDirichletFsT
import Submission.Work.BoseBoxFock.kinFormB_slot_fsT
import Submission.Work.BoseBoxFock.pinDirChi_slot_slice
import Submission.Work.BoseFixB2.Polar.fibre_H1_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinDirChi_le_kinFormB`

The `χ_ℓ`-weighted Dirichlet content `pinDirChi ℓ Θ` of a box state `Θ = Φ_ℂ` is dominated by the
box kinetic word `kinFormB` plus `n` times the state mass `normB`:

    `pinDirChi ℓ Φ_ℂ ≤ C·(kinFormB n ℓ d s εT b Φ + n·normB)`,

at FS's parameters (`ℓ = sideAt μ (a v)`, `(d,s,εT,b) = (paramsAt μ (a v))`).

## The reduction

* `pinDirChi_slot_slice` (delegated) rewrites the slot-`(i,j)` summand of `pinDirChi` as the
  iterated integral of the *fibre* derivative over `(w, x') ∈ Λ × Λ^{{k≠i}}`.
* `chiSqDirichletFsT` (delegated) is the one-body bound
  `∫_Λ χ²Σ_j(∂_jψ)² ≤ C₁(fsT ψ + ∫_Λψ²)`, applied to the slot-`i` fibre `ψ_{x'}` for each `x'`.
* `kinFormB_slot_fsT` (delegated) transports the `fsT`-term back to the box integral of `kinFormB`.

The remaining bookkeeping (`indU = 1` on the box, the mass slice, the sums over the slots) is
proved here.
-/

noncomputable section
open MeasureTheory
open scoped Topology BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The insertion/fibre dictionary -/

/-- Re-inserting a value in the slot `j` of `insertCoord j w x'` recovers `insertCoord j z x'`. -/
lemma update_insertCoord {n : ℕ} (j : Fin n) (w z : E3) (x' : {k : Fin n // k ≠ j} → E3) :
    Function.update (insertCoord j w x') j z = insertCoord j z x' := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    simp [insertCoord]
  · rw [Function.update_of_ne hk]
    simp [insertCoord, hk]

/-- The slot-`j` fibre of the configuration `insertCoord j w x'` is the slice
`z ↦ Φ (insertCoord j z x')`, which does not depend on `w`. -/
lemma fibre_insertCoord {n : ℕ} (j : Fin n) (Φ : Xn n → ℝ) (w : E3)
    (x' : {k : Fin n // k ≠ j} → E3) :
    Work.BoseKinLoc.fibre n j Φ (insertCoord j w x') = fun z => Φ (insertCoord j z x') := by
  funext z
  show Φ (Function.update (insertCoord j w x') j z) = Φ (insertCoord j z x')
  rw [update_insertCoord j w z x']

/-- **The chain rule for the insertion map**: the slot-`j`, direction-`k` derivative of `Φ` at
`insertCoord j w x'` is the derivative of the slice `z ↦ Φ (insertCoord j z x')` at `w`. -/
lemma fderiv_fibre_insertCoord {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (j : Fin n) (w : E3) (x' : {k : Fin n // k ≠ j} → E3) (k : Fin 3) :
    fderiv ℝ (fun z : E3 => Φ (insertCoord j z x')) w (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ Φ (insertCoord j w x') (slotDirVec j k) := by
  have h := Work.BoseFixB2.Polar.fderiv_fibre_apply hΦ j (insertCoord j w x') w k
  rw [fibre_insertCoord j Φ w x'] at h
  rw [h, update_insertCoord j w w x']
  rfl

/-- The complexified derivative along the slot direction of `insertCoord j w x'`. -/
lemma fderiv_complex_fibre_insertCoord {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (j : Fin n) (w : E3) (x' : {k : Fin n // k ≠ j} → E3) (k : Fin 3) :
    fderiv ℝ (fun y : Xn n => ((Φ y : ℝ) : ℂ)) (insertCoord j w x') (slotDirVec j k)
      = ((fderiv ℝ (fun z : E3 => Φ (insertCoord j z x')) w
            (Submission.BoseGases.kcStdBasis k) : ℝ) : ℂ) := by
  have hcompl : fderiv ℝ (fun y : Xn n => ((Φ y : ℝ) : ℂ)) (insertCoord j w x') (slotDirVec j k)
      = ((fderiv ℝ Φ (insertCoord j w x') (slotDirVec j k) : ℝ) : ℂ) := by
    have h1 : HasFDerivAt (fun y : Xn n => ((Φ y : ℝ) : ℂ))
        ((Complex.ofRealCLM).comp (fderiv ℝ Φ (insertCoord j w x'))) (insertCoord j w x') :=
      Complex.ofRealCLM.hasFDerivAt.comp _
        ((hΦ.differentiable (by simp) (insertCoord j w x')).hasFDerivAt)
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  rw [hcompl, ← fderiv_fibre_insertCoord hΦ j w x' k]

/-- The square of the norm of the complexified derivative is the square of the fibre derivative. -/
lemma normSq_fderiv_complex_fibre {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (j : Fin n) (w : E3) (x' : {k : Fin n // k ≠ j} → E3) (k : Fin 3) :
    ‖fderiv ℝ (fun y : Xn n => ((Φ y : ℝ) : ℂ)) (insertCoord j w x') (slotDirVec j k)‖ ^ 2
      = (fderiv ℝ (fun z : E3 => Φ (insertCoord j z x')) w
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  rw [fderiv_complex_fibre_insertCoord hΦ j w x' k]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-! ## 2. Continuity of the fibre-derivative integrand -/

/-- The parametric fibre derivative is continuous on the `(w,x')`-space. -/
lemma continuous_fibre_deriv {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : Fin n) (j : Fin 3) :
    Continuous (fun p : E3 × ({k : Fin n // k ≠ i} → E3) =>
      fderiv ℝ (fun z : E3 => Φ (insertCoord i z p.2)) p.1
        (Submission.BoseGases.kcStdBasis j)) := by
  have hfun : (fun p : E3 × ({k : Fin n // k ≠ i} → E3) =>
      fderiv ℝ (fun z : E3 => Φ (insertCoord i z p.2)) p.1
        (Submission.BoseGases.kcStdBasis j))
      = fun p : E3 × ({k : Fin n // k ≠ i} → E3) =>
          fderiv ℝ Φ (insertCoord i p.1 p.2) (slotDirVec i j) := by
    funext p
    exact fderiv_fibre_insertCoord hΦ i p.1 p.2 j
  rw [hfun]
  exact ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_insertCoord i)

/-! ## 3. Box bookkeeping: the indicator, the mass slice -/

/-- The box indicator is `1` on the box: `indU ℓ 0 (x i) = 1` for `x ∈ abox n ℓ`. -/
lemma indU_zero_of_mem_abox {n : ℕ} {ℓ : ℝ} {x : Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) :
    Work.BoseKinLoc.indU ℓ 0 (x i) = 1 := by
  have hmem : x i ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
    rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube]
    rw [Submission.BoseGases.mem_abox_iff] at hx
    exact hx i
  rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem]

/-- The box `Λ(ℓ)` is compact for `ℓ > 0`. -/
lemma isCompact_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (boxL ℓ) := by
  rw [corpusBox_boxL_eq_acube hℓ]
  exact Submission.BoseGases.acube_compact hℓ

/-- **The mass slice**: the `L²`-mass of the state on the box is the iterated integral of the
mass of its slot-`i` fibre. -/
lemma mass_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Xn n → ℝ} (hΦ : Continuous Φ) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Φ (insertCoord i w x')) ^ 2 := by
  have hslice : (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
        (Φ (insertCoord i w x')) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    setIntegral_insertCoord_slice (ℓ := ℓ) hℓ i (f := fun x : Xn n => (Φ x) ^ 2) (hΦ.pow 2)
  rw [← hslice]
  rw [MeasureTheory.integral_integral_swap]
  -- integrability of the uncurried integrand on the product of the restricted measures
  have hIntOn : Integrable
      (Function.uncurry (fun w (x' : {k : Fin n // k ≠ i} → E3) =>
        (Φ (insertCoord i w x')) ^ 2))
      (volume.restrict (boxL ℓ ×ˢ boxPiSet ({k : Fin n // k ≠ i}) ℓ)) :=
    ContinuousOn.integrableOn_compact
      ((isCompact_boxL hℓ).prod (isCompact_boxPiSet hℓ))
      ((hΦ.comp (continuous_insertCoord i)).pow 2).continuousOn
  rw [show (volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))
      = volume.restrict (boxL ℓ ×ˢ boxPiSet ({k : Fin n // k ≠ i}) ℓ) from by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]]
  exact hIntOn

/-- A continuous function is integrable on the box `Λ(ℓ)`. -/
lemma integrableOn_boxL_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (boxL ℓ)) := by
  obtain ⟨C, hC⟩ := (isCompact_boxL hℓ).exists_bound_of_continuousOn hf.continuousOn
  refine MeasureTheory.IntegrableOn.of_bound
    (lt_top_iff_ne_top.mpr (isCompact_boxL hℓ).measure_ne_top) hf.aestronglyMeasurable C ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict (isCompact_boxL hℓ).measurableSet]
    with x hx
  exact hC x hx

/-- Integrability of a continuous `(w,x')`-integrand against the product of the restricted box
measures. -/
lemma integrable_uncurry_of_continuous {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : E3 → (ι → E3) → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Integrable (Function.uncurry f)
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ι ℓ))) := by
  rw [show (volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ι ℓ))
      = volume.restrict (boxL ℓ ×ˢ boxPiSet ι ℓ) from by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]]
  exact ContinuousOn.integrableOn_compact
    ((isCompact_boxL hℓ).prod (isCompact_boxPiSet hℓ)) hf.continuousOn

/-- For a fixed `x'`, the `w ↦` slot integrand of the fibre is continuous. -/
lemma continuous_slot_integrand {n : ℕ} {ℓ : ℝ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : Fin n) (j : Fin 3) (x' : {k : Fin n // k ≠ i} → E3) :
    Continuous (fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2 *
      (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
        (Submission.BoseGases.kcStdBasis j)) ^ 2) := by
  have hfun : (fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
          (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        (fderiv ℝ Φ (insertCoord i w x') (slotDirVec i j)) ^ 2 := by
    funext w
    rw [fderiv_fibre_insertCoord hΦ i w x' j]
  rw [hfun]
  have hins : Continuous (fun w : E3 => insertCoord i w x') :=
    (continuous_insertCoord i).comp (continuous_id.prodMk continuous_const)
  exact ((Submission.BoseGases.chiScale_continuous ℓ).pow 2).mul
    ((((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).comp hins).pow 2)

/-- **The per-slot reduction.**  Applying the one-body bound `h₁` to the slot-`i` fibres and the
two slice identities `hslice` (for `pinDirChi`), `hkin`/`hkinint` (for `kinFormB`) and `hmass`
(for the state mass), the slot-`i` Dirichlet content of `pinDirChi` is dominated by the slot-`i`
contribution to `kinFormB` plus the state mass. -/
lemma pinDirChi_slot_le {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) {C₁ : ℝ}
    (h₁ : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ C₁ * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          + C₁ * (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z) ^ 2))
    (hslice : ∀ j : Fin 3,
      (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
        = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ,
              (Submission.BoseGases.chiScale ℓ w) ^ 2 *
                (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Φ (Work.BoseBoxFock.insertCoord i z x')) w
                  (Submission.BoseGases.kcStdBasis j)) ^ 2)
    (hkin : ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) *
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
        = ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Work.BoseBoxFock.insertCoord i z x')))
    (hkinint : MeasureTheory.IntegrableOn
        (fun x' : ({k : Fin n // k ≠ i} → EuclideanSpace ℝ (Fin 3)) =>
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Work.BoseBoxFock.insertCoord i z x')))
        (Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ))
    (hmass : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        = ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              (Φ (Work.BoseBoxFock.insertCoord i w x')) ^ 2) :
    (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      ≤ C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
          + (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
  -- continuity of the slot integrands, of the summed integrand and of the mass integrand
  have hdcont (j : Fin 3) : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
          (Submission.BoseGases.kcStdBasis j))) :=
    continuous_fibre_deriv hΦ i j
  have hFcont (j : Fin 3) : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2)) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).comp continuous_fst).mul
      ((hdcont j).pow 2)
  have hGcont : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).comp continuous_fst).mul
      (continuous_finsetSum _ (fun j _ => (hdcont j).pow 2))
  have hins : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : E3 × ({k : Fin n // k ≠ i} → E3) => insertCoord i q.1 q.2) :=
    contDiff_insertCoord_comp (P := E3 × ({k : Fin n // k ≠ i} → E3)) (j := i)
      (w := fun q => q.1) (x' := fun q => q.2) contDiff_fst contDiff_snd
  have hmcont : Continuous
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Φ (insertCoord i w x')) ^ 2)) :=
    (hΦ.comp hins).continuous.pow 2
  have hFint (j : Fin 3) : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ (hFcont j)
  have hGint : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2)))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ hGcont
  have hmint : Integrable
      (Function.uncurry (fun (w : E3) (x' : {k : Fin n // k ≠ i} → E3) =>
        (Φ (insertCoord i w x')) ^ 2))
      ((volume.restrict (boxL ℓ)).prod (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) :=
    integrable_uncurry_of_continuous hℓ hmcont
  have hmint2 : Integrable (fun x' : {k : Fin n // k ≠ i} → E3 =>
      ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ)) :=
    (Integrable.integral_prod_right hmint).congr
      (Filter.Eventually.of_forall fun x' =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => rfl))
  -- the smoothness of the slot fibres
  have hfib (x' : {k : Fin n // k ≠ i} → E3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => Φ (insertCoord i z x')) :=
    hΦ.comp (contDiff_insertCoord_comp (P := E3) (j := i) (w := fun z : E3 => z)
      (x' := fun _ : E3 => x') contDiff_id contDiff_const)
  -- Step A: the slices
  have hA : (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => hslice j)
  -- Step B: swap the two integrations in each summand
  have hB : (∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_integral_swap]
    exact hFint j
  -- Step C: pull the `j`-sum out of the `x'`-integral
  have hC : (∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 :=
    (MeasureTheory.integral_finsetSum (μ := volume.restrict (boxPiSet ({k : Fin n // k ≠ i}) ℓ))
      (s := Finset.univ)
      (f := fun j x' => ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w (Submission.BoseGases.kcStdBasis j)) ^ 2)
      (fun j _ => Integrable.integral_prod_right (hFint j))).symm
  -- Step D: the pointwise identification of the summed integrand
  have hDpoint (x' : {k : Fin n // k ≠ i} → E3) :
      (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
        = ∑ j : Fin 3, ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
    have hsplit : (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
            (Submission.BoseGases.kcStdBasis j)) ^ 2))
        = ∫ w in boxL ℓ, ∑ j : Fin 3,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      dsimp only
      rw [Finset.mul_sum]
    rw [hsplit, MeasureTheory.integral_finsetSum]
    intro j _
    exact integrableOn_boxL_of_continuous hℓ (continuous_slot_integrand hΦ i j x')
  have hD : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x' =>
      (hDpoint x').symm))
  -- Step E: the one-body bound, fibrewise
  have hE : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2))
      ≤ ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (C₁ * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + C₁ * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)) := by
    refine MeasureTheory.integral_mono_ae (Integrable.integral_prod_right hGint)
      (Integrable.add (hkinint.const_mul C₁) (hmint2.const_mul C₁))
      (Filter.Eventually.of_forall (fun x' => h₁ _ (hfib x')))
  -- Step F: split the sum of the two integrals
  have hF : (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (C₁ * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + C₁ * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)))
      = C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
          + C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
              ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2) := by
    rw [MeasureTheory.integral_add (hkinint.const_mul C₁) (hmint2.const_mul C₁),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Step G: the two slice identities
  have hG : C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
        + C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)
      = C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
          + (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
    rw [← hkin, ← hmass, mul_add]
  calc (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∑ j : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := hA
    _ = ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2 := hB
    _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          ∑ j : Fin 3, ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 := hC
    _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
              (Submission.BoseGases.kcStdBasis j)) ^ 2) := hD
    _ ≤ ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
          (C₁ * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (fun z : E3 => Φ (insertCoord i z x'))
            + C₁ * (∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2)) := hE
    _ = C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => Φ (insertCoord i z x')))
          + C₁ * (∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ,
              ∫ w in boxL ℓ, (Φ (insertCoord i w x')) ^ 2) := hF
    _ = C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x))
          + (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := hG

theorem pinDirChi_le_kinFormB {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {μ : ℝ} (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (hb : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
    (hεT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (hεT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseBoxFock.pinDirChi (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (fun x => ((Φ x : ℝ) : ℂ))
          ≤ C * (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ)
              + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  -- abbreviations for the parameters at FS's choice
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set εT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with hεTdef
  set b : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b with hbdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBox.sideAt_pos hμ hav
  have hd' : 0 < d := by rw [hddef]; exact hd
  have hs' : 0 < s := by rw [hsdef]; exact hs
  have hb' : 0 ≤ b := by rw [hbdef]; exact hb
  have hεT0' : 0 ≤ εT := by rw [hεTdef]; exact hεT0
  have hεT1' : εT ≤ 1 := by rw [hεTdef]; exact hεT1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := chiSqDirichletFsT (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
    hℓ hd' hs' hb' hεT0' hεT1'
  refine ⟨C₁, hC₁pos, ?_⟩
  intro Φ
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  -- the complexification of the fibre derivative
  have hcpx : ∀ (v : Submission.BoseGases.X n) (x : Submission.BoseGases.X n),
      fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x v
        = ((fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x v : ℝ) : ℂ) := by
    intro v x
    have h1 : HasFDerivAt (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ))
        ((Complex.ofRealCLM).comp (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp _
        ((hΦc.differentiable (by simp) x).hasFDerivAt)
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- continuity of the slot integrands
  have hcont (i : Fin n) (j : Fin 3) : Continuous (fun x : Submission.BoseGases.X n =>
      (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
        ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
          (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2) := by
    have hfun : (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
        = fun x : Submission.BoseGases.X n =>
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x
                (Work.BoseBoxFock.slotDirVec i j)) ^ 2 := by
      funext x
      rw [hcpx (Work.BoseBoxFock.slotDirVec i j) x, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_ofReal]
      ring
    rw [hfun]
    exact (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2).mul
      (((hΦc.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  -- `pinDirChi` splits into its slot-`(i,j)` summands
  have hpin : Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := by
    rw [Work.BoseBoxFock.pinDirChi]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_finsetSum]
      exact fun j _ => Work.BoseBoxFock.integrableOn_abox_of_continuous hℓ (hcont i j)
    · intro i _
      exact Work.BoseBoxFock.integrableOn_abox_of_continuous hℓ
        (continuous_finsetSum _ (fun j _ => hcont i j))
  -- the per-slot bound
  have hslot (i : Fin n) : (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      ≤ C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
    pinDirChi_slot_le (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hΦc i hC₁
      (fun j => pinDirChi_slot_slice hℓ hΦc i j)
      (kinFormB_slot_fsT hℓ hΦc i).2 (kinFormB_slot_fsT hℓ hΦc i).1
      (mass_slice hℓ hΦc.continuous i)
  -- the two `Finset` identifications
  have hkinSum : (∑ i : Fin n, ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
      = Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  have hmassSum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      = (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, ← hℓdef, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := hpin
    _ ≤ ∑ i : Fin n, C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hslot i)
    _ = C₁ * ((∑ i : Fin n, ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
          + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = C₁ * (Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ)
          + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
        rw [hkinSum, hmassSum]

end Work.BoseBoxFock
