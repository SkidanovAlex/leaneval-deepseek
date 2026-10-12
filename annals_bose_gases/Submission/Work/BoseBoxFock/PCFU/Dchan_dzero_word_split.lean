import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Dchan_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.word_split_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.PCFU.Dchan_dzero_word_split`

The `(D)`-channel word split: the `d = 0` term of the low-momentum image sum, transported back
onto the state `Θ` at the price of the volume factor `ℓ⁶`.

The proof is the assembly described in `FINDING_Dchan_dzero_word_split_PROVABLE.md`: the
`Ĉ`-piece is `word_split_core` (proved in `PCFU/word_split_core.lean`), the remainder is split off
with the pointwise identity `∫_y χ(y)W₁(y−z) = Ĉ z` (`integral_ofReal`) together with the
Bochner linearity of the integral in both variables.  The integrability inputs are

* `∫_z χ_ℓ(z)·W₁(z)`-type terms: continuity + compact support of `χ_ℓ` times the bounded frame;
* `z ↦ χ_ℓ(z)·Ĉ z`: the already-proved `chiW1_smear_integrable` (the cancellation
  `(χ_ℓ ⋆ χ_ℓ) = ℓ³ convScale ℓ` of the renormalisation).
-/

/-! ## 0. Small integrability helpers -/

/-- **A measurable bounded function supported in a set of finite measure is integrable.** -/
private theorem integrable_of_bounded_support_bcs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- **Integrability of `x ↦ Θ x · ∫_z g x z`** from the joint integrability of
`(x,z) ↦ Θ x · g x z`, by Fubini and the hypothesis-free `integral_const_mul`. -/
private theorem integrable_of_joint_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Θ' : α → ℂ} {g : α → E3 → ℂ}
    (h : Integrable (fun p : α × E3 => Θ' p.1 * g p.1 p.2)
      (μ.prod (volume : Measure E3))) :
    Integrable (fun x => Θ' x * ∫ z, g x z) μ := by
  have h1 : Integrable (fun x : α => ∫ z : E3, Θ' x * g x z) μ := h.integral_prod_left
  exact h1.congr (Filter.Eventually.of_forall fun x => integral_const_mul _ _)

/-! ## 1. The generic word split

The target statement with the concrete parameters `ℓ = ellH v μ`, `κ = ((paramsAt μ a).d²·sideAt μ a)⁻¹`
and the concrete kernel `KχfrU v h μ fu N` replaced by abstract `ℓ`, `κ`, `Kf` (and the single
integrability hypothesis on `χ_ℓ·Kf`). -/

private theorem dchan_word_split_generic {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut}
    {ℓ κ Cθ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) (hCθ : 0 ≤ Cθ)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ Cθ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {Kf : E3 → ℂ}
    (hKint : Integrable (fun z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : E3,
              ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((ℓ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ z : E3,
                    ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                      * (Kf z - (∫ y : E3,
                          ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
                            * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)))
                      * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                            (Function.update x j z) : ℝ) : ℂ))) := by
  classical
  -- ### 0. The low-slot factor: measurability and a uniform bound.
  obtain ⟨hQm, D, hD0, hDb⟩ :=
    lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := 0) (ℓ := ℓ) (κ := κ) (Cθ := Cθ)
      (i := i) (j := j) hℓ hκ hCθ hΘm hΘb
  have hQzC : ∀ x : Submission.BoseGases.X n, AEStronglyMeasurable
      (fun z : E3 => ((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update x j z) : ℝ) : ℂ)) (volume : Measure E3) := fun x =>
    (Complex.measurable_ofReal.comp (hQm.comp
      (by fun_prop : Measurable fun z : E3 => Function.update x j z))).aestronglyMeasurable
  have hQzb : ∀ (x : Submission.BoseGases.X n) (z : E3),
      ‖((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update x j z) : ℝ) : ℂ)‖ ≤ D := fun x z =>
    le_trans (le_of_eq (RCLike.norm_ofReal _)) (hDb _)
  have hQupdC : AEStronglyMeasurable
      (fun p : Submission.BoseGases.X n × E3 => ((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update p.1 j p.2) : ℝ) : ℂ))
      ((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)) :=
    (Complex.measurable_ofReal.comp (hQm.comp
      (by fun_prop : Measurable fun p : Submission.BoseGases.X n × E3 =>
        Function.update p.1 j p.2))).aestronglyMeasurable
  have hQupdb : ∀ᵐ p ∂((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)),
      ‖((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update p.1 j p.2) : ℝ) : ℂ)‖ ≤ D :=
    Filter.Eventually.of_forall fun p => le_trans (le_of_eq (RCLike.norm_ofReal _)) (hDb _)
  -- ### 1. Integrability of the smeared window `z ↦ χ_ℓ(z)·Ĉ z`.
  have hχĈ : Integrable (fun z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
        * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)) := by
    refine ((chiW1_smear_integrable h hℓ).ofReal).congr
      (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [Work.BoseBoxFock.PCFU.wsc_chiLam_eq_chiScale]
    norm_cast
  -- ### 2. The pointwise coercion identity `∫_y ↑χ(y)·↑W₁(y−z) = ↑Ĉ z`.
  have hCcoeb : ∀ z : E3,
      (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ))
      = ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
          * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ) := by
    intro z
    have hcast : (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y
          * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
        = ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ) := integral_ofReal
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans hcast
    norm_cast
  -- ### 3. The `z`-level split, for each configuration `x`.
  have hsplit_z : ∀ x : Submission.BoseGases.X n,
      (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
            (Function.update x j z) : ℝ) : ℂ))
      = (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ))
        + (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ)) := by
    intro x
    have hA : Integrable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
            (Function.update x j z) : ℝ) : ℂ)) :=
      hKint.mul_bdd (hQzC x) (Filter.Eventually.of_forall (hQzb x))
    have hB : Integrable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
        * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
            (Function.update x j z) : ℝ) : ℂ)) :=
      hχĈ.mul_bdd (hQzC x) (Filter.Eventually.of_forall (hQzb x))
    have h1 : (∫ z : E3, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ)
        - ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ)))
        = (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ))
          - (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
              * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                  * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
              * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ)) :=
      integral_sub hA hB
    have h2 : (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ))
        = ∫ z : E3, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ)
          - ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [h2, h1]
    ring
  -- ### 4. Integrability at the outer level, by Fubini on `X n × ℝ³`.
  have hg2 : Integrable (fun z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
        * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))) :=
    (hKint.sub hχĈ).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hΘint : Integrable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
      (volume : Measure (Submission.BoseGases.X n)) :=
    integrable_of_bounded_support_bcs (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓ.le) (Complex.measurable_ofReal.comp hΘm)
      ⟨Cθ, fun x => le_trans (le_of_eq (RCLike.norm_ofReal (Θ x))) (hΘb x)⟩
      (fun x hx => hΘs (Function.mem_support.mpr fun h0 => hx (by simp [h0])))
  have hJoint2 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      ((Θ p.1 : ℝ) : ℂ) * ((((Work.BoseK15.corpusBox.chiLam ℓ p.2 : ℝ) : ℂ)
        * (Kf p.2 - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - p.2) : ℝ) : ℝ) : ℂ)))
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
            (Function.update p.1 j p.2) : ℝ) : ℂ)))
      ((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)) := by
    have hbase2 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
        ((Θ p.1 : ℝ) : ℂ) * (((Work.BoseK15.corpusBox.chiLam ℓ p.2 : ℝ) : ℂ)
          * (Kf p.2 - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - p.2) : ℝ) : ℝ) : ℂ))))
        ((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)) :=
      hΘint.mul_prod hg2
    exact (hbase2.mul_bdd hQupdC hQupdb).congr
      (Filter.Eventually.of_forall fun p => by ring)
  have hOut2 : Integrable (fun x : Submission.BoseGases.X n =>
      ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ)))
      (volume : Measure (Submission.BoseGases.X n)) :=
    integrable_of_joint_const_mul (Θ' := fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
      (g := fun (x : Submission.BoseGases.X n) (z : E3) =>
        ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ))
      hJoint2
  have hJoint3 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      ((Θ p.1 : ℝ) : ℂ) * ((((Work.BoseK15.corpusBox.chiLam ℓ p.2 : ℝ) : ℂ)
        * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - p.2) : ℝ) : ℝ) : ℂ))
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
            (Function.update p.1 j p.2) : ℝ) : ℂ)))
      ((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)) := by
    have hbase3 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
        ((Θ p.1 : ℝ) : ℂ) * (((Work.BoseK15.corpusBox.chiLam ℓ p.2 : ℝ) : ℂ)
          * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - p.2) : ℝ) : ℝ) : ℂ)))
        ((volume : Measure (Submission.BoseGases.X n)).prod (volume : Measure E3)) :=
      hΘint.mul_prod hχĈ
    exact (hbase3.mul_bdd hQupdC hQupdb).congr
      (Filter.Eventually.of_forall fun p => by ring)
  have hOut3 : Integrable (fun x : Submission.BoseGases.X n =>
      ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ)))
      (volume : Measure (Submission.BoseGases.X n)) :=
    integrable_of_joint_const_mul (Θ' := fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
      (g := fun (x : Submission.BoseGases.X n) (z : E3) =>
        ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ))
      hJoint3
  -- ### 5. The main term, from `word_split_core`.
  have hcore := Work.BoseBoxFock.PCFU.word_split_core (i := i) (j := j) hij (h := h)
    (fc := fc) (ℓ := ℓ) (κ := κ) (Cθ := Cθ) hℓ hκ hΘm hΘb hCθ hΘs
  -- ### 6. The outer split and the final assembly.
  have hLHS : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * Kf z
              * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ)))
      = (∫ x : Submission.BoseGases.X n,
            ((Θ x : ℝ) : ℂ)
              * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                  * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
                  * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
        + (∫ x : Submission.BoseGases.X n,
            ((Θ x : ℝ) : ℂ)
              * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                  * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
                  * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ))) := by
    refine Eq.trans ?_ (integral_add hOut2 hOut3)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hsplit_z x]
    ring
  have hR2 : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
              * (Kf z - (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
                  * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)))
              * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ)))
      = (∫ x : Submission.BoseGases.X n,
            ((Θ x : ℝ) : ℂ)
              * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                  * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
                  * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrArg (fun t => ((Θ x : ℝ) : ℂ) * t)
      (integral_congr_ae (Filter.Eventually.of_forall fun z => by
        dsimp only; rw [hCcoeb z]))
  have hfin : (∫ x : Submission.BoseGases.X n,
          ((Θ x : ℝ) : ℂ)
            * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                * (Kf z - ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                    * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ))
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                    (Function.update x j z) : ℝ) : ℂ)))
        + (∫ x : Submission.BoseGases.X n,
            ((Θ x : ℝ) : ℂ)
              * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                  * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
                  * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((ℓ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ z : E3,
                    ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                      * (Kf z - (∫ y : E3,
                          ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
                            * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)))
                      * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                            (Function.update x j z) : ℝ) : ℂ))) := by
    rw [hcore, hR2]
    ring
  exact hLHS.trans hfin

/-! ## 2. The target statement -/

theorem Dchan_dzero_word_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
                      (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ z : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                      * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                          - (∫ y : EuclideanSpace ℝ (Fin 3),
                              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
                                * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                                    (y - z) : ℝ) : ℂ)))
                      * ((Work.BoseBoxFix.lowSlot fc
                            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                            (Work.BoseBoxFock.ellH v μ) j
                            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                            (Function.update x j z) : ℝ) : ℂ))) := by
  obtain ⟨C0, hC0⟩ := hΘb
  have hCθ : 0 ≤ max C0 0 := le_max_right _ _
  have hΘb' : ∀ x, |Θ x| ≤ max C0 0 := fun x => le_trans (hC0 x) (le_max_left _ _)
  refine dchan_word_split_generic (i := i) (j := j) hij (h := h) (fc := fc)
    (ℓ := Work.BoseBoxFock.ellH v μ)
    (κ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Cθ := max C0 0) hℓ hκ hCθ hΘm hΘb' hΘs ?_
  -- the single analytic input: `χ_ℓ · KχfrU` is integrable
  have hχcs : HasCompactSupport (fun z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)) :=
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_left
      (g := fun t : ℝ => ((t : ℝ) : ℂ)) (by simp)
  have hχcont : Continuous (fun z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Submission.BoseGases.chi_continuous.comp (by fun_prop))
  exact (hχcont.mul (continuous_KχfrU v h μ fu N)).integrable_of_hasCompactSupport
    (hχcs.mul_right (f' := fun z : E3 => Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z))

end Work.BoseBoxFock.PCFU
