import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PairGc21Aux` — the box measure theory of the clean `pairG21` fibre

The clean fibre `pairGc21 ℓ p hp Θ₀ A u y` of `Work.BoseBoxFock.pairGCore` is the *set* integral

    ∫ z in ((boxL ℓ) ×ˢ (boxL ℓ)) ×ˢ (boxPiSet P12 ℓ),
        star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2
          * Θ₀ (insertCoord2 p y u z.2)

over the "triple box".  This module collects the measure theory of that representation:

* the triple box `triBox`, its measurability and compactness;
* the full membership characterisation `insertCoord2_mem_abox_iff'` of an inserted configuration
  (the pointwise identity that factorises the `abox`-indicator);
* the **measure preserving equivalence** `insEquiv` identifying the triple box with the
  `n`-particle box, and the two change-of-variable identities
  `integral_abox_eq_integral_triBox` (Bochner) and `lintegral_abox_eq_lintegral_triBox`
  (for `ℝ≥0∞`-valued integrands);
* the Fubini identity `lintegral_triBox_snd` for integrands depending only on the `P12`-slot;
* the concrete factorisations consumed by the `L²` and Dirichlet bounds of `pairGc21_core`:
  `lintegral_abox_ofReal_sq` (the `pinL2`-side), `lintegral_triBox_ofReal_sq` (the `memY21`-side)
  and `lintegral_triBox_ofReal_fderiv_sum` (the `dirY21`-side), together with the integrability
  facts needed to pass between the Bochner and the `ℝ≥0∞` formulation.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The triple box -/

/-- **The triple box of the clean `pairG21` fibre**: the two kernel slots `p.1`, `p.2` and the
remaining `n - 2` coordinates all run over the one-particle box. -/
def triBox {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) :
    Set ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :=
  ((boxL ℓ) ×ˢ (boxL ℓ)) ×ˢ (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)

theorem triBox_measurableSet {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) :
    MeasurableSet (triBox ℓ p) := by
  refine MeasurableSet.prod ?_ (MeasurableSet.pi (s := Set.univ)
    (t := fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxL ℓ) Set.countable_univ ?_)
  · exact (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
  · intro i _
    exact Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ

theorem isCompact_triBox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    IsCompact (triBox ℓ p) :=
  ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod (Work.BoseK15.corpusBox.boxL_compact ℓ)).prod
    (isCompact_boxPiSet hℓ)

/-- A coordinate of the inserted configuration. -/
lemma insertCoord2_apply_self {n : ℕ} (p : Fin n × Fin n) (a b : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p a b x' p.1 = a := by
  simp [insertCoord2_eq]

lemma insertCoord2_apply_other {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a b : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p a b x' p.2 = b := by
  simp [insertCoord2_eq, hp.symm]

lemma insertCoord2_apply_ne {n : ℕ} {p : Fin n × Fin n} {i : Fin n} (h1 : i ≠ p.1)
    (h2 : i ≠ p.2) (a b : E3) (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p a b x' i = x' ⟨i, h1, h2⟩ := by
  simp [insertCoord2_eq, h1, h2]

/-- **Full membership characterisation of an inserted configuration. -/
theorem insertCoord2_mem_abox_iff' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) (a b : E3) (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p a b x' ∈ Submission.BoseGases.abox n ℓ ↔
      a ∈ boxL ℓ ∧ b ∈ boxL ℓ ∧ x' ∈ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ := by
  rw [Submission.BoseGases.mem_abox_iff, mem_boxPiSet, ← corpusBox_boxL_eq_acube hℓ]
  constructor
  · intro h
    exact ⟨by simpa using h p.1, by simpa [hp, hp.symm] using h p.2,
      fun k => by simpa [insertCoord2_eq, k.2.1, k.2.2] using h k.1⟩
  · rintro ⟨ha, hb, hx⟩ i
    by_cases h1 : i = p.1
    · simpa [insertCoord2_eq, h1] using ha
    · by_cases h2 : i = p.2
      · simpa [insertCoord2_eq, h1, h2, hp, hp.symm] using hb
      · simpa [insertCoord2_eq, h1, h2] using hx ⟨i, h1, h2⟩

/-- The insertion of the two coordinates is continuous. -/
lemma continuous_insertCoord2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Continuous (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      insertCoord2 p z.1.1 z.1.2 z.2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have : (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        insertCoord2 p z.1.1 z.1.2 z.2 k) = fun z => z.1.1 := by
      funext z; rw [show insertCoord2 p z.1.1 z.1.2 z.2 k = z.1.1 from by
        simp [insertCoord2_eq, h1]]
    rw [this]; exact continuous_fst.fst
  · by_cases h2 : k = p.2
    · have : (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          insertCoord2 p z.1.1 z.1.2 z.2 k) = fun z => z.1.2 := by
        funext z; rw [show insertCoord2 p z.1.1 z.1.2 z.2 k = z.1.2 from by
          simp [insertCoord2_eq, h1, h2, hp, hp.symm]]
      rw [this]; exact continuous_fst.snd
    · have : (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          insertCoord2 p z.1.1 z.1.2 z.2 k) = fun z => z.2 ⟨k, h1, h2⟩ := by
        funext z; rw [show insertCoord2 p z.1.1 z.1.2 z.2 k = z.2 ⟨k, h1, h2⟩ from by
          simp [insertCoord2_eq, h1, h2]]
      rw [this]
      exact (continuous_apply _).comp continuous_snd

lemma measurable_insertCoord2_apply {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      insertCoord2 p z.1.1 z.1.2 z.2) :=
  (continuous_insertCoord2 p hp).measurable

/-- The insertion map with the two parameters fixed is continuous. -/
lemma continuous_insertCoord2_fixed {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (a b : E3) :
    Continuous (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      insertCoord2 p a b x') := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have : (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
        insertCoord2 p a b x' k) = fun _ => a := by
      funext x'; rw [show insertCoord2 p a b x' k = a from by simp [insertCoord2_eq, h1]]
    rw [this]; exact continuous_const
  · by_cases h2 : k = p.2
    · have : (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
          insertCoord2 p a b x' k) = fun _ => b := by
        funext x'; rw [show insertCoord2 p a b x' k = b from by
          simp [insertCoord2_eq, h1, h2, hp, hp.symm]]
      rw [this]; exact continuous_const
    · have : (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
          insertCoord2 p a b x' k) = fun x' => x' ⟨k, h1, h2⟩ := by
        funext x'; rw [show insertCoord2 p a b x' k = x' ⟨k, h1, h2⟩ from by
          simp [insertCoord2_eq, h1, h2]]
      rw [this]
      exact (continuous_apply _)

/-- The update identity: replacing the two inserted coordinates by `y`, `u` gives the insertion
of `(y, u)`. -/
lemma insertCoord2_update {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a b y u : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    Function.update (Function.update (insertCoord2 p a b x') p.1 y) p.2 u
      = insertCoord2 p y u x' := by
  funext k
  rw [Function.update_apply]
  by_cases h2 : k = p.2
  · rw [if_pos h2, h2, insertCoord2_apply_other hp]
  · rw [if_neg h2, Function.update_apply]
    by_cases h1 : k = p.1
    · rw [if_pos h1, h1, insertCoord2_apply_self]
    · rw [if_neg h1, insertCoord2_apply_ne h1 h2, insertCoord2_apply_ne h1 h2]

/-! ## 2. The measure preserving equivalence -/

/-- The complement of the two removed indices is a two element type. -/
private lemma pgcIdxFact {n : ℕ} {i j : Fin n}
    (k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) : (k : Fin n) = i ∨ (k : Fin n) = j := by
  by_cases h : (k : Fin n) = i
  · exact Or.inl h
  · exact Or.inr (by by_contra hj; exact k.2 ⟨h, hj⟩)

/-- The complement of the two removed indices, as a finset, is exactly the pair `{i, j}`. -/
private lemma pgcIdxUniv {n : ℕ} {i j : Fin n} :
    (Finset.univ : Finset {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) = {⟨i, by simp⟩, ⟨j, by simp⟩} := by
  ext k
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff, Subtype.ext_iff]
  exact pgcIdxFact k

/-- The two element type `{k : Fin n // ¬(k ≠ i ∧ k ≠ j)}` is, for the product measure,
identified with `E × E` by evaluation at `i` and at `j`. -/
private noncomputable def pgcTwoEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasurableSpace E] :
    ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E) ≃ᵐ (E × E) where
  toFun y := (y ⟨i, by simp⟩, y ⟨j, by simp⟩)
  invFun p := fun k => if (k : Fin n) = i then p.1 else p.2
  left_inv := by
    intro y
    funext k
    dsimp only
    by_cases h : (k : Fin n) = i
    · rw [if_pos h]
      exact congrArg y (Subtype.ext h.symm)
    · rw [if_neg h]
      have h' : k = ⟨j, by simp⟩ := by
        refine Subtype.ext ?_
        by_contra hj
        exact k.2 ⟨h, hj⟩
      exact (congrArg y h').symm
  right_inv := by
    intro p
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [if_pos (show ((⟨i, by simp⟩ : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) : Fin n) = i from rfl)]
    · dsimp only
      rw [if_neg (show ¬(((⟨j, by simp⟩ : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) : Fin n) = i)
        from fun h => hij h.symm)]
  measurable_toFun := by
    exact (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  measurable_invFun := by
    refine measurable_pi_iff.2 (fun k => ?_)
    by_cases h : (k : Fin n) = i
    · simpa [h] using measurable_fst
    · simpa [h] using measurable_snd

private lemma pgcTwoEq_symm_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasurableSpace E] (a b : E) (k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) :
    (pgcTwoEq hij E).symm (a, b) k = if (k : Fin n) = i then a else b := by
  dsimp only [pgcTwoEq]
  rfl

private theorem pgcMeasurePreservingTwoEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    MeasurePreserving (pgcTwoEq hij E) volume volume := by
  refine ⟨(pgcTwoEq hij E).measurable, ?_⟩
  refine (Measure.prod_eq (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (μν := Measure.map (pgcTwoEq hij E) volume) ?_).symm
  intro s t hs ht
  rw [Measure.map_apply (pgcTwoEq hij E).measurable (hs.prod ht)]
  have hset : (pgcTwoEq hij E) ⁻¹' (s ×ˢ t)
      = Set.univ.pi (fun k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)} =>
          if (k : Fin n) = i then s else t) := by
    ext y
    dsimp only [pgcTwoEq]
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      rcases pgcIdxFact k with hk | hk
      · rw [if_pos hk]
        simpa [show k = ⟨i, by simp⟩ from Subtype.ext hk] using h1
      · rw [if_neg (show ¬((k : Fin n) = i) from fun hh => hij ((hk ▸ hh).symm))]
        simpa [show k = ⟨j, by simp⟩ from Subtype.ext hk] using h2
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using h ⟨i, by simp⟩
      · simpa [show (j : Fin n) ≠ i from fun hh => hij hh.symm] using h ⟨j, by simp⟩
  rw [hset,
    show (volume : Measure ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)) = Measure.pi (fun _ => volume)
      from rfl,
    Measure.pi_pi]
  rw [pgcIdxUniv, Finset.prod_pair (fun h => hij (Subtype.ext_iff.1 h))]
  simp [show (j : Fin n) ≠ i from fun hh => hij hh.symm]

/-- Splitting off the coordinates `i` and `j`: the space of functions on `Fin n` is the product of
the functions on the remaining indices with the values at `i` and at `j` (a two point type). -/
private noncomputable def pgcSplitEquiv {n : ℕ} {i j : Fin n} (E : Type*) [MeasurableSpace E] :
    (Fin n → E) ≃ᵐ
      (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => E) (fun k => k ≠ i ∧ k ≠ j)

private lemma pgcSplitEquiv_symm_apply {n : ℕ} {i j : Fin n} (E : Type*) [MeasurableSpace E]
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E)
    (y : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E) (k : Fin n) :
    (pgcSplitEquiv (i := i) (j := j) E).symm (x', y) k
      = if h : k ≠ i ∧ k ≠ j then x' ⟨k, h⟩ else y ⟨k, h⟩ := by
  dsimp only [pgcSplitEquiv]
  rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]

/-- The measure preserving equivalence `((x', a), b) ↦ (a at i, b at j, x' elsewhere)`. -/
private noncomputable def pgcΦ {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasurableSpace E] :
    ((({k : Fin n // k ≠ i ∧ k ≠ j} → E) × E) × E) ≃ᵐ (Fin n → E) :=
  ((MeasurableEquiv.prodAssoc).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E))
      (pgcTwoEq hij E).symm)).trans
    (pgcSplitEquiv (i := i) (j := j) E).symm

private lemma pgcΦ_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*) [MeasurableSpace E]
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E) (a b : E) (k : Fin n) :
    pgcΦ hij E ((x', a), b) k
      = if h : k = i then a else if h' : k = j then b else x' ⟨k, h, h'⟩ := by
  have h1 : pgcΦ hij E ((x', a), b)
      = (pgcSplitEquiv (i := i) (j := j) E).symm (x', (pgcTwoEq hij E).symm (a, b)) := rfl
  rw [h1, pgcSplitEquiv_symm_apply]
  simp only [pgcTwoEq_symm_apply]
  by_cases hki : k = i
  · rw [dif_neg (fun h => h.1 hki), if_pos hki, dif_pos hki]
  · by_cases hkj : k = j
    · rw [dif_neg (fun h => h.2 hkj), if_neg hki, dif_neg hki, dif_pos hkj]
    · rw [dif_pos ⟨hki, hkj⟩, dif_neg hki, dif_neg hkj]

private theorem pgcΦ_measurePreserving {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    MeasurePreserving (pgcΦ hij E) volume volume := by
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc) :
      ((({k : Fin n // k ≠ i ∧ k ≠ j} → E) × E) × E) →
        (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × (E × E))) volume volume :=
    volume_preserving_prodAssoc
  have h2 : MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E))
        (pgcTwoEq hij E).symm)) volume volume := by
    rw [show (⇑(MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E)) (pgcTwoEq hij E).symm) :
            (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × (E × E)) →
          (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)))
        = Prod.map (id : ({k : Fin n // k ≠ i ∧ k ≠ j} → E) →
            ({k : Fin n // k ≠ i ∧ k ≠ j} → E)) (⇑(pgcTwoEq hij E).symm) from rfl]
    exact MeasurePreserving.prod (μa := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E)))
      (μc := (volume : Measure (E × E)))
      (μb := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E)))
      (μd := (volume : Measure ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)))
      (MeasurePreserving.id _) ((pgcMeasurePreservingTwoEq hij E).symm (pgcTwoEq hij E))
  have h3 : MeasurePreserving (⇑(pgcSplitEquiv (i := i) (j := j) E).symm) volume volume :=
    (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => E) (fun k => k ≠ i ∧ k ≠ j)).symm
      (pgcSplitEquiv (i := i) (j := j) E)
  have h := h3.comp (h2.comp h1)
  simpa only [pgcΦ, MeasurableEquiv.coe_trans, Function.comp_assoc] using h

/-- **The measure preserving equivalence at the heart of the clean `pairG21` fibre**: it sends
`((a, b), x')` to the configuration with `a` at slot `p.1`, `b` at slot `p.2` and `x'`
elsewhere. -/
noncomputable def insEquiv {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) ≃ᵐ (Fin n → E3) :=
  (MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodAssoc.symm)).trans (pgcΦ hp E3)

lemma insEquiv_apply {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a b : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insEquiv p hp ((a, b), x') = insertCoord2 p a b x' := by
  funext k
  show pgcΦ hp E3 ((x', a), b) k = _
  rw [pgcΦ_apply]
  rfl

theorem insEquiv_measurePreserving {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    MeasurePreserving (insEquiv p hp)
      (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))) volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodComm :
        (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) ≃ᵐ
          ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3))
      (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)))
      (volume : Measure (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3))) := by
    refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
    exact Measure.prod_swap
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) ≃ᵐ
          (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3) × E3)
      (volume : Measure (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3)))
      (volume : Measure ((({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3) × E3)) :=
    (volume_preserving_prodAssoc (α₁ := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)
      (β₁ := E3) (γ₁ := E3)).symm _
  have h3 := (pgcΦ_measurePreserving hp E3)
  exact h3.comp (h2.comp h1)

/-- The equivalence maps the triple box onto the `n`-particle box. -/
theorem insEquiv_image_triBox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) :
    insEquiv p hp '' triBox ℓ p = Submission.BoseGases.abox n ℓ := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [triBox, Set.mem_prod, Set.mem_prod] at hz
    obtain ⟨⟨ha, hb⟩, hx⟩ := hz
    rw [insEquiv_apply]
    exact (insertCoord2_mem_abox_iff' hℓ hp z.1.1 z.1.2 z.2).mpr ⟨ha, hb, hx⟩
  · intro hx
    have hmem : ∀ k : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}, x k.1 ∈ boxL ℓ := by
      intro k
      have h1 := (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx k.1
      rwa [← corpusBox_boxL_eq_acube hℓ] at h1
    have h1 : x p.1 ∈ boxL ℓ := by
      have := (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx p.1
      rwa [← corpusBox_boxL_eq_acube hℓ] at this
    have h2 : x p.2 ∈ boxL ℓ := by
      have := (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx p.2
      rwa [← corpusBox_boxL_eq_acube hℓ] at this
    refine ⟨((x p.1, x p.2), fun k => x k.1), ?_, ?_⟩
    · rw [triBox, Set.mem_prod, Set.mem_prod]
      exact ⟨⟨h1, h2⟩, (mem_boxPiSet).mpr hmem⟩
    · rw [insEquiv_apply]
      funext k
      by_cases hk1 : k = p.1
      · rw [hk1, insertCoord2_apply_self]
      · by_cases hk2 : k = p.2
        · rw [hk2, insertCoord2_apply_other hp]
        · rw [insertCoord2_apply_ne hk1 hk2]

/-! ## 3. The two change-of-variable identities -/

/-- **Bochner change of variables for the box.**  The integral of any (complex-valued) function
over the `n`-particle box equals the integral over the triple box of the transported integrand. -/
theorem integral_abox_eq_integral_triBox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) (g : Xn n → ℂ) :
    (∫ x in Submission.BoseGases.abox n ℓ, g x)
      = ∫ z in triBox ℓ p, g (insertCoord2 p z.1.1 z.1.2 z.2) := by
  have himg := insEquiv_image_triBox hℓ p hp
  have hmp := insEquiv_measurePreserving p hp
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ, g x)
      = ∫ x, (Submission.BoseGases.abox n ℓ).indicator g x :=
    (integral_indicator (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_measurable n ℓ) (f := g)).symm
  have h2 : (∫ x, (Submission.BoseGases.abox n ℓ).indicator g x)
      = ∫ z, (Submission.BoseGases.abox n ℓ).indicator g (insEquiv p hp z) :=
    (hmp.integral_comp' _).symm
  have h3 : (fun z => (Submission.BoseGases.abox n ℓ).indicator g (insEquiv p hp z))
      = (triBox ℓ p).indicator (fun z => g (insertCoord2 p z.1.1 z.1.2 z.2)) := by
    funext z
    by_cases hz : z ∈ triBox ℓ p
    · have hz' : insEquiv p hp z ∈ Submission.BoseGases.abox n ℓ := by
        rw [← himg]; exact ⟨z, hz, rfl⟩
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz', insEquiv_apply]
    · have hz' : insEquiv p hp z ∉ Submission.BoseGases.abox n ℓ := by
        intro hh
        rw [← himg] at hh
        obtain ⟨w, hw, hwe⟩ := hh
        exact hz ((insEquiv p hp).injective hwe ▸ hw)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  rw [h1, h2, h3, integral_indicator (s := triBox ℓ p) (triBox_measurableSet ℓ p)]

/-- **`ℝ≥0∞`-valued change of variables for the box.** -/
theorem lintegral_abox_eq_lintegral_triBox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) (F : Xn n → ℝ≥0∞) :
    (∫⁻ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫⁻ z in triBox ℓ p, F (insertCoord2 p z.1.1 z.1.2 z.2) := by
  have himg := insEquiv_image_triBox hℓ p hp
  have hmp := insEquiv_measurePreserving p hp
  have h1 : (∫⁻ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫⁻ x, (Submission.BoseGases.abox n ℓ).indicator F x :=
    (lintegral_indicator (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_measurable n ℓ) F).symm
  have h2 : (∫⁻ x, (Submission.BoseGases.abox n ℓ).indicator F x)
      = ∫⁻ z, (Submission.BoseGases.abox n ℓ).indicator F (insEquiv p hp z) := by
    have hmap : Measure.map (⇑(insEquiv p hp))
        (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)))
        = (volume : Measure (Xn n)) := hmp.map_eq
    have := lintegral_map_equiv (μ := (volume : Measure ((E3 × E3) ×
      ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))))
      ((Submission.BoseGases.abox n ℓ).indicator F) (insEquiv p hp)
    rw [hmap] at this
    exact this
  have h3 : (fun z => (Submission.BoseGases.abox n ℓ).indicator F (insEquiv p hp z))
      = (triBox ℓ p).indicator (fun z => F (insertCoord2 p z.1.1 z.1.2 z.2)) := by
    funext z
    by_cases hz : z ∈ triBox ℓ p
    · have hz' : insEquiv p hp z ∈ Submission.BoseGases.abox n ℓ := by
        rw [← himg]; exact ⟨z, hz, rfl⟩
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz', insEquiv_apply]
    · have hz' : insEquiv p hp z ∉ Submission.BoseGases.abox n ℓ := by
        intro hh
        rw [← himg] at hh
        obtain ⟨w, hw, hwe⟩ := hh
        exact hz ((insEquiv p hp).injective hwe ▸ hw)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  rw [h1, h2, h3, lintegral_indicator (s := triBox ℓ p) (triBox_measurableSet ℓ p)]

/-! ## 4. Fubini in the `(a, b)`-slots -/

/-- The `(a, b)`-slots of the triple box have volume `ℓ⁶`. -/
theorem volume_prod_boxL (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (volume : Measure (E3 × E3)) (boxL ℓ ×ˢ boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) ^ 2 := by
  show (Measure.prod (volume : Measure E3) (volume : Measure E3)) (boxL ℓ ×ˢ boxL ℓ) = _
  rw [Measure.prod_prod, Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ, ← pow_two]

/-- `ofReal`-form of the box volume. -/
theorem ofReal_volume_boxL (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (volume : Measure E3) (boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) :=
  Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ

/-- **Fubini for integrands which only see the `P12`-slot**: the first two slots contribute
exactly the volume `ℓ⁶` of the box squared. -/
theorem lintegral_triBox_snd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {h : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z in triBox ℓ p, h z.2)
      = ENNReal.ofReal (ℓ ^ 3) ^ 2
          * ∫⁻ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ, h x'' := by
  have hres : (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict
      (triBox ℓ p)
      = (((volume : Measure E3).restrict (boxL ℓ)).prod
            ((volume : Measure E3).restrict (boxL ℓ))).prod
          ((volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)).restrict
            (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)) := by
    rw [triBox,
      show (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)))
        = (volume : Measure (E3 × E3)).prod (volume : Measure
            ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) from rfl,
      show (volume : Measure (E3 × E3)) = (volume : Measure E3).prod (volume : Measure E3)
        from rfl]
    rw [← Measure.prod_restrict, ← Measure.prod_restrict]
  have huniv : (((volume : Measure E3).restrict (boxL ℓ)).prod
      ((volume : Measure E3).restrict (boxL ℓ))) Set.univ = volume (boxL ℓ ×ˢ boxL ℓ) := by
    rw [show (Set.univ : Set (E3 × E3)) = Set.univ ×ˢ Set.univ from Set.univ_prod_univ.symm,
      Measure.prod_prod, Measure.restrict_apply_univ]
    rw [show (volume : Measure (E3 × E3)) = (volume : Measure E3).prod (volume : Measure E3)
        from rfl, Measure.prod_prod]
  rw [show (∫⁻ z in triBox ℓ p, h z.2)
      = ∫⁻ z, h z.2 ∂((volume : Measure ((E3 × E3) ×
            ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict (triBox ℓ p)) from rfl]
  rw [hres]
  rw [lintegral_prod (μ := ((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ)))
      (ν := (volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ))
      (f := fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) => h z.2)
      ((hh.comp measurable_snd).aemeasurable)]
  rw [show (∫⁻ x : E3 × E3, (∫⁻ y in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ, h (x, y).2)
        ∂(((volume : Measure E3).restrict (boxL ℓ)).prod
          ((volume : Measure E3).restrict (boxL ℓ))))
      = ∫⁻ x : E3 × E3, (∫⁻ y in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ, h y)
        ∂(((volume : Measure E3).restrict (boxL ℓ)).prod
          ((volume : Measure E3).restrict (boxL ℓ))) from
    lintegral_congr fun x => rfl]
  rw [lintegral_const, huniv, volume_prod_boxL ℓ hℓ]
  ring

/-! ## 5. The concrete factorisations -/

/-- The square of a continuous function of an inserted configuration is integrable over the box. -/
theorem integrableOn_sq_comp_continuous_insert {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3) :
    IntegrableOn (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ‖Θ₀ (insertCoord2 p y u x'')‖ ^ 2) (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) := by
  have hK := isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ
  have hcont : Continuous (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ‖Θ₀ (insertCoord2 p y u x'')‖ ^ 2) :=
    ((hΘ₀.continuous.comp (continuous_insertCoord2_fixed p hp y u)).norm.pow 2)
  exact hcont.continuousOn.integrableOn_compact hK

/-- The derivative analogue of `integrableOn_sq_comp_continuous_insert`. -/
theorem integrableOn_fderiv_comp_continuous_insert {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3)
    (j : Fin 3) :
    IntegrableOn (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2)
      (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) := by
  have hK := isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ
  have h2 : Continuous (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      fderiv ℝ Θ₀ (insertCoord2 p y u x'')) :=
    (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord2_fixed p hp y u)
  have hcont : Continuous (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2) :=
    ((h2.clm_apply continuous_const).norm.pow 2)
  exact hcont.continuousOn.integrableOn_compact hK

/-- The `pinL2`-side factorisation: the `abox`-`ℝ≥0∞`-integral of `‖Θ₀‖²` is the
`ofReal` of `pinL2`. -/
theorem lintegral_abox_ofReal_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫⁻ x in Submission.BoseGases.abox n ℓ, ENNReal.ofReal (‖Θ₀ x‖ ^ 2))
      = ENNReal.ofReal (pinL2 ℓ Θ₀) := by
  rw [pinL2]
  refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · have hK := Submission.BoseGases.abox_compact n hℓ
    exact (hΘ₀.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  · exact Filter.Eventually.of_forall fun x => by positivity

/-- The `memY21`-side factorisation. -/
theorem lintegral_triBox_ofReal_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3) :
    (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖Θ₀ (insertCoord2 p y u z.2)‖ ^ 2))
      = ENNReal.ofReal (ℓ ^ 3) ^ 2 * ENNReal.ofReal (memY21 ℓ p Θ₀ y u) := by
  have hmeas : Measurable (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ENNReal.ofReal (‖Θ₀ (insertCoord2 p y u x'')‖ ^ 2)) :=
    ((hΘ₀.continuous.comp (continuous_insertCoord2_fixed p hp y u)).norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_triBox_snd hℓ p hmeas]
  congr 1
  rw [memY21]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrableOn_sq_comp_continuous_insert hℓ hp hΘ₀ y u)
    (Filter.Eventually.of_forall fun x => by positivity)).symm

/-- The one-slot `dirY21`-integral, `ℝ≥0∞` form. -/
theorem lintegral_triBox_ofReal_fderiv {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3) (j : Fin 3) :
    (∫⁻ z in triBox ℓ p,
        ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2))
      = ENNReal.ofReal (ℓ ^ 3) ^ 2 * ENNReal.ofReal
          (∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            ‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2) := by
  have hmeas : Measurable (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
      ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2)) := by
    have h2 : Continuous (fun x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
        fderiv ℝ Θ₀ (insertCoord2 p y u x'')) :=
      (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord2_fixed p hp y u)
    exact ((h2.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_triBox_snd hℓ p hmeas]
  congr 1
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrableOn_fderiv_comp_continuous_insert hℓ hp hΘ₀ y u j)
    (Filter.Eventually.of_forall fun x => by positivity)).symm

/-- The `dirY21`-side factorisation, as a sum over the three derivatives. -/
theorem lintegral_triBox_ofReal_fderiv_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3) :
    (∑ j : Fin 3, ∫⁻ z in triBox ℓ p,
        ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2))
      = ENNReal.ofReal (ℓ ^ 3) ^ 2 * ENNReal.ofReal (dirY21 ℓ p Θ₀ y u) := by
  rw [Finset.sum_congr rfl (fun j _ => lintegral_triBox_ofReal_fderiv hℓ p hp hΘ₀ y u j)]
  rw [← Finset.mul_sum]
  congr 1
  rw [dirY21]
  exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg fun x => by positivity)).symm

end Work.BoseBoxFock
