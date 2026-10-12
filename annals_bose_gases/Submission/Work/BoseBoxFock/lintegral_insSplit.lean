import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Splitting a product integral along two coordinates

For `n : ℕ` and distinct `i j : Fin n`, the product space `Fin n → E` (with its product
Lebesgue measure) is, up to a measure preserving bijection, the product of

* the space of functions on the remaining indices `{k // k ≠ i ∧ k ≠ j}`,
* the value at `i`, and
* the value at `j`.

Consequently the integral of a nonnegative measurable function `g` over `Fin n → E` equals the
iterated integral over the value at `i`, the value at `j` and the remaining coordinates.

This file provides the measure preserving equivalence `Φeq` realising this splitting together with
the pointwise formula for it, and deduces the integration identity
`Work.BoseBoxFock.lintegral_insSplit`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- The complement of the two removed indices is a two element type: every element `k` of
`{k : Fin n // ¬(k ≠ i ∧ k ≠ j)}` satisfies `k = i` or `k = j`. -/
private lemma compatIdxFact {n : ℕ} {i j : Fin n}
    (k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) : (k : Fin n) = i ∨ (k : Fin n) = j := by
  by_cases h : (k : Fin n) = i
  · exact Or.inl h
  · exact Or.inr (by by_contra hj; exact k.2 ⟨h, hj⟩)

/-- The complement of the two removed indices, as a finset, is exactly the pair `{i, j}`. -/
private lemma compatIdx_univ {n : ℕ} {i j : Fin n} :
    (Finset.univ : Finset {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) = {⟨i, by simp⟩, ⟨j, by simp⟩} := by
  ext k
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff, Subtype.ext_iff]
  exact compatIdxFact k

/-- The two element type `{k : Fin n // ¬(k ≠ i ∧ k ≠ j)}` is, for the product measure,
identified with `E × E` by evaluation at `i` and at `j`. -/
private noncomputable def twoEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
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

private lemma twoEq_symm_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasurableSpace E] (a b : E) (k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)}) :
    (twoEq hij E).symm (a, b) k = if (k : Fin n) = i then a else b := by
  dsimp only [twoEq]
  rfl

theorem measurePreserving_twoEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    MeasurePreserving (twoEq hij E) volume volume := by
  refine ⟨(twoEq hij E).measurable, ?_⟩
  refine (Measure.prod_eq (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (μν := Measure.map (twoEq hij E) volume) ?_).symm
  intro s t hs ht
  rw [Measure.map_apply (twoEq hij E).measurable (hs.prod ht)]
  have hset : (twoEq hij E) ⁻¹' (s ×ˢ t)
      = Set.univ.pi (fun k : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)} =>
          if (k : Fin n) = i then s else t) := by
    ext y
    dsimp only [twoEq]
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      rcases compatIdxFact k with hk | hk
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
  rw [compatIdx_univ, Finset.prod_pair (fun h => hij (Subtype.ext_iff.1 h))]
  simp [show (j : Fin n) ≠ i from fun hh => hij hh.symm]

/-- Splitting off the coordinates `i` and `j`: the space of functions on `Fin n` is the product of
the functions on the remaining indices with the values at `i` and at `j` (a two point type). -/
private noncomputable def splitEquiv {n : ℕ} {i j : Fin n} (E : Type*) [MeasurableSpace E] :
    (Fin n → E) ≃ᵐ
      (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => E) (fun k => k ≠ i ∧ k ≠ j)

private lemma splitEquiv_symm_apply {n : ℕ} {i j : Fin n} (E : Type*) [MeasurableSpace E]
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E)
    (y : {k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E) (k : Fin n) :
    (splitEquiv (i := i) (j := j) E).symm (x', y) k
      = if h : k ≠ i ∧ k ≠ j then x' ⟨k, h⟩ else y ⟨k, h⟩ := by
  dsimp only [splitEquiv]
  rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]

/-- The measure preserving equivalence underlying the splitting: it sends `((x', a), b)` to the
function which is `a` at `i`, `b` at `j` and `x'` on the remaining coordinates. -/
private noncomputable def Φeq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasurableSpace E] :
    ((({k : Fin n // k ≠ i ∧ k ≠ j} → E) × E) × E) ≃ᵐ (Fin n → E) :=
  ((MeasurableEquiv.prodAssoc).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E))
      (twoEq hij E).symm)).trans
    (splitEquiv (i := i) (j := j) E).symm

private lemma Φeq_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*) [MeasurableSpace E]
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E) (a b : E) (k : Fin n) :
    Φeq hij E ((x', a), b) k
      = if h : k = i then a else if h' : k = j then b else x' ⟨k, h, h'⟩ := by
  have h1 : Φeq hij E ((x', a), b)
      = (splitEquiv (i := i) (j := j) E).symm (x', (twoEq hij E).symm (a, b)) := rfl
  rw [h1, splitEquiv_symm_apply]
  simp only [twoEq_symm_apply]
  by_cases hki : k = i
  · rw [dif_neg (fun h => h.1 hki), if_pos hki, dif_pos hki]
  · by_cases hkj : k = j
    · rw [dif_neg (fun h => h.2 hkj), if_neg hki, dif_neg hki, dif_pos hkj]
    · rw [dif_pos ⟨hki, hkj⟩, dif_neg hki, dif_neg hkj]

private theorem Φeq_measurePreserving {n : ℕ} {i j : Fin n} (hij : i ≠ j) (E : Type*)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    MeasurePreserving (Φeq hij E) volume volume := by
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc) :
      ((({k : Fin n // k ≠ i ∧ k ≠ j} → E) × E) × E) →
        (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × (E × E))) volume volume :=
    volume_preserving_prodAssoc
  have h2 : MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E))
        (twoEq hij E).symm)) volume volume := by
    rw [show (⇑(MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl ({k : Fin n // k ≠ i ∧ k ≠ j} → E)) (twoEq hij E).symm) :
            (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × (E × E)) →
          (({k : Fin n // k ≠ i ∧ k ≠ j} → E) × ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)))
        = Prod.map (id : ({k : Fin n // k ≠ i ∧ k ≠ j} → E) →
            ({k : Fin n // k ≠ i ∧ k ≠ j} → E)) (⇑(twoEq hij E).symm) from rfl]
    exact MeasurePreserving.prod (μa := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E)))
      (μc := (volume : Measure (E × E)))
      (μb := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E)))
      (μd := (volume : Measure ({k : Fin n // ¬(k ≠ i ∧ k ≠ j)} → E)))
      (MeasurePreserving.id _) ((measurePreserving_twoEq hij E).symm (twoEq hij E))
  have h3 : MeasurePreserving (⇑(splitEquiv (i := i) (j := j) E).symm) volume volume :=
    (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => E) (fun k => k ≠ i ∧ k ≠ j)).symm
      (splitEquiv (i := i) (j := j) E)
  have h := h3.comp (h2.comp h1)
  simpa only [Φeq, MeasurableEquiv.coe_trans, Function.comp_assoc] using h

/-- Abbreviation for the ambient Euclidean space of the statement. -/
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Abbreviation for the space of functions on the remaining coordinates. -/
private abbrev A3 {n : ℕ} {i j : Fin n} := {k : Fin n // k ≠ i ∧ k ≠ j} → EuclideanSpace ℝ (Fin 3)

theorem lintegral_insSplit {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : (Fin n → EuclideanSpace ℝ (Fin 3)) → ENNReal) (hg : AEMeasurable g) :
    (∫⁻ x, g x)
      = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → EuclideanSpace ℝ (Fin 3),
          ∫⁻ a, ∫⁻ b,
            g (fun k => if h : k = i then a else if h' : k = j then b else x' ⟨k, h, h'⟩) := by
  have hΦ : MeasurePreserving (Φeq hij E3) volume volume := Φeq_measurePreserving hij _
  have hform : ∀ (x' : A3 (i := i) (j := j)) (a b : E3),
      Φeq hij E3 ((x', a), b)
        = fun k => if h : k = i then a else if h' : k = j then b else x' ⟨k, h, h'⟩ :=
    fun x' a b => funext fun k => Φeq_apply hij _ x' a b k
  have hA : AEMeasurable (fun w : (A3 (i := i) (j := j) × E3) × E3 => g (Φeq hij E3 w))
      ((volume : Measure (A3 (i := i) (j := j) × E3)).prod (volume : Measure E3)) := by
    have h1 : AEMeasurable g (Measure.map (⇑(Φeq hij E3)) volume) := by
      rw [hΦ.map_eq]; exact hg
    exact h1.comp_measurable (Φeq hij E3).measurable
  have hG : AEMeasurable (fun y : A3 (i := i) (j := j) × E3 => ∫⁻ b, g (Φeq hij E3 (y, b)))
      volume := by
    have h2 : AEMeasurable (fun w : (A3 (i := i) (j := j) × E3) × E3 => g (Φeq hij E3 w))
        ((volume : Measure (A3 (i := i) (j := j) × E3)).prod (volume : Measure E3)) := hA
    exact AEMeasurable.lintegral_prod_right
      (f := fun (y : A3 (i := i) (j := j) × E3) (b : E3) => g (Φeq hij E3 (y, b))) h2
  have step1 : (∫⁻ x, g x) = ∫⁻ w : (A3 (i := i) (j := j) × E3) × E3, g (Φeq hij E3 w) := by
    have h := MeasureTheory.lintegral_map_equiv
      (μ := (volume : Measure ((A3 (i := i) (j := j) × E3) × E3))) g (Φeq hij E3)
    rw [hΦ.map_eq] at h
    exact h
  have step2 : (∫⁻ w : (A3 (i := i) (j := j) × E3) × E3, g (Φeq hij E3 w))
      = ∫⁻ y : A3 (i := i) (j := j) × E3, ∫⁻ b, g (Φeq hij E3 (y, b)) := by
    rw [show (volume : Measure ((A3 (i := i) (j := j) × E3) × E3))
        = (volume : Measure (A3 (i := i) (j := j) × E3)).prod (volume : Measure E3) from rfl,
      MeasureTheory.lintegral_prod _ hA]
  have step3 : (∫⁻ y : A3 (i := i) (j := j) × E3, ∫⁻ b, g (Φeq hij E3 (y, b)))
      = ∫⁻ x' : A3 (i := i) (j := j), ∫⁻ a, ∫⁻ b, g (Φeq hij E3 ((x', a), b)) := by
    rw [show (volume : Measure (A3 (i := i) (j := j) × E3))
        = (volume : Measure (A3 (i := i) (j := j))).prod (volume : Measure E3) from rfl,
      MeasureTheory.lintegral_prod _ hG]
  rw [step1, step2, step3]
  refine lintegral_congr fun x' => lintegral_congr fun a => lintegral_congr fun b => ?_
  rw [hform x' a b]

end Work.BoseBoxFock
