import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceDefs` — the vocabulary of the slicing identity

The target `Work.BoseBoxFock.setIntegral_insertCoord2_slice` states that for a continuous
`f : Xn n → ℝ`

    ∫ y in boxL ℓ, ∫ u in boxL ℓ, ∫ x'' in boxPiSet ι ℓ, f (insertCoord2 p y u x'')
      = ∫ x in abox n ℓ, f x

where `ι = {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}` and `p.1 ≠ p.2`.  Both sides are integrals of the
same function over the same set, the left one being the pull-back along the **coordinate
insertion** map

    Φ : (E3 × E3) × (ι → E3) → (Fin n → E3),   Φ ((y,u),x'') = insertCoord2 p y u x''.

This module fixes that vocabulary:

* `boxMeas ℓ` — the box measure `volume.restrict (corpusBox.boxL ℓ)` on `E3`;
* `sliceIdxEquiv` — the index equivalence `ι ⊕ Fin 2 ≃ Fin n` (used to compare the products of
  the coordinate weights);
* `sliceIns` — the insertion `Φ` as a **measurable equivalence**;
* the two measure identifications `restrict_boxPiSet_eq`, `restrict_abox_eq` expressing the
  restricted product measures as `Measure.pi` of `boxMeas`;
* the continuity of `Φ` and the integrability of `f ∘ Φ` on the product box.

`sorry`-free (definitions and elementary lemmas).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The box measure -/

/-- The measure of the corpus box `boxL ℓ ⊆ E3`, i.e. `volume` restricted to it. -/
noncomputable abbrev boxMeas (ℓ : ℝ) : Measure E3 :=
  (volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)

/-! ## 2. The index equivalence `ι ⊕ Fin 2 ≃ Fin n` -/

/-- Forward map of the slicing index equivalence: the two elements of `Fin 2` are sent to the
coordinates `p.1`, `p.2` and `ι` to the remaining ones. -/
def sliceIdxFwd {n : ℕ} (p : Fin n × Fin n) :
    ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} ⊕ Fin 2) → Fin n
  | Sum.inl i => i.1
  | Sum.inr t => if t = 0 then p.1 else p.2

/-- Backward map of the slicing index equivalence. -/
def sliceIdxBwd {n : ℕ} (p : Fin n × Fin n) :
    Fin n → ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} ⊕ Fin 2) :=
  fun k => if h : k = p.1 then Sum.inr 0
           else if h' : k = p.2 then Sum.inr 1
           else Sum.inl ⟨k, h, h'⟩

@[simp] lemma sliceIdxFwd_inl {n : ℕ} (p : Fin n × Fin n)
    (i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) : sliceIdxFwd p (Sum.inl i) = i.1 := rfl

@[simp] lemma sliceIdxFwd_inr_zero {n : ℕ} (p : Fin n × Fin n) :
    sliceIdxFwd p (Sum.inr (0 : Fin 2)) = p.1 := rfl

@[simp] lemma sliceIdxFwd_inr_one {n : ℕ} (p : Fin n × Fin n) :
    sliceIdxFwd p (Sum.inr (1 : Fin 2)) = p.2 := rfl

lemma sliceIdxBwd_fst {n : ℕ} (p : Fin n × Fin n) : sliceIdxBwd p p.1 = Sum.inr 0 := by
  rw [sliceIdxBwd]; rw [dif_pos rfl]

lemma sliceIdxBwd_snd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    sliceIdxBwd p p.2 = Sum.inr 1 := by
  rw [sliceIdxBwd]; rw [dif_neg (Ne.symm hp), dif_pos rfl]

lemma sliceIdxBwd_fwd_zero {n : ℕ} (p : Fin n × Fin n) :
    sliceIdxBwd p (sliceIdxFwd p (Sum.inr (0 : Fin 2))) = Sum.inr 0 := by
  rw [show sliceIdxFwd p (Sum.inr (0 : Fin 2)) = p.1 from rfl]
  exact sliceIdxBwd_fst p

lemma sliceIdxBwd_fwd_one {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    sliceIdxBwd p (sliceIdxFwd p (Sum.inr (1 : Fin 2))) = Sum.inr 1 := by
  rw [show sliceIdxFwd p (Sum.inr (1 : Fin 2)) = p.2 from rfl]
  exact sliceIdxBwd_snd p hp

lemma sliceIdxBwd_fwd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Function.LeftInverse (sliceIdxBwd p) (sliceIdxFwd p) := by
  intro j
  match j with
  | Sum.inl i =>
      show (if h : (↑i : Fin n) = p.1 then Sum.inr 0
              else if h' : ↑i = p.2 then Sum.inr 1
              else Sum.inl ⟨↑i, h, h'⟩) = Sum.inl i
      rw [dif_neg i.2.1, dif_neg i.2.2]
  | Sum.inr t =>
      by_cases ht : t = 0
      · subst ht
        exact sliceIdxBwd_fwd_zero p
      · have ht1 : t = 1 := by
          have h2 : t.val = 1 := by have := t.isLt; omega
          exact Fin.ext h2
        subst ht1
        exact sliceIdxBwd_fwd_one p hp

lemma sliceIdxFwd_bwd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Function.RightInverse (sliceIdxBwd p) (sliceIdxFwd p) := by
  intro k
  by_cases h : k = p.1
  · rw [show sliceIdxBwd p k = Sum.inr 0 from by rw [h]; exact sliceIdxBwd_fst p]
    exact h.symm
  · by_cases h' : k = p.2
    · rw [show sliceIdxBwd p k = Sum.inr 1 from by rw [h']; exact sliceIdxBwd_snd p hp]
      exact h'.symm
    · rw [show sliceIdxBwd p k = Sum.inl ⟨k, h, h'⟩ from by
        rw [sliceIdxBwd]; rw [dif_neg h, dif_neg h']]
      rfl

/-- **The index equivalence `ι ⊕ Fin 2 ≃ Fin n`** underlying the slicing identity: the two
coordinates `p.1`, `p.2` correspond to the two elements of `Fin 2`, all others to `ι`. -/
def sliceIdxEquiv {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} ⊕ Fin 2) ≃ Fin n where
  toFun := sliceIdxFwd p
  invFun := sliceIdxBwd p
  left_inv := sliceIdxBwd_fwd p hp
  right_inv := sliceIdxFwd_bwd p hp

@[simp] lemma sliceIdxEquiv_inl {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) : sliceIdxEquiv p hp (Sum.inl i) = i.1 := rfl

@[simp] lemma sliceIdxEquiv_inr_zero {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    sliceIdxEquiv p hp (Sum.inr (0 : Fin 2)) = p.1 := rfl

@[simp] lemma sliceIdxEquiv_inr_one {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    sliceIdxEquiv p hp (Sum.inr (1 : Fin 2)) = p.2 := rfl

/-! ## 3. The product identity for the coordinate weights -/

/-- **The product of the coordinate weights splits according to the insertion**: the product over
all coordinates of `Fin n` is the product over `ι` times the two special coordinates. -/
lemma prod_slice {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ k : Fin n, f k)
      = (f p.1 * f p.2) * ∏ i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}, f i.1 := by
  have h1 : (∏ k : Fin n, f k)
      = ∏ j : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} ⊕ Fin 2),
          f (sliceIdxEquiv p hp j) :=
    (Fintype.prod_equiv (sliceIdxEquiv p hp) (fun j => f (sliceIdxEquiv p hp j)) f
      (fun j => rfl)).symm
  rw [h1, Fintype.prod_sum_type]
  simp only [sliceIdxEquiv_inl, sliceIdxEquiv_inr_zero, sliceIdxEquiv_inr_one,
    Fin.prod_univ_two]
  rw [mul_comm]

/-! ## 4. The insertion as a measurable equivalence -/

/-- The insertion map `Φ ((y,u),x'') = insertCoord2 p y u x''`. -/
def sliceInsFun {n : ℕ} (p : Fin n × Fin n) :
    (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) → (Fin n → E3) :=
  fun w => insertCoord2 p w.1.1 w.1.2 w.2

/-- The inverse of the insertion map: the coordinates `p.1`, `p.2` of `x`, and the restriction of
`x` to the remaining coordinates. -/
def sliceInsInv {n : ℕ} (p : Fin n × Fin n) :
    (Fin n → E3) → (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :=
  fun x => ((x p.1, x p.2), fun i => x i.1)

lemma insertCoord2_apply_fst {n : ℕ} (p : Fin n × Fin n)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    insertCoord2 p w.1.1 w.1.2 w.2 p.1 = w.1.1 := by
  simp only [insertCoord2_eq]
  rw [dif_pos trivial]

lemma insertCoord2_apply_snd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    insertCoord2 p w.1.1 w.1.2 w.2 p.2 = w.1.2 := by
  simp only [insertCoord2_eq]
  rw [dif_neg (Ne.symm hp), dif_pos trivial]

lemma insertCoord2_apply_rest {n : ℕ} (p : Fin n × Fin n)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))
    (i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) :
    insertCoord2 p w.1.1 w.1.2 w.2 i.1 = w.2 i := by
  simp only [insertCoord2_eq]
  rw [dif_neg i.2.1, dif_neg i.2.2]

lemma sliceInsInv_insertCoord2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    sliceInsInv p (insertCoord2 p w.1.1 w.1.2 w.2) = w := by
  simp only [sliceInsInv, insertCoord2_apply_fst p w, insertCoord2_apply_snd p hp w]
  congr 1
  funext i
  exact insertCoord2_apply_rest p w i

lemma insertCoord2_sliceInsInv {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (x : Fin n → E3) : insertCoord2 p (x p.1) (x p.2) (fun i => x i.1) = x := by
  funext k
  by_cases h : k = p.1
  · subst h
    simp only [insertCoord2_eq]
    rw [dif_pos trivial]
  · by_cases h' : k = p.2
    · subst h'
      simp only [insertCoord2_eq]
      rw [dif_neg (Ne.symm hp), dif_pos trivial]
    · simp only [insertCoord2_eq]
      rw [dif_neg h, dif_neg h']

lemma measurable_sliceInsFun {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Measurable (sliceInsFun p) := by
  rw [measurable_pi_iff]
  intro k
  by_cases h : k = p.1
  · subst h
    rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        sliceInsFun p w p.1) = (fun w => w.1.1) from
      funext fun w => insertCoord2_apply_fst p w]
    exact (measurable_fst.comp measurable_fst)
  · by_cases h' : k = p.2
    · subst h'
      rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          sliceInsFun p w p.2) = (fun w => w.1.2) from
        funext fun w => insertCoord2_apply_snd p hp w]
      exact (measurable_snd.comp measurable_fst)
    · rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          sliceInsFun p w k) = (fun w => w.2 ⟨k, h, h'⟩) from
        funext fun w => insertCoord2_apply_rest p w (⟨k, h, h'⟩ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})]
      exact (measurable_pi_apply (⟨k, h, h'⟩ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})).comp measurable_snd

lemma measurable_sliceInsInv {n : ℕ} (p : Fin n × Fin n) : Measurable (sliceInsInv p) := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i.1)

/-- **The coordinate insertion `Φ ((y,u),x'') = insertCoord2 p y u x''` as a measurable
equivalence** between `(E3 × E3) × (ι → E3)` and the full configuration space `Xn n`. -/
def sliceIns {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) ≃ᵐ (Fin n → E3) where
  toEquiv :=
    { toFun := sliceInsFun p
      invFun := sliceInsInv p
      left_inv := sliceInsInv_insertCoord2 p hp
      right_inv := insertCoord2_sliceInsInv p hp }
  measurable_toFun := measurable_sliceInsFun p hp
  measurable_invFun := measurable_sliceInsInv p

@[simp] lemma sliceIns_apply {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    sliceIns p hp w = insertCoord2 p w.1.1 w.1.2 w.2 := rfl

/-! ## 5. The insertion map is continuous -/

/-- The insertion map is continuous. -/
lemma continuous_sliceInsFun {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Continuous (sliceInsFun p) := by
  rw [continuous_pi_iff (A := fun _ : Fin n => E3)]
  intro k
  by_cases h : k = p.1
  · subst h
    rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        sliceInsFun p w p.1) = (fun w => w.1.1) from
      funext fun w => insertCoord2_apply_fst p w]
    exact (continuous_fst.comp continuous_fst)
  · by_cases h' : k = p.2
    · subst h'
      rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          sliceInsFun p w p.2) = (fun w => w.1.2) from
        funext fun w => insertCoord2_apply_snd p hp w]
      exact (continuous_snd.comp continuous_fst)
    · rw [show (fun w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          sliceInsFun p w k) = (fun w => w.2 ⟨k, h, h'⟩) from
        funext fun w => insertCoord2_apply_rest p w (⟨k, h, h'⟩ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})]
      exact (continuous_apply (⟨k, h, h'⟩ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})).comp continuous_snd

/-! ## 6. The restricted product measures as `Measure.pi` of the box measure -/

lemma volume_pi_E3_mul {ι : Type*} [Fintype ι] :
    (volume : Measure (ι → E3)) = Measure.pi (fun _ : ι => (volume : Measure E3)) :=
  volume_pi

/-- The restricted volume on the product box is the product of the box measures. -/
lemma restrict_boxPiSet_eq {ι : Type*} [Fintype ι] {ℓ : ℝ} :
    (volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ) =
      Measure.pi (fun _ : ι => boxMeas ℓ) := by
  rw [volume_pi_E3_mul (ι := ι)]
  show (Measure.pi (fun _ : ι => (volume : Measure E3))).restrict
      (Set.pi Set.univ (fun _ : ι => Work.BoseK15.corpusBox.boxL ℓ)) =
    Measure.pi (fun _ : ι => boxMeas ℓ)
  rw [Measure.restrict_pi_pi]

/-- The restricted volume on `abox n ℓ` is the product of the box measures. -/
lemma restrict_abox_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (Fin n → E3)).restrict (Submission.BoseGases.abox n ℓ) =
      Measure.pi (fun _ : Fin n => boxMeas ℓ) := by
  rw [Submission.BoseGases.abox_eq_pi_acube, ← corpusBox_boxL_eq_acube hℓ]
  rw [volume_pi_E3_mul (ι := Fin n)]
  show (Measure.pi (fun _ : Fin n => (volume : Measure E3))).restrict
      (Set.pi Set.univ (fun _ : Fin n => Work.BoseK15.corpusBox.boxL ℓ)) =
    Measure.pi (fun _ : Fin n => boxMeas ℓ)
  rw [Measure.restrict_pi_pi]

end Work.BoseBoxFock
