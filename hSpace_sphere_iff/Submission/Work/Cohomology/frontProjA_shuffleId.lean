import Mathlib
import Submission.Work.Cohomology.EZShuffle

namespace Work.Cohomology

/-!
# The `A`-projection of the identity shuffle

For the shuffle `A = shuffleId p q = {0, 1, …, p-1} ⊆ Fin (p+q)` (the `p` "a-steps" first),
the `a`-side of the shuffle is the map `j ↦ #{i ∈ A : i < j} = min p j`, so the composite
of the inclusion `subinterval 0 p : ⦋p⦌ ⟶ ⦋p+q⦌` with `shuffleMapA A` is the identity of
`⦋p⦌`.  This is the "front projection" statement used in the proof that the Eilenberg–Zilber
shuffle chain evaluates to the cup product pairing on normalized cocycles.
-/

/-- The number of elements of `Fin n` that are `< m`, for `m ≤ n`. -/
lemma card_filter_fin_val_lt {n m : ℕ} (hm : m ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
  rw [← Fintype.card_subtype (fun i : Fin n => i.val < m)]
  have e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hm⟩, y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- The `a`-count of the identity shuffle is `min p j`. -/
lemma aCnt_shuffleId_eq_min {p q : ℕ} (j : Fin (p + q + 1)) :
    aCnt (shuffleId p q) j = min p j.val := by
  rw [aCnt, shuffleId, Finset.filter_filter]
  have h : (Finset.univ.filter fun i : Fin (p + q) => i.val < p ∧ i.val < j.val)
      = (Finset.univ.filter fun i : Fin (p + q) => i.val < min p j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.lt_min]
  rw [h, card_filter_fin_val_lt (by omega)]

/-- The underlying map of `shuffleMapA A hA` is `j ↦ aCnt A j`. -/
lemma shuffleMapA_toOrderHom_val {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (j : Fin (p + q + 1)) : ((shuffleMapA A hA).toOrderHom j).val = aCnt A j := rfl

/-- The underlying map of `subinterval j l h` is `i ↦ i + j`. -/
lemma subinterval_toOrderHom_val {n j l : ℕ} (h : j + l ≤ n) (i : Fin (l + 1)) :
    ((SimplexCategory.subinterval j l h).toOrderHom i).val = i.val + j := rfl

theorem frontProjA_shuffleId {p q : ℕ} (hA : (Work.Cohomology.shuffleId p q).card = p) :
    CategoryTheory.CategoryStruct.comp (SimplexCategory.subinterval 0 p (by omega))
      (Work.Cohomology.shuffleMapA (Work.Cohomology.shuffleId p q) hA)
      = CategoryTheory.CategoryStruct.id (SimplexCategory.mk p) := by
  apply SimplexCategory.Hom.ext
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.id_toOrderHom]
  ext k
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [shuffleMapA_toOrderHom_val, aCnt_shuffleId_eq_min, subinterval_toOrderHom_val,
    Nat.min_eq_right (by omega), Nat.add_zero]
  rfl

end Work.Cohomology
