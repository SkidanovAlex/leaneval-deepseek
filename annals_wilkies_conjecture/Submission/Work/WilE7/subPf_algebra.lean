import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE7.SubPfAux.unionSet_set
import Submission.Work.WilE7.SubPfAux.extend_castLE_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
# `SubPf` is closed under the elementary boolean operations on the cube

`SubPf n Y` means that `Y ⊆ ℝⁿ` is the projection of a restricted semi-Pfaffian (EA) set
(`WilkiesDesign.E.SubPf`).  This file proves the algebraic closure properties that the `E0`/`E10`
track needs:

* `∅` and the closed cube `[-1,1]ⁿ` are sub-Pfaffian;
* the union of two sub-Pfaffian sets is sub-Pfaffian;
* a union over any finset of a family of sub-Pfaffian sets is sub-Pfaffian.

The mathematical content is small but the encodings are not: a `SemiPf` set is a DNF of basic
sets over one EA chain, so a union of two of them has to be re-encoded as a *single* DNF over a
*single* chain.  That is what `SemiPf.unionSet` does (chains are concatenated, DNF lists are
appended), and its point set is computed in `SubPfAux.unionSet_set`.  The two sets being united
live in `ℝ^{n+m₁}` and `ℝ^{n+m₂}`; both are first transported to `ℝ^{n+(m₁+m₂)}` by extending
the chain along the injection `Fin.castLE`, whose effect on the projection is
`SubPfAux.extend_castLE_proj`.
-/

namespace SubPfAlg

/-! ## The empty set and the cube -/

/-- The `SemiPf` set with no branch at all: its point set is empty. -/
def emptySemiPf (k : ℕ) : SemiPf k := ⟨0, EAChain.nil k, []⟩

theorem emptySemiPf_set (k : ℕ) : (emptySemiPf k).set = (∅ : Set (Fin k → ℝ)) := by
  have hnil : (emptySemiPf k).basics = [] := rfl
  ext x
  constructor
  · rintro ⟨-, B, hB, -⟩
    rw [hnil] at hB
    simp at hB
  · intro hx
    exact (Set.notMem_empty x hx).elim

/-- The empty set is sub-Pfaffian. -/
theorem subPf_empty (n : ℕ) : SubPf n (∅ : Set (Fin n → ℝ)) := by
  refine ⟨0, emptySemiPf (n + 0), ?_⟩
  rw [emptySemiPf_set]
  simp

/-- The closed cube `[-1,1]ⁿ` is sub-Pfaffian: take the empty conjunction of conditions. -/
theorem subPf_cube (n : ℕ) : SubPf n (cubeC n) := by
  refine ⟨0, Work.WilE8.cubeSemiPf (n + 0), ?_⟩
  rw [Work.WilE8.cubeSemiPf_set]
  exact (Work.WilE8.projFirst_image_cubeC n 0).symm

/-! ## Zero padding of a point

`padZ K z` extends `z : Fin k → ℝ` by zeros to `K ≥ k` coordinates. -/

/-- Reading off the first `k` coordinates of `padZ K z` returns `z`. -/
theorem padZ_castLE_apply {k K : ℕ} (h : k ≤ K) (z : Fin k → ℝ) :
    (fun i : Fin k => padZ K z (Fin.castLE h i)) = z := by
  funext i
  have hi : (Fin.castLE h i).val < k := by rw [Fin.val_castLE]; exact i.isLt
  rw [padZ, dite_eq_left hi]
  exact congrArg z (Fin.ext (Fin.val_castLE h i))

/-- Zero padding preserves the closed cube. -/
theorem padZ_mem_cubeC {k K : ℕ} {z : Fin k → ℝ} (hz : z ∈ cubeC k) :
    padZ K z ∈ cubeC K := by
  intro i
  have hz' : ∀ i : Fin k, |z i| ≤ 1 := hz
  rw [padZ]
  split_ifs with h
  · exact hz' ⟨i.val, h⟩
  · simp

/-- Zero padding does not change the projection to the first `n` coordinates. -/
theorem projFirst_padZ {n m M : ℕ} (z : Fin (n + m) → ℝ) :
    projFirst n M (padZ (n + M) z) = projFirst n m z := by
  funext i
  have hi : (Fin.castAdd M i).val < n + m := by
    rw [Fin.val_castAdd]
    exact lt_of_lt_of_le i.isLt (Nat.le_add_right n m)
  rw [projFirst, padZ, dite_eq_left hi]
  exact congrArg z (Fin.ext (by rw [Fin.val_castAdd, Fin.val_castAdd]))

/-! ## Union of two sub-Pfaffian sets -/

/-- The union of two sub-Pfaffian sets is sub-Pfaffian.  Both are first transported to the
common ambient dimension `ℝ^{n+(m₁+m₂)}`, and then `SemiPf.unionSet` merges the two DNF's
into one. -/
theorem subPf_union {n : ℕ} {Y Z : Set (Fin n → ℝ)} (hY : SubPf n Y) (hZ : SubPf n Z) :
    SubPf n (Y ∪ Z) := by
  obtain ⟨m₁, X₁, h₁⟩ := hY
  obtain ⟨m₂, X₂, h₂⟩ := hZ
  have hm₁ : m₁ ≤ m₁ + m₂ := by omega
  have hm₂ : m₂ ≤ m₁ + m₂ := by omega
  have hp₁ : projFirst n (m₁ + m₂) ''
      (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left hm₁ n)) X₁).set
      = projFirst n m₁ '' X₁.set := SubPfAux.extend_castLE_proj hm₁ X₁
  have hp₂ : projFirst n (m₁ + m₂) ''
      (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left hm₂ n)) X₂).set
      = projFirst n m₂ '' X₂.set := SubPfAux.extend_castLE_proj hm₂ X₂
  refine ⟨m₁ + m₂, SemiPf.unionSet
    (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left hm₁ n)) X₁)
    (Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left hm₂ n)) X₂), ?_⟩
  rw [SubPfAux.unionSet_set, Set.image_union, hp₁, hp₂, h₁, h₂]

/-- Splitting off one term of a union over a finset. -/
theorem iUnion_finset_insert {k n : ℕ} (a : Fin k) (s : Finset (Fin k))
    (A : Fin k → Set (Fin n → ℝ)) :
    (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases hi with rfl | hi
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

/-- A finite union of sub-Pfaffian sets is sub-Pfaffian. -/
theorem subPf_iUnion {n k : ℕ} (s : Finset (Fin k)) (A : Fin k → Set (Fin n → ℝ))
    (h : ∀ i ∈ s, SubPf n (A i)) : SubPf n (⋃ i ∈ s, A i) := by
  classical
  revert h
  refine Finset.induction_on
    (motive := fun t => (∀ i ∈ t, SubPf n (A i)) → SubPf n (⋃ i ∈ t, A i)) s ?_ ?_
  · intro _
    have h0 : (⋃ i ∈ (∅ : Finset (Fin k)), A i) = (∅ : Set (Fin n → ℝ)) := by
      ext x
      simp
    rw [h0]
    exact subPf_empty n
  · intro a t ht ih h
    rw [iUnion_finset_insert]
    exact subPf_union (h a (Finset.mem_insert_self a t))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end SubPfAlg

theorem subPf_algebra :
    (∀ n : ℕ, WilkiesDesign.E.SubPf n (∅ : Set (Fin n → ℝ))) ∧
    (∀ n : ℕ, WilkiesDesign.E.SubPf n (WilkiesDesign.E.cubeC n)) ∧
    (∀ {n : ℕ} {Y Z : Set (Fin n → ℝ)}, WilkiesDesign.E.SubPf n Y →
        WilkiesDesign.E.SubPf n Z → WilkiesDesign.E.SubPf n (Y ∪ Z)) ∧
    (∀ {n k : ℕ} (s : Finset (Fin k)) (A : Fin k → Set (Fin n → ℝ)),
        (∀ i ∈ s, WilkiesDesign.E.SubPf n (A i)) →
        WilkiesDesign.E.SubPf n (⋃ i ∈ s, A i)) :=
  ⟨SubPfAlg.subPf_empty, SubPfAlg.subPf_cube,
   fun hY hZ => SubPfAlg.subPf_union hY hZ,
   fun s A h => SubPfAlg.subPf_iUnion s A h⟩

end Work.WilE7
