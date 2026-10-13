import Mathlib
import Submission.Work.DSCOH.simplexCechLiftAux

/-!
Area DSCOH — pointwise relation between the summands of the contraction boundary sum
and of the cocycle boundary sum at `T ∪ {a}`.

With `a ≤ x` for every `x ∉ Z` and `i ∈ T \ Z ⊆ (T ∪ {a}) \ Z`, the element `a` lies
strictly below `i`; consequently erasing `i` from `T ∪ {a}` is the same as first erasing
`i` from `T` and then adjoining `a`, and the alternating sign gains exactly one factor of
`(-1)`.  Comparing the two definitions gives the claimed identity.
-/

open Finset
open scoped BigOperators

namespace Work.DSCOH

theorem dsSummandRelation {A : Type*} [CommRing A] {V : Type*} [LinearOrder V] [DecidableEq V]
    (Z : Finset V) (m : ℕ) (a : V) (z0 : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m})
    (T' : {T : Finset V // Z ⊆ T ∧ T.card = m + 1})
    (haT : a ∉ T.1) (hale : ∀ x, x ∉ Z → a ≤ x) (hT' : T'.1 = T.1 ∪ {a})
    (i : V) (hi : i ∈ T.1 \ Z) :
    summandG (A := A) Z m a z0 c T i = (-((-1 : ℤ) ^ z0)) • summandH (A := A) Z m c T' i := by
  classical
  -- `i ∈ T \ Z`, so `a ≤ i`; `i ∈ T` and `a ∉ T` give `a ≠ i`, hence `a < i`.
  have hiT : i ∈ T.1 := (Finset.mem_sdiff.mp hi).1
  have hiZ : i ∉ Z := (Finset.mem_sdiff.mp hi).2
  have hai : a < i := by
    rcases lt_or_eq_of_le (hale i hiZ) with h | h
    · exact h
    · exact absurd (h ▸ hiT) haT
  have hai' : a ≠ i := ne_of_lt hai
  -- `i` is also a valid index for `T'`.
  have hi' : i ∈ T'.1 \ Z := by
    rw [Finset.mem_sdiff]
    exact ⟨by rw [hT', Finset.mem_union]; exact Or.inl hiT, hiZ⟩
  rw [summandG_eq Z m a z0 c T i hi, summandH_eq Z m c T' i hi']
  -- `a ∉ T.erase i`, so the `apexL` is evaluated at `(T.erase i) ∪ {a}`.
  have hnotmem : a ∉ (mkEraseIdx Z m T i hi).1 := by
    rw [mkEraseIdx_val]
    exact fun h => haT (Finset.mem_of_mem_erase h)
  rw [apexL_apply_of_not_mem hnotmem]
  -- `(T.erase i) ∪ {a} = (T ∪ {a}).erase i` as level-`m` indices.
  have hAug : augIdx Z m a (mkEraseIdx Z m T i hi) hnotmem = mkEraseIdxH Z m T' i hi' := by
    apply Subtype.ext
    rw [augIdx_val, mkEraseIdx_val, mkEraseIdxH_val, hT']
    simp only [Finset.union_singleton]
    rw [Finset.erase_insert_of_ne hai']
  -- The alternating sign gains one factor of `(-1)`: `a` is counted below `i` in `T'`
  -- but not in `T`.
  have hcT' : (T'.1.filter (fun x => x < i)).card = (T.1.filter (fun x => x < i)).card + 1 := by
    rw [hT', Finset.union_singleton]
    exact card_filter_lt_insert haT hai
  have hsign : ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i)).card)) * ((-1 : ℤ) ^ z0)
      = (-((-1 : ℤ) ^ z0)) * ((-1 : ℤ) ^ ((T'.1.filter (fun x => x < i)).card)) := by
    rw [hcT', pow_succ]
    ring
  rw [hAug, smul_smul, smul_smul, hsign]

end Work.DSCOH
