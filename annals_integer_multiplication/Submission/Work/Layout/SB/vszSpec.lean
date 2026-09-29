import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.SB.Core.vszFacts
import Submission.Work.Layout.sliceIdx

/-!
# `Work.Layout.VszSpec` — the size facts used by the sort-based `applyAlong`

`Work.Layout.VszSpec` (see `Submission/Work/Layout/SB/Specs.lean`) collects the four `vsz` estimates
on which the sort/strip route to `LayoutLib.applyAlong` rests:

1. the exact size of a list value, `vsz (ofList l) = Σ vsz + |l| + 1`;
2. the uniform bound `vsz (ofList l) ≤ (|l| + 1) * (L + 1)` when every entry has size `≤ L`;
3. the size of one slice `(slices A m B es).getD s []` of a flat `A × m × B` array `es`
   (of length `m`, entries of size `≤ L`);
4. the size of the packed list of output slices `outs.map ofList` (`A*B` rows of length `n`).

Items 1 and 2 are `Work.SB.Core.vsz_ofList_eq` / `vsz_ofList_le`; items 3 and 4 are proved here.
For 3 the point is that the `getD` fallback is never reached: for `s < A*B` and `j < m` the index
`(s/B*m + j)*B + s%B` is `< A*m*B = es.length`. For 4 the two `getD`-hypotheses make every row of
`outs` a list of `n` values of size `≤ L`, and summing the exact formula of 1 gives the bound.
-/

set_option autoImplicit false

namespace Work.Layout.SB

open HvdH

/-! ## Helpers -/

/-- The `s`-th slice of the flat `A × m × B` array `es`, unfolded. -/
private lemma slices_getD_eq (A m B : ℕ) (es : List Val) {s : ℕ} (hs : s < A * B) :
    (slices A m B es).getD s [] =
      (List.range m).map (fun j => es.getD ((s / B * m + j) * B + s % B) default) := by
  have hslen : s < (List.range (A * B)).length := by simpa using hs
  unfold HvdH.slices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hslen,
    Option.map_some, Option.getD_some]
  rw [List.getElem_range hslen]

/-- Every index met inside a slice of a flat `A × m × B` array is in range. -/
private lemma slices_idx_lt (A m B : ℕ) (s j : ℕ) (hs : s < A * B) (hj : j < m) :
    (s / B * m + j) * B + s % B < A * m * B := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hs
    · exact h
  have hsA : s / B < A := (Nat.div_lt_iff_lt_mul hB).mpr hs
  have hmod : s % B < B := Nat.mod_lt _ hB
  have h1 : s / B * m + j + 1 ≤ A * m := by
    calc s / B * m + j + 1 ≤ s / B * m + m := by omega
      _ = (s / B + 1) * m := by ring
      _ ≤ A * m := Nat.mul_le_mul_right _ (by omega)
  calc (s / B * m + j) * B + s % B < (s / B * m + j) * B + B := Nat.add_lt_add_left hmod _
    _ = (s / B * m + j + 1) * B := by ring
    _ ≤ A * m * B := Nat.mul_le_mul_right _ h1

/-- Sum of the sizes of the entries of a list, bounded by the length times a uniform bound. -/
private lemma sum_map_vsz_le (l : List Val) (B : ℕ) (h : ∀ x ∈ l, vsz x ≤ B) :
    (l.map vsz).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : vsz a ≤ B := h a (by simp)
    have ht : ∀ x ∈ t, vsz x ≤ B := fun x hx => h x (by simp [hx])
    have ih' := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [add_mul, one_mul]
    omega

/-- Sum of a constant list. -/
private lemma sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, Nat.succ_mul]
    omega

/-! ## Item 3: the size of one slice -/

private lemma vsz_slice_le (A m B : ℕ) (es : List Val) (L : ℕ)
    (_hm : 0 < m) (hlen : es.length = A * m * B) (hsz : ∀ x ∈ es, vsz x ≤ L)
    (s : ℕ) (hs : s < A * B) :
    vsz (ofList ((slices A m B es).getD s [])) ≤ (m + 1) * (L + 1) := by
  have hslice := slices_getD_eq A m B es hs
  have hsl : ((slices A m B es).getD s []).length = m := by
    rw [hslice, List.length_map, List.length_range]
  have helem : ∀ x ∈ (slices A m B es).getD s [], vsz x ≤ L := by
    intro x hx
    rw [hslice] at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hj
    have hidx := slices_idx_lt A m B s j hs hj
    rw [← hlen] at hidx
    rw [List.getD_eq_getElem _ _ hidx]
    exact hsz _ (List.getElem_mem hidx)
  have hl := Work.SB.Core.vsz_ofList_le (xs := (slices A m B es).getD s []) (B := L) helem
  rwa [hsl] at hl

/-! ## Item 4: the size of the packed output slices -/

private lemma vsz_outs_le (A n B : ℕ) (outs : List (List Val)) (L : ℕ)
    (hlen : outs.length = A * B)
    (hrow : ∀ s, s < A * B → (outs.getD s []).length = n)
    (hsz : ∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) :
    vsz (ofList (outs.map ofList)) ≤ A * B * (n * (L + 1) + 1) + A * B + 1 := by
  have hinner : ∀ ol ∈ outs, vsz (ofList ol) ≤ n * (L + 1) + 1 := by
    intro ol hol
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hol
    have hiAB : i < A * B := by rw [← hlen]; exact hi
    have hol' : outs.getD i [] = ol := by rw [List.getD_eq_getElem _ _ hi, hget]
    have hrowi : ol.length = n := by rw [← hol', hrow i hiAB]
    have hszi : ∀ y ∈ ol, vsz y ≤ L := by
      intro y hy
      rw [← hol'] at hy
      exact hsz i hiAB y hy
    have hsum := sum_map_vsz_le ol L hszi
    rw [Work.SB.Core.vsz_ofList_eq, hrowi] at *
    nlinarith
  have hlen2 : (outs.map ofList).length = A * B := by rw [List.length_map, hlen]
  have hsum2 : ((outs.map ofList).map vsz).sum ≤ A * B * (n * (L + 1) + 1) := by
    rw [List.map_map]
    calc (outs.map (vsz ∘ ofList)).sum
        ≤ (outs.map (fun _ => n * (L + 1) + 1)).sum :=
          List.sum_le_sum (fun ol hol => hinner ol hol)
      _ = outs.length * (n * (L + 1) + 1) := sum_map_const outs _
      _ = A * B * (n * (L + 1) + 1) := by rw [hlen]
  rw [Work.SB.Core.vsz_ofList_eq, hlen2]
  omega

/-! ## The four size facts -/

theorem vszSpec : Work.Layout.VszSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Work.SB.Core.vsz_ofList_eq
  · intro l L h
    exact Work.SB.Core.vsz_ofList_le h
  · intro A m B es L hm hlen hsz s hs
    exact vsz_slice_le A m B es L hm hlen hsz s hs
  · intro A n B outs L hlen hrow hsz
    exact vsz_outs_le A n B outs L hlen hrow hsz

end Work.Layout.SB
