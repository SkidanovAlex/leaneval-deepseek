import Mathlib
import Submission.Work.Layout.SB.Specs

/-!
# Size of the `unslices` output

`HvdH.unslices A n B outs` is the flat list of length `A * n * B` obtained by transposing an
`A × B` array of lists of length `n` into the `A × n × B` layout (`LayoutLib.applyAlong`, paper
Lemma 2.11).  This file bounds the encoding size of the value `ofList` of that list: if every entry
of every slice has size `≤ L`, then the whole value has size
`≤ A * n * B * (L + 3) + 1`.

The two ingredients are purely combinatorial:

* `vsz (ofList l) = (l.map vsz).sum + l.length + 1`, so a list of `N` values of size `≤ L` has
  size `≤ N * L + N + 1`;
* every index `i < A * n * B` selects an *in-range* entry of `outs`: the slice index
  `i / (n * B) * B + i % B` is `< A * B` and the inner index `i / B % n` is `< n`, so the
  `getD` fallbacks are never taken.
-/

set_option autoImplicit false

namespace Work.SB.RawOps

open HvdH

/-! ## `vsz` of `ofList` -/

/-- Size of a `cons` value. -/
private theorem vsz_cons_loc (a b : HvdH.Val) :
    HvdH.vsz (HvdH.Val.cons a b) = HvdH.vsz a + HvdH.vsz b + 1 := by
  simp [HvdH.vsz, HvdH.Val.enc, Nat.add_assoc]

private theorem ofList_cons_loc (x : HvdH.Val) (t : List HvdH.Val) :
    HvdH.ofList (x :: t) = HvdH.Val.cons x (HvdH.ofList t) := rfl

/-- The exact size of the value encoding a list. -/
theorem vsz_ofList_eq (l : List HvdH.Val) :
    HvdH.vsz (HvdH.ofList l) = (l.map HvdH.vsz).sum + l.length + 1 := by
  induction l with
  | nil => simp [HvdH.ofList, HvdH.vsz, HvdH.Val.enc]
  | cons x t ih =>
    rw [ofList_cons_loc, vsz_cons_loc, ih, List.map_cons, List.sum_cons, List.length_cons]
    ring

/-- A list of `N` values of size `≤ L` is encoded by a value of size `≤ N * L + N + 1`. -/
theorem vsz_ofList_le_of_forall {l : List HvdH.Val} {L : ℕ}
    (h : ∀ x ∈ l, HvdH.vsz x ≤ L) :
    HvdH.vsz (HvdH.ofList l) ≤ l.length * L + l.length + 1 := by
  rw [vsz_ofList_eq]
  suffices hsum : (l.map HvdH.vsz).sum ≤ l.length * L by omega
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx : HvdH.vsz x ≤ L := h x (by simp)
    have ht : ∀ y ∈ t, HvdH.vsz y ≤ L := fun y hy => h y (by simp [hy])
    have ht' := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mul, one_mul]
    omega

/-! ## The index arithmetic of `unslices` -/

/-- For `0 < n`, `0 < B` and `i < A * n * B` the slice index used by `unslices` is `< A * B`. -/
theorem unslicesIdx_lt (A n B i : ℕ) (hn : 0 < n) (hB : 0 < B) (hi : i < A * n * B) :
    i / (n * B) * B + i % B < A * B := by
  have h1 : i / (n * B) < A :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos hn hB)).mpr (by simpa [Nat.mul_assoc] using hi)
  have h2 : i % B < B := Nat.mod_lt _ hB
  calc i / (n * B) * B + i % B < i / (n * B) * B + B := by omega
    _ = (i / (n * B) + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B (by omega)

/-- Every entry selected by `unslices` is an entry of `outs`, hence of size `≤ L`. -/
theorem vsz_unslices_elem_le (A n B : ℕ) (outs : List (List HvdH.Val)) (L : ℕ)
    (_hlen : outs.length = A * B)
    (hsl : ∀ s, s < A * B → (outs.getD s []).length = n)
    (hsz : ∀ s, s < A * B → ∀ y ∈ outs.getD s [], HvdH.vsz y ≤ L) :
    ∀ i, i < A * n * B →
      HvdH.vsz ((outs.getD (i / (n * B) * B + i % B) []).getD (i / B % n) default) ≤ L := by
  intro i hi
  have hprod : 0 < A * n * B := lt_of_le_of_lt (Nat.zero_le _) hi
  have hB : 0 < B := Nat.pos_of_mul_pos_left hprod
  have hAn : 0 < A * n := Nat.pos_of_mul_pos_right hprod
  have hn : 0 < n := Nat.pos_of_mul_pos_left hAn
  have hs : i / (n * B) * B + i % B < A * B := unslicesIdx_lt A n B i hn hB hi
  have hj : i / B % n < n := Nat.mod_lt _ hn
  have hl : (outs.getD (i / (n * B) * B + i % B) []).length = n := hsl _ hs
  have hl' : i / B % n < (outs.getD (i / (n * B) * B + i % B) []).length := by omega
  have hmem : (outs.getD (i / (n * B) * B + i % B) []).getD (i / B % n) default
      ∈ outs.getD (i / (n * B) * B + i % B) [] := by
    rw [List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem _
  exact hsz _ hs _ hmem

/-! ## The main bound -/

theorem vszUnslicesLe (A n B : ℕ) (outs : List (List HvdH.Val)) (L : ℕ)
    (hlen : outs.length = A * B)
    (hsl : ∀ s, s < A * B → (outs.getD s []).length = n)
    (hsz : ∀ s, s < A * B → ∀ y ∈ outs.getD s [], HvdH.vsz y ≤ L) :
    HvdH.vsz (HvdH.ofList (HvdH.unslices A n B outs)) ≤ A * n * B * (L + 3) + 1 := by
  have hlen2 : (HvdH.unslices A n B outs).length = A * n * B := by
    simp [HvdH.unslices]
  have hmem : ∀ x ∈ HvdH.unslices A n B outs, HvdH.vsz x ≤ L := by
    intro x hx
    rw [HvdH.unslices] at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact vsz_unslices_elem_le A n B outs L hlen hsl hsz i hi
  have hb := vsz_ofList_le_of_forall (l := HvdH.unslices A n B outs) (L := L) hmem
  rw [hlen2] at hb
  have hfin : A * n * B * L + A * n * B + 1 ≤ A * n * B * (L + 3) + 1 := by
    have h1 : A * n * B * L + A * n * B = A * n * B * (L + 1) := by ring
    rw [h1]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
  exact le_trans hb hfin

end Work.SB.RawOps
