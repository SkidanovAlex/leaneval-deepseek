import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs

/-!
# CRT reindexing (Agarwal–Cooley) — shared definitions

Definitions shared by the proof of `HvdH.CrtWordProp` (paper Prop 5.4 step (2)): the place-value
table of the mixed-radix numeration, the label list `m ↦ crtIdx ss m` and its inverse, and the
record helpers used by the label-and-sort word.

The reindexing is `m ↦ Σᵢ (m % sᵢ) · ∏_{j>i} sⱼ` (`HvdH.crtIdx`), which is a bijection of
`[0, ∏ ss)` for pairwise coprime `sᵢ ≥ 1` (`HvdH.crtIdx` is literally `Work.Main.Pcr`).
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## The place-value table -/

/-- For `ss = [s₁, …, s_d]`, the table of pairs `(sᵢ, ∏_{j>i} sⱼ)`: the moduli together with the
place values of the mixed-radix numeration used by the CRT reindexing. -/
def crtTab : List ℕ → List (ℕ × ℕ)
  | [] => []
  | s :: ss => (s, ss.prod) :: crtTab ss

@[simp] theorem crtTab_nil : crtTab ([] : List ℕ) = [] := rfl

@[simp] theorem crtTab_cons (s : ℕ) (ss : List ℕ) :
    crtTab (s :: ss) = (s, ss.prod) :: crtTab ss := rfl

@[simp] theorem crtIdx_nil (m : ℕ) : crtIdx ([] : List ℕ) m = 0 := rfl

@[simp] theorem crtIdx_cons (s : ℕ) (ss : List ℕ) (m : ℕ) :
    crtIdx (s :: ss) m = (m % s) * ss.prod + crtIdx ss m := rfl

/-- The CRT index is the sum over the place-value table. -/
theorem crtIdx_eq_sum (ss : List ℕ) (m : ℕ) :
    crtIdx ss m = ((crtTab ss).map (fun sp => m % sp.1 * sp.2)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih]

/-- The entries of the table have the moduli as first components. -/
theorem crtTab_fst (ss : List ℕ) : (crtTab ss).map Prod.fst = ss := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih]

/-! ## The label list and its inverse -/

/-- `sigmaList ss = [crtIdx ss 0, …, crtIdx ss (∏ss - 1)]`: the image of the CRT reindexing in
the order of the original positions. -/
def sigmaList (ss : List ℕ) : List ℕ := (List.range ss.prod).map (crtIdx ss)

@[simp] theorem sigmaList_length (ss : List ℕ) : (sigmaList ss).length = ss.prod := by
  simp [sigmaList]

theorem sigmaList_getD {ss : List ℕ} {i : ℕ} (hi : i < ss.prod) :
    (sigmaList ss).getD i 0 = crtIdx ss i := by
  rw [List.getD_eq_getElem _ _ (by simpa [sigmaList] using hi)]
  simp [sigmaList]

/-- `crtPinv ss j` is the position of label `j`: the (chosen) `m < ∏ss` with `crtIdx ss m = j`
(`0` if there is none). -/
noncomputable def crtPinv (ss : List ℕ) (j : ℕ) : ℕ :=
  if h : ∃ m, m < ss.prod ∧ crtIdx ss m = j then h.choose else 0

theorem crtPinv_spec {ss : List ℕ} {j : ℕ}
    (h : ∃ m, m < ss.prod ∧ crtIdx ss m = j) :
    crtPinv ss j < ss.prod ∧ crtIdx ss (crtPinv ss j) = j := by
  have hpinv : crtPinv ss j = h.choose := by
    rw [crtPinv]; exact dite_eq_left h
  rw [hpinv]
  exact h.choose_spec

/-- `crtQ ss = [crtPinv ss 0, …, crtPinv ss (∏ss - 1)]`: the list of positions in flat (label)
order, i.e. the inverse permutation. -/
noncomputable def crtQ (ss : List ℕ) : List ℕ := (List.range ss.prod).map (crtPinv ss)

@[simp] theorem crtQ_length (ss : List ℕ) : (crtQ ss).length = ss.prod := by
  simp [crtQ]

/-! ## Records (key, payload) -/

/-- The payload of a record `cons a v` is `v` (and `.nil` for non-records). -/
def recPayload : Val → Val
  | .cons _ v => v
  | _ => .nil

@[simp] theorem recPayload_cons (a b : Val) : recPayload (.cons a b) = b := rfl

/-- The natural key of a record. -/
def recKey : Val → ℕ
  | .cons (.int k) _ => k.toNat
  | _ => 0

@[simp] theorem pairKey_cons (k : ℤ) (v : Val) : pairKey (.cons (.int k) v) = k := rfl

@[simp] theorem recKey_cons_int (k : ℤ) (v : Val) : recKey (.cons (.int k) v) = k.toNat := rfl

@[simp] theorem recKey_cons (k : ℕ) (v : Val) : recKey (.cons (.int (k : ℤ)) v) = k := by
  simp [recKey]

/-- Elementwise pairing: records with label `wᵢ` and payload `xᵢ`. -/
def zipRec (xs ws : List Val) : List Val := List.zipWith (fun x w => Val.cons w x) xs ws

theorem zipRec_length {xs ws : List Val} (h : xs.length = ws.length) :
    (zipRec xs ws).length = xs.length := by
  simp [zipRec, List.length_zipWith, h]

theorem zipRec_getD {xs ws : List Val} (h : xs.length = ws.length) {i : ℕ}
    (hi : i < xs.length) :
    (zipRec xs ws).getD i .nil = .cons (ws.getD i .nil) (xs.getD i .nil) := by
  have hi' : i < ws.length := by omega
  have hi'' : i < (zipRec xs ws).length := by rw [zipRec_length h]; exact hi
  rw [List.getD_eq_getElem _ _ hi'', List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi]
  simp only [zipRec, List.getElem_zipWith]

/-- The position of label `m` in the label list `lab` (0 if there is none). -/
noncomputable def invLab (lab : List ℕ) (m : ℕ) : ℕ :=
  if h : ∃ j, j < lab.length ∧ lab.getD j 0 = m then h.choose else 0

theorem invLab_spec {lab : List ℕ} {m : ℕ}
    (h : ∃ j, j < lab.length ∧ lab.getD j 0 = m) :
    invLab lab m < lab.length ∧ lab.getD (invLab lab m) 0 = m := by
  have hinv : invLab lab m = h.choose := by
    rw [invLab]; exact dite_eq_left h
  rw [hinv]
  exact h.choose_spec

/-! ## Sizes -/

/-- A value has nonempty encoding. -/
theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons a b => simp [vsz, Val.enc]

theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc]

theorem vsz_ofList (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl, vsz_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.Main.vsz_int z

/-- `isz (k : ℤ) = k.size + 2` for a natural `k`. -/
def iszN (k : ℕ) : ℕ := k.size + 2

@[simp] theorem isz_natCast (k : ℕ) : isz (k : ℤ) = iszN k := by
  simp [isz, iszN]

@[simp] theorem vsz_intNat (k : ℕ) : vsz (Val.int (k : ℤ)) = iszN k := by
  rw [vsz_int, isz_natCast]

theorem vsz_intList (l : List ℕ) :
    vsz (intList l) = (l.map iszN).sum + l.length + 1 := by
  induction l with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons k l ih =>
      have h1 : intList (k :: l) = Val.cons (.int (k : ℤ)) (intList l) := rfl
      rw [h1, vsz_cons, ih, vsz_intNat]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem vsz_intList_le {l : List ℕ} {B : ℕ} (h : ∀ k ∈ l, iszN k ≤ B) :
    vsz (intList l) ≤ l.length * B + l.length + 1 := by
  rw [vsz_intList]
  have h2 : (l.map iszN).sum ≤ l.length * B := by
    induction l with
    | nil => simp
    | cons k l ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have hk : iszN k ≤ B := h k (by simp)
        have hl : (l.map iszN).sum ≤ l.length * B := ih (fun k' hk' => h k' (by simp [hk']))
        calc iszN k + (l.map iszN).sum ≤ B + l.length * B := Nat.add_le_add hk hl
          _ = (l.length + 1) * B := by ring
  calc (l.map iszN).sum + l.length + 1 ≤ l.length * B + l.length + 1 := by
        exact Nat.add_le_add_right (Nat.add_le_add_right h2 l.length) 1

/-- The labels of a label list, as `Val`s. -/
def labVals (l : List ℕ) : List Val := l.map fun k : ℕ => Val.int (k : ℤ)

theorem intList_eq_ofList (l : List ℕ) : intList l = ofList (labVals l) := by
  induction l with
  | nil => rfl
  | cons k l ih =>
      have h1 : intList (k :: l) = Val.cons (.int (k : ℤ)) (intList l) := rfl
      rw [h1, ih]
      unfold labVals
      rw [List.map_cons]
      rfl

theorem intList_eq_labVals_map (l : List ℕ) :
    intList l = ofList (l.map fun k : ℕ => Val.int (k : ℤ)) := intList_eq_ofList l

theorem labVals_getD {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (labVals l).getD i .nil = .int ((l.getD i 0 : ℕ) : ℤ) := by
  rw [List.getD_eq_getElem _ _ (by simpa [labVals] using hi)]
  unfold labVals
  rw [List.getElem_map, ← List.getD_eq_getElem _ _ hi]

end Work.MainP
