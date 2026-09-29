import Mathlib
import Submission.Work.KronP.defs

/-!
# `Work.KronP.quadRevWord`: a word that doubles a list, reversing the second copy

Given a value stack `ofList ys :: tl`, the word produces `ofList (ys ++ ys.reverse) :: tl`
at cost `O (vsz (ofList ys) + 1)`.

The word is four library calls:

1. `dup`     : `ofList ys :: tl ↦ ofList ys :: ofList ys :: tl`
2. `reverse` : reverses the top copy : `ofList ys.reverse :: ofList ys :: tl`
3. `swap`    : exchanges the two copies : `ofList ys :: ofList ys.reverse :: tl`
4. `append`  : `ofList (ys ++ ys.reverse) :: tl`

The cost of step 3 is phrased by `KernelLib.swap` in terms of the *sizes of the two values on
top*, and the value on top there is `ofList ys.reverse`; the size of a `cons`-chain does not
depend on the order of its elements (`vsz_ofList_reverse`), which is what lets every step be
charged to `vsz (ofList ys) + 1`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## The size of a `cons`-chain, and its invariance under reversal -/

/-- The size of a `cons`-node. -/
theorem vsz_cons_eq (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (a.enc ++ b.enc).length + 1 = a.enc.length + b.enc.length + 1
  rw [List.length_append]

/-- The size of the encoding of a `cons`-chain: one glyph per element plus one per link plus the
final `nil`. -/
theorem vsz_ofList_eq (l : List Val) : vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, vsz_cons_eq, ih,
        List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- `vsz (ofList l)` is invariant under reversing `l`. -/
theorem vsz_ofList_reverse (l : List Val) : vsz (ofList l.reverse) = vsz (ofList l) := by
  rw [vsz_ofList_eq, vsz_ofList_eq, List.length_reverse, List.map_reverse, List.sum_reverse]

/-! ## Two proof rules for `WordR` -/

/-- The `conseq` field of `KernelLib`, with the parameters inferred. -/
theorem wordR_conseq (hK : KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' :=
  hK.conseq (main := main) (p := p) (P := P) (Q := Q) (C := C) (P' := P') (Q' := Q')
    (C' := C') h hP hQ hC

/-- Sequence a word with an exact input/output relation and a constant cost with a second word
whose precondition is met by that output. -/
theorem wordR_seq_eq (hK : KernelLib) {main p q : Cmd} {P2 : List Val → Prop}
    {vs0 m1 m2 : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = vs0) (fun _ out => out = m1) (fun _ => c1))
    (h2 : WordR main q P2 (fun _ out => out = m2) (fun _ => c2)) (hP2 : P2 m1) :
    WordR main (.seq p q) (fun vs => vs = vs0) (fun _ out => out = m2) (fun _ => c1 + c2) := by
  have hcond : ∀ vs mid, (fun vs : List Val => vs = vs0) vs →
      (fun _ out => out = m1) vs mid → P2 mid ∧ (fun _ => c2) mid ≤ (fun _ => c2) vs := by
    intro vs mid _ hQ
    exact ⟨by rw [hQ]; exact hP2, le_rfl⟩
  have hseq := hK.seq (main := main) (p := p) (q := q) (P := fun vs => vs = vs0)
    (Q := fun _ out => out = m1) (C := fun _ => c1) (P' := P2) (Q' := fun _ out => out = m2)
    (C' := fun _ => c2) (B := fun _ => c2) h1 h2 hcond
  refine hK.conseq (main := main) (p := .seq p q) (P := fun vs => vs = vs0)
    (Q := fun vs out => ∃ mid, (fun _ out => out = m1) vs mid ∧ (fun _ out => out = m2) mid out)
    (C := fun _ => c1 + c2) (P' := fun vs => vs = vs0) (Q' := fun _ out => out = m2)
    (C' := fun _ => c1 + c2) hseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro vs out _ hQ
  obtain ⟨mid, -, hout⟩ := hQ
  exact hout

/-! ## The word -/

theorem quadRevWord (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (ys : List HvdH.Val) (tl : List HvdH.Val),
        HvdH.WordR main prog
          (fun vs => vs = HvdH.ofList ys :: tl)
          (fun _ out => out = HvdH.ofList (ys ++ ys.reverse) :: tl)
          (fun _ => K * (HvdH.vsz (HvdH.ofList ys) + 1)) := by
  obtain ⟨pD, KD, hD⟩ := hK.dup
  obtain ⟨pR, KR, hR⟩ := hL.reverse
  obtain ⟨pS, KS, hS⟩ := hK.swap
  obtain ⟨pA, KA, hA⟩ := hL.append
  refine ⟨.seq (.seq (.seq pD pR) pS) pA, KD + KR + KA + 2 * KS, ?_⟩
  intro main ys tl
  -- 1. duplicate the list
  have h1 : WordR main pD (fun vs => vs = ofList ys :: tl)
      (fun _ out => out = ofList ys :: ofList ys :: tl)
      (fun _ => KD * (vsz (ofList ys) + 1)) := by
    refine wordR_conseq hK (hD main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hQ
      obtain ⟨v, rest, hv, hout⟩ := hQ
      rw [hvs, List.cons.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact hout
    · intro vs hvs
      rw [hvs]
      simp
  -- 2. reverse the top copy
  have h2 : WordR main pR (fun vs => vs = ofList ys :: ofList ys :: tl)
      (fun _ out => out = ofList ys.reverse :: ofList ys :: tl)
      (fun _ => KR * (vsz (ofList ys) + 1)) := by
    refine wordR_conseq hK (hR main ys) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨ofList ys :: tl, rfl⟩
    · intro vs out hvs hQ
      obtain ⟨rest, hrest, hout⟩ := hQ
      rw [hvs, List.cons.injEq] at hrest
      obtain ⟨-, hrest⟩ := hrest
      rw [← hrest] at hout
      exact hout
    · intro vs _
      exact le_rfl
  -- 3. swap the two copies
  have h3 : WordR main pS (fun vs => vs = ofList ys.reverse :: ofList ys :: tl)
      (fun _ out => out = ofList ys :: ofList ys.reverse :: tl)
      (fun _ => KS * (vsz (ofList ys.reverse) + vsz (ofList ys) + 1)) := by
    refine wordR_conseq hK (hS main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hQ
      obtain ⟨a, b, rest, hv, hout⟩ := hQ
      rw [hvs, List.cons.injEq, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact hout
    · intro vs hvs
      rw [hvs]
      simp
  -- 4. append the two copies
  have h4 : WordR main pA (fun vs => vs = ofList ys :: ofList ys.reverse :: tl)
      (fun _ out => out = ofList (ys ++ ys.reverse) :: tl)
      (fun _ => KA * (vsz (ofList ys) + 1)) := by
    refine wordR_conseq hK (hA main ys ys.reverse) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨tl, rfl⟩
    · intro vs out hvs hQ
      obtain ⟨rest, hrest, hout⟩ := hQ
      rw [hvs, List.cons.injEq, List.cons.injEq] at hrest
      obtain ⟨-, -, hrest⟩ := hrest
      rw [← hrest] at hout
      exact hout
    · intro vs _
      exact le_rfl
  have hs12 := wordR_seq_eq hK h1 h2 (vs0 := ofList ys :: tl) (m1 := ofList ys :: ofList ys :: tl)
    (m2 := ofList ys.reverse :: ofList ys :: tl) (c1 := KD * (vsz (ofList ys) + 1))
    (c2 := KR * (vsz (ofList ys) + 1)) (P2 := fun vs => vs = ofList ys :: ofList ys :: tl) (hP2 := rfl)
  have hs123 := wordR_seq_eq hK hs12 h3
    (m2 := ofList ys :: ofList ys.reverse :: tl)
    (c2 := KS * (vsz (ofList ys.reverse) + vsz (ofList ys) + 1))
    (P2 := fun vs => vs = ofList ys.reverse :: ofList ys :: tl) (hP2 := rfl)
  have hs1234 := wordR_seq_eq hK hs123 h4 (c2 := KA * (vsz (ofList ys) + 1))
    (P2 := fun vs => vs = ofList ys :: ofList ys.reverse :: tl) (hP2 := rfl)
  refine wordR_conseq hK hs1234 (fun _ h => h) (fun _ _ _ h => h) ?_
  intro vs _
  rw [vsz_ofList_reverse]
  have hVS : vsz (ofList ys) + vsz (ofList ys) + 1 ≤ 2 * (vsz (ofList ys) + 1) := by omega
  have hKS : KS * (vsz (ofList ys) + vsz (ofList ys) + 1)
      ≤ 2 * (KS * (vsz (ofList ys) + 1)) := by
    have := Nat.mul_le_mul_left KS hVS
    nlinarith
  nlinarith

end Work.KronP
