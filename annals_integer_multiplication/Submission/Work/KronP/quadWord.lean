import Mathlib
import Submission.Work.KronP.defs

namespace Work.KronP

/-!
# `Work.KronP.quadWord`: duplicate a list on the value stack

Given a value stack `ofList ys :: tl`, produce `ofList (ys ++ ys) :: tl` at cost
`K * (vsz (ofList ys) + 1)`, i.e. linear in the size of the list.

The word is the composition of two library words:

1. `KernelLib.dup` copies the top value: `ofList ys :: tl ↦ ofList ys :: ofList ys :: tl`,
   at cost `KD * (vsz (ofList ys) + 1)`;
2. `LayoutLib.append` (with `xs = ys = ys`) appends the second list to the first:
   `ofList ys :: ofList ys :: tl ↦ ofList (ys ++ ys) :: tl`, at cost `KA * (vsz (ofList ys) + 1)`.

Both words are stated with the automatic `WordR` frame, so the surviving tail `tl` is untouched
and the total cost is `(KD + KA) * (vsz (ofList ys) + 1)`.
-/

theorem quadWord (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (ys : List HvdH.Val) (tl : List HvdH.Val),
        HvdH.WordR main prog
          (fun vs => vs = HvdH.ofList ys :: tl)
          (fun _ out => out = HvdH.ofList (ys ++ ys) :: tl)
          (fun _ => K * (HvdH.vsz (HvdH.ofList ys) + 1)) := by
  obtain ⟨pD, KD, hD⟩ := hK.dup
  obtain ⟨pA, KA, hA⟩ := hL.append
  refine ⟨HvdH.Cmd.seq pD pA, KD + KA, ?_⟩
  intro main ys tl
  -- Step 1: duplicate the top value `ofList ys`.
  have h1 : HvdH.WordR main pD
      (fun vs => vs = HvdH.ofList ys :: tl)
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) :=
    hK.conseq main pD (fun vs => vs ≠ [])
      (fun vs => vs = HvdH.ofList ys :: tl)
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))
      (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))
      (hD main)
      (fun vs hv => by rw [hv]; exact List.cons_ne_nil _ _)
      (fun vs out _ hq => hq)
      (fun vs _ => le_rfl)
  -- Step 2: append the copy to the original.
  have h2 : HvdH.WordR main pA
      (fun vs => ∃ rest, vs = HvdH.ofList ys :: HvdH.ofList ys :: rest)
      (fun vs out => ∃ rest, vs = HvdH.ofList ys :: HvdH.ofList ys :: rest ∧
        out = HvdH.ofList (ys ++ ys) :: rest)
      (fun _ => KA * (HvdH.vsz (HvdH.ofList ys) + 1)) := hA main ys ys
  have h3 : HvdH.WordR main (HvdH.Cmd.seq pD pA)
      (fun vs => vs = HvdH.ofList ys :: tl)
      (fun vs out => ∃ mid,
        (∃ v rest, vs = v :: rest ∧ mid = v :: v :: rest) ∧
        (∃ rest, mid = HvdH.ofList ys :: HvdH.ofList ys :: rest ∧
          out = HvdH.ofList (ys ++ ys) :: rest))
      (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1) +
        KA * (HvdH.vsz (HvdH.ofList ys) + 1)) :=
    hK.seq main pD pA
      (fun vs => vs = HvdH.ofList ys :: tl)
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))
      (fun vs => ∃ rest, vs = HvdH.ofList ys :: HvdH.ofList ys :: rest)
      (fun vs out => ∃ rest, vs = HvdH.ofList ys :: HvdH.ofList ys :: rest ∧
        out = HvdH.ofList (ys ++ ys) :: rest)
      (fun _ => KA * (HvdH.vsz (HvdH.ofList ys) + 1))
      (fun _ => KA * (HvdH.vsz (HvdH.ofList ys) + 1))
      h1 h2 (fun vs mid hv hq => by
        -- the middle value is `ofList ys :: ofList ys :: tl`, and the second word costs exactly `B`
        obtain ⟨v, rest, hveq, hmid⟩ := hq
        rw [hv] at hveq
        obtain ⟨hv', hr'⟩ := List.cons.injEq _ _ _ _ ▸ hveq
        exact ⟨⟨tl, by rw [hmid, hv', hr']⟩, le_rfl⟩)
  -- Consequence: the intermediate value stack is `ofList ys :: ofList ys :: tl`.
  exact hK.conseq main (HvdH.Cmd.seq pD pA)
    (fun vs => vs = HvdH.ofList ys :: tl)
    (fun vs => vs = HvdH.ofList ys :: tl)
    (fun vs out => ∃ mid,
      (∃ v rest, vs = v :: rest ∧ mid = v :: v :: rest) ∧
      (∃ rest, mid = HvdH.ofList ys :: HvdH.ofList ys :: rest ∧
        out = HvdH.ofList (ys ++ ys) :: rest))
    (fun vs out => out = HvdH.ofList (ys ++ ys) :: tl)
    (fun vs => KD * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1) +
      KA * (HvdH.vsz (HvdH.ofList ys) + 1))
    (fun _ => (KD + KA) * (HvdH.vsz (HvdH.ofList ys) + 1))
    h3
    (fun vs hv => hv)
    (fun vs out hv hq => by
      obtain ⟨mid, ⟨v, rest, hveq, hmid⟩, rest', hmid', hout⟩ := hq
      rw [hv] at hveq
      obtain ⟨hv', hr'⟩ := List.cons.injEq _ _ _ _ ▸ hveq
      have hEq : HvdH.ofList ys :: HvdH.ofList ys :: rest' =
          HvdH.ofList ys :: HvdH.ofList ys :: tl := by
        rw [← hmid', hmid, hv', hr']
      have hrest' : rest' = tl :=
        ((List.cons.injEq _ _ _ _).mp ((List.cons.injEq _ _ _ _).mp hEq).2).2
      rw [hrest'] at hout
      exact hout)
    (fun vs hv => by
      rw [hv]
      simp only [List.headD_cons]
      exact le_of_eq (by ring))

end Work.KronP
