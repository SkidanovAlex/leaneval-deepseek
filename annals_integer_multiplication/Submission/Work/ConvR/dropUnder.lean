import Mathlib
import Submission.Work.ConvR.pwdefs

/-!
# ConvR: dropping the two values just below the top of the value stack

A small `KernelLib` word needed by the ConvR pipeline: from `z :: a :: b :: rest` it produces
`z :: rest`, i.e. it deletes the second and third values of the value stack, at linear cost.

The word is the straight-line composition `roll 2, drop, roll 1, drop` of `KernelLib`:

* `roll 2` moves the third value `b` to the front: `b :: z :: a :: rest`,
* `drop` deletes it: `z :: a :: rest`,
* `roll 1` moves `a` to the front: `a :: z :: rest`,
* `drop` deletes it: `z :: rest`.

The total cost is `3·KR·sz + KD·(|b|+1) + 2·KR·(|z|+|a|+1) + KD·(|a|+1)`, bounded by
`(5·KR + 2·KD)·(|z|+|a|+|b|+1)`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Constant-cost words with fixed input/output windows -/

/-- Sequential composition of two `WordC`s whose specifications are given by explicit lists:
`L ↦ M` followed by `M ↦ N` gives `L ↦ N`. -/
theorem WordC.seqEq (hK : KernelLib) {main p q : Cmd} {L M N : List Val} {C C' : ℕ}
    (h1 : WordC main p (fun vs => vs = L) (fun _ out => out = M) C)
    (h2 : WordC main q (fun vs => vs = M) (fun _ out => out = N) C') :
    WordC main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (C + C') := by
  refine WordC.conseq hK (WordC.seq hK h1 h2 ?_) (fun _ h => h) ?_ (le_refl _)
  · intro vs mid _ hq
    exact hq
  · rintro vs out _ ⟨mid, -, hout⟩
    exact hout

/-- One `roll k` on a fixed list `L`, with the cost of the instance written out. -/
theorem WordC.rollStep (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {KR : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k C : ℕ} (hk : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L')
    (hC : KR * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordC main (rollP k) (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main (rollP k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun _ out => out = L')
    (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => C)
    (hroll main k) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hQ; rw [hvs] at hQ; rw [hQ, hL']
  · intro vs hvs; rw [hvs]; exact hC

/-- One `drop` on a fixed nonempty list `L = v :: rest`, with the cost of the instance written
out (`L.tail` is `rest`). -/
theorem WordC.dropStep (hK : KernelLib) {main : Cmd} {dropP : Cmd} {KD : ℕ}
    (hdrop : ∀ main : Cmd, WordR main dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest', vs = v :: rest' ∧ out = rest')
      (fun vs => KD * (vsz (vs.headD .nil) + 1)))
    {L L' : List Val} {C : ℕ} (hne : L ≠ []) (hL' : L.tail = L')
    (hC : KD * (vsz (L.headD .nil) + 1) ≤ C) :
    WordC main dropP (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main dropP (fun vs => vs ≠ []) (fun vs => vs = L)
    (fun vs out => ∃ v rest', vs = v :: rest' ∧ out = rest') (fun _ out => out = L')
    (fun vs => KD * (vsz (vs.headD .nil) + 1)) (fun _ => C)
    (hdrop main) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hne
  · intro vs out hvs hQ
    rw [hvs] at hQ
    obtain ⟨v, rest', hv, hout⟩ := hQ
    rw [hout]
    have htail : rest' = L.tail := by rw [hv]; simp
    rw [htail, hL']
  · intro vs hvs; rw [hvs]; exact hC

/-! ## The word -/

theorem dropUnder (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (z a b : HvdH.Val) (rest : List HvdH.Val),
      Work.ConvR.WordC main prog (fun vs => vs = z :: a :: b :: rest)
        (fun _ out => out = z :: rest)
        (K * (HvdH.vsz z + HvdH.vsz a + HvdH.vsz b + 1)) := by
  obtain ⟨rollP, KR, hroll⟩ := hK.roll
  obtain ⟨dropP, KD, hdrop⟩ := hK.drop
  refine ⟨.seq (.seq (.seq (rollP 2) dropP) (rollP 1)) dropP, 5 * KR + 2 * KD, ?_⟩
  intro main z a b rest
  set S : ℕ := vsz z + vsz a + vsz b + 1 with hS
  have H1 : WordC main (rollP 2) (fun vs => vs = z :: a :: b :: rest)
      (fun _ out => out = b :: z :: a :: rest) (3 * KR * S) := by
    refine WordC.rollStep hK hroll (k := 2) (L := z :: a :: b :: rest)
      (L' := b :: z :: a :: rest) ?_ ?_ ?_
    · simp
    · simp
    · have ht : (((z :: a :: b :: rest).take (2 + 1)).map vsz).sum + 1 = S := by
        simp [hS, Nat.add_assoc]
      rw [ht]
      exact Nat.le_of_eq (by ring)
  have H2 : WordC main dropP (fun vs => vs = b :: z :: a :: rest)
      (fun _ out => out = z :: a :: rest) (KD * (vsz b + 1)) := by
    refine WordC.dropStep hK hdrop (L := b :: z :: a :: rest) (L' := z :: a :: rest)
      ?_ ?_ ?_
    · simp
    · rfl
    · exact le_of_eq rfl
  have H3 : WordC main (rollP 1) (fun vs => vs = z :: a :: rest)
      (fun _ out => out = a :: z :: rest) (2 * KR * (vsz z + vsz a + 1)) := by
    refine WordC.rollStep hK hroll (k := 1) (L := z :: a :: rest) (L' := a :: z :: rest)
      ?_ ?_ ?_
    · simp
    · simp
    · have ht : (((z :: a :: rest).take (1 + 1)).map vsz).sum + 1 = vsz z + vsz a + 1 := by
        simp [Nat.add_assoc]
      rw [ht]
      exact Nat.le_of_eq (by ring)
  have H4 : WordC main dropP (fun vs => vs = a :: z :: rest) (fun _ out => out = z :: rest)
      (KD * (vsz a + 1)) := by
    refine WordC.dropStep hK hdrop (L := a :: z :: rest) (L' := z :: rest) ?_ ?_ ?_
    · simp
    · rfl
    · exact le_of_eq rfl
  refine WordC.conseq hK (WordC.seqEq hK (WordC.seqEq hK (WordC.seqEq hK H1 H2) H3) H4)
    (fun _ h => h) (fun _ _ _ hout => hout) ?_
  have hb : KD * (vsz b + 1) ≤ KD * S := Nat.mul_le_mul_left _ (by omega)
  have hza : 2 * KR * (vsz z + vsz a + 1) ≤ 2 * KR * S := Nat.mul_le_mul_left _ (by omega)
  have ha : KD * (vsz a + 1) ≤ KD * S := Nat.mul_le_mul_left _ (by omega)
  calc ((3 * KR * S + KD * (vsz b + 1)) + 2 * KR * (vsz z + vsz a + 1)) + KD * (vsz a + 1)
      ≤ ((3 * KR * S + KD * S) + 2 * KR * S) + KD * S :=
        add_le_add (add_le_add (Nat.add_le_add_left hb (3 * KR * S)) hza) ha
    _ = (5 * KR + 2 * KD) * S := by ring

end Work.ConvR
