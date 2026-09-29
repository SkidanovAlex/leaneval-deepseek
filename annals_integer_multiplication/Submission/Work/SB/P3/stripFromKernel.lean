import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared

/-!
# The key-stripping word `Work.Layout.StripSpec`, from `KernelLib` alone

`StripSpec` asks for a word `p` and a constant `K` such that, from a value stack
`Val.cons (Val.int k) v :: tail`, `p` produces `v :: tail` at cost `≤ K * (Lin + 1)`, provided
`vsz (Val.cons (Val.int k) v) ≤ Lin`.

The word is the sequential composition of the two generic `KernelLib` words `unconsV` (which
splits the record into its key and its payload) and `drop` (which discards the key).  The cost
bookkeeping is the only content: `drop`'s cost `Kdr * (vsz (int k) + 1)` is bounded by
`Kdr * (vsz (Val.cons (Val.int k) v) + 1) ≤ Kdr * (Lin + 1)`, and the constant cost `Kun` of
`unconsV` is absorbed by `Kun ≤ Kun * (Lin + 1)`.
-/

set_option autoImplicit false

namespace Work.SB.P3

open HvdH
open Work.Layout

/-- Size of a `cons`-value: the payload encodings plus the `cons` glyph. -/
theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_append]

theorem stripFromKernel (hK : HvdH.KernelLib) : Work.Layout.StripSpec := by
  obtain ⟨pun, Kun, hun⟩ := hK.unconsV
  obtain ⟨pdr, Kdr, hdr⟩ := hK.drop
  refine ⟨Cmd.seq pun pdr, Kun + Kdr, ?_⟩
  intro main Lin k v tail hsz
  have hv : vsz v ≤ Lin := by
    have h := vsz_cons (Val.int k) v
    omega
  refine ⟨hv, ?_⟩
  -- the composition step: `unconsV` then `drop`
  have hstep : ∀ vs mid : List Val,
      (∃ a b rest, vs = Val.cons a b :: rest) →
      (∃ a b rest, vs = Val.cons a b :: rest ∧ mid = a :: b :: rest) →
      mid ≠ [] ∧ Kdr * (vsz (mid.headD Val.nil) + 1) ≤ Kdr * (vsz (vs.headD Val.nil) + 1) := by
    intro vs mid hP hQ
    obtain ⟨a, b, rest, rfl⟩ := hP
    obtain ⟨a', b', rest', heq, hmid⟩ := hQ
    obtain ⟨h1, h2⟩ := List.cons.inj heq
    obtain ⟨rfl, rfl⟩ := Val.cons.inj h1
    subst h2
    rw [hmid]
    refine ⟨by simp, ?_⟩
    simp only [List.headD_cons]
    apply Nat.mul_le_mul_left
    have h := vsz_cons a b
    omega
  have hseq := hK.seq main pun pdr
      (fun vs => ∃ a b rest, vs = Val.cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = Val.cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => Kun)
      (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD Val.nil) + 1))
      (fun vs => Kdr * (vsz (vs.headD Val.nil) + 1))
      (hun main) (hdr main) hstep
  refine hK.conseq main (.seq pun pdr) _ _ _ _ _ _ hseq ?_ ?_ ?_
  · -- the actual precondition `vs = cons (int k) v :: tail` implies the generic one
    intro vs hvs
    subst hvs
    exact ⟨Val.int k, v, tail, rfl⟩
  · -- the composite postcondition collapses to `out = v :: tail`
    intro vs out hvs hpost
    subst hvs
    obtain ⟨mid, ⟨a, b, rest, hvs', hmid⟩, w, rest2, hmid', hout⟩ := hpost
    obtain ⟨h1, h2⟩ := List.cons.inj hvs'
    obtain ⟨h1a, h1b⟩ := Val.cons.inj h1
    subst h1a
    subst h1b
    subst h2
    rw [hmid] at hmid'
    obtain ⟨h1', h2'⟩ := List.cons.inj hmid'
    subst h1'
    subst h2'
    exact hout
  · -- cost bound: `Kun + Kdr * (vsz (cons (int k) v) + 1) ≤ (Kun + Kdr) * (Lin + 1)`
    intro vs hvs
    subst hvs
    simp only [List.headD_cons]
    have hS : vsz (Val.cons (Val.int k) v) + 1 ≤ Lin + 1 := by omega
    have h1 : Kdr * (vsz (Val.cons (Val.int k) v) + 1) ≤ Kdr * (Lin + 1) :=
      Nat.mul_le_mul_left _ hS
    have h2 : Kun ≤ Kun * (Lin + 1) := by
      calc Kun = Kun * 1 := (Nat.mul_one _).symm
        _ ≤ Kun * (Lin + 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : Kun + Kdr * (vsz (Val.cons (Val.int k) v) + 1) ≤
        Kun * (Lin + 1) + Kdr * (Lin + 1) := Nat.add_le_add h2 h1
    simpa [Nat.add_mul] using h3

end Work.SB.P3
