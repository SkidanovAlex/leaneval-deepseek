import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Kernel.encodeNatBits

namespace Work.Resample

open HvdH

/-- `Computability.encodeNat` has the length of the binary size (`Nat.bits`). -/
theorem buScStripWord_encodeNat_length (n : ℕ) :
    (Computability.encodeNat n).length = n.size := by
  rw [Work.Kernel.encodeNatBits]
  exact Nat.size_eq_bits_len n

/-- The encoding of an integer value has length `isz`. -/
theorem buScStripWord_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  simp only [Val.enc, vsz, List.length_cons, List.length_append, List.length_map, List.length_nil,
    isz, buScStripWord_encodeNat_length]

/-- The element word of the final `mapList`: it drops the key of a record.
`q := KL.unconsV ;; KL.drop` works, with `K := Ku + Kd + 1`. -/
theorem buScStripWord (KL : KernelLib) :
    ∃ (q : Cmd) (K : ℕ),
    ∀ (main : Cmd) (k a b : ℤ) (T : List Val),
      WordR main q
        (fun vs => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
        (fun _ out => out = Val.cons (Val.int a) (Val.int b) :: T)
        (fun _ => K * (isz k + isz a + isz b + 2)) := by
  obtain ⟨up, Ku, hup⟩ := KL.unconsV
  obtain ⟨dp, Kd, hdp⟩ := KL.drop
  refine ⟨Cmd.seq up dp, Ku + Kd + 1, ?_⟩
  intro main k a b T
  -- leg 1: `unconsV` splits the record `cons (int k) (cons (int a) (int b))`
  have h1 : WordR main up
      (fun vs : List Val => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
      (fun _ out => out = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Ku) := by
    refine KL.conseq main up
      (fun vs : List Val => ∃ x y rest, vs = Val.cons x y :: rest)
      (fun vs : List Val => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
      (fun vs out => ∃ x y rest, vs = Val.cons x y :: rest ∧ out = x :: y :: rest)
      (fun _ out => out = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Ku) (fun _ => Ku) (hup main)
      (fun vs hvs => ⟨Val.int k, Val.cons (Val.int a) (Val.int b), T, hvs⟩)
      ?_ (fun vs _ => le_rfl)
    intro vs out hvs hpost
    obtain ⟨x, y, rest, hvs', hout'⟩ := hpost
    rw [hvs] at hvs'
    rw [List.cons.injEq] at hvs'
    obtain ⟨hva, hrest⟩ := hvs'
    rw [Val.cons.injEq] at hva
    obtain ⟨hak, hab⟩ := hva
    rw [← hak, ← hab, ← hrest] at hout'
    exact hout'
  -- leg 2: `drop` removes the key, keeping the payload and the rest of the stack
  have h2 : WordR main dp
      (fun vs : List Val => vs = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ out => out = Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Kd * (isz k + 1)) := by
    refine KL.conseq main dp
      (fun vs : List Val => vs ≠ [])
      (fun vs : List Val => vs = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun _ out => out = Val.cons (Val.int a) (Val.int b) :: T)
      (fun vs => Kd * (vsz (vs.headD Val.nil) + 1))
      (fun _ => Kd * (isz k + 1)) (hdp main)
      ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hpost
      obtain ⟨v, rest, hvs', hout⟩ := hpost
      rw [hvs] at hvs'
      rw [List.cons.injEq] at hvs'
      obtain ⟨hv, hrest⟩ := hvs'
      rw [← hrest] at hout
      exact hout
    · intro vs hvs
      rw [hvs]
      simp [buScStripWord_vsz_int]
  -- the two legs in sequence
  have hseq := KL.seq main up dp
      (fun vs : List Val => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
      (fun _ out => out = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Ku)
      (fun vs : List Val => vs = Val.int k :: Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ out => out = Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Kd * (isz k + 1)) (fun _ => Kd * (isz k + 1))
      h1 h2
      (fun vs mid _ hmid => ⟨hmid, le_rfl⟩)
  refine KL.conseq main (Cmd.seq up dp)
      (fun vs : List Val => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
      (fun vs : List Val => vs = Val.cons (Val.int k) (Val.cons (Val.int a) (Val.int b)) :: T)
      _ (fun _ out => out = Val.cons (Val.int a) (Val.int b) :: T)
      (fun _ => Ku + Kd * (isz k + 1))
      (fun _ => (Ku + Kd + 1) * (isz k + isz a + isz b + 2))
      hseq (fun _ hvs => hvs) ?_ ?_
  · intro vs out _ hpost
    obtain ⟨mid, _, hout⟩ := hpost
    exact hout
  · intro vs _
    have hA : Kd * (isz k + 1) ≤ Kd * (isz k + isz a + isz b + 2) :=
      Nat.mul_le_mul_left Kd (by omega)
    have hB : Ku ≤ Ku * (isz k + isz a + isz b + 2) := by
      simpa using Nat.mul_le_mul_left Ku (show 1 ≤ isz k + isz a + isz b + 2 by omega)
    calc Ku + Kd * (isz k + 1)
        ≤ Ku * (isz k + isz a + isz b + 2) + Kd * (isz k + isz a + isz b + 2) :=
          Nat.add_le_add hB hA
      _ = (Ku + Kd) * (isz k + isz a + isz b + 2) := by ring
      _ ≤ (Ku + Kd + 1) * (isz k + isz a + isz b + 2) :=
          Nat.mul_le_mul_right _ (by omega)

end Work.Resample
