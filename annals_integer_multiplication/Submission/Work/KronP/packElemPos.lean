import Mathlib
import Submission.Work.KronP.defs

namespace Work.KronP

/-
`int z :: rest ↦ int (max z 0) :: rest` (the nonnegative part of an integer), at cost linear in
`isz z`.  The word is `pushVal (int 0) ; IntLib.max`: pushing the constant `0` on top of `int z`
turns the integer `max` (whose first argument is the top of the stack) into `max 0 z = max z 0`,
and `((max z 0).toNat : ℤ) = max z 0` because `max z 0 ≥ 0`.
-/
theorem packElemPos (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (c : ℕ),
      ∀ (main : HvdH.Cmd) (rest : List HvdH.Val) (L : ℕ) (z : ℤ), HvdH.isz z ≤ L →
        HvdH.WordR main q
          (fun vs => vs = HvdH.Val.int z :: rest)
          (fun _ out => out = HvdH.Val.int (((max z 0).toNat : ℤ)) :: rest)
          (fun _ => c * (L + 1)) := by
  obtain ⟨pushP, Kp, hpush⟩ := hK.pushVal
  obtain ⟨maxP, Km, hmax⟩ := hI.max
  refine ⟨HvdH.Cmd.seq (pushP (HvdH.Val.int 0)) maxP, 3 * Kp + 2 * Km, ?_⟩
  intro main rest L z hz
  have hv0 : HvdH.vsz (HvdH.Val.int (0 : ℤ)) = 2 := by decide
  have hisz0 : HvdH.isz (0 : ℤ) = 2 := by decide
  have hpost0 : max (0 : ℤ) z = (((max z 0).toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg (Int.le_max_right z 0), max_comm]
  -- the constant `0` is pushed on top of `int z`
  have hpush' : HvdH.WordR main (pushP (HvdH.Val.int 0))
      (fun vs => vs = HvdH.Val.int z :: rest)
      (fun _ out => out = HvdH.Val.int (0:ℤ) :: (HvdH.Val.int z :: rest))
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int (0:ℤ)) + 1)) :=
    hK.conseq main (pushP (HvdH.Val.int 0)) (fun _ => True)
      (fun vs => vs = HvdH.Val.int z :: rest)
      (fun vs out => out = HvdH.Val.int (0:ℤ) :: vs)
      (fun vs out => out = HvdH.Val.int (0:ℤ) :: (HvdH.Val.int z :: rest))
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int (0:ℤ)) + 1))
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int (0:ℤ)) + 1))
      (hpush main (HvdH.Val.int 0))
      (fun vs _ => trivial)
      (fun vs out hvs h => by rw [h, hvs])
      (fun vs _ => le_rfl)
  -- the integer `max` (top = first argument) applied to `0` and `z`
  have hmax' : HvdH.WordR main maxP
      (fun vs => ∃ (a b : ℤ) (r : List HvdH.Val),
        vs = HvdH.Val.int a :: HvdH.Val.int b :: r ∧ True)
      (fun vs out => ∃ (a b : ℤ) (r : List HvdH.Val),
        vs = HvdH.Val.int a :: HvdH.Val.int b :: r ∧ out = HvdH.Val.int (max a b) :: r)
      (HvdH.binCost (fun a b => Km * (HvdH.isz a + HvdH.isz b))) := hmax main
  have hseq := hK.seq main (pushP (HvdH.Val.int 0)) maxP
      (fun vs => vs = HvdH.Val.int z :: rest)
      (fun _ out => out = HvdH.Val.int (0:ℤ) :: (HvdH.Val.int z :: rest))
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int (0:ℤ)) + 1))
      (fun vs => ∃ (a b : ℤ) (r : List HvdH.Val),
        vs = HvdH.Val.int a :: HvdH.Val.int b :: r ∧ True)
      (fun vs out => ∃ (a b : ℤ) (r : List HvdH.Val),
        vs = HvdH.Val.int a :: HvdH.Val.int b :: r ∧ out = HvdH.Val.int (max a b) :: r)
      (HvdH.binCost (fun a b => Km * (HvdH.isz a + HvdH.isz b)))
      (fun _ => Km * (HvdH.isz (0:ℤ) + HvdH.isz z))
      hpush' hmax'
      (fun vs mid hvs hmid => by
        subst hmid
        refine ⟨⟨0, z, rest, rfl, trivial⟩, ?_⟩
        show HvdH.binCost (fun a b => Km * (HvdH.isz a + HvdH.isz b))
          (HvdH.Val.int (0:ℤ) :: HvdH.Val.int z :: rest) ≤ Km * (HvdH.isz (0:ℤ) + HvdH.isz z)
        rfl)
  exact hK.conseq main (HvdH.Cmd.seq (pushP (HvdH.Val.int 0)) maxP)
      (fun vs => vs = HvdH.Val.int z :: rest)
      (fun vs => vs = HvdH.Val.int z :: rest)
      (fun vs out => ∃ mid, mid = HvdH.Val.int (0:ℤ) :: (HvdH.Val.int z :: rest) ∧
        (∃ (a b : ℤ) (r : List HvdH.Val), mid = HvdH.Val.int a :: HvdH.Val.int b :: r ∧
          out = HvdH.Val.int (max a b) :: r))
      (fun _ out => out = HvdH.Val.int (((max z 0).toNat : ℤ)) :: rest)
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int (0:ℤ)) + 1) + Km * (HvdH.isz (0:ℤ) + HvdH.isz z))
      (fun _ => (3 * Kp + 2 * Km) * (L + 1))
      hseq
      (fun vs h => h)
      (fun vs out hvs h => by
        obtain ⟨mid, hmid, hrest⟩ := h
        obtain ⟨a, b, r, heq, hout⟩ := hrest
        rw [hmid] at heq
        simp only [List.cons.injEq, HvdH.Val.int.injEq] at heq
        obtain ⟨h0a, hzb, hrr⟩ := heq
        rw [← h0a, ← hzb, ← hrr, hpost0] at hout
        exact hout)
      (fun vs hvs => by
        rw [hv0, hisz0]
        have hA : 2 + HvdH.isz z ≤ 2 * (L + 1) := by omega
        have hB : Km * (2 + HvdH.isz z) ≤ (2 * Km) * (L + 1) := by
          calc Km * (2 + HvdH.isz z) ≤ Km * (2 * (L + 1)) := Nat.mul_le_mul_left _ hA
            _ = (2 * Km) * (L + 1) := by ring
        have hC : 3 * Kp ≤ (3 * Kp) * (L + 1) := by
          have h := Nat.mul_le_mul_left (3 * Kp) (by omega : 1 ≤ L + 1)
          simpa using h
        have hD : (3 * Kp) * (L + 1) + (2 * Km) * (L + 1) =
            (3 * Kp + 2 * Km) * (L + 1) := by ring
        omega)

end Work.KronP
