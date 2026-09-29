import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.Params.steps

/-!
# `packElemNeg`: the negative part of an integer value

`int z :: rest  ↦  int ((max (-z) 0).toNat) :: rest`, i.e. `z ↦ max (-z) 0 = |z|` for `z < 0`
and `0` for `z ≥ 0`.  The straight-line program is `neg ; push 0 ; max`: negate the top value,
push the constant `0` and take the maximum, which is `-z` when `z < 0` and `0` otherwise.

The cost is linear in `isz z ≤ L`, hence `≤ c·(L+1)`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- `((max (-z) 0).toNat : ℤ) = max (-z) 0`: the negative part of an integer is a natural. -/
theorem toNat_max_neg (z : ℤ) : (((max (-z) 0).toNat : ℕ) : ℤ) = max (-z) 0 :=
  Int.toNat_of_nonneg (le_max_right _ _)

/-- `isz (-z) = isz z`. -/
theorem isz_neg (z : ℤ) : HvdH.isz (-z) = HvdH.isz z := by
  simp [HvdH.isz]

theorem isz_zero : HvdH.isz (0 : ℤ) = 2 := rfl

theorem packElemNeg (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (c : ℕ),
      ∀ (main : HvdH.Cmd) (rest : List HvdH.Val) (L : ℕ) (z : ℤ), HvdH.isz z ≤ L →
        HvdH.WordR main q
          (fun vs => vs = HvdH.Val.int z :: rest)
          (fun _ out => out = HvdH.Val.int (((max (-z) 0).toNat : ℤ)) :: rest)
          (fun _ => c * (L + 1)) := by
  obtain ⟨pneg, Kn, hneg⟩ := hI.neg
  obtain ⟨ppush, Kp, hpush⟩ := hK.pushVal
  obtain ⟨pmax, Kx, hmax⟩ := hI.max
  refine ⟨.seq pneg (.seq (ppush (.int 0)) pmax), Kn + 3 * Kp + 3 * Kx, ?_⟩
  intro main rest L z hz
  have hv0 : HvdH.vsz (HvdH.Val.int (0 : ℤ)) = 2 := by
    rw [vsz_int_eq]; exact isz_zero
  have hnegz : HvdH.isz (-z) = HvdH.isz z := isz_neg z
  have hX : max (0 : ℤ) (-z) = ((max (-z) 0).toNat : ℤ) := by
    rw [max_comm]; exact (toNat_max_neg z).symm
  -- step 1: negate
  have h1 : HvdH.WordR main pneg (fun vs => vs = HvdH.Val.int z :: rest)
      (fun _ out => out = HvdH.Val.int (-z) :: rest) (fun _ => Kn * HvdH.isz z) :=
    Work.Params.unStepP hK (hneg main) z rest trivial (-z) rfl _ le_rfl
  -- step 2: push the constant `0`
  have h2 : HvdH.WordR main (ppush (.int 0)) (fun vs => vs = HvdH.Val.int (-z) :: rest)
      (fun _ out => out = HvdH.Val.int 0 :: HvdH.Val.int (-z) :: rest)
      (fun _ => Kp * (HvdH.vsz (HvdH.Val.int 0) + 1)) :=
    Work.Params.pushValStep hK (hpush main) (.int 0) (.int (-z) :: rest) _ le_rfl
  -- step 3: take the maximum
  have h3 : HvdH.WordR main pmax
      (fun vs => vs = HvdH.Val.int 0 :: HvdH.Val.int (-z) :: rest)
      (fun _ out => out = HvdH.Val.int (((max (-z) 0).toNat : ℤ)) :: rest)
      (fun _ => Kx * (HvdH.isz 0 + HvdH.isz (-z))) :=
    Work.Params.binStepP hK (hmax main) 0 (-z) rest trivial _ hX _ le_rfl
  have hIn := Work.Params.seqC hK h2 h3
  have hFull := Work.Params.seqC hK h1 hIn
  refine Work.Params.conseqC hK hFull ?_
  rw [hv0, hnegz, isz_zero]
  have hL : HvdH.isz z ≤ L := hz
  nlinarith [hL, Nat.zero_le (HvdH.isz z), Nat.zero_le L, Nat.zero_le Kn, Nat.zero_le Kp,
    Nat.zero_le Kx]

end Work.KronP
