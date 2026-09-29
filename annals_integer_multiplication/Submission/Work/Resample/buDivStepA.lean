import Mathlib
import Submission.Work.Resample.buDivDefs
import Submission.Work.Resample.buWdKit

/-!
# `Work.Resample.buDivStepA`

First phase of the shift word of `Work.Resample.buWdDiv`: from the window
`[Ad, p, α] ++ V` produce `[α, α, Ad, p, α] ++ V`, i.e. copy the `α` entry of the block twice
on top (the two copies are the arguments of `IntLib.mulS` used in the next phase to form
`buDivZ1 α = α·α`).  Two `KernelLib.pick` steps (`k = 2`, then `k = 0`) suffice; the cost is
absorbed by the uniform size bound `buSZ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

theorem buDivStepA (KL : HvdH.KernelLib) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (Ad : ℤ) (hAd : HvdH.isz Ad ≤ Work.Resample.buSZ p) (V : List HvdH.Val), Work.Resample.Pipe main prog ([HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) ([HvdH.Val.int (α : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) (K * (Work.Resample.buSZ p + 8) ^ 2) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  refine ⟨Cmd.seq (pickProg 2) (pickProg 0), Kpk, ?_⟩
  intro main p α hα hαp Ad hAd V
  have hαlt : α < 2 ^ p := by
    have h3 : p < 2 ^ p := Nat.lt_two_pow_self
    have h4 : α ≤ α ^ 2 := by nlinarith
    omega
  have hsAd : HvdH.isz Ad ≤ buSZ p := hAd
  have hsp : HvdH.isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ p
  have hsα : HvdH.isz ((α : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hαlt
  -- step 1: pick the `α` entry (`k = 2`) to the top
  have s1 : Pipe main (pickProg 2)
      ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V)
      ([HvdH.Val.int (α:ℤ), HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V)
      (Kpk * 3 * (HvdH.isz Ad + HvdH.isz ((p:ℤ)) + HvdH.isz ((α:ℤ)) + 1)) := by
    have h := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick
      (A := [HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V) (k := 2) (by simp)
      (v := HvdH.Val.int (α:ℤ)) (by simp)
    refine Pipe.le h (le_of_eq ?_)
    have hsz : szl (([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V).take (2+1))
        = HvdH.isz Ad + HvdH.isz ((p:ℤ)) + HvdH.isz ((α:ℤ)) := by
      rw [show ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V).take (2+1)
            = [HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] from by simp, szl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    rw [hsz]
  -- step 2: pick the (new) top `α` (`k = 0`) again
  have s2 : Pipe main (pickProg 0)
      ([HvdH.Val.int (α:ℤ)]
        ++ ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V))
      ([HvdH.Val.int (α:ℤ), HvdH.Val.int (α:ℤ), HvdH.Val.int Ad, HvdH.Val.int (p:ℤ),
        HvdH.Val.int (α:ℤ)] ++ V)
      (Kpk * (0+1) * (HvdH.isz ((α:ℤ)) + 1)) := by
    have h := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick
      (A := [HvdH.Val.int (α:ℤ)]
        ++ ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V))
      (k := 0) (by simp) (v := HvdH.Val.int (α:ℤ)) (by simp)
    refine Pipe.le h (le_of_eq ?_)
    have hsz : szl (([HvdH.Val.int (α:ℤ)]
        ++ ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V)).take (0+1))
        = HvdH.isz ((α:ℤ)) := by
      rw [show ([HvdH.Val.int (α:ℤ)]
            ++ ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V)).take (0+1)
            = [HvdH.Val.int (α:ℤ)] from by simp, szl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    rw [hsz]
  have hall : Pipe main (Cmd.seq (pickProg 2) (pickProg 0))
      ([HvdH.Val.int Ad, HvdH.Val.int (p:ℤ), HvdH.Val.int (α:ℤ)] ++ V)
      ([HvdH.Val.int (α:ℤ), HvdH.Val.int (α:ℤ), HvdH.Val.int Ad, HvdH.Val.int (p:ℤ),
        HvdH.Val.int (α:ℤ)] ++ V)
      (Kpk * 3 * (HvdH.isz Ad + HvdH.isz ((p:ℤ)) + HvdH.isz ((α:ℤ)) + 1)
        + Kpk * (0+1) * (HvdH.isz ((α:ℤ)) + 1)) :=
    Pipe.comp s1 s2
  refine Pipe.le hall ?_
  have hnorm : Kpk * (0+1) * (HvdH.isz ((α:ℤ)) + 1) = Kpk * (HvdH.isz ((α:ℤ)) + 1) := by ring
  rw [hnorm]
  have h3 : 3 * (3 * buSZ p + 1) + (buSZ p + 1) ≤ (buSZ p + 8) ^ 2 := by nlinarith
  calc Kpk * 3 * (HvdH.isz Ad + HvdH.isz ((p:ℤ)) + HvdH.isz ((α:ℤ)) + 1)
        + Kpk * (HvdH.isz ((α:ℤ)) + 1)
      = Kpk * (3 * (HvdH.isz Ad + HvdH.isz ((p:ℤ)) + HvdH.isz ((α:ℤ)) + 1)
          + (HvdH.isz ((α:ℤ)) + 1)) := by ring
    _ ≤ Kpk * (3 * (3 * buSZ p + 1) + (buSZ p + 1)) := by
        apply Nat.mul_le_mul_left
        nlinarith
    _ ≤ Kpk * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left Kpk h3

end Work.Resample
