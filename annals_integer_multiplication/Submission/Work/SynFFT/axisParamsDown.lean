import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `Work.SynFFT.axisParamsDown`

The word that moves the four *parameter* values `k sgn r p` of a synthetic-FFT axis step above the
three *shape* values `A t B` of the axis decomposition, leaving the array `X` (and everything below)
untouched:

`X :: A :: t :: B :: k :: sgn :: r :: p :: rest ↦ X :: k :: sgn :: r :: p :: A :: t :: B :: rest`.

Both blocks lie on stack 0 with the array on top, so the permutation is a *rotation of the seven
values below the array*: the block `[A,t,B,k,sgn,r,p]` is rotated right by `4` (i.e. left by `3`),
which lands `[k,sgn,r,p,A,t,B]` after the (fixed) array `X`.

## The program

A rotation of the values at positions `1, …, 7` is realised by `roll 7` (bringing the *last* of them
— the 8th value — to the very top) followed by `swap`-ing it back below `X`; four of these rounds
rotate by `4`.  The final `roll 4` then brings `X` (which the four rounds have pushed down to
position `4`) back to the top, restoring the array without touching anything else:

| state | operation |
|---|---|
| `X A t B k sgn r p` | |
| `p X A t B k sgn r` | `roll 7` |
| `r p X A t B k sgn` | `roll 7` |
| `sgn r p X A t B k` | `roll 7` |
| `k sgn r p X A t B` | `roll 7` |
| `X k sgn r p A t B` | `roll 4` |

The equivalent formulation with `swap` (`(roll 7 ;;; swap)` four times) also works, but the
`roll`-only version above is one step shorter and uses a single kernel primitive.

## Cost

Every `roll` costs `Kr * (j+1) * (sum of the sizes of the first j+1 values + 1)`, which is at most
`Kr * 8 * W` with `W = Σ vsz (first 8 values) + 1`; five steps give `5 * (Kr * 8 * W) = (40 * Kr) * W`,
so `K = 40 * Kr` is a uniform constant (independent of `main`, the values and the parameters), as
required by the interface.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- Cost of one `roll` step, against the uniform per-step budget `Kr * (8 * W)`. -/
private theorem rollCost_le (Kr W j Xs : ℕ) (hj : j + 1 ≤ 8) (h : Xs + 1 ≤ W) :
    Kr * (j + 1) * (Xs + 1) ≤ Kr * (8 * W) := by
  rw [mul_assoc]
  refine Nat.mul_le_mul_left Kr ?_
  calc (j + 1) * (Xs + 1) ≤ 8 * (Xs + 1) := Nat.mul_le_mul_right _ hj
    _ ≤ 8 * W := Nat.mul_le_mul_left 8 h

theorem axisParamsDown (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X A t B k sgn r p : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = X :: A :: t :: B :: k :: sgn :: r :: p :: rest)
        (fun _ out => out = X :: k :: sgn :: r :: p :: A :: t :: B :: rest)
        (fun vs => K * (HvdH.vsz X + HvdH.vsz A + HvdH.vsz t + HvdH.vsz B + HvdH.vsz k +
          HvdH.vsz sgn + HvdH.vsz r + HvdH.vsz p + 1)) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  refine ⟨rollP 7 ;;; rollP 7 ;;; rollP 7 ;;; rollP 7 ;;; rollP 4, 40 * Kr, ?_⟩
  intro main X A t B k sgn r p rest
  set W : ℕ := vsz X + vsz A + vsz t + vsz B + vsz k + vsz sgn + vsz r + vsz p + 1 with hW
  set Db : ℕ := Kr * (8 * W) with hDb
  -- one `roll j` step against the uniform budget `Db`
  have hstep : ∀ (j : ℕ) (L : List Val), j + 1 ≤ 8 → ((L.take (j+1)).map vsz).sum + 1 ≤ W →
      j < L.length →
      WordR main (rollP j) (fun vs => vs = L) (fun _ out => out = L.getD j .nil :: L.eraseIdx j)
        (fun _ => Db) := by
    intro j L hj hsum hlen
    refine rollStep (hroll main) j L hlen Db ?_
    rw [hDb]
    exact rollCost_le Kr W j _ hj hsum
  have e1 : (((X :: A :: t :: B :: k :: sgn :: r :: p :: rest).take 8).map vsz).sum + 1 ≤ W := by
    rw [hW]; simp; omega
  have h1 : WordR main (rollP 7)
      (fun vs => vs = X :: A :: t :: B :: k :: sgn :: r :: p :: rest)
      (fun _ out => out = p :: X :: A :: t :: B :: k :: sgn :: r :: rest) (fun _ => Db) := by
    simpa using hstep 7 (X :: A :: t :: B :: k :: sgn :: r :: p :: rest) (by norm_num) e1 (by simp)
  have e2 : (((p :: X :: A :: t :: B :: k :: sgn :: r :: rest).take 8).map vsz).sum + 1 ≤ W := by
    rw [hW]; simp; omega
  have h2 : WordR main (rollP 7)
      (fun vs => vs = p :: X :: A :: t :: B :: k :: sgn :: r :: rest)
      (fun _ out => out = r :: p :: X :: A :: t :: B :: k :: sgn :: rest) (fun _ => Db) := by
    simpa using hstep 7 (p :: X :: A :: t :: B :: k :: sgn :: r :: rest) (by norm_num) e2 (by simp)
  have e3 : (((r :: p :: X :: A :: t :: B :: k :: sgn :: rest).take 8).map vsz).sum + 1 ≤ W := by
    rw [hW]; simp; omega
  have h3 : WordR main (rollP 7)
      (fun vs => vs = r :: p :: X :: A :: t :: B :: k :: sgn :: rest)
      (fun _ out => out = sgn :: r :: p :: X :: A :: t :: B :: k :: rest) (fun _ => Db) := by
    simpa using hstep 7 (r :: p :: X :: A :: t :: B :: k :: sgn :: rest) (by norm_num) e3 (by simp)
  have e4 : (((sgn :: r :: p :: X :: A :: t :: B :: k :: rest).take 8).map vsz).sum + 1 ≤ W := by
    rw [hW]; simp; omega
  have h4 : WordR main (rollP 7)
      (fun vs => vs = sgn :: r :: p :: X :: A :: t :: B :: k :: rest)
      (fun _ out => out = k :: sgn :: r :: p :: X :: A :: t :: B :: rest) (fun _ => Db) := by
    simpa using hstep 7 (sgn :: r :: p :: X :: A :: t :: B :: k :: rest) (by norm_num) e4 (by simp)
  have e5 : (((k :: sgn :: r :: p :: X :: A :: t :: B :: rest).take 5).map vsz).sum + 1 ≤ W := by
    rw [hW]; simp; omega
  have h5 : WordR main (rollP 4)
      (fun vs => vs = k :: sgn :: r :: p :: X :: A :: t :: B :: rest)
      (fun _ out => out = X :: k :: sgn :: r :: p :: A :: t :: B :: rest) (fun _ => Db) := by
    simpa using hstep 4 (k :: sgn :: r :: p :: X :: A :: t :: B :: rest) (by norm_num) e5 (by simp)
  have c12 := WordR_seqC h1 h2
  have c123 := WordR_seqC c12 h3
  have c1234 := WordR_seqC c123 h4
  have c12345 := WordR_seqC c1234 h5
  refine WordR_weaken c12345 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs _
  have e : (((Db + Db) + Db) + Db) + Db = 5 * Db := by ring
  rw [e, hDb]
  have e2' : 5 * (Kr * (8 * W)) = (40 * Kr) * W := by ring
  rw [e2']

end Work.SynFFT
