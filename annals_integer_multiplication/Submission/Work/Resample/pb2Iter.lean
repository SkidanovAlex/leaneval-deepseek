import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs

/-! Guidance from the project lead (the requester):

LEAD (endgame: Resample's B half is the LAST open piece of the whole problem — speed matters). This statement is the
MIRROR of the already PROVED `Work.Resample.paIter(paProofs1.lean)` (Submission/Work/Resample/). Start by COPYING that file's proof and
adapting it; do not design anything new. Mirror dictionary (definitions in Submission/Work/Resample/pb2Defs.lean):
PAVec/PAInv/PAMid/PABr/PAIterBrF ↦ PB2Vec/PB2Inv/PB2Mid/PB2Br/PB2IterBrF; the array flows from shape ts (input,
ts.prod entries) to shape ss (output); list iteration is `axisIter ts ss Φ` with Φ j : (Fin t_j → ℤ×ℤ) → (Fin s_j → ℤ×ℤ);
applyAlong arguments per axis j are A = (ss.take j).prod, m = t_j, n = s_j, B = (ts.drop (j+1)).prod; stack 2 holds the
remaining INPUT dims (ts.drop j), stack 3 the remaining OUTPUT dims (ss.drop j), stack 6 (ss.take j).prod, stack 7 s_j;
SliceSpecAtA Kb p α s t prep q Φ P ↦ SliceSpecAt prep q Kb p α s t Φ P (argument order differs; its q cost has the extra
Kb(t+1)(p+1)² term, already in PB2Br); resAop/rA ↦ resBop/rB. Size bounds keep ts.prod (sᵢ < tᵢ, so every intermediate
array has ≤ ts.prod entries: (ss.take j).prod ≤ (ts.take j).prod). NEVER import pbSetupF, pbRoundF, pbIterGo*, pbIterF*
(obsolete route; pbSetupF needs 17 GB). Split into children only where the A-side proof was split.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- Mirror of paIter for the B half: the D-fold iteration of one axis step. -/
theorem pb2Iter (Kb Kc0 : ℕ) (round : HvdH.Cmd) :
    ∃ (iter : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
        (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      (∀ j < HvdH.D, Work.Resample.WordP main round
        (fun vs rest a => Work.Resample.PB2Inv p α ss ts Φ zs0 j vs rest a)
        (fun vs rest a out b => Work.Resample.PB2Inv p α ss ts Φ zs0 (j + 1) out rest b)
        (fun _ _ _ => Kc0 * Work.Resample.PB2Br Kb Cm p α ss ts j)) →
      Work.Resample.WordP main iter
        (fun vs rest a => Work.Resample.PB2Inv p α ss ts Φ zs0 0 vs rest a)
        (fun vs rest a out b => Work.Resample.PB2Inv p α ss ts Φ zs0 HvdH.D out rest b)
        (fun _ _ _ => Kc * Work.Resample.PB2IterBrF Kb Cm p α ss ts) := by
  refine ⟨paIterN round HvdH.D, Kc0 + 1, ?_⟩
  intro main N Cm p α ss ts Φ zs0 hpar hmon hmb hN hround
  have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
  have hiter := WordP.iterate (main := main) round (fun j => PB2Inv p α ss ts Φ zs0 j)
    (fun j => Kc0 * PB2Br Kb Cm p α ss ts j) HvdH.D 0 hD1
    (fun t _ ht2 => hround t (by omega))
  refine WordP.mono hiter (fun vs rest a => ?_)
  have h1 : (∑ t ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts (0 + t))
      ≤ (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j) :=
    Finset.sum_le_sum (fun t _ => le_of_eq (by rw [Nat.zero_add]))
  have h2 : (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j) + 1
      = PB2IterBrF Kb Cm p α ss ts := rfl
  rw [← Finset.mul_sum]
  calc Kc0 * (∑ t ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts (0 + t))
      ≤ Kc0 * (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j) := Nat.mul_le_mul_left _ h1
    _ ≤ (Kc0 + 1) * ((∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j) + 1) := by
        nlinarith [Nat.zero_le Kc0, Nat.zero_le (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j)]
    _ = (Kc0 + 1) * PB2IterBrF Kb Cm p α ss ts := by rw [h2]

end Work.Resample
