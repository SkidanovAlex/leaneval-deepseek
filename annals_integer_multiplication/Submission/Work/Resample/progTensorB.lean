import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.specs
import Submission.Work.Resample.progTensorB_mirror

/-!
# The tensoring program `B̃` of paper Theorem 4.1 (the `B` half)

`progTensorB` is the `B` half of Theorem 4.1: the word applies the uniform one-dimensional
resampling word of `Work.Resample.SliceSpecB` along all `D = 1729` axes of the flat lexicographic
array `zs` of `ts.prod` fixed-point complex numbers, and identifies the result with
`resBop ss ts α (fxVec p ts.prod zs)` with error `< D p²` and cost `resCost K Cm p α ts`.

The program and its proof are assembled in `Submission/Work/Resample/progTensorB_mirror.lean` as a
mirror of the `A` half (`Work.Resample.progTensorA`, `Submission/Work/Resample/progTensorA.lean`):

* `pb2SetupE` — the prologue,
* `pb2StageE` / `pb2ApplyE` — the two halves of one axis step (`prep`, then
  `LayoutLib.applyAlong (comb q)` followed by the glyph-marker drain of the table),
* `pb2Iter` — the `D`-fold iteration,
* `pb2FinalD` — the epilogue,
* `pb2FinApproxD` — the analytic end (the error `< D p²`),
* `pb2CostD` — the cost arithmetic against `HvdH.resCost`.

This file only re-exports that theorem under the name required by the challenge.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

theorem progTensorB (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (RM : HvdH.ResMath1DProp) (hB : Work.Resample.SliceSpecB KL IL LL FL RM) :
    ∃ (progB : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
      HvdH.WordR main progB
        (fun vs => ∃ (zs : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = .int p :: .int α :: HvdH.intList ss :: HvdH.intList ts :: HvdH.cvecVal zs :: rest ∧
          HvdH.InDiscVec p ts.prod zs)
        (fun vs out => ∃ (zs : List (ℤ × ℤ)) (rest : List HvdH.Val) (ws : List (ℤ × ℤ)),
          vs = .int p :: .int α :: HvdH.intList ss :: HvdH.intList ts :: HvdH.cvecVal zs :: rest ∧
          out = HvdH.cvecVal ws :: rest ∧
          HvdH.Approx p ws (Work.Resample.resBop ss ts α (HvdH.fxVec p ts.prod zs))
            (HvdH.D * p ^ 2 : ℕ))
        (fun _ => HvdH.resCost K Cm p α ts) :=
  progTensorB_mirror KL IL LL FL RM hB

end Work.Resample
