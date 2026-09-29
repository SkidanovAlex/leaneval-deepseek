import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.buPrepKit
import Submission.Work.Resample.buColsWord
import Submission.Work.Resample.buLamWord

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buPrep` — the uniform preparation word of the one-dimensional `B̃` resampling

`prep` reads the four integer parameters `p, α, s, t` from the top of the value stack and pushes
the static table `buTabList p α s t` (paper §4, Lemmas 4.8–4.12) in cost `K·(t+1)·(p+1)^K`.

The composition of the eight sub-words is `Work.Resample.buPrepCore` and its assembly from the
library Props is `Work.Resample.buPrepOfTwo`, both in `Submission/Work/Resample/buPrepKit.lean`.
Here the two sub-words whose modules are built separately are supplied: the `2m` labelled weight
columns `buL10` (`Work.Resample.buColsWord`) and the `t` `λ`-keys `buL7` (`Work.Resample.buLamWord`).
-/

set_option maxRecDepth 10000

/-- The uniform preparation word: reads `p, α, s, t` and pushes the static table `buTabList`. -/
theorem buPrep (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (prep : HvdH.Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
    HvdH.WordR main prep
      (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest)
      (fun _ => K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨hornerProg, Kh, hh⟩ := buHornerWord KL IL
  obtain ⟨wtElem, Kwe, hWe⟩ := buWtElem KL IL hornerProg Kh hh
  obtain ⟨colsProg, K10, h10⟩ := buColsWord KL IL LL wtElem Kwe hWe
  obtain ⟨lamProg, K7, h7⟩ := buLamWord KL IL LL
  exact buPrepOfTwo KL IL LL colsProg K10 h10 lamProg K7 h7

end Work.Resample
