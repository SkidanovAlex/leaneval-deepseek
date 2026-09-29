import Mathlib
import Submission.Work.Transform.chirpAux
import Submission.Work.Transform.Defs
import Submission.Work.Transform.conjKit
import Submission.Work.Transform.conjRowWord
import Submission.Work.Transform.conjElemWord

/-!
# `Work.Transform.conjVecWord`: conjugating a vector of fixed-point complex coefficients

Given `p` and a vector `a ∈ C̃◦ⁿ` on the value stack, with `int p` sitting above it,
`Work.Transform.conjVecWord` computes the pointwise conjugate `ab = a.map conjPair`
(negate every imaginary part) of the vector:

`int p :: cvecVal a :: R ↦ cvecVal ab :: int p :: R`,

at cost `K (n p²) + K`.  The program is `KernelLib.roll 1 ;;; conjRow`

* `KernelLib.roll 1` puts the parameters in the order expected by the row word
  (`cvecVal a :: int p :: R`), and
* `Work.Transform.conjRowWord_of` (`Submission/Work/Transform/conjRowWord.lean`) walks the row with
  the `KernelLib.mapList` loop, conjugating every coefficient with the per-coefficient word of
  `Work.Transform.conjElemWord` (`Submission/Work/Transform/conjElemWord.lean`), whose statement is
  the `Prop` `Work.Transform.ConjElemSpec`.

Conjugation is exact on fixed-point values (`(x, y) ↦ (x, -y)`), and `inDisc` is preserved because
`x² + y² = x² + (-y)²`; so the output vector is still in `C̃◦ⁿ` and has the same length.
-/

namespace Work.Transform

theorem conjVecWord : HvdH.KernelLib → HvdH.IntLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p n : ℕ) (a : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 1 ≤ n → a.length = n → HvdH.InDiscVec p n a →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.cvecVal a :: R)
        (fun vs out => vs = HvdH.Val.int p :: HvdH.cvecVal a :: R ∧
          ∃ (ab : List (ℤ × ℤ)),
            out = HvdH.cvecVal ab :: HvdH.Val.int p :: R ∧
            ab.length = n ∧ HvdH.InDiscVec p n ab ∧
            ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2))
        (fun _ => K * (n * p ^ 2) + K) := by
  intro hKer hInt
  exact conjVecWord_of hKer hInt (conjElemWord hKer hInt)

end Work.Transform
