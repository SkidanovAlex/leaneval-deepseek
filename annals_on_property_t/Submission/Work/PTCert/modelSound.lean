import Mathlib
import Submission.Work.PTCert.Checkers
import Submission.Work.PTCert.WordModel
import Submission.Work.PTCert.LetterEval
import Submission.Work.PTCert.ApplyLetter
import Submission.Work.PTCert.lprodProdImg
import Submission.Work.RouteB.FreeGroupAutDecEq

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions: `Submission/Work/PTCert/Checkers.lean` (word model: `evalW`, `redW`, `invW`, `letterImg`,
`applyLetter`, `prodImg`, `modelEq`, `lprod`).  Prove `ModelSound r`.  Plan:
(1) `evalW (redW w) = evalW w` (free reduction: `redStep` cancels `c` against `c ^^^ 1`, which is the
    inverse letter; induction on the foldl with the invariant `evalW (acc.reverse) * evalW rest`), and
    `evalW (invW w) = (evalW w)⁻¹`, `evalW (u ++ v) = evalW u * evalW v`.
(2) Letter images: for `k < NB1 r` and `i < r`, `(b1 r k) (FreeGroup.of i) = evalW (letterImg r k i)`
    (unfold `b1`; the four kinds are `rho/rhoNeg/lam/lamNeg` of FreeGroupAut.lean with
    `rho_apply_self`/`rho_apply_other` style lemmas; letter `0` is `1`).  Helper lemmas about `b1` already
    exist in Submission/Work/PTCert/ (`LetterCore.lean`, `LetterAPI.lean`, `letterAction.lean`) — reuse.
(3) Hence for every word `w` with letters `< 2r`: `(b1 r k) (evalW w) = evalW (applyLetter r k w)`
    (a group hom is determined by generators; `map_list_prod`).
(4) By induction on `ks`: `(lprod r ks) (of i) = evalW (prodImg r ks i)` (note `(g * h) x = g (h x)`
    in `MulAut`, and `prodImg` is a `foldr`, rightmost letter first).
(5) `modelEq` true ⇒ equal images of all generators ⇒ equal automorphisms
    (`Submission.RouteB.mulAut_eq_iff`).  Numerically cross-checked against an independent python
    model on 30 random products.  ~250 lines; request (1),(2) as sub-lemmas if convenient.
-/

namespace Work.PTCert

open Submission.PTCert

/-- **Soundness of the word model.**  The ingredients are the word-model lemmas of
`WordModel.lean` ((1): `evalW_redW`, `evalW_invW`, `evalW_append`), the letter evaluation
`b1Img` of `LetterEval.lean` ((2)), the homomorphism step `applyLetterSound` of
`ApplyLetter.lean` ((3)) and the generator formula `lprodProdImg` ((4)).  Step (5) reduces
`modelEq` to equality of the images of all generators and applies `mulAut_eq_iff`. -/
theorem modelSound (r : ℕ) : ModelSound r := by
  intro ks ls hks hls heq
  rw [Submission.RouteB.mulAut_eq_iff]
  intro i
  rw [lprodProdImg r ks hks i, lprodProdImg r ls hls i]
  congr 1
  simp only [modelEq] at heq
  exact beq_iff_eq.mp ((List.all_eq_true.mp heq) i.val (List.mem_range.mpr i.isLt))

end Work.PTCert
