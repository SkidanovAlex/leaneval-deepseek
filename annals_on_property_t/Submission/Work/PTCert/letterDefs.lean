import Submission.Work.PTCert.Interfaces
import Submission.Work.RouteB.TransvectionEquiv
import Submission.Work.RouteB.FreeGroupAutDecEq
import Mathlib

/-!
# Letter action: shared auxiliary definitions

Re-encoding of the ordered pairs of distinct indices used by `pairOf`, and the
`kindAutNat` packaging of the four Nielsen transvections carrying a kind with bits
`(b0, b1)` (`rho = (0,0)`, `rhoNeg = (0,1)`, `lam = (1,0)`, `lamNeg = (1,1)`).
-/

namespace Submission.PTCert

open Submission.FreeGroupAut

/-- Re-encoding of an ordered pair of distinct indices into `[0, r * (r-1))`. -/
def pairIndex (r i j : ℕ) : ℕ := i * (r - 1) + (if j < i then j else j - 1)

/-- The transvection with kind bits `(b0, b1)`. -/
def kindAutNat {r : ℕ} (i j : Fin r) (hij : i ≠ j) (b0 b1 : ℕ) :
    MulAut (FreeGroup (Fin r)) :=
  if b0 = 1 then (if b1 = 1 then lamNeg i j hij else lam i j hij)
  else (if b1 = 1 then rhoNeg i j hij else rho i j hij)

@[simp] lemma kindAutNat_zero_zero {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    kindAutNat i j hij 0 0 = rho i j hij := rfl

@[simp] lemma kindAutNat_zero_one {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    kindAutNat i j hij 0 1 = rhoNeg i j hij := rfl

@[simp] lemma kindAutNat_one_zero {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    kindAutNat i j hij 1 0 = lam i j hij := rfl

@[simp] lemma kindAutNat_one_one {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    kindAutNat i j hij 1 1 = lamNeg i j hij := rfl

end Submission.PTCert
