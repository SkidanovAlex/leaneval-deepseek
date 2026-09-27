import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.PsiC.PB_comm_frame

/-!
# `Work.PsiC.PB_comm_cycProj`

`PB p` is the six-fold tensor power `p^{⊗6}` in the bracketing `((1,2),(3,4)),(5,6)` of the
index type `IB n = (I2 n × I2 n) × I2 n`.  Over a commutative ring `A`, the entries of `PB p`
are products of the six entries of `p.2`, so `PB p` commutes with the permutation matrix of any
permutation of the six tensor slots.

The transports `uB`, `vB` of the frame-A cyclic permutations `c1A`, `c2A` act on `IB n`
precisely as such slot permutations (a `3`-cycle on the first, resp. second, elements of the
three pairs).  Hence `PB p` commutes with `(uB p.1).permMatrix A` and `(vB p.1).permMatrix A`,
and therefore (by `cycProj_comm_of`) with the corresponding cyclic projectors.
-/

namespace Work.PsiC

open Matrix

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

section Frame

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The slot permutation `uB`: a `3`-cycle on the first elements of the three pairs. -/
theorem uB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.uB n (((a, b), (c, d)), (e, f)) = (((e, b), (a, d)), (c, f)) := rfl

/-- The slot permutation `vB`: a `3`-cycle on the second elements of the three pairs. -/
theorem vB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.vB n (((a, b), (c, d)), (e, f)) = (((a, f), (c, b)), (e, d)) := rfl

theorem PB_comm_uB (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.uB p.1).permMatrix A =
      (Work.KT.PsiC.uB p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.uB p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, uB_apply]
  ring

theorem PB_comm_vB (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) :
    Work.KT.PsiC.PB p * (Work.KT.PsiC.vB p.1).permMatrix A =
      (Work.KT.PsiC.vB p.1).permMatrix A * Work.KT.PsiC.PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  refine PB_comm_of_reindex p (Work.KT.PsiC.vB p.1) ?_
  intro a b
  rcases a with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨a5, a6⟩⟩
  rcases b with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩, ⟨b5, b6⟩⟩
  simp only [PB_apply, vB_apply]
  ring

end Frame

theorem PB_comm_cycProj (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (lam : ℂ) :
    (Work.KT.PsiC.PB p * Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) lam = Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) lam * Work.KT.PsiC.PB p) ∧
    (Work.KT.PsiC.PB p * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) lam = Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) lam * Work.KT.PsiC.PB p) := by
  refine ⟨?_, ?_⟩
  · exact Work.KT.PsiC.cycProj_comm_of (A := A) hA (Work.KT.PsiC.uB p.1) lam
      (Work.KT.PsiC.PB p) (PB_comm_uB hA p)
  · exact Work.KT.PsiC.cycProj_comm_of (A := A) hA (Work.KT.PsiC.vB p.1) lam
      (Work.KT.PsiC.PB p) (PB_comm_vB hA p)

end Work.PsiC
