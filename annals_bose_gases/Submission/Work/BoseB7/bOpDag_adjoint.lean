import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Adjointness of the squeezed operators `b_k` and `b_k†`

`FockData.bOpDag α k = a_k† + α_k a_{-k}` is the adjoint of
`FockData.bOp α k = a_k + α_k a_{-k}†` with respect to the Fock form `bp`.
Indeed `a_k†` is the adjoint of `a_k` (`FockData.aDag_adjoint`) and `a_{-k}†`
that of `a_{-k}`, applied with the mode `-k`; symmetry of `bp` gives the symmetric
form of the second pair.  No evenness of `α` is needed.
-/

namespace Work.BoseB7

/-- `a_{-k}†` is the adjoint of `a_{-k}`, in the direction needed for the second
term of the decomposition (the symmetry of `bp` converts the `aDag_adjoint`
instance into the mirrored pairing). -/
theorem aDag_neg_adjoint {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (i : Mode) (f g : F.H) :
    F.bp (F.a (-i) f) g = F.bp f (F.aDag (-i) g) := by
  rw [F.bp_symm (F.a (-i) f) g, ← F.aDag_adjoint (-i) g f,
    F.bp_symm (F.aDag (-i) g) f]

theorem bOpDag_adjoint {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (α : Mode → ℝ) (i : Mode) (f g : F.H) :
    F.bp (F.bOpDag α i f) g = F.bp f (F.bOp α i g) := by
  simp only [FockData.bOpDag, FockData.bOp, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul]
  rw [F.aDag_adjoint i f g, aDag_neg_adjoint F i f g]

end Work.BoseB7
