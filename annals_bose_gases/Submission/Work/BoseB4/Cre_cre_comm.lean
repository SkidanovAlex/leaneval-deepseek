import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Cre_cre_comm` — creation operators of distinct modes commute

`cre m l` is multiplication by the `l`-th indeterminate in the monomial-coefficient
model of the Fock space (`Submission/Work/BoseB4/RealFock.lean`), so
`cre m l (Finsupp.single α c) = Finsupp.single (α + e m l) c`: the operator shifts the
multi-index by `e m l`.  Two such shifts commute, whence `cre m l ∘ cre m l' = cre m l' ∘ cre m l`.
-/

namespace Work.BoseB4

/-- `cre m l` shifts the multi-index: `cre m l (single α c) = single (α + e m l) c`. -/
private lemma cre_single_shift (m : ℕ) (l : Fin m) (α : Fin m →₀ ℕ) (c : ℝ) :
    cre m l (Finsupp.single α c) = Finsupp.single (α + e m l) c := by
  rw [cre, Finsupp.lsum_single]
  rfl

theorem Cre_cre_comm {m : ℕ} (l l' : Fin m) :
    (Work.BoseB4.cre m l).comp (Work.BoseB4.cre m l')
      = (Work.BoseB4.cre m l').comp (Work.BoseB4.cre m l) := by
  ext A B
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, cre_single_shift]
  have h : A + e m l' + e m l = A + e m l + e m l' := by
    ext i
    simp [Finsupp.add_apply, e]
    omega
  rw [h]

end Work.BoseB4
