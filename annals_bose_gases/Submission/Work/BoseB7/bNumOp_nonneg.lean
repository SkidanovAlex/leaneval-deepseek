import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `bNumOp_nonneg` — positivity of the squeezed number operator `b_k†b_k`

FS `thm:BogHamDiag` diagonalises the quadratic part of the box Hamiltonian into
`Σ_k D_k b_k†b_k`.  Every estimate that uses this diagonal form needs only one
thing from `b_k†b_k`: it is a *positive* operator,

  `⟨f, b_k†b_k f⟩ = ‖b_k f‖² ≥ 0`,

i.e. `0 ≤ F.bp (F.bNumOp α i f) f`.

Here `b_k = a_k + α_k a_{-k}†` and `b_k† = a_k† + α_k a_{-k}` (`FockDefs.bOp`,
`FockDefs.bOpDag`).  The point of the auxiliary lemma `bOpDag_bp` below is that
`b_k†` is the adjoint of `b_k` with respect to the Fock form for *every* `α`:
no evenness of `α` is needed (only the adjointness `a† ⊣ a` of the raw
operators, together with symmetry of `bp`).  Hence

  `⟨b_k†(b_k f), f⟩ = ⟨b_k f, b_k f⟩ ≥ 0`.
-/

noncomputable section

namespace Work.BoseB7

/-- `b_k† = a_k† + α_k a_{-k}` is the adjoint of `b_k = a_k + α_k a_{-k}†` with respect to
the Fock form `bp`, for *every* `α`: no evenness of `α` is needed. -/
theorem bOpDag_bp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (α : Mode → ℝ) (i : Mode) (g f : F.H) :
    F.bp (F.bOpDag α i g) f = F.bp g (F.bOp α i f) := by
  simp only [FockData.bOpDag, FockData.bOp, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul]
  have h1 : F.bp (F.aDag i g) f = F.bp g (F.a i f) := F.aDag_adjoint i g f
  have h2 : F.bp (F.a (-i) g) f = F.bp g (F.aDag (-i) f) := by
    rw [F.bp_symm (F.a (-i) g) f, ← F.aDag_adjoint (-i) f g, F.bp_symm (F.aDag (-i) f) g]
  rw [h1, h2]

/-- The squeezed number operator `b_k†b_k` is positive in the Fock quadratic form:
`⟨b_k†b_k f, f⟩ = ⟨b_k f, b_k f⟩ = ‖b_k f‖² ≥ 0`. -/
theorem bNumOp_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (α : Mode → ℝ) (i : Mode) (f : F.H) :
    0 ≤ F.bp (F.bNumOp α i f) f := by
  show 0 ≤ F.bp (F.bOpDag α i (F.bOp α i f)) f
  rw [bOpDag_bp F α i (F.bOp α i f) f]
  exact F.bp_nonneg (F.bOp α i f)

end Work.BoseB7
