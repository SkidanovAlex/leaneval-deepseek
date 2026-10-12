import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeParsevalDefs` — the lattice characters of the box lattice

The single definition shared by the proof of `Work.BoseFixR.LatticeW1sqParseval`
(the lattice Parseval/Plancherel identity on the box `boxL ℓ`) and by its pieces.

`labChar ℓ N k : EuclideanSpace ℝ (Fin 3) → ℂ` is the character
`x ↦ e^{i⟪kmomLab ℓ N k, x⟫}` of the box lattice `(2π/ℓ)ℤ³` restricted to the
truncated cube `Lab N` of mode labels.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

/-- The lattice character `x ↦ e^{i⟪k, x⟫}` at the box-lattice momentum
`k = kmomLab ℓ N k`. -/
def labChar (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℝ) : ℂ))

@[simp] lemma labChar_apply (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) :
    labChar ℓ N k x
      = Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℝ) : ℂ)) :=
  rfl

end Work.BoseFixR
