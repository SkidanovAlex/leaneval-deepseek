/-
Copyright: none.  Part of the Newlander-Nirenberg formalisation project.

# The restricted-measure vocabulary `dbarStar1C`, `dbarStar2C`, `quadWeightSum`, `dCoord1`

These definitions were originally declared in `Submission/Work/NN/Final/uniformDbarL2_holds.lean`
(the file carrying the crux `Work.NN.Final.uniformDbarL2_holds`).  They are moved here, unchanged in
name and namespace, so that the modules *using* them do not have to import the crux file itself.

**Why this matters (import-cycle note).**  A module `M` that mentions `dbarStar1C` must import a
module declaring it.  While the declaration lived in `uniformDbarL2_holds.lean`, every such `M`
imported the crux file, hence could not be used to *prove* the crux (Lean forbids import cycles):
the crux file would have to import `M`.  With the vocabulary here, the users only need
`Submission.Work.NN.Final.dbarStarDefs`, and the crux file may freely import them.

`uniformDbarL2_holds.lean` re-exports this module, so every existing import of that file still sees
the declarations unchanged.
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.l2SolverRegion
import Submission.Work.NN.Final.aPrioriFlex
import Submission.Work.NN.Final.l2ExistenceDefs
import Submission.Work.NN.Final.uniformDbarL2_flatCase

namespace Work.NN.Final

open Set MeasureTheory

noncomputable section

/-- `∂̄`-closedness, at the level of coefficient families (`Clos1`): every pair of coefficients
has equal cross-`∂̄`-derivatives.  For `C¹` families this is the pointwise equation
`∂̄_l g_j = ∂̄_j g_l`. -/
def IsClosed1C {n : ℕ} (g : Fin n → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ j l z, Work.CR.Flat.dbarCoord l (g j) z = Work.CR.Flat.dbarCoord j (g l) z

/-- The `(1,0)`-derivative, obtained from `dbarCoord` by conjugation:
`∂_j u = conj (∂̄_j (conj ∘ u))`. -/
noncomputable def dCoord1 {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  starRingEnd ℂ (Work.CR.Flat.dbarCoord j (fun w => starRingEnd ℂ (u w)) z)

/-- The `(0,2)`-level weighted adjoint coefficient `(∂̄*_φ ζ)_j = -Σ_k (∂_k ζ_{jk} - ζ_{jk} ∂_k φ)`,
so that `Σ_j ⟪g_j, (∂̄*_φ ζ)_j⟫` is the pairing `⟪g, ∂̄*_φ ζ⟫`; its vanishing for all nice `ζ` is
the *weak* `∂̄`-closedness of the `(0,1)`-form `g` on the polydisc. -/
noncomputable def dbarStar2C {n : ℕ} (φ : (Fin n → ℂ) → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  -∑ k, (dCoord1 k (ζ j k) z - ζ j k z * ((dCoord1 k (fun w => (φ w : ℂ)) z)))

/-- The weighted adjoint coefficient of the weak equation: for a `(0,1)`-form `v`,
`∂̄*_φ v = -Σ_j (∂_j v_j - v_j ∂_j φ)`, so that `∫ u · conj(∂̄*_φ v) e^{-φ}` is the pairing of `u`
against `∂̄*_φ v` (the form of the weak equation `∂̄u = g` that makes sense for `u ∈ L²` alone,
cf. `Work.Hormander.Weights.IsWeakDbarSolution`). -/
noncomputable def dbarStar1C {n : ℕ} (φ : (Fin n → ℂ) → ℝ) (v : Fin n → (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ℂ :=
  -∑ j, (dCoord1 j (v j) z - v j z * (dCoord1 j (fun w => (φ w : ℂ)) z))

/-- The sum-of-squares (`ℓ²`) weight on `Fin n → ℂ`; note `‖z‖` on `Fin n → ℂ` is the *sup* norm,
so the quadratic weight of the Fock space (`Work.Hormander.Weights.quadWeight`, whose complex
Hessian is `K·I`) must be written out as a sum of squares. -/
noncomputable def quadWeightSum (n : ℕ) (K : ℝ) (z : Fin n → ℂ) : ℝ :=
  K * ∑ j, ‖z j‖ ^ 2

end

end Work.NN.Final
