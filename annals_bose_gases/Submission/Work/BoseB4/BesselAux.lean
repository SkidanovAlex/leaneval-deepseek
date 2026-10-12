import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.AnnOf_creOf_ccr
import Submission.Work.BoseB4.Bomb_self_nonneg
import Submission.Work.BoseB4.Bomb_symm
import Submission.Work.BoseB4.CreOf_annOf_adjoint
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BesselAux` — the matrix-of-operators bookkeeping for the Bessel bound

On the real bosonic Fock space `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` over `m` modes
(`Work.BoseB4.RealFock`), with the coordinate annihilation/creation
`ann m l`, `cre m l` and the superposed mode operators
`annOf m f = Σ_l f_l a_l`, `creOf m f = Σ_l f_l a_l†`
(`Work.BoseB4.ModeFock`), every operator that will be compared in the Bessel
inequality is of the form

    `Σ_{l,l'} M l l' • a_l† a_{l'}`

for a matrix `M : Fin m → Fin m → ℝ`.  This module collects the (purely
multilinear) calculus of that representation:

* `besselOpMat m M` — the operator above;
* `besselOpMat_add`, `besselOpMat_sub` — additivity in the matrix;
* `creOf_comp_annOf_eq_besselOpMat` — `a†(f) a(g) = Σ_{l,l'} f_l g_{l'} • a_l†a_{l'}`,
  i.e. the rank-one matrix `f gᵀ` (this is `comp_sum_smul_expand` of
  `Work.BoseB4.AnnOf_creOf_ccr` read through `besselOpMat`).

The point of the representation is that `totNumOp m` is `besselOpMat` of the
identity matrix, the sum `Σ_{s∈S} a†(g_s)a(g_s)` is `besselOpMat` of the matrix
`Σ_{s∈S} g_s g_sᵀ`, and for an orthonormal family the *difference* of the two
matrices is a sum of rank-one matrices — which is exactly the statement that the
difference operator is a sum of squares, hence form-positive.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- The endomorphism `Σ_{l,l'} M l l' • a_l† a_{l'}` of `RealFock m` attached to a
`Fin m × Fin m` matrix `M`.  In the second-quantised notation it is
`Σ_{l,l'} M_{ll'} a_l† a_{l'}`. -/
noncomputable def besselOpMat (m : ℕ) (M : Fin m → Fin m → ℝ) :
    RealFock m →ₗ[ℝ] RealFock m :=
  ∑ l : Fin m, ∑ l' : Fin m, M l l' • (cre m l).comp (ann m l')

/-- Evaluation of `besselOpMat` at a state: the composition is absorbed. -/
lemma besselOpMat_comp_apply (m : ℕ) (M : Fin m → Fin m → ℝ) (Φ : RealFock m) :
    besselOpMat m M Φ
      = ∑ l : Fin m, ∑ l' : Fin m, M l l' • ((cre m l) ((ann m l') Φ)) := by
  simp only [besselOpMat, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/-- `besselOpMat` is additive in the matrix. -/
lemma besselOpMat_add (m : ℕ) (M M' : Fin m → Fin m → ℝ) :
    besselOpMat m (M + M') = besselOpMat m M + besselOpMat m M' := by
  apply LinearMap.ext
  intro Φ
  simp only [besselOpMat_comp_apply, LinearMap.add_apply, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]

/-- `besselOpMat` is additive in the matrix, subtraction form. -/
lemma besselOpMat_sub (m : ℕ) (M M' : Fin m → Fin m → ℝ) :
    besselOpMat m (M - M') = besselOpMat m M - besselOpMat m M' := by
  apply LinearMap.ext
  intro Φ
  simp only [besselOpMat_comp_apply, LinearMap.sub_apply, Pi.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

/-- `besselOpMat` depends only on the matrix: equal matrices give equal operators. -/
lemma besselOpMat_congr {m : ℕ} {M M' : Fin m → Fin m → ℝ} (h : M = M') :
    besselOpMat m M = besselOpMat m M' := by rw [h]

/-- **The rank-one case**: the product `a†(f) a(g)` of a superposed creation and
annihilation is `besselOpMat` of the rank-one matrix `l l' ↦ f_l g_{l'}`.
This is the bilinear expansion `comp_sum_smul_expand` (`Work.BoseB4.AnnOf_creOf_ccr`). -/
lemma creOf_comp_annOf_eq_besselOpMat {m : ℕ} (f g : Fin m → ℝ) :
    (creOf m f).comp (annOf m g) = besselOpMat m (fun l l' => f l * g l') := by
  simpa only [besselOpMat, creOf, annOf] using comp_sum_smul_expand (cre m) (ann m) f g

end Work.BoseB4
