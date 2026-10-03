/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The dimension theory attached to a Sylvester rank function

Following [JZLA20, §2.4] and [Li20, §2--§5], a Sylvester matrix rank function `rk` on a ring `R`
gives rise to a *dimension function* on `R`-modules:

* on a finitely presented `R`-module with presentation `M ≅ R^n / R^m A` it is `n - rk A`;
* on a finitely generated `R`-module it is the infimum of `fpDim` over its finitely presented
  quotients;
* on an arbitrary `R`-module it is the supremum of `fgDim` over its finitely generated
  submodules.

The point for `Epic/rk_injective_of_isEpic` is that this dimension is built purely out of the
values of `rk` on matrices.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u v

namespace Work.ORHughesFree.Epic

open Matrix

variable {R : Type u} [Ring R]

/-- The `R`-linear map `v ↦ v ᵥ* A` attached to a matrix `A : m × n`. -/
def rowMulLin {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : (Fin m → R) →ₗ[R] (Fin n → R) where
  toFun v := fun j => ∑ i, v i * A i j
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc])

/-- The cokernel `R^n / R^m A` of the right-multiplication map `v ↦ v ᵥ* A`, where
`A : m × n`. -/
abbrev cokerMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : Type u :=
  (Fin n → R) ⧸ LinearMap.range (rowMulLin A)

/-- The `R`-dimension of a finitely presented `R`-module: the common value `n - rk A` over all
presentations `M ≅ R^n / R^m A`, written as a supremum over all presentations. -/
noncomputable def fpDim (rk : SylvesterRank R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] : ℝ :=
  sSup { x : ℝ | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
      Nonempty (cokerMat A ≃ₗ[R] M) ∧ x = (n : ℝ) - rk.rk m n A }

/-- The `R`-dimension of a finitely generated `R`-module: the infimum of `fpDim` over the
finitely presented modules admitting `M` as a quotient. -/
noncomputable def fgDim (rk : SylvesterRank R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : ℝ :=
  sInf { x : ℝ | ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : Module.FinitePresentation R Q),
      ∃ (g : Q →ₗ[R] M), Function.Surjective g ∧ x = fpDim rk Q }

/-- Li's *relative* dimension `dim (N' | M)` for a finitely generated submodule `N'` of an
`R`-module `M` ([Li20, Theorem 4.4]): the infimum, over finitely generated `N''` with
`N' ≤ N'' ≤ M`, of `dim N'' - dim (N''/N')`. -/
noncomputable def relDimFg (rk : SylvesterRank R) {M : Type v} [AddCommGroup M] [Module R M]
    (N' : Submodule R M) [Module.Finite R ↥N'] : ℝ :=
  sInf { x : ℝ | ∃ (N'' : Submodule R M) (_ : Module.Finite R ↥N'') (_h : N' ≤ N''),
      x = fgDim rk ↥N'' - fgDim rk ((↥N'') ⧸ (N'.comap N''.subtype)) }

/-- Li's dimension `dim M` of an arbitrary `R`-module `M` ([Li20, Theorem 4.4]): the supremum of
the relative dimensions `dim (N' | M)` over the finitely generated submodules `N' ≤ M`.

Note that this is *not* the supremum of the absolute dimensions `dim N'`: the two differ in
general (Li–Liang, *Sofic mean length*, Example 6.3). -/
noncomputable def modDim (rk : SylvesterRank R) (M : Type v) [AddCommGroup M] [Module R M] : ℝ :=
  sSup { x : ℝ | ∃ (N' : Submodule R M) (_ : Module.Finite R ↥N'), x = relDimFg rk N' }

end Work.ORHughesFree.Epic
