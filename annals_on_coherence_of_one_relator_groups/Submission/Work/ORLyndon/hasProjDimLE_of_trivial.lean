import Mathlib
import Submission.Work.ORLyndon.ProjDim
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.DiagTensor
import Submission.Work.ORLyndon.HasProjDimLE_of_linearEquiv
import Submission.Work.ORLyndon.diagTensor_projective
import Submission.Work.ORLyndon.ker_diagTensorMap_equiv
import Submission.Work.ORLyndon.trivialTensorEquiv

/-!
# Every module over `K[G]` has projective dimension at most that of the trivial module

If the trivial left `K[G]`-module `K[G] / I` admits a projective resolution of length at most `n`,
then so does every left `K[G]`-module `M` (JL, Prop. 2.2): tensor a projective resolution of the
trivial module with `M` over `K`, using the *diagonal* action
`g • (x ⊗ₜ m) = (g • x) ⊗ₜ (g • m)` of `DiagTensor.lean`.  Tensoring with `M` over the field `K`
preserves projectivity (`diagTensor_projective`) and exactness (`ker_diagTensorMap_equiv`), and the
trivial module tensored with `M` is `M` again (`trivialTensorEquiv`).
-/

set_option autoImplicit false

open TensorProduct MonoidAlgebra

namespace Work.ORLyndon

universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G]

/-- **The transfer step** (JL, Proposition 2.2, for group algebras over a field): if the left
`K[G]`-module `N` has a projective resolution of length at most `n`, then so does `N ⊗[K] M` with
respect to the *diagonal* action `g • (x ⊗ₜ m) = (g • x) ⊗ₜ (g • m)`.

The proof is the induction on `n` along the recursive definition of `HasProjDimLE`: tensoring a
projective cover `P ↠ N` with `M` over the field `K` gives a projective cover
`P ⊗[K] M ↠ N ⊗[K] M` (`diagTensor_projective`, `diagTensorMap_surjective`) whose kernel is
`(ker f) ⊗[K] M` (`ker_diagTensorMap_equiv`), to which the induction hypothesis applies. -/
theorem hasProjDimLE_tensor {M : Type (max u v)} [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] (n : ℕ) :
    ∀ (N : Type (max u v)) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
      [IsScalarTower K (MonoidAlgebra K G) N],
      HasProjDimLE (MonoidAlgebra K G) N n →
        HasProjDimLE (MonoidAlgebra K G) (TensorProduct K N M) n := by
  induction n with
  | zero =>
    intro N i1 i2 i3 i4 h
    haveI : Module.Projective (MonoidAlgebra K G) N := h
    exact diagTensor_projective N
  | succ k ih =>
    intro N i1 i2 i3 i4 h
    obtain ⟨P, j1, j2, j3, f, hf, hker⟩ := h
    letI : AddCommGroup P := j1
    letI : Module (MonoidAlgebra K G) P := j2
    letI : Module.Projective (MonoidAlgebra K G) P := j3
    letI : Module K P := Module.compHom P (algebraMap K (MonoidAlgebra K G))
    haveI : IsScalarTower K (MonoidAlgebra K G) P := by
      refine ⟨fun c r x => ?_⟩
      rw [Algebra.smul_def]
      exact mul_smul _ _ _
    refine ⟨TensorProduct K P M, inferInstance, inferInstance,
      diagTensor_projective P, diagTensorMap (M := M) f, diagTensorMap_surjective hf, ?_⟩
    obtain ⟨e⟩ := ker_diagTensorMap_equiv (M := M) f
    exact HasProjDimLE_of_linearEquiv e.symm (ih (LinearMap.ker f) hker)

/-- **Jaikin-Zapirain–Linton, Proposition 2.2**: if the trivial left `K[G]`-module
`K[G] / I_{K[G]}` admits a projective resolution of length at most `n`, then *every* left
`K[G]`-module admits one.

Indeed, `(K[G] / I_{K[G]}) ⊗[K] M ≅ M` as `K[G]`-modules for the diagonal action
(`trivialTensorEquiv`), and tensoring with `M` over the field `K` preserves projective resolutions
of bounded length (`hasProjDimLE_tensor`). -/
theorem hasProjDimLE_of_trivial {K : Type v} [Field K] {G : Type u} [Group G]
    (n : ℕ) {M : Type (max u v)} [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    (h : Work.ORLyndon.HasProjDimLE (MonoidAlgebra K G)
      (MonoidAlgebra K G ⧸ Work.ORLyndon.augIdeal K G) n) :
    Work.ORLyndon.HasProjDimLE (MonoidAlgebra K G) M n := by
  letI : Module K M := Module.compHom M (algebraMap K (MonoidAlgebra K G))
  haveI : IsScalarTower K (MonoidAlgebra K G) M := by
    refine ⟨fun c r x => ?_⟩
    rw [Algebra.smul_def]
    exact mul_smul _ _ _
  have h' := hasProjDimLE_tensor (K := K) (G := G) (M := M) n
    (MonoidAlgebra K G ⧸ augIdeal K G) h
  obtain ⟨e⟩ := trivialTensorEquiv (K := K) (G := G) (M := M)
  exact HasProjDimLE_of_linearEquiv e h'

end Work.ORLyndon
