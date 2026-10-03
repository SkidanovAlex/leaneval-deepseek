import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory

universe u

namespace Work.Section3.RkFinModel

open Work.ORHughesFree.Epic (rowMulLin cokerMat)

/-- **Change of coefficients for the cokernel of a matrix, as an additive map.**

Given a ring homomorphism `f : R →+* S` and a matrix `A` over `R`, the componentwise reduction
`v ↦ (fun j => f (v j))` sends the row space of `A` into the row space of `A.map f`, hence descends
to an additive map `cokerMat A →+ cokerMat (A.map f)` which is `f`-semilinear.  Composing with an
`R`-linear presentation `e : cokerMat A ≃ₗ[R] L` of `L` gives an `f`-semilinear additive map
`ψ : L →+ cokerMat (A.map f)` with the stated compatibility on representatives. -/
theorem exists_addHom_cokerMat_map {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Work.ORHughesFree.Epic.cokerMat A ≃ₗ[R] L) :
    ∃ ψ : L →+ Work.ORHughesFree.Epic.cokerMat (A.map f),
      (∀ (a : R) (l : L), ψ (a • l) = f a • ψ l) ∧
      (∀ v : Fin n → R,
        ψ (e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)) v))
          = Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin (A.map f)))
              (fun j => f (v j))) := by
  classical
  -- the `f`-semilinear componentwise reduction `R^n → S^n`
  let F : (Fin n → R) →ₛₗ[f] (Fin n → S) :=
    { toFun := fun v => fun j => f (v j)
      map_add' := by intro v w; ext j; simp
      map_smul' := by intro a v; ext j; simp }
  -- it intertwines the two row-multiplication maps
  have hkey : ∀ v : Fin m → R, rowMulLin (A.map f) (fun i => f (v i))
      = fun j => f (rowMulLin A v j) := by
    intro v
    ext j
    show (∑ i, f (v i) * f (A i j)) = f (∑ i, v i * A i j)
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => (map_mul f (v i) (A i j)).symm)
  -- whence the row space of `A` is carried into the row space of `A.map f`
  have hle : LinearMap.range (rowMulLin A)
      ≤ Submodule.comap F (LinearMap.range (rowMulLin (A.map f))) := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨fun i => f (u i), hkey u⟩
  -- the induced `f`-semilinear map on the cokernels
  let g := Submodule.mapQ (LinearMap.range (rowMulLin A))
      (LinearMap.range (rowMulLin (A.map f))) F hle
  refine ⟨{ toFun := fun l => g (e.symm l), map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · show g (e.symm 0) = 0
    rw [map_zero, map_zero]
  · intro x y
    show g (e.symm (x + y)) = g (e.symm x) + g (e.symm y)
    rw [map_add, map_add]
  · intro a l
    show g (e.symm (a • l)) = f a • g (e.symm l)
    rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ]
  · intro v
    show g (e.symm (e (Submodule.mkQ (LinearMap.range (rowMulLin A)) v))) =
      Submodule.mkQ (LinearMap.range (rowMulLin (A.map f))) (fun j => f (v j))
    rw [LinearEquiv.symm_apply_apply]
    rw [Submodule.mkQ_apply]
    show g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => f (v j))
    rw [show g = Submodule.mapQ (LinearMap.range (rowMulLin A))
        (LinearMap.range (rowMulLin (A.map f))) F hle from rfl]
    rw [Submodule.mapQ_apply]
    rfl

end Work.Section3.RkFinModel
