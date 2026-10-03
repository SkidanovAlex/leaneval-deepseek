import Mathlib
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.Section6.isUnit_of_isUnit_map_of_vonNeumannRegular

set_option linter.style.haveILetI false

namespace Work.ORDivLoc.Closure

open Work.Section6 Work.ORHughesFree

/-- The image of a scalar matrix under an entrywise ring homomorphism is the scalar matrix of the
image. -/
theorem map_matrix_scalar {R U : Type} [Semiring R] [Semiring U] (ρ : R →+* U)
    (n : ℕ) (c : R) :
    (Matrix.scalar (Fin n) c).map ⇑ρ = Matrix.scalar (Fin n) (ρ c) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero ρ)]

theorem isHughesFreeEnv_of_ringHom {K : Type} [Field K] {G : Type} [Group G]
    {R : Type} [Ring R] [StarRing R] [Work.ORHughesFree.IsStarRegular R]
    {U : Type} [Ring U] [StarRing U] [Work.ORHughesFree.IsStarRegular U]
    (ρ : R →+* U) (hρ : Function.Injective ρ)
    (φR : MonoidAlgebra K G →+* R) (φU : MonoidAlgebra K G →+* U)
    (hcomp : φU = ρ.comp φR)
    (hUN : ∀ (H : Subgroup G) (N : Subgroup H),
      ∀ z : Work.Section6.UNty φR H N, ρ (z : R) ∈ (Work.Section6.UN φU H N : Set U))
    (h : Work.ORHughesFree.IsHughesFreeEnv φU) :
    Work.ORHughesFree.IsHughesFreeEnv φR := by
  intro H hfg hne N hN t hdec htinf n A
  -- `Mat_{n}(R)` is von Neumann regular, so it suffices to test invertibility after applying
  -- the (injective) entrywise ring homomorphism `Mat_n(ρ)`.
  haveI : Work.ORHughesFree.VonNeumannRegularRing (Matrix (Fin n) (Fin n) R) :=
    Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix n
  -- The map `U_N(φ_R) → U_N(φ_U)` induced by `ρ`, using the hypothesis `hUN`.
  let ψ : Work.Section6.UNty φR H N →+* Work.Section6.UNty φU H N :=
    { toFun := fun z => ⟨ρ (z : R), hUN H N z⟩
      map_one' := Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (map_add ρ (x : R) (y : R))
      map_mul' := fun x y => Subtype.ext (map_mul ρ (x : R) (y : R)) }
  -- Hughes-freeness of `φ_U` applied to the matrix `A` pushed forward along `ψ`.
  have hA := h H hfg hne N hN t hdec htinf n (A.map ψ)
  have hψval : ∀ z : Work.Section6.UNty φR H N,
      ((ψ z : Work.Section6.UNty φU H N) : U) = ρ (z : R) := fun _ => rfl
  -- `A.map ψ`, read in `U`, is `A` read in `U` through `ρ`.
  have hAeq : (A.map (Subtype.val : Work.Section6.UNty φR H N → R)).map ⇑ρ
      = (A.map ψ).map (Subtype.val : Work.Section6.UNty φU H N → U) := by
    ext i j
    simp only [Matrix.map_apply]
    exact hψval (A i j)
  -- The two scalars match because `φ_U = ρ ∘ φ_R`.
  have hρc : ρ ((φR.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K)))
      = (φU.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K)) := by
    rw [hcomp, RingHom.comp_assoc]
    rfl
  have hscalar :
      (Matrix.scalar (Fin n) ((φR.comp (inducedMapRing (K := K) H))
        (MonoidAlgebra.single t (1 : K)))).map ⇑ρ
      = Matrix.scalar (Fin n) ((φU.comp (inducedMapRing (K := K) H))
        (MonoidAlgebra.single t (1 : K))) := by
    rw [map_matrix_scalar, hρc]
  refine Work.Section6.isUnit_of_isUnit_map_of_vonNeumannRegular (RingHom.mapMatrix ρ) ?_ ?_
  · intro M N' h
    ext i j
    exact hρ (by
      have := congrArg (fun B : Matrix (Fin n) (Fin n) U => B i j) h
      simpa [RingHom.mapMatrix_apply] using this)
  · show IsUnit ((RingHom.mapMatrix ρ)
      (1 + A.map (Subtype.val : Work.Section6.UNty φR H N → R) *
        Matrix.scalar (Fin n) ((φR.comp (inducedMapRing (K := K) H))
          (MonoidAlgebra.single t (1 : K)))))
    rw [map_add, map_one, map_mul]
    simp only [RingHom.mapMatrix_apply]
    rw [hAeq, hscalar]
    exact hA

end Work.ORDivLoc.Closure
