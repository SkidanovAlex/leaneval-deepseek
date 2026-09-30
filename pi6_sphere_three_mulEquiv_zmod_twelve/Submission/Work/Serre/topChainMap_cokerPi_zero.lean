import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.simpHomChain
import Submission.Work.Serre.prismHom_map_incl_zero
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.SmallChainsIsoAux

/-!
# The top of the compression homotopy lands in the chains of the subspace

For `H : SimpHom X A N` the "top" map `topChainMap H n : C_n(X) ⟶ C_n(X)` sends every simplex
`σ` to the simplex `z ↦ G n σ (z,1)`, whose image lies in `A` by `SimpHom.htop`.  Hence
`topChainMap H n` lands in the subcomplex of `A`-chains, so its composite with the cokernel
projection `C_n(X) ⟶ C_n(X,A)` vanishes.  Together with the chain identity
`∂T + T∂ = 𝟙 - τ` this identifies the relative complex as the cone of a chain homotopy.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- **The top of the homotopy is a simplex of `A`.**  For any `n`-simplex `σ` of `X` and `n ≤ N`,
the simplex `z ↦ G n σ (z,1)` takes its values in `A`, so it is the image of a simplex of `A`. -/
theorem exists_map_gSimplex (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N)
    (τ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) :
    ∃ τ' : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌,
      (TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ' = gSimplex H n τ := by
  refine ⟨((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋n⦌)).symm
    ⟨fun z => ⟨H.G n ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) τ) (z, 1),
        H.htop n hn _ z⟩, ?_⟩, ?_⟩
  · exact Continuous.subtype_mk
      ((H.G n ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) τ)).continuous.comp
        (continuous_id.prodMk continuous_const))
      (fun z => H.htop n hn _ z)
  · apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌)).injective
    rw [toSSetObjEquiv_map_incl, Equiv.apply_symm_apply, toSSetObjEquiv_gSimplex]
    rfl

/-- **The top map vanishes on the relative chains.**  The composite
`C_n(X) ⟶ C_n(X) ⟶ C_n(X,A)` is zero: every singular simplex is sent by `topChainMap H n` to a
chain supported on `A`. -/
theorem topChainMap_cokerPi_zero {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (H : Work.Serre.SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.topChainMap H n)
      (CategoryTheory.Limits.cokernel.π ((Work.Cohomology.inclChains (TopCat.of X) A).f n))
    = 0 := by
  show CategoryTheory.CategoryStruct.comp (topChainMap H n)
      (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n)) = 0
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  show (ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n))).comp
      ((ModuleCat.Hom.hom (topChainMap H n))) = 0
  have key : ∀ σ : (singX X) _⦋n⦌,
      (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n)))
        (topVal H n σ) = 0 := by
    intro σ
    obtain ⟨τ', hτ'⟩ := exists_map_gSimplex (X := X) (A := A) H n hn σ
    rw [topVal, ← hτ']
    have hgen : (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) n))
        ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ))
        = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ'))) (1 : ℤ) :=
      Work.Cohomology.chainComplexMap_ι_apply (TopCat.toSSet.map inclHom) n τ' 1
    rw [← hgen]
    have hcond : (inclChainMap (X := X) (A := A) n) ≫
        (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n)) = 0 :=
      cokernel.condition _
    have h3 := congrArg (fun (m : (singChainC A).X n ⟶
          CategoryTheory.Limits.cokernel (inclChainMap (X := X) (A := A) n)) =>
        (ModuleCat.Hom.hom m)
          ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ)))
      hcond
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] using h3
  have hP : LinearMap.ker ((ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n))).comp
      (ModuleCat.Hom.hom (topChainMap H n))) = ⊤ :=
    mem_of_gen_sset X n _ (fun σ => by
      rw [LinearMap.mem_ker]
      show (ModuleCat.Hom.hom
            (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) n)))
          ((ModuleCat.Hom.hom (topChainMap H n))
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ))
              (1 : ℤ))) = 0
      rw [show (ModuleCat.Hom.hom (topChainMap H n))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)) (1 : ℤ))
            = topVal H n σ from topChainMap_gen H n σ]
      exact key σ)
  refine LinearMap.ext (fun x => ?_)
  exact LinearMap.mem_ker.mp (by rw [hP]; exact Submodule.mem_top)

end

end Work.Serre
