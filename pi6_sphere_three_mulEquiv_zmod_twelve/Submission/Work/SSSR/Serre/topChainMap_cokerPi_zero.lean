import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.Serre.simpHomChain
import Submission.Work.SSSR.Serre.prismHom_map_incl_zero
import Submission.Work.SSSR.Cohomology.Sd_comm
import Submission.Work.SSSR.Cohomology.SmallChainsIsoAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial
namespace Work.SSSR.Serre

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
`C_n(X) ⟶ C_n(X) ⟶ C_n(X,A)` is zero: every singular simplex is sent by `topChainMap R H n` to a
chain supported on `A`. -/
theorem topChainMap_cokerPi_zero {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (H : Work.SSSR.Serre.SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    CategoryTheory.CategoryStruct.comp (Work.SSSR.Serre.topChainMap R H n)
      (CategoryTheory.Limits.cokernel.π ((Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f n))
    = 0 := by
  show CategoryTheory.CategoryStruct.comp (topChainMap R H n)
      (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n)) = 0
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  show (ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n))).comp
      ((ModuleCat.Hom.hom (topChainMap R H n))) = 0
  have key : ∀ σ : (singX X) _⦋n⦌,
      (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n)))
        (topVal R H n σ) = 0 := by
    intro σ
    obtain ⟨τ', hτ'⟩ := exists_map_gSimplex (X := X) (A := A) H n hn σ
    rw [topVal, ← hτ']
    have hgen : (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) n))
        ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R))
        = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
            ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ'))) (1 : R) :=
      Work.SSSR.Cohomology.chainComplexMap_ι_apply R (TopCat.toSSet.map inclHom) n τ' 1
    rw [← hgen]
    have hcond : (inclChainMap R (X := X) (A := A) n) ≫
        (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n)) = 0 :=
      cokernel.condition _
    have h3 := congrArg (fun (m : (singChainC R A).X n ⟶
          CategoryTheory.Limits.cokernel (inclChainMap R (X := X) (A := A) n)) =>
        (ModuleCat.Hom.hom m)
          ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R)))
      hcond
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] using h3
  have hP : LinearMap.ker ((ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n))).comp
      (ModuleCat.Hom.hom (topChainMap R H n))) = ⊤ :=
    mem_of_gen_sset X n _ (fun σ => by
      rw [LinearMap.mem_ker]
      show (ModuleCat.Hom.hom
            (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) n)))
          ((ModuleCat.Hom.hom (topChainMap R H n))
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R) σ))
              (1 : R))) = 0
      rw [show (ModuleCat.Hom.hom (topChainMap R H n))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R) σ)) (1 : R))
            = topVal R H n σ from topChainMap_gen H n σ]
      exact key σ)
  refine LinearMap.ext (fun x => ?_)
  exact LinearMap.mem_ker.mp (by rw [hP]; exact Submodule.mem_top)

end

end Work.SSSR.Serre
