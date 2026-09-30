import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.Serre.simpHomChain
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

/-- The inclusion `A ⊆ X` of a subset, as a morphism of topological spaces. -/
abbrev inclHom : TopCat.of A ⟶ TopCat.of X := Work.SSSR.Cohomology.subtypeIncl (TopCat.of X) A

/-- Naturality of `TopCat.toSSetObjEquivT` for the inclusion of a subspace: the simplex of `X`
underlying a simplex `τ` of `A` is `τ` composed with the inclusion. -/
theorem toSSetObjEquiv_map_incl (m : ℕ) (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋m⦌) :
    (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m⦌)
        ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋m⦌) τ)
      = (ConcreteCategory.hom inclHom).comp
          ((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋m⦌) τ) := by
  ext z
  exact Work.SSSR.Cohomology.toSSetObjEquiv_map_apply inclHom (Opposite.op ⦋m⦌) τ z

/-- **The `A`-simplex carried by the `k`-th prism piece** of a simplex `c` of `A`: the composite of
`c` with the collapse of the standard simplex onto the `k`-th prism piece followed by the
projection onto the first factor. -/
def prismSimplexA (n : ℕ) (k : Fin (n + 1))
    (c : C(↥(stdSimplex ℝ (Fin (n + 1))), A)) :
    C(↥(stdSimplex ℝ (Fin (n + 2))), A) :=
  ⟨fun z => c ((pp n k z).1), c.continuous.comp (continuous_fst.comp (pp n k).continuous)⟩

@[simp]
theorem prismSimplexA_apply (n : ℕ) (k : Fin (n + 1))
    (c : C(↥(stdSimplex ℝ (Fin (n + 1))), A)) (z : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    prismSimplexA n k c z = c ((pp n k z).1) := rfl

/-- **The prism pieces of the image of a simplex of `A` are images of simplices of `A`.**  If `τ` is
an `n`-simplex of `A`, with underlying `n`-simplex `σ` of `X`, then for every `k` the `k`-th prism
piece `hSimplex H n k σ` of the compression homotopy is the image of an `(n+1)`-simplex of `A`
(namely the simplex `z ↦ τ ((pp n k z).1)`). -/
theorem exists_map_hSimplex (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N)
    (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌) (k : Fin (n + 1)) :
    ∃ τ' : (TopCat.toSSet.obj (TopCat.of A)) _⦋n + 1⦌,
      (TopCat.toSSet.map inclHom).app (Opposite.op ⦋n + 1⦌) τ'
        = hSimplex H n k ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ) := by
  refine ⟨((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋n + 1⦌)).symm
    (prismSimplexA n k ((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋n⦌) τ)), ?_⟩
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n + 1⦌)).injective
  rw [toSSetObjEquiv_map_incl, Equiv.apply_symm_apply, toSSetObjEquiv_hSimplex,
    toSSetObjEquiv_map_incl]
  ext z
  simp only [ContinuousMap.comp_apply, prismSimplex, prismSimplexA_apply]
  exact (H.hconst n hn ((ConcreteCategory.hom inclHom).comp _)
    (fun w => (((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋n⦌)) τ w).2)
    ((pp n k z).1) ((pp n k z).2)).symm

/-- The `n`-th component of the chain map induced by the inclusion `A ⊆ X`, written in the guise
of the singular simplicial set of `A`.  This is definitionally the `n`-th component of
`Work.Cohomology.inclChains R`, but keeping *one* representation throughout the proof below avoids
instance-transparency trouble between the two (definitionally equal) descriptions of the singular
chain complex (`Work.Cohomology.singularChains` versus `Work.Serre.singChainC R`). -/
abbrev inclChainMap (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (singChainC R A).X n ⟶ (singChainC R X).X n :=
  (SSet.chainComplexMap (TopCat.toSSet.map inclHom) (ModuleCat.of R R)).f n

/-- **A submodule of the chains of `A` containing the generators `1 • σ` is everything**, in the
guise of the singular simplicial set (the analogue of `Work.Cohomology.mem_of_gen`). -/
theorem mem_of_gen_sset (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (P : Submodule R ↑((singChainC R Y).X n))
    (h : ∀ σ : (singX Y) _⦋n⦌,
      (ModuleCat.Hom.hom ((singX Y).ιChainComplex (R := ModuleCat.of R R) σ)) (1 : R) ∈ P) :
    P = ⊤ :=
  Work.SSSR.Cohomology.mem_of_gen (TopCat.of Y) n P (fun σ => h σ)

/-- **The prism homotopy preserves the chains of `A`**: the composite

`C_n(A) ⟶ C_n(X) ⟶ C_{n+1}(X) ⟶ C_{n+1}(X,A)`

is zero, i.e. `prismHom R H n` sends the subcomplex `C_*(A)` of `C_*(X)` into `C_{*+1}(A)`.

The proof is elementwise on the generators of `C_n(A)`: the image of a generator `1 • τ` in
`C_n(X)` is the simplex `σ` of `X` underlying `τ`, which takes its values in `A`; by
`SimpHom.hconst` the homotopy `G n σ` is constant, so every prism piece `hSimplex H n k σ` is the
image of the `A`-simplex `z ↦ τ ((pp n k z).1)`, and `prismVal R H n σ` is therefore killed by the
cokernel projection `C_{n+1}(X) ⟶ C_{n+1}(X,A)`. -/
theorem prismHom_map_incl_zero {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (H : Work.SSSR.Serre.SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp
        ((Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f n) (Work.SSSR.Serre.prismHom R H n))
      (CategoryTheory.Limits.cokernel.π ((Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f (n + 1)))
    = 0 := by
  show CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp (inclChainMap R (X := X) (A := A) n) (prismHom R H n))
      (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1))) = 0
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  show (ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1)))).comp
      ((ModuleCat.Hom.hom (prismHom R H n)).comp
        (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) n))) = 0
  have key : ∀ τ : (singX A) _⦋n⦌,
      (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1))))
        (prismVal R H n ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)) = 0 := by
    intro τ
    rw [prismVal, map_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [map_zsmul]
    obtain ⟨τ', hτ'⟩ := exists_map_hSimplex H n hn τ k
    have hgen' : (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) (n + 1)))
        ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R))
        = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
            (hSimplex H n k ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)))) (1 : R) := by
      rw [show (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) (n + 1)))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R))
            = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n + 1⦌) τ'))) (1 : R)
          from Work.SSSR.Cohomology.chainComplexMap_ι_apply R (TopCat.toSSet.map inclHom) (n + 1) τ' 1]
      rw [hτ']
    rw [← hgen']
    have h2 : (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1))))
        ((ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) (n + 1)))
          ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R))) = 0 := by
      have hcond : (inclChainMap R (X := X) (A := A) (n + 1)) ≫
          (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1))) = 0 :=
        cokernel.condition _
      have h3 := congrArg (fun (m : (singChainC R A).X (n + 1) ⟶
            CategoryTheory.Limits.cokernel (inclChainMap R (X := X) (A := A) (n + 1))) =>
          (ModuleCat.Hom.hom m)
            ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ')) (1 : R))) hcond
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] using h3
    rw [h2]
    exact zsmul_zero _
  have hP : LinearMap.ker ((ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1)))).comp
      ((ModuleCat.Hom.hom (prismHom R H n)).comp
        (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) n)))) = ⊤ :=
    mem_of_gen_sset A n _ (fun τ => by
      rw [LinearMap.mem_ker]
      show (ModuleCat.Hom.hom
            (CategoryTheory.Limits.cokernel.π (inclChainMap R (X := X) (A := A) (n + 1))))
          ((ModuleCat.Hom.hom (prismHom R H n))
            ((ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) n))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ))
                (1 : R)))) = 0
      rw [show (ModuleCat.Hom.hom (inclChainMap R (X := X) (A := A) n))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of R R) τ)) (1 : R))
            = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ))) (1 : R)
          from Work.SSSR.Cohomology.chainComplexMap_ι_apply R (TopCat.toSSet.map inclHom) n τ 1]
      rw [show (ModuleCat.Hom.hom (prismHom R H n))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ))) (1 : R))
            = prismVal R H n ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)
          from prismHom_gen H n _]
      exact key τ)
  refine LinearMap.ext (fun x => ?_)
  exact LinearMap.mem_ker.mp (by rw [hP]; exact Submodule.mem_top)

end

end Work.SSSR.Serre
