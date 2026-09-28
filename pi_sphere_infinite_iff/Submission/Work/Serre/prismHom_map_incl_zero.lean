import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.simpHomChain
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.SmallChainsIsoAux

/-!
# The prism homotopy preserves the chains of a subspace

Let `(X,A)` be a pair and `H : SimpHom X A N` a family of compression homotopies of singular
simplices in dimensions `≤ N`, whose restriction to a simplex with image in `A` is the *constant*
homotopy (`SimpHom.hconst`).  Then the associated chain homotopy
`prismHom H n : C_n(X) ⟶ C_{n+1}(X)` (`Submission/Work/Serre/simpHomChain.lean`) sends the
subcomplex `C_n(A) ⊆ C_n(X)` into `C_{n+1}(A) ⊆ C_{n+1}(X)`, i.e. it descends to the relative
complex `C_*(X,A) = C_*(X)/C_*(A)`:

`C_n(A) ⟶ C_n(X) ⟶ C_{n+1}(X) ⟶ C_{n+1}(X,A)`  is zero.

This is one of the two properties which make `prismHom H` a chain contraction of the *relative*
complex (the other being the chain identity `∂T + T∂ = 𝟙 - τ` of
`prismHom_chain_identity.lean`).

The proof is elementwise on the generators `gen A n τ` of the chains of `A`: the image of such a
generator in `C_n(X)` is the simplex `σ` of `X` underlying `τ`, which takes its values in `A`; by
`SimpHom.hconst` the homotopy `G n σ` is constant, so every prism piece `hSimplex H n k σ` is the
image of the `A`-simplex `z ↦ τ ((pp n k z).1)`, and `prismVal H n σ` is therefore a cycle for the
cokernel `C_{n+1}(X) ⟶ C_{n+1}(X,A)`.

## Main results

* `Work.Serre.prismSimplexA` — the `A`-simplex underlying the `k`-th prism piece;
* `Work.Serre.exists_map_hSimplex` — the prism piece of the image of a simplex of `A` is the image
  of a simplex of `A`;
* `Work.Serre.prismHom_map_incl_zero` — the target statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The inclusion `A ⊆ X` of a subset, as a morphism of topological spaces. -/
abbrev inclHom : TopCat.of A ⟶ TopCat.of X := Work.Cohomology.subtypeIncl (TopCat.of X) A

/-- Naturality of `TopCat.toSSetObjEquivT` for the inclusion of a subspace: the simplex of `X`
underlying a simplex `τ` of `A` is `τ` composed with the inclusion. -/
theorem toSSetObjEquiv_map_incl (m : ℕ) (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋m⦌) :
    (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m⦌)
        ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋m⦌) τ)
      = (ConcreteCategory.hom inclHom).comp
          ((TopCat.of A).toSSetObjEquivT (Opposite.op ⦋m⦌) τ) := by
  ext z
  exact Work.Cohomology.toSSetObjEquiv_map_apply inclHom (Opposite.op ⦋m⦌) τ z

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
`Work.Cohomology.inclChains`, but keeping *one* representation throughout the proof below avoids
instance-transparency trouble between the two (definitionally equal) descriptions of the singular
chain complex (`Work.Cohomology.singularChains` versus `Work.Serre.singChainC`). -/
abbrev inclChainMap (n : ℕ) : (singChainC A).X n ⟶ (singChainC X).X n :=
  (SSet.chainComplexMap (TopCat.toSSet.map inclHom) (ModuleCat.of ℤ ℤ)).f n

/-- **A submodule of the chains of `A` containing the generators `1 • σ` is everything**, in the
guise of the singular simplicial set (the analogue of `Work.Cohomology.mem_of_gen`). -/
theorem mem_of_gen_sset (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (P : Submodule ℤ ↑((singChainC Y).X n))
    (h : ∀ σ : (singX Y) _⦋n⦌,
      (ModuleCat.Hom.hom ((singX Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)) (1 : ℤ) ∈ P) :
    P = ⊤ :=
  Work.Cohomology.mem_of_gen (TopCat.of Y) n P (fun σ => h σ)

/-- **The prism homotopy preserves the chains of `A`**: the composite

`C_n(A) ⟶ C_n(X) ⟶ C_{n+1}(X) ⟶ C_{n+1}(X,A)`

is zero, i.e. `prismHom H n` sends the subcomplex `C_*(A)` of `C_*(X)` into `C_{*+1}(A)`.

The proof is elementwise on the generators of `C_n(A)`: the image of a generator `1 • τ` in
`C_n(X)` is the simplex `σ` of `X` underlying `τ`, which takes its values in `A`; by
`SimpHom.hconst` the homotopy `G n σ` is constant, so every prism piece `hSimplex H n k σ` is the
image of the `A`-simplex `z ↦ τ ((pp n k z).1)`, and `prismVal H n σ` is therefore killed by the
cokernel projection `C_{n+1}(X) ⟶ C_{n+1}(X,A)`. -/
theorem prismHom_map_incl_zero {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (H : Work.Serre.SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp
        ((Work.Cohomology.inclChains (TopCat.of X) A).f n) (Work.Serre.prismHom H n))
      (CategoryTheory.Limits.cokernel.π ((Work.Cohomology.inclChains (TopCat.of X) A).f (n + 1)))
    = 0 := by
  show CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp (inclChainMap (X := X) (A := A) n) (prismHom H n))
      (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1))) = 0
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  show (ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1)))).comp
      ((ModuleCat.Hom.hom (prismHom H n)).comp
        (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) n))) = 0
  have key : ∀ τ : (singX A) _⦋n⦌,
      (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1))))
        (prismVal H n ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)) = 0 := by
    intro τ
    rw [prismVal, map_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [map_zsmul]
    obtain ⟨τ', hτ'⟩ := exists_map_hSimplex H n hn τ k
    have hgen' : (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) (n + 1)))
        ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ))
        = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (hSimplex H n k ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)))) (1 : ℤ) := by
      rw [show (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) (n + 1)))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ))
            = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n + 1⦌) τ'))) (1 : ℤ)
          from Work.Cohomology.chainComplexMap_ι_apply (TopCat.toSSet.map inclHom) (n + 1) τ' 1]
      rw [hτ']
    rw [← hgen']
    have h2 : (ModuleCat.Hom.hom
          (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1))))
        ((ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) (n + 1)))
          ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ))) = 0 := by
      have hcond : (inclChainMap (X := X) (A := A) (n + 1)) ≫
          (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1))) = 0 :=
        cokernel.condition _
      have h3 := congrArg (fun (m : (singChainC A).X (n + 1) ⟶
            CategoryTheory.Limits.cokernel (inclChainMap (X := X) (A := A) (n + 1))) =>
          (ModuleCat.Hom.hom m)
            ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ')) (1 : ℤ))) hcond
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] using h3
    rw [h2]
    exact zsmul_zero _
  have hP : LinearMap.ker ((ModuleCat.Hom.hom
        (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1)))).comp
      ((ModuleCat.Hom.hom (prismHom H n)).comp
        (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) n)))) = ⊤ :=
    mem_of_gen_sset A n _ (fun τ => by
      rw [LinearMap.mem_ker]
      show (ModuleCat.Hom.hom
            (CategoryTheory.Limits.cokernel.π (inclChainMap (X := X) (A := A) (n + 1))))
          ((ModuleCat.Hom.hom (prismHom H n))
            ((ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) n))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ))
                (1 : ℤ)))) = 0
      rw [show (ModuleCat.Hom.hom (inclChainMap (X := X) (A := A) n))
              ((ModuleCat.Hom.hom ((singX A).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)) (1 : ℤ))
            = (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ))) (1 : ℤ)
          from Work.Cohomology.chainComplexMap_ι_apply (TopCat.toSSet.map inclHom) n τ 1]
      rw [show (ModuleCat.Hom.hom (prismHom H n))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ))) (1 : ℤ))
            = prismVal H n ((TopCat.toSSet.map inclHom).app (Opposite.op ⦋n⦌) τ)
          from prismHom_gen H n _]
      exact key τ)
  refine LinearMap.ext (fun x => ?_)
  exact LinearMap.mem_ker.mp (by rw [hP]; exact Submodule.mem_top)

end

end Work.Serre
