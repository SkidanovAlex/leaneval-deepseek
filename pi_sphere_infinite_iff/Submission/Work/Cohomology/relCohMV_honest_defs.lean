import Mathlib
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.relCohMV_honest_prereq
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relSmallCochains_iso
import Submission.Work.Cohomology.relCohMV_les
import Submission.Work.Cohomology.Endgame.relMVUVQuasiIso
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.cokerSmallAux

/-!
# The relative Mayer–Vietoris sequence of **honest** relative cochains: the maps

For a topological space `X`, a subset `A ⊆ X` and an open cover `X = U ∪ V`, the relative
Mayer–Vietoris sequence of the pair `(X,A)` is exhibited here as a short exact sequence of cochain
complexes

`0 → C^*(C^{U,V}(X,A)) --F--> C^*(U, U∩A) ⊞ C^*(V, V∩A) --G--> C^*(U∩V, U∩V∩A) → 0`

whose middle and right terms are the **honest** relative cochain complexes `relComplex`, and whose
first term is the `ℤ`-dual of the relative small chains of the cover.  The two maps are

* `hmvF` — the transpose of the canonical chain maps `alphaU`, `alphaV`
  (`Work.Cohomology.HMV.alphaU`) which send a small simplex lying in `U` (resp. `V`) to the class of
  the same simplex in `C^{U,V}(X,A)`;
* `hmvG` — the transpose of the canonical chain maps `gamma`, `delta` (the inclusions
  `C^{U,V}(U∩V, U∩V∩A) → C^{U,V}(U, U∩A)`, `→ C^{U,V}(V, V∩A)`), with the sign convention of the
  Mayer–Vietoris differential.

The comparison with the honest relative complexes is provided by the cochain maps `cmpU`, `cmpV`,
`cmpW`, `cmpX`, which are the transposes of the comparison quasi-isomorphisms
`Work.Cohomology.HMV.etaU`, `Work.Cohomology.HMV.etaV`, `Work.Cohomology.relMVUVPhi`,
`Work.Cohomology.HMV.mvPhi` (identifying a simplex of the subspace with the same small simplex).

## Main definitions

* `relDualIsoComplex` — the relative cochains as the `ℤ`-dual of the relative chains;
* `hmvF`, `hmvG` — the maps of the relative Mayer–Vietoris sequence;
* `cmpU`, `cmpV`, `cmpW`, `cmpX` — the comparison maps with the honest relative complexes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## 1. The relative cochains as the dual of the relative chains -/

/-- The relative cochain complex is the `ℤ`-dual of the relative chain complex, as a chosen
isomorphism of cochain complexes whose components are `relDualIso`. -/
noncomputable def relDualIsoComplex (X : TopCat) (A : Set X) :
    dualComplex ℤ (relChains X A) ≅ relComplex ℤ X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n)
    (fun i j hij => by rw [← hij]; exact relDualIso_comm X A i)

@[simp] theorem relDualIsoComplex_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualIsoComplex X A).hom.f n = (relDualIso X A n).hom :=
  HomologicalComplex.Hom.isoOfComponents_hom_f _ _ n

@[simp] theorem relDualIsoComplex_inv_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualIsoComplex X A).inv.f n = (relDualIso X A n).inv :=
  HomologicalComplex.Hom.isoOfComponents_inv_f _ _ n

/-! ## 2. The two maps of the relative Mayer–Vietoris sequence -/

/-- **The first map of the relative Mayer–Vietoris sequence**, `C^*(C^{U,V}(X,A)) ⟶
C^*(U,U∩A) ⊞ C^*(V,V∩A)`: the transpose of the canonical chain maps `alphaU`, `alphaV`. -/
noncomputable def hmvF (X : TopCat) (A U V : Set X) :
    dualComplex ℤ (relMVTopC X A U V)
      ⟶ dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V) :=
  biprod.lift
    (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V))
    (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V))

/-- **The second map of the relative Mayer–Vietoris sequence**, `C^*(U,U∩A) ⊞ C^*(V,V∩A) ⟶
C^*(U∩V,U∩V∩A)`: the transpose of the canonical chain maps `gamma`, `delta`. -/
noncomputable def hmvG (X : TopCat) (A U V : Set X) :
    dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)
      ⟶ dualComplex ℤ (relMVUV X A U V) :=
  biprod.desc
    (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V))
    (-(dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)))

/-- The canonical chain maps `gamma` and `delta` agree after composition with `alphaU` and `alphaV`
respectively; this is the chain level content of `hmvF ≫ hmvG = 0`. -/
theorem gamma_comp_alphaU_eq_delta_comp_alphaV (X : TopCat) (A U V : Set X) :
    HMV.gamma X A U V ≫ HMV.alphaU X A U V = HMV.delta X A U V ≫ HMV.alphaV X A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₁ U V A))).1
  rw [← Category.assoc, ← Category.assoc, HMV.gamma_comp X A U V, HMV.delta_comp X A U V]
  rw [Category.assoc, Category.assoc, HMV.alphaU_comp X A U V, HMV.alphaV_comp X A U V]
  rw [← Category.assoc, ← Category.assoc,
    subInclChain_smallInToSmall U V (Set.inter_subset_left : U ∩ V ⊆ U),
    subInclChain_smallInToSmall U V (Set.inter_subset_right : U ∩ V ⊆ V)]

/-- The two maps of the relative Mayer–Vietoris sequence compose to zero. -/
theorem hmv_comp (X : TopCat) (A U V : Set X) :
    hmvF X A U V ≫ hmvG X A U V = 0 := by
  rw [hmvF, hmvG, biprod.lift_desc, Preadditive.comp_neg, ← dualComplexMap_comp,
    ← dualComplexMap_comp, gamma_comp_alphaU_eq_delta_comp_alphaV X A U V, add_neg_cancel]

/-- The subspace `U ∩ V` as a topological space (named so that statements can avoid the `↥`
notation). -/
abbrev topW (X : TopCat) (U V : Set X) : TopCat := TopCat.of ↥(U ∩ V)

/-- The inclusion of the subspace `A ∩ U` into `A`, as a hypothesis for `relComplexMap`. -/
theorem interAU_incl_subtypeIncl (X : TopCat) (A U : Set X) :
    ∀ x ∈ interAU A U, (Work.Cohomology.subtypeIncl X U) x ∈ A := fun x hx => hx

/-- The inclusion of the subspace `A ∩ V` into `A`, as a hypothesis for `relComplexMap`. -/
theorem interAU_incl_subtypeIncl_V (X : TopCat) (A V : Set X) :
    ∀ x ∈ interAU A V, (Work.Cohomology.subtypeIncl X V) x ∈ A := fun x hx => hx

/-- The map of pairs `(U∩V, A∩(U∩V)) → (U, A∩U)`, as a hypothesis for `relComplexMap`. -/
theorem interAU_incl_pdIncl_U (X : TopCat) (A U V : Set X) :
    ∀ x ∈ interAU A (U ∩ V), (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) x
      ∈ interAU A U := fun x hx => hx

/-- The map of pairs `(U∩V, A∩(U∩V)) → (V, A∩V)`, as a hypothesis for `relComplexMap`. -/
theorem interAU_incl_pdIncl_V (X : TopCat) (A U V : Set X) :
    ∀ x ∈ interAU A (U ∩ V), (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) x
      ∈ interAU A V := fun x hx => hx


/-! ## 3. The comparison maps with the honest relative complexes -/

/-- **The comparison of the `U`-piece with the honest relative cochains of `U`**: the transpose of
the quasi-isomorphism `etaU` identifying a simplex of `U` with the same small simplex. -/
noncomputable def cmpU (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of U) (interAU A U) ⟶ dualComplex ℤ (relMVUU X A U V) :=
  (relDualIsoComplex (TopCat.of U) (interAU A U)).inv
    ≫ dualComplexMap ℤ (relMVUU X A U V)
        (relChains (TopCat.of U) (interAU A U)) (HMV.etaU A U V)

/-- **The comparison of the `V`-piece with the honest relative cochains of `V`**. -/
noncomputable def cmpV (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of V) (interAU A V) ⟶ dualComplex ℤ (relMVVV X A U V) :=
  (relDualIsoComplex (TopCat.of V) (interAU A V)).inv
    ≫ dualComplexMap ℤ (relMVVV X A U V)
        (relChains (TopCat.of V) (interAU A V)) (HMV.etaV A U V)

/-- **The comparison of the overlap piece with the honest relative cochains of `U ∩ V`**. -/
noncomputable def cmpW (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
      ⟶ dualComplex ℤ (relMVUV X A U V) :=
  (relDualIsoComplex (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))).inv
    ≫ dualComplexMap ℤ (relMVUV X A U V)
        (relChains (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))) (relMVUVPhi X A U V)

/-- **The comparison of the pair `(X,A)` with the relative small cochains**: a relative cochain is
restricted to the small chains of the cover. -/
noncomputable def cmpX (X : TopCat) (A U V : Set X) :
    relComplex ℤ X A ⟶ dualComplex ℤ (relMVTopC X A U V) :=
  (relDualIsoComplex X A).inv
    ≫ dualComplexMap ℤ (relMVTopC X A U V) (relChains X A) (HMV.mvPhi X A U V)

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-! ## 4. The comparison maps are isomorphisms on cohomology -/

/-- The dual of an isomorphism of chain complexes is an isomorphism of cochain complexes. -/
theorem isIso_dualComplexMap {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) [IsIso φ] :
    IsIso (dualComplexMap ℤ C D φ) := by
  refine IsIso.mk ⟨dualComplexMap ℤ D C (CategoryTheory.inv φ), ?_, ?_⟩
  · rw [← dualComplexMap_comp, IsIso.inv_hom_id, dualComplexMap_id]
  · rw [← dualComplexMap_comp, IsIso.hom_inv_id, dualComplexMap_id]

/-- **The comparison `cmpX` is an isomorphism on cohomology**: the relative cohomology of the pair
`(X,A)` is computed by the relative small cochains of the cover. -/
theorem isIso_homologyMap_cmpX (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cmpX X A U V) k) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap (relDualIsoComplex X A).inv k) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k)
      (relDualIsoComplex X A).inv
  haveI h2 : IsIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relMVTopC X A U V) (relChains X A) (HMV.mvPhi X A U V)) k) :=
    dualComplexMap_quasiIso (HMV.mvPhi X A U V) (fun n => relSmallTopProjective X U V A n)
      (fun n => relChainsProjective X A n)
      (fun n => HMV.isIso_homologyMap_mvPhi X A U V hU hV hcov n) k
  rw [cmpX, HomologicalComplex.homologyMap_comp]
  exact inferInstance

end

section NatWrappers

/-- The left-hand side of the naturality square for the `U`-piece. -/
noncomputable abbrev natU_lhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ X A ⟶ dualComplex ℤ (relMVUU X A U V) :=
  relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := X) (interAU A U) A (subtypeIncl X U)
      (interAU_incl_subtypeIncl X A U)
    ≫ cmpU X A U V

/-- The right-hand side of the naturality square for the `U`-piece. -/
noncomputable abbrev natU_rhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ X A ⟶ dualComplex ℤ (relMVUU X A U V) :=
  cmpX X A U V ≫ dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V)

/-- The left-hand side of the naturality square for the `V`-piece. -/
noncomputable abbrev natV_lhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ X A ⟶ dualComplex ℤ (relMVVV X A U V) :=
  relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := X) (interAU A V) A (subtypeIncl X V)
      (interAU_incl_subtypeIncl_V X A V)
    ≫ cmpV X A U V

/-- The right-hand side of the naturality square for the `V`-piece. -/
noncomputable abbrev natV_rhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ X A ⟶ dualComplex ℤ (relMVVV X A U V) :=
  cmpX X A U V ≫ dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V)

/-- The left-hand side of the naturality square for the overlap, `U`-component. -/
noncomputable abbrev natWU_lhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of U) (interAU A U) ⟶ dualComplex ℤ (relMVUV X A U V) :=
  relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of U)
      (interAU A (U ∩ V)) (interAU A U) (pdIncl U (U ∩ V) Set.inter_subset_left)
      (interAU_incl_pdIncl_U X A U V)
    ≫ cmpW X A U V

/-- The right-hand side of the naturality square for the overlap, `U`-component. -/
noncomputable abbrev natWU_rhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of U) (interAU A U) ⟶ dualComplex ℤ (relMVUV X A U V) :=
  cmpU X A U V ≫ dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)

/-- The left-hand side of the naturality square for the overlap, `V`-component. -/
noncomputable abbrev natWV_lhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of V) (interAU A V) ⟶ dualComplex ℤ (relMVUV X A U V) :=
  relComplexMap ℤ (X₁ := topW X U V) (X₂ := TopCat.of V)
      (interAU A (U ∩ V)) (interAU A V) (pdIncl V (U ∩ V) Set.inter_subset_right)
      (interAU_incl_pdIncl_V X A U V)
    ≫ cmpW X A U V

/-- The right-hand side of the naturality square for the overlap, `V`-component. -/
noncomputable abbrev natWV_rhs (X : TopCat) (A U V : Set X) :
    relComplex ℤ (TopCat.of V) (interAU A V) ⟶ dualComplex ℤ (relMVUV X A U V) :=
  cmpV X A U V ≫ dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)

end NatWrappers

end Work.Cohomology
