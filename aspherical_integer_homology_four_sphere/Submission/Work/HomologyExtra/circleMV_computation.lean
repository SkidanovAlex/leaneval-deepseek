import Mathlib
import Submission.Work.HomologyExtra.SimplexCircleCover
import Submission.Work.HomologyExtra.cycleClass_naturality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Mayer–Vietoris computation for the two–element cover of `∂Δ²`

Let `X = ∂Δ²` be the boundary of the standard `2`-simplex, covered by the two open sets
`circleU = {w 0 < 1/2}` and `circleV = {w 1 < 1/2} ∪ {w 2 < 1/2}`
(`Submission/Work/HomologyExtra/SimplexCircleCover.lean`).  The fundamental cycle of `∂Δ²`
is *small* for this cover without subdivision, so the Mayer–Vietoris connecting map
`mvδX : H₁(∂Δ²) ⟶ H₀(circleU ∩ circleV)` can be computed on the level of chains.

The result — the main theorem of this file — is

`mvδX (fundamental class) = [ [v₂] - [v₁] ]`,

i.e. the connecting map sends the fundamental class of `∂Δ²` to the class of the
`0`-chain `[v₂] - [v₁]` in `H₀(circleU ∩ circleV)`.  The two vertices `v₁` and `v₂` lie in
different components of the intersection, which is why this class is non–trivial and why the
fundamental class of `∂Δ²` detects the generator of the kernel of the Mayer–Vietoris map.

The proof is the standard computation of a connecting homomorphism on an explicit cycle:

* `circleLift` — the lift of the small chain `x₃` to `C₁(U) ⊞ C₁(V)` (Lemma `circleLift_mvRight`);
* the boundary of that lift is the intersection chain (`mvLeft_circleLift`, using the two
  hypotheses `hU`, `hV` which are the statements that the boundaries of `x_U` and `x_V` are the
  intersection chain);
* `ShortComplex.ShortExact.δ_eq` computes the connecting map on the cycle, and the small–chains
  isomorphism identifies the fundamental class of `∂Δ²` with the class of the small chain
  `x₃` (`simplexBoundaryClass_comp_smallIso_inv`).

## Main results

* `circleUChain_smallOfU`, `circleVChain_smallOfV` — the images of the two pieces of the
  fundamental cycle in the small chains;
* `circleLift_mvRight`, `mvLeft_circleLift` — the two compatibility relations for the lift;
* `cycleClass_comp_mvδ` — the Mayer–Vietoris connecting map on the class of `x₃`;
* `simplexBoundaryClass_comp_smallIso_inv` — the fundamental class as a small chain;
* `circleMV_computation` — the computation of the connecting map on the fundamental class.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-! ## Transport along the canonical isomorphism `(K ⊞ L).X n ≅ K.X n ⊞ L.X n`

The first terms of the Mayer–Vietoris sequence are a biproduct of chain complexes, whose
degree–`n` parts are only canonically isomorphic to the biproducts of the degree–`n` parts.
The lemmas below translate the differential, and the structure maps of the Mayer–Vietoris
sequence, across that isomorphism. -/

section BiprodTransport
variable {K L M : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}

lemma biprodXIso_inv_fst (i : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (biprod.fst : K ⊞ L ⟶ K).f i = biprod.fst := by
  rw [← HomologicalComplex.biprodXIso_hom_fst K L i, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

lemma biprodXIso_inv_snd (i : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (biprod.snd : K ⊞ L ⟶ L).f i = biprod.snd := by
  rw [← HomologicalComplex.biprodXIso_hom_snd K L i, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

lemma inl_f_comp_biprodXIso_hom (i : ℕ) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (HomologicalComplex.biprodXIso K L i).hom = biprod.inl := by
  rw [← HomologicalComplex.inl_biprodXIso_inv K L i, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

lemma inr_f_comp_biprodXIso_hom (i : ℕ) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (HomologicalComplex.biprodXIso K L i).hom = biprod.inr := by
  rw [← HomologicalComplex.inr_biprodXIso_inv K L i, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The degree–`i` part of `biprod.desc`, transported across `biprodXIso`. -/
lemma biprod_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ℕ) :
    (biprod.desc α β).f i =
      (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.desc (α.f i) (β.f i) := by
  rw [HomologicalComplex.biprodX_ext_from_iff]
  constructor
  · rw [HomologicalComplex.biprod_inl_desc_f, ← Category.assoc, inl_f_comp_biprodXIso_hom,
      biprod.inl_desc]
  · rw [HomologicalComplex.biprod_inr_desc_f, ← Category.assoc, inr_f_comp_biprodXIso_hom,
      biprod.inr_desc]

/-- The `fst`–component of the differential of a biproduct of chain complexes. -/
lemma biprodXIso_inv_d_fst (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (K ⊞ L).d i j ≫ (biprod.fst : K ⊞ L ⟶ K).f j
      = biprod.fst ≫ K.d i j := by
  rw [← HomologicalComplex.Hom.comm (biprod.fst : K ⊞ L ⟶ K) i j, ← Category.assoc,
    biprodXIso_inv_fst]

/-- The `snd`–component of the differential of a biproduct of chain complexes. -/
lemma biprodXIso_inv_d_snd (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (K ⊞ L).d i j ≫ (biprod.snd : K ⊞ L ⟶ L).f j
      = biprod.snd ≫ L.d i j := by
  rw [← HomologicalComplex.Hom.comm (biprod.snd : K ⊞ L ⟶ L) i j, ← Category.assoc,
    biprodXIso_inv_snd]

end BiprodTransport

/-! ## The two components of `mvLeft`, in the "chainComplex" presentation -/

lemma mvLeft_fst_apply' {X : TopCat} (U V : Set X) (n : ℕ) :
    (Work.Cohomology.mvLeft U V).f n
        ≫ (biprod.fst : Work.Cohomology.singularChains ℤ (TopCat.of U) ⊞
            Work.Cohomology.singularChains ℤ (TopCat.of V) ⟶
            Work.Cohomology.singularChains ℤ (TopCat.of U)).f n
      = (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVU U V))
          (ModuleCat.of ℤ ℤ)).f n :=
  HomologicalComplex.biprod_lift_fst_f _ _ n

lemma mvLeft_snd_apply' {X : TopCat} (U V : Set X) (n : ℕ) :
    (Work.Cohomology.mvLeft U V).f n
        ≫ (biprod.snd : Work.Cohomology.singularChains ℤ (TopCat.of U) ⊞
            Work.Cohomology.singularChains ℤ (TopCat.of V) ⟶
            Work.Cohomology.singularChains ℤ (TopCat.of V)).f n
      = (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVV U V))
          (ModuleCat.of ℤ ℤ)).f n :=
  HomologicalComplex.biprod_lift_snd_f _ _ n

/-! ## The two pieces of the fundamental cycle in the small chains -/

/-- The `U`–part of the fundamental cycle, viewed in the small chains. -/
theorem circleUChain_smallOfU :
    circleUChain ≫ (Work.Cohomology.smallOfU circleU circleV).f 1
      = (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
          ⟨simplexBoundaryFaceSimplex 1 0, circleFace0_isSmall⟩ :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

/-- The `V`–part of the fundamental cycle, viewed in the small chains. -/
theorem circleVChain_smallOfV :
    circleVChain ≫ (Work.Cohomology.smallOfV circleU circleV).f 1
      = (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
            ⟨simplexBoundaryFaceSimplex 1 1, circleFace1_isSmall⟩
          - (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
            ⟨simplexBoundaryFaceSimplex 1 2, circleFace2_isSmall⟩ := by
  show ((SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
        (Work.Homology.liftSimplex (simplexBoundaryFaceSimplex 1 1) circleFace1_mem_circleV) :
          Work.Homology.ZMod ⟶ (SSet.chainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
            (ModuleCat.of ℤ ℤ)).X 1)
      - (SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
        (Work.Homology.liftSimplex (simplexBoundaryFaceSimplex 1 2) circleFace2_mem_circleV) :
          Work.Homology.ZMod ⟶ (SSet.chainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
            (ModuleCat.of ℤ ℤ)).X 1))
      ≫ (SSet.chainComplexMap (Work.Cohomology.smallLiftV circleU circleV)
          (ModuleCat.of ℤ ℤ)).f 1
    = SSet.ιChainComplex (Work.Cohomology.smallSSet circleU circleV)
          ⟨simplexBoundaryFaceSimplex 1 1, circleFace1_isSmall⟩
        - SSet.ιChainComplex (Work.Cohomology.smallSSet circleU circleV)
          ⟨simplexBoundaryFaceSimplex 1 2, circleFace2_isSmall⟩
  rw [Preadditive.sub_comp]
  congr 1 <;> (rw [SSet.ι_chainComplexMap_f]; rfl)

/-! ## The lift of the small chain to `C₁(U) ⊞ C₁(V)` -/

/-- **The lift of the small chain `x₃ = F₀ - F₁ + F₂` to `C₁(U) ⊞ C₁(V)`**, i.e. the pair
`(x_U, x_V)` of its two pieces, transported across the canonical isomorphism
`(C(U) ⊞ C(V)).X 1 ≅ C(U).X 1 ⊞ C(V).X 1`. -/
def circleLift : Work.Homology.ZMod ⟶ ((Work.Cohomology.mvShort circleU circleV).X₂).X 1 :=
  biprod.lift circleUChain circleVChain
    ≫ (HomologicalComplex.biprodXIso (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU))
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)) 1).inv

/-- **The lift of the small chain `x₃` is indeed a lift**: it maps to `x₃` under the second
Mayer–Vietoris map. -/
theorem circleLift_mvRight :
    circleLift ≫ (Work.Cohomology.mvRight circleU circleV).f 1 = circleSmallChain := by
  rw [show circleLift ≫ (Work.Cohomology.mvRight circleU circleV).f 1
      = circleUChain ≫ (Work.Cohomology.smallOfU circleU circleV).f 1
        + circleVChain ≫ (-(Work.Cohomology.smallOfV circleU circleV)).f 1 from ?_]
  · rw [circleUChain_smallOfU,
      show (-(Work.Cohomology.smallOfV circleU circleV)).f 1
        = -((Work.Cohomology.smallOfV circleU circleV).f 1) from rfl,
      Preadditive.comp_neg, circleVChain_smallOfV, circleSmallChain]
    abel
  · rw [show Work.Cohomology.mvRight circleU circleV
        = biprod.desc (Work.Cohomology.smallOfU circleU circleV)
            (-(Work.Cohomology.smallOfV circleU circleV)) from rfl]
    rw [biprod_desc_f]
    rw [show circleLift = biprod.lift circleUChain circleVChain
        ≫ (HomologicalComplex.biprodXIso (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU))
            (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)) 1).inv from rfl]
    rw [Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_desc]

/-- **The boundary of the lift is the intersection chain.**  This is where the two hypotheses
about the boundaries of `x_U` and `x_V` are used. -/
theorem mvLeft_circleLift
    (hU : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleUChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleU)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVU Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0))
    (hV : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleVChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleV)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVV Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0)) :
    circleIntersectionChain ≫ (Work.Cohomology.mvLeft circleU circleV).f 0
      = circleLift ≫ ((Work.Cohomology.mvShort circleU circleV).X₂).d 1 0 := by
  apply HomologicalComplex.biprodX_ext_to
  · have h1 : (circleIntersectionChain ≫ (Work.Cohomology.mvLeft circleU circleV).f 0)
          ≫ (biprod.fst : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).f 0
        = circleUChain ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).d 1 0 := by
      rw [Category.assoc, mvLeft_fst_apply' circleU circleV 0]
      exact hU.symm
    have h2 : circleUChain ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).d 1 0
        = (circleLift ≫ ((Work.Cohomology.mvShort circleU circleV).X₂).d 1 0)
            ≫ (biprod.fst : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).f 0 := by
      rw [show (circleLift ≫ ((Work.Cohomology.mvShort circleU circleV).X₂).d 1 0)
            ≫ (biprod.fst : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).f 0
          = biprod.lift circleUChain circleVChain
            ≫ ((HomologicalComplex.biprodXIso (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU))
                (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)) 1).inv
              ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).d 1 0
              ≫ (biprod.fst : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).f 0) from rfl]
      rw [biprodXIso_inv_d_fst, ← Category.assoc, biprod.lift_fst]
    exact h1.trans h2
  · have h1 : (circleIntersectionChain ≫ (Work.Cohomology.mvLeft circleU circleV).f 0)
          ≫ (biprod.snd : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).f 0
        = circleVChain ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).d 1 0 := by
      rw [Category.assoc, mvLeft_snd_apply' circleU circleV 0]
      exact hV.symm
    have h2 : circleVChain ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).d 1 0
        = (circleLift ≫ ((Work.Cohomology.mvShort circleU circleV).X₂).d 1 0)
            ≫ (biprod.snd : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
              Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).f 0 := by
      rw [show (circleLift ≫ ((Work.Cohomology.mvShort circleU circleV).X₂).d 1 0)
            ≫ (biprod.snd : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).f 0
          = biprod.lift circleUChain circleVChain
            ≫ ((HomologicalComplex.biprodXIso (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU))
                (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)) 1).inv
              ≫ (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).d 1 0
              ≫ (biprod.snd : Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU) ⊞
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV) ⟶
                Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).f 0) from rfl]
      rw [biprodXIso_inv_d_snd, ← Category.assoc, biprod.lift_snd]
    exact h1.trans h2

/-! ## The small chain as a cycle, at the index `next 1` -/

lemma circleSmallChain_cycle' :
    circleSmallChain ≫ (Work.Cohomology.smallChains circleU circleV).d 1
      ((ComplexShape.down ℕ).next 1) = 0 := by
  rw [show (ComplexShape.down ℕ).next 1 = 0 from
    ComplexShape.next_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 1 0 by simp [ComplexShape.down_Rel])]
  exact circleSmallChain_cycle

/-! ## The connecting map on the class of the small chain -/

/-- **The Mayer–Vietoris connecting map on the class of the small chain `x₃`** is the class of
the intersection chain.  This is the chain–level form of the main theorem, obtained by applying
`ShortComplex.ShortExact.δ_eq` to the lift `circleLift`. -/
theorem cycleClass_comp_mvδ
    (hU : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleUChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleU)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVU Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0))
    (hV : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleVChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleV)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVV Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0)) :
    cycleClass circleSmallChain circleSmallChain_cycle'
        ≫ Work.Cohomology.mvδ circleU circleV 0
      = cycleClass circleIntersectionChain circleIntersectionChain_cycle := by
  have hS : (Work.Cohomology.mvShort circleU circleV).ShortExact :=
    Work.Cohomology.mvShort_shortExact circleU circleV
  have hij : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  have hk : (ComplexShape.down ℕ).next 0 = 0 :=
    ComplexShape.next_eq_self' _ 0 (fun k hk => by simp [ComplexShape.down_Rel] at hk)
  have hmvδ : Work.Cohomology.mvδ circleU circleV 0 = hS.δ 1 0 hij := by
    rw [Work.Cohomology.mvδ]
  rw [hmvδ]
  exact ShortComplex.ShortExact.δ_eq hS 1 0 hij circleSmallChain circleSmallChain_cycle
    (x₂ := circleLift) circleLift_mvRight (x₁ := circleIntersectionChain)
    (mvLeft_circleLift hU hV) 0 hk

/-! ## The fundamental class of `∂Δ²` in the small chains -/

/-- **The fundamental class of `∂Δ²` is the class of the small chain `x₃`**: the inverse of the
small–chains isomorphism sends the fundamental class of the sphere to the class of the
fundamental cycle, viewed in the small chains. -/
theorem simplexBoundaryClass_comp_smallIso_inv :
    simplexBoundaryClass 1
        ≫ (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
            circleU_union_circleV 1).inv
      = cycleClass circleSmallChain circleSmallChain_cycle' := by
  have h1 : cycleClass circleSmallChain circleSmallChain_cycle'
      ≫ (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
          circleU_union_circleV 1).hom
      = simplexBoundaryClass 1 := by
    rw [show (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
          circleU_union_circleV 1).hom
        = HomologicalComplex.homologyMap (Work.Cohomology.smallToSing circleU circleV) 1
        from rfl]
    rw [cycleClass_naturality (Work.Cohomology.smallToSing circleU circleV) circleSmallChain
      circleSmallChain_cycle']
    rw [simplexBoundaryClass]
    exact cycleClass_eq _ _ circleSmallChain_smallToSing
  calc simplexBoundaryClass 1
        ≫ (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
            circleU_union_circleV 1).inv
      = (cycleClass circleSmallChain circleSmallChain_cycle'
          ≫ (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
              circleU_union_circleV 1).hom)
          ≫ (Work.Cohomology.smallIso circleU circleV isOpen_circleU isOpen_circleV
              circleU_union_circleV 1).inv := by
            rw [h1]
      _ = cycleClass circleSmallChain circleSmallChain_cycle' := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## The main theorem -/

theorem circleMV_computation
    (hU : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleUChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleU)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVU Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0))
    (hV : CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleVChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleV)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVV Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0)) :
    CategoryTheory.CategoryStruct.comp (Work.HomologyExtra.simplexBoundaryClass 1)
        (Work.Cohomology.mvδX Work.HomologyExtra.circleU Work.HomologyExtra.circleV
          Work.HomologyExtra.isOpen_circleU Work.HomologyExtra.isOpen_circleV
          Work.HomologyExtra.circleU_union_circleV 0)
      = Work.HomologyExtra.cycleClass Work.HomologyExtra.circleIntersectionChain
          Work.HomologyExtra.circleIntersectionChain_cycle := by
  rw [Work.Cohomology.mvδX]
  rw [← Category.assoc]
  have key : Work.HomologyExtra.simplexBoundaryClass 1
      ≫ (Work.Cohomology.smallIso Work.HomologyExtra.circleU Work.HomologyExtra.circleV
          Work.HomologyExtra.isOpen_circleU Work.HomologyExtra.isOpen_circleV
          Work.HomologyExtra.circleU_union_circleV ((0 : ℕ) + 1)).inv
      = Work.HomologyExtra.cycleClass Work.HomologyExtra.circleSmallChain
          Work.HomologyExtra.circleSmallChain_cycle' := by
    simpa using simplexBoundaryClass_comp_smallIso_inv
  rw [key, cycleClass_comp_mvδ hU hV]

end

end Work.HomologyExtra
