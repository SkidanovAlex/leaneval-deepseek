import Mathlib
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.ThomBordism.doubleFC.defs
import Submission.Work.ThomBordism.doubleFC.interiorData
import Submission.Work.ThomBordism.doubleFC.span_pairMap_M
import Submission.Work.ThomBordism.doubleFC.span_pairMap_N
import Submission.Work.ThomBordism.doubleFC.span_localClassAt_seam
import Submission.Work.ThomBordism.localClassAt
import Submission.Work.Orient.Port.Hatcher
import Submission.Work.Cohomology.pd_alpha2_zeta
import Submission.Work.Cohomology.cokerSmallLemmas
import Submission.Work.Cohomology.capRelAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fundamental class of the double, and its relative class

`Work.ThomBordism.doubleFundClass` produces a fundamental class `c ∈ H₉(D;ℤ)` of the double
`D = M ∪_{∂M} M̄` of a compact `C¹` `9`-manifold with boundary `M` whose localisation at every
point of `D` generates the local homology, and whose image in `H₉(D, B;ℤ)` (`B` the second half
of the double) is `±` the image of the relative fundamental class `w ∈ H₉(M, ∂M;ℤ)` of `M` under
`Work.ThomBordism.inclRelMap`.

The proof reproduces, in the namespace `Work.ThomBordism.RelDoubleClass`, the construction of the
fundamental class of the double from a relative class of `(M, ∂M)`
(`Work.ThomBordism.doubleFC.classLocalClass`, which computes the local classes of that class at the
interior points of either copy of `M`), and adds to it the chain-level computation identifying the
image of the class in `H(D, B)` with the image of `w` under `inclRelMap`: the class is represented
by `τ_M(x) - τ_N(x)` for a chain `x` of `M` representing `w`, the second summand is supported in `B`
(hence dies in `C_*(D, B)`), and the first is the image of `x` under `inclRelMap` by the defining
property of `relChainsMapOf`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.RelDoubleClass

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]

/-- The boundary of `M` as an excluded set. -/
abbrev bdry : Set M := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M

/-- The complement of the image of `y` under the first inclusion. -/
abbrev complM (y : M) : Set (Double n M) := ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ

/-- The complement of the image of `y` under the second inclusion. -/
abbrev complN (y : M) : Set (Double n M) := ({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ

/-- The local class of `w` at an interior point `y` (the expression in the hypothesis `hwint` of
`Work.ThomBordism.doubleFundamentalClass`). -/
noncomputable def locW
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1))
    (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    (Work.Cohomology.relChains (TopCat.of M) ({y} : Set M)ᶜ).homology (n + 1) :=
  (HomologicalComplex.homologyMap
    (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy)
    (n + 1)) w

/-- The image of the local class of `w` at `y` in the double, along the first copy. -/
noncomputable def pairWιM
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1))
    (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    (Work.Cohomology.relChains (TopCat.of (Double n M))
      ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ).homology (n + 1) :=
  (HomologicalComplex.homologyMap
    (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy
      ≫ DoubleFC.pairMapιM n M y) (n + 1)) w

/-- The image of the local class of `w` at `y` in the double, along the second copy. -/
noncomputable def pairWιN
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1))
    (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    (Work.Cohomology.relChains (TopCat.of (Double n M))
      ({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ).homology (n + 1) :=
  (HomologicalComplex.homologyMap
    (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy
      ≫ DoubleFC.pairMapιN n M y) (n + 1)) w

theorem pairWιM_eq
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1))
    (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    pairWιM w y hy
      = (HomologicalComplex.homologyMap (DoubleFC.pairMapιM n M y) (n + 1)) (locW w y hy) := by
  rw [pairWιM, locW, HomologicalComplex.homologyMap_comp]
  rfl

theorem pairWιN_eq
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1))
    (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    pairWιN w y hy
      = (HomologicalComplex.homologyMap (DoubleFC.pairMapιN n M y) (n + 1)) (locW w y hy) := by
  rw [pairWιN, locW, HomologicalComplex.homologyMap_comp]
  rfl

/-- `chainMap` of the identity is the identity. -/
theorem chainMap_id (X : TopCat) :
    Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 (Work.Cohomology.singularChains ℤ X) :=
  CategoryTheory.Functor.map_id _ _

/-- The defining property of `relChainsInclPunct`: the projection to the pair `(M, M∖{y})`. -/
theorem relChainsInclPunct_π (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        (bdry (n := n) (M := M))) ≫
      Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy
      = CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          ({z : M | z ≠ y})) := by
  rw [Work.ThomBordism.relChainsInclPunct, Work.ThomBordism.relChainsIncl,
    Work.Cohomology.capRel_cokernel_π_relChainsMapOf, chainMap_id, Category.id_comp]

/-- The second inclusion factors through the complement of the image of the first one. -/
theorem iNHom_eq_corestr (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    ∃ (g : TopCat.of M ⟶ TopCat.of (complM (n := n) (M := M) y)),
      DoubleFC.iNHom n M = g ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double n M))
        (complM (n := n) (M := M) y) := by
  let gfun : M → complM (n := n) (M := M) y := fun z =>
    ⟨doubleιN (n := n) (M := M) z, by
      intro h
      obtain ⟨p, hp, -⟩ := doubleιM_eq_ιN_iff.mp h.symm
      exact hy (by rw [hp]; exact p.2)⟩
  have hg : Continuous gfun :=
    Continuous.subtype_mk (continuous_doubleιN (n := n) (M := M)) (fun z => by
      show doubleιN (n := n) (M := M) z ∈ complM (n := n) (M := M) y
      intro h
      obtain ⟨p, hp, -⟩ := doubleιM_eq_ιN_iff.mp h.symm
      exact hy (by rw [hp]; exact p.2))
  refine ⟨TopCat.ofHom ⟨gfun, hg⟩, ?_⟩
  ext z
  rfl

/-- The first inclusion factors through the complement of the image of the second one. -/
theorem iMHom_eq_corestr (y : M) (hy : y ∉ bdry (n := n) (M := M)) :
    ∃ (g : TopCat.of M ⟶ TopCat.of (complN (n := n) (M := M) y)),
      DoubleFC.iMHom n M = g ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double n M))
        (complN (n := n) (M := M) y) := by
  let gfun : M → complN (n := n) (M := M) y := fun z =>
    ⟨doubleιM (n := n) (M := M) z, by
      intro h
      obtain ⟨p, -, hp⟩ := doubleιM_eq_ιN_iff.mp h
      exact hy (by rw [hp]; exact p.2)⟩
  have hg : Continuous gfun :=
    Continuous.subtype_mk (continuous_doubleιM (n := n) (M := M)) (fun z => by
      show doubleιM (n := n) (M := M) z ∈ complN (n := n) (M := M) y
      intro h
      obtain ⟨p, -, hp⟩ := doubleιM_eq_ιN_iff.mp h
      exact hy (by rw [hp]; exact p.2))
  refine ⟨TopCat.ofHom ⟨gfun, hg⟩, ?_⟩
  ext z
  rfl

/-- The chain map of the second inclusion is killed by the projection away from `doubleιM y`. -/
theorem chainMap_iNHom_killed (y : M) (hy : y ∉ bdry (n := n) (M := M))
    (k : ℕ) (z : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
        (complM (n := n) (M := M) y))).f k)
      (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (DoubleFC.iNHom n M)).f k) z)
      = 0 := by
  obtain ⟨g, hg⟩ := iNHom_eq_corestr (n := n) (M := M) y hy
  rw [hg, Work.Cohomology.chainMap_comp_relChains, HomologicalComplex.comp_f,
    CategoryTheory.ConcreteCategory.comp_apply]
  exact Work.Cohomology.cokernel_π_f_apply_eq_zero k _

/-- The chain map of the first inclusion is killed by the projection away from `doubleιN y`. -/
theorem chainMap_iMHom_killed (y : M) (hy : y ∉ bdry (n := n) (M := M))
    (k : ℕ) (z : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
        (complN (n := n) (M := M) y))).f k)
      (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (DoubleFC.iMHom n M)).f k) z)
      = 0 := by
  obtain ⟨g, hg⟩ := iMHom_eq_corestr (n := n) (M := M) y hy
  rw [hg, Work.Cohomology.chainMap_comp_relChains, HomologicalComplex.comp_f,
    CategoryTheory.ConcreteCategory.comp_apply]
  exact Work.Cohomology.cokernel_π_f_apply_eq_zero k _


/-- **The second half of the double**, the image of the second copy of `M`. -/
abbrev secondHalfG : Set (Double n M) := Set.range (doubleιN (n := n) (M := M))

/-- **The inclusion of the boundary into the second half** (the two copies of `∂M` agree). -/
noncomputable def iBdryHom :
    TopCat.of {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M} ⟶
      TopCat.of (secondHalfG (n := n) (M := M)) :=
  TopCat.ofHom ⟨fun x => ⟨doubleιM (n := n) (M := M) x.1,
      ⟨x.1, ((doubleιM_eq_ιN_iff (n := n) (M := M)).mpr ⟨x, rfl, rfl⟩).symm⟩⟩,
    Continuous.subtype_mk
      (((continuous_doubleιM (n := n) (M := M)).comp continuous_subtype_val)) _⟩

/-- The compatibility of the two inclusions of the boundary. -/
theorem iBdryHom_comp :
    Work.Cohomology.subtypeIncl (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ≫ DoubleFC.iMHom n M
      = iBdryHom (n := n) (M := M) ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double n M))
        (secondHalfG (n := n) (M := M)) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro x
  rfl

/-- **The relative map `C_*(M, ∂M) ⟶ C_*(D, B)`** of the double, `B` the second half. -/
abbrev inclRelMapG : Work.Cohomology.relChains (TopCat.of M)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ⟶
      Work.Cohomology.relChains (TopCat.of (Double n M)) (secondHalfG (n := n) (M := M)) :=
  Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
    ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (secondHalfG (n := n) (M := M))
    (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M)) (iBdryHom_comp (n := n) (M := M))

/-- The second inclusion factors through the second half of the double. -/
theorem iNHom_corestr_secondHalf :
    ∃ (g : TopCat.of M ⟶ TopCat.of (secondHalfG (n := n) (M := M))),
      DoubleFC.iNHom n M = g ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double n M))
        (secondHalfG (n := n) (M := M)) := by
  refine ⟨TopCat.ofHom ⟨fun z => ⟨doubleιN (n := n) (M := M) z, ⟨z, rfl⟩⟩,
      Continuous.subtype_mk (continuous_doubleιN (n := n) (M := M)) _⟩, ?_⟩
  ext z
  rfl

/-- A chain in the image of the second copy of `M` is killed by the projection to `(D, B)`. -/
theorem chainMap_iNHom_killed_secondHalf (k : ℕ)
    (z : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
        (secondHalfG (n := n) (M := M)))).f k)
      (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
        (DoubleFC.iNHom n M)).f k) z) = 0 := by
  obtain ⟨g, hg⟩ := iNHom_corestr_secondHalf (n := n) (M := M)
  rw [hg, Work.Cohomology.chainMap_comp_relChains, HomologicalComplex.comp_f,
    CategoryTheory.ConcreteCategory.comp_apply]
  exact Work.Cohomology.cokernel_π_f_apply_eq_zero k _

/-- **Comparison of the cycle of a chain with the image of a cycle**: if the images of the
underlying chains agree, then so do the cycles. -/
lemma cyclesMap_cycleOf_eq_cyclesMap_chain {A C D : ChainComplex (ModuleCat ℤ) ℕ} (N : ℕ)
    (φ : A ⟶ D) (π : C ⟶ D) (y : A.X N) (hy : A.d N (N - 1) y = 0) (cc : C.X N)
    (hcc : C.d N (N - 1) cc = 0) (h : π.f N cc = φ.f N y) :
    HomologicalComplex.cyclesMap π N (Work.Cohomology.cycleOf N cc hcc)
      = HomologicalComplex.cyclesMap φ N (Work.Cohomology.cycleOf N y hy) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles N)).mp inferInstance
  rw [Work.Cohomology.iCycles_cyclesMap_apply, Work.Cohomology.iCycles_cyclesMap_apply,
    Work.Cohomology.iCycles_cycleOf, Work.Cohomology.iCycles_cycleOf]
  exact h

/-- **The key element-level computation**: the image of a relative chain of `(M, ∂M)` under
`inclRelMapG` is the image of the corresponding chain of `D` under the projection to `(D, B)`. -/
theorem keyElement (x : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (n + 1)) :
    (inclRelMapG (n := n) (M := M)).f (n + 1)
      (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M))).f (n + 1)) x)
    = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
        (secondHalfG (n := n) (M := M)))).f (n + 1))
      (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
        (DoubleFC.iMHom n M)).f (n + 1)) x) := by
  have hkey := Work.Cohomology.capRel_cokernel_π_relChainsMapOf
    (X := TopCat.of M) (Y := TopCat.of (Double n M))
    ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (secondHalfG (n := n) (M := M))
    (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M)) (iBdryHom_comp (n := n) (M := M))
  have hval := congrArg (fun (φ : Work.Cohomology.singularChains ℤ (TopCat.of M) ⟶
      Work.Cohomology.relChains (TopCat.of (Double n M))
        (secondHalfG (n := n) (M := M))) => (φ.f (n + 1)) x) hkey
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply] at hval
  exact hval

/-- `d` commutes with the projection to `(M, M∖{y})`, on elements. -/
theorem pi_y_d_apply (y : M) (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1)) :
    (Work.Cohomology.relChains (TopCat.of M) ({z : M | z ≠ y})).d (k + 1) k
        (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          ({z : M | z ≠ y}))).f (k + 1)) v)
      = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          ({z : M | z ≠ y}))).f k)
        ((Work.Cohomology.singularChains ℤ (TopCat.of M)).d (k + 1) k v) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1) ⟶
      (Work.Cohomology.relChains (TopCat.of M) ({z : M | z ≠ y})).X k) => m v)
    (HomologicalComplex.Hom.comm (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains (TopCat.of M) ({z : M | z ≠ y}))) (k + 1) k)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- `d` commutes with the projection to `(M, ∂M)`, on elements. -/
theorem pi_bdry_d_apply (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1)) :
    (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).d (k + 1) k
        (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M)))).f (k + 1)) v)
      = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M)))).f k)
        ((Work.Cohomology.singularChains ℤ (TopCat.of M)).d (k + 1) k v) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1) ⟶
      (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).X k) => m v)
    (HomologicalComplex.Hom.comm (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains (TopCat.of M) (bdry (n := n) (M := M)))) (k + 1) k)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- `d` commutes with the chain map of the first inclusion, on elements. -/
theorem chainMap_iMHom_d (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1)) :
    (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).d (k + 1) k
        (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iMHom n M)).f (k + 1)) v)
      = ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iMHom n M)).f k)
        ((Work.Cohomology.singularChains ℤ (TopCat.of M)).d (k + 1) k v) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1) ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).X k) => m v)
    (HomologicalComplex.Hom.comm (Work.Cohomology.chainMap ℤ (TopCat.of M)
      (TopCat.of (Double n M)) (DoubleFC.iMHom n M)) (k + 1) k)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- `d` commutes with the chain map of the second inclusion, on elements. -/
theorem chainMap_iNHom_d (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1)) :
    (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).d (k + 1) k
        (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iNHom n M)).f (k + 1)) v)
      = ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iNHom n M)).f k)
        ((Work.Cohomology.singularChains ℤ (TopCat.of M)).d (k + 1) k v) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (k + 1) ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).X k) => m v)
    (HomologicalComplex.Hom.comm (Work.Cohomology.chainMap ℤ (TopCat.of M)
      (TopCat.of (Double n M)) (DoubleFC.iNHom n M)) (k + 1) k)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
/-- The projection to the pair `(M, M∖{y})` applied to a chain, in element form. -/
theorem pi_y_apply (y : M) (hy : y ∉ bdry (n := n) (M := M)) (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
      ({z : M | z ≠ y}))).f k) v
      = (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f k
          (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
            (bdry (n := n) (M := M)))).f k) v) := by
  have h := congrArg (fun (φ : Work.Cohomology.singularChains ℤ (TopCat.of M) ⟶
      Work.Cohomology.relChains (TopCat.of M) ({z : M | z ≠ y})) => (φ.f k) v)
    (relChainsInclPunct_π (n := n) (M := M) y hy)
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact h.symm

/-- **Comparison of the cycle `cycleOf cc` with the image of a cycle `z`**, when the underlying
chains match: if `π.f N cc = ψ.f N (φ.f N (z.iCycles))` then the corresponding cycles agree. -/
lemma cyclesMap_cycleOf_eq_cyclesMap {A B C D : ChainComplex (ModuleCat ℤ) ℕ}
    (N : ℕ) (φ : A ⟶ B) (ψ : B ⟶ D) (π : C ⟶ D)
    (z : A.cycles N) (cc : C.X N)
    (hcc : C.d N (N - 1) cc = 0) (h : π.f N cc = ψ.f N (φ.f N (A.iCycles N z))) :
    HomologicalComplex.cyclesMap π N (Work.Cohomology.cycleOf N cc hcc)
      = HomologicalComplex.cyclesMap ψ N (HomologicalComplex.cyclesMap φ N z) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles N)).mp inferInstance
  rw [Work.Cohomology.iCycles_cyclesMap_apply, Work.Cohomology.iCycles_cyclesMap_apply,
    Work.Cohomology.iCycles_cyclesMap_apply, Work.Cohomology.iCycles_cycleOf]
  exact h

/-- The same as `cyclesMap_cycleOf_eq_cyclesMap`, with the images related by a sign. -/
lemma cyclesMap_cycleOf_eq_neg_cyclesMap {A B C D : ChainComplex (ModuleCat ℤ) ℕ}
    (N : ℕ) (φ : A ⟶ B) (ψ : B ⟶ D) (π : C ⟶ D)
    (z : A.cycles N) (cc : C.X N)
    (hcc : C.d N (N - 1) cc = 0) (h : π.f N cc = -(ψ.f N (φ.f N (A.iCycles N z)))) :
    HomologicalComplex.cyclesMap π N (Work.Cohomology.cycleOf N cc hcc)
      = -(HomologicalComplex.cyclesMap ψ N (HomologicalComplex.cyclesMap φ N z)) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles N)).mp inferInstance
  rw [map_neg, Work.Cohomology.iCycles_cyclesMap_apply, Work.Cohomology.iCycles_cyclesMap_apply,
    Work.Cohomology.iCycles_cyclesMap_apply, Work.Cohomology.iCycles_cycleOf]
  exact h

/-- The two-step form of `homologyMap_homologyπ_cyclesMap`. -/
lemma homologyMap_homologyMap_homologyπ {K L M : ChainComplex (ModuleCat ℤ) ℕ} (N : ℕ)
    (φ : K ⟶ L) (ψ : L ⟶ M) (z : K.cycles N) :
    (HomologicalComplex.homologyMap ψ N) ((HomologicalComplex.homologyMap φ N) ((K.homologyπ N) z))
      = (M.homologyπ N)
        ((HomologicalComplex.cyclesMap ψ N) ((HomologicalComplex.cyclesMap φ N) z)) := by
  rw [Work.Cohomology.homologyMap_homologyπ_cyclesMap]
  rw [Work.Cohomology.homologyMap_homologyπ_cyclesMap]

/-- **The fundamental class of the double and its local classes at the interior points.** -/
theorem relDoubleClass_exists
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).homology (n + 1)) :
    ∃ cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).homology (n + 1),
      (∀ (y : M) (hy : y ∉ bdry (n := n) (M := M)),
        Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
            (doubleιM (n := n) (M := M) y)
          = (HomologicalComplex.homologyMap (DoubleFC.pairMapιM n M y) (n + 1))
              (locW (n := n) (M := M) w y hy))
      ∧ (∀ (y : M) (hy : y ∉ bdry (n := n) (M := M)),
        Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
            (doubleιN (n := n) (M := M) y)
          = -((HomologicalComplex.homologyMap (DoubleFC.pairMapιN n M y) (n + 1))
              (locW (n := n) (M := M) w y hy)))
      ∧ (HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (Double n M)) (secondHalfG (n := n) (M := M)))) (n + 1) cD
          = HomologicalComplex.homologyMap
              (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
                (bdry (n := n) (M := M)) (secondHalfG (n := n) (M := M))
                (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M))
                (iBdryHom_comp (n := n) (M := M))) (n + 1) w) := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : (Work.Cohomology.relChains (TopCat.of M)
        (bdry (n := n) (M := M))).cycles (n + 1),
      (HomologicalComplex.homologyπ
        (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1)) z = w :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance w
  obtain ⟨x, hx⟩ : ∃ x : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X (n + 1),
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        (bdry (n := n) (M := M)))).f (n + 1)) x
        = (HomologicalComplex.iCycles
            (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1)) z :=
    (ModuleCat.epi_iff_surjective _).mp
      (Work.Cohomology.epi_cokernel_π_f (Work.Cohomology.inclChains (TopCat.of M)
        (bdry (n := n) (M := M))) (n + 1)) _
  have hdx : (Work.Cohomology.singularChains ℤ (TopCat.of M)).d (n + 1) n x
      ∈ LinearMap.range ((Work.Cohomology.inclChains (TopCat.of M)
        (bdry (n := n) (M := M))).f n).hom := by
    refine (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains (TopCat.of M)
      (bdry (n := n) (M := M))) n _).mp ?_
    rw [← pi_bdry_d_apply (n := n) (M := M) n x, hx]
    exact CategoryTheory.ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d
      (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1) n) z
  obtain ⟨b, hb⟩ := hdx
  have hzcyc : (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))).d (n + 1) n
      (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        (bdry (n := n) (M := M)))).f (n + 1)) x) = 0 := by
    rw [hx]
    exact CategoryTheory.ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d
      (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1) n) z
  have hwx : w = (HomologicalComplex.homologyπ
      (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1))
      (Work.Cohomology.cycleOf (n + 1) (((CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of M) (bdry (n := n) (M := M)))).f (n + 1)) x)
        hzcyc) := by
    rw [← hz]
    congr 1
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles
      (Work.Cohomology.relChains (TopCat.of M) (bdry (n := n) (M := M))) (n + 1))).mp inferInstance
    rw [Work.Cohomology.iCycles_cycleOf]
    exact hx.symm
  set cc : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).X (n + 1) :=
    ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
        (DoubleFC.iMHom n M)).f (n + 1)) x
      - ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
        (DoubleFC.iNHom n M)).f (n + 1)) x with hcc_def
  have hcc : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).d (n + 1) n cc = 0 := by
    have hcoM : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).d (n + 1) n
        (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iMHom n M)).f (n + 1)) x)
        = ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iMHom n M)).f n) ((Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M))).f n b) := by
      rw [chainMap_iMHom_d (n := n) (M := M) n x, ← hb]
    have hcoN : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).d (n + 1) n
        (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iNHom n M)).f (n + 1)) x)
        = ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iNHom n M)).f n) ((Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M))).f n b) := by
      rw [chainMap_iNHom_d (n := n) (M := M) n x, ← hb]
    have hmaps : Work.Cohomology.subtypeIncl (TopCat.of M) (bdry (n := n) (M := M)) ≫
        DoubleFC.iMHom n M = Work.Cohomology.subtypeIncl (TopCat.of M)
          (bdry (n := n) (M := M)) ≫ DoubleFC.iNHom n M := by
      ext p
      exact doubleιM_eq_ιN_iff.mpr ⟨p, rfl, rfl⟩
    have hkey : ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iMHom n M)).f n) ((Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M))).f n b)
        = ((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
          (DoubleFC.iNHom n M)).f n) ((Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M))).f n b) := by
      have h2 := congrArg (fun (g : TopCat.of ↥(bdry (n := n) (M := M)) ⟶
          TopCat.of (Double n M)) => Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(bdry (n := n) (M := M))) (TopCat.of (Double n M)) g) hmaps
      rw [Work.Cohomology.chainMap_comp_relChains,
        Work.Cohomology.chainMap_comp_relChains] at h2
      have h3 := congrArg (fun (φ : Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(bdry (n := n) (M := M))) ⟶ Work.Cohomology.singularChains ℤ
          (TopCat.of (Double n M))) => (φ.f n) b) h2
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h3
      rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h3
    rw [hcc_def, map_sub, hcoM, hcoN, hkey, sub_self]
  set cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).homology (n + 1) :=
    (HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M)))
      (n + 1)) (Work.Cohomology.cycleOf (n + 1) cc hcc) with hcD_def
  refine ⟨cD, ?_, ?_, ?_⟩
  · intro y hy
    have hsub : bdry (n := n) (M := M) ⊆ ({z : M | z ≠ y}) := fun z hz hyz => hy (hyz ▸ hz)
    have hξcyc : (Work.Cohomology.relChains (TopCat.of M) ({z : M | z ≠ y})).d (n + 1) n
        (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          ({z : M | z ≠ y}))).f (n + 1)) x) = 0 := by
      rw [pi_y_d_apply y n x, ← hb]
      exact Work.Cohomology.coker_π_inclChains_apply_eq_zero_of_subset hsub n b
    have hb1 : ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Double n M)) (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ))).f
            (n + 1)) cc
        = (DoubleFC.pairMapιM n M y).f (n + 1)
            (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
              ({z : M | z ≠ y}))).f (n + 1)) x) := by
      have h2 : ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Double n M))
            (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ))).f (n + 1))
            (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
              (DoubleFC.iNHom n M)).f (n + 1)) x) = 0 :=
        chainMap_iNHom_killed y hy (n + 1) x
      rw [hcc_def, map_sub, h2, sub_zero]
      have happ := DoubleFC.pairMapιM_apply n M y (n + 1) x
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at happ
      exact happ.symm
    have hleft : Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
        (doubleιM (n := n) (M := M) y)
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ)) (n + 1))
            (HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (Double n M))
                (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ))) (n + 1)
              (Work.Cohomology.cycleOf (n + 1) cc hcc)) := by
      show (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of (Double n M))
          ({v : Double n M | v ≠ doubleιM (n := n) (M := M) y}))) (n + 1)) cD = _
      rw [hcD_def]
      exact Work.Cohomology.homologyMap_homologyπ_cyclesMap _ _ _
    have hright : (HomologicalComplex.homologyMap (DoubleFC.pairMapιM n M y) (n + 1))
          (locW (n := n) (M := M) w y hy)
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ)) (n + 1))
            (HomologicalComplex.cyclesMap (DoubleFC.pairMapιM n M y) (n + 1)
              (HomologicalComplex.cyclesMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
                (bdry (n := n) (M := M)) y hy) (n + 1) z)) := by
      show (HomologicalComplex.homologyMap (DoubleFC.pairMapιM n M y) (n + 1))
          ((HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
            (bdry (n := n) (M := M)) y hy) (n + 1)) w) = _
      rw [← hz]
      exact homologyMap_homologyMap_homologyπ (n + 1)
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy)
        (DoubleFC.pairMapιM n M y) z
    have hcycM : HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of (Double n M))
          (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ))) (n + 1)
        (Work.Cohomology.cycleOf (n + 1) cc hcc)
        = HomologicalComplex.cyclesMap (DoubleFC.pairMapιM n M y) (n + 1)
            (HomologicalComplex.cyclesMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
              (bdry (n := n) (M := M)) y hy) (n + 1) z) :=
      cyclesMap_cycleOf_eq_cyclesMap (n + 1)
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy)
        (DoubleFC.pairMapιM n M y)
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
          (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ)))
        z cc hcc (by
          have h1 : (DoubleFC.pairMapιM n M y).f (n + 1)
                (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                  ({z : M | z ≠ y}))).f (n + 1)) x)
              = (DoubleFC.pairMapιM n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                    (bdry (n := n) (M := M)))).f (n + 1)) x)) :=
            congrArg (fun v => (DoubleFC.pairMapιM n M y).f (n + 1) v)
              (pi_y_apply y hy (n + 1) x)
          have h2 : (DoubleFC.pairMapιM n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                    (bdry (n := n) (M := M)))).f (n + 1)) x))
              = (DoubleFC.pairMapιM n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  ((Work.Cohomology.relChains (TopCat.of M)
                    (bdry (n := n) (M := M))).iCycles (n + 1) z)) :=
            congrArg (fun u => (DoubleFC.pairMapιM n M y).f (n + 1)
              ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                (n + 1) u)) hx
          exact (hb1.trans h1).trans h2)
    rw [hleft, hright, hcycM]
  · intro y hy
    have hsub : bdry (n := n) (M := M) ⊆ ({z : M | z ≠ y}) := fun z hz hyz => hy (hyz ▸ hz)
    have hξcyc : (Work.Cohomology.relChains (TopCat.of M) ({z : M | z ≠ y})).d (n + 1) n
        (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          ({z : M | z ≠ y}))).f (n + 1)) x) = 0 := by
      rw [pi_y_d_apply y n x, ← hb]
      exact Work.Cohomology.coker_π_inclChains_apply_eq_zero_of_subset hsub n b
    have hb1 : ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Double n M)) (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ))).f
            (n + 1)) cc
        = -((DoubleFC.pairMapιN n M y).f (n + 1)
            (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
              ({z : M | z ≠ y}))).f (n + 1)) x)) := by
      have h2 : ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Double n M))
            (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ))).f (n + 1))
            (((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M))
              (DoubleFC.iMHom n M)).f (n + 1)) x) = 0 :=
        chainMap_iMHom_killed y hy (n + 1) x
      rw [hcc_def, map_sub, h2, zero_sub]
      have happ := DoubleFC.pairMapιN_apply n M y (n + 1) x
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at happ
      exact congrArg Neg.neg happ.symm
    have hleft : Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
        (doubleιN (n := n) (M := M) y)
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ)) (n + 1))
            (HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (Double n M))
                (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ))) (n + 1)
              (Work.Cohomology.cycleOf (n + 1) cc hcc)) := by
      show (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of (Double n M))
          ({v : Double n M | v ≠ doubleιN (n := n) (M := M) y}))) (n + 1)) cD = _
      rw [hcD_def]
      exact Work.Cohomology.homologyMap_homologyπ_cyclesMap _ _ _
    have hright : (HomologicalComplex.homologyMap (DoubleFC.pairMapιN n M y) (n + 1))
          (locW (n := n) (M := M) w y hy)
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ)) (n + 1))
            (HomologicalComplex.cyclesMap (DoubleFC.pairMapιN n M y) (n + 1)
              (HomologicalComplex.cyclesMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
                (bdry (n := n) (M := M)) y hy) (n + 1) z)) := by
      show (HomologicalComplex.homologyMap (DoubleFC.pairMapιN n M y) (n + 1))
          ((HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
            (bdry (n := n) (M := M)) y hy) (n + 1)) w) = _
      rw [← hz]
      exact homologyMap_homologyMap_homologyπ (n + 1)
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy)
        (DoubleFC.pairMapιN n M y) z
    have hcyc : HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of (Double n M))
          (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ))) (n + 1)
        (Work.Cohomology.cycleOf (n + 1) cc hcc)
        = -(HomologicalComplex.cyclesMap (DoubleFC.pairMapιN n M y) (n + 1)
            (HomologicalComplex.cyclesMap (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
              (bdry (n := n) (M := M)) y hy) (n + 1) z)) :=
      cyclesMap_cycleOf_eq_neg_cyclesMap (n + 1)
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy)
        (DoubleFC.pairMapιN n M y)
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
          (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ)))
        z cc hcc (by
          have h1 : -((DoubleFC.pairMapιN n M y).f (n + 1)
                (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                  ({z : M | z ≠ y}))).f (n + 1)) x))
              = -((DoubleFC.pairMapιN n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                    (bdry (n := n) (M := M)))).f (n + 1)) x))) :=
            congrArg (fun v => -((DoubleFC.pairMapιN n M y).f (n + 1) v))
              (pi_y_apply y hy (n + 1) x)
          have h2 : -((DoubleFC.pairMapιN n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                    (bdry (n := n) (M := M)))).f (n + 1)) x)))
              = -((DoubleFC.pairMapιN n M y).f (n + 1)
                ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                  (n + 1)
                  ((Work.Cohomology.relChains (TopCat.of M)
                    (bdry (n := n) (M := M))).iCycles (n + 1) z))) :=
            congrArg (fun u => -((DoubleFC.pairMapιN n M y).f (n + 1)
              ((Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry (n := n) (M := M)) y hy).f
                (n + 1) u))) hx
          exact (hb1.trans h1).trans h2)
    rw [hleft, hright, hcyc, map_neg]

  · -- the relative class of `cD` in `H_{n+1}(D, B)` is the image of the class of `w`
    have hkey : (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Double n M)) (secondHalfG (n := n) (M := M)))).f (n + 1) cc
        = (inclRelMapG (n := n) (M := M)).f (n + 1)
            (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
              (bdry (n := n) (M := M)))).f (n + 1)) x) := by
      rw [hcc_def, map_sub,
        chainMap_iNHom_killed_secondHalf (n := n) (M := M) (n + 1) x, sub_zero]
      exact (keyElement (n := n) (M := M) x).symm
    have hcycEq : HomologicalComplex.cyclesMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
            (secondHalfG (n := n) (M := M)))) (n + 1) (Work.Cohomology.cycleOf (n + 1) cc hcc)
        = HomologicalComplex.cyclesMap
          (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
            (bdry (n := n) (M := M)) (secondHalfG (n := n) (M := M))
            (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M))
            (iBdryHom_comp (n := n) (M := M))) (n + 1)
          (Work.Cohomology.cycleOf (n + 1)
            (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
              (bdry (n := n) (M := M)))).f (n + 1)) x) hzcyc) :=
      cyclesMap_cycleOf_eq_cyclesMap_chain (n + 1) (inclRelMapG (n := n) (M := M))
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Double n M)) (secondHalfG (n := n) (M := M))))
        (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
          (bdry (n := n) (M := M)))).f (n + 1)) x) hzcyc cc hcc hkey
    have h1 : HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
            (secondHalfG (n := n) (M := M)))) (n + 1) cD
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (secondHalfG (n := n) (M := M))) (n + 1))
            (HomologicalComplex.cyclesMap
              (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
                (TopCat.of (Double n M)) (secondHalfG (n := n) (M := M)))) (n + 1)
              (Work.Cohomology.cycleOf (n + 1) cc hcc)) := by
      rw [hcD_def]
      exact Work.Cohomology.homologyMap_homologyπ_cyclesMap _ _ _
    have h2 : HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
            (bdry (n := n) (M := M)) (secondHalfG (n := n) (M := M))
            (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M))
            (iBdryHom_comp (n := n) (M := M))) (n + 1) w
        = (HomologicalComplex.homologyπ (Work.Cohomology.relChains (TopCat.of (Double n M))
            (secondHalfG (n := n) (M := M))) (n + 1))
            (HomologicalComplex.cyclesMap
              (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
                (bdry (n := n) (M := M)) (secondHalfG (n := n) (M := M))
                (DoubleFC.iMHom n M) (iBdryHom (n := n) (M := M))
                (iBdryHom_comp (n := n) (M := M))) (n + 1)
              (Work.Cohomology.cycleOf (n + 1)
                (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
                  (bdry (n := n) (M := M)))).f (n + 1)) x) hzcyc)) := by
      rw [hwx]
      exact Work.Cohomology.homologyMap_homologyπ_cyclesMap _ _ _
    rw [h1, h2, hcycEq]



end

end Work.ThomBordism.RelDoubleClass

namespace Work.ThomBordism.RelDuality

noncomputable section

/-! ## The fundamental class of the double -/

theorem doubleFundClass {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Work.ThomBordism.Double 8 M)]
    [T2Space (Work.ThomBordism.Double 8 M)] [CompactSpace (Work.ThomBordism.Double 8 M)]
    (w : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology 9)
    (hw : ∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M) x hx) 9 w)} = ⊤) :
    ∃ c : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.ThomBordism.Double 8 M))).homology 9,
      (∀ x : Work.ThomBordism.Double 8 M, Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsProj (TopCat.of (Work.ThomBordism.Double 8 M)) {y | y ≠ x}) 9 c)} = ⊤) ∧
      (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        HomologicalComplex.homologyMap (Work.ThomBordism.projSecondHalf (M := M)) 9 c =
          ε • HomologicalComplex.homologyMap (Work.ThomBordism.inclRelMap (M := M)) 9 w) := by
  classical
  obtain ⟨cD, hM, hN, hrel⟩ := RelDoubleClass.relDoubleClass_exists (n := 8) (M := M) w
  have hgenM : ∀ (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt
        (TopCat.of (Work.ThomBordism.Double 8 M)) 9 cD
        (Work.ThomBordism.doubleιM (n := 8) (M := M) y))} = ⊤ := by
    intro y hy
    rw [hM y hy]
    exact doubleFC.span_pairMap_M 8 M y hy
      (RelDoubleClass.locW (n := 8) (M := M) w y hy) (hw y hy)
  have hgenN : ∀ (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt
        (TopCat.of (Work.ThomBordism.Double 8 M)) 9 cD
        (Work.ThomBordism.doubleιN (n := 8) (M := M) y))} = ⊤ := by
    intro y hy
    have h := doubleFC.span_pairMap_N 8 M y hy
      (RelDoubleClass.locW (n := 8) (M := M) w y hy) (hw y hy)
    set v := (HomologicalComplex.homologyMap (DoubleFC.pairMapιN 8 M y) 9)
      (RelDoubleClass.locW (n := 8) (M := M) w y hy) with hv
    have hneg : Submodule.span ℤ ({(-v)} : Set _) = ⊤ := by
      rw [show ({(-v)} : Set _) = -({v} : Set _) from (Set.neg_singleton v).symm,
        Submodule.span_neg]
      exact h
    rw [hN y hy, ← hv]
    exact hneg
  refine ⟨cD, ?_, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    rcases a with m | m
    · by_cases hb : m ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
      · exact DoubleFC.span_localClassAt_seam 8 M cD hgenM ⟨m, hb⟩
      · exact hgenM m hb
    · by_cases hb : m ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
      · exact DoubleFC.span_localClassAt_seamN 8 M cD hgenM ⟨m, hb⟩
      · exact hgenN m hb
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul]
    exact hrel


end

end Work.ThomBordism.RelDuality
