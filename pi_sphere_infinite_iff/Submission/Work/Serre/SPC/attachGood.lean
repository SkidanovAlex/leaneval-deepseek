import Mathlib
import Submission.Work.Serre.SPC.Setup
import Submission.Work.Serre.SPC.attachGeom
import Submission.Work.Serre.SPC.tauTwoRange
import Submission.Work.Serre.SPC.attachFibreData
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Serre.cellStepDefs
import Submission.Work.Serre.Assembly.pullbackFst_serre

set_option synthInstance.maxHeartbeats 400000


/-!
# The cell-attachment step of the tower comparison

One step of the induction in the proof of `Work.Serre.SPC.towerComparison`: for a map
`g : Γ → B` extended over an attachment of cells (`g' : attachCells n Γ ι fr → B`), the comparison
map of the pullback of `p` along `g'` is an isomorphism in the stable range as soon as the
comparison map for `g` is.  The proof uses the triple exact sequences of `(P, q⁻¹{γ₀'}, q⁻¹Γ)` and
`(Γ', {γ₀'}, Γ)`, the cell step `hcell` (which controls the third terms) and the transport of the
fibre homology `htr` (which supplies the connectivity of the fibres of the pullback).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Serre.SPC

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

/-! ## Two general lemmas on `cokernel.map` -/

/-- **Composition of `cokernel.map`s.** -/
theorem cokernel_map_comp {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B A' B' A'' B'' : C} (f : A ⟶ B) [HasCokernel f] (f' : A' ⟶ B') [HasCokernel f']
    (f'' : A'' ⟶ B'') [HasCokernel f''] (p₁ : A ⟶ A') (q₁ : B ⟶ B') (w₁ : f ≫ q₁ = p₁ ≫ f')
    (p₂ : A' ⟶ A'') (q₂ : B' ⟶ B'') (w₂ : f' ≫ q₂ = p₂ ≫ f'')
    (w : f ≫ (q₁ ≫ q₂) = (p₁ ≫ p₂) ≫ f'') :
    cokernel.map f f' p₁ q₁ w₁ ≫ cokernel.map f' f'' p₂ q₂ w₂
      = cokernel.map f f'' (p₁ ≫ p₂) (q₁ ≫ q₂) w := by
  rw [← cancel_epi (cokernel.π f)]
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.cokernel_π_map, Work.Cohomology.cokernel_π_map, Category.assoc]

/-- **`cokernel.map` depends on the commuting square only through its `p`- and `q`-components.** -/
theorem cokernel_map_eq {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B A' B' : C} (f : A ⟶ B) [HasCokernel f] (f' : A' ⟶ B') [HasCokernel f']
    {p p' : A ⟶ A'} (hp : p = p') {q q' : B ⟶ B'} (hq : q = q')
    (w : f ≫ q = p ≫ f') (w' : f ≫ q' = p' ≫ f') :
    cokernel.map f f' p q w = cokernel.map f f' p' q' w' := by
  subst hp; subst hq; rfl

/-! ## The invariant of the tower induction -/

/-- **The invariant of the tower induction.**  The comparison map of the pullback of `p` along
`g` with the fibre over `γ₀` is an isomorphism in degrees `< b + f` and an epimorphism in degree
`b + f`. -/
def GoodMap (p : C(E, B)) (b f : ℕ) (g : C(Γ, B)) (γ₀ : Γ) : Prop :=
  (∀ i : ℕ, i < b + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.CWModel.stagePairMap g p γ₀) i)) ∧
    Epi (HomologicalComplex.homologyMap (Work.Serre.CWModel.stagePairMap g p γ₀) (b + f))

/-! ## The geometry of one cell attachment -/

/-- The old part of `attachCells n Γ ι fr`, as a set: the image of the attaching map. -/
abbrev oldPart (n : ℕ) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) :
    Set (Work.RatHurewicz.attachCells n Γ ι fr) :=
  Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y

/-- The new base point of `attachCells n Γ ι fr`, as a set. -/
abbrev bptSet (n : ℕ) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (γ₀ : Γ) :
    Set (Work.RatHurewicz.attachCells n Γ ι fr) :=
  {Work.RatHurewicz.attachIncl n Γ ι fr γ₀}

/-- The new base point lies in the old part. -/
theorem bpt_mem_oldPart (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (γ₀ : Γ) :
    Work.RatHurewicz.attachIncl n Γ ι fr γ₀ ∈ oldPart n ι fr :=
  Set.mem_range_self γ₀

/-- The base point set is contained in the old part. -/
theorem bptSet_subset_oldPart (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (γ₀ : Γ) :
    bptSet n ι fr γ₀ ⊆ oldPart n ι fr := by
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  exact Set.mem_range_self γ₀

/-- The fibre over the new base point, inside the pullback. -/
abbrev fibSet (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    Set (Work.StemsB.Pullback g' p) :=
  (Work.StemsB.pullbackFst g' p) ⁻¹' ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
    (Work.RatHurewicz.attachCells n Γ ι fr))

/-- The preimage of the old part, inside the pullback. -/
abbrev oldSetX (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) :
    Set (Work.StemsB.Pullback g' p) :=
  (Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)

/-- The fibre over the new base point is contained in the preimage of the old part. -/
theorem fibSet_subset_oldSetX (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    fibSet p n ι fr g' γ₀ ⊆ oldSetX p n ι fr g' :=
  Set.preimage_mono (bptSet_subset_oldPart n ι fr γ₀)

/-- The map from the new fibre to the new base point. -/
def toNewBase (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    C(↥(fibSet p n ι fr g' γ₀), ↥(bptSet n ι fr γ₀)) where
  toFun x := ⟨(Work.StemsB.pullbackFst g' p) x.val,
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2)⟩
  continuous_toFun := by fun_prop

/-- The map from the preimage of the old part to the old part. -/
def toOldPart (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) :
    C(↥(oldSetX p n ι fr g'), ↥(oldPart n ι fr)) where
  toFun x := ⟨(Work.StemsB.pullbackFst g' p) x.val, x.2⟩
  continuous_toFun := by fun_prop

/-- The compatibility of the two maps on the fibre. -/
theorem tauOneMap_w (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
        (fibSet_subset_oldSetX p n ι fr g' γ₀)
      ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(oldSetX p n ι fr g'))
          (TopCat.of ↥(oldPart n ι fr)) (TopCat.ofHom (toOldPart p n ι fr g'))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(fibSet p n ι fr g' γ₀))
          (TopCat.of ↥(bptSet n ι fr γ₀))
          (TopCat.ofHom (toNewBase p n ι fr g' γ₀))
        ≫ Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀) := by
  simp only [Work.Cohomology.inclChainsSub, Work.Cohomology.chainMap, ← Functor.map_comp]
  congr 1

/-- **The map on the first terms of the triple sequences.** -/
def tauOneMap (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
          (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
          (fibSet_subset_oldSetX p n ι fr g' γ₀))
      ⟶ CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)) :=
  cokernel.map (f := Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
      (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
      (fibSet_subset_oldSetX p n ι fr g' γ₀))
    (f' := Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
      (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀))
    (Work.Cohomology.chainMap ℤ (TopCat.of ↥(fibSet p n ι fr g' γ₀))
      (TopCat.of ↥(bptSet n ι fr γ₀)) (TopCat.ofHom (toNewBase p n ι fr g' γ₀)))
    (Work.Cohomology.chainMap ℤ (TopCat.of ↥(oldSetX p n ι fr g'))
      (TopCat.of ↥(oldPart n ι fr)) (TopCat.ofHom (toOldPart p n ι fr g')))
    (tauOneMap_w p n ι fr g' γ₀)

/-- The projective description of `tauOneMap`. -/
theorem tauOneMap_π (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    cokernel.π (Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
        (fibSet_subset_oldSetX p n ι fr g' γ₀))
      ≫ tauOneMap p n ι fr g' γ₀
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(oldSetX p n ι fr g'))
          (TopCat.of ↥(oldPart n ι fr)) (TopCat.ofHom (toOldPart p n ι fr g'))
        ≫ cokernel.π (Work.Cohomology.inclChainsSub
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)) := by
  rw [tauOneMap]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-! ## The naturality of `cokernel.π` with respect to the three comparison maps -/

/-- The projective description of the fibre comparison map. -/
theorem stagePairMap_π (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀))
      ≫ Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀)
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
          (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr)) (bptSet n ι fr γ₀)) := by
  rw [Work.Serre.CWModel.stagePairMap]
  exact Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _
    (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
    (TopCat.ofHom (toNewBase p n ι fr g' γ₀)) _

/-- The projective description of the cell step map. -/
theorem cellStepMap_π (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
        (oldSetX p n ι fr g'))
      ≫ Work.Serre.cellStepAttachMap (n + 2) Γ ι fr (Work.StemsB.Pullback g' p)
          (Work.StemsB.pullbackFst g' p)
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
          (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr)) (oldPart n ι fr)) := by
  rw [Work.Serre.cellStepAttachMap]
  exact Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _
    (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
    (TopCat.ofHom (Work.Serre.cellStepMapRel (n + 2) Γ ι fr (Work.StemsB.Pullback g' p)
      (Work.StemsB.pullbackFst g' p))) _

/-- The projective description of the first map of the target triple sequence. -/
theorem tripleShort_f_π (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    cokernel.π (Work.Cohomology.inclChainsSub X A B hAB)
      ≫ (Work.Cohomology.tripleShort X A B hAB).f
      = Work.Cohomology.inclChains X B ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
  rw [Work.Cohomology.tripleShort_f]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The projective description of the second map of the target triple sequence. -/
theorem tripleShort_g_π (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    cokernel.π (Work.Cohomology.inclChains X A)
      ≫ (Work.Cohomology.tripleShort X A B hAB).g
      = cokernel.π (Work.Cohomology.inclChains X B) := by
  rw [Work.Cohomology.tripleShort_g]
  exact Work.Cohomology.relCokerMap_comp_π X A B hAB

/-- **Identification of the first term of the source triple sequence with the old stage's relative
chain complex.** -/
noncomputable def sourceIso (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))
      ≅ CategoryTheory.Limits.cokernel (Work.Cohomology.inclChainsSub
          (TopCat.of (Work.StemsB.Pullback g' p))
          ((Work.StemsB.pullbackFst g' p) ⁻¹'
            ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells n Γ ι fr)))
          ((Work.StemsB.pullbackFst g' p) ⁻¹'
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
          (fibSet_subset_oldSetX p n ι fr g' γ₀)) := by
  let F := (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hsq : Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))
      ≫ (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg'))).hom
      = (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeoA p g n ι fr g' hg' γ₀))).hom
        ≫ Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
            ((Work.StemsB.pullbackFst g' p) ⁻¹'
              ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                (Work.RatHurewicz.attachCells n Γ ι fr)))
            ((Work.StemsB.pullbackFst g' p) ⁻¹'
              (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
            (fibSet_subset_oldSetX p n ι fr g' γ₀) := by
    rw [show Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p))
          ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))
        = Work.Cohomology.chainMap ℤ (TopCat.of ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
            (TopCat.of (Work.StemsB.Pullback g p))
            (Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
              ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))) from rfl,
      show Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
          ((Work.StemsB.pullbackFst g' p) ⁻¹'
            ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set (Work.RatHurewicz.attachCells n Γ ι fr)))
          ((Work.StemsB.pullbackFst g' p) ⁻¹'
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
          (fibSet_subset_oldSetX p n ι fr g' γ₀)
        = Work.Cohomology.chainMap ℤ
            (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
              ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                (Work.RatHurewicz.attachCells n Γ ι fr))))
            (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
              (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
            (TopCat.ofHom ⟨fun x => ⟨x.1, ⟨γ₀, by
                rw [show (Work.StemsB.pullbackFst g' p) x = _ from
                  Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2)]⟩⟩,
              Continuous.subtype_mk (f := fun x : ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
                  ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                    (Work.RatHurewicz.attachCells n Γ ι fr))) => (x : Work.StemsB.Pullback g' p))
                continuous_subtype_val _⟩) from rfl,
      show (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg'))).hom
        = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p))
            (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
              (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
            (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg')).hom from rfl,
      show (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeoA p g n ι fr g' hg' γ₀))).hom
        = Work.Cohomology.chainMap ℤ
            (TopCat.of ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
            (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
              ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                (Work.RatHurewicz.attachCells n Γ ι fr))))
            (TopCat.isoOfHomeo (pullbackOldHomeoA p g n ι fr g' hg' γ₀)).hom from rfl]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact cokernel.mapIso (f := Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p))
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
    (f' := Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
      ((Work.StemsB.pullbackFst g' p) ⁻¹'
        ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set (Work.RatHurewicz.attachCells n Γ ι fr)))
      ((Work.StemsB.pullbackFst g' p) ⁻¹'
        (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
      (fibSet_subset_oldSetX p n ι fr g' γ₀))
    (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeoA p g n ι fr g' hg' γ₀)))
    (F.mapIso (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg'))) hsq

/-- **Identification of the first term of the target triple sequence with the old base pair.** -/
noncomputable def targetIso (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    Work.Cohomology.relChains (TopCat.of Γ) ({γ₀} : Set Γ)
      ≅ CategoryTheory.Limits.cokernel (Work.Cohomology.inclChainsSub
          (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
            (Work.RatHurewicz.attachCells n Γ ι fr))
          (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)
          (bptSet_subset_oldPart n ι fr γ₀)) := by
  let F := (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hsq : Work.Cohomology.inclChains (TopCat.of Γ) ({γ₀} : Set Γ)
      ≫ (F.mapIso (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr))).hom
      = (F.mapIso (TopCat.isoOfHomeo (basePointHomeo (Γ := Γ) n ι fr γ₀))).hom
        ≫ Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells n Γ ι fr))
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)
            (bptSet_subset_oldPart n ι fr γ₀) := by
    rw [show Work.Cohomology.inclChains (TopCat.of Γ) ({γ₀} : Set Γ)
        = Work.Cohomology.chainMap ℤ (TopCat.of ↥({γ₀} : Set Γ)) (TopCat.of Γ)
            (Work.Cohomology.subtypeIncl (TopCat.of Γ) ({γ₀} : Set Γ)) from rfl,
      show Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
            (Work.RatHurewicz.attachCells n Γ ι fr))
          (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)
          (bptSet_subset_oldPart n ι fr γ₀)
        = Work.Cohomology.chainMap ℤ
            (TopCat.of ↥({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells n Γ ι fr)))
            (TopCat.of ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
            (TopCat.ofHom ⟨fun x => ⟨x.1, ⟨γ₀, by rw [x.2]⟩⟩,
              Continuous.subtype_mk (f := fun x : ↥({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                (Work.RatHurewicz.attachCells n Γ ι fr)) => (x : Work.RatHurewicz.attachCells n Γ ι fr))
                continuous_subtype_val _⟩) from rfl,
      show (F.mapIso (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr))).hom
        = Work.Cohomology.chainMap ℤ (TopCat.of Γ)
            (TopCat.of ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
            (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr)).hom from rfl,
      show (F.mapIso (TopCat.isoOfHomeo (basePointHomeo (Γ := Γ) n ι fr γ₀))).hom
        = Work.Cohomology.chainMap ℤ (TopCat.of ↥({γ₀} : Set Γ))
            (TopCat.of ↥({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells n Γ ι fr)))
            (TopCat.isoOfHomeo (basePointHomeo (Γ := Γ) n ι fr γ₀)).hom from rfl]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext x
    show (attachRangeHomeo (Γ := Γ) n ι fr (Subtype.val x) :
        Work.RatHurewicz.attachCells n Γ ι fr)
      = ((⟨Work.RatHurewicz.attachIncl n Γ ι fr γ₀, ⟨γ₀, rfl⟩⟩ : ↥(Set.range fun y : Γ =>
          Work.RatHurewicz.attachIncl n Γ ι fr y)) : Work.RatHurewicz.attachCells n Γ ι fr)
    rw [attachRangeHomeo_apply_val, Set.mem_singleton_iff.mp x.2]
  exact cokernel.mapIso (f := Work.Cohomology.inclChains (TopCat.of Γ) ({γ₀} : Set Γ))
    (f' := Work.Cohomology.inclChainsSub (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
      ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set (Work.RatHurewicz.attachCells n Γ ι fr))
      (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)
      (bptSet_subset_oldPart n ι fr γ₀))
    (F.mapIso (TopCat.isoOfHomeo (basePointHomeo (Γ := Γ) n ι fr γ₀)))
    (F.mapIso (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr))) hsq

/-! ## The old-stage comparison and the two isomorphisms, projectively -/

/-- The projective description of the old-stage comparison map. -/
theorem stagePairMap_old_π (p : C(E, B)) (g : C(Γ, B)) (γ₀ : Γ) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
      ≫ Work.Serre.CWModel.stagePairMap g p γ₀
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of Γ)
          (TopCat.ofHom (Work.StemsB.pullbackFst g p))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of Γ) ({γ₀} : Set Γ)) := by
  rw [Work.Serre.SPC.stagePairMap_eq_relPairMap, Work.StemsB.relPairMap]
  exact Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _
    (TopCat.ofHom (Work.StemsB.pullbackFst g p))
    (Work.StemsB.fibreMap (Work.StemsB.pullbackFst g p) γ₀) _

/-- The projective description of `sourceIso`. -/
theorem sourceIso_π (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
      ≫ (sourceIso p g n ι fr g' hg' γ₀).hom
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p))
          (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
          (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg')).hom
        ≫ cokernel.π (Work.Cohomology.inclChainsSub (TopCat.of (Work.StemsB.Pullback g' p))
            ((Work.StemsB.pullbackFst g' p) ⁻¹'
              ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
                (Work.RatHurewicz.attachCells n Γ ι fr)))
            ((Work.StemsB.pullbackFst g' p) ⁻¹'
              (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
            (fibSet_subset_oldSetX p n ι fr g' γ₀)) := by
  rw [sourceIso]
  simp only [cokernel.mapIso_hom]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The projective description of `targetIso`. -/
theorem targetIso_π (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    cokernel.π (Work.Cohomology.inclChains (TopCat.of Γ) ({γ₀} : Set Γ))
      ≫ (targetIso p g n ι fr g' hg' γ₀).hom
      = Work.Cohomology.chainMap ℤ (TopCat.of Γ)
          (TopCat.of ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
          (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr)).hom
        ≫ cokernel.π (Work.Cohomology.inclChainsSub
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells n Γ ι fr))
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)
            (bptSet_subset_oldPart n ι fr γ₀)) := by
  rw [targetIso]
  simp only [cokernel.mapIso_hom]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **The compatibility of the first term of the two triple sequences with the old stage.** -/
theorem sq1 (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    (sourceIso p g n ι fr g' hg' γ₀).hom ≫ tauOneMap p n ι fr g' γ₀
      = Work.Serre.CWModel.stagePairMap g p γ₀ ≫ (targetIso p g n ι fr g' hg' γ₀).hom := by
  have hkey : Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p))
        (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
          (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
        (TopCat.isoOfHomeo (pullbackOldHomeo p g n ι fr g' hg')).hom
      ≫ Work.Cohomology.chainMap ℤ
          (TopCat.of ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
            (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
          (TopCat.of ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
          (TopCat.ofHom (toOldPart p n ι fr g'))
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of Γ)
            (TopCat.ofHom (Work.StemsB.pullbackFst g p))
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of Γ)
              (TopCat.of ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))
              (TopCat.isoOfHomeo (attachRangeHomeo (Γ := Γ) n ι fr)).hom := by
    rw [← Work.Cohomology.chainMap_comp_relChains, ← Work.Cohomology.chainMap_comp_relChains]
    congr 1
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of (Work.StemsB.Pullback g p)) ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))))).mp
  rw [← Category.assoc, sourceIso_π, Category.assoc, tauOneMap_π, ← Category.assoc, hkey,
    ← Category.assoc, stagePairMap_old_π, Category.assoc, Category.assoc, targetIso_π]

/-! ## The pullback square of the two projection maps -/

/-- **The chain-level identity of the two projections.**  The composite `q ∘ (inclusion of the old
part) : q⁻¹Γ → Γ'` is the inclusion of `Γ` composed with `q`. -/
theorem oldPart_chain_eq (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) :
    Work.Cohomology.chainMap ℤ (TopCat.of ↥(oldSetX p n ι fr g')) (TopCat.of ↥(oldPart n ι fr))
        (TopCat.ofHom (toOldPart p n ι fr g'))
      ≫ Work.Cohomology.inclChains (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (oldPart n ι fr)
      = Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
          (oldSetX p n ι fr g')
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            (TopCat.ofHom (Work.StemsB.pullbackFst g' p)) := by
  rw [Work.Cohomology.inclChains, Work.Cohomology.inclChains, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1

/-! ## The two commutation squares of the comparison -/

/-- **Commutativity of the first square** of the morphism of triple sequences. -/
theorem comm12 (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    tauOneMap p n ι fr g' γ₀
      ≫ (Work.Cohomology.tripleShort (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)).f
      = (Work.Cohomology.tripleShort (TopCat.of (Work.StemsB.Pullback g' p))
          (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
          (fibSet_subset_oldSetX p n ι fr g' γ₀)).f
        ≫ Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChainsSub
    (TopCat.of (Work.StemsB.Pullback g' p)) (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
    (fibSet_subset_oldSetX p n ι fr g' γ₀)))).mp
  have hL : cokernel.π (Work.Cohomology.inclChainsSub
        (TopCat.of (Work.StemsB.Pullback g' p)) (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
        (fibSet_subset_oldSetX p n ι fr g' γ₀))
      ≫ (tauOneMap p n ι fr g' γ₀
        ≫ (Work.Cohomology.tripleShort (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)).f)
      = Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
            (oldSetX p n ι fr g')
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
              (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
              (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
          ≫ cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
              (bptSet n ι fr γ₀)) := by
    rw [← Category.assoc, tauOneMap_π, Category.assoc, tripleShort_f_π, ← Category.assoc,
      oldPart_chain_eq, Category.assoc]
  have hR : cokernel.π (Work.Cohomology.inclChainsSub
        (TopCat.of (Work.StemsB.Pullback g' p)) (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
        (fibSet_subset_oldSetX p n ι fr g' γ₀))
      ≫ ((Work.Cohomology.tripleShort (TopCat.of (Work.StemsB.Pullback g' p))
            (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
            (fibSet_subset_oldSetX p n ι fr g' γ₀)).f
        ≫ Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀))
      = Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
            (oldSetX p n ι fr g')
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
              (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
              (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
          ≫ cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
              (bptSet n ι fr γ₀)) := by
    rw [← Category.assoc, tripleShort_f_π, Category.assoc, stagePairMap_π]
  rw [hL, hR]

/-- **Commutativity of the second square** of the morphism of triple sequences. -/
theorem comm23 (p : C(E, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B)) (γ₀ : Γ) :
    Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀)
      ≫ (Work.Cohomology.tripleShort (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)).g
      = (Work.Cohomology.tripleShort (TopCat.of (Work.StemsB.Pullback g' p))
          (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
          (fibSet_subset_oldSetX p n ι fr g' γ₀)).g
        ≫ Work.Serre.cellStepAttachMap (n + 2) Γ ι fr (Work.StemsB.Pullback g' p)
            (Work.StemsB.pullbackFst g' p) := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of (Work.StemsB.Pullback g' p)) (fibSet p n ι fr g' γ₀)))).mp
  have hL : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀))
      ≫ (Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀)
        ≫ (Work.Cohomology.tripleShort (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
            (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀)).g)
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
          (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr)) (oldPart n ι fr)) := by
    rw [← Category.assoc, stagePairMap_π, Category.assoc, tripleShort_g_π]
  have hR : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀))
      ≫ ((Work.Cohomology.tripleShort (TopCat.of (Work.StemsB.Pullback g' p))
            (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
            (fibSet_subset_oldSetX p n ι fr g' γ₀)).g
        ≫ Work.Serre.cellStepAttachMap (n + 2) Γ ι fr (Work.StemsB.Pullback g' p)
            (Work.StemsB.pullbackFst g' p))
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g' p))
          (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
          (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
        ≫ cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr)) (oldPart n ι fr)) := by
    rw [← Category.assoc, tripleShort_g_π, cellStepMap_π]
  rw [hL, hR]



/-- **The morphism of triple sequences of one cell attachment.** -/
noncomputable def stageMorphism (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    Work.Cohomology.tripleShort (TopCat.of (Work.StemsB.Pullback g' p))
        (fibSet p n ι fr g' γ₀) (oldSetX p n ι fr g')
        (fibSet_subset_oldSetX p n ι fr g' γ₀)
      ⟶ Work.Cohomology.tripleShort (TopCat.of (Work.RatHurewicz.attachCells n Γ ι fr))
        (bptSet n ι fr γ₀) (oldPart n ι fr) (bptSet_subset_oldPart n ι fr γ₀) :=
  ShortComplex.homMk (tauOneMap p n ι fr g' γ₀)
    (Work.Serre.CWModel.stagePairMap g' p (Work.RatHurewicz.attachIncl n Γ ι fr γ₀))
    (Work.Serre.cellStepAttachMap (n + 2) Γ ι fr (Work.StemsB.Pullback g' p)
      (Work.StemsB.pullbackFst g' p))
    (comm12 p n ι fr g' γ₀) (comm23 p n ι fr g' γ₀)

/-- **The cell-attachment step of the tower induction.** -/
theorem attachGood
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (f : ℕ) (hcell : CellStepHyp) (htr : FibreTransport)
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (b : ℕ) (hb : 2 ≤ b) (g : C(Γ, B)) (γ₀ : Γ) (gbase : g γ₀ = b₀) [PathConnectedSpace Γ]
    (n : ℕ) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x)
    (hbn : b ≤ n + 2) (hgood : GoodMap p b f g γ₀) :
    GoodMap p b f g' (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) := by
  classical
  haveI hpc : PathConnectedSpace (Work.RatHurewicz.attachCells n Γ ι fr) :=
    Work.Serre.CWModel.pathConnectedSpace_attachCells n Γ ι fr
  have hserre := Work.Serre.Assembly.pullbackFst_serre g' p hp
  obtain ⟨hfiber, h0⟩ := attachFibreData p hp b₀ e₀ he₀ f htr hfib hfib0
    (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) g' ((hg' γ₀).trans gbase)
  have hcs := hcell (n + 2) (by omega) Γ ι fr (Work.StemsB.Pullback g' p)
    (Work.StemsB.pullbackFst g' p) hserre f hfiber h0
  have hτeq : tauOneMap p n ι fr g' γ₀
      = (sourceIso p g n ι fr g' hg' γ₀).inv ≫ Work.Serre.CWModel.stagePairMap g p γ₀
        ≫ (targetIso p g n ι fr g' hg' γ₀).hom := by
    rw [← sq1 p g n ι fr g' hg' γ₀, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h₁ : ∀ i : ℕ, i < b + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (tauOneMap p n ι fr g' γ₀) i) := by
    intro i hi
    rw [hτeq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI := hgood.1 i hi
    infer_instance
  have h₁N : Epi (HomologicalComplex.homologyMap (tauOneMap p n ι fr g' γ₀) (b + f)) := by
    rw [hτeq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI := hgood.2
    infer_instance
  have h₃ : ∀ i : ℕ, i < b + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.cellStepAttachMap (n + 2) Γ ι fr
        (Work.StemsB.Pullback g' p) (Work.StemsB.pullbackFst g' p)) i) :=
    fun i hi => hcs.1 i (by omega)
  have h₃N : Epi (HomologicalComplex.homologyMap (Work.Serre.cellStepAttachMap (n + 2) Γ ι fr
      (Work.StemsB.Pullback g' p) (Work.StemsB.pullbackFst g' p)) (b + f)) := by
    rcases lt_or_eq_of_le (show b + f ≤ (n + 2) + f by omega) with h | h
    · haveI := hcs.1 (b + f) h
      infer_instance
    · rw [h]
      exact (ModuleCat.epi_iff_surjective _).mpr (by simpa using hcs.2)
  have hkey := tauTwoRange (stageMorphism p g n ι fr g' hg' γ₀)
    (Work.Cohomology.relChains_triple_shortExact _ _ _ _)
    (Work.Cohomology.relChains_triple_shortExact _ _ _ _)
    (b + f) (by omega) h₁ h₃ h₁N h₃N
  exact ⟨hkey.1, hkey.2⟩


/-- `GoodMap` for a model stage follows from `Good`. -/
theorem goodMap_of_good (p : C(E, B)) (b f : ℕ) {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) (h : Good p b f s) :
    GoodMap p b f s.g s.y₀ where
  left := h.1
  right := (ModuleCat.epi_iff_surjective _).mpr (by simpa using h.2)

end

end Work.Serre.SPC
