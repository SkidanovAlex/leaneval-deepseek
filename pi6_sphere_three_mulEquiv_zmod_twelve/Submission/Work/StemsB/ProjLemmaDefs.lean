import Submission.Work.StemsB.CollarModel
import Submission.Work.StemsB.SerreSphereStep
import Submission.Work.StemsB.SurjIntIso
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The projection lemma of the Serre exact sequence over a sphere

The mathematical core of the pentagon (`Submission/Work/StemsB/SERRE_PLAN.md` §6): the projection

  `↥(sphLoopBig n) × Y ⟶ ↥(sphLoopBig n) × PUnit,  (q, y) ↦ (q, ())`

induces an isomorphism on *relative* homology in degrees `k < n + f`, where `f` is the vanishing
range of the homology of the fibre `Y` (`H_j(Y) = 0` for `0 < j < f`) and `H_0(Y) ≅ ℤ`.

The proof computes both sides with the collar Künneth (`serreSphere_collar_iso`,
`serreSphere_collar_isZero`, proved in `CollarModel.lean`):

* `k < n`: both sides vanish;
* `n < k < n+f`: the source vanishes by the hypothesis on `Y`, the target because `H_j(pt) = 0` for
  `j > 0`;
* `k = n`: both sides are `ℤ` (`H_0(Y) ≅ ℤ` by hypothesis, `H_0(pt) ≅ ℤ` since a point is path
  connected), and the map is a **split epimorphism** — the section `q ↦ (q, y₀)` satisfies
  `sec ≫ proj = 𝟙` — so it is an isomorphism by the elementary algebra lemma
  `bijective_of_surjective_of_int_iso`.

No naturality of the collar Künneth is used.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 64000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

/-- **A morphism between two zero objects is an isomorphism.** -/
theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C}
    {f : A ⟶ B} (hA : IsZero A) (hB : IsZero B) : IsIso f := by
  have h1 : 𝟙 A = 0 := (IsZero.iff_id_eq_zero A).mp hA
  have h2 : 𝟙 B = 0 := (IsZero.iff_id_eq_zero B).mp hB
  refine ⟨(0 : B ⟶ A), ?_, ?_⟩
  · rw [h1, comp_zero]
  · rw [h2, zero_comp]

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

/-! ## The projection and its section -/

/-- The projection `↥(sphLoopBig n) × Y → ↥(sphLoopBig n) × PUnit`. -/
def sphProjHom (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    TopCat.of (↥(sphLoopBig n) × Y) ⟶ TopCat.of (↥(sphLoopBig n) × PUnit) :=
  TopCat.ofHom ⟨fun p => (p.1, ()), by fun_prop⟩

/-- Its restriction to the collar. -/
def sphProjRelHom (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    TopCat.of ↥(sphLoopCollarProd n Y) ⟶ TopCat.of ↥(sphLoopCollarProd n PUnit) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.1, ()), p.2⟩, by
    have hf : Continuous fun p : ↥(sphLoopCollarProd n Y) => (p.1.1, ()) :=
      Continuous.prodMk (continuous_fst.comp continuous_subtype_val) continuous_const
    exact Continuous.subtype_mk hf (fun p => p.2)⟩

theorem sphProjHom_subtypeIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n Y)
        ≫ sphProjHom n Y
      = sphProjRelHom n Y
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
            (sphLoopCollarProd n PUnit) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The section `q ↦ (q, y₀)`. -/
def sphProjSec (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    TopCat.of (↥(sphLoopBig n) × PUnit) ⟶ TopCat.of (↥(sphLoopBig n) × Y) :=
  TopCat.ofHom ⟨fun p => (p.1, y₀), by fun_prop⟩

/-- Its restriction to the collar. -/
def sphProjSecRel (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    TopCat.of ↥(sphLoopCollarProd n PUnit) ⟶ TopCat.of ↥(sphLoopCollarProd n Y) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.1, y₀), p.2⟩, by
    have hf : Continuous fun p : ↥(sphLoopCollarProd n PUnit) => (p.1.1, y₀) :=
      Continuous.prodMk (continuous_fst.comp continuous_subtype_val) continuous_const
    exact Continuous.subtype_mk hf (fun p => p.2)⟩

theorem sphProjSec_subtypeIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
        (sphLoopCollarProd n PUnit) ≫ sphProjSec n Y y₀
      = sphProjSecRel n Y y₀
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × Y))
            (sphLoopCollarProd n Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

theorem sphProjSec_comp_projHom (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    sphProjSec n Y y₀ ≫ sphProjHom n Y
      = 𝟙 (TopCat.of (↥(sphLoopBig n) × PUnit)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  obtain ⟨q, u⟩ := p
  obtain rfl : u = () := Subsingleton.elim u ()
  rfl

theorem sphProjSecRel_comp_projRelHom (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    sphProjSecRel n Y y₀ ≫ sphProjRelHom n Y
      = 𝟙 (TopCat.of ↥(sphLoopCollarProd n PUnit)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-! ## The projection lemma -/

/-- The chain map of relative complexes induced by the projection. -/
def sphProjRelMap (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n Y) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
        (sphLoopCollarProd n PUnit) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig n) × Y))
    (TopCat.of (↥(sphLoopBig n) × PUnit)) (sphLoopCollarProd n Y) (sphLoopCollarProd n PUnit)
    (sphProjHom n Y) (sphProjRelHom n Y) (sphProjHom_subtypeIncl n Y)

/-- The chain map of relative complexes induced by the section. -/
def sphSecRelMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit)) (sphLoopCollarProd n PUnit) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n Y) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig n) × PUnit))
    (TopCat.of (↥(sphLoopBig n) × Y)) (sphLoopCollarProd n PUnit) (sphLoopCollarProd n Y)
    (sphProjSec n Y y₀) (sphProjSecRel n Y y₀) (sphProjSec_subtypeIncl n Y y₀)

/-- The relation `relChainsMapOf (𝟙) (𝟙) = 𝟙`. -/
theorem relChainsMapOf_id (X : TopCat) (A : Set X)
    (w : Work.Cohomology.subtypeIncl X A ≫ 𝟙 X = 𝟙 (TopCat.of A) ≫ Work.Cohomology.subtypeIncl X A) :
    Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w
      = 𝟙 (Work.Cohomology.relChains X A) := by
  unfold Work.Cohomology.relChainsMapOf
  simp only [CategoryTheory.Functor.map_id]
  exact cokernel.map_id _ _ _

/-- `relChainsMapOf` only depends on the maps (the compatibility proofs live in a proposition). -/
theorem relChainsMapOf_congr {X Y : TopCat} (A : Set X) (B : Set Y) {f f' : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  subst hf
  subst hg
  exact congrArg (fun w => Work.Cohomology.relChainsMapOf X Y A B f g w)
    (Subsingleton.elim w w')

/-! ## The splitting of the projection: `sec ≫ proj = 𝟙`

The section `q ↦ (q, y₀)` is a right inverse of the projection as a map of pairs, hence the induced
map of relative chain complexes is a right inverse.  This is the only place where the naturality of
`relChainsMapOf` in a composite is used; it is `Work.Cohomology.relChainsMapOf_comp`. -/

/-- The compatibility proof of the composite `sec ≫ proj`. -/
theorem sphProjSec_projHom_rel (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit)) (sphLoopCollarProd n PUnit)
        ≫ (sphProjSec n Y y₀ ≫ sphProjHom n Y)
      = (sphProjSecRel n Y y₀ ≫ sphProjRelHom n Y)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
            (sphLoopCollarProd n PUnit) := by
  rw [← Category.assoc, sphProjSec_subtypeIncl, Category.assoc, sphProjHom_subtypeIncl,
    ← Category.assoc]

/-- **The projection is a split epimorphism on relative chain complexes**: the section at `y₀`
composes with it to the identity. -/
theorem sphSecRelMap_comp_sphProjRelMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    sphSecRelMap n Y y₀ ≫ sphProjRelMap n Y
      = 𝟙 (Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (sphLoopCollarProd n PUnit)) := by
  have h := Work.Cohomology.relChainsMapOf_comp (X := TopCat.of (↥(sphLoopBig n) × PUnit))
    (Y := TopCat.of (↥(sphLoopBig n) × Y)) (Z := TopCat.of (↥(sphLoopBig n) × PUnit))
    (A := sphLoopCollarProd n PUnit) (B := sphLoopCollarProd n Y) (C := sphLoopCollarProd n PUnit)
    (f := sphProjSec n Y y₀) (g := sphProjSecRel n Y y₀) (w := sphProjSec_subtypeIncl n Y y₀)
    (f' := sphProjHom n Y) (g' := sphProjRelHom n Y) (w' := sphProjHom_subtypeIncl n Y)
    (w'' := sphProjSec_projHom_rel n Y y₀)
  rw [sphSecRelMap, sphProjRelMap, h]
  rw [relChainsMapOf_congr (A := sphLoopCollarProd n PUnit) (B := sphLoopCollarProd n PUnit)
    (f := sphProjSec n Y y₀ ≫ sphProjHom n Y)
    (g := sphProjSecRel n Y y₀ ≫ sphProjRelHom n Y) (f' := 𝟙 _) (g' := 𝟙 _)
    (sphProjSec_comp_projHom n Y y₀) (sphProjSecRel_comp_projRelHom n Y y₀)
    (w' := by rw [Category.id_comp, Category.comp_id])]
  exact relChainsMapOf_id _ _ _

/-- The positive-degree homology of the one-point space vanishes. -/
theorem isZero_homology_punit (j : ℕ) (hj : 0 < j) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of PUnit)).homology j) :=
  Work.Cohomology.homologyPUnit ℤ j hj

/-- `H_0` of the one-point space is `ℤ`. -/
theorem nonempty_homology_zero_punit_linEquiv :
    Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of PUnit)).homology 0) ≃ₗ[ℤ] ℤ) := by
  haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) := inferInstance
  exact ⟨Work.Cohomology.uctIsoToLinearEquiv
    (asIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)))⟩

end

end Work.StemsB
