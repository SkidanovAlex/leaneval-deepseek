import Mathlib
import Submission.Work.Serre.serreC0KillHomologyDefs
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.serreC0KillUAcyclic
import Submission.Work.Serre.serreC0KillZHomeo
import Submission.Work.Serre.serreC0KillRho
import Submission.Work.Serre.serreC0KillShellHomology
import Submission.Work.Serre.serreC0KillShellImage
import Submission.Work.Serre.serreC0KillHomologyAux
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Stems.HurewiczSphere

/-!
# `serreC0KillHomology`: attaching `(n+2)`-cells kills homology modulo the attaching classes

For `n ≥ 1`, a space `Y`, an index type `ι` and attaching maps `f : ι → C(S^{n+1}, Y)`, the singular
homology of `X = attachCells n Y ι f` in degree `n+1` is the quotient of `H_{n+1}(Y)` by the span
of the Hurewicz classes of the attaching maps.

## The plan (Mayer–Vietoris)

Write `A = range attachIncl` (the old part), `U = cellU f (1/4)` (the outer part, a strong
deformation retract of `A`), `V = cellV f (1/2)` (the inner part, a disjoint union of open balls)
and `Z = U ∩ V` (the union of the shell bands `1/4 < ‖x‖ < 1/2`, one per cell).  Then

1. `U ∪ V = X` is an open cover, so the Mayer–Vietoris sequence gives
   `H_{n+1}(X) ≅ H_{n+1}(U) ⧸ image(H_{n+1}(Z) → H_{n+1}(U))`, because `H_n(Z) = 0`
   (`serreC0KillShellHomology`) and `H_{n+1}(V) = 0`;
2. `H_*(U) ≅ H_*(A)` since `(U,A)` is a strong deformation retract pair
   (`serreC0KillUAcyclic.isIso_inclChains_KillU`), and `H_*(A) ≅ H_*(Y)` via
   `Work.RatHurewicz.rangeHomeo`;
3. the image of `H_{n+1}(Z)` in `H_{n+1}(Y)` is exactly the span of the Hurewicz classes
   (`serreC0KillShellImage`, via the retraction `serreC0KillRho`).

## What is already proved

* `Submission/Work/Serre/serreC0KillHomologySets.lean`: the point-set facts about the cover and the
  shell pieces (open, disjoint, covering, the coordinate description `mem_KillQ`), together with
  the maps `shellDir` and `KillShellToA`;
* `Submission/Work/Serre/serreC0KillUAcyclic.lean`:
  `isZero_relChains_KillU` and `isIso_inclChains_KillU`;
* `Submission/Work/Serre/serreC0KillZHomeo.lean`: `↥(KillZ f) ≃ₜ Σ i, ↥(KillQ f i)`;
* `Submission/Work/Serre/serreC0KillRho.lean`: the retraction `KillU → KillA` fixing `KillA`,
  agreeing with `KillShellToA` on the shell;
* `Submission/Work/Serre/serreC0KillShellHomology.lean`,
  `Submission/Work/Serre/serreC0KillShellImage.lean` (delegated, in progress):
  the vanishings `H_n(Z) = 0`, `H_{n+1}(V) = 0` and the image computation.

## What is left

* the Mayer–Vietoris cokernel algebra (the last two sections of the plan above), whose first step
  is the surjectivity of `Work.Cohomology.mvRightX` from `H_n(Z) = 0`;
* the final chaining of the three isomorphisms.

A first attempt at the algebra is in `Submission/Work/Serre/_my_assembly.lean` (scratch): the
statements are right but the elaborator times out on the `KillZ`-heavy statements at low
heartbeat budgets; `set_option maxHeartbeats` and, if necessary, restating the lemmas in terms of
`cellU f (1/4) ∩ cellV f (1/2)` directly (rather than through the `abbrev`s) is the way forward.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

theorem serreC0KillHomology {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))).homology (n+1)) ≅
      ModuleCat.of ℤ (((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)) ⧸
        Submodule.span ℤ (Set.range (fun i => Work.Stems.hurewiczClass (n+1) (by omega) (f i))))) := by
  classical
  obtain ⟨-, hZn, hVn⟩ := serreC0KillShellHomology (n := n) hn ι f
  obtain ⟨ρ, eρ, hρfix, hρshell⟩ := serreC0KillRho (n := n) hn ι f
  obtain ⟨eMV⟩ := mvCoker (n := n) (Y := Y) (ι := ι) f hZn
  -- ### 1. the retraction `KillU → KillA` gives an isomorphism in homology
  haveI hρiso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) (n+1)) :=
    isIso_homologyMap_retractKillU f ρ hρfix (n+1)
  let eUA : ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f))).homology (n+1)) ≃ₗ[ℤ]
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1)) :=
    linEquivOfIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) (n+1))
  -- ### 2. the homeomorphism `Y ≅ KillA` gives an isomorphism in homology
  have hEH : (TopCat.isoOfHomeo (Work.RatHurewicz.rangeHomeo n Y ι f)).hom
      = TopCat.ofHom (⟨Work.RatHurewicz.rangeHomeo n Y ι f,
          (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩ : C(Y, ↥(KillA f))) :=
    TopCat.isoOfHomeo_hom (X := TopCat.of Y) (Y := TopCat.of ↥(KillA f)) _
  haveI hHiso : IsIso (TopCat.ofHom (⟨Work.RatHurewicz.rangeHomeo n Y ι f,
      (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩ : C(Y, ↥(KillA f)))) := by
    rw [← hEH]
    infer_instance
  haveI hAIso : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of ↥(KillA f))
      (TopCat.ofHom ⟨Work.RatHurewicz.rangeHomeo n Y ι f,
        (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩)) := by
    rw [Work.Cohomology.chainMap]
    exact Functor.map_isIso _ _
  haveI hAIso' : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of Y)
      (TopCat.of ↥(KillA f)) (TopCat.ofHom ⟨Work.RatHurewicz.rangeHomeo n Y ι f,
        (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩)) (n+1)) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso (asIso (Work.Cohomology.chainMap ℤ
      (TopCat.of Y) (TopCat.of ↥(KillA f)) (TopCat.ofHom ⟨Work.RatHurewicz.rangeHomeo n Y ι f,
        (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩))) (n+1))
  let eAY : ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)) ≃ₗ[ℤ]
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1)) :=
    linEquivOfIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of Y)
      (TopCat.of ↥(KillA f)) (TopCat.ofHom ⟨Work.RatHurewicz.rangeHomeo n Y ι f,
        (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩)) (n+1))
  -- ### 3. the projection onto the `U`-factor of the biproduct
  haveI hfst : IsIso (HomologicalComplex.homologyMap (biprod.fst
      (X := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f)))
      (Y := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillV f)))) (n+1)) :=
    homologyMap_biprod_fst_isIso (n+1) hVn
  let φ₁ : ↥(Work.Cohomology.HBiprod (X := TopCat.of (KillX f)) (KillU f) (KillV f) (n+1)) ≃ₗ[ℤ]
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f))).homology (n+1)) :=
    linEquivOfIso (HomologicalComplex.homologyMap (biprod.fst
      (X := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f)))
      (Y := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillV f)))) (n+1))
  -- ### 4. the Mayer–Vietoris maps
  let a := HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (X := TopCat.of (KillX f))
    (KillU f) (KillV f)) (n+1)
  let μ := HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f))
    (TopCat.of ↥(KillU f)) (TopCat.ofHom (Work.Cohomology.inclUVU (X := TopCat.of (KillX f))
      (KillU f) (KillV f)).hom)) (n+1)
  -- ### 5. the two submodules agree
  have h3 : Submodule.map (φ₁ : ↥(Work.Cohomology.HBiprod (X := TopCat.of (KillX f))
        (KillU f) (KillV f) (n+1)) →ₗ[ℤ]
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f))).homology (n+1)))
      (LinearMap.range (ModuleCat.Hom.hom a))
      = LinearMap.range (ModuleCat.Hom.hom μ) := by
    have hφ1 : (φ₁ : ↥(Work.Cohomology.HBiprod (X := TopCat.of (KillX f))
          (KillU f) (KillV f) (n+1)) →ₗ[ℤ]
          ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f))).homology (n+1)))
        = ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst
          (X := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f)))
          (Y := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillV f)))) (n+1)) := rfl
    have ha : a = HomologicalComplex.homologyMap (Work.Cohomology.mvLeft
        (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1) := rfl
    have hlift : Work.Cohomology.mvLeft (X := TopCat.of (KillX f)) (KillU f) (KillV f)
        ≫ biprod.fst (X := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f)))
            (Y := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillV f)))
        = Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillU f))
          (TopCat.ofHom (Work.Cohomology.inclUVU (X := TopCat.of (KillX f))
            (KillU f) (KillV f)).hom) :=
      mvLeft_comp_fst (X := TopCat.of (KillX f)) (KillU f) (KillV f)
    have hcomp : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst
          (X := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f)))
          (Y := Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillV f)))) (n+1))).comp
        (ModuleCat.Hom.hom a) = ModuleCat.Hom.hom μ := by
      rw [← ModuleCat.hom_comp, ha, ← HomologicalComplex.homologyMap_comp, hlift]
    rw [hφ1, ← LinearMap.range_comp, hcomp]
  -- ### 6. the submodule in `H_{n+1}(Y)`
  let eUY : ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillU f))).homology (n+1)) ≃ₗ[ℤ]
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)) :=
    eUA.trans eAY.symm
  let S : Submodule ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)) :=
    Submodule.span ℤ (Set.range (fun i => Work.Stems.hurewiczClass (n+1) (by omega) (f i)))
  have h5 : Submodule.map (eUY : ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(KillU f))).homology (n+1)) →ₗ[ℤ]
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)))
      (LinearMap.range (ModuleCat.Hom.hom μ)) = S := by
    have hcoe : (eUY : ↥((Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(KillU f))).homology (n+1)) →ₗ[ℤ]
          ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)))
        = (eAY.symm : ↥((Work.Cohomology.singularChains ℤ
              (TopCat.of ↥(KillA f))).homology (n+1)) →ₗ[ℤ]
              ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1))).comp
          (eUA : ↥((Work.Cohomology.singularChains ℤ
              (TopCat.of ↥(KillU f))).homology (n+1)) →ₗ[ℤ]
              ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1))) := rfl
    have hρpart : Submodule.map (eUA : ↥((Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(KillU f))).homology (n+1)) →ₗ[ℤ]
          ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1)))
        (LinearMap.range (ModuleCat.Hom.hom μ))
        = killHurewiczSpan (n := n) (Y := Y) (ι := ι) hn f := by
      have heUA : (eUA : ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of ↥(KillU f))).homology (n+1)) →ₗ[ℤ]
            ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1)))
          = ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) (n+1)) := rfl
      have hmap : ρ.comp ((Work.Cohomology.inclUVU (X := TopCat.of (KillX f))
            (KillU f) (KillV f)).hom)
          = (KillShellToA f).comp ⟨eρ, eρ.continuous_toFun⟩ := by
        apply ContinuousMap.ext
        intro z
        have hz : (⟨(z : KillX f), z.2.1⟩ : ↥(KillU f))
            = ⟨(z : KillX f), KillZ_subset_KillU f z.2⟩ := Subtype.ext rfl
        exact (congrArg (fun w => ρ w) hz).trans (hρshell z)
      have hcomp : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) (n+1))).comp
          (ModuleCat.Hom.hom μ)
          = ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
              (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillA f))
              (TopCat.ofHom ((KillShellToA f).comp ⟨eρ, eρ.continuous_toFun⟩))) (n+1)) := by
        rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
          ← Work.Cohomology.chainMap_comp', ← TopCat.ofHom_comp, hmap]
      rw [heUA, ← LinearMap.range_comp, hcomp]
      exact range_homologyMap_KillShellToA_comp (n := n) hn f eρ
    have hpt : ∀ i : ι, (eAY.symm : ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of ↥(KillA f))).homology (n+1)) →ₗ[ℤ]
            ↥((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (n+1)))
          (Work.Stems.hurewiczClass (n+1) (by omega)
            (killAIMap (n := n) (Y := Y) (ι := ι) f i))
        = Work.Stems.hurewiczClass (n+1) (by omega) (f i) := by
      intro i
      rw [← hurewiczClass_rangeHomeo (n := n) hn ι f i]
      exact eAY.symm_apply_apply _
    rw [hcoe, Submodule.map_comp, hρpart, killHurewiczSpan, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hpt i
  -- ### 7. assembly
  exact ⟨eMV ≪≫ quotCongrIso (φ₁) (LinearMap.range (ModuleCat.Hom.hom a))
      (LinearMap.range (ModuleCat.Hom.hom μ)) h3
    ≪≫ quotCongrIso (eUY) (LinearMap.range (ModuleCat.Hom.hom μ)) S h5⟩

end Work.Serre
