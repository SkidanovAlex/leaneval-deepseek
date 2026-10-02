import Mathlib
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.Cohomology.isIso_smallIsoHom
import Submission.Work.Thom.Pair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The cohomology of a space split into two disjoint open pieces

If `U, V ⊆ X` are open, disjoint and cover `X`, then every singular simplex of `X` lies in `U` or
in `V` (a simplex is a continuous map out of a connected standard simplex), so the cohomology of
`X` is the direct sum of the cohomologies of the two pieces and the restriction maps
`(i_U^*, i_V^*) : H^n(X;ℤ) → H^n(U;ℤ) ⊕ H^n(V;ℤ)` are injective (in fact an isomorphism).

This module proves the statements in the workspace's model, using the Mayer–Vietoris short exact
sequence of cochain complexes (`Work.Cohomology.mvCochainSES`), whose intersection term vanishes
when `U ∩ V = ∅` (`Work.Cohomology.isZero_dualComplex_empty`), together with the small-chains
identification (`Work.Cohomology.isIso_smallIsoHom`).  The only statement actually needed by the
Thom chapter is the *injectivity* `Work.Thom.eq_zero_of_restrCoh_eq_zero_of_disjoint`.

## Main results

* `Work.Thom.isZero_cochainUV_of_disjoint` — `C^*(U ∩ V)` is a zero complex when `U ∩ V = ∅`;
* `Work.Thom.isIso_mvCochainF_of_disjoint` — hence the first Mayer–Vietoris map is an isomorphism;
* `Work.Thom.mvCochainF_comp_fst` / `_comp_snd` — its components are the duals of `smallOfU`,
  `smallOfV`;
* `Work.Thom.eq_zero_of_homologyMap_proj_eq_zero` — in a biproduct of cochain complexes, an
  element of the homology with vanishing two projections is zero;
* `Work.Thom.eq_zero_of_restrCoh_eq_zero_of_disjoint` — **a cohomology class of `X` vanishing on
  both pieces of a disjoint open cover is zero**.
-/

open CategoryTheory AlgebraicTopology Limits

open scoped Simplicial

namespace Work.Thom

noncomputable section

open Bundle Filter

open scoped Topology

variable {X : TopCat}

/-- `C^*(U ∩ V)` is a zero complex when `U ∩ V = ∅`. -/
theorem isZero_cochainUV_of_disjoint (U V : Set X) (h : Disjoint U V) :
    IsZero (Work.Cohomology.cochainUV U V) := by
  rw [Work.Cohomology.cochainUV, Set.disjoint_iff_inter_eq_empty.mp h]
  exact Work.Cohomology.isZero_dualComplex_empty X

/-- The first map of the Mayer–Vietoris sequence is an isomorphism when `U ∩ V = ∅`. -/
theorem isIso_mvCochainF_of_disjoint (U V : Set X) (h : Disjoint U V) :
    IsIso (Work.Cohomology.mvCochainF U V) := by
  haveI hZ : IsZero (Work.Cohomology.cochainUV U V) := isZero_cochainUV_of_disjoint U V h
  haveI hmono : Mono (Work.Cohomology.mvCochainF U V) :=
    (Work.Cohomology.mvCochainSES U V).mono_f
  have hepi : Epi (Work.Cohomology.mvCochainF U V) :=
    (ShortComplex.exact_iff_epi (ShortComplex.mk (Work.Cohomology.mvCochainF U V)
        (Work.Cohomology.mvCochainG U V) (Work.Cohomology.mvCochainComp U V))
      (IsZero.eq_of_tgt hZ _ 0)).mp (Work.Cohomology.mvCochainSES U V).exact
  haveI := hepi
  exact isIso_of_mono_of_epi _

/-- The first component of `mvCochainF` is the dual of `smallOfU`, globally. -/
theorem mvCochainF_comp_fst (U V : Set X) :
    Work.Cohomology.mvCochainF U V ≫
        (biprod.fst : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
          Work.Cohomology.cochainU U V)
      = Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.singularChains ℤ (TopCat.of ↥U))
          (Work.Cohomology.smallChains U V) (Work.Cohomology.smallOfU U V) := by
  rw [Work.Cohomology.mvCochainF]
  exact biprod.lift_fst _ _

/-- The second component of `mvCochainF` is minus the dual of `smallOfV`, globally. -/
theorem mvCochainF_comp_snd (U V : Set X) :
    Work.Cohomology.mvCochainF U V ≫
        (biprod.snd : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
          Work.Cohomology.cochainV U V)
      = -(Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.singularChains ℤ (TopCat.of ↥V))
          (Work.Cohomology.smallChains U V) (Work.Cohomology.smallOfV U V)) := by
  rw [Work.Cohomology.mvCochainF]
  exact biprod.lift_snd _ _

/-- A morphism of cochain complexes that is an isomorphism induces an injective map on homology. -/
theorem injective_homologyMap_of_isIso {C D : CochainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D)
    [IsIso f] (n : ℕ) : Function.Injective (HomologicalComplex.homologyMap f n).hom := by
  have hleft : HomologicalComplex.homologyMap f n ≫ HomologicalComplex.homologyMap (inv f) n
      = 𝟙 (C.homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, IsIso.hom_inv_id,
      HomologicalComplex.homologyMap_id]
  intro a b hab
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hleft) a
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hleft) b
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    at h1 h2
  rw [hab] at h1
  exact h1.symm.trans h2

/-- The composite of the small-chains isomorphism with the first Mayer–Vietoris map and the first
projection is the restriction to `U`. -/
theorem smallIsoHom_mvCochainF_fst (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    Work.Cohomology.smallIsoHom U V hU hV hcov n
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) n
      ≫ HomologicalComplex.homologyMap
          (biprod.fst : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
            Work.Cohomology.cochainU U V) n
    = Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
        (Work.Cohomology.subtypeIncl X U) n := by
  rw [← HomologicalComplex.homologyMap_comp, mvCochainF_comp_fst,
    Work.Cohomology.smallIsoHom_comp_smallOfU U V hU hV hcov n]

/-- The composite of the small-chains isomorphism with the first Mayer–Vietoris map and the second
projection is minus the restriction to `V`. -/
theorem smallIsoHom_mvCochainF_snd (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    Work.Cohomology.smallIsoHom U V hU hV hcov n
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) n
      ≫ HomologicalComplex.homologyMap
          (biprod.snd : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
            Work.Cohomology.cochainV U V) n
    = - Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥V) X
        (Work.Cohomology.subtypeIncl X V) n := by
  rw [← HomologicalComplex.homologyMap_comp, mvCochainF_comp_snd,
    HomologicalComplex.homologyMap_neg, CategoryTheory.Preadditive.comp_neg,
    Work.Cohomology.smallIsoHom_comp_smallOfV U V hU hV hcov n]

/-- The applied form of `Work.Thom.smallIsoHom_mvCochainF_fst`. -/
theorem smallIsoHom_mvCochainF_fst_apply (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) (x : Work.Cohomology.singularCohomology ℤ n X) :
    (HomologicalComplex.homologyMap
        (biprod.fst : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
          Work.Cohomology.cochainU U V) n).hom
        ((HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) n).hom
          ((Work.Cohomology.smallIsoHom U V hU hV hcov n).hom x))
    = (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
        (Work.Cohomology.subtypeIncl X U) n).hom x := by
  have h := congrArg ModuleCat.Hom.hom (smallIsoHom_mvCochainF_fst U V hU hV hcov n)
  exact LinearMap.congr_fun (by simpa only [ModuleCat.hom_comp] using h) x

/-- The applied form of `Work.Thom.smallIsoHom_mvCochainF_snd`. -/
theorem smallIsoHom_mvCochainF_snd_apply (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) (x : Work.Cohomology.singularCohomology ℤ n X) :
    (HomologicalComplex.homologyMap
        (biprod.snd : Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V ⟶
          Work.Cohomology.cochainV U V) n).hom
        ((HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) n).hom
          ((Work.Cohomology.smallIsoHom U V hU hV hcov n).hom x))
    = - (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥V) X
        (Work.Cohomology.subtypeIncl X V) n).hom x := by
  have h := congrArg ModuleCat.Hom.hom (smallIsoHom_mvCochainF_snd U V hU hV hcov n)
  exact LinearMap.congr_fun (by simpa only [ModuleCat.hom_comp, ModuleCat.hom_neg,
    LinearMap.neg_apply] using h) x

/-- **An element of the homology of a biproduct of cochain complexes whose two projections vanish
is zero.** -/
theorem eq_zero_of_homologyMap_proj_eq_zero (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (y : (C ⊞ D).homology k)
    (h1 : (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k).hom y = 0)
    (h2 : (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k).hom y = 0) : y = 0 := by
  have htot := congrArg (fun (f : (C ⊞ D).homology k ⟶ (C ⊞ D).homology k) => f.hom y)
    (Work.Cohomology.coh_homologyMap_total C D k)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at htot
  rw [h1, h2] at htot
  simpa using htot.symm

/-- **A cohomology class of `X` vanishing on both pieces of a disjoint open cover is zero**: the
pair of restrictions `(i_U^*, i_V^*)` is injective. -/
theorem eq_zero_of_singularCohomologyMap_eq_zero_of_disjoint (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hd : Disjoint U V) (hcov : U ∪ V = Set.univ) (n : ℕ)
    (x : Work.Cohomology.singularCohomology ℤ n X)
    (hU0 : (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
      (Work.Cohomology.subtypeIncl X U) n).hom x = 0)
    (hV0 : (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥V) X
      (Work.Cohomology.subtypeIncl X V) n).hom x = 0) : x = 0 := by
  haveI hS : IsIso (Work.Cohomology.smallIsoHom U V hU hV hcov n) :=
    Work.Cohomology.isIso_smallIsoHom U V hU hV hcov n
  have hinjS : Function.Injective (Work.Cohomology.smallIsoHom U V hU hV hcov n).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  haveI hF : IsIso (Work.Cohomology.mvCochainF U V) := isIso_mvCochainF_of_disjoint U V hd
  have hinjF : Function.Injective
      (HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) n).hom :=
    injective_homologyMap_of_isIso _ n
  set y := (Work.Cohomology.smallIsoHom U V hU hV hcov n).hom x with hy
  suffices y = 0 by
    have hy0 : (Work.Cohomology.smallIsoHom U V hU hV hcov n).hom x = 0 := hy.symm.trans this
    exact hinjS (by rw [hy0, map_zero])
  apply hinjF
  rw [map_zero, hy]
  refine eq_zero_of_homologyMap_proj_eq_zero _ _ n _ ?_ ?_
  · rw [smallIsoHom_mvCochainF_fst_apply U V hU hV hcov n x]
    exact hU0
  · rw [smallIsoHom_mvCochainF_snd_apply U V hU hV hcov n x]
    rw [hV0, neg_zero]

end

end Work.Thom
