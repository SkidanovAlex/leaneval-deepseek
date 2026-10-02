import Mathlib
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.relCohMV_les
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.Endgame.relMVUVQuasiIso
import Submission.Work.Cohomology.Endgame.overlapQuasiIso
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.excisionAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The canonical maps of the relative Mayer--Vietoris sequence (prerequisites)

This file collects, in one self-contained module, the canonical chain maps
`alphaU`, `alphaV`, `gamma`, `delta` of the relative Mayer--Vietoris sequence together with the
comparison quasi-isomorphisms `etaU`, `etaV`, `mvPhi` with the genuine relative chains, and their
defining rules.  These are the ingredients out of which the relative Mayer--Vietoris short exact
sequence of *honest* relative cochains is assembled (see
`Submission/Work/Cohomology/relCohMV_honest_les.lean`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.HMV

noncomputable section

variable {X : TopCat} {Y : TopCat}

/-! ## 1. Naturality of the lift of small simplices -/

/-- The canonical identification of `↥C` with the part of `↥B` lying in `C`. -/
def subSubIso {C B : Set X} (h : C ⊆ B) :
    TopCat.of ↥C ≅ TopCat.of ↥((Subtype.val : ↥B → X) ⁻¹' C) :=
  TopCat.isoOfHomeo
    { toFun := fun p => ⟨⟨(p : X), h p.2⟩, p.2⟩
      invFun := fun q => ⟨(q.1 : X), q.2⟩
      left_inv := fun p => by rfl
      right_inv := fun q => by rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The inclusion of the part of `↥B` lying in `C` into `↥B`. -/
def subInclPre {C B : Set X} (h : C ⊆ B) :
    TopCat.of ↥((Subtype.val : ↥B → X) ⁻¹' C) ⟶ TopCat.of ↥B :=
  Work.Cohomology.subtypeIncl (TopCat.of ↥B) ((Subtype.val : ↥B → X) ⁻¹' C)

/-- The canonical map `↥C ⟶ ↥B`. -/
def subInclSub {C B : Set X} (h : C ⊆ B) : TopCat.of ↥C ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun p => ⟨(p : X), h p.2⟩, by fun_prop⟩

theorem subSubIso_comp_inclPre {C B : Set X} (h : C ⊆ B) :
    (subSubIso h).hom ≫ subInclPre h = subInclSub h := by
  apply TopCat.hom_ext
  ext p
  rfl

theorem subInclSub_comp_subtypeIncl {C B : Set X} (h : C ⊆ B) :
    subInclSub h ≫ Work.Cohomology.subtypeIncl X B = Work.Cohomology.subtypeIncl X C := by
  apply TopCat.hom_ext
  ext p
  rfl

/-- The inclusion of the small simplices lying in `C` into those lying in `B`. -/
def subInclSSetGen (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    Work.Cohomology.smallInSSet U V C ⟶ Work.Cohomology.smallInSSet U V B :=
  Subfunctor.homOfLe (by
    intro n x hx
    exact ⟨hx.1, hx.2.trans h⟩)

theorem subInclChain_eq_gen (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    Work.Cohomology.subInclChain U V h
      = SSet.chainComplexMap (subInclSSetGen U V h) (ModuleCat.of ℤ ℤ) := rfl

theorem subInclSSetGen_comp (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    subInclSSetGen U V h ≫ (Work.Cohomology.smallInSubcomplex U V B).ι
      = (Work.Cohomology.smallInSubcomplex U V C).ι :=
  Subfunctor.homOfLe_ι _

/-- **Naturality of the lift of small simplices (subspace form).** -/
theorem smallInLift_gen_natural (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    subInclSSetGen U V h ≫ Work.Cohomology.smallInLift U V B
      = Work.Cohomology.smallInLift U V C ≫ TopCat.toSSet.map (subInclSub h) := by
  apply (cancel_mono (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X B))).1
  have hL : (subInclSSetGen U V h ≫ Work.Cohomology.smallInLift U V B)
      ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl X B)
      = (Work.Cohomology.smallInSubcomplex U V C).ι := by
    rw [Category.assoc, Work.Cohomology.smallInLift_comp, subInclSSetGen_comp]
  have hR : (Work.Cohomology.smallInLift U V C ≫ TopCat.toSSet.map (subInclSub h))
      ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl X B)
      = (Work.Cohomology.smallInSubcomplex U V C).ι := by
    rw [Category.assoc, ← Functor.map_comp, subInclSub_comp_subtypeIncl,
      Work.Cohomology.smallInLift_comp]
  exact hL.trans hR.symm

/-- **Naturality of the lift of small simplices (chain level, subspace form).** -/
theorem subInclChain_gen_natural' (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    Work.Cohomology.subInclChain U V h ≫ Work.Cohomology.smallInToSingA U V B
      = Work.Cohomology.smallInToSingA U V C
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥C) (TopCat.of ↥B) (subInclSub h) := by
  have hnat := congrArg (fun (f : Work.Cohomology.smallInSSet U V C
      ⟶ TopCat.toSSet.obj (TopCat.of ↥B)) => SSet.chainComplexMap f (ModuleCat.of ℤ ℤ))
    (smallInLift_gen_natural U V h)
  simp only [Functor.map_comp] at hnat
  exact hnat

/-- **Naturality of the lift of small simplices (relative chain form).** -/
theorem subInclChain_gen_natural_incl (U V : Set X) {C B : Set X} (h : C ⊆ B) :
    Work.Cohomology.subInclChain U V h ≫ Work.Cohomology.smallInToSingA U V B
      = Work.Cohomology.smallInToSingA U V C
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subSubIso h).hom) (ModuleCat.of ℤ ℤ)
        ≫ Work.Cohomology.inclChains (TopCat.of ↥B) (Work.Cohomology.interAU C B) := by
  have hnat := congrArg (fun (f : Work.Cohomology.smallInSSet U V C
      ⟶ TopCat.toSSet.obj (TopCat.of ↥B)) => SSet.chainComplexMap f (ModuleCat.of ℤ ℤ))
    (show subInclSSetGen U V h ≫ Work.Cohomology.smallInLift U V B
        = Work.Cohomology.smallInLift U V C
          ≫ TopCat.toSSet.map (subSubIso h).hom
          ≫ TopCat.toSSet.map (subInclPre h) from by
      rw [smallInLift_gen_natural U V h, ← Functor.map_comp, subSubIso_comp_inclPre])
  simp only [Functor.map_comp] at hnat
  exact hnat

/-- The subcomplex of small simplices lying in `C` is the range of `Simp(C) ⟶ Simp(X)`, for `C`
contained in `U`. -/
theorem smallInSubcomplex_eq_range_of_le (U V C : Set X) (h : C ⊆ U) :
    Work.Cohomology.smallInSubcomplex U V C
      = Subfunctor.range (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)) := by
  ext n σ
  rw [Subfunctor.range_obj]
  constructor
  · intro hσ
    exact exists_map_inclUX_of_range_subset C n σ hσ.2
  · rintro ⟨a, rfl⟩
    have hsd : ∀ z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
        TopCat.toSSetObjEquiv X n
            ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z
          = (Work.Cohomology.subtypeIncl X C)
              (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z) :=
      fun _ => rfl
    refine ⟨Or.inl ?_, ?_⟩
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z ∈ U
      rw [hsd z]
      exact h (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z).2
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z ∈ C
      rw [hsd z]
      exact (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z).2

/-- The subcomplex of small simplices lying in `C` is the range of `Simp(C) ⟶ Simp(X)`, for `C`
contained in `V`. -/
theorem smallInSubcomplex_eq_range_of_le_V (U V C : Set X) (h : C ⊆ V) :
    Work.Cohomology.smallInSubcomplex U V C
      = Subfunctor.range (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)) := by
  ext n σ
  rw [Subfunctor.range_obj]
  constructor
  · intro hσ
    exact exists_map_inclUX_of_range_subset C n σ hσ.2
  · rintro ⟨a, rfl⟩
    have hsd : ∀ z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
        TopCat.toSSetObjEquiv X n
            ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z
          = (Work.Cohomology.subtypeIncl X C)
              (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z) :=
      fun _ => rfl
    refine ⟨Or.inr ?_, ?_⟩
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z ∈ V
      rw [hsd z]
      exact h (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z).2
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquiv X n
          ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X C)).app n a) z ∈ C
      rw [hsd z]
      exact (TopCat.toSSetObjEquiv (TopCat.of ↥C) n a z).2

/-- The lift of the small simplices lying in `C` is an isomorphism, for `C ⊆ U`. -/
theorem isIso_smallInLift_of_le (U V C : Set X) (h : C ⊆ U) :
    IsIso (Work.Cohomology.smallInLift U V C) := by
  have heq := smallInSubcomplex_eq_range_of_le U V C h
  haveI : IsIso (Subfunctor.homOfLe (Work.Cohomology.smallInSubcomplex_le_range U V C)) := by
    refine ⟨Subfunctor.homOfLe (le_of_eq heq.symm), ?_, ?_⟩ <;> ext x <;> rfl
  rw [Work.Cohomology.smallInLift]
  infer_instance

/-- The lift of the small simplices lying in `C` is an isomorphism, for `C ⊆ V`. -/
theorem isIso_smallInLift_of_le_V (U V C : Set X) (h : C ⊆ V) :
    IsIso (Work.Cohomology.smallInLift U V C) := by
  have heq := smallInSubcomplex_eq_range_of_le_V U V C h
  haveI : IsIso (Subfunctor.homOfLe (Work.Cohomology.smallInSubcomplex_le_range U V C)) := by
    refine ⟨Subfunctor.homOfLe (le_of_eq heq.symm), ?_, ?_⟩ <;> ext x <;> rfl
  rw [Work.Cohomology.smallInLift]
  infer_instance

theorem chainMap_comp_local (P Q R : TopCat) (f : P ⟶ Q) (g : Q ⟶ R) :
    Work.Cohomology.chainMap ℤ P Q f ≫ Work.Cohomology.chainMap ℤ Q R g
      = Work.Cohomology.chainMap ℤ P R (f ≫ g) := by
  show (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f)
      ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map g)
    = (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (f ≫ g))
  rw [Functor.map_comp]

theorem chainComplexMap_le_coker {S S' : Set Y} (h : S ⊆ S') :
    SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S)) (ModuleCat.of ℤ ℤ)
      ≫ CategoryTheory.Limits.cokernel.π (SSet.chainComplexMap
          (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S')) (ModuleCat.of ℤ ℤ)) = 0 := by
  have h1 : TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S)
      = TopCat.toSSet.map (subInclSub h)
        ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S') := by
    rw [← Functor.map_comp, subInclSub_comp_subtypeIncl]
  have hfac : SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S))
        (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (TopCat.toSSet.map (subInclSub h)) (ModuleCat.of ℤ ℤ)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S'))
            (ModuleCat.of ℤ ℤ) := by
    have h2 := congrArg (fun (f : TopCat.toSSet.obj (TopCat.of ↥S) ⟶ TopCat.toSSet.obj Y) =>
      SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) h1
    simp only [Functor.map_comp] at h2
    exact h2
  rw [hfac, Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero]

theorem inclChains_le_coker {S S' : Set Y} (h : S ⊆ S') :
    Work.Cohomology.inclChains Y S
      ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y S') = 0 := by
  rw [show Work.Cohomology.inclChains Y S
      = SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S))
          (ModuleCat.of ℤ ℤ) from Work.Cohomology.inclChains_eq_map Y S]
  rw [show Work.Cohomology.inclChains Y S'
      = SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y S'))
          (ModuleCat.of ℤ ℤ) from Work.Cohomology.inclChains_eq_map Y S']
  exact chainComplexMap_le_coker h

/-! ## 2. The comparison of the `U`- and `V`-pieces with the genuine relative chains -/

/-- The canonical identification of the subspace `U ∩ A` with the part of `U` lying in `A`. -/
def subInterIso (A U : Set X) :
    TopCat.of ↥(U ∩ A) ≅ TopCat.of ↥(Work.Cohomology.interAU A U) :=
  TopCat.isoOfHomeo
    { toFun := fun p => ⟨⟨(p : X), p.2.1⟩, p.2.2⟩
      invFun := fun q => ⟨(q.1 : X), ⟨q.1.2, q.2⟩⟩
      left_inv := fun p => by rfl
      right_inv := fun q => by rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

theorem subInterIso_comp (A U : Set X) :
    (subInterIso A U).hom ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥U)
        (Work.Cohomology.interAU A U)
      = subInclSub (Set.inter_subset_left : U ∩ A ⊆ U) := by
  apply TopCat.hom_ext
  ext p
  rfl

/-- The two spellings of the part of `U` lying in `A` agree. -/
theorem interAU_inter_eq (A U : Set X) :
    Work.Cohomology.interAU (U ∩ A) U = Work.Cohomology.interAU A U := by
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩

/-- **Naturality of the comparison with the genuine relative chains of the `U`-piece.** -/
theorem subInterIso_inclChains (A U : Set X) :
    SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom) (ModuleCat.of ℤ ℤ)
        ≫ Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ A)) (TopCat.of ↥U)
          (subInclSub (Set.inter_subset_left : U ∩ A ⊆ U)) := by
  have h1 : TopCat.toSSet.map (subInterIso A U).hom
      ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of ↥U)
          (Work.Cohomology.interAU A U))
      = TopCat.toSSet.map (subInclSub (Set.inter_subset_left : U ∩ A ⊆ U)) := by
    rw [← Functor.map_comp, subInterIso_comp A U]
  have h2 := congrArg (fun (f : TopCat.toSSet.obj (TopCat.of ↥(U ∩ A))
      ⟶ TopCat.toSSet.obj (TopCat.of ↥U)) =>
    SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) h1
  simp only [Functor.map_comp] at h2
  rw [show Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U)
      = SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of ↥U)
          (Work.Cohomology.interAU A U))) (ModuleCat.of ℤ ℤ)
      from Work.Cohomology.inclChains_eq_map _ _]
  exact h2

theorem subInclChain_U_natural (A U V : Set X) :
    Work.Cohomology.subInclChain U V (Set.inter_subset_left : U ∩ A ⊆ U)
      ≫ Work.Cohomology.smallInToSingA U V U
      = Work.Cohomology.smallInToSingA U V (U ∩ A)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom) (ModuleCat.of ℤ ℤ)
        ≫ Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U) := by
  rw [subInclChain_gen_natural' U V (Set.inter_subset_left : U ∩ A ⊆ U)]
  simp only [subInterIso_inclChains]

/-- **Naturality of the comparison with the genuine relative chains of the `V`-piece.** -/
theorem subInterIso_comp_V (A V : Set X) :
    (subInterIso A V).hom ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥V)
        (Work.Cohomology.interAU A V)
      = subInclSub (Set.inter_subset_left : V ∩ A ⊆ V) := by
  apply TopCat.hom_ext
  ext p
  rfl

theorem subInterIsoV_inclChains (A V : Set X) :
    SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom) (ModuleCat.of ℤ ℤ)
        ≫ Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(V ∩ A)) (TopCat.of ↥V)
          (subInclSub (Set.inter_subset_left : V ∩ A ⊆ V)) := by
  have h1 : TopCat.toSSet.map (subInterIso A V).hom
      ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of ↥V)
          (Work.Cohomology.interAU A V))
      = TopCat.toSSet.map (subInclSub (Set.inter_subset_left : V ∩ A ⊆ V)) := by
    rw [← Functor.map_comp, subInterIso_comp_V A V]
  have h2 := congrArg (fun (f : TopCat.toSSet.obj (TopCat.of ↥(V ∩ A))
      ⟶ TopCat.toSSet.obj (TopCat.of ↥V)) =>
    SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) h1
  simp only [Functor.map_comp] at h2
  rw [show Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V)
      = SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of ↥V)
          (Work.Cohomology.interAU A V))) (ModuleCat.of ℤ ℤ)
      from Work.Cohomology.inclChains_eq_map _ _]
  exact h2

theorem subInclChain_V_natural (A U V : Set X) :
    Work.Cohomology.subInclChain U V (Set.inter_subset_left : V ∩ A ⊆ V)
      ≫ Work.Cohomology.smallInToSingA U V V
      = Work.Cohomology.smallInToSingA U V (V ∩ A)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom) (ModuleCat.of ℤ ℤ)
        ≫ Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V) := by
  rw [subInclChain_gen_natural' U V (Set.inter_subset_left : V ∩ A ⊆ V)]
  simp only [subInterIsoV_inclChains]

theorem relMVτ₂U_eq (U V A : Set X) :
    Work.Cohomology.relMVτ₂U U V A
      = Work.Cohomology.subInclChain U V (Set.inter_subset_left : U ∩ A ⊆ U) := rfl

theorem relMVτ₂V_eq (U V A : Set X) :
    Work.Cohomology.relMVτ₂V U V A
      = Work.Cohomology.subInclChain U V (Set.inter_subset_left : V ∩ A ⊆ V) := rfl

/-- **The comparison `C^{U,V}(U,U∩A) ⟶ C_*(U, U∩A)`.** -/
noncomputable def etaU (A U V : Set X) :
    Work.Cohomology.relMVUU X A U V ⟶
      Work.Cohomology.relChains (TopCat.of ↥U) (Work.Cohomology.interAU A U) :=
  CategoryTheory.Limits.cokernel.desc (Work.Cohomology.relMVτ₂U U V A)
    (Work.Cohomology.smallInToSingA U V U
      ≫ CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U)))
    (by
      rw [relMVτ₂U_eq U V A, ← Category.assoc, subInclChain_U_natural A U V]
      simp only [Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero,
        zero_comp])

/-- **The comparison `C^{U,V}(V,V∩A) ⟶ C_*(V, V∩A)`.** -/
noncomputable def etaV (A U V : Set X) :
    Work.Cohomology.relMVVV X A U V ⟶
      Work.Cohomology.relChains (TopCat.of ↥V) (Work.Cohomology.interAU A V) :=
  CategoryTheory.Limits.cokernel.desc (Work.Cohomology.relMVτ₂V U V A)
    (Work.Cohomology.smallInToSingA U V V
      ≫ CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V)))
    (by
      rw [relMVτ₂V_eq U V A, ← Category.assoc, subInclChain_V_natural A U V]
      simp only [Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero,
        zero_comp])

/-- The defining rule of `etaU`. -/
theorem etaU_comp (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂U U V A) ≫ etaU A U V
      = Work.Cohomology.smallInToSingA U V U
        ≫ CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains (TopCat.of ↥U) (Work.Cohomology.interAU A U)) :=
  CategoryTheory.Limits.cokernel.π_desc _ _ _

/-- The defining rule of `etaV`. -/
theorem etaV_comp (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂V U V A) ≫ etaV A U V
      = Work.Cohomology.smallInToSingA U V V
        ≫ CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains (TopCat.of ↥V) (Work.Cohomology.interAU A V)) :=
  CategoryTheory.Limits.cokernel.π_desc _ _ _

/-- **The comparison of the `U`-piece is a quasi-isomorphism.** -/
theorem isIso_homologyMap_etaU (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (etaU A U V) n) := by
  haveI hfun : IsIso (Work.Cohomology.smallInLift U V (U ∩ A)) :=
    isIso_smallInLift_of_le U V (U ∩ A) (Set.inter_subset_left : U ∩ A ⊆ U)
  haveI hfunU : IsIso (Work.Cohomology.smallInLift U V U) :=
    isIso_smallInLift_of_le U V U (le_refl U)
  haveI hmap1 : IsIso (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (U ∩ A))
      (ModuleCat.of ℤ ℤ)) :=
    Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (Work.Cohomology.smallInLift U V (U ∩ A))
  haveI hmap2 : IsIso (SSet.chainComplexMap (Work.Cohomology.smallInLift U V U)
      (ModuleCat.of ℤ ℤ)) :=
    Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (Work.Cohomology.smallInLift U V U)
  haveI hmap3 : IsIso (subInterIso A U).hom := (subInterIso A U).isIso_hom
  haveI hmap3' : IsIso (TopCat.toSSet.map (subInterIso A U).hom) := Functor.map_isIso _ _
  haveI hmap4 : IsIso (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom)
      (ModuleCat.of ℤ ℤ)) := Functor.map_isIso _ _
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (Work.Cohomology.relMVτ₂U U V A)
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂U U V A))
      (CategoryTheory.Limits.cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Work.Cohomology.relMVτ₂U U V A))
      (Work.Cohomology.mono_subInclChain U V (Set.inter_subset_left : U ∩ A ⊆ U))
      inferInstance
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.hPairShort (TopCat.of ↥U) (Work.Cohomology.interAU A U)
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact _ _
  let ψ : S₁ ⟶ S₂ :=
    { τ₁ := Work.Cohomology.smallInToSingA U V (U ∩ A)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom) (ModuleCat.of ℤ ℤ)
      τ₂ := Work.Cohomology.smallInToSingA U V U
      τ₃ := etaU A U V
      comm₁₂ := (subInclChain_U_natural A U V).symm
      comm₂₃ := (etaU_comp A U V).symm }
  have hq1 : QuasiIso ψ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    rw [HomologicalComplex.homologyMap_comp]
    haveI hA : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (U ∩ A))
          (ModuleCat.of ℤ ℤ)) i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) i)
        (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (U ∩ A)) (ModuleCat.of ℤ ℤ))
    haveI hB : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom) (ModuleCat.of ℤ ℤ)) i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) i)
        (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A U).hom) (ModuleCat.of ℤ ℤ))
    exact inferInstance
  have hq2 : QuasiIso ψ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) i)
      (SSet.chainComplexMap (Work.Cohomology.smallInLift U V U) (ModuleCat.of ℤ ℤ))
  have hq3 := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hS₁ hS₂ hq1 hq2
  have h := hq3.quasiIsoAt n
  rw [quasiIsoAt_iff_isIso_homologyMap] at h
  exact h

/-- **The comparison of the `V`-piece is a quasi-isomorphism.** -/
theorem isIso_homologyMap_etaV (A U V : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (etaV A U V) n) := by
  haveI hfun : IsIso (Work.Cohomology.smallInLift U V (V ∩ A)) :=
    isIso_smallInLift_of_le_V U V (V ∩ A) (Set.inter_subset_left : V ∩ A ⊆ V)
  haveI hfunV : IsIso (Work.Cohomology.smallInLift U V V) :=
    isIso_smallInLift_of_le_V U V V (le_refl V)
  haveI hmap1 : IsIso (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (V ∩ A))
      (ModuleCat.of ℤ ℤ)) :=
    Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (Work.Cohomology.smallInLift U V (V ∩ A))
  haveI hmap2 : IsIso (SSet.chainComplexMap (Work.Cohomology.smallInLift U V V)
      (ModuleCat.of ℤ ℤ)) :=
    Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (Work.Cohomology.smallInLift U V V)
  haveI hmap3 : IsIso (subInterIso A V).hom := (subInterIso A V).isIso_hom
  haveI hmap3' : IsIso (TopCat.toSSet.map (subInterIso A V).hom) := Functor.map_isIso _ _
  haveI hmap4 : IsIso (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom)
      (ModuleCat.of ℤ ℤ)) := Functor.map_isIso _ _
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (Work.Cohomology.relMVτ₂V U V A)
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂V U V A))
      (CategoryTheory.Limits.cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Work.Cohomology.relMVτ₂V U V A))
      (Work.Cohomology.mono_subInclChain U V (Set.inter_subset_left : V ∩ A ⊆ V))
      inferInstance
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.hPairShort (TopCat.of ↥V) (Work.Cohomology.interAU A V)
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact _ _
  let ψ : S₁ ⟶ S₂ :=
    { τ₁ := Work.Cohomology.smallInToSingA U V (V ∩ A)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom) (ModuleCat.of ℤ ℤ)
      τ₂ := Work.Cohomology.smallInToSingA U V V
      τ₃ := etaV A U V
      comm₁₂ := (subInclChain_V_natural A U V).symm
      comm₂₃ := (etaV_comp A U V).symm }
  have hq1 : QuasiIso ψ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    rw [HomologicalComplex.homologyMap_comp]
    haveI hA : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (V ∩ A))
          (ModuleCat.of ℤ ℤ)) i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) i)
        (SSet.chainComplexMap (Work.Cohomology.smallInLift U V (V ∩ A)) (ModuleCat.of ℤ ℤ))
    haveI hB : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom) (ModuleCat.of ℤ ℤ)) i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) i)
        (SSet.chainComplexMap (TopCat.toSSet.map (subInterIso A V).hom) (ModuleCat.of ℤ ℤ))
    exact inferInstance
  have hq2 : QuasiIso ψ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) i)
      (SSet.chainComplexMap (Work.Cohomology.smallInLift U V V) (ModuleCat.of ℤ ℤ))
  have hq3 := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hS₁ hS₂ hq1 hq2
  have h := hq3.quasiIsoAt n
  rw [quasiIsoAt_iff_isIso_homologyMap] at h
  exact h



/-! ## 4. The comparison `C^{U,V}(X,A) ⟶ C_*(X,A)`

This is the comparison of the small relative chains of the cover with the genuine relative chains;
it is a quasi-isomorphism for an open cover. -/

/-- **The comparison of the relative small chains with the genuine relative chains.** -/
noncomputable def mvPhi (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relMVTopC X A U V ⟶ Work.Cohomology.relChains X A :=
  CategoryTheory.Limits.cokernel.desc (Work.Cohomology.smallInToSmall U V A)
    (Work.Cohomology.smallToSing U V
      ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))
    (by
      have hzero : Work.Cohomology.smallInToSmall U V A
          ≫ (Work.Cohomology.smallToSing U V
            ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) = 0 := by
        rw [← Category.assoc, ← Work.Cohomology.smallInToSingA_comp U V A, Category.assoc,
          CategoryTheory.Limits.cokernel.condition, comp_zero]
      exact hzero)

theorem mvPhi_comp (X : TopCat) (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V A) ≫ mvPhi X A U V
      = Work.Cohomology.smallToSing U V
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A) :=
  CategoryTheory.Limits.cokernel.π_desc _ _ _

/-- **The comparison is a quasi-isomorphism for an open cover.** -/
theorem isIso_homologyMap_mvPhi (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mvPhi X A U V) n) := by
  obtain ⟨phi, hphi, hrule⟩ := Work.Cohomology.relMV_quasiIso X A U V hU hV hcov
  have heq : mvPhi X A U V = phi := by
    apply (cancel_epi (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.smallInToSmall U V A))).1
    rw [mvPhi_comp, hrule]
  rw [heq]
  exact hphi n

/-! ## 5. The natural maps of the small relative Mayer--Vietoris sequence -/

theorem subInclChain_congr (U V : Set X) {C B : Set X} {h h' : C ⊆ B} :
    Work.Cohomology.subInclChain U V h = Work.Cohomology.subInclChain U V h' := rfl

theorem relMVτ₁_congr (U V A : Set X) (h : U ∩ V ∩ A ⊆ U ∩ V) :
    Work.Cohomology.relMVτ₁ U V A = Work.Cohomology.subInclChain U V h :=
  subInclChain_congr U V

theorem relMVτ₂V_congr (U V A : Set X) (h : V ∩ A ⊆ V) :
    Work.Cohomology.relMVτ₂V U V A = Work.Cohomology.subInclChain U V h :=
  subInclChain_congr U V

/-- The `U`-component of the second map of the relative Mayer--Vietoris sequence. -/
abbrev alphaU (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relMVUU X A U V ⟶ Work.Cohomology.relMVTopC X A U V :=
  CategoryTheory.Limits.cokernel.map (Work.Cohomology.relMVτ₂U U V A)
    (Work.Cohomology.smallInToSmall U V A)
    (Work.Cohomology.subInclChain U V (Set.inter_subset_right : U ∩ A ⊆ A))
    (Work.Cohomology.smallInToSmall U V U)
    (by
      rw [relMVτ₂U_eq U V A,
        Work.Cohomology.subInclChain_smallInToSmall U V (Set.inter_subset_left : U ∩ A ⊆ U),
        Work.Cohomology.subInclChain_smallInToSmall U V (Set.inter_subset_right : U ∩ A ⊆ A)])

/-- The `V`-component of the second map of the relative Mayer--Vietoris sequence. -/
abbrev alphaV (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relMVVV X A U V ⟶ Work.Cohomology.relMVTopC X A U V :=
  CategoryTheory.Limits.cokernel.map (Work.Cohomology.relMVτ₂V U V A)
    (Work.Cohomology.smallInToSmall U V A)
    (Work.Cohomology.subInclChain U V (Set.inter_subset_right : V ∩ A ⊆ A))
    (Work.Cohomology.smallInToSmall U V V)
    (by
      rw [relMVτ₂V_congr U V A Set.inter_subset_left,
        Work.Cohomology.subInclChain_smallInToSmall U V (Set.inter_subset_left : V ∩ A ⊆ V),
        Work.Cohomology.subInclChain_smallInToSmall U V (Set.inter_subset_right : V ∩ A ⊆ A)])

/-- The `U`-component of the first map of the relative Mayer--Vietoris sequence. -/
abbrev gamma (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relMVUV X A U V ⟶ Work.Cohomology.relMVUU X A U V :=
  CategoryTheory.Limits.cokernel.map (Work.Cohomology.relMVτ₁ U V A)
    (Work.Cohomology.relMVτ₂U U V A)
    (Work.Cohomology.subInclChain U V (fun x hx => ⟨hx.1.1, hx.2⟩ : U ∩ V ∩ A ⊆ U ∩ A))
    (Work.Cohomology.subInclChain U V (Set.inter_subset_left : U ∩ V ⊆ U))
    (by
      rw [relMVτ₁_congr U V A, relMVτ₂U_eq U V A]
      exact (Work.Cohomology.subInclChain_comp U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
          (Set.inter_subset_left : U ∩ V ⊆ U)).trans
        ((subInclChain_congr U V).trans
          (Work.Cohomology.subInclChain_comp U V
            (fun x hx => ⟨hx.1.1, hx.2⟩ : U ∩ V ∩ A ⊆ U ∩ A)
            (Set.inter_subset_left : U ∩ A ⊆ U)).symm))

/-- The `V`-component of the first map of the relative Mayer--Vietoris sequence. -/
abbrev delta (X : TopCat) (A U V : Set X) :
    Work.Cohomology.relMVUV X A U V ⟶ Work.Cohomology.relMVVV X A U V :=
  CategoryTheory.Limits.cokernel.map (Work.Cohomology.relMVτ₁ U V A)
    (Work.Cohomology.relMVτ₂V U V A)
    (Work.Cohomology.subInclChain U V (fun x hx => ⟨hx.1.2, hx.2⟩ : U ∩ V ∩ A ⊆ V ∩ A))
    (Work.Cohomology.subInclChain U V (Set.inter_subset_right : U ∩ V ⊆ V))
    (by
      rw [relMVτ₁_congr U V A, relMVτ₂V_congr U V A Set.inter_subset_left]
      exact (Work.Cohomology.subInclChain_comp U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V)
          (Set.inter_subset_right : U ∩ V ⊆ V)).trans
        ((subInclChain_congr U V).trans
          (Work.Cohomology.subInclChain_comp U V
            (fun x hx => ⟨hx.1.2, hx.2⟩ : U ∩ V ∩ A ⊆ V ∩ A)
            (Set.inter_subset_left : V ∩ A ⊆ V)).symm))

theorem alphaU_comp (X : TopCat) (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂U U V A) ≫ alphaU X A U V
      = Work.Cohomology.smallInToSmall U V U
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V A) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem alphaV_comp (X : TopCat) (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂V U V A) ≫ alphaV X A U V
      = Work.Cohomology.smallInToSmall U V V
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V A) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem gamma_comp (X : TopCat) (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₁ U V A) ≫ gamma X A U V
      = Work.Cohomology.subInclChain U V (Set.inter_subset_left : U ∩ V ⊆ U)
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂U U V A) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem delta_comp (X : TopCat) (A U V : Set X) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₁ U V A) ≫ delta X A U V
      = Work.Cohomology.subInclChain U V (Set.inter_subset_right : U ∩ V ⊆ V)
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.relMVτ₂V U V A) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _


end

end Work.Cohomology.HMV
