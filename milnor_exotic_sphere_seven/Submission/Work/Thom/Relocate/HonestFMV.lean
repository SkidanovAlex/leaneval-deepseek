-- Copied (truncated) from `Submission/Work/Thom/nonempty_thomClass_of_disjoint_cover.lean`, minus
-- the import of `Submission.Work.Thom.DisjointCover` (which drags in the `prod_sphere_aux`
-- island) and minus the second half of that file (the glueing lemmas, which use `DisjointCover`).
-- The declarations kept here (`isZero_pdCohSub_empty`, the `biprodHomology_*` computations and
-- `honestF_injective_zero`/`_succ`/`_of_disjoint`) use only the honest relative Mayer--Vietoris
-- long exact sequence.
import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.Glue2
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Cohomology.isZero_dualComplex_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The Thom class of a bundle whose base splits into two disjoint open pieces

If `U, V ⊆ B` are disjoint open sets covering the base of a real bundle `Z`, and a global class
`τ ∈ Hⁿ(E,E∖0)` restricts to a local Thom class over each of `U` and `V`, then `τ` is a global
Thom class of `Z`.

The two halves of the proof are:

* **injectivity** of the Thom map: `Work.Thom.ker_thomMap_le` (the unconditional
  Mayer–Vietoris step) together with `Work.Thom.eq_zero_of_singularCohomologyMap_eq_zero_of_disjoint`
  (a cohomology class of the base vanishing on both pieces of a disjoint open cover is zero);
* **surjectivity** of the Thom map: on each piece the *local* Thom map is bijective by hypothesis,
  so it suffices to glue a global base class from two piece classes
  (`Work.Thom.exists_restr_pair_of_disjoint`), and to know that the two restrictions of the Thom
  pair over the pieces jointly detect a class of `Hᵐ(E,E∖0)`
  (`Work.Thom.honestF_injective_of_disjoint`).

The "detection" ingredient is the degeneration of the honest relative Mayer–Vietoris sequence
(`Work.Cohomology.honest_exact₁`) for a cover whose overlap is empty: the connecting map
`δ : Hᵐ⁻¹(X|_(U∩V)) → Hᵐ(X,A)` out of the vanishing overlap term is zero, so the map
`Hᵐ(E,E∖0) → Hᵐ(E|_U, E|_U∖0) ⊞ Hᵐ(E|_V, E|_V∖0)` is injective.  Its degree-zero case needs a
separate argument (there is no incoming connecting map in degree zero), supplied here by the
degreewise injectivity of the Mayer–Vietoris comparison map `hmvF`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The relative cohomology of the empty piece vanishes -/

/-- **The relative cohomology of a pair with empty ambient space vanishes**: the singular chains of
the empty space are zero, so all the components of `C^*(∅, A ∩ ∅)` are zero modules. -/
theorem isZero_pdCohSub_empty (X : TopCat) (A : Set X) (k : ℕ) :
    IsZero (Work.Cohomology.pdCohSub X A (∅ : Set X) k) := by
  show IsZero ((Work.Cohomology.relComplex ℤ (TopCat.of (∅ : Set X))
    {y : ↥(∅ : Set X) | (y : X) ∈ A}).homology k)
  have hcoch : IsZero (Work.Cohomology.singularCochainComplex ℤ (TopCat.of (∅ : Set X))) := by
    rw [← Work.Cohomology.dualComplex_singularChains ℤ (TopCat.of (∅ : Set X))]
    exact Work.Cohomology.isZero_dualComplex_empty X
  have hX : IsZero ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of (∅ : Set X))).X k) :=
    Functor.map_isZero (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) k) hcoch
  have hsub0 : Subsingleton ((Work.Cohomology.singularCochainComplex ℤ
      (TopCat.of (∅ : Set X))).X k) := ModuleCat.subsingleton_of_isZero hX
  have hsub : Subsingleton (Work.Cohomology.relKern ℤ (TopCat.of (∅ : Set X))
      {y : ↥(∅ : Set X) | (y : X) ∈ A} k) :=
    Subsingleton.intro fun a b => Subtype.ext (Subsingleton.elim (a.1) (b.1))
  have hZ0 : IsZero (ModuleCat.of ℤ (Work.Cohomology.relKern ℤ (TopCat.of (∅ : Set X))
      {y : ↥(∅ : Set X) | (y : X) ∈ A} k)) := ModuleCat.isZero_of_subsingleton _
  have hZ : IsZero ((Work.Cohomology.relComplex ℤ (TopCat.of (∅ : Set X))
      {y : ↥(∅ : Set X) | (y : X) ∈ A}).X k) := hZ0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ k).mp
    (HomologicalComplex.ExactAt.of_isZero hZ)

/-! ## Elementwise structure of the homology of a biproduct of cochain complexes -/

/-- The decomposition of an element of the homology of a biproduct of cochain complexes into its
two summands. -/
theorem biprodHomology_total {C D : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (y : (C ⊞ D).homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n)) y)
      + (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n)) y) = y := by
  have hmor : HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n
        ≫ HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n
      + HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n
        ≫ HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n
      = 𝟙 ((C ⊞ D).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
  have h := congrArg (fun (f : (C ⊞ D).homology n ⟶ (C ⊞ D).homology n) =>
    ModuleCat.Hom.hom f y) hmor
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- The first projection of the first inclusion of the homology of a biproduct of cochain
complexes. -/
theorem biprodHomology_inl_fst {C D : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (a : C.homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n)) a) = a := by
  have hmor : HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n
      ≫ HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n = 𝟙 (C.homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  have h := congrArg (fun (f : C.homology n ⟶ C.homology n) => ModuleCat.Hom.hom f a) hmor
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] using h

/-- The second projection of the first inclusion of the homology of a biproduct of cochain
complexes. -/
theorem biprodHomology_inl_snd {C D : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (a : C.homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n)) a) = 0 := by
  have hmor : HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n
      ≫ HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inl_snd, HomologicalComplex.homologyMap_zero]
  have h := congrArg (fun (f : C.homology n ⟶ D.homology n) => ModuleCat.Hom.hom f a) hmor
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The first projection of the second inclusion of the homology of a biproduct of cochain
complexes. -/
theorem biprodHomology_inr_fst {C D : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (b : D.homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n)) b) = 0 := by
  have hmor : HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n
      ≫ HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inr_fst, HomologicalComplex.homologyMap_zero]
  have h := congrArg (fun (f : D.homology n ⟶ C.homology n) => ModuleCat.Hom.hom f b) hmor
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The second projection of the second inclusion of the homology of a biproduct of cochain
complexes. -/
theorem biprodHomology_inr_snd {C D : CochainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (b : D.homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n)) b) = b := by
  have hmor : HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n
      ≫ HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n = 𝟙 (D.homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inr_snd, HomologicalComplex.homologyMap_id]
  have h := congrArg (fun (f : D.homology n ⟶ D.homology n) => ModuleCat.Hom.hom f b) hmor
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] using h

/-! ## Elementwise structure of a biproduct of modules -/

/-- The decomposition of an element of a biproduct of modules into its two summands. -/
theorem biprod_total_apply {M N : ModuleCat ℤ} (y : (M ⊞ N : ModuleCat ℤ)) :
    (ModuleCat.Hom.hom (biprod.inl : M ⟶ (M ⊞ N : ModuleCat ℤ)))
        ((ModuleCat.Hom.hom (biprod.fst : (M ⊞ N : ModuleCat ℤ) ⟶ M)) y)
      + (ModuleCat.Hom.hom (biprod.inr : N ⟶ (M ⊞ N : ModuleCat ℤ)))
        ((ModuleCat.Hom.hom (biprod.snd : (M ⊞ N : ModuleCat ℤ) ⟶ N)) y) = y := by
  have h := congrArg (fun (f : (M ⊞ N : ModuleCat ℤ) ⟶ (M ⊞ N : ModuleCat ℤ)) =>
    ModuleCat.Hom.hom f y) (biprod.total (X := M) (Y := N))
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- An element of a biproduct of modules whose two projections vanish is zero. -/
theorem biprod_eq_zero_of_fst_snd_eq_zero {M N : ModuleCat ℤ} (y : (M ⊞ N : ModuleCat ℤ))
    (h1 : (ModuleCat.Hom.hom (biprod.fst : (M ⊞ N : ModuleCat ℤ) ⟶ M)) y = 0)
    (h2 : (ModuleCat.Hom.hom (biprod.snd : (M ⊞ N : ModuleCat ℤ) ⟶ N)) y = 0) : y = 0 := by
  have h := biprod_total_apply y
  rw [h1, h2, map_zero, map_zero, add_zero] at h
  exact h.symm

/-! ## Injectivity of the honest Mayer–Vietoris map

The map `Work.Cohomology.honestF X A U V m : Hᵐ(X,A) → Hᵐ(U,U∩A) ⊞ Hᵐ(V,V∩A)` is injective
whenever `U ∩ V = ∅`.  For `m ≥ 1` this is the exactness of the honest relative Mayer–Vietoris
sequence at `Hᵐ(X,A)`: its kernel is the image of the connecting map `δ : Hᵐ⁻¹(U∩V) → Hᵐ(X,A)`,
which vanishes because `Hᵐ⁻¹(U∩V)` does.  In degree `0` there is no connecting map, and injectivity
follows instead from the degreewise-injectivity of the comparison map `hmvF`
(`H⁰` of a degreewise injective cochain map is injective). -/

/-- **`honestF` is injective in degree zero** (for any open cover, not necessarily disjoint). -/
theorem honestF_injective_zero (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V 0)) := by
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom ((Work.Cohomology.hmvChainRight X A U V).f 0)) :=
    Work.Cohomology.hmvChainDW_surjective X A U V 0 (Work.Cohomology.hmv_chain_zero X A U V)
      (Work.Cohomology.hmvChainSES X A U V)
  have hinjF0 : Function.Injective
      (ModuleCat.Hom.hom ((Work.Cohomology.hmvF X A U V).f 0)) :=
    Work.Cohomology.hmvF_injective X A U V 0 hsurj
  haveI hmono0 : Mono ((Work.Cohomology.hmvF X A U V).f 0) :=
    (ModuleCat.mono_iff_injective _).2 hinjF0
  have hmonoF : Mono (HomologicalComplex.homologyMap (Work.Cohomology.hmvF X A U V) 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (Work.Cohomology.hmvF X A U V) 0
      (fun i hi => by simp [ComplexShape.up] at hi)
  haveI hisocmp : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) 0) :=
    Work.Cohomology.isIso_homologyMap_cmpX X A U V hU hV hcov 0
  haveI hmonocmp : Mono (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) 0) :=
    inferInstance
  have hcomp : Mono (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) 0
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.hmvF X A U V) 0) := inferInstance
  have hinjcomp : Function.Injective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) 0
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.hmvF X A U V) 0)) :=
    (ModuleCat.mono_iff_injective _).1 hcomp
  intro a b hab
  apply hinjcomp
  have hsq := congrArg ModuleCat.Hom.hom (Work.Cohomology.honestSq₁ X A U V 0)
  simp only [ModuleCat.hom_comp] at hsq ⊢
  rw [LinearMap.congr_fun hsq a, LinearMap.congr_fun hsq b]
  exact congrArg (ModuleCat.Hom.hom (Work.Cohomology.hmvMidIso X A U V 0).inv) hab

/-- **`honestF` is injective in positive degree** when the two pieces of the cover are disjoint: the
connecting map of the honest relative Mayer–Vietoris sequence out of the (vanishing) overlap
term is zero. -/
theorem honestF_injective_succ (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hd : Disjoint U V) (j : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V (j + 1))) := by
  have hzero : IsZero (Work.Cohomology.pdCohSub X A (U ∩ V) j) := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hd]
    exact isZero_pdCohSub_empty X A j
  have hdelta0 : Work.Cohomology.honestDelta X A U V hU hV hcov j = 0 :=
    IsZero.eq_zero_of_src hzero _
  have hex := Work.Cohomology.honest_exact₁ X A U V hU hV hcov j
  have h' : LinearMap.range (ModuleCat.Hom.hom
        (Work.Cohomology.honestDelta X A U V hU hV hcov j))
      = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V (j + 1))) :=
    ShortComplex.Exact.moduleCat_range_eq_ker hex
  rw [hdelta0] at h'
  rw [ModuleCat.hom_zero, LinearMap.range_zero] at h'
  exact LinearMap.ker_eq_bot.mp h'.symm

/-- **The map `Hᵐ(X,A) → Hᵐ(X|_U, X|_U∖A) ⊞ Hᵐ(X|_V, X|_V∖A)` is injective** when `U, V` are
open, disjoint and cover `X`. -/
theorem honestF_injective_of_disjoint (X : TopCat) (A U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (hd : Disjoint U V) (m : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V m)) := by
  rcases m with _ | j
  · exact honestF_injective_zero X A U V hU hV hcov
  · exact honestF_injective_succ X A U V hU hV hcov hd j

end

end Work.Thom
