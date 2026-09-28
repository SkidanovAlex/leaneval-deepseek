import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.DiscPair.cylPreimageDefs
import Submission.Work.Serre.DiscPair.isQuotientMap_cylPreimageLift
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso
import Submission.Work.Serre.DiscPair.subsingleton_relCoh_cylPre
import Submission.Work.StemsB.AToolsR
import Submission.Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Cohomology.PairSequence

/-!
# The "subspace world" form of `Work.Serre.ThomCylAt`

`Work.Serre.ThomCylAt r N q` is the statement that the pair
`(cyl q, range (cylIncl q))` carries a Thom class whose mixed cup product with the pullback along
the retraction `cylRetract q` is an isomorphism in the range `m + r + 1 ≤ N + 1`.

In the base-change lemmas (`Work.Serre.DiscPair.thomCylAt_of_relVanishing`) it is convenient to
work instead with the *subspace* `↥(cylPre q V) = ↥((cylRetract q) ⁻¹' V)` of the mapping cylinder,
whose relative set is the part of the bottom copy lying over `V`, and with the retraction
`cylPreRetract q V` (the restriction of `cylRetract q`).  This module

* defines the resulting predicate `Work.Serre.DiscPair.ThomSubAt`;
* proves that it is *equivalent* to `Work.Serre.ThomCylAt` for the restricted fibration
  `restrictFibre q V`, along any homeomorphism `cyl (restrictFibre q V) ≃ₜ T` which matches the
  bottom copies and the retractions (`thomSubAt_iff_thomCylAt`);
* records the vanishing criterion for the *absolute* restriction map of a pair
  (`isIso_restrCoh_of_relCoh_isZero`).

The homeomorphisms themselves (for `V` open, and for the composite over a closed `S ⊆ V`) are
constructed elsewhere.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]

/-! ## The relative sets of the subspace worlds -/

/-- The part of the bottom copy lying in `↥(cylPre q V)` — the relative set of the subspace world
over `V`. -/
def cylPreBot (q : C(X, Γ)) (V : Set Γ) : Set ↥(Work.Serre.cylPre q V) :=
  {x | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q}

/-- The part of `↥(cylPre q V)` lying over `S` (so that, for `S ⊆ V`, the pair
`(cylPreSub q V S, cylPreBot q V ∩ cylPreSub q V S)` is the subspace world of `q|_S`). -/
def cylPreSub (q : C(X, Γ)) (V S : Set Γ) : Set ↥(Work.Serre.cylPre q V) :=
  {x | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}

/-- The base map of the pair over `S`, in the subspace world `↥(cylPreSub q V S)`. -/
def cylPreSubRetract (q : C(X, Γ)) (V S : Set Γ) : C(↥(cylPreSub q V S), ↥S) where
  toFun x := ⟨Work.Serre.cylRetract q ((x : ↥(cylPreSub q V S)) : ↥(Work.Serre.cylPre q V)),
    (x : ↥(cylPreSub q V S)).2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.comp (Work.Serre.cylRetract q).continuous
      (Continuous.comp continuous_subtype_val continuous_subtype_val)) _

/-- The relative set of the pair over `S` in the subspace world `↥(cylPreSub q V S)`. -/
def cylPreSubBot (q : C(X, Γ)) (V S : Set Γ) : Set ↥(cylPreSub q V S) :=
  {x | (x : ↥(cylPre q V)) ∈ cylPreBot q V ∩ cylPreSub q V S}

/-- **The canonical homeomorphism `↥(cylPre q S) ≃ₜ ↥(cylPreSub q V S)`** for `S ⊆ V`: both are the
same set of points of the mapping cylinder, read in the two ambients. -/
def cylPreSubHomeo (q : C(X, Γ)) (V S : Set Γ) (hSV : S ⊆ V) :
    ↥(Work.Serre.cylPre q S) ≃ₜ ↥(cylPreSub q V S) where
  toFun y := ⟨⟨(y : Work.Serre.cyl q), hSV y.2⟩, y.2⟩
  invFun x := ⟨(x : ↥(cylPreSub q V S)).1.1, (x : ↥(cylPreSub q V S)).2⟩
  left_inv y := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## The subspace-world predicate -/

/-- **The subspace world of `Work.Serre.ThomCylAt`.**  For a space `T`, a relative set `A ⊆ T` and a
base map `π : C(T,B)`, `ThomSubAt r N A π` says that there is a class `U ∈ H^{r+1}(T,A;ℚ)` whose
mixed cup product with the pullback along `π` is an isomorphism in the range `m + r + 1 ≤ N + 1`.
For `T = ↥(cylPre q V)`, `A = cylPreBot q V`, `π = cylPreRetract q V` this is the subspace form of
`Work.Serre.ThomCylAt r N (restrictFibre q V)`. -/
def ThomSubAt {B T : Type} [TopologicalSpace B] [TopologicalSpace T]
    (r N : ℕ) (A : Set T) (π : C(T, B)) : Prop :=
  ∃ U : Work.Thom.RelCoh ℚ (r + 1) T A, ∀ m : ℕ, m + r + 1 ≤ N + 1 →
    CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ A m (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap π ℚ m).hom))

/-! ## The homeomorphism of the restricted mapping cylinder and the retraction -/

/-- **The retraction is compatible with the identification of the restricted mapping cylinder.**
On the presenting disjoint unions both sides are `q` (resp. the identity) on the two summands. -/
theorem cylRetract_cylPreimageLift_qS (q : C(X, Γ)) (S : Set Γ)
    (x : Work.Serre.cyl (qS q S)) :
    Work.Serre.cylRetract q (cylPreimageLift q S x : Work.Serre.cyl q) =
      ((Work.Serre.cylRetract (qS q S) x : ↥S) : Γ) := by
  induction x using Quotient.inductionOn with
  | h a =>
    rw [cylPreimageLift_mk q S a]
    cases a with
    | inl z => simp only [cylPreimageFun_inl]; rfl
    | inr y => simp only [cylPreimageFun_inr]; rfl

/-! ## The transfer of the Thom cup property between the subspace world and the cylinder world -/

/-- **`ThomSubAt` and `Work.Serre.ThomCylAt` agree.**  If `e` is a homeomorphism from the mapping
cylinder of `q|_S` onto `T` which matches the bottom copies (`hbot`) and the retractions (`hret`),
then the Thom cup property for `q|_S` (with base `↥S` and the retraction `cylRetract (qS q S)`) is
equivalent to the subspace-world statement for `(T, A, π)`.

The proof is the naturality of the mixed cup product along `e` (and `e.symm`), together with the
fact that the pullback along a homeomorphism of pairs is an isomorphism
(`Work.Thom.CapGlue.isIso_relComplexMap_homeomorph`). -/
theorem thomSubAt_iff_thomCylAt_qS (q : C(X, Γ)) (S : Set Γ) (r N : ℕ)
    {T : Type} [TopologicalSpace T] (A : Set T) (π : C(T, ↥S))
    (e : Work.Serre.cyl (qS q S) ≃ₜ T)
    (hbot : ∀ y, y ∈ Set.range (Work.Serre.cylIncl (qS q S)) ↔ e y ∈ A)
    (hret : ∀ y, π (e y) = Work.Serre.cylRetract (qS q S) y) :
    Work.Serre.ThomCylAt r N (qS q S) ↔ ThomSubAt r N A π := by
  classical
  have hsym : ∀ x : T, x ∈ A ↔ e.symm x ∈ Set.range (Work.Serre.cylIncl (qS q S)) := by
    intro x
    rw [hbot (e.symm x), e.apply_symm_apply]
  have hcomp₁ : (Work.Serre.cylRetract (qS q S)).comp
      (e.symm : C(T, Work.Serre.cyl (qS q S))) = π := by
    ext y
    show (((Work.Serre.cylRetract (qS q S)) (e.symm y) : ↥S) : Γ) = ((π y : ↥S) : Γ)
    exact (congrArg Subtype.val (hret (e.symm y))).symm.trans
      (congrArg (fun w => ((π w : ↥S) : Γ)) (e.apply_symm_apply y))
  have hcomp₂ : π.comp (e : C(Work.Serre.cyl (qS q S), T))
      = Work.Serre.cylRetract (qS q S) := by
    ext y
    show ((π (e y) : ↥S) : Γ) = (((Work.Serre.cylRetract (qS q S)) y : ↥S) : Γ)
    exact congrArg Subtype.val (hret y)
  have hCoh₁ : ∀ (m : ℕ) (x : Work.Thom.Coh ℚ m ↥S),
      (Work.Thom.CohMap (e.symm : C(T, Work.Serre.cyl (qS q S))) ℚ m).hom
        ((Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x)
      = (Work.Thom.CohMap π ℚ m).hom x := by
    intro m x
    have h1 : (Work.Thom.CohMap (e.symm : C(T, Work.Serre.cyl (qS q S))) ℚ m).hom
          ((Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x)
        = (Work.Thom.CohMap ((Work.Serre.cylRetract (qS q S)).comp
            (e.symm : C(T, Work.Serre.cyl (qS q S)))) ℚ m).hom x := by
      rw [Work.Thom.CohMap_comp (f := (e.symm : C(T, Work.Serre.cyl (qS q S))))
        (g := Work.Serre.cylRetract (qS q S))]
      rfl
    rw [h1, hcomp₁]
  have hCoh₂ : ∀ (m : ℕ) (x : Work.Thom.Coh ℚ m ↥S),
      (Work.Thom.CohMap (e : C(Work.Serre.cyl (qS q S), T)) ℚ m).hom
        ((Work.Thom.CohMap π ℚ m).hom x)
      = (Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x := by
    intro m x
    have h1 : (Work.Thom.CohMap (e : C(Work.Serre.cyl (qS q S), T)) ℚ m).hom
          ((Work.Thom.CohMap π ℚ m).hom x)
        = (Work.Thom.CohMap (π.comp (e : C(Work.Serre.cyl (qS q S), T))) ℚ m).hom x := by
      rw [Work.Thom.CohMap_comp (f := (e : C(Work.Serre.cyl (qS q S), T))) (g := π)]
      rfl
    rw [h1, hcomp₂]
  constructor
  · rintro ⟨U, hU⟩
    have hf : ∀ x ∈ A, (e.symm : C(T, Work.Serre.cyl (qS q S))) x
        ∈ Set.range (Work.Serre.cylIncl (qS q S)) := fun x hx => (hsym x).mp hx
    set U' : Work.Thom.RelCoh ℚ (r + 1) T A :=
      (Work.Thom.relCohMap (e.symm : C(T, Work.Serre.cyl (qS q S))) A
        (Set.range (Work.Serre.cylIncl (qS q S))) hf ℚ (r + 1)).hom U with hU'def
    refine ⟨U', ?_⟩
    intro m hm
    have hIrel : IsIso (Work.Thom.relCohMap (e.symm : C(T, Work.Serre.cyl (qS q S))) A
        (Set.range (Work.Serre.cylIncl (qS q S))) hf ℚ (m + (r + 1))) :=
      Work.Thom.CapGlue.isIso_relComplexMap_homeomorph A
        (Set.range (Work.Serre.cylIncl (qS q S))) e.symm hsym ℚ (m + (r + 1))
    set rl : Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl (qS q S))
        (Set.range (Work.Serre.cylIncl (qS q S))) → Work.Thom.RelCoh ℚ (m + (r + 1)) T A :=
      fun y => (Work.Thom.relCohMap (e.symm : C(T, Work.Serre.cyl (qS q S))) A
        (Set.range (Work.Serre.cylIncl (qS q S))) hf ℚ (m + (r + 1))).hom y with hrl
    set G : Work.Thom.Coh ℚ m ↥S → Work.Thom.RelCoh ℚ (m + (r + 1))
        (Work.Serre.cyl (qS q S)) (Set.range (Work.Serre.cylIncl (qS q S))) :=
      fun x => (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (qS q S))) m (r + 1))
        ((Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x) U with hG
    set F : Work.Thom.Coh ℚ m ↥S → Work.Thom.RelCoh ℚ (m + (r + 1)) T A :=
      fun x => (Work.Thom.mixedCupC ℚ A m (r + 1)) ((Work.Thom.CohMap π ℚ m).hom x) U'
      with hF
    have hkey : ∀ x, rl (G x) = F x := by
      intro x
      simp only [hrl, hG, hF, hU'def]
      rw [← hCoh₁ m x]
      exact Work.StemsB.mixedCupC_pairNaturalR ℚ (e.symm : C(T, Work.Serre.cyl (qS q S))) A
        (Set.range (Work.Serre.cylIncl (qS q S))) hf m (r + 1)
        ((Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x) U
    have hGbij : Function.Bijective G := by
      simp only [hG]
      exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp (hU m hm)
    have hrlbij : Function.Bijective rl := by
      simp only [hrl]
      exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hIrel
    rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
    show Function.Bijective F
    rw [show F = rl ∘ G from funext (fun x => (hkey x).symm)]
    exact hrlbij.comp hGbij
  · rintro ⟨U', hU'⟩
    have hf : ∀ y ∈ Set.range (Work.Serre.cylIncl (qS q S)),
        (e : C(Work.Serre.cyl (qS q S), T)) y ∈ A := fun y hy => (hbot y).mp hy
    set U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (qS q S))
        (Set.range (Work.Serre.cylIncl (qS q S))) :=
      (Work.Thom.relCohMap (e : C(Work.Serre.cyl (qS q S), T))
        (Set.range (Work.Serre.cylIncl (qS q S))) A hf ℚ (r + 1)).hom U' with hUdef
    refine ⟨U, ?_⟩
    intro m hm
    have hIrel : IsIso (Work.Thom.relCohMap (e : C(Work.Serre.cyl (qS q S), T))
        (Set.range (Work.Serre.cylIncl (qS q S))) A hf ℚ (m + (r + 1))) :=
      Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
        (Set.range (Work.Serre.cylIncl (qS q S))) A e hbot ℚ (m + (r + 1))
    set rl : Work.Thom.RelCoh ℚ (m + (r + 1)) T A →
        Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl (qS q S))
          (Set.range (Work.Serre.cylIncl (qS q S))) :=
      fun y => (Work.Thom.relCohMap (e : C(Work.Serre.cyl (qS q S), T))
        (Set.range (Work.Serre.cylIncl (qS q S))) A hf ℚ (m + (r + 1))).hom y with hrl
    set F : Work.Thom.Coh ℚ m ↥S → Work.Thom.RelCoh ℚ (m + (r + 1)) T A :=
      fun x => (Work.Thom.mixedCupC ℚ A m (r + 1)) ((Work.Thom.CohMap π ℚ m).hom x) U'
      with hF
    set G : Work.Thom.Coh ℚ m ↥S → Work.Thom.RelCoh ℚ (m + (r + 1))
        (Work.Serre.cyl (qS q S)) (Set.range (Work.Serre.cylIncl (qS q S))) :=
      fun x => (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (qS q S))) m (r + 1))
        ((Work.Thom.CohMap (Work.Serre.cylRetract (qS q S)) ℚ m).hom x) U with hG
    have hkey : ∀ x, rl (F x) = G x := by
      intro x
      simp only [hrl, hF, hG, hUdef]
      rw [← hCoh₂ m x]
      exact Work.StemsB.mixedCupC_pairNaturalR ℚ (e : C(Work.Serre.cyl (qS q S), T))
        (Set.range (Work.Serre.cylIncl (qS q S))) A hf m (r + 1)
        ((Work.Thom.CohMap π ℚ m).hom x) U'
    have hFbij : Function.Bijective F := by
      simp only [hF]
      exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp (hU' m hm)
    have hrlbij : Function.Bijective rl := by
      simp only [hrl]
      exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hIrel
    rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
    show Function.Bijective G
    rw [show G = rl ∘ F from funext (fun x => (hkey x).symm)]
    exact hrlbij.comp hFbij

/-- **`ThomSubAt` and `Work.Serre.ThomCylAt` agree** (the `restrictFibre` form). -/
theorem thomSubAt_iff_thomCylAt (q : C(X, Γ)) (S : Set Γ) (r N : ℕ)
    {T : Type} [TopologicalSpace T] (A : Set T) (π : C(T, ↥S))
    (e : Work.Serre.cyl (Work.Serre.restrictFibre q S) ≃ₜ T)
    (hbot : ∀ y, y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)) ↔ e y ∈ A)
    (hret : ∀ y, π (e y) = Work.Serre.cylRetract (Work.Serre.restrictFibre q S) y) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S) ↔ ThomSubAt r N A π :=
  thomSubAt_iff_thomCylAt_qS q S r N A π e hbot hret

/-! ## The absolute restriction map of a pair -/

/-- **The restriction `H^n(X;R) → H^n(A;R)` is an isomorphism as soon as the relative groups
`H^n(X,A;R)` and `H^{n+1}(X,A;R)` vanish.**  This is the piece
`H^n(X,A) → H^n(X) → H^n(A) → H^{n+1}(X,A)` of the long exact sequence of the pair: the first map
is zero (its source is zero), so the middle one is injective, and the last one is zero (its target
is zero), so it is surjective. -/
theorem isIso_restrCoh_of_relCoh_isZero {B : Type} [TopologicalSpace B] (A : Set B) (n : ℕ)
    (h₁ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n B A))
    (h₂ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (n + 1) B A)) :
    CategoryTheory.IsIso (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, B)) ℚ n) := by
  have hex₂ := Work.Cohomology.pair_exact₂ ℚ (TopCat.of B) A n
  have hmono : Mono (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (TopCat.of B) A) n) :=
    (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src h₁ _)).mp hex₂
  have hex₃ := Work.Cohomology.pair_exact₃ ℚ (TopCat.of B) A n
  have hepi : Epi (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (TopCat.of B) A) n) :=
    (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt h₂ _)).mp hex₃
  haveI := hmono
  haveI := hepi
  have hmain : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (TopCat.of B) A) n) :=
    isIso_of_mono_of_epi _
  exact hmain

end

end Work.Serre.DiscPair
