import Mathlib
import Submission.Work.RatHurewicz.cupBijectiveOverPiece
import Submission.Work.Serre.bijective_mixedCup_of_openCover_zero
import Submission.Work.Serre.MVGlue.glueCupIso
import Submission.Work.Serre.MVGlue.mvDeltaCupMixed
import Submission.Work.RatHurewicz.bijective_mixedCup_of_homeo
import Submission.Work.RatHurewicz.zero_bijective_mixedCup_of_disjoint_pair

/-!
# The cup isomorphism over a finite disjoint union of pieces

This file proves `Work.RatHurewicz.cupBijective_cylPre_iUnion`: for a Serre fibration `q` with
rationally spherical fibres in the range, and a *pairwise disjoint* finite family of open
weakly contractible pieces `V i` of the base, the mixed cup product with the restriction of a
non-zero relative class `U` is bijective over the part of the mapping cylinder over `⋃ i, V i`.

The proof glues the local statement `Work.RatHurewicz.cupBijective_cylPre` over the finite disjoint
family.  The Mayer--Vietoris gluing is `Work.Serre.MVGlue.glueCupIso`, and the *only* extra input it
needs is the Mayer--Vietoris boundary square `hdelta`; over a **disjoint** cover the overlap
`U ∩ V` is empty, so in every degree the overlap term vanishes and `hdelta` is trivial.  Since the
pieces of the cover in the induction step are not literally the pieces over which the local
statement is known, we transport the local statements along the canonical homeomorphism
`↥{y : ↥T | (y : Z) ∈ S} ≃ₜ ↥S` (`Work.RatHurewicz.bijective_mixedCup_of_homeo`), and the
degree-zero part of the gluing is `Work.RatHurewicz.zero_bijective_mixedCup_of_disjoint_pair`
(the overlap term vanishes, which is what makes `mvF` injective there).
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Abbreviations and canonical inclusions -/

/-- The trace of a set `A ⊆ Z` on a subset `T ⊆ Z`, read as a subset of `↥T`. -/
abbrev subSet {Z : Type} (A T : Set Z) : Set ↥T := {y | (y : Z) ∈ A}

/-- The canonical inclusion `↥(subSet S T) → ↥T`. -/
abbrev subInclST {Z : Type} [TopologicalSpace Z] (S T : Set Z) :
    C(↥(subSet S T), ↥T) :=
  ⟨(Subtype.val : ↥(subSet S T) → ↥T), continuous_subtype_val⟩

/-- The canonical inclusion `↥T → Z`. -/
abbrev subInclT {Z : Type} [TopologicalSpace Z] (T : Set Z) : C(↥T, Z) :=
  ⟨(Subtype.val : ↥T → Z), continuous_subtype_val⟩

/-- The canonical inclusion `↥(subSet S T) → Z`. -/
abbrev subInclSZ {Z : Type} [TopologicalSpace Z] (S T : Set Z) :
    C(↥(subSet S T), Z) := (subInclT T).comp (subInclST S T)

/-- **The canonical homeomorphism `↥{y : ↥T | (y : Z) ∈ S} ≃ₜ ↥S`** for `S ⊆ T`. -/
def subHomeo {Z : Type} [TopologicalSpace Z] (S T : Set Z) (hST : S ⊆ T) :
    ↥(subSet S T) ≃ₜ ↥S where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, hST z.2⟩, z.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The union of the pieces of a finite family indexed by a finset. -/
def Wt {Z : Type} {ι : Type} (W : ι → Set Z) (t : Finset ι) : Set Z := ⋃ i ∈ t, W i

theorem mem_Wt {Z : Type} {ι : Type} {W : ι → Set Z} {z : Z} {t : Finset ι} :
    z ∈ Wt W t ↔ ∃ i ∈ t, z ∈ W i := by
  simp only [Wt, Set.mem_iUnion, exists_prop]

theorem Wt_empty {Z : Type} {ι : Type} (W : ι → Set Z) : Wt W (∅ : Finset ι) = ∅ := by
  ext z; simp [mem_Wt]

theorem Wt_insert {Z : Type} {ι : Type} [DecidableEq ι] (W : ι → Set Z) (a : ι)
    (t : Finset ι) : Wt W (insert a t) = W a ∪ Wt W t := by
  ext z
  simp only [mem_Wt, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨i, rfl | hit, hzi⟩
    · exact Or.inl hzi
    · exact Or.inr ⟨i, hit, hzi⟩
  · rintro (hz | ⟨i, hit, hzi⟩)
    · exact ⟨a, Or.inl rfl, hz⟩
    · exact ⟨i, Or.inr hit, hzi⟩

theorem isOpen_Wt {Z : Type} [TopologicalSpace Z] {ι : Type} [DecidableEq ι] {W : ι → Set Z}
    (hWo : ∀ i, IsOpen (W i)) (t : Finset ι) : IsOpen (Wt W t) := by
  induction t using Finset.induction_on with
  | empty => rw [Wt_empty]; exact isOpen_empty
  | insert a t ha ih => rw [Wt_insert]; exact (hWo a).union ih

theorem Wt_subset_insert {Z : Type} {ι : Type} [DecidableEq ι] (W : ι → Set Z) (a : ι)
    (t : Finset ι) : Wt W t ⊆ Wt W (insert a t) := by
  rw [Wt_insert]; exact Set.subset_union_right

theorem singleton_subset_Wt {Z : Type} {ι : Type} [DecidableEq ι] (W : ι → Set Z) (a : ι)
    (t : Finset ι) : W a ⊆ Wt W (insert a t) := by
  rw [Wt_insert]; exact Set.subset_union_left

theorem disjoint_Wt_singleton {Z : Type} {ι : Type} [DecidableEq ι] {W : ι → Set Z}
    (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j)) {a : ι} {t : Finset ι} (ha : a ∉ t) :
    Disjoint (Wt W t) (W a) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨i, hit, hzi⟩ := mem_Wt.mp hz
  exact Set.disjoint_left.mp (hWd i a (fun h => ha (h ▸ hit))) hzi hz'

/-! ## The two spellings of the restriction of a class to a sub-ambient -/

theorem relCohMap_restrict_comp {Z : Type} [TopologicalSpace Z] (A S T : Set Z) (hST : S ⊆ T)
    (n : ℕ) (U₀ : Work.Thom.RelCoh ℚ n Z A) :
    (Work.Thom.relCohMap (subInclST S T)
        (subSet (subSet A T) (subSet S T)) (subSet A T) (fun _ hy => hy) ℚ n).hom
      ((Work.Thom.relCohMap (subInclT T) (subSet A T) A (fun _ hy => hy) ℚ n).hom U₀)
    = (Work.Thom.relCohMap (subInclSZ S T)
        (subSet (subSet A T) (subSet S T)) A (fun _ hy => hy) ℚ n).hom U₀ := by
  exact Work.Thom.relCohMap_compA_apply (subSet (subSet A T) (subSet S T)) (subSet A T) A
    (subInclST S T) (subInclT T) (fun _ hy => hy) (fun _ hy => hy) (fun _ hy => hy) ℚ n U₀

/-! ## Transport of the cup bijectivity to a sub-ambient -/

/-- **The cup bijectivity restricted to a sub-ambient.**  If for all admissible `m` the mixed cup
product with the restriction of `U₀` to `↥S` is bijective, then the same holds over
`↥(subSet S T)` (`T ⊇ S`) with the class obtained by first restricting to `↥T` and then pulling back
along the canonical homeomorphism: both spellings are the restriction of `U₀` to the pair over
`↥(subSet S T)`. -/
theorem bijective_cup_subSet {Z : Type} [TopologicalSpace Z] (A S T : Set Z) (hST : S ⊆ T)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A)
    (hb : ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥S =>
      (Work.Thom.mixedCupC ℚ (subSet A S) m n₀) x
        ((Work.Thom.relCohMap (subInclT S) (subSet A S) A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(subSet S T) =>
      (Work.Thom.mixedCupC ℚ (subSet (subSet A T) (subSet S T)) m n₀) x
        ((Work.Thom.relCohMap (subInclST S T) (subSet (subSet A T) (subSet S T)) (subSet A T)
            (fun _ hy => hy) ℚ n₀).hom
          ((Work.Thom.relCohMap (subInclT T) (subSet A T) A (fun _ hy => hy) ℚ n₀).hom U₀))) := by
  have he : ∀ y : ↥(subSet S T),
      y ∈ subSet (subSet A T) (subSet S T) ↔
        (subHomeo S T hST : C(↥(subSet S T), ↥S)) y ∈ subSet A S := fun y => Iff.rfl
  intro m hm
  have hb' := bijective_mixedCup_of_homeo (subHomeo S T hST)
    (subSet (subSet A T) (subSet S T)) (subSet A S) he m n₀
    ((Work.Thom.relCohMap (subInclT S) (subSet A S) A (fun _ hy => hy) ℚ n₀).hom U₀) (hb m hm)
  have hside : ((Work.Thom.relCohMap (subHomeo S T hST : C(↥(subSet S T), ↥S))
        (subSet (subSet A T) (subSet S T)) (subSet A S) (fun x hx => (he x).mp hx) ℚ n₀).hom
      ((Work.Thom.relCohMap (subInclT S) (subSet A S) A (fun _ hy => hy) ℚ n₀).hom U₀))
    = ((Work.Thom.relCohMap (subInclST S T) (subSet (subSet A T) (subSet S T)) (subSet A T)
          (fun _ hy => hy) ℚ n₀).hom
        ((Work.Thom.relCohMap (subInclT T) (subSet A T) A (fun _ hy => hy) ℚ n₀).hom U₀)) := by
    rw [Work.Thom.relCohMap_compA_apply (subSet (subSet A T) (subSet S T)) (subSet A S) A
      (subHomeo S T hST : C(↥(subSet S T), ↥S)) (subInclT S) (fun x hx => (he x).mp hx)
      (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀,
      relCohMap_restrict_comp A S T hST n₀ U₀]
    have hmap : (subInclT S).comp (subHomeo S T hST : C(↥(subSet S T), ↥S)) =
        subInclSZ S T := ContinuousMap.ext fun y => rfl
    exact congrArg (fun φ => φ.hom U₀) (Work.Thom.relCohMap_congrA
      (subSet (subSet A T) (subSet S T)) A hmap
      (fun _ hy => hy) (fun _ hy => hy) ℚ n₀)
  rw [hside] at hb'
  exact hb'

/-! ## The gluing step over two disjoint pieces -/

/-- **The gluing step over a cover by two disjoint open sets, in every degree.**  If the mixed cup
product with the restriction of `U₀` is bijective over both pieces, it is bijective over the whole
space (in all degrees `m` with `m + n₀ ≤ K`, including `m = 0`).

For `m ≥ 1` this is `Work.Serre.MVGlue.glueCupIso` with the trivial boundary square
`mvDeltaCupMixed_of_disjoint`; for `m = 0` it is
`Work.RatHurewicz.zero_bijective_mixedCup_of_disjoint_pair`. -/
theorem bijective_mixedCup_of_disjoint_pair {Z : Type} [TopologicalSpace Z]
    (A Uc Vc : Set Z) (hUo : IsOpen Uc) (hVo : IsOpen Vc) (hcov : Uc ∪ Vc = Set.univ)
    (hdisj : Disjoint Uc Vc) (n₀ K : ℕ) (hn₀ : 0 < n₀) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A)
    (hlocU : ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥Uc =>
      (Work.Thom.mixedCupC ℚ (subSet A Uc) m n₀) x
        ((Work.Thom.relCohMap (subInclT Uc) (subSet A Uc) A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥Vc =>
      (Work.Thom.mixedCupC ℚ (subSet A Vc) m n₀) x
        ((Work.Thom.relCohMap (subInclT Vc) (subSet A Vc) A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m Z =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) := by
  intro m hm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact zero_bijective_mixedCup_of_disjoint_pair A Uc Vc hUo hVo hcov hdisj n₀ hn₀ U₀
      (hlocU 0 (by omega)) (hlocV 0 (by omega))
  · refine Work.Serre.MVGlue.glueCupIso A Uc Vc hUo hVo hcov n₀ K U₀ ?hdelta hlocU hlocV
      ?hlocUV m hmpos hm
    case hdelta =>
      intro m' x
      haveI hEm : IsEmpty ↥(Uc ∩ Vc) :=
        ⟨fun y => Set.disjoint_left.mp hdisj y.2.1 y.2.2⟩
      haveI hEm2 : IsEmpty ↥{x : ↥(Uc ∩ Vc) | (x : Z) ∈ (∅ : Set Z)} :=
        ⟨fun y => isEmptyElim y.1⟩
      haveI hsub : Subsingleton (Work.Serre.mvCohUV (TopCat.of Z) (∅ : Set Z) Uc Vc m') :=
        ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ m')
      rw [Subsingleton.elim x 0]
      simp
    case hlocUV =>
      intro m' hm'
      haveI hEm : IsEmpty ↥(Uc ∩ Vc) :=
        ⟨fun y => Set.disjoint_left.mp hdisj y.2.1 y.2.2⟩
      haveI hC : Subsingleton ↥(Work.Thom.Coh ℚ m' ↥(Uc ∩ Vc)) :=
        ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_coh_of_isEmpty_space m')
      haveI hR : Subsingleton ↥(Work.Thom.RelCoh ℚ (m' + n₀) ↥(Uc ∩ Vc)
          {y : ↥(Uc ∩ Vc) | (y : Z) ∈ A}) :=
        ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)
      exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-! ## The finite disjoint union -/

/-- **The induction over the finite family**: the cup bijectivity over the union of the pieces of a
finset of indices. -/
theorem bijective_mixedCup_Wt {Z : Type} [TopologicalSpace Z] {ι : Type} [DecidableEq ι]
    (A : Set Z) (n₀ K : ℕ) (hn₀ : 0 < n₀) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A) (W : ι → Set Z)
    (hWo : ∀ i, IsOpen (W i)) (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hloc : ∀ i, ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(W i) =>
        (Work.Thom.mixedCupC ℚ (subSet A (W i)) m n₀) x
          ((Work.Thom.relCohMap (subInclT (W i)) (subSet A (W i)) A
            (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ t : Finset ι, ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(Wt W t) =>
        (Work.Thom.mixedCupC ℚ (subSet A (Wt W t)) m n₀) x
          ((Work.Thom.relCohMap (subInclT (Wt W t)) (subSet A (Wt W t)) A
            (fun _ hy => hy) ℚ n₀).hom U₀)) := by
  intro t
  refine Finset.induction_on t ?base ?step
  case base =>
    intro m hm
    haveI hEm : IsEmpty ↥(Wt W (∅ : Finset ι)) := by rw [Wt_empty]; exact ⟨fun x => x.2⟩
    haveI hC : Subsingleton ↥(Work.Thom.Coh ℚ m ↥(Wt W ∅)) :=
      ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_coh_of_isEmpty_space m)
    haveI hR : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + n₀) ↥(Wt W ∅) (subSet A (Wt W ∅))) :=
      ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩
  case step =>
    intro a t ha ih m hm
    let X := ↥(Wt W (insert a t))
    let Uc : Set X := subSet (Wt W t) (Wt W (insert a t))
    let Vc : Set X := subSet (W a) (Wt W (insert a t))
    let Ac : Set X := subSet A (Wt W (insert a t))
    let U₀X : Work.Thom.RelCoh ℚ n₀ X Ac :=
      (Work.Thom.relCohMap (subInclT (Wt W (insert a t))) Ac A (fun _ hy => hy) ℚ n₀).hom U₀
    have hUo : IsOpen Uc :=
      (isOpen_Wt hWo t).preimage (subInclT (Wt W (insert a t))).continuous
    have hVo : IsOpen Vc :=
      (hWo a).preimage (subInclT (Wt W (insert a t))).continuous
    have hcov : Uc ∪ Vc = Set.univ := by
      ext y
      constructor
      · intro _; exact trivial
      · intro _
        have hy : (y : Z) ∈ W a ∪ Wt W t := by rw [← Wt_insert]; exact y.2
        rcases hy with hy | hy
        · exact Or.inr hy
        · exact Or.inl hy
    have hdisj : Disjoint Uc Vc := by
      rw [Set.disjoint_left]
      intro y hy hy'
      exact Set.disjoint_left.mp (disjoint_Wt_singleton hWd ha) hy hy'
    have hlocU : ∀ m' : ℕ, m' + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m' ↥Uc =>
        (Work.Thom.mixedCupC ℚ (subSet Ac Uc) m' n₀) x
          ((Work.Thom.relCohMap (subInclT Uc) (subSet Ac Uc) Ac
            (fun _ hy => hy) ℚ n₀).hom U₀X)) :=
      fun m' hm' => bijective_cup_subSet A (Wt W t) (Wt W (insert a t))
        (Wt_subset_insert W a t) n₀ K U₀ (fun m'' hm'' => ih m'' hm'') m' hm'
    have hlocV : ∀ m' : ℕ, m' + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m' ↥Vc =>
        (Work.Thom.mixedCupC ℚ (subSet Ac Vc) m' n₀) x
          ((Work.Thom.relCohMap (subInclT Vc) (subSet Ac Vc) Ac
            (fun _ hy => hy) ℚ n₀).hom U₀X)) :=
      fun m' hm' => bijective_cup_subSet A (W a) (Wt W (insert a t))
        (singleton_subset_Wt W a t) n₀ K U₀ (fun m'' hm'' => hloc a m'' hm'') m' hm'
    exact bijective_mixedCup_of_disjoint_pair Ac Uc Vc hUo hVo hcov hdisj n₀ K hn₀ U₀X
      hlocU hlocV m hm

/-- **The cup bijectivity over a finite pairwise disjoint family of open pieces.** -/
theorem bijective_mixedCup_iUnion {Z : Type} [TopologicalSpace Z] {ι : Type} [Fintype ι]
    (A : Set Z) (n₀ K : ℕ) (hn₀ : 0 < n₀) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A) (W : ι → Set Z)
    (hWo : ∀ i, IsOpen (W i)) (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hloc : ∀ i, ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(W i) =>
        (Work.Thom.mixedCupC ℚ (subSet A (W i)) m n₀) x
          ((Work.Thom.relCohMap (subInclT (W i)) (subSet A (W i)) A
            (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(⋃ i, W i) =>
        (Work.Thom.mixedCupC ℚ (subSet A (⋃ i, W i)) m n₀) x
          ((Work.Thom.relCohMap (subInclT (⋃ i, W i)) (subSet A (⋃ i, W i)) A
            (fun _ hy => hy) ℚ n₀).hom U₀)) := by
  classical
  have h := bijective_mixedCup_Wt A n₀ K hn₀ U₀ W hWo hWd hloc Finset.univ
  have hun : Wt W (Finset.univ : Finset ι) = ⋃ i, W i := by
    ext z; simp [mem_Wt]
  rw [← hun]
  exact h

/-! ## The target -/

theorem cupBijective_cylPre_iUnion (r N : ℕ) (hr : 1 ≤ r)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ)
    {X : Type} [TopologicalSpace X] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
      ≅ ModuleCat.of ℚ ℚ))
    {ι : Type} [Fintype ι] (V : ι → Set Γ)
    (hVopen : ∀ i, IsOpen (V i))
    (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hVc : ∀ i, ∃ b₀ : ↥(V i), ∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥(V i) b₀))
    (hVpc : ∀ i, PathConnectedSpace ↥(V i))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Work.Serre.cylBot q))
    (hU : U ≠ 0) :
    ∀ m : ℕ, 1 ≤ m → m + r + 1 ≤ N + 1 →
      Function.Bijective (fun x : Work.Thom.Coh ℚ m
          ↥((Work.Serre.cylRetract q) ⁻¹' (⋃ i, V i)) =>
        (Work.Thom.mixedCupC ℚ
          {y : ↥((Work.Serre.cylRetract q) ⁻¹' (⋃ i, V i)) |
            (y : Work.Serre.cyl q) ∈ Work.Serre.cylBot q} m (r + 1)) x
          ((Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥((Work.Serre.cylRetract q) ⁻¹' (⋃ i, V i)), Work.Serre.cyl q))
            {y : ↥((Work.Serre.cylRetract q) ⁻¹' (⋃ i, V i)) |
              (y : Work.Serre.cyl q) ∈ Work.Serre.cylBot q}
            (Work.Serre.cylBot q) (fun x hx => hx) ℚ (r + 1)).hom U)) := by
  classical
  intro m hm hK
  let W : ι → Set (Work.Serre.cyl q) := fun i => Work.Serre.cylPre q (V i)
  have hWo : ∀ i, IsOpen (W i) := fun i =>
    (hVopen i).preimage (Work.Serre.cylRetract q).continuous
  have hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hz hz'
    exact Set.disjoint_left.mp (hVdisj i j hij) hz hz'
  have hloc : ∀ i, ∀ m' : ℕ, m' + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m' ↥(W i) =>
        (Work.Thom.mixedCupC ℚ (subSet (Work.Serre.cylBot q) (W i)) m' (r + 1)) x
          ((Work.Thom.relCohMap (subInclT (W i)) (subSet (Work.Serre.cylBot q) (W i))
            (Work.Serre.cylBot q) (fun _ hy => hy) ℚ (r + 1)).hom U)) := by
    intro i m' hm'
    obtain ⟨b₀, hc₀⟩ := hVc i
    simpa only [W, Work.Serre.DiscPair.cylPreBot, subSet]
      using Work.RatHurewicz.cupBijective_cylPre (r := r) (N := N) hr (Γ := Γ) hΓ
        (X := X) q hq hpc hvan hgen (V := V i) (hVopen i) b₀ hc₀ (hVpc i) U hU m' hm'
  have h := bijective_mixedCup_iUnion (Z := Work.Serre.cyl q) (A := Work.Serre.cylBot q)
      (n₀ := r + 1) (K := N + 1) (by omega) U W hWo hWd hloc m (by omega)
  have hun : (⋃ i, W i) = (Work.Serre.cylRetract q) ⁻¹' (⋃ i, V i) := by
    rw [Set.preimage_iUnion]
  rw [hun] at h
  exact h

end

end Work.RatHurewicz
