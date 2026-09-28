import Mathlib
import Submission.Work.RatHurewicz.SphereThomDefs
import Submission.Work.RatHurewicz.cupBijZeroUnion
import Submission.Work.RatHurewicz.relCohUnionVanish
import Submission.Work.Thom.suspensionStep_bijective_zero

/-!
# The local-to-global gluing of `CvGood` over a finite open cover

`Work.RatHurewicz.CvGood A n₀ K U₀ S` bundles the three properties of a piece `S` that the
local-to-global argument for the sphere case of the CW-model Thom theorem needs:
the mixed cup product with `U₀|_S` is bijective in every degree `m ≥ 1` with `m + n₀ ≤ K`, it is
bijective in degree `0`, and the relative cohomology of `(S, S ∩ A)` vanishes in degrees
`≤ n₀ - 1`.

The main result of this file, `Work.RatHurewicz.cvGoodIUnion`, says that `CvGood` glues over a
finite open cover: if it holds on every nonempty finite intersection `⋂ i ∈ T, W i` of a finite
family of open sets `W i ⊆ Γ`, then it holds on the union `⋃ i, W i` (inside the mapping cylinder
of `q : C(X, Γ)`).

The proof is the standard finite-cover induction.

* The two-piece step `cvUnion_CvGood_union` glues `CvGood` over `Uc ∪ Vc` from `CvGood` over the
  two pieces and their intersection: the positive-degree clause is the Mayer–Vietoris gluing
  `Work.RatHurewicz.cupBij_union_subset`, the degree-`0` clause is the Mayer–Vietoris gluing in
  degree zero `Work.RatHurewicz.cupBijZeroUnion`, and the vanishing clause is
  `Work.RatHurewicz.relCohUnionVanish` (degrees `≥ 1`) together with a degree-`0` vanishing
  from a two-piece cover (proved here as `cvUnion_relCoh_zero_twoPiece`, since only the *relative*
  part of the two-piece degree-`0` statement is needed and no such lemma was available).

* The finite induction `cvUnion_CvGood_finInter` runs over the finite families of *sub*families
  `Family : Finset (Finset ι)` (the piece is `⋃ S ∈ Family, ⋂ i ∈ S, W i`): the new piece is the
  intersection `⋂ i ∈ S₀, W i` and the overlap is again a union of finite intersections, namely
  over the image family `Family'.image (S₀ ∪ ·)`, which is the paradigm of
  `Work.Thom.subsingleton_PieceCoh_iUnion_finInter`.

* Finally the union `⋃ i, W i` is the union of the singleton subfamilies `{i}`, which is how the
  target is reached (`⋂ i ∈ {i}, W i = W i`).
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## Transport of `CvGood` and of the vanishing clause -/

/-- **`CvGood` only depends on the piece through its set.** -/
theorem cvUnion_CvGood_congr_set {X : Type} [TopologicalSpace X] {A : Set X} {n₀ K : ℕ}
    {U₀ : Work.Thom.RelCoh ℚ n₀ X A} {S S' : Set X} (h : S = S')
    (hh : CvGood A n₀ K U₀ S) : CvGood A n₀ K U₀ S' := h ▸ hh

/-- **Vanishing of a relative cohomology group transports across a homeomorphism of pairs.** -/
theorem cvUnion_relCoh_subsingleton_of_homeo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : Set X} {B : Set Y} (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B)
    (j : ℕ) (h : Subsingleton ↥(Work.Thom.RelCoh ℚ j X A)) :
    Subsingleton ↥(Work.Thom.RelCoh ℚ j Y B) := by
  haveI := h
  obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph A B e he ℚ j
  exact ⟨fun a b => iso.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- **Vanishing passes to a sub-ambient**: `H^j(S, S∩A;ℚ) = 0` implies
`H^j(S, S∩A;ℚ) = 0` read inside the ambient space `↥T`, for `S ⊆ T`. -/
theorem cvUnion_relCoh_subsingleton_subSet {Z : Type} [TopologicalSpace Z] (A S T : Set Z)
    (hST : S ⊆ T) (j : ℕ)
    (h : Subsingleton ↥(Work.Thom.RelCoh ℚ j ↥S {y : ↥S | (y : Z) ∈ A})) :
    Subsingleton ↥(Work.Thom.RelCoh ℚ j ↥(subSet S T)
      (subSet (subSet A T) (subSet S T))) :=
  cvUnion_relCoh_subsingleton_of_homeo (subHomeo S T hST).symm (fun _ => Iff.rfl) j h

/-! ## The trivial piece and the empty piece -/

/-- The mixed cup product with any class is bijective over the empty piece. -/
theorem cvUnion_cupBij_empty {X : Type} [TopologicalSpace X] (A : Set X) (n₀ m : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) : CupBij A n₀ U₀ (∅ : Set X) m := by
  haveI : IsEmpty ↥(∅ : Set X) := ⟨fun x => x.2⟩
  haveI h1 : Subsingleton ↥(Work.Thom.Coh ℚ m ↥(∅ : Set X)) :=
    ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_coh_of_isEmpty_space m)
  haveI h2 : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + n₀) ↥(∅ : Set X)
      {y : ↥(∅ : Set X) | (y : X) ∈ A}) :=
    ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)
  exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- The empty piece is `CvGood`. -/
theorem cvUnion_CvGood_empty {X : Type} [TopologicalSpace X] (A : Set X) (n₀ K : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) : CvGood A n₀ K U₀ (∅ : Set X) := by
  refine ⟨fun m _ _ => cvUnion_cupBij_empty A n₀ m U₀, cvUnion_cupBij_empty A n₀ 0 U₀, ?_⟩
  intro k hk
  haveI : IsEmpty ↥(∅ : Set X) := ⟨fun x => x.2⟩
  exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)

/-! ## The degree-zero vanishing over a two-piece cover -/

/-- **Degree-zero vanishing from a two-piece open cover.**  If `H^0(U, U∩A;ℚ)` and
`H^0(V, V∩A;ℚ)` vanish for a cover `U ∪ V = Z` of `Z`, then `H^0(Z, A;ℚ)` vanishes: a class in
`H^0(Z,A)` restricts to zero over both pieces (the restriction factors through the vanishing
groups), hence its image in `H^0(Z)` is zero by the separation property of `H^0`
(`Work.Serre.h0_restrict_eq_zero_of_cover`), and `relToAbs` is injective in degree zero
(`Work.Thom.relToAbs_zero_injective`). -/
theorem cvUnion_relCoh_zero_twoPiece {Z : Type} [TopologicalSpace Z] (A U V : Set Z)
    (hcov : U ∪ V = Set.univ)
    (hUv : Subsingleton ↥(Work.Thom.RelCoh ℚ 0 ↥U {y : ↥U | (y : Z) ∈ A}))
    (hVv : Subsingleton ↥(Work.Thom.RelCoh ℚ 0 ↥V {y : ↥V | (y : Z) ∈ A})) :
    Subsingleton ↥(Work.Thom.RelCoh ℚ 0 Z A) := by
  haveI := hUv
  haveI := hVv
  have hzeroU : ∀ z : Work.Thom.RelCoh ℚ 0 Z A,
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, Z)) ℚ 0).hom
        ((Work.Thom.relToAbs ℚ A 0).hom z) = 0 := by
    intro z
    have hnat := Work.Thom.relCohMap_relToAbs
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, Z))
      {y : ↥U | (y : Z) ∈ A} A (fun _ hy => hy) ℚ 0
    have h2 := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 Z A ⟶ Work.Thom.Coh ℚ 0 ↥U) =>
      φ.hom z) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h2]
    have : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, Z))
        {y : ↥U | (y : Z) ∈ A} A (fun _ hy => hy) ℚ 0).hom z = 0 :=
      Subsingleton.elim _ _
    rw [this, map_zero]
  have hzeroV : ∀ z : Work.Thom.RelCoh ℚ 0 Z A,
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, Z)) ℚ 0).hom
        ((Work.Thom.relToAbs ℚ A 0).hom z) = 0 := by
    intro z
    have hnat := Work.Thom.relCohMap_relToAbs
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, Z))
      {y : ↥V | (y : Z) ∈ A} A (fun _ hy => hy) ℚ 0
    have h2 := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 Z A ⟶ Work.Thom.Coh ℚ 0 ↥V) =>
      φ.hom z) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h2]
    have : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, Z))
        {y : ↥V | (y : Z) ∈ A} A (fun _ hy => hy) ℚ 0).hom z = 0 :=
      Subsingleton.elim _ _
    rw [this, map_zero]
  refine ⟨fun a b => ?_⟩
  have hsub : (Work.Thom.relToAbs ℚ A 0).hom (a - b) = 0 := by
    refine Work.Serre.h0_restrict_eq_zero_of_cover hcov
      ((Work.Thom.relToAbs ℚ A 0).hom (a - b)) ?_ ?_
    · exact hzeroU (a - b)
    · exact hzeroV (a - b)
  have hab : a - b = 0 := Work.Thom.relToAbs_zero_injective ℚ A (by rw [hsub, map_zero])
  exact sub_eq_zero.mp hab

/-! ## The two-piece gluing of `CvGood` -/

/-- **The two-piece gluing.**  If `CvGood` holds over the open sets `Uc`, `Vc` and over their
intersection, then it holds over the union `Uc ∪ Vc`. -/
theorem cvUnion_CvGood_union {X : Type} [TopologicalSpace X] (A : Set X) (n₀ K : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (Uc Vc : Set X) (hUo : IsOpen Uc) (hVo : IsOpen Vc)
    (hU : CvGood A n₀ K U₀ Uc) (hV : CvGood A n₀ K U₀ Vc)
    (hUV : CvGood A n₀ K U₀ (Uc ∩ Vc)) :
    CvGood A n₀ K U₀ (Uc ∪ Vc) := by
  have hlocU : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Uc m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact hU.2.1
    · exact hU.1 m hpos hm
  have hlocV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Vc m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact hV.2.1
    · exact hV.1 m hpos hm
  have hlocUV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ (Uc ∩ Vc) m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact hUV.2.1
    · exact hUV.1 m hpos hm
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hmK
    exact cupBij_union_subset A Uc Vc hUo hVo n₀ K U₀ hlocU hlocV hlocUV m hm hmK
  · exact cupBijZeroUnion A Uc Vc hUo hVo n₀ U₀
      (hU.2.2 (n₀ - 1) le_rfl) (hV.2.2 (n₀ - 1) le_rfl) (hUV.2.2 (n₀ - 1) le_rfl)
      hU.2.1 hV.2.1 hUV.2.1
  · intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      refine cvUnion_relCoh_zero_twoPiece (subSet A (Uc ∪ Vc)) (subSet Uc (Uc ∪ Vc))
        (subSet Vc (Uc ∪ Vc)) ?_ ?_ ?_
      · ext y
        constructor
        · intro _; trivial
        · intro _
          rcases y.2 with hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
      · exact cvUnion_relCoh_subsingleton_subSet A Uc (Uc ∪ Vc) Set.subset_union_left 0
          (hU.2.2 0 (by omega))
      · exact cvUnion_relCoh_subsingleton_subSet A Vc (Uc ∪ Vc) Set.subset_union_right 0
          (hV.2.2 0 (by omega))
    · exact relCohUnionVanish A Uc Vc hUo hVo (n₀ - 1)
        (fun k' hk' => hU.2.2 k' hk') (fun k' hk' => hV.2.2 k' hk')
        (fun k' hk' => hUV.2.2 k' hk') k hpos hk

/-! ## The finite-cover induction -/

/-- The intersection over a union of two finite subfamilies. -/
theorem cvUnion_iInter_union {X : Type} {ι : Type} [DecidableEq ι] (W : ι → Set X)
    (S₀ S : Finset ι) :
    (⋂ i ∈ S₀ ∪ S, W i) = (⋂ i ∈ S₀, W i) ∩ (⋂ i ∈ S, W i) := by
  ext x
  simp only [Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi)
    · exact h1 i hi
    · exact h2 i hi

/-- The union over the family of finitary intersections, with the subfamily `S₀` added to each
member. -/
theorem cvUnion_inter_iUnion_image {X : Type} {ι : Type} [DecidableEq ι] (W : ι → Set X)
    (S₀ : Finset ι) (Family : Finset (Finset ι)) :
    (⋂ i ∈ S₀, W i) ∩ (⋃ S ∈ Family, ⋂ i ∈ S, W i)
      = ⋃ S ∈ Family.image (fun S => S₀ ∪ S), ⋂ i ∈ S, W i := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image, exists_prop]
  constructor
  · rintro ⟨hx, S, hS, hxS⟩
    exact ⟨S₀ ∪ S, ⟨S, hS, rfl⟩, (cvUnion_iInter_union W S₀ S).symm ▸ ⟨hx, hxS⟩⟩
  · rintro ⟨T, ⟨S, hS, rfl⟩, hxT⟩
    rw [cvUnion_iInter_union] at hxT
    exact ⟨hxT.1, S, hS, hxT.2⟩

/-- The union over the family `insert S₀ Family` of finitary intersections. -/
theorem cvUnion_biUnion_insert {X : Type} {ι : Type} [DecidableEq ι] (W : ι → Set X)
    (S₀ : Finset ι)
    (Family : Finset (Finset ι)) :
    (⋃ S ∈ insert S₀ Family, ⋂ i ∈ S, W i)
      = (⋂ i ∈ S₀, W i) ∪ (⋃ S ∈ Family, ⋂ i ∈ S, W i) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert, exists_prop]
  constructor
  · rintro ⟨S, hS | hS, hx⟩
    · exact Or.inl (hS ▸ hx)
    · exact Or.inr ⟨S, hS, hx⟩
  · rintro (hx | ⟨S, hS, hx⟩)
    · exact ⟨S₀, Or.inl rfl, hx⟩
    · exact ⟨S, Or.inr hS, hx⟩

/-- **The finite-cover induction.**  Let `hinter` witness `CvGood` for every nonempty finite
intersection of the open family `W`.  Then for every finite family `Family` of *nonempty*
subfamilies the union `⋃ S ∈ Family, ⋂ i ∈ S, W i` of the corresponding intersections is
`CvGood`. -/
theorem cvUnion_CvGood_finInter {X : Type} [TopologicalSpace X] (A : Set X) (n₀ K : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) {ι : Type} [DecidableEq ι] (W : ι → Set X)
    (hWo : ∀ i, IsOpen (W i))
    (hinter : ∀ S : Finset ι, S.Nonempty → CvGood A n₀ K U₀ (⋂ i ∈ S, W i)) :
    ∀ n : ℕ, ∀ Family : Finset (Finset ι), Family.card = n →
      (∀ S ∈ Family, S.Nonempty) →
      CvGood A n₀ K U₀ (⋃ S ∈ Family, ⋂ i ∈ S, W i) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih Family hcard hne
  rcases Finset.eq_empty_or_nonempty Family with h0 | hFne
  · rw [h0]
    have hun : (⋃ S ∈ (∅ : Finset (Finset ι)), ⋂ i ∈ S, W i) = (∅ : Set X) := by
      ext x; simp
    exact cvUnion_CvGood_congr_set hun.symm (cvUnion_CvGood_empty A n₀ K U₀)
  · obtain ⟨S₀, hS₀⟩ := hFne
    set Family' : Finset (Finset ι) := Family.erase S₀ with hF'def
    have hcard' : Family'.card < n := by
      rw [hF'def, ← hcard]
      exact Finset.card_erase_lt_of_mem hS₀
    have hne' : ∀ S ∈ Family', S.Nonempty := fun S hS => hne S (Finset.mem_of_mem_erase hS)
    have hins : Family = insert S₀ Family' := by
      rw [hF'def]; exact (Finset.insert_erase hS₀).symm
    set Family'' : Finset (Finset ι) := Family'.image (fun S => S₀ ∪ S) with hF''def
    have hcard'' : Family''.card < n :=
      lt_of_le_of_lt (by rw [hF''def]; exact Finset.card_image_le) hcard'
    have hne'' : ∀ S ∈ Family'', S.Nonempty := by
      intro S hS
      rw [hF''def, Finset.mem_image] at hS
      obtain ⟨T, hT, rfl⟩ := hS
      exact Finset.Nonempty.mono Finset.subset_union_right (hne' T hT)
    have hUnion : (⋃ S ∈ Family, ⋂ i ∈ S, W i)
        = (⋂ i ∈ S₀, W i) ∪ (⋃ S ∈ Family', ⋂ i ∈ S, W i) := by
      rw [hins]
      exact cvUnion_biUnion_insert W S₀ Family'
    have hInter : (⋂ i ∈ S₀, W i) ∩ (⋃ S ∈ Family', ⋂ i ∈ S, W i)
        = (⋃ S ∈ Family'', ⋂ i ∈ S, W i) := by
      rw [hF''def]
      exact cvUnion_inter_iUnion_image W S₀ Family'
    have hUc : CvGood A n₀ K U₀ (⋂ i ∈ S₀, W i) := hinter S₀ (hne S₀ hS₀)
    have hVc : CvGood A n₀ K U₀ (⋃ S ∈ Family', ⋂ i ∈ S, W i) :=
      ih Family'.card hcard' Family' rfl hne'
    have hUVc : CvGood A n₀ K U₀ (⋃ S ∈ Family'', ⋂ i ∈ S, W i) :=
      ih Family''.card hcard'' Family'' rfl hne''
    have hUo : IsOpen (⋂ i ∈ S₀, W i) := isOpen_biInter_finset fun i _ => hWo i
    have hVo : IsOpen (⋃ S ∈ Family', ⋂ i ∈ S, W i) :=
      isOpen_iUnion fun S => isOpen_iUnion fun _ => isOpen_biInter_finset fun i _ => hWo i
    have hUV : CvGood A n₀ K U₀
        ((⋂ i ∈ S₀, W i) ∩ (⋃ S ∈ Family', ⋂ i ∈ S, W i)) :=
      cvUnion_CvGood_congr_set hInter.symm hUVc
    exact cvUnion_CvGood_congr_set hUnion.symm
      (cvUnion_CvGood_union A n₀ K U₀ _ _ hUo hVo hUc hVc hUV)

/-! ## The target -/

/-- **The local-to-global gluing of `CvGood` over a finite open cover** (in the mapping cylinder of
`q`).  If `CvGood` holds on every nonempty finite intersection `⋂ i ∈ T, W i` of the open family
`W : ι → Set Γ` (`ι` finite), then it holds on the union `⋃ i, W i`. -/
theorem cvGoodIUnion {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (hfib : ∀ γ : Γ, Nonempty (Work.StemsB.fibre q γ))
    (n₀ K : ℕ) {U₀ : Work.Thom.RelCoh ℚ n₀ (Work.Serre.cyl q) (Work.Serre.cylBot q)}
    {ι : Type} [Fintype ι] (W : ι → Set Γ) (hWo : ∀ i, IsOpen (W i))
    (hloc : ∀ T : Finset ι, T.Nonempty →
      Work.RatHurewicz.CvGood (Work.Serre.cylBot q) n₀ K U₀
        (Work.Serre.cylPre q (⋂ i ∈ T, W i))) :
    Work.RatHurewicz.CvGood (Work.Serre.cylBot q) n₀ K U₀
      (Work.Serre.cylPre q (⋃ i, W i)) := by
  classical
  -- the pieces inside the mapping cylinder
  have hZo : ∀ i, IsOpen (Work.Serre.cylPre q (W i)) := fun i =>
    (hWo i).preimage (Work.Serre.cylRetract q).continuous
  have hZpre : ∀ S : Finset ι,
      (⋂ i ∈ S, Work.Serre.cylPre q (W i)) = Work.Serre.cylPre q (⋂ i ∈ S, W i) := by
    intro S
    ext y
    simp only [Work.Serre.cylPre, Set.mem_iInter, Set.mem_preimage]
  have hZun : (⋃ i, Work.Serre.cylPre q (W i)) = Work.Serre.cylPre q (⋃ i, W i) := by
    ext y
    simp only [Work.Serre.cylPre, Set.mem_iUnion, Set.mem_preimage]
  have hZuniv : (⋃ i, Work.Serre.cylPre q (W i))
      = ⋃ i ∈ (Finset.univ : Finset ι), Work.Serre.cylPre q (W i) := by
    ext y; simp
  have hinter : ∀ S : Finset ι, S.Nonempty → CvGood (Work.Serre.cylBot q) n₀ K U₀
      (⋂ i ∈ S, Work.Serre.cylPre q (W i)) :=
    fun S hS => cvUnion_CvGood_congr_set (hZpre S).symm (hloc S hS)
  -- the union of the singleton subfamilies
  have hFne : ∀ S ∈ (Finset.univ : Finset ι).image (fun i => ({i} : Finset ι)), S.Nonempty := by
    intro S hS
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨i, Finset.mem_singleton_self i⟩
  have hFunion : (⋃ S ∈ (Finset.univ : Finset ι).image (fun i => ({i} : Finset ι)),
        ⋂ i ∈ S, Work.Serre.cylPre q (W i)) = (⋃ i, Work.Serre.cylPre q (W i)) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_iUnion, Set.mem_iInter,
      Finset.mem_singleton, exists_prop]
    constructor
    · rintro ⟨S, ⟨i, rfl⟩, hyS⟩
      exact ⟨i, hyS i (Finset.mem_singleton_self i)⟩
    · rintro ⟨i, hi⟩
      exact ⟨{i}, ⟨i, rfl⟩, fun j hj => by
        rw [Finset.mem_singleton] at hj
        simpa [hj] using hi⟩
  have hmain := cvUnion_CvGood_finInter (Work.Serre.cylBot q) n₀ K U₀
    (fun i => Work.Serre.cylPre q (W i)) hZo hinter
    ((Finset.univ : Finset ι).image (fun i => ({i} : Finset ι))).card
    ((Finset.univ : Finset ι).image (fun i => ({i} : Finset ι))) rfl hFne
  exact cvUnion_CvGood_congr_set hZun (cvUnion_CvGood_congr_set hFunion hmain)

end

end Work.RatHurewicz

-- audit: the proof rests only on the three standard axioms
#print axioms Work.RatHurewicz.cvGoodIUnion
