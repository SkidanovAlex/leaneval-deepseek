import Mathlib
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.pdCohMap_comp
import Submission.Work.Thom.Relocate.HonestFMV
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.Glue
import Submission.Work.Thom.FiniteCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Uniqueness of a class detecting on a finite cover of pieces

The finite-cover Thom class theorem `Work.Thom.thomClass_of_finite_cover` produces a class over the
union `⋃ k, U k` of a finite open cover that restricts to prescribed classes on the pieces
`finInter U S`.  This module proves that such a class is *unique*: a class whose restriction to
every piece `finInter U S` vanishes is itself zero, under the low-degree vanishing hypothesis
`hlowU` (relative cohomology of unions of pieces in degree `n-1`) that the finite-cover theorem
already assumes.  Consequently the witness chosen by `Classical.choose` in
`thomClass_of_finite_cover` is canonical.

The proof is an induction over the finite family of pieces.  The induction step is the two-piece
case, which is the injectivity of the honest relative Mayer--Vietoris map
`Work.Cohomology.honestF` when the relative cohomology of the overlap in degree `n-1` vanishes:
a class killed by restriction to the two pieces of a cover is zero.  The transport of the honest
relative cohomology of a piece into the subspace over the union is
`Work.Cohomology.luIso_res`.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Elementary cast lemmas -/

/-- Casting along an equality of sets is inverse to the opposite cast. -/
theorem pdcz_cast_symm_cast {α : Type _} {P : α → Type _} {a b : α} (h : a = b) (x : P b) :
    h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

/-- Casting zero along an equality is zero. -/
theorem pdcz_cast_zero {α : Type _} {P : α → Type _} [∀ a, Zero (P a)] {a b : α} (h : a = b) :
    (h ▸ (0 : P a)) = (0 : P b) := by
  cases h; rfl

/-- Casting zero of a piece cohomology along an equality of base pieces. -/
theorem pdcz_cast_zero_piece {Z : Work.TangentClasses.RealBundle B F ι} (n : ℕ)
    {a b : Set B} (h : a = b) :
    (h ▸ (0 : Work.Thom.PieceCoh Z a n)) = (0 : Work.Thom.PieceCoh Z b n) := by
  cases h; rfl

/-- Casting a piece cohomology class along an equality of base pieces, both ways. -/
theorem pdcz_cast_symm_cast_piece {Z : Work.TangentClasses.RealBundle B F ι} (n : ℕ)
    {a b : Set B} (h : a = b) (x : Work.Thom.PieceCoh Z b n) :
    h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

/-- A `Subsingleton` module is a subsingleton after transporting along an isomorphism. -/
theorem pdcz_subsingleton_of_iso {M N : ModuleCat ℤ} (e : M ≅ N) (h : Subsingleton M) :
    Subsingleton N := by
  obtain ⟨-, hs⟩ := ConcreteCategory.bijective_of_isIso e.hom
  exact ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [Subsingleton.elim x y]⟩

/-- The value of `pdCohMap` only depends on the actual sets, not on the proof of the inclusion. -/
theorem pdcz_pdCohMap_apply_congr (X : TopCat) (A : Set X) {W U : Set X}
    (h1 h2 : W ⊆ U) (k : ℕ) (c : Work.Cohomology.pdCohSub X A U k) :
    (Work.Cohomology.pdCohMap X A U W h1 k).hom c
      = (Work.Cohomology.pdCohMap X A U W h2 k).hom c :=
  congrArg (fun h => (Work.Cohomology.pdCohMap X A U W h k).hom c) (Subsingleton.elim h1 h2)

/-- **Functoriality of `pdCohMap` in element form**: restricting from `W` to `V` in two steps. -/
theorem pdcz_pdCohMap_comp_apply (X : TopCat) (A : Set X) {V U W : Set X}
    (hVU : V ⊆ U) (hUW : U ⊆ W) (k : ℕ) (c : Work.Cohomology.pdCohSub X A W k) :
    (Work.Cohomology.pdCohMap X A U V hVU k).hom
        ((Work.Cohomology.pdCohMap X A W U hUW k).hom c)
      = (Work.Cohomology.pdCohMap X A W V (hVU.trans hUW) k).hom c := by
  have h := congrArg (fun (f : Work.Cohomology.pdCohSub X A W k
      ⟶ Work.Cohomology.pdCohSub X A V k) => (ModuleCat.Hom.hom f) c)
    (Work.Thom.pdCohMap_comp X A hVU hUW k)
  exact h.symm

/-- The first component of the honest Mayer--Vietoris map, evaluated. -/
theorem pdcz_honestF_fst_apply (X : TopCat) (A U V : Set X) (n : ℕ)
    (c : Work.Cohomology.pdCoh X A n) :
    (ModuleCat.Hom.hom (biprod.fst : Work.Cohomology.pdCohSub X A U n ⊞
        Work.Cohomology.pdCohSub X A V n ⟶ Work.Cohomology.pdCohSub X A U n))
      ((ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V n)) c)
      = (ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X A U n)) c := by
  have h := congrArg (fun (f : Work.Cohomology.pdCoh X A n
      ⟶ Work.Cohomology.pdCohSub X A U n) => (ModuleCat.Hom.hom f) c)
    (Work.Cohomology.honestF_fst X A U V n)
  exact h

/-- The second component of the honest Mayer--Vietoris map, evaluated. -/
theorem pdcz_honestF_snd_apply (X : TopCat) (A U V : Set X) (n : ℕ)
    (c : Work.Cohomology.pdCoh X A n) :
    (ModuleCat.Hom.hom (biprod.snd : Work.Cohomology.pdCohSub X A U n ⊞
        Work.Cohomology.pdCohSub X A V n ⟶ Work.Cohomology.pdCohSub X A V n))
      ((ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V n)) c)
      = (ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X A V n)) c := by
  have h := congrArg (fun (f : Work.Cohomology.pdCoh X A n
      ⟶ Work.Cohomology.pdCohSub X A V n) => (ModuleCat.Hom.hom f) c)
    (Work.Cohomology.honestF_snd X A U V n)
  exact h

/-! ## The injectivity of the honest relative Mayer--Vietoris map -/

/-- **Injectivity of the honest relative Mayer--Vietoris map under a vanishing overlap.**  If the
relative cohomology of the overlap `U ∩ V` in degree `m - 1` is a subsingleton, then the two
restrictions `H^m(X,A) → H^m(U,U∩A) ⊞ H^m(V,V∩A)` are injective: their kernel is the image of the
connecting map `δ : H^{m-1}(U ∩ V, U∩V∩A) → H^m(X,A)`, which is zero. -/
theorem pdcz_honestF_injective_of_subsingleton_overlap (X : TopCat) {A U V : Set X} (m : ℕ)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hsub : Subsingleton (Work.Cohomology.pdCohSub X A (U ∩ V) (m - 1))) :
    Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V m)) := by
  rcases m with _ | k
  · exact honestF_injective_zero X A U V hU hV hcov
  · haveI : Subsingleton (Work.Cohomology.pdCohSub X A (U ∩ V) k) := hsub
    have hdelta0 : ModuleCat.Hom.hom
        (Work.Cohomology.honestDelta X A U V hU hV hcov k) = 0 := by
      refine LinearMap.ext (fun x => ?_)
      rw [Subsingleton.elim x 0]
      simp
    have hex := Work.Cohomology.honest_exact₁ X A U V hU hV hcov k
    have h' : LinearMap.range (ModuleCat.Hom.hom
          (Work.Cohomology.honestDelta X A U V hU hV hcov k))
        = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V (k + 1))) :=
      ShortComplex.Exact.moduleCat_range_eq_ker hex
    rw [hdelta0, LinearMap.range_zero] at h'
    exact LinearMap.ker_eq_bot.mp h'.symm

/-! ## The two-piece injectivity -/

/-- **The two-piece injectivity.**  If `W = U ∪ V` with `U, V` open, and the relative cohomology
of the overlap `U ∩ V` in degree `n - 1` vanishes, then a class `c ∈ H^n(W, W∩A)` whose
restrictions to `U` and `V` are zero is zero. -/
theorem pdcz_pair_eq_zero {X : TopCat} (A : Set X) {W U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUW : U ⊆ W) (hVW : V ⊆ W)
    (hcov : U ∪ V = W) (n : ℕ)
    (hUV : Subsingleton (Work.Cohomology.pdCohSub X A (U ∩ V) (n - 1)))
    (c : Work.Cohomology.pdCohSub X A W n)
    (hcU : (Work.Cohomology.pdCohMap X A W U hUW n).hom c = 0)
    (hcV : (Work.Cohomology.pdCohMap X A W V hVW n).hom c = 0) :
    c = 0 := by
  let AY : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' A
  let UY : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' U
  let VY : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' V
  let Y : TopCat := TopCat.of ↥W
  have hUc : IsOpen UY := hU.preimage continuous_subtype_val
  have hVc : IsOpen VY := hV.preimage continuous_subtype_val
  have hcovc : UY ∪ VY = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have hy : (y : X) ∈ U ∪ V := by rw [hcov]; exact y.2
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr h
  have h1 : (Work.Cohomology.pdCohRes (TopCat.of ↥W) AY UY n).hom c = 0 := by
    rw [← Work.Cohomology.luIso_res X A hUW n]
    show (ModuleCat.Hom.hom (Work.Cohomology.luIso X A hUW n).hom)
        ((ModuleCat.Hom.hom (Work.Cohomology.pdCohMap X A W U hUW n)) c) = 0
    rw [hcU, map_zero]
  have h2 : (Work.Cohomology.pdCohRes (TopCat.of ↥W) AY VY n).hom c = 0 := by
    rw [← Work.Cohomology.luIso_res X A hVW n]
    show (ModuleCat.Hom.hom (Work.Cohomology.luIso X A hVW n).hom)
        ((ModuleCat.Hom.hom (Work.Cohomology.pdCohMap X A W V hVW n)) c) = 0
    rw [hcV, map_zero]
  have hsub : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W) AY (UY ∩ VY) (n - 1)) := by
    have hkey := Work.Thom.pdcz_subsingleton_of_iso
      (Work.Cohomology.luIso X A (Set.inter_subset_left.trans hUW) (n - 1)) hUV
    simpa only [AY, UY, VY, Set.preimage_inter] using hkey
  have hzero : (ModuleCat.Hom.hom (Work.Cohomology.honestF (TopCat.of ↥W) AY UY VY n)) c = 0 := by
    apply Work.Thom.biprod_eq_zero_of_fst_snd_eq_zero
      (M := Work.Cohomology.pdCohSub (TopCat.of ↥W) AY UY n)
      (N := Work.Cohomology.pdCohSub (TopCat.of ↥W) AY VY n)
    · exact (Work.Thom.pdcz_honestF_fst_apply (TopCat.of ↥W) AY UY VY n c).trans h1
    · exact (Work.Thom.pdcz_honestF_snd_apply (TopCat.of ↥W) AY UY VY n c).trans h2
  have hinj := Work.Thom.pdcz_honestF_injective_of_subsingleton_overlap
    (TopCat.of ↥W) (A := AY) (U := UY) (V := VY) n hUc hVc hcovc hsub
  refine hinj ?_
  rw [hzero, map_zero]


/-- **The induction over the finite family of pieces.**  For a finite set `T` of indices, a class
over `⋃ i ∈ T, U i` whose restriction to every nonempty subfamily `S ⊆ T` vanishes is zero. -/
theorem pdcz_finset {τ : Type} [DecidableEq τ]
    (T : Finset τ) (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (U : τ → Set B)
    (hU : ∀ i, IsOpen (U i))
    (hlow : ∀ A : Finset (Finset τ), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (Work.Thom.PieceCoh Z (⋃ S ∈ A, ⋂ i ∈ (S : Set τ), U i) (n - 1))) :
    ∀ (x : Work.Thom.PieceCoh Z (⋃ i ∈ (T : Set τ), U i) n),
      (∀ (S : Finset τ) (hS : S.Nonempty) (hST : S ⊆ T),
        (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃ i ∈ (T : Set τ), U i)) (Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i))
          (Set.preimage_mono (Work.Thom.biInter_finset_subset_biUnion U hS hST)) n).hom x = 0) →
      x = 0 := by
  induction T using Finset.induction with
  | empty =>
    intro x _
    have hunion_empty : (⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) = (∅ : Set B) := by
      rw [Finset.coe_empty, Set.biUnion_empty]
    haveI : Subsingleton (Work.Thom.PieceCoh Z (⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) n) :=
      Work.Thom.subsingleton_PieceCoh_of_eq Z hunion_empty.symm
        (Work.Thom.subsingleton_PieceCoh_of_isEmpty Z n (W := (∅ : Set B)) ⟨fun x => x.2⟩)
    exact Subsingleton.elim x 0
  | insert a T' haT ih =>
    intro x hx
    let Wb : Set B := ⋃ i ∈ (T' : Set τ), U i
    let Vb : Set B := U a
    have hWset : (⋃ i ∈ (↑(insert a T') : Set τ), U i) = Wb ∪ Vb := by
      rw [Work.Thom.biUnion_finset_insert]
      exact Set.union_comm _ _
    have hWbopen : IsOpen Wb := isOpen_biUnion (fun i _ => hU i)
    have hVbopen : IsOpen Vb := hU a
    have hUopen : IsOpen (Z.proj ⁻¹' Wb) := hWbopen.preimage Z.continuous_proj
    have hVopen : IsOpen (Z.proj ⁻¹' Vb) := hVbopen.preimage Z.continuous_proj
    have hUW : Z.proj ⁻¹' Wb ⊆ Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i) := by
      rw [hWset]
      exact Set.preimage_mono Set.subset_union_left
    have hVbU : Vb ⊆ (⋃ i ∈ (↑(insert a T') : Set τ), U i) := by
      rw [hWset]
      exact Set.subset_union_right
    have hVW : Z.proj ⁻¹' Vb ⊆ Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i) :=
      Set.preimage_mono hVbU
    set xWb : Work.Thom.PieceCoh Z Wb n :=
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i)) (Z.proj ⁻¹' Wb) hUW n).hom x
      with hxWbdef
    have hcU : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i)) (Z.proj ⁻¹' Wb) hUW n).hom x = 0 := by
      have hxWb : ∀ (S : Finset τ) (hS : S.Nonempty) (hST : S ⊆ T'),
          (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' Wb) (Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i))
            (Set.preimage_mono (Work.Thom.biInter_finset_subset_biUnion U hS hST)) n).hom
            xWb = 0 := by
        intro S hS hST
        have hSins : S ⊆ insert a T' := fun i hi => Finset.mem_insert_of_mem (hST hi)
        have hx0 := hx S hS hSins
        have hVU : Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i) ⊆ Z.proj ⁻¹' Wb :=
          Set.preimage_mono (Work.Thom.biInter_finset_subset_biUnion U hS hST)
        rw [hxWbdef]
        rw [Work.Thom.pdcz_pdCohMap_comp_apply (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z)
          (V := Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i)) (U := Z.proj ⁻¹' Wb)
          (W := Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i)) hVU hUW n x]
        exact (Work.Thom.pdcz_pdCohMap_apply_congr (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z)
          (U := Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i))
          (W := Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i)) (hVU.trans hUW) _ n x).trans hx0
      exact ih xWb hxWb
    have hcV : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i)) (Z.proj ⁻¹' Vb) hVW n).hom x = 0 := by
      have hSne : ({a} : Finset τ).Nonempty := Finset.singleton_nonempty a
      have hSins : ({a} : Finset τ) ⊆ insert a T' := by
        intro i hi
        rw [Finset.mem_singleton] at hi
        rw [hi]
        exact Finset.mem_insert_self a T'
      have hUW' : (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i)
          ⊆ (⋃ i ∈ (↑(insert a T') : Set τ), U i) :=
        Work.Thom.biInter_finset_subset_biUnion U hSne hSins
      have hset : (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i) = Vb :=
        Work.Thom.biInter_finset_singleton a U
      have hx0 := hx {a} hSne hSins
      have hx0c := congrArg (fun z => hset ▸ z) hx0
      rw [Work.Thom.pdcz_cast_zero_piece n hset] at hx0c
      rwa [Work.Thom.pdCohMap_cast_target Z hset hVbU hUW' x] at hx0c
    have hUV : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' Wb ∩ Z.proj ⁻¹' Vb) (n - 1)) := by
      rw [← Set.preimage_inter]
      by_cases hT : T'.Nonempty
      · have hA'ne : ∀ S ∈ T'.image (fun i => ({i} ∪ {a} : Finset τ)), S.Nonempty := by
          intro S hS
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
          exact Finset.Nonempty.mono Finset.subset_union_right (Finset.singleton_nonempty a)
        have hA'nonempty : (T'.image (fun i => ({i} ∪ {a} : Finset τ))).Nonempty :=
          hT.image (fun i => ({i} ∪ {a} : Finset τ))
        have hUnionEq : (⋃ S ∈ (T'.image (fun i => ({i} ∪ {a} : Finset τ))),
            ⋂ j ∈ (S : Set τ), U j) = Wb ∩ Vb := by
          rw [Work.Thom.biUnion_finset_image]
          show (⋃ i ∈ (T' : Set τ), ⋂ j ∈ (↑({i} ∪ {a} : Finset τ) : Set τ), U j) = Wb ∩ Vb
          rw [show Wb ∩ Vb = (⋃ i ∈ (T' : Set τ), U i) ∩ U a from rfl,
            ← Work.Thom.biUnion_finset_inter T' U (U a)]
          refine Work.Thom.biUnion_congr_finset (fun i _ => ?_)
          rw [Work.Thom.biInter_finset_union, Work.Thom.biInter_finset_singleton,
            Work.Thom.biInter_finset_singleton]
        have hpiece := hlow _ hA'ne hA'nonempty
        rwa [hUnionEq] at hpiece
      · rw [Finset.not_nonempty_iff_eq_empty] at hT
        have hWb0 : Wb = (∅ : Set B) := by
          show (⋃ i ∈ (T' : Set τ), U i) = (∅ : Set B)
          rw [hT, Finset.coe_empty, Set.biUnion_empty]
        rw [hWb0, Set.empty_inter]
        exact Work.Thom.subsingleton_PieceCoh_of_isEmpty Z (n - 1) (W := (∅ : Set B))
          ⟨fun x => x.2⟩
    have hcov : Z.proj ⁻¹' Wb ∪ Z.proj ⁻¹' Vb
        = Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i) := by
      rw [← Set.preimage_union, hWset]
    exact Work.Thom.pdcz_pair_eq_zero (X := TopCat.of Z.TotalSpace)
      (A := Work.Thom.zeroComplement Z)
      (W := Z.proj ⁻¹' (⋃ i ∈ (↑(insert a T') : Set τ), U i))
      (U := Z.proj ⁻¹' Wb) (V := Z.proj ⁻¹' Vb)
      hUopen hVopen hUW hVW hcov n hUV x hcU hcV

end

/-- **Uniqueness of a class of the Thom pair detected by a finite open cover.**  A class
`cU ∈ H^n(X|_⋃kUk, X|_⋃kUk ∖ 0)` whose restriction to every nonempty piece `finInter U S` vanishes
is itself zero, under the low-degree vanishing hypothesis `hlowU`. -/
theorem pdCohMap_finInter_eq_zero {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n N : ℕ) (U : Fin N → Set B) (hU : ∀ k, IsOpen (U k))
    (hlowU : ∀ A : Finset (Finset (Fin N)), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (Work.Thom.PieceCoh Z (⋃ S ∈ A, Work.Thom.finInter U S) (n - 1)))
    (cU : Work.Thom.PieceCoh Z (⋃ k, U k) n)
    (h : ∀ (S : Finset (Fin N)) (hS : S.Nonempty),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, U k)) (Z.proj ⁻¹' (Work.Thom.finInter U S))
        (Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)) n).hom cU = 0) :
    cU = 0 := by
  have hE : (⋃ i ∈ (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)), U i) = (⋃ k, U k) :=
    Work.Thom.biUnion_finset_univ U
  have hx : ∀ (S : Finset (Fin N)) (hS : S.Nonempty) (hST : S ⊆ Finset.univ),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ i ∈ (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)), U i))
        (Z.proj ⁻¹' (⋂ i ∈ (S : Set (Fin N)), U i))
        (Set.preimage_mono (Work.Thom.biInter_finset_subset_biUnion U hS hST)) n).hom
        (hE.symm ▸ cU) = 0 := by
    intro S hS hST
    have hcast := Work.Thom.pdCohMap_cast_source Z
      (U := (⋃ k, U k))
      (U' := (⋃ i ∈ (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)), U i))
      (W := (⋂ i ∈ (S : Set (Fin N)), U i))
      hE.symm (Work.Thom.finInter_nonempty_subset_iUnion hS)
      (Work.Thom.biInter_finset_subset_biUnion U hS hST) cU
    rw [hcast]
    exact h S hS
  have hres := Work.Thom.pdcz_finset (Finset.univ : Finset (Fin N)) Z n U hU hlowU
    (hE.symm ▸ cU) hx
  have h1 := congrArg (fun z => hE ▸ z) hres
  rwa [Work.Thom.pdcz_cast_symm_cast_piece n hE cU, Work.Thom.pdcz_cast_zero_piece n hE] at h1

end Work.Thom
