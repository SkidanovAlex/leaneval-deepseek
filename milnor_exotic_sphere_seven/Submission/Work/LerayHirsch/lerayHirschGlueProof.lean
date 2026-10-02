import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.lhAny_bijective_iff
import Submission.Work.LerayHirsch.lerayHirschFull_of_two_cover
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.Thom.localThom_union
import Submission.Work.LerayHirsch.lhAny_glue_comap
import Submission.Work.LerayHirsch.exists_homeo_projSpace_bundleComap_homeo
import Submission.Work.LerayHirsch.lerayHirschFull_of_isEmpty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Mayer--Vietoris rung of the Leray--Hirsch induction for a finite open cover

This module proves the milestone `Work.LerayHirsch.LerayHirschGlue`, the second of the two inputs
of the Leray--Hirsch chapter (`Submission/Work/LerayHirsch/LH.lean`):

> if a finite open cover of the base `B` is such that the restriction of `Z` to every
> **nonempty finite intersection** of the members of the cover satisfies Leray--Hirsch, then `Z`
> itself satisfies Leray--Hirsch.

This is the standard Mayer--Vietoris induction over an open cover, with the two-set case
`Work.LerayHirsch.lerayHirschFull_of_two_cover` (`Submission/Work/LerayHirsch/lerayHirschFull_of_two_cover.lean`,
proved from the five lemma on the two ladders of Mayer--Vietoris) as the induction step.

## The shape of the induction

Two ingredients are needed beyond the two-set case.

1. **Leray--Hirsch is invariant under a change of the base.**  For a homeomorphism `e : B' ≃ₜ B`
   and a bundle `W` over `B`, the pullback `W' = bundleComap W e` satisfies Leray--Hirsch iff `W`
   does (`lerayHirschFull_bundleComap_of_homeo`).  The proof compares the two uniform
   Leray--Hirsch maps through the naturality `lhAny_glue_comap`, the homeomorphism
   `P(e) : P(W') ≃ₜ P(W)` (`Work.LerayHirsch.exists_homeo_projSpace_bundleComap_homeo`) and the
   bijectivity of `CohMap` of a homeomorphism.  This gives the restriction transfer
   `lerayHirschFull_restrict_subtype`: for `Y ⊆ X`, Leray--Hirsch for `Z|_Y` gives Leray--Hirsch for
   `Z|_X` restricted to the trace of `Y` on `X`.

2. **The induction itself** (`lerayHirschFull_of_finset_union_aux`), on a bound for the number of
   pieces in a union `⋃_{k ∈ S} U k`: peel off one piece `a ∈ S` and use the two-set case with the
   pair `(⋃_{k ∈ S ∖ {a}} U k, U a)`.  All three inputs are instances of the induction hypothesis:
   the first for the sub-family `S ∖ {a}`, the second for the singleton `{a}`, and the third for
   the family `k ↦ U k ∩ U a` (whose nonempty finite intersections are again nonempty finite
   intersections of the `U k`, namely `⋂_{k ∈ T}(U k ∩ U a) = ⋂_{k ∈ T ∪ {a}} U k`).  This is why
   the induction statement is universally quantified over the family of pieces, and why the
   hypothesis is that Leray--Hirsch holds on *intersections*: the trace of a union on a new piece is
   a union of traces.  Empty pieces are covered by
   `Work.LerayHirsch.lerayHirschFull_of_isEmpty`.

The assembly `lerayHirschGlueProof` then applies the induction to the cover `Finset.univ` and
transports the resulting statement about `Z|_{⋃_k U k} = Z|_B` back to `Z`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {ι : Type} {m : ℕ}

/-! ## 1. Base change along a homeomorphism -/

/-- **The abstract transfer of bijectivity.**  If the pullback `f^*W` is such that both `CohMap f`
and the induced map `P(f^*W) → P(W)` are bijective on cohomology in every degree, then
`LerayHirschFull` of `f^*W` and of `W` are equivalent: the uniform Leray--Hirsch maps are
intertwined by these two bijections (`lhAny_glue_comap`). -/
theorem lhAny_bijective_bundleComap_of_iff (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (f : C(B', B)) (hf : ∀ n, Function.Bijective (CohMap f ℤ n).hom)
    (hg : ∀ n, Function.Bijective (CohMap (projMapComap W f) ℤ n).hom) (k : ℕ) :
    Function.Bijective (lhAny (bundleComap W f) k) ↔ Function.Bijective (lhAny W k) := by
  set R : ((i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) →
      ((i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B') :=
    fun x i => (CohMap f ℤ (k - 2 * (i : ℕ))).hom (x i) with hRdef
  have hR : Function.Bijective R := by
    constructor
    · intro x y hxy
      funext i
      exact (hf (k - 2 * (i : ℕ))).1 (congrFun hxy i)
    · intro y
      refine ⟨fun i => Classical.choose ((hf (k - 2 * (i : ℕ))).2 (y i)), ?_⟩
      funext i
      exact Classical.choose_spec ((hf (k - 2 * (i : ℕ))).2 (y i))
  have hcomp : lhAny (bundleComap W f) k ∘ R
      = (CohMap (projMapComap W f) ℤ k).hom ∘ lhAny W k := by
    funext x
    exact (lhAny_glue_comap W f k x).symm
  calc Function.Bijective (lhAny (bundleComap W f) k)
      ↔ Function.Bijective (lhAny (bundleComap W f) k ∘ R) :=
        (Function.Bijective.of_comp_iff (lhAny (bundleComap W f) k) hR).symm
    _ ↔ Function.Bijective ((CohMap (projMapComap W f) ℤ k).hom ∘ lhAny W k) := by rw [hcomp]
    _ ↔ Function.Bijective (lhAny W k) :=
        (Function.Bijective.of_comp_iff' (hg k) (lhAny W k))

/-- **`LerayHirschFull` is invariant under base change along a homeomorphism.** -/
theorem lerayHirschFull_bundleComap_of_homeo {f : C(B', B)}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (e : B' ≃ₜ B) (he : ⇑f = ⇑e) :
    LerayHirschFull (bundleComap W f) ↔ LerayHirschFull W := by
  have hfa : ∀ n, Function.Bijective (CohMap f ℤ n).hom := by
    intro n
    rw [show f = (e : C(B', B)) from ContinuousMap.ext (congrFun he)]
    exact Work.Cohomology.bijective_CohMap_homeomorph e n
  have hgb : ∀ n, Function.Bijective (CohMap (projMapComap W f) ℤ n).hom := by
    intro n
    obtain ⟨φ, hφ⟩ := exists_homeo_projSpace_bundleComap_homeo W e
    have hc : (φ : C(ProjSpace (bundleComap W (e : C(B', B))), ProjSpace W))
        = projMapComap W (e : C(B', B)) := ContinuousMap.ext (fun x => congrFun hφ x)
    rw [show f = (e : C(B', B)) from ContinuousMap.ext (congrFun he), ← hc]
    exact Work.Cohomology.bijective_CohMap_homeomorph φ n
  rw [← lhAny_bijective_iff, ← lhAny_bijective_iff]
  refine ⟨fun h k => (lhAny_bijective_bundleComap_of_iff W f hfa hgb k).mp (h k),
    fun h k => (lhAny_bijective_bundleComap_of_iff W f hfa hgb k).mpr (h k)⟩

/-- **Restriction of a Leray--Hirsch bundle to a smaller piece inside a larger one.**  If `Y ⊆ X`
are subsets of `B` and the restriction of `Z` to `Y` satisfies Leray--Hirsch, then so does the
restriction of `Z|_X` to the trace of `Y` on `X`. -/
theorem lerayHirschFull_restrict_subtype (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] {X Y : Set B} (hXY : Y ⊆ X) :
    LerayHirschFull (bundleComap Z (subtypeMap Y)) →
      LerayHirschFull (bundleComap (bundleComap Z (subtypeMap X))
        (subtypeMap ((subtypeMap X) ⁻¹' Y))) := by
  intro h
  set A' : Set ↥X := (subtypeMap X) ⁻¹' Y with hA'def
  let Φ : ↥A' ≃ₜ ↥Y :=
    { toFun := fun u => ⟨(u : ↥X).1, u.2⟩
      invFun := fun y => ⟨⟨(y : B), hXY y.2⟩, y.2⟩
      left_inv := fun u => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk
        ((continuous_subtype_val : Continuous (Subtype.val : ↥X → B)).comp
          (continuous_subtype_val : Continuous (Subtype.val : ↥A' → ↥X))) _
      continuous_invFun := (continuous_subtype_val.subtype_mk (fun y => hXY y.2)).subtype_mk _ }
  have hmain : LerayHirschFull (bundleComap (bundleComap Z (subtypeMap Y))
      (Φ : C(↥A', ↥Y))) :=
    (lerayHirschFull_bundleComap_of_homeo (bundleComap Z (subtypeMap Y)) Φ
      (f := (Φ : C(↥A', ↥Y))) rfl).mpr h
  have hcomp : (subtypeMap X).comp (subtypeMap A')
      = (subtypeMap Y).comp (Φ : C(↥A', ↥Y)) := by
    ext u
    rfl
  have hgoal : bundleComap (bundleComap Z (subtypeMap X)) (subtypeMap A')
      = bundleComap (bundleComap Z (subtypeMap Y)) (Φ : C(↥A', ↥Y)) := by
    rw [bundleComap_comp Z (subtypeMap X) (subtypeMap A'),
      bundleComap_comp Z (subtypeMap Y) (Φ : C(↥A', ↥Y)), hcomp]
  rw [hgoal]
  exact hmain

/-! ## 2. Set algebra for finset-indexed unions and intersections -/

variable {ιc : Type} [Fintype ιc]

/-- The union over all of a finite type. -/
theorem glue_iUnion_finset_univ (U : ιc → Set B) :
    (⋃ k ∈ (Finset.univ : Finset ιc), U k) = ⋃ k, U k := by
  ext x; simp

/-- The union over the empty family. -/
theorem glue_iUnion_finset_empty (U : ιc → Set B) :
    (⋃ k ∈ (∅ : Finset ιc), U k) = (∅ : Set B) := by
  ext x; simp

/-- The intersection over a singleton. -/
theorem glue_biInter_finset_singleton (U : ιc → Set B) (a : ιc) :
    (⋂ k ∈ ({a} : Finset ιc), U k) = U a := by
  ext x; simp

/-- The union over `{a} ∪ S`. -/
theorem glue_biUnion_singleton_union [DecidableEq ιc] (U : ιc → Set B) (a : ιc) (S : Finset ιc) :
    (⋃ k ∈ ({a} ∪ S : Finset ιc), U k) = U a ∪ ⋃ k ∈ S, U k := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_union, Finset.mem_singleton, exists_prop]
  constructor
  · rintro ⟨k, rfl | hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hk, hx⟩
  · rintro (hx | ⟨k, hk, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨k, Or.inr hk, hx⟩

/-- The intersection over `{a} ∪ S`. -/
theorem glue_biInter_singleton_union [DecidableEq ιc] (U : ιc → Set B) (a : ιc) (S : Finset ιc) :
    (⋂ k ∈ ({a} ∪ S : Finset ιc), U k) = U a ∩ ⋂ k ∈ S, U k := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl), fun k hk => h k (Or.inr hk)⟩
  · rintro ⟨h1, h2⟩ k (rfl | hk)
    · exact h1
    · exact h2 k hk

/-- Distributivity of a finite union over a further intersection. -/
theorem glue_inter_biUnion (U : ιc → Set B) (a : ιc) (S : Finset ιc) :
    ((⋃ k ∈ S, U k) ∩ U a) = ⋃ k ∈ S, (U k ∩ U a) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, ha⟩
    exact ⟨i, hi, hx, ha⟩
  · rintro ⟨i, hi, hx, ha⟩
    exact ⟨⟨i, hi, hx⟩, ha⟩

/-- A finite intersection of intersections with a fixed set. -/
theorem glue_biInter_inter_nonempty (U : ιc → Set B) (a : ιc) (S : Finset ιc) (hS : S.Nonempty) :
    (⋂ k ∈ S, (U k ∩ U a)) = (⋂ k ∈ S, U k) ∩ U a := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    exact ⟨fun i hi => (h i hi).1, (h hS.choose hS.choose_spec).2⟩
  · rintro ⟨h1, h2⟩ i hi
    exact ⟨h1 i hi, h2⟩

/-! ## 3. The finite-cover induction -/

/-- **The finite-cover Mayer--Vietoris induction for Leray--Hirsch.**  For a finite family `U` of
open subsets of `B`, if every nonempty finite intersection of the `U k` satisfies Leray--Hirsch
(as a bundle over its own base), then so does the restriction of `Z` to any finite union of the
`U k`.  The induction is on a bound for the number of pieces in the union; the family of pieces is
universally quantified so that the induction also applies to the family `k ↦ U k ∩ U a` of traces
on a new piece. -/
theorem lerayHirschFull_of_finset_union_aux (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (n : ℕ) :
    ∀ (U : ιc → Set B), (∀ k, IsOpen (U k)) →
      (∀ S : Finset ιc, S.Nonempty →
        LerayHirschFull (bundleComap Z (subtypeMap (⋂ k ∈ S, U k)))) →
      ∀ (S : Finset ιc), S.card ≤ n →
        LerayHirschFull (bundleComap Z (subtypeMap (⋃ k ∈ S, U k))) := by
  induction n with
  | zero =>
    intro U hU hint S hS
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    subst hS0
    rw [glue_iUnion_finset_empty]
    haveI : IsEmpty ↥(∅ : Set B) := Set.isEmpty_coe_sort.mpr rfl
    exact lerayHirschFull_of_isEmpty _
  | succ n ih =>
    intro U hU hint S hS
    by_cases hle : S.card ≤ n
    · exact ih U hU hint S hle
    · classical
      have hcard : S.card = n + 1 := by omega
      have hSpos : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hSpos
      set S₀ : Finset ιc := S.erase a with hS₀def
      have hcardS₀ : S₀.card = n := by
        rw [hS₀def, Finset.card_erase_of_mem ha, hcard]; omega
      have hS_eq : S = {a} ∪ S₀ := by
        rw [hS₀def, ← Finset.insert_eq, Finset.insert_erase ha]
      set X : Set B := ⋃ k ∈ S, U k with hXdef
      have hXeq : X = U a ∪ ⋃ k ∈ S₀, U k := by rw [hXdef, hS_eq, glue_biUnion_singleton_union]
      -- the sub-family hypotheses
      have hintS₀ : LerayHirschFull (bundleComap Z (subtypeMap (⋃ k ∈ S₀, U k))) :=
        ih U hU hint S₀ (le_of_eq hcardS₀)
      have hsingle : LerayHirschFull (bundleComap Z (subtypeMap (U a))) := by
        have h1 := hint ({a} : Finset ιc) (Finset.singleton_nonempty a)
        rw [glue_biInter_finset_singleton] at h1
        exact h1
      have hintU' : ∀ T : Finset ιc, T.Nonempty →
          LerayHirschFull (bundleComap Z (subtypeMap (⋂ k ∈ T, (U k ∩ U a)))) := by
        intro T hT
        have hne : ({a} ∪ T : Finset ιc).Nonempty :=
          ⟨a, Finset.mem_union_left T (Finset.mem_singleton_self a)⟩
        have h1 := hint ({a} ∪ T) hne
        rw [glue_biInter_singleton_union] at h1
        have h2 : (⋂ k ∈ T, (U k ∩ U a)) = U a ∩ ⋂ k ∈ T, U k := by
          rw [glue_biInter_inter_nonempty U a T hT, Set.inter_comm]
        rw [h2]
        exact h1
      have hintUnion : LerayHirschFull (bundleComap Z
          (subtypeMap (⋃ k ∈ S₀, (U k ∩ U a)))) :=
        ih (fun k => U k ∩ U a) (fun k => (hU k).inter (hU a)) hintU' S₀ (le_of_eq hcardS₀)
      -- the three pieces in the restricted base
      have hsubW : (⋃ k ∈ S₀, U k) ⊆ X := by
        intro x hx; rw [hXeq]; exact Or.inr hx
      have hsubV : U a ⊆ X := by
        intro x hx; rw [hXeq]; exact Or.inl hx
      have hsubC : (⋃ k ∈ S₀, (U k ∩ U a)) ⊆ X :=
        Set.Subset.trans (Set.biUnion_mono (fun k hk => hk) (fun k _ => Set.inter_subset_left))
          hsubW
      have hW : LerayHirschFull (bundleComap (bundleComap Z (subtypeMap X))
          (subtypeMap ((subtypeMap X) ⁻¹' (⋃ k ∈ S₀, U k)))) :=
        lerayHirschFull_restrict_subtype Z hsubW hintS₀
      have hV : LerayHirschFull (bundleComap (bundleComap Z (subtypeMap X))
          (subtypeMap ((subtypeMap X) ⁻¹' (U a)))) :=
        lerayHirschFull_restrict_subtype Z hsubV hsingle
      have hC : LerayHirschFull (bundleComap (bundleComap Z (subtypeMap X))
          (subtypeMap ((subtypeMap X) ⁻¹' (⋃ k ∈ S₀, (U k ∩ U a))))) :=
        lerayHirschFull_restrict_subtype Z hsubC hintUnion
      -- openness of the two pieces
      have hWopen : IsOpen ((subtypeMap X) ⁻¹' (⋃ k ∈ S₀, U k)) :=
        (isOpen_biUnion fun k _ => hU k).preimage continuous_subtype_val
      have hVopen : IsOpen ((subtypeMap X) ⁻¹' (U a)) := (hU a).preimage continuous_subtype_val
      have hcov : (subtypeMap X) ⁻¹' (⋃ k ∈ S₀, U k) ∪ (subtypeMap X) ⁻¹' (U a) = Set.univ := by
        rw [← Set.preimage_union,
          show (⋃ k ∈ S₀, U k) ∪ U a = X from by rw [Set.union_comm, ← hXeq]]
        exact Set.eq_univ_of_forall (fun u => u.2)
      have hC' : LerayHirschFull (bundleComap (bundleComap Z (subtypeMap X))
          (subtypeMap ((subtypeMap X) ⁻¹' (⋃ k ∈ S₀, U k)
            ∩ (subtypeMap X) ⁻¹' (U a)))) := by
        rw [← Set.preimage_inter, glue_inter_biUnion]
        exact hC
      exact lerayHirschFull_of_two_cover (bundleComap Z (subtypeMap X)) hWopen hVopen hcov
        hW hV hC'

/-! ## 4. The assembly: the finite open cover rung of Leray--Hirsch -/

/-- **The Mayer--Vietoris rung of the Leray--Hirsch induction for a finite open cover.** -/
theorem lerayHirschGlueProof : Work.LerayHirsch.LerayHirschGlue := by
  intro m B _ ι _ Z ιc _ U hU hcov hint
  classical
  have hint' : ∀ S : Finset ιc, S.Nonempty →
      LerayHirschFull (bundleComap Z (subtypeMap (⋂ k ∈ S, U k))) := by
    intro S hS
    by_cases hne : (⋂ k ∈ S, U k).Nonempty
    · exact hint S hS hne
    · haveI : IsEmpty ↥(⋂ k ∈ S, U k) := ⟨fun x => hne ⟨x.1, x.2⟩⟩
      exact lerayHirschFull_of_isEmpty _
  have h1 : LerayHirschFull (bundleComap Z
      (subtypeMap (⋃ k ∈ (Finset.univ : Finset ιc), U k))) :=
    lerayHirschFull_of_finset_union_aux Z (Fintype.card ιc) U hU hint' Finset.univ
      (le_of_eq Finset.card_univ)
  have h2 : LerayHirschFull (bundleComap Z (subtypeMap (Set.univ : Set B))) := by
    rw [glue_iUnion_finset_univ] at h1
    rw [hcov] at h1
    exact h1
  let ψ : ↥(Set.univ : Set B) ≃ₜ B :=
    { toFun := fun x => x.1
      invFun := fun b => ⟨b, trivial⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun b => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := Continuous.subtype_mk continuous_id (fun b => trivial) }
  exact (lerayHirschFull_bundleComap_of_homeo Z ψ
    (f := subtypeMap (Set.univ : Set B)) rfl).mp h2

end

end Work.LerayHirsch
