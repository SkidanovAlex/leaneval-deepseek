/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary constructions for the induction of [JZLA20, Theorem 6.1]

This file collects the small glue that the well-founded induction on the `G`-complexity needs:

* order glue for the DHS04 tree order (`Tree.lt_of_lt_of_le`, `Tree.lt_of_le_of_lt`);
* `SourceReduction φ`, the source-based finitely generated reduction of
  `Section6.exists_source_reduction`, packaged as a `Prop` so that the induction can be stated
  against it without unfolding the whole `∃`-nesting;
* `Phi_ofSubgroup_eq_iff`: equality of `Rat(Kˣ × H)`-elements evaluated through the subgroup
  `Kˣ × H ≤ Kˣ × G` is equality after the identification `Rat(Kˣ × H) ≃ Rat(Kˣ × ↥H)`;
* `map_snd_unitsTimesSubgroup`: `(Kˣ × N).map snd = N`;
* `inclSub φ H`: the inclusion `D_{K[↥H],U} ⊆ D_{K[G],U}` of division closures as a ring
  homomorphism, with `inclSub_apply` and `inclSub_ne_zero_iff`;
* `isUnit_divisionClosure_of_isUnit_coe`, `isUnit_of_exists_mul_eq_one`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity
import Submission.Work.ORHughesFree.Section6.Reduce
import Submission.Work.ORHughesFree.Section6.exists_source_reduction
import Submission.Work.ORHughesFree.Section6.Phi_ofSubgroup_ratUnitsTimesEquiv
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono
import Submission.Work.ORHughesFree.Rat.Source

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-! ### Order glue for the DHS04 tree order -/

theorem Tree.lt_of_lt_of_le {x y z : Tree} (h1 : Tree.lt x y) (h2 : Tree.le y z) : Tree.lt x z := by
  rcases h2 with rfl | h2
  · exact h1
  · exact Tree.lt_trans h1 h2

theorem Tree.lt_of_le_of_lt {x y z : Tree} (h1 : Tree.le x y) (h2 : Tree.lt y z) : Tree.lt x z := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Tree.lt_trans h1 h2

namespace Section6

/-- **The source-based finitely generated reduction**, packaged as a hypothesis: this is exactly
the statement of `Section6.exists_source_reduction`. -/
def SourceReduction (φ : MonoidAlgebra K G →+* U) : Prop :=
  ∀ a : ↥(divisionClosure (Set.range φ)),
    ∃ (H : Subgroup G) (α : RatU (Kˣ × H)) (u : Kˣ × G),
      H.FG ∧
      ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H α)) : U) = (a : U) * φ (unitOf u) ∧
      treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H α))) = treeG φ a ∧
      Rat.treeOfRat (Kˣ × H) α
        = treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H α))) ∧
      (∀ β : RatU (Kˣ × H),
        (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H β))
          = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
              (ratUnitsTimesEquiv (K := K) H α)) →
        Tree.le (Rat.treeOfRat (Kˣ × H) α) (Rat.treeOfRat (Kˣ × H) β)) ∧
      (∀ (V : Subgroup (Kˣ × H)) (v : Kˣ × H) (e : RatU ↥V),
        RatU.ofSubgroup V e * RatU.ofGroup v = α →
        H ≤ (V.map (MonoidHom.snd Kˣ H)).map (Subgroup.subtype H))

/-- The reduction is available from `Section6.exists_source_reduction`. -/
theorem sourceReduction_of_exists_source_reduction
    (φ : MonoidAlgebra K G →+* U) : SourceReduction (K := K) (G := G) (U := U) φ :=
  fun a => exists_source_reduction φ a

/-- **The `E ∗ H`-presentation of the reduced element.**  Evaluating `Rat(Kˣ × H)` inside
`D_{K[G],U}` through the subgroup `Kˣ × H ≤ Kˣ × G` is the same as evaluating `Rat(Kˣ × ↥H)`
inside `D_{K[↥H],U}` and including. -/
theorem Phi_ofSubgroup_eq_iff (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (β γ : RatU (Kˣ × H)) :
    ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H β))
      = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H γ)))
    ↔ (Phi (φ.comp (inducedMapRing (K := K) H))) β
        = (Phi (φ.comp (inducedMapRing (K := K) H))) γ := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun z : ↥(divisionClosure (Set.range φ)) => (z : U)) h
    rw [Phi_ofSubgroup_ratUnitsTimesEquiv φ H β, Phi_ofSubgroup_ratUnitsTimesEquiv φ H γ] at h'
    exact h'
  · intro h
    apply Subtype.ext
    rw [Phi_ofSubgroup_ratUnitsTimesEquiv φ H β, Phi_ofSubgroup_ratUnitsTimesEquiv φ H γ]
    exact congrArg (fun z : ↥(divisionClosure
      (Set.range (φ.comp (inducedMapRing (K := K) H)))) => (z : U)) h

/-- The image of `Kˣ × ↥N` under the second projection is `N`. -/
theorem map_snd_unitsTimesSubgroup {K : Type} [Monoid K] {G : Type} [Group G]
    (N : Subgroup G) :
    (unitsTimesSubgroup (K := K) (G := G) N).map (MonoidHom.snd Kˣ G) = N := by
  ext g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    exact mem_unitsTimesSubgroup.mp hu
  · intro hg
    exact Subgroup.mem_map.mpr ⟨(1, g), mem_unitsTimesSubgroup.mpr hg, rfl⟩

/-- The inclusion of the two division closures `D_{K[↥H],U} ⊆ D_{K[G],U}`, as a `≤`-statement. -/
noncomputable def inclSubLe (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))) ≤
      divisionClosure (Set.range φ) :=
  fun _ hx => DivisionClosure.divisionClosure_mono (range_inducedMapRing_le φ H) hx

/-- The inclusion `D_{K[↥H],U} ⊆ D_{K[G],U}` of division closures, as a ring homomorphism. -/
noncomputable def inclSub (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) →+*
      ↥(divisionClosure (Set.range φ)) :=
  Subring.inclusion (inclSubLe φ H)

theorem inclSub_apply (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (x : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))))) :
    (inclSub φ H x : U) = (x : U) :=
  Subring.coe_inclusion (inclSubLe φ H) x

theorem inclSub_injective (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    Function.Injective (inclSub φ H) :=
  Subring.inclusion_injective (inclSubLe φ H)

theorem inclSub_ne_zero_iff (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (x : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))))) :
    inclSub φ H x ≠ 0 ↔ x ≠ 0 := by
  have hinj := inclSub_injective φ H
  have h0 : inclSub φ H (0 : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))))
      = 0 := map_zero _
  constructor
  · intro h hx
    exact h (by rw [hx, h0])
  · intro h hx
    refine h (hinj ?_)
    rw [hx, h0]

/-- A unit of `S` whose value lies in a division closure is a unit of the division closure. -/
theorem isUnit_divisionClosure_of_isUnit_coe {S : Type*} [Ring S] {R : Set S}
    {x : ↥(divisionClosure R)} (h : IsUnit (x : S)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  have h1 : (x : S) * ((u⁻¹ : Sˣ) : S) = 1 := by
    rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((u⁻¹ : Sˣ) : S) * (x : S) = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmem : ((u⁻¹ : Sˣ) : S) ∈ (divisionClosure R : Subring S) :=
    DivisionClosure.inverse_mem_divisionClosure x.2 h1 h2
  exact ⟨⟨x, ⟨(u⁻¹ : Sˣ), hmem⟩, Subtype.ext h1, Subtype.ext h2⟩, rfl⟩

/-- A two-sided inverse exhibits a unit. -/
theorem isUnit_of_exists_mul_eq_one {R : Type*} [Ring R] {x : R}
    (h : ∃ y : R, x * y = 1 ∧ y * x = 1) : IsUnit x :=
  let ⟨y, h1, h2⟩ := h
  ⟨⟨x, y, h1, h2⟩, rfl⟩

end Section6

end Work.ORHughesFree
