/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The induction step of [JZLA20, Theorem 6.1] for a fixed finitely generated `H ≤ G`

This file contains the mathematical heart of the induction of [JZLA20, Theorem 6.1]: the `H ≠ ⊥`
case, as a self-contained lemma.  Its inputs are

* the reduced element: `a ∈ D_{K[G],U}`, `α ∈ Rat(Kˣ × H)`, `u ∈ Kˣ × G` with
  `a' := Φ_{Kˣ×G}(ofSubgroup (ratUnitsTimesEquiv α)) = a · φ(unitOf u)`, `Tree_G a' = Tree_G a`,
  `Tree α = Tree_G a'`, `α` minimal among the realisers of `a'`, and `H` contained in the image
  in `G` of the source of `α`;
* the ambient ring of [JZLA20, Proposition 5.1]: `P`, `DN = D_{N,P}`, `data : Prop51Data (Kˣ × H) P DN`
  together with the isomorphism `e : D_{H,U} ≃+* D_{H,P}` and its compatibility `e_Phi` with the
  universal morphisms of rational `Kˣ × H`-semirings;
* the identification `data.N = Kˣ × N` and the non-triviality `N ≠ H`;
* the induction hypothesis, in the form in which the well-founded induction on `Tree_G` supplies
  it.

The conclusion is `IsUnit a`.

Stating the lemma with `P`, `DN`, `data`, `e`, `e_Phi` as *variables* (rather than through the
projections of a `Thm61Step`) is essential for the elaborator: the `Ring P` instance field of a
structure is not visible to instance search from the projections of a local hypothesis, and the
resulting projections `step.data.treeH`, `step.e ⋯` are also prohibitively expensive to elaborate.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.ORHughesFree.Section6.Thm61InductionAux
import Submission.Work.ORHughesFree.Section6.Thm61Inv
import Submission.Work.ORHughesFree.Section6.treeG_le_treeG_of_subgroup
import Submission.Work.ORHughesFree.Prop51.prop51P
import Submission.Work.ORHughesFree.Prop51.isUnit_of_conclB
import Submission.Work.ORHughesFree.Section6.Thm61InductionBase
import Submission.Work.ORHughesFree.Section6.Thm61UnitSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **[JZLA20, Theorem 6.1], the induction step for a fixed `H`.** -/
theorem isUnit_of_thm61StepData
    (φ : MonoidAlgebra K G →+* U) [Nontrivial U]
    {H : Subgroup G}
    {P : Type} [Ring P] {DN : Subring P} [MulSemiringAction (Multiplicative ℤ) ↥DN]
    (data : Prop51Data (Kˣ × H) P DN)
    (e : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+* ↥data.DH)
    (e_Phi : ∀ β : RatU (Kˣ × H),
      e ((Phi (φ.comp (inducedMapRing (K := K) H))) β) = ⟨data.Φ β, data.map_mem β⟩)
    {N : Subgroup H} (data_N : data.N = unitsTimesSubgroup (K := K) (G := H) N)
    (N_ne_top : N ≠ ⊤)
    (a : ↥(divisionClosure (Set.range φ))) (ha : a ≠ 0)
    (α : RatU (Kˣ × H)) (u : Kˣ × G)
    (hEq : ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)) : U) = (a : U) * φ (unitOf u))
    (hTreeA : treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α))) = treeG φ a)
    (hTreeRat : Rat.treeOfRat (Kˣ × H) α
        = treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H α))))
    (hMin : ∀ β : RatU (Kˣ × H),
        (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H β))
          = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
              (ratUnitsTimesEquiv (K := K) H α)) →
        Tree.le (Rat.treeOfRat (Kˣ × H) α) (Rat.treeOfRat (Kˣ × H) β))
    (hLeast : ∀ (V : Subgroup (Kˣ × H)) (v : Kˣ × H) (e' : RatU ↥V),
        RatU.ofSubgroup V e' * RatU.ofGroup v = α →
        H ≤ (V.map (MonoidHom.snd Kˣ H)).map (Subgroup.subtype H))
    (ih : ∀ b : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))),
        b ≠ 0 → Tree.lt (treeG φ (inclSub φ H b)) (treeG φ a) → IsUnit (inclSub φ H b)) :
    IsUnit a := by
  have ha'eq : (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)) = a * imElem φ u := by
    refine Subtype.ext ?_
    show ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)) : U) = (a : U) * φ (unitOf u)
    exact hEq
  obtain ⟨wu, hwu⟩ := (imElem_isUnit φ u).1
  have hw_inv : imElem φ u * ((wu⁻¹ : (↥(divisionClosure (Set.range φ)))ˣ) :
      ↥(divisionClosure (Set.range φ))) = 1 := by
    rw [← hwu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha'0 : (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)) ≠ 0 := by
    intro h0
    refine ha ?_
    have hthis : a * imElem φ u = 0 := by rw [← ha'eq]; exact h0
    have h2 : a = a * imElem φ u *
        ((wu⁻¹ : (↥(divisionClosure (Set.range φ)))ˣ) : ↥(divisionClosure (Set.range φ))) := by
      rw [mul_assoc, hw_inv, mul_one]
    rw [h2, hthis, zero_mul]
  have h_a_eq : a = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)) *
        ((wu⁻¹ : (↥(divisionClosure (Set.range φ)))ˣ) : ↥(divisionClosure (Set.range φ))) := by
    rw [ha'eq, mul_assoc, hw_inv, mul_one]
  -- the `H`-presentation of the reduced element
  set aH : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) :=
    (Phi (φ.comp (inducedMapRing (K := K) H))) α with haHdef
  have hincl : inclSub φ H aH = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
      (ratUnitsTimesEquiv (K := K) H α)) := by
    apply Subtype.ext
    rw [inclSub_apply]
    exact (Phi_ofSubgroup_ratUnitsTimesEquiv φ H α).symm
  have haH0 : aH ≠ 0 := by
    intro h
    refine ha'0 ?_
    rw [← hincl, h, map_zero]
  -- the `H`-complexity of `aH` is the complexity of the minimal realiser `α`
  have htree_alpha : Rat.treeOfRat (Kˣ × H) α
      = treeG (φ.comp (inducedMapRing (K := K) H)) aH := by
    refine Tree.le_antisymm ?_ ?_
    · obtain ⟨β, hβ, hβt⟩ := (treeG_spec (φ.comp (inducedMapRing (K := K) H)) aH).1
      have hle := hMin β ((Phi_ofSubgroup_eq_iff φ H β α).mpr hβ)
      rwa [hβt] at hle
    · exact (treeG_spec (φ.comp (inducedMapRing (K := K) H)) aH).2 α rfl
  -- Proposition 5.1 at `e aH`: its hypothesis comes from the induction on `Tree_G`
  have hTHeq : data.treeH (e aH) = treeG φ a := by
    rw [Thm61Step.e_tree_local e_Phi aH, ← htree_alpha, hTreeRat, hTreeA]
  have hInv : Prop51Inv data (e aH) :=
    prop51Inv_of_stepData φ data e e_Phi aH a hTHeq ih
  have hconcl : Prop51ConclP data (e aH) :=
    Prop51.prop51P data (e aH) hInv (e aH) (e aH).2 (Tree.le_refl _)
  obtain ⟨f, hf, hbound, _hsing, hmono⟩ := hconcl
  have hb_ne : (e aH : P) ≠ 0 := by
    intro h0
    have hav : e aH = (0 : ↥data.DH) := Subtype.ext h0
    exact haH0 (e.injective (by rw [hav, map_zero]))
  by_cases hAtt : ∃ k : ℤ, f.1 k ≠ 0 ∧
      data.treeH (data.coeffToP (f.1 k)) = data.treeH (e aH)
  · -- the single-monomial case, excluded by the leastness of the source
    obtain ⟨k, hk, hatt⟩ := hAtt
    have hΦα : data.Φ α = (e aH : P) := by
      rw [haHdef]
      exact (congrArg (fun z : ↥data.DH => (z : P)) (e_Phi α)).symm
    have htree : Rat.treeOfRat (Kˣ × H) α = data.treeH (e aH) :=
      htree_alpha.trans (Thm61Step.e_tree_local e_Phi aH).symm
    obtain ⟨β', hβ'⟩ := hmono k hatt α hΦα htree
    have hmap := hLeast data.N (data.t ^ k) β' hβ'
    rw [data_N] at hmap
    rw [map_snd_unitsTimesSubgroup N] at hmap
    have hNtop : N = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : (x : G) ∈ N.map (Subgroup.subtype H) := hmap x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    exact (N_ne_top hNtop).elim
  · -- every non-zero coefficient of `f` is a unit of `D_{N,P}`: the result is a unit
    have hnoAtt : ∀ k : ℤ, f.1 k ≠ 0 →
        data.treeH (data.coeffToP (f.1 k)) ≠ data.treeH (e aH) :=
      fun k hk heq => hAtt ⟨k, hk, heq⟩
    have hu' := isUnit_of_unitSeries φ data e aH haH0 hInv α hincl hb_ne f hf hbound hnoAtt
    rw [h_a_eq]
    exact IsUnit.mul hu' (Units.isUnit _)

end Work.ORHughesFree.Section6
