/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# [JZLA20, Theorem 6.1]: the induction on the `G`-complexity

This is the last step of [JZLA20, Theorem 6.1].  Given the two inputs

* `SourceReduction φ` — the source-based finitely generated reduction
  (`Section6.exists_source_reduction`): every `a ∈ D_{K[G],U}` is, up to a unit `φ (unitOf u)`,
  the image of a `Rat(Kˣ × H)`-element for a finitely generated `H ≤ G`, with `H` contained in the
  image in `G` of the source of that element;
* `hstep` — the environment of the induction step (`Section6.Thm61Step`): for every finitely
  generated non-trivial `H ≤ G` there is an ambient ring `P` in which [JZLA20, Proposition 5.1]
  applies and an isomorphism `D_{H,U} ≃+* D_{H,P}`,

we prove that every non-zero element of `D = D_{K[G],U}` is a unit.

The proof is the well-founded induction on `Tree_G` of [JZLA20, Theorem 6.1, proof].  The `H ≠ ⊥`
case is the self-contained lemma `isUnit_of_thm61StepData` of `Section6.Thm61StepData`; the
`H = ⊥` case is the degenerate one where the reduced element lies in the image of the field `K`
and is a unit by `isUnit_of_mem_divisionClosure_bot`.  The only other ingredient is that
multiplying by `φ (unitOf u)` (a unit of `D`) does not change being a unit.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61InductionAux
import Submission.Work.ORHughesFree.Section6.Thm61StepData
import Submission.Work.ORHughesFree.Section6.Thm61InductionBase
import Submission.Work.ORHughesFree.Section6.isUnit_of_mem_divisionClosure_bot
import Submission.Work.ORHughesFree.Section6.treeG_Phi_mul_ofGroup

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **[JZLA20, Theorem 6.1]**: if the source-based reduction and the environment of the induction
step are available, then every non-zero element of `D_{K[G],U}` is a unit. -/
theorem isUnit_of_mem_divisionClosure_of_reduction
    (φ : MonoidAlgebra K G →+* U) [Nontrivial U]
    (hsr : SourceReduction (K := K) (G := G) (U := U) φ)
    (hstep : ∀ H : Subgroup G, H.FG → H ≠ ⊥ → Nonempty (Thm61Step K G U φ H)) :
    ∀ a : ↥(divisionClosure (Set.range φ)), a ≠ 0 → IsUnit a := by
  suffices h : ∀ T : Tree, ∀ a : ↥(divisionClosure (Set.range φ)), treeG φ a = T →
      a ≠ 0 → IsUnit a by
    intro a ha
    exact h (treeG φ a) a rfl ha
  intro T
  induction T using Tree.lt_wf.induction with
  | h T ih =>
    intro a hT ha
    by_cases hT1 : T = 1
    · exact isUnit_of_exists_mul_eq_one (isUnit_of_treeG_eq_one φ a (hT.trans hT1))
    · obtain ⟨H, α, u, hHfg, hEq, hTreeA, hTreeRat, hMin, hLeast⟩ := hsr a
      -- `a' = a * φ (unitOf u)`, and `φ (unitOf u)` is a unit of `D`
      obtain ⟨wu, hwu⟩ := (imElem_isUnit φ u).1
      have hw_inv : imElem φ u * ((wu⁻¹ : (↥(divisionClosure (Set.range φ)))ˣ) :
          ↥(divisionClosure (Set.range φ))) = 1 := by
        rw [← hwu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have ha'eq : (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H α)) = a * imElem φ u := by
        refine Subtype.ext ?_
        show ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H α)) : U) = (a : U) * φ (unitOf u)
        exact hEq
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
      rcases eq_or_ne H ⊥ with hHbot | hHne
      · -- `H = ⊥`: `a'` lies in the image of the field `K`
        subst H
        have hmem : ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) (⊥ : Subgroup G))
              (ratUnitsTimesEquiv (K := K) (⊥ : Subgroup G) α)) : U)
            ∈ (divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) (⊥ : Subgroup G))))
                : Subring U) := by
          rw [Phi_ofSubgroup_ratUnitsTimesEquiv φ ⊥ α]
          exact (Phi (φ.comp (inducedMapRing (K := K) (⊥ : Subgroup G))) α).2
        have hU : IsUnit (((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) (⊥ : Subgroup G))
              (ratUnitsTimesEquiv (K := K) (⊥ : Subgroup G) α)) : U)) :=
          isUnit_of_mem_divisionClosure_bot φ hmem (fun h0 => ha'0 (Subtype.ext h0))
        have hu' : IsUnit ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) (⊥ : Subgroup G))
              (ratUnitsTimesEquiv (K := K) (⊥ : Subgroup G) α))) :=
          isUnit_divisionClosure_of_isUnit_coe hU
        rw [h_a_eq]
        exact IsUnit.mul hu' (Units.isUnit _)
      · -- `H ≠ ⊥`: the full [JZLA20, Proposition 5.1] machinery
        obtain ⟨step⟩ := hstep H hHfg hHne
        letI : Ring step.P := step.ringP
        letI : MulSemiringAction (Multiplicative ℤ) ↥step.DN := step.smulDN
        refine isUnit_of_thm61StepData φ step.data step.e step.e_Phi step.data_N step.N_ne_top
          a ha α u hEq hTreeA hTreeRat hMin hLeast ?_
        intro b hb0 hb
        exact ih (treeG φ (inclSub φ H b)) (by rw [hT] at hb; exact hb) (inclSub φ H b) rfl
          ((inclSub_ne_zero_iff φ H b).mpr hb0)

end Work.ORHughesFree.Section6
