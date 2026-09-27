/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The evaluation pairing of cohomology classes with cycles

Over `ℚ`, the evaluation pairing `seval` identifies the `n`-th cohomology `H S ℚ n` with the
space of linear functionals on the `n`-cycles of `S` which vanish on the boundaries:

`pairMap S n : H S ℚ n →ₗ[ℚ] (chainCycles S ℚ n →ₗ[ℚ] ℚ)`,

sending the class of a cocycle `u` to the functional `c ↦ seval u c` on cycles.  This is the
Universal Coefficient Theorem over the field `ℚ`: the map is injective
(`Work.Cohomology.pairMap_injective`, from `exists_chain_eval_ne_zero`) with range exactly the
annihilator of `chainBoundariesInCycles` (`Work.Cohomology.pairMap_range`).

The pairing is natural: for a morphism `f : S ⟶ T` of simplicial sets,
`pairMap S n (H.map ℚ f n x) = (pairMap T n x) ∘ (chainMap ℚ f n)`, which is what makes the
duality between the maps induced by an inclusion of simplicial sets on homology and cohomology
available.
-/
import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The pushforward of cycles along a morphism of simplicial sets. -/
def cycleChainMap {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) :
    chainCycles S ℚ n →ₗ[ℚ] chainCycles T ℚ n where
  toFun c := ⟨chainMap ℚ f n c.1, by
    rcases n with _ | m
    · exact Submodule.mem_top
    · rw [mem_chainCycles_succ] at ⊢
      rw [← chainMap_sbdry]
      rw [mem_chainCycles_succ.mp c.2, map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp] lemma cycleChainMap_coe {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (c : chainCycles S ℚ n) : (cycleChainMap f n c).1 = chainMap ℚ f n c.1 := rfl

/-- The evaluation pairing, defined on cocycles. -/
def pairMapAux (S : SSet.{0}) (n : ℕ) :
    cycles S ℚ n →ₗ[ℚ] (chainCycles S ℚ n →ₗ[ℚ] ℚ) where
  toFun u := (seval S ℚ n u.1).comp (chainCycles S ℚ n).subtype
  map_add' u v := by
    refine LinearMap.ext fun c => ?_
    show (seval S ℚ n (u.1 + v.1)) c.1 = (seval S ℚ n u.1) c.1 + (seval S ℚ n v.1) c.1
    simp only [seval_apply, Pi.add_apply, mul_add]
    rw [Finsupp.sum_add]
  map_smul' r u := by
    refine LinearMap.ext fun c => ?_
    show (seval S ℚ n (r • u.1)) c.1 = r * (seval S ℚ n u.1) c.1
    simp only [seval_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun σ _ => ?_
    ring

/-- Coboundaries pair to zero with cycles: the pairing is well defined on cohomology. -/
lemma pairMapAux_compat (S : SSet.{0}) (n : ℕ) :
    boundariesInCycles S ℚ n ≤ LinearMap.ker (pairMapAux S n) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun c => ?_
  rw [boundariesInCycles, Submodule.mem_comap] at hu
  rcases n with _ | m
  · rw [boundaries, Submodule.mem_bot] at hu
    have h : (u : Cochain S ℚ 0) = 0 := hu
    show (seval S ℚ 0 (u : Cochain S ℚ 0)) c.1 = 0
    rw [h]
    have hz : seval S ℚ 0 (0 : Cochain S ℚ 0) = 0 := by
      ext d
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [seval_apply]
      simp [Finsupp.sum]
    rw [hz]
    rfl
  · rw [boundaries, LinearMap.mem_range] at hu
    obtain ⟨w, hw⟩ := hu
    have h : (u : Cochain S ℚ (m+1)) = coboundary S ℚ m w := hw.symm
    show (seval S ℚ (m+1) (u : Cochain S ℚ (m+1))) c.1 = 0
    rw [h]
    exact seval_coboundary_eq_zero w c.1 c.2

/-- The evaluation pairing of a cohomology class with cycles, as a linear map. -/
def pairMap (S : SSet.{0}) (n : ℕ) :
    H S ℚ n →ₗ[ℚ] (chainCycles S ℚ n →ₗ[ℚ] ℚ) :=
  (boundariesInCycles S ℚ n).liftQ (pairMapAux S n) (pairMapAux_compat S n)

@[simp] lemma pairMap_mk {S : SSet.{0}} {n : ℕ} (u : Cochain S ℚ n)
    (hu : u ∈ cycles S ℚ n) (c : chainCycles S ℚ n) :
    pairMap S n (H.mk u hu) c = seval S ℚ n u c.1 := by
  have h := Submodule.liftQ_mkQ (boundariesInCycles S ℚ n) (pairMapAux S n)
    (pairMapAux_compat S n)
  have h2 : pairMap S n (H.mk u hu)
      = pairMapAux S n ⟨u, hu⟩ := congrArg (fun g => g ⟨u, hu⟩) h
  rw [h2]
  rfl

/-- The pairing is natural with respect to morphisms of simplicial sets. -/
theorem pairMap_natural {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) (x : H T ℚ n) :
    pairMap S n (H.map ℚ f n x) = (pairMap T n x).comp (cycleChainMap f n) := by
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
      obtain ⟨u, hu⟩ := u
      rw [show (Submodule.Quotient.mk ⟨u, hu⟩ : H T ℚ n) = H.mk u hu from rfl]
      ext c
      rw [H.map_mk, pairMap_mk, LinearMap.comp_apply, pairMap_mk, cycleChainMap_coe,
        seval_chainMap]

end

end Submission.Cohomology
