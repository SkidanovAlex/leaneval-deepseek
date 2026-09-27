/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Non-degeneracy of the pairing of a nonzero rational cohomology class with cycles

Let `u` be a rational `n`-cochain of a simplicial set `S` which is a cocycle, and suppose that
its cohomology class `H.mk u hu` is nonzero, i.e. that `u` is *not* a coboundary.  Then there is
a *cycle* `c` on which `u` does not vanish:

`∃ c ∈ chainCycles S ℚ n, seval S ℚ n u c ≠ 0`.

Equivalently (the contrapositive, which is what is proved here): a cocycle `u` that pairs to zero
with every cycle is a coboundary.  This uses that the coefficient ring `ℚ` is a field: the
pairing of cochains with chains identifies `u : Cochain S ℚ n` with the linear functional
`seval S ℚ n u : SChain S ℚ n →ₗ[ℚ] ℚ`, and the classical fact that for a linear map of `ℚ`-vector
spaces `f`, the annihilator of `ker f` is the range of the dual (transpose) map
`LinearMap.range_dualMap_eq_dualAnnihilator_ker` shows that a functional vanishing on the cycles
comes from a functional on the lower chains, i.e. is a coboundary.

The two ingredients are

* `seval_cochainOfDual`: the cochain `σ ↦ V (single σ 1)` reconstructs a functional `V` from its
  values on the basis `single σ 1` of the chain module (the inverse of the `seval` identification);
* `mem_boundaries_of_forall_chainCycles_seval_eq_zero`: the contrapositive of the statement.
-/
import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology

namespace Work.Cohomology

open Submission.Cohomology

/-- The inverse of the `seval` identification of cochains with linear functionals on chains: the
cochain `σ ↦ V (Finsupp.single σ 1)` has the same values as `V` on the basis of chains given by
the single simplices. -/
lemma seval_cochainOfDual {S : SSet.{0}} {n : ℕ} (V : SChain S ℚ n →ₗ[ℚ] ℚ)
    (c : SChain S ℚ n) :
    seval S ℚ n (fun σ => V (Finsupp.single σ 1)) c = V c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
      rw [map_add, map_add, ih, seval_single]
      congr 1
      rw [show (Finsupp.single a b : SChain S ℚ n) = b • Finsupp.single a 1 by
        rw [Finsupp.smul_single', mul_one], map_smul, smul_eq_mul]

/-- Contrapositive form of the non-degeneracy of the evaluation pairing: a cochain (indeed any
cochain) which pairs to zero with every cycle is a coboundary. -/
lemma mem_boundaries_of_forall_chainCycles_seval_eq_zero {S : SSet.{0}} {n : ℕ}
    (u : Cochain S ℚ n)
    (h : ∀ c, c ∈ chainCycles S ℚ n → seval S ℚ n u c = 0) :
    u ∈ boundaries S ℚ n := by
  match n with
  | 0 =>
      rw [boundaries, Submodule.mem_bot]
      funext σ
      have h1 := h (Finsupp.single σ 1) Submodule.mem_top
      rwa [seval_single, one_mul] at h1
  | m + 1 =>
      rw [boundaries, LinearMap.mem_range]
      -- `h` says exactly that `seval u` lies in the annihilator of the `(m+1)`-cycles
      -- `ker (sbdry S ℚ m)`, which over the field `ℚ` is the range of the dual map.
      have hmem : seval S ℚ (m+1) u ∈ (LinearMap.ker (sbdry S ℚ m)).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro c hc
        exact h c hc
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker (sbdry S ℚ m)] at hmem
      obtain ⟨V, hV⟩ := hmem
      -- `V : SChain S ℚ m →ₗ[ℚ] ℚ` is the required lower cochain, read back as a cochain.
      refine ⟨fun σ => V (Finsupp.single σ 1), ?_⟩
      funext σ
      have h1 : coboundary S ℚ m (fun σ => V (Finsupp.single σ 1)) σ
          = seval S ℚ (m+1) (coboundary S ℚ m (fun σ => V (Finsupp.single σ 1)))
              (Finsupp.single σ 1) := by
        rw [seval_single, one_mul]
      rw [h1, seval_coboundary, seval_cochainOfDual]
      rw [show u σ = seval S ℚ (m+1) u (Finsupp.single σ 1) by rw [seval_single, one_mul]]
      rw [← hV, LinearMap.dualMap_apply]

theorem exists_chain_eval_ne_zero {S : SSet.{0}} {n : ℕ} (u : Submission.Cohomology.Cochain S ℚ n)
    (hu : u ∈ Submission.Cohomology.cycles S ℚ n)
    (hx : Submission.Cohomology.H.mk u hu ≠ 0) :
    ∃ c : Submission.Cohomology.SChain S ℚ n,
      c ∈ Submission.Cohomology.chainCycles S ℚ n ∧ Submission.Cohomology.seval S ℚ n u c ≠ 0 := by
  by_contra h
  push Not at h
  refine hx ?_
  rw [H.mk, Submodule.Quotient.mk_eq_zero]
  exact mem_boundaries_of_forall_chainCycles_seval_eq_zero u h

end Work.Cohomology
