/-
Copyright: subproject `ORLocInd` -- the Cohen--Lyndon basis theorem (node N4).

# The Cohen--Lyndon basis theorem for free groups

This file assembles the strong induction (on `Work.OROneRel.relatorNorm`, uniformly over all
generating types in the universe) that proves the free-group instance of the Cohen--Lyndon
theorem, in the classical (`⟪r⟫ · C_G(r)`-coset) form `Work.CohenLyndon.CohenLyndonNC`.

The induction follows Putnam, *One-relator groups*, Theorem 6.1 (Karrass--Solitar 1972):

* a relator is first replaced by a cyclically reduced conjugate
  (`Work.OROneRel.cyclicReduction`), using the conjugation invariance
  `Work.ORLocInd.CohenLyndon.cohenLyndonNC_conj`;
* **base case** `relatorNorm r ≤ 1`: `r` is `of a` or `(of a)⁻¹`
  (`Work.ORLocInd.CohenLyndon.relatorNorm_le_one`), handled by
  `Work.ORLocInd.CohenLyndon.cohenLyndonNC_generator` and
  `Work.ORLocInd.CohenLyndon.cohenLyndonNC_invLetter`;
* **Case 1**: some letter `t` occurring in `r` has exponent sum zero -- the Magnus/HNN step
  `Work.ORLocInd.CohenLyndon.cohenLyndonNC_magnusStep`;
* **Case 2**: every letter occurring in `r` has nonzero exponent sum.  Two distinct letters
  `t ≠ x` are chosen (`Work.ORLocInd.CohenLyndon.exists_two_letters`), the relator is substituted
  along Magnus' `ψ = subst t x (σ_x r) (σ_t r)` (so that `σ_t (ψ r) = 0`), a cyclically reduced
  conjugate `v` of `ψ r` satisfies `letterCountNot t v < relatorNorm r`, so Case 1 applies to `v`,
  and Karrass--Solitar's descent `Work.ORLocInd.CohenLyndon.cohenLyndonNC_subst` carries
  `CohenLyndonNC (ψ r)` back to `CohenLyndonNC r`.

## Main declarations

* `Work.ORLocInd.CohenLyndon.CLBelow`, `...CLBelow_all` -- the induction hypothesis and the
  induction;
* `Work.ORLocInd.CohenLyndon.cohenLyndonNC_freeGroup` -- `CohenLyndonNC` for every nontrivial
  non-proper-power element of a free group;
* `Work.ORLocInd.CohenLyndon.cohenLyndonIso_freeGroup` -- the same in the quotient form
  `Work.CohenLyndon.CohenLyndonIso` consumed by
  `Submission/Work/ORLocInd/FKSKernel/cohenLyndonBasis.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.CLBelowDefs
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_conj
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_generator
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_magnusStep
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_subst_transport
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_magnusStep_fixed
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_invLetter
import Submission.Work.ORLocInd.CohenLyndon.letterCountNot_conj_subst_lt
import Submission.Work.ORLocInd.CohenLyndon.exists_two_letters
import Submission.Work.ORLocInd.CohenLyndon.relatorNorm_le_one
import Submission.Work.ORLocInd.CohenLyndon.relatorNorm_cyclicReduction_le
import Submission.Work.ORLocInd.CohenLyndon.isProperPower_conj_OROneRel
import Submission.Work.ORLocInd.CohenLyndon.isProperPower_bridge
import Submission.Work.ORLocInd.CohenLyndon.relatorNorm_eq_letterCountNot_of_not_mem
import Submission.Work.ORLocInd.CohenLyndon.sigma_t_subst_cyclic
import Submission.Work.ORLocInd.CohenLyndon.magW_relatorNorm_le_letterCountNot
import Submission.Work.ORLocInd.CohenLyndon.magnusStepDefs
import Submission.Work.ORLocInd.CohenLyndon.magnusStep.not_isProperPower_magW
import Submission.Work.ORLocInd.CohenLyndon.centralizer_eq_zpowers
import Submission.Work.OROneRel.wcp_not_isProperPower_subst

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

variable {α : Type u}

/-- The exponent sum `sigma` is invariant under conjugation. -/
theorem sigma_conj (t : α) (g r : FreeGroup α) :
    Work.OROneRel.sigma t (g * r * g⁻¹) = Work.OROneRel.sigma t r := by
  have h : (Work.OROneRel.sigma t) g * (Work.OROneRel.sigma t) r *
      ((Work.OROneRel.sigma t) g)⁻¹ = (Work.OROneRel.sigma t) r := by
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  simpa only [map_mul, map_inv] using h

/-- **Case 2 of the Cohen--Lyndon induction.**  Let `r ∈ F(α)` be cyclically reduced, not a proper
power, with two distinct letters `t ≠ x` occurring in it whose exponent sums are nonzero.  Assume
the Cohen--Lyndon property for all relators of norm `< relatorNorm r` over all generating types
(`IH`).  Then `r` has the Cohen--Lyndon property.

The relator `ψ r := subst t x (σ_x r) (σ_t r) r` has exponent sum zero in `t`; a cyclically reduced
conjugate `v` of `ψ r` still has exponent sum zero in `t` and satisfies
`letterCountNot t v < relatorNorm r`, so Case 1 (`cohenLyndonNC_magnusStep_fixed`) gives
`CohenLyndonNC v`, conjugation (`cohenLyndonNC_conj`) gives `CohenLyndonNC (ψ r)`, and
Karrass--Solitar's descent (`cohenLyndonNC_subst`) gives `CohenLyndonNC r`. -/
theorem cohenLyndonNC_case2 {r : FreeGroup α} {t x : α}
    (htx : t ≠ x) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hr1 : r ≠ 1)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (hσt : Work.OROneRel.sigma t r ≠ 1) (hσx : Work.OROneRel.sigma x r ≠ 1)
    (IH : CLBelow.{u} (Work.OROneRel.relatorNorm r)) :
    Work.CohenLyndon.CohenLyndonNC r := by
  classical
  have hxt : x ≠ t := fun h => htx h.symm
  have hσxne : Multiplicative.toAdd (Work.OROneRel.sigma x r) ≠ 0 := by
    intro h0
    refine hσx ?_
    have hsigx : Work.OROneRel.sigma x r =
        Multiplicative.ofAdd (Multiplicative.toAdd (Work.OROneRel.sigma x r)) := by simp
    rw [hsigx, h0]
    rfl
  -- the substituted relator
  set ψr : FreeGroup α := Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
      (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r with hψr
  have hσψ : Work.OROneRel.sigma t ψr = 1 := by
    rw [hψr]
    exact sigma_t_subst_cyclic hxt
  have hppψ : ¬ Work.OROneRel.IsProperPower ψr := by
    rw [hψr]
    exact Work.OROneRel.wcp_not_isProperPower_subst r hxt hcyc hpp hσxne
  -- a cyclically reduced conjugate of `ψr`
  set v : FreeGroup α := Work.OROneRel.cyclicReduction ψr with hv
  set c : FreeGroup α := Work.OROneRel.cyclicConjugator ψr with hc
  have hcv : c * v * c⁻¹ = ψr := by
    rw [hv, hc]
    exact Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv ψr
  have hvcyc : Work.OROneRel.IsCyclicallyReducedRelator v := by
    rw [hv]
    exact Work.OROneRel.isCyclicallyReducedRelator_cyclicReduction ψr
  have hconjv : IsConj v ψr := isConj_iff.mpr ⟨c, hcv⟩
  have hppv : ¬ Work.OROneRel.IsProperPower v := by
    intro hv'
    have h2 : Work.OROneRel.IsProperPower (c * v * c⁻¹) :=
      (isProperPower_conj_OROneRel v c).mpr hv'
    rw [hcv] at h2
    exact hppψ h2
  have hv1 : v ≠ 1 := by
    intro hv1'
    refine Work.OROneRel.ne_one_of_not_isProperPower hppψ ?_
    rw [← hcv, hv1']
    simp
  have hσv : Work.OROneRel.sigma t v = 1 := by
    rw [← sigma_conj t c v, hcv, hσψ]
  -- the letter count of `v` is smaller than the norm of `r`
  have hcount : Work.OROneRel.letterCountNot t v < Work.OROneRel.relatorNorm r :=
    letterCountNot_conj_subst_lt r t x ht hvcyc hconjv
  -- `CohenLyndonNC (ψr)`
  have hCLψr : Work.CohenLyndon.CohenLyndonNC ψr := by
    by_cases htv : t ∈ Work.OROneRel.relatorLetters v
    · have heps : Work.OROneRel.eps t v = 0 :=
        (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t v).mpr hσv
      have hCLmag : Work.CohenLyndon.CohenLyndonNC (magW t v) := by
        refine IH (magS t v) (magW t v) ?_ ?_ ?_
        · exact magnusStep.not_isProperPower_magW v t hppv heps
        · exact magW_ne_one t v hvcyc hv1 htv heps
        · exact lt_of_le_of_lt (magW_relatorNorm_le_letterCountNot t v) hcount
      have hCLv : Work.CohenLyndon.CohenLyndonNC v :=
        cohenLyndonNC_magnusStep_fixed v t hvcyc hv1 htv hσv hCLmag
      have h2 := (cohenLyndonNC_conj (G := FreeGroup α) (r := v) c).mpr hCLv
      rwa [hcv] at h2
    · have hltv : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm r := by
        rw [relatorNorm_eq_letterCountNot_of_not_mem t htv]
        exact hcount
      have hCLv : Work.CohenLyndon.CohenLyndonNC v := IH α v hppv hv1 hltv
      have h2 := (cohenLyndonNC_conj (G := FreeGroup α) (r := v) c).mpr hCLv
      rwa [hcv] at h2
  exact cohenLyndonNC_subst_transport htx hcyc hpp hr1 ht hx hσt hσx hCLψr

/-- **The Cohen--Lyndon property for a cyclically reduced relator which is not a proper power**,
by the case analysis of Putnam's Theorem 6.1: the base case `relatorNorm r ≤ 1`, Case 1 (a letter
of exponent sum zero, `cohenLyndonNC_magnusStep`) and Case 2 (`cohenLyndonNC_case2`). -/
theorem cohenLyndonNC_of_isCyclicallyReduced {r : FreeGroup α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hr1 : r ≠ 1)
    (IH : CLBelow.{u} (Work.OROneRel.relatorNorm r)) :
    Work.CohenLyndon.CohenLyndonNC r := by
  classical
  by_cases h : Work.OROneRel.relatorNorm r ≤ 1
  · rcases relatorNorm_le_one h with h1 | ⟨a, ha | ha⟩
    · exact absurd h1 hr1
    · rw [ha]; exact cohenLyndonNC_generator a
    · rw [ha]; exact cohenLyndonNC_invLetter a
  · have h2 : 2 ≤ Work.OROneRel.relatorNorm r := by omega
    by_cases hz : ∃ t ∈ Work.OROneRel.relatorLetters r, Work.OROneRel.sigma t r = 1
    · obtain ⟨t, ht, hσ⟩ := hz
      exact cohenLyndonNC_magnusStep r t hcyc hpp ht hσ IH
    · push_neg at hz
      obtain ⟨t, x, htx, ht, hx⟩ := exists_two_letters hpp hr1 h2
      exact cohenLyndonNC_case2 htx hcyc hpp hr1 ht hx (hz t ht) (hz x hx) IH

/-- **The Cohen--Lyndon property for an arbitrary relator**, by cyclic reduction: replace `r` by
its cyclically reduced conjugate `cyclicReduction r`, transport the induction hypothesis (the norm
does not increase) and transport the conclusion back by conjugation. -/
theorem cohenLyndonNC_main (s : FreeGroup α) (hpp : ¬ Work.OROneRel.IsProperPower s)
    (hne : s ≠ 1) (IH : CLBelow.{u} (Work.OROneRel.relatorNorm s)) :
    Work.CohenLyndon.CohenLyndonNC s := by
  classical
  have hcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.cyclicReduction s) :=
    Work.OROneRel.isCyclicallyReducedRelator_cyclicReduction s
  have hne' : Work.OROneRel.cyclicReduction s ≠ 1 := Work.OROneRel.cyclicReduction_ne_one hne
  have hconj : Work.OROneRel.cyclicConjugator s * Work.OROneRel.cyclicReduction s *
      (Work.OROneRel.cyclicConjugator s)⁻¹ = s :=
    Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv s
  have hpp' : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.cyclicReduction s) := by
    intro h'
    have h2 : Work.OROneRel.IsProperPower (Work.OROneRel.cyclicConjugator s *
        Work.OROneRel.cyclicReduction s * (Work.OROneRel.cyclicConjugator s)⁻¹) :=
      (isProperPower_conj_OROneRel (Work.OROneRel.cyclicReduction s)
        (Work.OROneRel.cyclicConjugator s)).mpr h'
    rw [hconj] at h2
    exact hpp h2
  have IH' : CLBelow.{u} (Work.OROneRel.relatorNorm (Work.OROneRel.cyclicReduction s)) :=
    CLBelow.mono (relatorNorm_cyclicReduction_le s) IH
  have hCL := cohenLyndonNC_of_isCyclicallyReduced hcyc hpp' hne' IH'
  have h2 : Work.CohenLyndon.CohenLyndonNC (Work.OROneRel.cyclicConjugator s *
      Work.OROneRel.cyclicReduction s * (Work.OROneRel.cyclicConjugator s)⁻¹) :=
    (cohenLyndonNC_conj (G := FreeGroup α) (r := Work.OROneRel.cyclicReduction s)
      (Work.OROneRel.cyclicConjugator s)).mpr hCL
  rwa [hconj] at h2

/-- One step of the strong induction: if the Cohen--Lyndon property holds below `N`, it holds
below `N + 1`. -/
theorem CLBelow_succ (N : ℕ) (ih : CLBelow.{u} N) : CLBelow.{u} (N + 1) := by
  intro γ inst s hpp hne hlt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
  · exact ih γ s hpp hne h
  · exact cohenLyndonNC_main s hpp hne (h.symm ▸ ih)

/-- **The strong induction hypothesis holds for every bound**: the Cohen--Lyndon property for every
nontrivial non-proper-power relator over every generating type. -/
theorem CLBelow_all : ∀ N : ℕ, CLBelow.{u} N
  | 0 => fun γ [DecidableEq γ] s _ _ hlt => absurd hlt (Nat.not_lt_zero _)
  | n + 1 => CLBelow_succ n (CLBelow_all n)

/-- **The Cohen--Lyndon property for free groups**: every nontrivial element of a free group which
is not a proper power has the Cohen--Lyndon property. -/
theorem cohenLyndonNC_freeGroup {X : Type u} (u : FreeGroup X) (hu : u ≠ 1)
    (hpp : ¬ Work.ORLocInd.IsProperPower u) :
    Work.CohenLyndon.CohenLyndonNC u := by
  classical
  have hpp' : ¬ Work.OROneRel.IsProperPower u := fun h => hpp ((isProperPower_bridge hu).mpr h)
  exact CLBelow_all (Work.OROneRel.relatorNorm u + 1) X u hpp' hu (Nat.lt_succ_self _)

/-- **The Cohen--Lyndon basis theorem for free groups, quotient form.** -/
theorem cohenLyndonIso_freeGroup {X : Type u} (u : FreeGroup X) (hu : u ≠ 1)
    (hpp : ¬ Work.ORLocInd.IsProperPower u) :
    Work.CohenLyndon.CohenLyndonIso u := by
  have hC : Subgroup.centralizer ({u} : Set (FreeGroup X)) ≤
      Subgroup.normalClosure ({u} : Set (FreeGroup X)) := by
    rw [centralizer_eq_zpowers hu hpp]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_normalClosure (Set.mem_singleton u))
  exact Work.CohenLyndon.cohenLyndon_iso
    (Work.CohenLyndon.CohenLyndon.ofNC hC (cohenLyndonNC_freeGroup u hu hpp))

end Work.ORLocInd.CohenLyndon
