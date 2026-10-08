import Mathlib
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic

namespace Work.BSW.BSW36

/-- **A nontrivial finite solvable group has a nontrivial normal `p`-subgroup.**

Proof.  By Isaacs Cor 1.28 (`OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial`) the
Fitting subgroup `F(D)` of a nontrivial finite solvable group `D` is nontrivial.  The Fitting
subgroup is the supremum of the `O_p(D) = opCore p D` over the prime divisors `p` of `|D|`
(`fitting_eq_iSup_primeFactors`), so some `O_p(D)` is nontrivial.  That `O_p(D)` is normal
(`opCore.normal`), nontrivial, and a `p`-group (`opCore_isPGroup`). -/
theorem exists_normal_pgroup_of_isSolvable {D : Type} [Group D] [Finite D] [Nontrivial D]
    (hsolv : Group.IsSolvable D) :
    ∃ (r : ℕ) (R : Subgroup D), r.Prime ∧ R ≠ ⊥ ∧ R.Normal ∧ IsPGroup r R := by
  classical
  haveI : Group.IsSolvable D := hsolv
  -- `F(D) ≠ ⊥` for a nontrivial finite solvable group.
  have hF : OddOrder.Isaacs.Ch01.fitting D ≠ ⊥ :=
    OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial D
  -- hence some `O_p(D)` is nontrivial.
  have hkey : ∃ p ∈ (Nat.card D).primeFactors, OddOrder.Isaacs.Ch01.opCore p D ≠ ⊥ := by
    by_contra h
    have hbot : ∀ q : (Nat.card D).primeFactors,
        OddOrder.Isaacs.Ch01.opCore (q : ℕ) D = ⊥ := by
      intro q
      by_contra hq
      exact h ⟨q.1, q.2, hq⟩
    refine hF ?_
    rw [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors]
    exact iSup_eq_bot.mpr hbot
  obtain ⟨p, hp_mem, hpne⟩ := hkey
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  haveI : Fact p.Prime := ⟨hpp⟩
  exact ⟨p, OddOrder.Isaacs.Ch01.opCore p D, hpp, hpne,
    OddOrder.Isaacs.Ch01.opCore.normal p D, OddOrder.Isaacs.Ch01.opCore_isPGroup p D⟩

end Work.BSW.BSW36
