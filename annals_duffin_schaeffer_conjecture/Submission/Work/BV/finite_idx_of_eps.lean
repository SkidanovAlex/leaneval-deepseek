/-
# The index set of the `d`-scaled Duffin–Schaeffer system is "co-small"

`finite_idx_of_eps` is the elementary finiteness statement behind the
Beresnevich–Velani mass-transference construction: for `ψ ≤ 1/2` and any `ε > 0`,
only finitely many coprime pairs `(a,q)` of the truncated index set `Idx ψ d` carry
a radius `rrP ψ (a,q) = ψ(q)/q` at least `ε`.

Indeed `ψ(q)/q ≤ (1/2)/q`, so `ε ≤ ψ(q)/q` forces `q ≤ 1/(2ε)`; there are only
finitely many such `q`.  For each fixed `q` the numerator `a` is bounded by
`numBound ψ d q`, a real number, so again only finitely many `a` occur.  This is
exactly what is needed to enumerate the system by a sequence (the property
`MassTransference.CoSmall`) and hence to run the mass-distribution argument.

Note that neither `0 < d`, `d < 1` nor the actual value of `numBound ψ d q` beyond
its finiteness are used: for a fixed denominator the truncation bound is a real
number, and it is the smallness hypothesis `ψ ≤ 1/2` that bounds the denominators.
-/
import Mathlib
import Submission.Work.BV.Bridge

open scoped NNReal Nat

namespace Work.BV

/-- A set of natural numbers bounded above by a real number is finite. -/
lemma finite_setOf_nat_le_real (R : ℝ) : ({a : ℕ | (a : ℝ) ≤ R}).Finite := by
  refine Set.Finite.subset (Set.finite_le_nat ⌈R⌉₊) ?_
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  have h : (a : ℝ) ≤ (⌈R⌉₊ : ℝ) := le_trans ha (Nat.le_ceil R)
  exact_mod_cast h

/-- A set of positive natural numbers bounded above by a real number is finite. -/
lemma finite_setOf_pnat_le_real (R : ℝ) : ({q : ℕ+ | (q : ℝ) ≤ R}).Finite := by
  have h : ((fun q : ℕ+ => (q : ℕ)) ⁻¹' {i : ℕ | i ≤ ⌈R⌉₊}).Finite :=
    (Set.finite_le_nat ⌈R⌉₊).preimage (f := fun q : ℕ+ => (q : ℕ))
      Subtype.val_injective.injOn
  refine Set.Finite.subset h ?_
  intro q hq
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hq ⊢
  have : (q : ℝ) ≤ (⌈R⌉₊ : ℝ) := le_trans hq (Nat.le_ceil R)
  exact_mod_cast this

/-- For `ψ ≤ 1/2` and `ε > 0`, only finitely many truncated coprime pairs `(a,q)`
carry a `ψ`-radius at least `ε`. -/
theorem finite_idx_of_eps (ψ : PNat → NNReal) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (hψ : ∀ q : PNat, ψ q ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ({p : Submission.Main.Idx ψ d | ε ≤ Submission.Main.rrP ψ p.1}.Finite) := by
  -- The ambient finite set of pairs: bounded denominator and bounded numerator.
  have hS0 : ({p : ℕ × ℕ+ | (p.2 : ℝ) ≤ 1 / (2 * ε) ∧
      ((p.1 : ℕ) : ℝ) ≤ Submission.Main.numBound ψ d p.2}).Finite := by
    have hQ := finite_setOf_pnat_le_real (1 / (2 * ε))
    -- For a fixed denominator `q` only finitely many numerators occur.
    have hpiece : ∀ q : ℕ+, ({p : ℕ × ℕ+ | p.2 = q ∧
        ((p.1 : ℕ) : ℝ) ≤ Submission.Main.numBound ψ d p.2}).Finite := by
      intro q
      have himg := (finite_setOf_nat_le_real (Submission.Main.numBound ψ d q)).image
        (fun a : ℕ => (a, q))
      refine himg.subset ?_
      rintro ⟨a, b⟩ ⟨hb, ha⟩
      have hb' : b = q := hb
      refine ⟨a, ?_, ?_⟩
      · simpa [hb'] using ha
      · rw [Prod.mk.injEq]
        exact ⟨rfl, hb'.symm⟩
    refine Set.Finite.subset (hQ.biUnion (fun q _ => hpiece q)) ?_
    rintro p ⟨hp2, hp1⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨p.2, hp2, rfl, hp1⟩
  -- Every index of large radius has its underlying pair in `hS0`.
  have himg : (Subtype.val '' ({p : Submission.Main.Idx ψ d |
      ε ≤ Submission.Main.rrP ψ p.1})).Finite := by
    refine hS0.subset ?_
    rintro p ⟨q, hq, rfl⟩
    refine ⟨?_, ?_⟩
    · -- `ψ(q)/q ≥ ε` with `ψ(q) ≤ 1/2` forces `q ≤ 1/(2ε)`.
      have hq0 : (0 : ℝ) < ((q.1).2 : ℝ) := by exact_mod_cast PNat.pos (q.1).2
      have hψle : (ψ (q.1).2 : ℝ) ≤ 1 / 2 := by
        have h2 : (ψ (q.1).2 : ℝ) ≤ ((1 / 2 : NNReal) : ℝ) := hψ (q.1).2
        simpa using h2
      have hrr : Submission.Main.rrP ψ q.1 ≤ (1 / 2) / ((q.1).2 : ℝ) := by
        rw [Submission.Main.rrP]
        exact div_le_div_of_nonneg_right hψle hq0.le
      have hε' : ε ≤ (1 / 2) / ((q.1).2 : ℝ) := le_trans hq hrr
      rw [le_div_iff₀ hq0] at hε'
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)]
      nlinarith
    · -- The numerator bound is part of the definition of `Idx`.
      exact (q.2).2
  exact himg.of_finite_image Subtype.val_injective.injOn

end Work.BV
