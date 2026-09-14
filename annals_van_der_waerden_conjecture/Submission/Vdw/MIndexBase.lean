import Mathlib
import Submission.Vdw.FourierPrime
import Submission.Vdw.FourierExpand
import Submission.Vdw.IndexBounded

open Polynomial Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The single-prime §4 input: the two extreme index values

`FourierPrime.MIndexBound` asks for the paper's Proposition `ftgen2` bound
`‖indexFourierCoeff p n k a‖ ≤ C·p^{n-k-1/2}` for every `a ≠ 0` and every
`k ≤ n`.

This module records the two extreme values of `k`:

* `k = 0`: the index condition is vacuous, so the Fourier coefficient is the
  *complete* character sum `Σ_{v : (ZMod p)^n} stdAddChar (a·v)`, which vanishes
  for `a ≠ 0` by orthogonality (`FourierExpand.sum_stdAddChar_coord`);
* `k = n`: no degree-`n` polynomial has index `≥ n` (`IndexBounded.
  indexClass_self_false`), so the index set is empty and the coefficient is
  `0`.

Consequently `MIndexBound` for `n ≥ 1` follows from its restriction to the
*interior* range `1 ≤ k < n` (`MIndexBoundMid`), which is the range actually
needed in the applications (`k = v_p(D)` with `p` a prime divisor of `D`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- For `k = 0` the index condition is vacuous: the index set is everything. -/
theorem indexClassFinset_zero (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    indexClassFinset p n 0 = Finset.univ := by
  classical
  refine Finset.eq_univ_of_forall (fun v => ?_)
  rw [indexClassFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Nat.zero_le _⟩

/-- **The `k = 0` Fourier coefficient**: a complete character sum, which
vanishes for every nonzero frequency. -/
theorem indexFourierCoeff_zero (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (a : Fin n → ZMod p) (ha : a ≠ 0) :
    indexFourierCoeff p n 0 a = 0 := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [indexFourierCoeff, indexClassFinset_zero]
  have h := sum_stdAddChar_coord p n a
  have hswap : (∑ v : Fin n → ZMod p, ZMod.stdAddChar (∑ i, a i * v i))
      = ∑ v : Fin n → ZMod p, ZMod.stdAddChar (∑ i, v i * a i) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    refine congrArg ZMod.stdAddChar ?_
    exact Finset.sum_congr rfl (fun i _ => mul_comm (a i) (v i))
  rw [hswap, h, if_neg ha]

/-- **The `k = n` Fourier coefficient**: the index set is empty, so the
coefficient vanishes. -/
theorem indexFourierCoeff_top (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → ZMod p) :
    indexFourierCoeff p n n a = 0 := by
  classical
  rw [indexFourierCoeff]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  rw [indexClassFinset, Finset.mem_filter] at hv
  exact absurd hv.2 (indexClass_self_false (F := ZMod p) n hn v)

/-- **The single-prime §4 input restricted to the interior range**
`1 ≤ k < n` — the range in which the bound has content. -/
def MIndexBoundMid (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (p : ℕ) [Fact (Nat.Prime p)], ∀ k : ℕ, 1 ≤ k → k < n →
      ∀ a : Fin n → ZMod p, a ≠ 0 →
        ‖indexFourierCoeff p n k a‖ ≤ C * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2)

/-- **`MIndexBound` follows from its interior range.** -/
theorem MIndexBound_of_mid (n : ℕ) (hn : 1 ≤ n) (h : MIndexBoundMid n) :
    MIndexBound n := by
  obtain ⟨C, hC, hCb⟩ := h
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro p _inst k hk a ha
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, indexFourierCoeff_zero p n a ha]
    simp only [norm_zero]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have h1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
      exact_mod_cast h1
    have : (0 : ℝ) ≤ (max C 1) * (p : ℝ) ^ ((n : ℝ) - (0 : ℝ) - 1 / 2) := by positivity
    linarith
  · rcases lt_or_eq_of_le hk with hlt | heq
    · refine le_trans (hCb p k hpos hlt a ha) ?_
      refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [heq, indexFourierCoeff_top p n hn a]
      simp only [norm_zero]
      have hnn : (0 : ℝ) ≤ (max C 1) * (p : ℝ) ^ ((n : ℝ) - (n : ℝ) - 1 / 2) := by positivity
      linarith

end
end Submission.Vdw
