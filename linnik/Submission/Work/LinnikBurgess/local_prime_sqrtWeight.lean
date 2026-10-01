import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikAreas.CorrAllR.Defs
import Submission.Work.LinnikAreas.CorrAllR.corrSumV_prime_good

open scoped BigOperators

namespace Work.LinnikBurgess

/-! ### The prime-modulus square-root weighted correlation bound (Burgess route, unit U9).

The correlation `∑_x χ (∏_l (x + a_l)) · conj (χ (∏_l (x + b_l)))` of two products of three
linear factors is `≤ 6 √p · ∏_{l ≠ i} √(gcd (p, |v_i - v_l|))`, where `v = shift a b` is the
six-shift vector.

Two regimes:

* if some `v_j` (`j ≠ i`) is congruent to `v_i` modulo `p`, the `gcd`-weight has a factor
  `√p`, so the right-hand side is `≥ 6p`, which dominates the trivial bound `≤ p`;
* otherwise `v_i` is unique modulo `p`, so the local Weil bound
  (`Work.LinnikAreas.CorrAllV_prime_good`) gives `≤ 6 √p`, and the weight is `≥ 1`. -/

/-- `shift a b` is the append of `a` and `b`. -/
lemma shift_eq_combShift (a b : Fin 3 → ℕ) :
    shift a b = Work.LinnikAreas.combShift a b := by
  funext i
  refine Fin.addCases (m := 3) (n := 3)
    (motive := fun i => shift a b i = Work.LinnikAreas.combShift a b i) ?_ ?_ i
  · intro l
    rw [Work.LinnikAreas.combShift_castAdd]
    fin_cases l <;> rfl
  · intro l
    rw [Work.LinnikAreas.combShift_natAdd]
    fin_cases l <;> rfl

/-- The `gcd` weight is always at least `1`. -/
lemma one_le_sqrtGcdW {p : ℕ} [Fact p.Prime] (i : Fin 6) (v : Fin 6 → ℕ) :
    1 ≤ sqrtGcdW p i v := by
  rw [sqrtGcdW]
  refine Finset.one_le_prod₀ (fun j _ => ?_)
  rw [Real.one_le_sqrt]
  have h : 0 < Nat.gcd p (((v i : ℤ) - (v j : ℤ)).natAbs) :=
    Nat.gcd_pos_of_pos_left _ (Fact.out : p.Prime).pos
  exact_mod_cast h

/-- If some other shift is congruent to `v i` modulo `p`, the `gcd` weight is at least `√p`. -/
lemma sqrtGcdW_ge_sqrt_of_collision {p : ℕ} [Fact p.Prime] {i : Fin 6} {v : Fin 6 → ℕ}
    (h : ∃ j : Fin 6, j ≠ i ∧ (v i : ZMod p) = (v j : ZMod p)) :
    Real.sqrt (p : ℝ) ≤ sqrtGcdW p i v := by
  obtain ⟨j, hji, hjeq⟩ := h
  rw [sqrtGcdW]
  have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i)
    (fun l => Real.sqrt ((Nat.gcd p (((v i : ℤ) - (v l : ℤ)).natAbs) : ℕ) : ℝ)) hmem]
  have hgcd : Nat.gcd p (((v i : ℤ) - (v j : ℤ)).natAbs) = p := by
    rw [Nat.gcd_eq_left_iff_dvd]
    have h0 : ((((v i : ℤ) - (v j : ℤ)) : ℤ) : ZMod p) = 0 := by
      push_cast; rw [hjeq, sub_self]
    have h1 : (p : ℤ) ∣ ((v i : ℤ) - (v j : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h1)
  have hfac : Real.sqrt ((Nat.gcd p (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ)
      = Real.sqrt (p : ℝ) := by rw [hgcd]
  rw [hfac]
  have hrest : 1 ≤ ∏ x ∈ (Finset.univ.erase i).erase j,
      Real.sqrt ((Nat.gcd p (((v i : ℤ) - (v x : ℤ)).natAbs) : ℕ) : ℝ) := by
    refine Finset.one_le_prod₀ (fun x _ => ?_)
    rw [Real.one_le_sqrt]
    have h : 0 < Nat.gcd p (((v i : ℤ) - (v x : ℤ)).natAbs) :=
      Nat.gcd_pos_of_pos_left _ (Fact.out : p.Prime).pos
    exact_mod_cast h
  have hsp : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  calc Real.sqrt (p : ℝ) = Real.sqrt (p : ℝ) * 1 := by ring
    _ ≤ Real.sqrt (p : ℝ) * ∏ x ∈ (Finset.univ.erase i).erase j,
          Real.sqrt ((Nat.gcd p (((v i : ℤ) - (v x : ℤ)).natAbs) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hrest hsp

theorem local_prime_sqrtWeight {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6) :
    ‖∑ x : ZMod p, χ (∏ l : Fin 3, (x + (a l : ZMod p)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod p))))‖
      ≤ 6 * Real.sqrt p * sqrtGcdW p i (shift a b) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hsum : (∑ x : ZMod p, χ (∏ l : Fin 3, (x + (a l : ZMod p)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod p)))))
      = Work.LinnikAreas.corrSumV p χ 3 (shift a b) := by
    rw [shift_eq_combShift, Work.LinnikAreas.corrSumV_combShift]
    rfl
  rw [hsum]
  have htriv : ‖Work.LinnikAreas.corrSumV p χ 3 (shift a b)‖ ≤ (p : ℝ) :=
    Work.LinnikAreas.corrSumV_norm_le_card p χ 3 (shift a b)
  have hW1 : (1 : ℝ) ≤ sqrtGcdW p i (shift a b) := one_le_sqrtGcdW i (shift a b)
  have hsp : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  by_cases hcoll : ∃ j : Fin 6, j ≠ i ∧ (shift a b i : ZMod p) = (shift a b j : ZMod p)
  · have hWp : Real.sqrt (p : ℝ) ≤ sqrtGcdW p i (shift a b) :=
      sqrtGcdW_ge_sqrt_of_collision hcoll
    have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt (by positivity)
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hA : 6 * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)
        ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) :=
      mul_le_mul_of_nonneg_left hWp (by positivity)
    have hB : 6 * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = 6 * (p : ℝ) := by
      rw [mul_assoc, hsq]
    nlinarith [htriv, hA, hB, hp0]
  · push Not at hcoll
    have huniq : Work.LinnikAreas.IsUniqModV p (r := 3) (shift a b) i := by
      intro j hj hmod
      exact hcoll j hj ((ZMod.natCast_eq_natCast_iff (shift a b j) (shift a b i) p).mpr hmod).symm
    have hgood : ‖Work.LinnikAreas.corrSumV p χ 3 (shift a b)‖ ≤ 6 * Real.sqrt (p : ℝ) := by
      have h := Work.LinnikAreas.CorrAllR.corrSumV_prime_good p χ h1 (r := 3) (by norm_num) (shift a b) i huniq
      norm_num at h
      exact h
    have hWnn : (0 : ℝ) ≤ sqrtGcdW p i (shift a b) := le_trans zero_le_one hW1
    have hA : 6 * Real.sqrt (p : ℝ) ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) := by
      calc 6 * Real.sqrt (p : ℝ) = 6 * Real.sqrt (p : ℝ) * 1 := by ring
        _ ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) :=
            mul_le_mul_of_nonneg_left hW1 (by positivity)
    linarith [hgood, hA]

end Work.LinnikBurgess
