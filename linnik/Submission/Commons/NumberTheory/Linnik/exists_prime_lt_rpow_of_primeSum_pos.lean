import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds

namespace Commons.NumberTheory.Linnik

theorem exists_prime_lt_rpow_of_primeSum_pos {q a X : ℕ} (hq : 2 ≤ q) {L K : ℝ} (hK : 0 < K)
    (h2K : 2 * K < L)
    (hpos : 0 < ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
      (Real.log (p : ℝ) / (p : ℝ)) * Commons.NumberTheory.Linnik.tentWeight L K (Real.log (p : ℝ) / Real.log (q : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < (q : ℝ) ^ L := by
  by_contra hcon
  push Not at hcon
  have hsum0 :
      ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
        (Real.log (p : ℝ) / (p : ℝ)) *
          tentWeight L K (Real.log (p : ℝ) / Real.log (q : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hprime, hmod⟩ := hp
    have hple : (q : ℝ) ^ L ≤ (p : ℝ) := hcon p hprime hmod
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hqpos : 0 < (q : ℝ) := by linarith
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
    have hlogle : Real.log ((q : ℝ) ^ L) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos hqpos L) hple
    rw [Real.log_rpow hqpos L] at hlogle
    have hx : L ≤ Real.log (p : ℝ) / Real.log (q : ℝ) :=
      (le_div_iff₀ hlogq).mpr hlogle
    have hw := (tentWeight_bounds hK.le h2K.le).2.2.2 (Real.log (p : ℝ) / Real.log (q : ℝ)) hx
    rw [hw, mul_zero]
  rw [hsum0] at hpos
  exact lt_irrefl 0 hpos

end Commons.NumberTheory.Linnik