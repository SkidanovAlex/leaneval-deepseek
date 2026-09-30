import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Any prime in `[P, 2P]` is a prime `≤ ⌊2P⌋₊`: in other words
`primesIn P (2P) ⊆ primesLE ⌊2P⌋₊`. -/
theorem primesIn_subset_primesLE (P : ℝ) :
    Work.BMF.primesIn P (2 * P) ⊆ (⌊2 * P⌋₊).primesLE := by
  intro p hp
  rw [Work.BMF.primesIn, Work.BMF.natIcc] at hp
  obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hmem).2, hprime⟩

/-- Chebyshev-type upper bound for the number of primes in `[P, 2P]`:
`#(primesIn P (2P)) ≤ C π₀(P) = C P/log P` for `P ≥ P₀`, from the prime number theorem
(`Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`); the split `P ≤ 2P` and
`∑_{P < p ≤ 2P} log p ≤ θ(2P) ≪ P` give the claim. -/
theorem primesIn_card_le_pi0 : ∃ C P₀ : ℝ, 0 < C ∧ ∀ P : ℝ, P₀ ≤ P →
    ((Work.BMF.primesIn P (2 * P)).card : ℝ) ≤ C * Work.BMF.pi0 P := by
  refine ⟨4 * Real.log 4 + 4, 2, ?_, ?_⟩
  · have h : 0 < Real.log 4 := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  · intro P hP
    have hP0 : 0 < P := by linarith
    have h2P : 1 < 2 * P := by linarith
    have hcard : (Work.BMF.primesIn P (2 * P)).card ≤ (⌊2 * P⌋₊).primeCounting := by
      calc (Work.BMF.primesIn P (2 * P)).card
          ≤ (⌊2 * P⌋₊).primesLE.card := Finset.card_le_card (primesIn_subset_primesLE P)
        _ = (⌊2 * P⌋₊).primeCounting := Nat.primesLE_card_eq_primeCounting _
    have hcardR : ((Work.BMF.primesIn P (2 * P)).card : ℝ) ≤
        ((⌊2 * P⌋₊).primeCounting : ℝ) := by exact_mod_cast hcard
    have hcheb := Chebyshev.pi_le_log4_mul_div h2P
    have hL : 0 < Real.log P := Real.log_pos (by linarith)
    have hM : 0 < Real.log (2 * P) := Real.log_pos h2P
    have hLM : Real.log P ≤ Real.log (2 * P) := Real.log_le_log hP0 (by linarith)
    have hAeq : Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) =
        4 * Real.log 4 * P / Real.log (2 * P) := by
      rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ 2 * P)]
      field_simp
      ring
    have hA : Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) ≤
        4 * Real.log 4 * P / Real.log P := by
      rw [hAeq]
      exact div_le_div_of_nonneg_left (by positivity) hL hLM
    have h1 : Real.log (2 * P) ≤ 2 * Real.sqrt (2 * P) := by
      have h := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 * P by linarith)
        (show (0:ℝ) < 1/2 by norm_num)
      have h' : (2 * P) ^ ((1:ℝ)/2) / (1/2) = 2 * Real.sqrt (2 * P) := by
        rw [← Real.sqrt_eq_rpow]; ring
      rw [h'] at h
      exact h
    have h2 : Real.sqrt (2 * P) * Real.log (2 * P) ≤ 4 * P := by
      have hsq : 0 ≤ Real.sqrt (2 * P) := Real.sqrt_nonneg _
      calc Real.sqrt (2 * P) * Real.log (2 * P)
            ≤ Real.sqrt (2 * P) * (2 * Real.sqrt (2 * P)) :=
              mul_le_mul_of_nonneg_left h1 hsq
        _ = 2 * (Real.sqrt (2 * P)) ^ 2 := by ring
        _ = 2 * (2 * P) := by rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * P)]
        _ = 4 * P := by ring
    have hB : Real.sqrt (2 * P) ≤ 4 * P / Real.log P := by
      have h3 : Real.sqrt (2 * P) ≤ 4 * P / Real.log (2 * P) := by
        rw [le_div_iff₀ hM]
        exact h2
      calc Real.sqrt (2 * P) ≤ 4 * P / Real.log (2 * P) := h3
        _ ≤ 4 * P / Real.log P := div_le_div_of_nonneg_left (by positivity) hL hLM
    calc ((Work.BMF.primesIn P (2 * P)).card : ℝ)
        ≤ ((⌊2 * P⌋₊).primeCounting : ℝ) := hcardR
      _ ≤ Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) + Real.sqrt (2 * P) := hcheb
      _ ≤ (4 * Real.log 4 + 4) * P / Real.log P := by
          calc Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) + Real.sqrt (2 * P)
              ≤ 4 * Real.log 4 * P / Real.log P + 4 * P / Real.log P := add_le_add hA hB
            _ = (4 * Real.log 4 + 4) * P / Real.log P := by ring
      _ = (4 * Real.log 4 + 4) * Work.BMF.pi0 P := by
          rw [Work.BMF.pi0]; ring

end Work.BMF
