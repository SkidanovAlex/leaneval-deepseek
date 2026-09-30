import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.mertens

theorem primeRpow_small_shift {y x ε : ℝ} (hy : 2 < y) (hy11 : y < 11) (hx : 11 ≤ x) (hε : 0 < ε) :
    (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε)) ≤
      (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => 11 < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε)) + 2 := by
  -- Abstract the two finsets.
  set A : Finset ℕ := (⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ)) with hA
  set B : Finset ℕ := (⌊x⌋₊).primesLE.filter (fun p : ℕ => 11 < (p : ℝ)) with hB
  -- Every prime above 11 is above y, since y < 11.
  have hBA : B ⊆ A := by
    intro p hp
    simp only [hA, hB, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, lt_trans hy11 hp.2⟩
  -- Split the sum over A into the sum over B plus the sum over the extra primes.
  have hsplit :
      (∑ q ∈ A \ B, (1 : ℝ) / (q : ℝ) ^ (1 + ε)) + (∑ q ∈ B, (1 : ℝ) / (q : ℝ) ^ (1 + ε))
        = (∑ q ∈ A, (1 : ℝ) / (q : ℝ) ^ (1 + ε)) :=
    Finset.sum_sdiff hBA
  rw [← hsplit]
  -- It remains to bound the sum over the extra primes A \ B by 2.
  have hC : ∑ q ∈ A \ B, (1 : ℝ) / (q : ℝ) ^ (1 + ε) ≤ 2 := by
    -- Each term is at most 1/q.
    have hterm : ∀ q ∈ A \ B, (1 : ℝ) / (q : ℝ) ^ (1 + ε) ≤ (1 : ℝ) / (q : ℝ) := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpA, _⟩ := hp
      rw [hA, Finset.mem_filter] at hpA
      obtain ⟨_, hpy⟩ := hpA
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        have : (2 : ℝ) < (p : ℝ) := lt_trans hy hpy
        linarith
      have hmono : (p : ℝ) ≤ (p : ℝ) ^ (1 + ε) := by
        have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : (1 : ℝ) ≤ 1 + ε)
        rwa [Real.rpow_one] at h
      exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < (p : ℝ)) hmono
    have h1 : ∑ q ∈ A \ B, (1 : ℝ) / (q : ℝ) ^ (1 + ε) ≤ ∑ q ∈ A \ B, (1 : ℝ) / (q : ℝ) :=
      Finset.sum_le_sum hterm
    -- The extra primes lie in {3, …, 11}, so we may sum over that whole interval.
    have hsub : A \ B ⊆ (Finset.Icc 3 11 : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpA, hpnb⟩ := hp
      rw [hA, Finset.mem_filter] at hpA
      obtain ⟨hps, hpy⟩ := hpA
      have hpn11 : ¬ (11 < (p : ℝ)) := by
        intro h
        apply hpnb
        rw [hB, Finset.mem_filter]
        exact ⟨hps, h⟩
      have hp11r : (p : ℝ) ≤ 11 := le_of_not_gt hpn11
      have hp2 : (2 : ℝ) < (p : ℝ) := lt_trans hy hpy
      have hp11 : p ≤ 11 := by exact_mod_cast hp11r
      have hp3 : 3 ≤ p := by
        have : (2 : ℕ) < p := by exact_mod_cast hp2
        omega
      exact Finset.mem_Icc.mpr ⟨hp3, hp11⟩
    have h2 : ∑ q ∈ A \ B, (1 : ℝ) / (q : ℝ)
        ≤ ∑ n ∈ (Finset.Icc 3 11 : Finset ℕ), (1 : ℝ) / (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have h3 : ∑ n ∈ (Finset.Icc 3 11 : Finset ℕ), (1 : ℝ) / (n : ℝ) < 2 := by
      norm_num [Finset.sum_Icc_succ_top]
    linarith
  linarith

end Work.BMF.mertens
