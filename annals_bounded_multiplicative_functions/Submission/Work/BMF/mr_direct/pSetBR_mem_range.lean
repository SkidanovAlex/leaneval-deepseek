import Mathlib
import Submission.Work.BMF.mr_direct.eboundR_defs
import Submission.Work.BMF.mr_direct.range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- A member `i = (p, m)` of `pSetBR K P Q A B` has merged frequency `ebnn i = p * m` lying in
`[A e^{-1/K}, B e^{1/K}]`, and never in the unrescaled interval `[A, B]`.

The lower/upper bounds come from `p ∈ [e^{j/K}, e^{(j+1)/K}]` where `j = jdex K p`, combined with
`m ∈ winIdxR K A B j` (i.e. `m ∈ [A e^{-(j+1)/K}, B e^{-j/K}]`); the non-membership in `[A,B]`
is exactly the filter condition `m ∉ natIcc (A/p) (B/p)`, rescaled by `p`. -/
theorem pSetBR_mem_range (K P Q A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hK : 1 ≤ K)
    (i : Σ _ : ℕ, ℕ) (hi : i ∈ Work.BMF.mr_direct.pSetBR K P Q A B) :
    Work.BMF.mr_direct.ebnn i ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) ∧
      Work.BMF.mr_direct.ebnn i ∉ Work.BMF.natIcc A B := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_trans hA hAB)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hAnonneg : (0 : ℝ) ≤ A := hApos.le
  have hBnonneg : (0 : ℝ) ≤ B := hBpos.le
  -- Unpack the sigma membership: i.1 is a prime in [P,Q], i.2 is in the window minus [A/p,B/p].
  rw [Work.BMF.mr_direct.pSetBR, Finset.mem_sigma] at hi
  obtain ⟨hp_mem, hm_mem⟩ := hi
  rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hp_mem
  obtain ⟨-, hp_prime⟩ := hp_mem
  rw [Finset.mem_filter] at hm_mem
  obtain ⟨hm_win, hm_not⟩ := hm_mem
  have hppos_nat : 0 < i.1 := hp_prime.pos
  have hppos : (0 : ℝ) < (i.1 : ℝ) := by exact_mod_cast hppos_nat
  have hlogpos : 0 < Real.log (i.1 : ℝ) := Real.log_pos (by exact_mod_cast hp_prime.one_lt)
  -- Bounds for j = jdex K i.1 :  j ≤ K log p < j+1.
  have hj_le : ((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) ≤ K * Real.log (i.1 : ℝ) := by
    rw [Work.BMF.mrDirect.jdex]
    exact Nat.floor_le (le_of_lt (mul_pos hKpos hlogpos))
  have hj_lt : K * Real.log (i.1 : ℝ) < ((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1 := by
    rw [Work.BMF.mrDirect.jdex]
    exact Nat.lt_floor_add_one _
  -- p ∈ [exp(j/K), exp((j+1)/K)].
  have hexp_lo : Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) ≤ (i.1 : ℝ) := by
    rw [← Real.exp_log hppos]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hKpos, mul_comm]
    exact hj_le
  have hexp_hi : (i.1 : ℝ) ≤ Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) := by
    rw [← Real.exp_log hppos]
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hKpos, mul_comm]
    linarith
  -- m ∈ [A exp(-(j+1)/K), B exp(-j/K)].
  have hb2 : (0 : ℝ) ≤ B * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K) :=
    mul_nonneg hBnonneg (Real.exp_pos _).le
  obtain ⟨hm_lo, hm_hi⟩ := (Work.BMF.mrDirect.mem_winIdxR hb2).mp hm_win
  -- Cast of ebnn i.
  have hcast : ((ebnn i : ℕ) : ℝ) = (i.1 : ℝ) * (i.2 : ℝ) := by
    simp only [Work.BMF.mr_direct.ebnn, Nat.cast_mul]
  -- Exponential identities collapsing the product bounds.
  have hkey : Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
      Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) = Real.exp (-(1 / K)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey2 : Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
      Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K) = Real.exp (1 / K) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEq_lo : Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
      (A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) =
      A * Real.exp (-(1 / K)) := by
    rw [show Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
        (A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) =
        A * (Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
          Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) by ring, hkey]
  have hEq_hi : Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
      (B * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) =
      B * Real.exp (1 / K) := by
    rw [show Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
        (B * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) =
        B * (Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
          Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) by ring, hkey2]
  constructor
  · rw [Work.BMF.mrDirect.mem_natIcc
      (show (0 : ℝ) ≤ B * Real.exp (1 / K) by positivity)]
    constructor
    · rw [hcast]
      calc A * Real.exp (-(1 / K))
          = Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
              (A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) := hEq_lo.symm
        _ ≤ (i.1 : ℝ) * (i.2 : ℝ) :=
              mul_le_mul hexp_lo hm_lo (mul_nonneg hAnonneg (Real.exp_pos _).le) hppos.le
    · rw [hcast]
      calc (i.1 : ℝ) * (i.2 : ℝ)
          ≤ Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
              (B * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) :=
              mul_le_mul hexp_hi hm_hi (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = B * Real.exp (1 / K) := hEq_hi
  · intro hmem
    rw [Work.BMF.mrDirect.mem_natIcc hBnonneg] at hmem
    rw [hcast] at hmem
    apply hm_not
    rw [Work.BMF.mrDirect.mem_natIcc
      (show (0 : ℝ) ≤ B / (i.1 : ℝ) by positivity)]
    constructor
    · rw [div_le_iff₀ hppos, mul_comm]
      exact hmem.1
    · rw [le_div_iff₀ hppos, mul_comm]
      exact hmem.2

end Work.BMF.mr_direct
