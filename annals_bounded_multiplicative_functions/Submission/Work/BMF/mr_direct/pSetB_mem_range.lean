import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.ebound_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- A member `i = (p, m)` of `pSetB K P Q X` has merged frequency `ebnn i = p * m` lying in
`[X e^{-1/K}, 2X e^{1/K}]`, and never in the unrescaled dyadic interval `[X, 2X]`.

The lower/upper bounds come from `p ∈ [e^{j/K}, e^{(j+1)/K}]` where `j = jdex K p`, combined with
`m ∈ winIdx K X j`; the non-membership in `[X,2X]` is exactly the filter condition
`m ∉ natIcc (X/p) (2X/p)`, rescaled by `p`. -/
theorem pSetB_mem_range (K P Q X : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (i : Σ _ : ℕ, ℕ)
    (hi : i ∈ Work.BMF.mrDirect.pSetB K P Q X) :
    Work.BMF.mr_direct.ebnn i ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) ∧
      Work.BMF.mr_direct.ebnn i ∉ Work.BMF.natIcc X (2 * X) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  -- Unpack the sigma membership: i.1 is a prime in [P,Q], i.2 is in the window minus [X/p,2X/p].
  rw [Work.BMF.mrDirect.pSetB, Finset.mem_sigma] at hi
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
  -- m ∈ [X exp(-(j+1)/K), 2X exp(-j/K)].
  rw [Work.BMF.mrDirect.winIdx] at hm_win
  have hb2 : (0 : ℝ) ≤ 2 * X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K) := by
    positivity
  obtain ⟨hm_lo, hm_hi⟩ := (Work.BMF.mrDirect.mem_natIcc hb2).mp hm_win
  -- Cast of ebnn i.
  have hcast : ((ebnn i : ℕ) : ℝ) = (i.1 : ℝ) * (i.2 : ℝ) := by simp [ebnn]
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
      (X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) =
      X * Real.exp (-(1 / K)) := by
    rw [show Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
        (X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) =
        X * (Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
          Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) by ring, hkey]
  have hEq_hi : Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
      (2 * X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) =
      2 * X * Real.exp (1 / K) := by
    rw [show Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
        (2 * X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) =
        2 * X * (Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
          Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) by ring, hkey2]
  constructor
  · rw [Work.BMF.mrDirect.mem_natIcc (show (0 : ℝ) ≤ 2 * X * Real.exp (1 / K) by positivity)]
    constructor
    · rw [hcast]
      calc X * Real.exp (-(1 / K))
          = Real.exp (((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) / K) *
              (X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)) := hEq_lo.symm
        _ ≤ (i.1 : ℝ) * (i.2 : ℝ) :=
              mul_le_mul hexp_lo hm_lo (by positivity) hppos.le
    · rw [hcast]
      calc (i.1 : ℝ) * (i.2 : ℝ)
          ≤ Real.exp ((((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) *
              (2 * X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ)) / K)) :=
              mul_le_mul hexp_hi hm_hi (by positivity) (by positivity)
        _ = 2 * X * Real.exp (1 / K) := hEq_hi
  · intro hmem
    rw [Work.BMF.mrDirect.mem_natIcc (show (0 : ℝ) ≤ 2 * X by positivity)] at hmem
    rw [hcast] at hmem
    apply hm_not
    rw [Work.BMF.mrDirect.mem_natIcc (show (0 : ℝ) ≤ 2 * X / (i.1 : ℝ) by positivity)]
    constructor
    · rw [div_le_iff₀ hppos, mul_comm]
      exact hmem.1
    · rw [le_div_iff₀ hppos, mul_comm]
      exact hmem.2

end Work.BMF.mr_direct
