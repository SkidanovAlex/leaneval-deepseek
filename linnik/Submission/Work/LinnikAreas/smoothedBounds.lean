import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.sum_card_divisors_div_le
import Submission.Work.LinnikAreas.harmonic_sum_le_one_add_log

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

theorem smoothedBounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hpos : ∀ n : ℕ, 0 ≤ (Work.LinnikAreas.lam χ n).re)
    (hbd : ∀ n : ℕ, (Work.LinnikAreas.lam χ n).re ≤ ((n.divisors.card : ℕ) : ℝ))
    (β : ℝ) (hβ1 : β ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    1 - 1/x ≤ Work.LinnikAreas.Ssm χ β x ∧
      Work.LinnikAreas.Ssm χ β x ≤ x ^ (1 - β) * (1 + Real.log x) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hNle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  constructor
  · -- lower bound: only the `n = 1` term is needed, all others are nonnegative
    rw [Work.LinnikAreas.Ssm_apply]
    have hf1 : Work.LinnikAreas.lamR χ 1 * ((1 : ℕ) : ℝ) ^ (-β) * (1 - ((1 : ℕ) : ℝ) / x)
        = 1 - 1 / x := by
      rw [Work.LinnikAreas.lamR_apply, Work.LinnikAreas.lam_one, MulChar.map_one,
        Complex.one_re]
      norm_num
    have hmem : 1 ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
    calc 1 - 1 / x
        = Work.LinnikAreas.lamR χ 1 * ((1 : ℕ) : ℝ) ^ (-β) * (1 - ((1 : ℕ) : ℝ) / x) :=
          hf1.symm
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            Work.LinnikAreas.lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) := by
          refine Finset.single_le_sum (s := Finset.Icc 1 ⌊x⌋₊)
            (f := fun n : ℕ => Work.LinnikAreas.lamR χ n * (n : ℝ) ^ (-β)
              * (1 - (n : ℝ) / x)) (fun i hi => ?_) hmem
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hix : (i : ℝ) ≤ x :=
            le_trans (by exact_mod_cast (Finset.mem_Icc.mp hi).2) hNle
          have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
          refine mul_nonneg (mul_nonneg (hpos i) (Real.rpow_nonneg hi0 _)) ?_
          rw [sub_nonneg, div_le_one hx0]
          exact hix
  · -- upper bound
    rw [Work.LinnikAreas.Ssm_apply]
    have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
        Work.LinnikAreas.lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)
          ≤ ((n.divisors.card : ℕ) : ℝ) * (x ^ (1 - β) / (n : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hNle
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
      -- `n ^ (-β) ≤ x ^ (1 - β) / n`
      have step1 : (n : ℝ) ^ (-β) ≤ x ^ (1 - β) / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]
        have hmul : (n : ℝ) ^ (-β) * (n : ℝ) = (n : ℝ) ^ (1 - β) := by
          calc (n : ℝ) ^ (-β) * (n : ℝ)
              = (n : ℝ) ^ (-β) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = (n : ℝ) ^ (-β + 1) := (Real.rpow_add hnpos (-β) 1).symm
            _ = (n : ℝ) ^ (1 - β) := by rw [show -β + 1 = 1 - β by ring]
        rw [hmul]
        exact Real.rpow_le_rpow hnnonneg hnx (by linarith)
      have h1nnn : (0 : ℝ) ≤ 1 - (n : ℝ) / x := by
        rw [sub_nonneg, div_le_one hx0]; exact hnx
      have h1le : (1 - (n : ℝ) / x : ℝ) ≤ 1 := by
        linarith [div_nonneg hnnonneg hx0.le]
      have hxn : (0 : ℝ) ≤ x ^ (1 - β) / (n : ℝ) :=
        div_nonneg (Real.rpow_nonneg hx0.le _) hnnonneg
      have hB : (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) ≤ x ^ (1 - β) / (n : ℝ) := by
        calc (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)
            ≤ (x ^ (1 - β) / (n : ℝ)) * (1 - (n : ℝ) / x) :=
              mul_le_mul_of_nonneg_right step1 h1nnn
          _ ≤ (x ^ (1 - β) / (n : ℝ)) * 1 := mul_le_mul_of_nonneg_left h1le hxn
          _ = x ^ (1 - β) / (n : ℝ) := mul_one _
      have hdnn : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by positivity
      calc Work.LinnikAreas.lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)
          = Work.LinnikAreas.lamR χ n * ((n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)) := by ring
        _ ≤ ((n.divisors.card : ℕ) : ℝ) * (x ^ (1 - β) / (n : ℝ)) :=
              mul_le_mul (hbd n) hB (mul_nonneg (Real.rpow_nonneg hnnonneg _) h1nnn) hdnn
    calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            Work.LinnikAreas.lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((n.divisors.card : ℕ) : ℝ) * (x ^ (1 - β) / (n : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = x ^ (1 - β) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((n.divisors.card : ℕ) : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ ≤ x ^ (1 - β) * (1 + Real.log x) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx0.le _)
          calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ)
              ≤ (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / (m : ℝ)) ^ 2 :=
                sum_card_divisors_div_le ⌊x⌋₊
            _ ≤ (1 + Real.log x) ^ 2 := by
                apply pow_le_pow_left₀ (by positivity) _ 2
                calc ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / (m : ℝ)
                    ≤ 1 + Real.log ((⌊x⌋₊ : ℕ) : ℝ) := harmonic_sum_le_one_add_log ⌊x⌋₊
                  _ ≤ 1 + Real.log x := by
                      have : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN1
                      linarith [Real.log_le_log this hNle]

end

end Work.LinnikAreas
