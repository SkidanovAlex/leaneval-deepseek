import Mathlib
import Submission.Work.Maximal.mstWide_defs

namespace Work.Maximal

open Work.BourgainPlan.Maximal

/-- `mstQ' s = (⌈exp((s+1)^{1/10})⌉)!` dominates `exp((s+1)^{1/10})`: the ceiling is at least the
argument and `n! ≥ n`. -/
private theorem le_mstQ'_exp (s : ℕ) :
    Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ (mstQ' s : ℝ) := by
  have h1 : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
      ≤ ((⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ : ℕ) ≤ mstQ' s := by
    rw [mstQ']
    exact Nat.self_le_factorial _
  exact le_trans h1 (by exact_mod_cast h2)

/-- The wide scale `mstWideC P s = (mstQ' s)^{3d}` dominates `exp((s+1)^{1/10})`. -/
private theorem exp_le_mstWideC (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (s : ℕ) :
    Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ mstWideC P s := by
  have hbase : (1 : ℝ) ≤ (mstQ' s : ℝ) := by exact_mod_cast one_le_mstQ' s
  have hexp1 : 1 ≤ 3 * P.natDegree := by omega
  have hpow : (mstQ' s : ℝ) ^ 1 ≤ (mstQ' s : ℝ) ^ (3 * P.natDegree) :=
    pow_le_pow_right₀ hbase hexp1
  rw [pow_one] at hpow
  rw [mstWideC]
  exact le_trans (le_mstQ'_exp s) hpow

/-- For any `c > 0`, eventually `(s+1)^{1/10} < c·s`: sublinear growth. -/
private theorem exists_eventually_rpow_lt_mul (c : ℝ) (hc : 0 < c) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ((s : ℝ) + 1) ^ (1 / 10 : ℝ) < c * (s : ℝ) := by
  refine ⟨max 2 ⌈2 / c ^ 10⌉₊, ?_⟩
  intro s hs
  have hs2 : 2 ≤ s := le_trans (le_max_left _ _) hs
  have hsc : 2 / c ^ 10 ≤ (s : ℝ) := by
    have : (⌈2 / c ^ 10⌉₊ : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hs
    exact le_trans (Nat.le_ceil _) this
  have hs2R : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
  have hs1R : (1 : ℝ) ≤ (s : ℝ) := by linarith
  have hcpos : 0 < c ^ 10 := pow_pos hc 10
  have hcs : (2 : ℝ) ≤ c ^ 10 * (s : ℝ) := by
    have h : 2 ≤ (s : ℝ) * c ^ 10 := by
      rw [div_le_iff₀ hcpos] at hsc; exact hsc
    linarith
  have hspow : (s : ℝ) ≤ (s : ℝ) ^ 8 := by
    have := pow_le_pow_right₀ (a := (s : ℝ)) hs1R (by norm_num : (1 : ℕ) ≤ 8)
    simpa using this
  have hbig : (2 : ℝ) ≤ c ^ 10 * (s : ℝ) ^ 8 := by
    have h : c ^ 10 * (s : ℝ) ≤ c ^ 10 * (s : ℝ) ^ 8 :=
      mul_le_mul_of_nonneg_left hspow hcpos.le
    linarith
  have hsq : (s : ℝ) + 1 < 2 * (s : ℝ) ^ 2 := by
    have h : 0 ≤ ((s : ℝ) - 1) * (2 * (s : ℝ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h]
  have hkey : (s : ℝ) + 1 < (c * (s : ℝ)) ^ 10 := by
    have heq : (c * (s : ℝ)) ^ 10 = (c ^ 10 * (s : ℝ) ^ 8) * (s : ℝ) ^ 2 := by ring
    rw [heq]
    have h2 : 2 * (s : ℝ) ^ 2 ≤ (c ^ 10 * (s : ℝ) ^ 8) * (s : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
    linarith
  have hxnn : 0 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hynn : 0 ≤ c * (s : ℝ) := by positivity
  have hiff := Real.rpow_lt_rpow_iff (x := ((s : ℝ) + 1) ^ (1 / 10 : ℝ))
    (y := c * (s : ℝ)) (z := 10) hxnn hynn (by norm_num)
  have hlhs : (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) = (s : ℝ) + 1 := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ (s : ℝ) + 1 by positivity),
      show (1 / 10 : ℝ) * 10 = 1 by norm_num, Real.rpow_one]
  have hrhs : (c * (s : ℝ)) ^ (10 : ℝ) = (c * (s : ℝ)) ^ 10 := Real.rpow_natCast _ 10
  have hlt : (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) < (c * (s : ℝ)) ^ (10 : ℝ) := by
    rw [hlhs, hrhs]; exact hkey
  exact hiff.mp hlt

theorem mstBump_radius_lt_sep (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ}
    (hχ1 : χ < 1 / 10) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
          < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
      ∧ 1 / (2 * Work.Maximal.mstWideC P s)
          < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
  have hcpos : 0 < ((P.natDegree : ℝ) - χ) * Real.log 2 := by
    have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    exact mul_pos (by linarith) (Real.log_pos (by norm_num))
  obtain ⟨s₀, hs₀⟩ := exists_eventually_rpow_lt_mul _ hcpos
  refine ⟨s₀, fun s hs => ⟨?_, ?_⟩⟩
  · have h2pos : (0 : ℝ) < 2 := by norm_num
    have hrpow : (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
        = Real.exp (Real.log 2 * (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))) :=
      Real.rpow_def_of_pos h2pos _
    have hhalf : (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_log h2pos]; norm_num
    have heq : (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
        = Real.exp (-(Real.log 2 + (s : ℝ) * ((P.natDegree : ℝ) - χ) * Real.log 2)) := by
      rw [hrpow, hhalf, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    apply Real.exp_lt_exp.mpr
    have h := hs₀ s hs
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
        < Real.log 2 + (s : ℝ) * ((P.natDegree : ℝ) - χ) * Real.log 2 := by
      nlinarith [h, hlog]
    linarith
  · have hexp := exp_le_mstWideC P hd s
    have ht : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) < 2 * mstWideC P s := by
      linarith [hexp, Real.exp_pos (((s : ℝ) + 1) ^ (1 / 10 : ℝ))]
    have hpos : 0 < Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := Real.exp_pos _
    have h := one_div_lt_one_div_of_lt hpos ht
    simpa [Real.exp_neg, one_div] using h

end Work.Maximal
