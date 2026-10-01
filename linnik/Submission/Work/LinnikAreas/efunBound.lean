import Mathlib
import Submission.Work.LinnikAreas.efunAux
import Submission.Work.LinnikAreas.efunCore
import Submission.Work.LinnikAreas.efunRealReduce

namespace Work.LinnikAreas

open DirichletCharacter
open scoped BigOperators

/-- **Error term bound for `λ = 1 * χ`.**  There is an absolute constant `C` such that for every
non-principal Dirichlet character `χ` mod `q` and every `x ≥ 1`,
`‖A(x) - x L(1,χ)‖ ≤ C √q log(2q+2) √x`. -/
theorem efunBound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      ‖Work.LinnikAreas.Efun χ x‖
        ≤ C * Real.sqrt (q:ℝ) * Real.log (2 * (q:ℝ) + 2) * Real.sqrt x := by
  obtain ⟨B₁, hB₁pos, hPV⟩ := chiPrefix_bound
  obtain ⟨B₂, hB₂pos, hLS⟩ := LSeries_partial_bound_one
  refine ⟨(1 + 2*B₁ + 2*B₂) + (1 + 2*B₂) + 1, by positivity, ?_⟩
  intro q _inst χ hχ x hx
  by_cases hq1 : q = 1
  · subst hq1
    exact absurd (DirichletCharacter.level_one χ) hχ
  · have hq2 : 2 ≤ q := by
      have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    have hB₁ : 0 ≤ B₁ := le_of_lt hB₁pos
    have hB₂ : 0 ≤ B₂ := le_of_lt hB₂pos
    have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hsqrtq1 : (1:ℝ) ≤ Real.sqrt (q:ℝ) := by
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (q:ℝ) := Real.sqrt_le_sqrt hq1R
    have hlog1 : (1:ℝ) ≤ Real.log (2*(q:ℝ)+2) := by
      have h4 : (4:ℝ) ≤ 2*(q:ℝ)+2 := by
        have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
        linarith
      have hlog4 : Real.log 4 ≤ Real.log (2*(q:ℝ)+2) := Real.log_le_log (by norm_num) h4
      have h24 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      rw [h24] at hlog4
      nlinarith [Real.log_two_gt_d9]
    have hsq0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
    have hlog0 : (0:ℝ) ≤ Real.log (2*(q:ℝ)+2) := le_of_lt (lt_of_lt_of_le zero_lt_one hlog1)
    have hA : ∀ N : ℕ, 1 ≤ N → ‖Asum χ (N:ℝ) - (N:ℂ) * LFunction χ 1‖
        ≤ (1 + 2*B₁ + 2*B₂) * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ) := by
      intro N hN
      exact asum_sub_LFunction_bound χ hq2 hB₁ hB₂ (hPV q χ hχ hq2) (hLS q χ hχ hq2) hN
    have hL : ‖LFunction χ 1‖ ≤ (1 + 2*B₂) * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := by
      have h1 := hLS q χ hχ hq2 1 le_rfl
      have hsum1 : (∑ n ∈ (Finset.Icc 1 1 : Finset ℕ), (χ (n : ZMod q) : ℂ) / (n:ℂ)) = 1 := by
        rw [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, map_one χ]
        simp
      rw [hsum1, Nat.cast_one, div_one] at h1
      have hL1 : ‖LFunction χ 1‖ ≤ 1 + B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := by
        have hsplit : LFunction χ 1 = 1 - (1 - LFunction χ 1) := by ring
        rw [hsplit]
        calc ‖(1:ℂ) - (1 - LFunction χ 1)‖ ≤ ‖(1:ℂ)‖ + ‖1 - LFunction χ 1‖ := norm_sub_le _ _
          _ ≤ 1 + B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := by
              rw [norm_one]
              linarith [h1]
      refine hL1.trans ?_
      have hprod : (1:ℝ) ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := by nlinarith
      have hX : (0:ℝ) ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := mul_nonneg hsq0 hlog0
      nlinarith [hprod, hX, hB₂]
    have hfin := efunRealReduce χ (K := 1 + 2*B₁ + 2*B₂) (K' := 1 + 2*B₂)
      (by positivity) (by positivity) hA hL x hx
    refine hfin.trans ?_
    have hnn : (0:ℝ) ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt x :=
      mul_nonneg (mul_nonneg hsq0 hlog0) (Real.sqrt_nonneg x)
    have hkey : (1 + 2*B₁ + 2*B₂) + (1 + 2*B₂) ≤ (1 + 2*B₁ + 2*B₂) + (1 + 2*B₂) + 1 := by
      linarith
    have hgoal1 : ((1 + 2*B₁ + 2*B₂) + (1 + 2*B₂)) * Real.sqrt (q:ℝ)
          * Real.log (2*(q:ℝ)+2) * Real.sqrt x
        = ((1 + 2*B₁ + 2*B₂) + (1 + 2*B₂))
          * (Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt x) := by ring
    have hgoal2 : ((1 + 2*B₁ + 2*B₂) + (1 + 2*B₂) + 1) * Real.sqrt (q:ℝ)
          * Real.log (2*(q:ℝ)+2) * Real.sqrt x
        = ((1 + 2*B₁ + 2*B₂) + (1 + 2*B₂) + 1)
          * (Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt x) := by ring
    rw [hgoal1, hgoal2]
    exact mul_le_mul_of_nonneg_right hkey hnn

end Work.LinnikAreas
