import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open DirichletCharacter

theorem efunRealReduce {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K K' : ℝ}
    (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hA : ∀ N : ℕ, 1 ≤ N → ‖Work.LinnikAreas.Asum χ (N : ℝ) - (N : ℂ) * DirichletCharacter.LFunction χ 1‖
        ≤ K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt (N : ℝ))
    (hL : ‖DirichletCharacter.LFunction χ 1‖ ≤ K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) :
    ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖
        ≤ (K + K') * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x := by
  intro x hx
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast hqpos
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact (Nat.one_le_floor_iff x).mpr hx
  have hNx : (N : ℝ) ≤ x := by
    rw [hN]; exact Nat.floor_le (by linarith)
  have hxN1 : x - (N : ℝ) ≤ 1 := by
    have hlt := Nat.lt_floor_add_one x
    rw [← hN] at hlt
    linarith
  have hxNnn : 0 ≤ x - (N : ℝ) := by linarith
  have hCnn : 0 ≤ Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
    refine mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg ?_)
    linarith
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hKC : 0 ≤ K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
    mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hlogq
  have hK'C : 0 ≤ K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
    mul_nonneg (mul_nonneg hK' (Real.sqrt_nonneg _)) hlogq
  have hAsum : Asum χ x = Asum χ (N : ℝ) := by
    rw [Asum_apply, Asum_apply, hN, Nat.floor_natCast]
  have hsqrtx1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hxN_sqrt : x - (N : ℝ) ≤ Real.sqrt x := le_trans hxN1 hsqrtx1
  have hEfunN : Efun χ (N : ℝ) = Asum χ (N : ℝ) - (N : ℂ) * LFunction χ 1 := by
    rw [Efun_apply]
    push_cast
    ring
  have hdecomp : Efun χ x = Efun χ (N : ℝ) - ((x - (N : ℝ) : ℝ) : ℂ) * LFunction χ 1 := by
    rw [Efun_apply, hAsum, hEfunN]
    push_cast
    ring
  have hstep1 : ‖Efun χ x‖ ≤ ‖Asum χ (N : ℝ) - (N : ℂ) * LFunction χ 1‖
      + (x - (N : ℝ)) * ‖LFunction χ 1‖ := by
    rw [hdecomp, hEfunN]
    refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
    rw [Complex.norm_mul]
    have h1 : ‖((x - (N : ℝ) : ℝ) : ℂ)‖ = x - (N : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxNnn]
    rw [h1]
  calc ‖Efun χ x‖
      ≤ ‖Asum χ (N : ℝ) - (N : ℂ) * LFunction χ 1‖ + (x - (N : ℝ)) * ‖LFunction χ 1‖ :=
        hstep1
    _ ≤ K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt (N : ℝ)
          + (x - (N : ℝ)) * (K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) := by
        have h1 := hA N hN1
        have h2 := mul_le_mul_of_nonneg_left hL hxNnn
        linarith
    _ ≤ K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x
          + Real.sqrt x * (K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) := by
        have hs : Real.sqrt (N : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
        have h1 : K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt (N : ℝ)
            ≤ K * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hs hKC
        have h2 : (x - (N : ℝ)) * (K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2))
            ≤ Real.sqrt x * (K' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right hxN_sqrt hK'C
        linarith
    _ = (K + K') * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x := by
        ring

end Work.LinnikAreas
