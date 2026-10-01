import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.Defs

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-! ## `Ψ(1) = Θ` at the parameter `U = 1`

At `U = 1` the mollifier `ψ_d` of HB (11.6) coincides with `θ_d` of HB (11.7) with `W = V`,
because `log(V/1) = log V` and because the first branch `d ≤ 1` of `ψ_d` (where `ψ_d = μ_d`)
reproduces `μ_d · log(V/d)/log V` at `d = 1` (and `μ_0 = 0`).  Consequently the divisor sums
`Ψ(n) = Σ_{d|n} ψ_d` and `Θ(n) = Σ_{d|n} θ_d` agree for `U = V = W > 1`. -/

/-- At `d ≥ 2` the two mollifiers `ψ_d` (with `U = 1`, `V = W`) and `θ_d` (with cut-off `W`)
are *definitionally* the same expression. -/
private lemma psiM_one_eq_thetaM_of_two_le {W : ℝ} {d : ℕ} (hd : 2 ≤ d) :
    psiM 1 W d = thetaM W d := by
  have hd1 : ¬ ((d:ℝ) ≤ 1) := by
    have h2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  simp only [psiM, thetaM, if_neg hd1, div_one]

/-- At `d = 1` the first branch of `ψ_1` gives `μ_1 = 1`, while `θ_1 = μ_1 log(W/1)/log W = 1`
since `W > 1` forces `log W ≠ 0`. -/
private lemma psiM_one_eq_thetaM_one {W : ℝ} (hW : 1 < W) : psiM 1 W 1 = thetaM W 1 := by
  have hlog : Real.log W ≠ 0 := ne_of_gt (Real.log_pos hW)
  simp only [psiM, thetaM, Nat.cast_one, div_one]
  rw [if_pos le_rfl, if_pos hW.le]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
  exact (div_self hlog).symm

/-- Pointwise identity of the two mollifiers for every `d ≥ 1`. -/
private lemma psiM_one_eq_thetaM {W : ℝ} (hW : 1 < W) {d : ℕ} (hd : 1 ≤ d) :
    psiM 1 W d = thetaM W d := by
  rcases eq_or_lt_of_le hd with h | h
  · subst h
    exact psiM_one_eq_thetaM_one hW
  · exact psiM_one_eq_thetaM_of_two_le (by omega)

theorem psiS_one_eq_thetaS {W : ℝ} (hW : 1 < W) (n : ℕ) :
    Work.LinnikAreas.Density4.psiS 1 W n = Work.LinnikAreas.Density4.thetaS W n := by
  unfold psiS thetaS
  refine Finset.sum_congr rfl (fun d hd => ?_)
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
  have hd1 : 1 ≤ d := by
    have := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
    omega
  exact psiM_one_eq_thetaM hW hd1

end Work.LinnikAreas2
