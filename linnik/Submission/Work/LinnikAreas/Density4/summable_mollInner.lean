import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

namespace Work.LinnikAreas.Density4

/-- **Summability of the mollified inner sum.**

For `Re w > 1` the summand `(if d ∣ n then Ψ_d else 0) (if e ∣ n then Θ_e else 0) χ(n) n^{-w}`
is dominated by the constant `‖Ψ_d‖ ‖Θ_e‖` times `n^{-Re w}`, which is summable because
`Re w > 1`.  (This is the summability half of HB §11 (11.8).) -/
theorem summable_mollInner (q : ℕ) [NeZero q] {U V W : ℝ} (χ : DirichletCharacter ℂ q) {w : ℂ}
    (hw : 1 < w.re) (d e : ℕ) :
    Summable (fun n : ℕ => (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
        * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  set C : ℝ := ‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖ with hC
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * (n : ℝ) ^ (-w.re)) ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  · intro n
    have h1 : ‖(if d ∣ n then (psiM U V d : ℂ) else 0)‖ ≤ ‖(psiM U V d : ℂ)‖ := by split_ifs <;> simp
    have h2 : ‖(if e ∣ n then (thetaM W e : ℂ) else 0)‖ ≤ ‖(thetaM W e : ℂ)‖ := by split_ifs <;> simp
    have h3 : ‖(χ (n : ZMod q) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hP : (0:ℝ) ≤ (n : ℝ) ^ (-w.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ‖(n : ℂ) ^ (-w)‖ ≤ (n : ℝ) ^ (-w.re) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hw0)]
        simp only [norm_zero]
        positivity
      · rw [Complex.norm_natCast_cpow_of_pos hn (-w), Complex.neg_re]
    have hAB : ‖(if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
        * (χ (n : ZMod q) : ℂ)‖
        ≤ ‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖ := by
      rw [norm_mul, norm_mul]
      calc ‖(if d ∣ n then (psiM U V d : ℂ) else 0)‖ * ‖(if e ∣ n then (thetaM W e : ℂ) else 0)‖
              * ‖(χ (n : ZMod q) : ℂ)‖
          ≤ (‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖) * 1 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)) h3 (norm_nonneg _)
              (by positivity)
        _ = ‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖ := by ring
    calc ‖(if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
            * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)‖
        = ‖(if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
            * (χ (n : ZMod q) : ℂ)‖ * ‖(n : ℂ) ^ (-w)‖ := by rw [norm_mul]
      _ ≤ (‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖) * (n : ℝ) ^ (-w.re) :=
          mul_le_mul hAB h4 (norm_nonneg _) (by positivity)
      _ = C * (n : ℝ) ^ (-w.re) := by rw [hC]

end Work.LinnikAreas.Density4
