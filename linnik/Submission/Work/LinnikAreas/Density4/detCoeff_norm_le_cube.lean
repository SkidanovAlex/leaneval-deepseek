import Mathlib
import Submission.Work.LinnikAreas.Density4.det_split

namespace Work.LinnikAreas.Density4

/-- **Uniform polynomial bound for the detector coefficient.** With `|Re ρ| ≤ 1` the detector
coefficient `a_n = Ψ(n)Θ(n)χ(n)n^{-ρ}` of HB (11.8) satisfies `‖a_n‖ ≤ n³`: `|Ψ(n)|,|Θ(n)| ≤ n`
(`abs_psiS_le`, `abs_thetaS_le` in `Submission/Work/LinnikAreas/Density4/det_split.lean`),
`‖χ(n)‖ ≤ 1`, and `‖n^{-ρ}‖ = n^{-Re ρ} ≤ n`. -/
lemma detCoeff_norm_le_cube {q : ℕ} [NeZero q] {U V W : ℝ} (hU : 0 < U)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hre : |ρ.re| ≤ 1) (n : ℕ) :
    ‖detCoeff q U V W χ ρ n‖ ≤ (n : ℝ)^3 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : detCoeff q U V W χ ρ 0 = 0 := by simp [detCoeff, psiS_zero]
    rw [h0, norm_zero]
    simp
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hpsi : ‖((psiS U V n : ℝ) : ℂ)‖ ≤ (n:ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_psiS_le hU n
    have htheta : ‖((thetaS W n : ℝ) : ℂ)‖ ≤ (n:ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_thetaS_le W n
    have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hcp : ‖((n:ℂ)^(-ρ))‖ ≤ (n:ℝ) ^ (|ρ.re|) := by
      rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_abs ρ.re)
    have hpow : (n:ℝ) ^ (|ρ.re|) ≤ (n:ℝ) := by
      calc (n:ℝ) ^ (|ρ.re|) ≤ (n:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 hre
        _ = (n:ℝ) := Real.rpow_one _
    calc ‖detCoeff q U V W χ ρ n‖
        = ‖((psiS U V n : ℝ) : ℂ) * ((thetaS W n : ℝ) : ℂ) * χ (n : ZMod q)
            * ((n:ℂ)^(-ρ))‖ := rfl
      _ = ‖((psiS U V n : ℝ) : ℂ)‖ * ‖((thetaS W n : ℝ) : ℂ)‖ * ‖χ (n : ZMod q)‖
            * ‖((n:ℂ)^(-ρ))‖ := by simp only [norm_mul]
      _ ≤ (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) ^ (|ρ.re|) := by gcongr
      _ ≤ (n:ℝ)^3 := by
            have h3 : (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) = (n:ℝ)^3 := by ring
            calc (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) ^ (|ρ.re|)
                ≤ (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) :=
                  mul_le_mul_of_nonneg_left hpow (by positivity)
              _ = (n:ℝ)^3 := h3

end Work.LinnikAreas.Density4
