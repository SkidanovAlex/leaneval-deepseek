import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea5.S16Hecke.gammaLowerSharpVertical

namespace Work.FIArea6Hecke.R

/-- Lower bound for the 20-th power of the gamma ratio `‖Γ(2 - s/2)‖ / ‖Γ(1 + s/2)‖` on the
strip `1/2 ≤ σ ≤ 1` (`s = σ + iτ`): it dominates `c·(2+|τ|)^{20(1-σ)}`.
This mirrors the sharp Stirling growth `‖Γ(u+iT)‖ ≍ (1+|T|)^{u-1/2} e^{-π|T|/2}`: pairing a
**lower** bound for `Γ(2-σ/2 - iτ/2)` (real part in `[3/2,7/4]`) with an **upper** bound for
`Γ(1+σ/2 + iτ/2)` (real part in `[5/4,3/2]`) makes the exponential factors cancel and leaves
`(1+|τ|/2)^{1-σ} ≥ (1/2)(2+|τ|)^{1-σ}`. -/
theorem gammaRatioStripLower :
    ∃ c : ℝ, 0 < c ∧ ∀ (σ τ : ℝ), 1 / 2 ≤ σ → σ ≤ 1 →
      c * (2 + |τ|) ^ (20 * (1 - σ)) ≤
        (‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ /
         ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖) ^ (20 : ℕ) := by
  obtain ⟨cl, hclpos, hcl⟩ := Work.FIArea5.S16Hecke.gammaLowerSharpVertical
  obtain ⟨Cu, hCupos, hCu⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨(cl / (2 * Cu)) ^ (20 : ℕ), by positivity, ?_⟩
  intro σ τ hσ1 hσ2
  set hb : ℝ := 1 + |τ| / 2 with hbdef
  have hbpos : 0 < hb := by rw [hbdef]; positivity
  set E : ℝ := Real.exp (-(Real.pi / 2) * (|τ| / 2)) with hEdef
  have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have e1 : (2 : ℂ) - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2
      = ((2 - σ / 2 : ℝ) : ℂ) + ((-(τ / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : (1 : ℂ) + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2
      = ((1 + σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hN : cl * hb ^ (3 / 2 - σ / 2) * E ≤
      ‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := by
    have h := hcl (2 - σ / 2) (-(τ / 2)) (by linarith) (by linarith)
    have habs : |(-(τ / 2) : ℝ)| = |τ| / 2 := by
      rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp : (2 - σ / 2) - 1 / 2 = 3 / 2 - σ / 2 := by ring
    rw [habs, hexp] at h
    rw [e1, hbdef, hEdef]
    exact h
  have hD : ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ ≤
      Cu * hb ^ (1 / 2 + σ / 2) * E := by
    have h := hCu (1 + σ / 2) (τ / 2) (by linarith) (by linarith)
    have habs : |(τ / 2 : ℝ)| = |τ| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp : (1 + σ / 2) - 1 / 2 = 1 / 2 + σ / 2 := by ring
    rw [habs, hexp] at h
    rw [e2, hbdef, hEdef]
    exact h
  have hDpos : 0 < ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := by
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero_of_re_pos
    have hre : (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2).re = 1 + σ / 2 := by simp
    rw [hre]; linarith
  have hkey : (cl / Cu) * hb ^ (1 - σ) *
        ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ ≤
      ‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := by
    have hBeq : (cl / Cu) * hb ^ (1 - σ) * (Cu * hb ^ (1 / 2 + σ / 2) * E)
        = cl * hb ^ (3 / 2 - σ / 2) * E := by
      have hcomb : hb ^ (1 - σ) * hb ^ (1 / 2 + σ / 2) = hb ^ (3 / 2 - σ / 2) := by
        rw [← Real.rpow_add hbpos]
        congr 1; ring
      rw [← hcomb]
      field_simp
    calc (cl / Cu) * hb ^ (1 - σ) *
            ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖
        ≤ (cl / Cu) * hb ^ (1 - σ) * (Cu * hb ^ (1 / 2 + σ / 2) * E) := by
          exact mul_le_mul_of_nonneg_left hD (by positivity)
      _ = cl * hb ^ (3 / 2 - σ / 2) * E := hBeq
      _ ≤ ‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := hN
  have hratio : (cl / Cu) * hb ^ (1 - σ) ≤
      ‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ /
      ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := by
    rw [le_div_iff₀ hDpos]
    exact hkey
  have hpoly : (2 + |τ|) ^ (1 - σ) ≤ 2 * hb ^ (1 - σ) := by
    have h2eq : (2 + |τ|) = 2 * hb := by rw [hbdef]; ring
    rw [h2eq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbpos.le]
    have h2 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hbpos.le _)
  have hbase_ge : (cl / (2 * Cu)) * (2 + |τ|) ^ (1 - σ) ≤ (cl / Cu) * hb ^ (1 - σ) := by
    have h := mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ cl / (2 * Cu))
    have heq : (cl / (2 * Cu)) * (2 * hb ^ (1 - σ)) = (cl / Cu) * hb ^ (1 - σ) := by
      field_simp
    linarith [h, heq]
  have hKD : (cl / (2 * Cu)) * (2 + |τ|) ^ (1 - σ) ≤
      ‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ /
      ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ := hbase_ge.trans hratio
  have hpow := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ (cl / (2 * Cu)) * (2 + |τ|) ^ (1 - σ)) hKD 20
  have hLHS : ((cl / (2 * Cu)) * (2 + |τ|) ^ (1 - σ)) ^ (20 : ℕ)
      = (cl / (2 * Cu)) ^ 20 * (2 + |τ|) ^ (20 * (1 - σ)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 + |τ|)]
    ring_nf
  calc (cl / (2 * Cu)) ^ 20 * (2 + |τ|) ^ (20 * (1 - σ))
      = ((cl / (2 * Cu)) * (2 + |τ|) ^ (1 - σ)) ^ (20 : ℕ) := hLHS.symm
    _ ≤ (‖Complex.Gamma (2 - ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖ /
        ‖Complex.Gamma (1 + ((σ : ℂ) + (τ : ℂ) * Complex.I) / 2)‖) ^ (20 : ℕ) := hpow

end Work.FIArea6Hecke.R
