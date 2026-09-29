import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

/-- **A constant of the barrier comparison.**  With
`c = cc R ρ = log (R/(R-ρ))` (the boundary normalisation of the logarithmic potential),
`C = CC R ρ τ = log R + (1/(1-τ)) (log(1/ρ) + 1)` (the interior normalisation), and
`M ≥ 0`, `ε > 0`, the hypotheses of the Cartan-barrier comparison force
`barrier Φ M ε c C x ≤ -ε/2` at every point `x` where the potential `Φ` dominates the
geometric mean `log (R/(ρ+r))` of the potential of a set of measure `≥ 2ρ(1-τ)` filling
`[x₀-ρ, x₀+ρ]`.

The content is the elementary arithmetic of the two normalisations: the required lower bound
on `log (1/ρ)` is exactly the constant appearing in the hypothesis `hlog`. -/
theorem rcBarrier_const {R ρ r M ε τ : ℝ} {Φ : ℂ → ℝ} {x : ℂ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R / 4) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r) (hrρ : r ≤ ρ / 2)
    (hM : 0 ≤ M) (hε : 0 < ε) (hτ : 0 < τ) (hτδ : τ ≤ (ε / 2) / (M + ε) / 16)
    (hlog : Real.log (1 / ρ) ≥ max ((8 * (M + ε) / (7 * (ε / 2))) *
        (1 + (ε / 2) / (M + ε) / 8 + Real.log 2 + (ε / 2) / (M + ε) / 2
          - ((ε / 2) / (M + ε)) * Real.log R)) (Real.log (1 / (R - ρ))))
    (hΦ : Real.log (R / (ρ + r)) ≤ Φ x) :
    Work.TMComp.RC.barrier Φ M ε (Work.TMComp.RC.cc R ρ) (Work.TMComp.RC.CC R ρ τ) x ≤ -(ε / 2) := by
  -- Basic positivity and geometric comparisons coming from `ρ ≤ R/4`, `ρ ≤ 1`, `r ≤ ρ/2`.
  have hMs : 0 < M + ε := by linarith
  have hRmρ : 0 < R - ρ := by linarith
  have hpr : 0 < ρ + r := by linarith
  have hRne : R ≠ 0 := ne_of_gt hR
  -- `a = (ε/2)/(M+ε)`; then `1 - a = (M + ε/2)/(M + ε)` and `a < 1`.
  set a : ℝ := (ε / 2) / (M + ε) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_lt1 : a < 1 := by rw [ha_def, div_lt_one hMs]; linarith
  have ha_le1 : a ≤ 1 := le_of_lt ha_lt1
  have hτlt1 : τ < 1 := by linarith [hτδ, ha_lt1]
  have h1mτ : 0 < 1 - τ := by linarith
  -- `ℓ = log (1/ρ)`.
  set ℓ : ℝ := Real.log (1 / ρ) with hl_def
  have hℓ_nonneg : 0 ≤ ℓ := by
    rw [hl_def]; apply Real.log_nonneg; rw [one_le_div₀ hρ]; exact hρ1
  -- Unfold the two halves of the hypothesis `hlog`, and rewrite the first one.
  have hlogA : ℓ ≥ (8 * (M + ε) / (7 * (ε / 2))) *
        (1 + a / 8 + Real.log 2 + a / 2 - a * Real.log R) := (max_le_iff.mp hlog).1
  have hlogB : ℓ ≥ Real.log (1 / (R - ρ)) := (max_le_iff.mp hlog).2
  have hA_eq : (7*a/8) * (8 * (M + ε) / (7 * (ε / 2)) * (1 + a/8 + Real.log 2 + a/2 - a*Real.log R))
      = 1 + Real.log 2 + 5*a/8 - a*Real.log R := by
    rw [ha_def]; field_simp; ring
  -- The hypothesis, multiplied by `7a/8 ≥ 0`.
  have key1 : 1 + Real.log 2 + 5*a/8 ≤ (7*a/8) * ℓ + a * Real.log R := by
    have h7 : (0:ℝ) ≤ 7*a/8 := by linarith
    have h := mul_le_mul_of_nonneg_left hlogA h7
    rw [hA_eq] at h; linarith
  have L43rel : Real.log (4/3) = Real.log 2 + Real.log (2/3) := by
    rw [show (4:ℝ)/3 = 2*(2/3) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have L43nn : 0 ≤ Real.log (4/3) := Real.log_nonneg (by norm_num)
  -- The core arithmetic step: `a log(R-ρ) - log(ρ+r) ≥ (1 - 7a/8)(ℓ+1)`.
  have key2 : (1 - 7*a/8) * (ℓ + 1) ≤ a * (Real.log R - Real.log (4/3)) + ℓ + Real.log (2/3) := by
    nlinarith [key1, L43rel, L43nn, ha_le1, ha_pos]
  have hRmρ_log : Real.log R - Real.log (4/3) ≤ Real.log (R - ρ) := by
    have e1 : Real.log (3*R/4) = Real.log R - Real.log (4/3) := by
      have h34 : Real.log ((3:ℝ)/4) = -Real.log (4/3) := by
        rw [show (4:ℝ)/3 = ((3:ℝ)/4)⁻¹ by norm_num, Real.log_inv]; ring
      rw [show (3:ℝ)*R/4 = R * (3/4) by ring,
          Real.log_mul hRne (by norm_num : (3:ℝ)/4 ≠ 0), h34]; ring
    rw [← e1]
    apply Real.log_le_log (by linarith) (by linarith)
  have hpr_log : ℓ + Real.log (2/3) ≤ -(Real.log (ρ + r)) := by
    have hle : Real.log (ρ + r) ≤ Real.log (3*ρ/2) := Real.log_le_log hpr (by linarith)
    have e2 : Real.log (3*ρ/2) = Real.log ρ + Real.log (3/2) := by
      rw [show (3:ℝ)*ρ/2 = ρ * (3/2) by ring, Real.log_mul (ne_of_gt hρ) (by norm_num : (3:ℝ)/2 ≠ 0)]
    have e3 : Real.log (2/3) = -Real.log (3/2) := by
      rw [show (2:ℝ)/3 = ((3:ℝ)/2)⁻¹ by norm_num, Real.log_inv]
    have e4 : ℓ = -Real.log ρ := by rw [hl_def, one_div, Real.log_inv]
    linarith
  have keyLHS : (1 - 7*a/8) * (ℓ + 1) ≤ a * Real.log (R - ρ) - Real.log (ρ + r) := by
    have h1 : a * (Real.log R - Real.log (4/3)) ≤ a * Real.log (R - ρ) :=
      mul_le_mul_of_nonneg_left hRmρ_log (le_of_lt ha_pos)
    linarith [h1, key2, hpr_log]
  -- `(1-a)/(1-τ) ≤ 1 - 7a/8`, using `τ ≤ a/16` and `a < 1`.
  have hq_le : (1 - a)/(1 - τ) ≤ 1 - 7*a/8 := by
    have hle1 : 1 - 7*a/8 ≤ 1 := by linarith
    have hτ1 : τ * (1 - 7*a/8) ≤ a/8 := by
      have hA : τ * (1 - 7*a/8) ≤ τ * 1 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hτ)
      have hB : τ ≤ a/8 := by linarith [hτδ]
      linarith
    rw [div_le_iff₀ h1mτ]
    nlinarith [hτ1]
  have hmain : a * Real.log (R - ρ) - Real.log (ρ + r) ≥ (1 - a)/(1 - τ) * (ℓ + 1) := by
    have hpos : (0:ℝ) ≤ ℓ + 1 := by linarith
    have := mul_le_mul_of_nonneg_right hq_le hpos
    linarith [this, keyLHS]
  -- Identify `CC - cc` and `log(R/(ρ+r)) - cc`.
  have hCCcc : Work.TMComp.RC.CC R ρ τ - Work.TMComp.RC.cc R ρ
      = (1/(1-τ))*(ℓ+1) + Real.log (R - ρ) := by
    rw [Work.TMComp.RC.CC, Work.TMComp.RC.cc, ← hl_def, Real.log_div hRne (ne_of_gt hRmρ)]
    ring
  have hlogRatio : Real.log (R / (ρ + r)) - Work.TMComp.RC.cc R ρ = Real.log (R - ρ) - Real.log (ρ + r) := by
    rw [Work.TMComp.RC.cc, Real.log_div hRne (ne_of_gt hpr), Real.log_div hRne (ne_of_gt hRmρ)]
    ring
  -- `Φ x - cc ≥ (1-a)(CC - cc)`, transported from the hypothesis on `Φ x`.
  have hΦc : Φ x - Work.TMComp.RC.cc R ρ ≥ ((M + ε/2)/(M + ε)) * (Work.TMComp.RC.CC R ρ τ - Work.TMComp.RC.cc R ρ) := by
    have hq : (M + ε/2)/(M + ε) = 1 - a := by rw [ha_def]; field_simp; ring
    rw [hq, hCCcc]
    have h1 : Real.log (R - ρ) - Real.log (ρ + r) ≤ Φ x - Work.TMComp.RC.cc R ρ := by
      rw [← hlogRatio]; linarith [hΦ]
    have h2 : (1 - a) * ((1/(1-τ))*(ℓ+1) + Real.log (R-ρ)) ≤ Real.log (R-ρ) - Real.log (ρ + r) := by
      have heq : (1 - a) * ((1/(1-τ))*(ℓ+1) + Real.log (R-ρ)) = (1-a)/(1-τ)*(ℓ+1) + (1-a)*Real.log (R-ρ) := by ring
      rw [heq]; linarith [hmain]
    linarith
  have hDpos : 0 < Work.TMComp.RC.CC R ρ τ - Work.TMComp.RC.cc R ρ := by
    rw [hCCcc]
    have hℓR : 0 ≤ ℓ + Real.log (R - ρ) := by
      have hb := hlogB
      have e : Real.log (1/(R-ρ)) = -Real.log (R-ρ) := by rw [one_div, Real.log_inv]
      rw [e] at hb; linarith
    have h1 : (1:ℝ) ≤ 1/(1-τ) := by rw [one_le_div₀ h1mτ]; linarith
    have h2 : ℓ + 1 ≤ (1/(1-τ))*(ℓ+1) := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ ℓ + 1)
      simpa using this
    linarith
  -- Divide, then read off the barrier.
  have hqle : (M + ε/2)/(M + ε) ≤ (Φ x - Work.TMComp.RC.cc R ρ) / (Work.TMComp.RC.CC R ρ τ - Work.TMComp.RC.cc R ρ) :=
    (le_div_iff₀ hDpos).mpr hΦc
  rw [Work.TMComp.RC.barrier]
  have hbignum : M + ε/2 ≤ (M + ε) * ((Φ x - Work.TMComp.RC.cc R ρ) / (Work.TMComp.RC.CC R ρ τ - Work.TMComp.RC.cc R ρ)) := by
    have h1 := mul_le_mul_of_nonneg_left hqle (le_of_lt hMs)
    have h2 : (M + ε) * ((M + ε/2)/(M + ε)) = M + ε/2 := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hMs)]
    linarith [h1, h2]
  linarith [hbignum]

end Work.TMComp.RealCartan
