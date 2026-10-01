import Mathlib
import Submission.Work.LinnikAreas.log_unbounded_nat

namespace Work.LinnikAreas

/-- For `x ≥ 0`, `log x ≤ 2 * sqrt x`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1/2)
  rw [Real.sqrt_eq_rpow]
  have : x ^ (1/2 : ℝ) / (1/2 : ℝ) = 2 * x ^ (1/2 : ℝ) := by ring
  linarith [h, this]

/-- Elementary numerical fact: for every `ε > 0` and every absolute constant `A`, all
sufficiently large `q` satisfy
`log q + (1/2)·log(2 + 10·log q) + (1/2)·log(2 + 5·log q) + A ≤ (1 + ε/4)·log q`
(since `log log q = o(log q)`). -/
theorem logSum_threshold (A : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      Real.log (q : ℝ) + (1 / 2) * Real.log (2 + 10 * Real.log (q : ℝ)) +
        (1 / 2) * Real.log (2 + 5 * Real.log (q : ℝ)) + A
        ≤ (1 + ε / 4) * Real.log (q : ℝ) := by
  set B : ℝ := max A 0 with hBdef
  have hBge : A ≤ B := le_max_left A 0
  set M : ℝ := max 11 (max (1024 / ε^2) (8 * B / ε)) with hMdef
  obtain ⟨q₀, hq₀⟩ := log_unbounded_nat M
  refine ⟨q₀, fun q hq => ?_⟩
  have hxM : M ≤ Real.log (q : ℝ) := hq₀ q hq
  set x : ℝ := Real.log (q : ℝ) with hxdef
  have hx11 : (11:ℝ) ≤ x := by
    have : (11:ℝ) ≤ M := by rw [hMdef]; exact le_max_left _ _
    linarith
  have hx1024 : 1024 / ε^2 ≤ x := by
    have : 1024 / ε^2 ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hx8B : 8 * B / ε ≤ x := by
    have : 8 * B / ε ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hxpos : 0 < x := by linarith
  have hxnn : 0 ≤ x := le_of_lt hxpos
  have hε2pos : 0 < ε^2 := pow_pos hε 2
  have hε2ne : ε^2 ≠ 0 := ne_of_gt hε2pos
  have hεne : ε ≠ 0 := ne_of_gt hε
  have h1024 : (1024:ℝ) ≤ ε^2 * x := by
    have h := mul_le_mul_of_nonneg_left hx1024 (le_of_lt hε2pos)
    have hc : ε^2 * (1024/ε^2) = 1024 := by
      rw [mul_comm (ε^2) (1024/ε^2), div_mul_cancel₀ 1024 hε2ne]
    rwa [hc] at h
  have h8B : 8 * B ≤ ε * x := by
    have h := mul_le_mul_of_nonneg_left hx8B (le_of_lt hε)
    have hc : ε * (8*B/ε) = 8*B := by
      rw [mul_comm ε (8*B/ε), div_mul_cancel₀ (8*B) hεne]
    rwa [hc] at h
  have hBle : B ≤ (ε/8) * x := by linarith
  have hA_bound : A ≤ (ε/8) * x := le_trans hBge hBle
  have hsqrt : 4 * Real.sqrt x ≤ (ε/8) * x := by
    have hmul : 1024 * x ≤ (ε^2 * x) * x := mul_le_mul_of_nonneg_right h1024 hxnn
    have hx2sq : x ≤ ((ε/32) * x)^2 := by nlinarith [hmul]
    have hy : 0 ≤ (ε/32) * x :=
      mul_nonneg (le_of_lt (div_pos hε (by norm_num))) hxnn
    have hle : Real.sqrt x ≤ (ε/32) * x := (Real.sqrt_le_left hy).mpr hx2sq
    nlinarith [hle]
  have hlog1 : Real.log (2 + 10 * x) ≤ (ε/8) * x := by
    have hx2 : 2 + 10 * x ≤ x^2 := by nlinarith [hx11]
    have hpos : 0 < 2 + 10 * x := by linarith
    have h1 : Real.log (2 + 10 * x) ≤ Real.log (x^2) := Real.log_le_log hpos hx2
    rw [Real.log_pow] at h1
    have h2 : Real.log x ≤ 2 * Real.sqrt x := log_le_two_sqrt hxnn
    have h1' : Real.log (2 + 10 * x) ≤ 2 * Real.log x := by simpa using h1
    have h2' : 2 * Real.log x ≤ 4 * Real.sqrt x := by linarith [h2]
    exact le_trans h1' (le_trans h2' hsqrt)
  have hlog2 : Real.log (2 + 5 * x) ≤ (ε/8) * x := by
    have hx2 : 2 + 5 * x ≤ x^2 := by nlinarith [hx11]
    have hpos : 0 < 2 + 5 * x := by linarith
    have h1 : Real.log (2 + 5 * x) ≤ Real.log (x^2) := Real.log_le_log hpos hx2
    rw [Real.log_pow] at h1
    have h2 : Real.log x ≤ 2 * Real.sqrt x := log_le_two_sqrt hxnn
    have h1' : Real.log (2 + 5 * x) ≤ 2 * Real.log x := by simpa using h1
    have h2' : 2 * Real.log x ≤ 4 * Real.sqrt x := by linarith [h2]
    exact le_trans h1' (le_trans h2' hsqrt)
  linarith [hlog1, hlog2, hA_bound]

end Work.LinnikAreas
