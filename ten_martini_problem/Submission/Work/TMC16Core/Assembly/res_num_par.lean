import Mathlib
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Assembly.res_par_bg
import Submission.Work.TMC16Core.Assembly.res_par_lin
import Submission.Work.TMC16Core.Assembly.res_par_exp

namespace Work.TMC16Core.Assembly

/-- The four purely numerical `εf`-facts of `res_num_par`: with
`0 < εf ≤ min (L/1000) ((9L/64 - b₀/4)/8)` (and `0 < b₀`, `16b₀/9 < L`) the two
thresholds `u = 9L/64 + b₀/4` and `A = 9L/32 - 2εf` satisfy `0 < A`,
`u < A`, `εf < A` and `2 (A - u) ≥ 9L/64 - b₀/4`. -/
lemma res_par_eps {L b₀ εf : ℝ} (hb₀ : 0 < b₀) (hLb : 16 * b₀ / 9 < L)
    (hεf0 : 0 < εf) (hεf : εf ≤ min (L / 1000) ((9 * L / 64 - b₀ / 4) / 8)) :
    0 < 9 * L / 32 - 2 * εf ∧
    9 * L / 64 + b₀ / 4 < 9 * L / 32 - 2 * εf ∧
    εf < 9 * L / 32 - 2 * εf ∧
    2 * ((9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4)) ≥ 9 * L / 64 - b₀ / 4 := by
  have hL : 0 < L := by linarith
  have hε1 : εf ≤ L / 1000 := le_trans hεf (min_le_left _ _)
  have hε2 : εf ≤ (9 * L / 64 - b₀ / 4) / 8 := le_trans hεf (min_le_right _ _)
  have hd0 : 0 < 9 * L / 64 - b₀ / 4 := by linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem res_num_par {L b₀ : ℝ} (hb₀ : 0 < b₀) (hLb : 16 * b₀ / 9 < L) :
    ∃ N : ℕ, ∀ (q : ℕ → ℕ) (n : ℕ), N ≤ n → StrictMono q → 0 < q n →
    ∀ εf : ℝ, 0 < εf → εf ≤ min (L / 1000) ((9 * L / 64 - b₀ / 4) / 8) →
      0 < 9 * L / 32 - 2 * εf ∧
      9 * L / 64 + b₀ / 4 < 9 * L / 32 - 2 * εf ∧
      εf < 9 * L / 32 - 2 * εf ∧
      2 * ((9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4)) ≥ 9 * L / 64 - b₀ / 4 ∧
      0 ≤ Work.TMC16Core.Assembly.bG q n ∧
      Work.TMC16Core.Assembly.bG q n ≤ (q n : ℝ) / 20 + 3 ∧
      Work.TMC16Core.Assembly.bG q n ≤ (((5 * q n / 8 : ℕ) : ℝ)) - 1 ∧
      (((2 * q n - 1 : ℕ) : ℝ)) ≤ 40 * ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - Work.TMC16Core.Assembly.bG q n) ∧
      ((L + εf) * ((((2 * q n - 1 : ℕ) : ℝ)) - 1 - ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - Work.TMC16Core.Assembly.bG q n))
        - ((((2 * q n - 1 : ℕ) : ℝ)) + 1) * (23 * L / 32 + 2 * εf)
        + (L / 100) * ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - Work.TMC16Core.Assembly.bG q n) < 0) ∧
      4 * ((((2 * q n - 1 : ℕ) : ℝ)) + 1) * Real.exp (23 * L / 32 + 2 * εf)
        < Real.exp ((((2 * q n - 1 : ℕ) : ℝ)) * ((9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4))) := by
  have hL : 0 < L := by linarith
  -- The exponential threshold: `8 m e^C < e^{m δ₀}` with
  -- `δ₀ = 27L/256 - 3b₀/16 ≤ (9L/32 - 2εf) - (9L/64 + b₀/4)` and `C = 23L/32 + L/500`.
  obtain ⟨Nexp, hNexp⟩ :=
    res_par_exp (C := 23 * L / 32 + 2 * (L / 1000)) (δ := 27 * L / 256 - 3 * b₀ / 16)
      (by linarith)
  refine ⟨max (max Nexp 1000) (20 ^ 9), ?_⟩
  intro q n hn hmono hqnpos εf hεf0 hεf
  have hNexp_le : Nexp ≤ n :=
    le_trans (le_trans (le_max_left Nexp 1000) (le_max_left (max Nexp 1000) (20 ^ 9))) hn
  have h1000_le : 1000 ≤ n :=
    le_trans (le_trans (le_max_right Nexp 1000) (le_max_left (max Nexp 1000) (20 ^ 9))) hn
  have h20_le : 20 ^ 9 ≤ n :=
    le_trans (le_max_right (max Nexp 1000) (20 ^ 9)) hn
  have hnq : n ≤ q n := hmono.id_le n
  have hm1 : 1000 ≤ q n := le_trans h1000_le hnq
  have hm20 : 20 ^ 9 ≤ q n := le_trans h20_le hnq
  have hmpos : 1 ≤ q n := by omega
  have hε1 : εf ≤ L / 1000 := le_trans hεf (min_le_left _ _)
  have hε2 : εf ≤ (9 * L / 64 - b₀ / 4) / 8 := le_trans hεf (min_le_right _ _)
  obtain ⟨hbG0, hbG2, hbG7, hbG8⟩ := res_par_bg hmono hm20
  obtain ⟨he1, he2, he3, he4⟩ := res_par_eps hb₀ hLb hεf0 hεf
  refine ⟨he1, he2, he3, he4, hbG0, hbG2, hbG7, hbG8, ?_, ?_⟩
  · exact res_par_lin hL hεf0 hε1 hm1 hbG0 hbG2
  · have h2m : (((2 * q n - 1 : ℕ) : ℝ)) = 2 * (q n : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 * q n by omega)]
      push_cast
      ring
    have hcw : 23 * L / 32 + 2 * εf ≤ 23 * L / 32 + 2 * (L / 1000) := by linarith
    have hδw : 27 * L / 256 - 3 * b₀ / 16 ≤
        (9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4) := by linarith
    have hδR0 : 0 ≤ (9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4) := by linarith
    have hNq : 8 * (q n : ℝ) * Real.exp (23 * L / 32 + 2 * (L / 1000))
        < Real.exp ((q n : ℝ) * (27 * L / 256 - 3 * b₀ / 16)) :=
      hNexp (q n) (le_trans hNexp_le hnq)
    calc 4 * ((((2 * q n - 1 : ℕ) : ℝ)) + 1) * Real.exp (23 * L / 32 + 2 * εf)
        = 8 * (q n : ℝ) * Real.exp (23 * L / 32 + 2 * εf) := by rw [h2m]; ring
      _ ≤ 8 * (q n : ℝ) * Real.exp (23 * L / 32 + 2 * (L / 1000)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcw) (by positivity)
      _ < Real.exp ((q n : ℝ) * (27 * L / 256 - 3 * b₀ / 16)) := hNq
      _ ≤ Real.exp ((((2 * q n - 1 : ℕ) : ℝ)) *
              ((9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4))) := by
            apply Real.exp_le_exp.mpr
            have h1 : (q n : ℝ) * (27 * L / 256 - 3 * b₀ / 16) ≤
                (q n : ℝ) * ((9 * L / 32 - 2 * εf) - (9 * L / 64 + b₀ / 4)) :=
              mul_le_mul_of_nonneg_left hδw (by positivity)
            have h2 : (q n : ℝ) ≤ 2 * (q n : ℝ) - 1 := by
              have : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hmpos
              linarith
            have h3 := mul_le_mul_of_nonneg_right h2 hδR0
            rw [h2m]
            linarith [h1, h3]

end Work.TMC16Core.Assembly
