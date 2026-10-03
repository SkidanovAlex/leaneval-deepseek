import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Work.FIArea5.HeckeZFR.Hadm.zeroSetFinite
import Submission.Work.FIArea5.HeckeZFR.Hadm.zeroCardLeDivisorFinsum

namespace Work.FIArea5.HeckeZFR.Hadm

open Complex Metric MeromorphicOn
open scoped BigOperators

noncomputable section

/-- **Existence of a good radius.**  If the divisor sum of an entire non-zero `Λ` is bounded by
`c·R·(log (R+2) + K)`, then for all large `A` there is `T ∈ [A, 2A]` such that every zero `u` of
`Λ` keeps distance at least `(log (A+2) + K + 1)^{-2}` from the circle `‖z‖ = T`. -/
theorem goodRadius (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (hne : ∃ z : ℂ, Λ z ≠ 0)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hcount : ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K)) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
        ∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1 := by
  classical
  -- The window radius: beyond it `log (A+2) ≥ 12c+10`, so that `6c < L` where
  -- `L = log (A+2) + K + 1` is the required resolution.
  refine ⟨max 1 (max 2 (Real.exp (12 * c + 10))), le_max_left _ _, ?_⟩
  intro A hA
  have hA2 : (2 : ℝ) ≤ A :=
    le_trans (le_trans (le_max_left (2 : ℝ) (Real.exp (12 * c + 10)))
      (le_max_right (1 : ℝ) (max 2 (Real.exp (12 * c + 10))))) hA
  have hAexp : Real.exp (12 * c + 10) ≤ A :=
    le_trans (le_trans (le_max_right (2 : ℝ) (Real.exp (12 * c + 10)))
      (le_max_right (1 : ℝ) (max 2 (Real.exp (12 * c + 10))))) hA
  have hApos : 0 < A := by linarith
  let L : ℝ := Real.log (A + 2) + K + 1
  have hlogexp : Real.log (Real.exp (12 * c + 10)) ≤ Real.log (A + 2) :=
    Real.log_le_log (Real.exp_pos _) (by linarith)
  rw [Real.log_exp] at hlogexp
  have hLbig : 12 * c + 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  -- We forbid the intervals `(‖u‖-δ, ‖u‖+δ)`, `δ = 1/L²`, around the zeros of `Λ`.
  let B : ℝ := 2 * A + 2
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith
  have hB3 : B ≤ 3 * A := by dsimp only [B]; linarith
  have hZfin : ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := zeroSetFinite Λ hDiff hne B
  let Z : Finset ℂ := hZfin.toFinset
  have hZmem : ∀ u : ℂ, u ∈ Z ↔ Λ u = 0 ∧ ‖u‖ ≤ B := by
    intro u; dsimp only [Z]; exact hZfin.mem_toFinset
  let centres : Finset ℝ := Z.image (fun u : ℂ => ‖u‖)
  have hcentres_le : (centres.card : ℝ) ≤ (Z.card : ℝ) := by
    dsimp only [centres]
    exact_mod_cast (Finset.card_image_le (s := Z) (f := fun u : ℂ => ‖u‖))
  have hcardZ : (Z.card : ℝ) ≤
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 B)) u : ℝ) :=
    zeroCardLeDivisorFinsum Λ hDiff hne B hZfin
  have hbound : (Z.card : ℝ) ≤ c * B * (Real.log (B + 2) + K) :=
    le_trans hcardZ (hcount B hB1)
  have hcentres_bound : (centres.card : ℝ) ≤ c * B * (Real.log (B + 2) + K) :=
    le_trans hcentres_le hbound
  have hlogB : Real.log (B + 2) ≤ Real.log (A + 2) + 1 := by
    have hEq : B + 2 = 2 * (A + 2) := by dsimp only [B]; ring
    rw [hEq, Real.log_mul (by norm_num) (by linarith)]
    linarith [Commons.NumberTheory.Linnik.grg_log_two_le_one]
  have hℓB_le : Real.log (B + 2) + K ≤ L := by dsimp only [L]; linarith
  -- Total width of the forbidden intervals is `< A`.
  have hmainAux : (centres.card : ℝ) * 2 < A * L ^ 2 := by
    have h1 : (centres.card : ℝ) ≤ c * B * L := by
      calc (centres.card : ℝ) ≤ c * B * (Real.log (B + 2) + K) := hcentres_bound
        _ ≤ c * B * L := mul_le_mul_of_nonneg_left hℓB_le (by positivity)
    have h2 : c * B * L ≤ c * (3 * A) * L := by
      have hBL : B * L ≤ (3 * A) * L := mul_le_mul_of_nonneg_right hB3 (le_of_lt hLpos)
      calc c * B * L = c * (B * L) := by ring
        _ ≤ c * ((3 * A) * L) := mul_le_mul_of_nonneg_left hBL hc
        _ = c * (3 * A) * L := by ring
    have h12 : (centres.card : ℝ) ≤ c * (3 * A) * L := le_trans h1 h2
    have hcard2 : (centres.card : ℝ) * 2 ≤ (c * (3 * A) * L) * 2 :=
      mul_le_mul_of_nonneg_right h12 (by norm_num)
    have h6 : (c * (3 * A) * L) * 2 = 6 * c * A * L := by ring
    have h6c : 6 * c < L := by linarith
    have hkey : 6 * c * (A * L) < L * (A * L) :=
      mul_lt_mul_of_pos_right h6c (mul_pos hApos hLpos)
    have hkey' : 6 * c * A * L < A * L ^ 2 := by nlinarith [hkey]
    have hcard2' : (centres.card : ℝ) * 2 ≤ 6 * c * A * L := by rw [← h6]; exact hcard2
    linarith
  have hcard' : (centres.card : ℝ) * (2 / L ^ 2) < A := by
    rw [← mul_div_assoc]
    rw [div_lt_iff₀ hL2pos]
    simpa [mul_assoc] using hmainAux
  have hcard'' : (centres.card : ℝ) * (2 / L ^ 2) < 2 * A - A := by linarith
  have hw : 0 < 2 / L ^ 2 := div_pos (by norm_num) hL2pos
  have hab : A ≤ 2 * A := by linarith
  obtain ⟨T, hT1, hT2, hgood⟩ :=
    Commons.NumberTheory.Linnik.grg_exists_good_point_of_small_measure hab hw centres hcard''
  have hw2 : (2 / L ^ 2) / 2 = (1 : ℝ) / L ^ 2 := by
    have hne : L ^ 2 ≠ 0 := ne_of_gt hL2pos
    field_simp
  have hgood' : ∀ z ∈ centres, (1 : ℝ) / L ^ 2 ≤ |T - z| := by
    intro z hz
    rw [← hw2]
    exact hgood z hz
  refine ⟨T, hT1, hT2, ?_⟩
  intro u hu0
  have hdist : (1 : ℝ) / L ^ 2 ≤ |‖u‖ - T| := by
    by_cases huB : ‖u‖ ≤ B
    · -- zeros inside the ball have their modulus in `centres`
      have hmem : ‖u‖ ∈ centres := by
        dsimp only [centres]
        exact Finset.mem_image.mpr ⟨u, (hZmem u).2 ⟨hu0, huB⟩, rfl⟩
      have hd := hgood' (‖u‖) hmem
      simpa [abs_sub_comm] using hd
    · -- zeros outside the ball are far beyond the window
      have hBlt : B < ‖u‖ := lt_of_not_ge huB
      have hbig : (2 : ℝ) ≤ ‖u‖ - T := by dsimp only [B] at hBlt; linarith
      have hd2 : (1 : ℝ) / L ^ 2 ≤ 2 := by
        have h1 := Commons.NumberTheory.Linnik.grg_one_div_sq_le_one hL1
        linarith
      have hle : (1 : ℝ) / L ^ 2 ≤ ‖u‖ - T := le_trans hd2 hbig
      have hnn : 0 ≤ ‖u‖ - T := by linarith
      simpa [abs_of_nonneg hnn] using hle
  have hfin : L ^ 2 * |‖u‖ - T| ≥ 1 := by
    have h2 : 1 ≤ |‖u‖ - T| * L ^ 2 := (div_le_iff₀ hL2pos).mp hdist
    have h3 : (1 : ℝ) ≤ L ^ 2 * |‖u‖ - T| := by simpa [mul_comm] using h2
    linarith
  dsimp only [L] at hfin ⊢
  exact hfin

end

end Work.FIArea5.HeckeZFR.Hadm
