import Mathlib
import Submission.Work.TMC16Core.Basic.green_bound_notA

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- **Windowed Green-function bound (AJ §9).**  Same as `green_bound_notA` but the
continuant bound `hbd` is only assumed on the window `n₀ ≤ n ≤ k`; the two indices at
which it is actually consumed, `(x₂-y).toNat` and `(y-x₁).toNat`, are placed in the
window by the hypotheses `hn₁`, `hn₂`. -/
theorem green_bound_notA_win {α lam : ℝ} {E : ℂ} {θ r L ε₁ : ℝ} {k : ℕ} {x₁ x₂ y : ℤ} {n₀ : ℕ}
    (hbd : ∀ n : ℕ, n₀ ≤ n → n ≤ k → ∀ ζ : ℝ, ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤
        Real.exp ((n : ℝ) * (L + ε₁)))
    (hn₁ : n₀ ≤ (x₂ - y).toNat) (hn₂ : n₀ ≤ (y - x₁).toNat)
    (hx : x₂ = x₁ + (k : ℤ) - 1) (h1 : x₁ ≤ y) (h2 : y ≤ x₂)
    (hnot : Real.exp (((k : ℝ) + 1) * r) <
        ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (k + 1)‖) :
    ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ <
        Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) ∧
      ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ <
        Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
  obtain ⟨htn, htn1, hy_le, hxy_le, hlen, hy_cast, hxy_cast, hx1x1⟩ :=
    toNat_interval_facts hx h1 h2
  have hkpos : 0 < k := by omega
  have hyx1_lt : (y - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    have hyz : ((y - x₁).toNat : ℤ) = y - x₁ := Int.toNat_of_nonneg (by omega)
    have hxz : ((x₂ - x₁).toNat : ℤ) = x₂ - x₁ := Int.toNat_of_nonneg (by omega)
    have hle : (y - x₁).toNat ≤ (x₂ - x₁).toNat := by
      have h2' : ((y - x₁).toNat : ℤ) ≤ ((x₂ - x₁).toNat : ℤ) := by rw [hyz, hxz]; omega
      omega
    have hle2 : (y - x₁).toNat ≤ k - 1 := by rw [← htn1]; exact hle
    rw [htn]
    omega
  have hx2x1_lt : (x₂ - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    rw [htn, htn1]; omega
  have hx1x1_lt : (x₁ - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    rw [hx1x1, htn]; omega
  have hG1 := G_eq_inv_entry (α := α) (lam := lam) (θ := θ) (E := E) (x₁ := x₁) (x₂ := x₂)
    (y := y) (z := x₁) hyx1_lt hx1x1_lt
  have hG2 := G_eq_inv_entry (α := α) (lam := lam) (θ := θ) (E := E) (x₁ := x₁) (x₂ := x₂)
    (y := y) (z := x₂) hyx1_lt hx2x1_lt
  have hden1 : (x₂-x₁+1).toNat + 1 = k + 1 := by rw [htn]
  constructor
  · rw [hG1]
    by_cases hdet : (dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat)).det = 0
    · rw [matrix_inv_apply_eq_zero_of_det_eq_zero hdet]
      simp only [norm_zero]
      exact Real.exp_pos _
    · have hcol := dirMat_inv_firstCol (α := α) (lam := lam) (φ := θ + (x₁:ℝ)*α) (E := E)
        hdet ⟨(x₁-x₁).toNat, hx1x1_lt⟩ hx1x1 ⟨(y-x₁).toNat, hyx1_lt⟩
      rw [hcol]
      have hph : θ + (x₁:ℝ)*α + (((y-x₁).toNat : ℝ) + 1) * α = θ + ((y:ℝ) + 1) * α := by
        rw [hy_cast]; push_cast; ring
      have hlen1 : (x₂-x₁+1).toNat - (y-x₁).toNat = (x₂-y).toNat + 1 := by
        rw [htn]; exact hlen
      rw [hph, hlen1, hden1, norm_div, norm_neg]
      have hnum : ‖pd α lam (θ + ((y:ℝ) + 1) * α) E ((x₂-y).toNat + 1)‖
          ≤ Real.exp (((x₂-y : ℤ) : ℝ) * (L + ε₁)) := by
        have h := hbd (x₂-y).toNat hn₁ hxy_le (θ + ((y:ℝ) + 1) * α)
        rwa [hxy_cast] at h
      have hthis : ‖pd α lam (θ + ((y:ℝ) + 1) * α) E ((x₂-y).toNat + 1)‖
            / ‖pd α lam (θ + (x₁:ℝ)*α) E (k + 1)‖
          < Real.exp (((x₂-y : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r) :=
        div_lt_exp_sub hnot (norm_nonneg _) hnum
      rwa [show ((x₂ - y : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r
          = (L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k:ℝ) + 1) * r by ring] at hthis
  · rw [hG2]
    by_cases hdet : (dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat)).det = 0
    · rw [matrix_inv_apply_eq_zero_of_det_eq_zero hdet]
      simp only [norm_zero]
      exact Real.exp_pos _
    · have hj2 : ((⟨(x₂-x₁).toNat, hx2x1_lt⟩ : Fin (x₂-x₁+1).toNat) : ℕ) = (x₂-x₁+1).toNat - 1 := by
        show (x₂ - x₁).toNat = (x₂ - x₁ + 1).toNat - 1
        rw [htn, htn1]
      have hcol := dirMat_inv_lastCol' (α := α) (lam := lam) (φ := θ + (x₁:ℝ)*α) (E := E)
        hdet ⟨(x₂-x₁).toNat, hx2x1_lt⟩ hj2 ⟨(y-x₁).toNat, hyx1_lt⟩
      rw [hcol, hden1, norm_neg, norm_div]
      have hnum : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
          ≤ Real.exp (((y-x₁ : ℤ) : ℝ) * (L + ε₁)) := by
        have h := hbd (y-x₁).toNat hn₂ hy_le (θ + (x₁:ℝ)*α)
        rwa [hy_cast] at h
      have hthis : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
            / ‖pd α lam (θ + (x₁:ℝ)*α) E (k + 1)‖
          < Real.exp (((y-x₁ : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r) :=
        div_lt_exp_sub hnot (norm_nonneg _) hnum
      rwa [show ((y - x₁ : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r
          = (L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k:ℝ) + 1) * r by ring] at hthis

end Work.TMC16Core.Basic
