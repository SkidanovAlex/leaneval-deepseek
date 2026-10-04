import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise Friedrichs weight estimate, support-only form

This is `Work.Diff.STE.B3.SymCalcStep1.friedrichs_pointwise_nosupp`, the pointwise estimate on
the Fourier side of the Friedrichs mollifier `trunc ρ ε` (design A8 of the STE layer), in the
form in which the downstream symbol-calculus layer consumes it: the profile `ρ` is only assumed
to be bounded by `1`, to vanish outside the ball of radius `√2` (`2 < Σ yᵢ² → ρ y = 0`) and to be
Lipschitz with constant `L`.  In particular the hypothesis `ρ = 1` on the unit ball, which the
sibling statement `Work.Diff.STE.friedrichs_pointwise` carries, is **not** needed.

For the weight `wt k = ⟨k⟩² = 1 + Σ kᵢ²` and `0 < ε ≤ 1`, `m k : ι → ℤ`:

`wt m * (ρ (ε • m) - ρ (ε • k))² ≤ 64 (1 + L²) wt (k - m)`.

The mathematical content is that the multiplier difference is controlled by the *weighted*
distance `wt (k-m)`: if `m` is large (`wt m` large) then, unless `ρ` already vanishes at both
`ε • m` and `ε • k`, the point `ε • m` is forced into the ball of radius `√2` and the Lipschitz
bound makes the difference small.

Everything is reduced to two elementary steps: the Lipschitz estimate in the Euclidean norm
(`‖y - z‖ ≤ √(Σ (yᵢ - zᵢ)²)` — Mathlib's norm on `ι → ℝ` is the sup norm, which is dominated by
the Euclidean one), and a purely algebraic case distinction on `ε² Σ mᵢ² ≤ 2`, on `ε² Σ kᵢ² ≤ 2`,
and on both being `> 2` (where `ρ` vanishes at both points).
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The sup norm on `ι → ℝ` is bounded by the Euclidean norm. -/
private lemma norm_le_sqrt_sum_sq (v : ι → ℝ) :
    ‖v‖ ≤ Real.sqrt (∑ i, (v i)^2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The scalar core of `friedrichs_pointwise_nosupp`.  `s` stands for the square of the
multiplier difference, `P` for `Σ mᵢ²`, `R` for `Σ (mᵢ - kᵢ)²`, `e` for `ε`, and
`h1P` is the case-dependent bound on `(1 + P) * ε²` obtained from the support of `ρ`. -/
private lemma wt_arith {P s L R e : ℝ} (hR : 0 ≤ R) (he : 0 < e) (he1 : e ≤ 1)
    (hP : 0 ≤ P) (h1P : (1 + P) * e^2 ≤ 4 + e^2 + 2*e^2*R) (hs4 : s ≤ 4)
    (hsL : s ≤ L^2*e^2*R) : (1+P)*s ≤ 64*(1+L^2)*(1+R) := by
  have he2 : 0 < e^2 := by positivity
  have he2le1 : e^2 ≤ 1 := by nlinarith
  have hPn : (0:ℝ) ≤ 1 + P := by linarith
  have hLRn : 0 ≤ L^2*R := mul_nonneg (sq_nonneg L) hR
  by_cases h : L^2*e^2*R ≤ 4
  · have h1 : (1+P)*s ≤ (1+P)*(L^2*e^2*R) := mul_le_mul_of_nonneg_left hsL hPn
    have h2 : (1+P)*(L^2*e^2*R) = ((1+P)*e^2)*(L^2*R) := by ring
    have h3 : ((1+P)*e^2)*(L^2*R) ≤ (4 + e^2 + 2*e^2*R)*(L^2*R) :=
      mul_le_mul_of_nonneg_right h1P hLRn
    have h4 : (4 + e^2 + 2*e^2*R)*(L^2*R) ≤ 5*L^2*R + 8*R := by
      have ha : e^2*(L^2*R) ≤ L^2*R := by
        have := mul_le_mul_of_nonneg_right he2le1 hLRn; simpa using this
      have hb : R*(L^2*e^2*R) ≤ R*4 := mul_le_mul_of_nonneg_left h hR
      nlinarith [ha, hb]
    have h5 : (5:ℝ)*L^2*R + 8*R ≤ 64*(1+L^2)*(1+R) := by nlinarith [hR]
    linarith
  · push Not at h
    have h16 : (16:ℝ) ≤ 4*(L^2*e^2*R) := by nlinarith [h]
    have hmul : (1+P)*e^2 * 4 ≤ (4 + e^2 + 2*e^2*R)*4 :=
      mul_le_mul_of_nonneg_right h1P (by norm_num)
    have hkey : (4*(1+P)) * e^2 ≤ (4*L^2*R + 4 + 8*R) * e^2 := by
      nlinarith [hmul, h16, hR]
    have h4 : 4*(1+P) ≤ 4*L^2*R + 4 + 8*R := le_of_mul_le_mul_right hkey he2
    have h5 : (1+P)*s ≤ 4*(1+P) := by
      have := mul_le_mul_of_nonneg_left hs4 hPn; linarith
    have h6 : 4*L^2*R + 4 + 8*R ≤ 64*(1+L^2)*(1+R) := by nlinarith [hR]
    linarith

theorem friedrichs_pointwise_nosupp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (k m : ι → ℤ) :
    Work.Diff.STE.wt m * (ρ (ε • (fun i => (m i : ℝ))) - ρ (ε • (fun i => (k i : ℝ)))) ^ 2
      ≤ 64 * (1 + L ^ 2) * Work.Diff.STE.wt (k - m) := by
  set a : ι → ℝ := ε • (fun i => (m i : ℝ)) with ha
  set b : ι → ℝ := ε • (fun i => (k i : ℝ)) with hb
  set P : ℝ := ∑ i, ((m i : ℝ))^2 with hP
  set Q : ℝ := ∑ i, ((k i : ℝ))^2 with hQ
  set R : ℝ := ∑ i, ((k i : ℝ) - (m i : ℝ))^2 with hR
  set A : ℝ := ∑ i, (a i)^2 with hA
  set B : ℝ := ∑ i, (b i)^2 with hB
  set D : ℝ := ∑ i, (a i - b i)^2 with hD
  have hPnn : 0 ≤ P := by rw [hP]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQnn : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hRnn : 0 ≤ R := by rw [hR]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hDnn : 0 ≤ D := by rw [hD]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA' : A = ε^2 * P := by
    rw [hA, hP]; simp only [ha, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hB' : B = ε^2 * Q := by
    rw [hB, hQ]; simp only [hb, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hD' : D = ε^2 * R := by
    rw [hD, hR]; simp only [ha, hb, Pi.smul_apply, smul_eq_mul]
    have : ∀ i, (ε * (m i : ℝ) - ε * (k i : ℝ))^2 = ε^2 * ((k i : ℝ) - (m i : ℝ))^2 :=
      fun i => by ring
    simp only [this]; rw [Finset.mul_sum]
  have hε2pos : 0 < ε^2 := by positivity
  have habsa : |ρ a| ≤ 1 := by have := hρb a; rwa [Real.norm_eq_abs] at this
  have habsb : |ρ b| ≤ 1 := by have := hρb b; rwa [Real.norm_eq_abs] at this
  have hnorm : ‖a - b‖ ≤ Real.sqrt D := by
    rw [hD]; exact norm_le_sqrt_sum_sq (a - b)
  have hlip : |ρ a - ρ b| ≤ L * Real.sqrt D := by
    rw [← Real.norm_eq_abs]
    exact le_trans (hρlip a b) (mul_le_mul_of_nonneg_left hnorm hL)
  have hsqD : (ρ a - ρ b)^2 ≤ L^2 * D := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (ρ a - ρ b)) hlip 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hDnn] at h3
    exact h3
  have hsL : (ρ a - ρ b)^2 ≤ L^2 * ε^2 * R := by
    rw [hD'] at hsqD
    linarith
  have hs4 : (ρ a - ρ b)^2 ≤ 4 := by
    have h3 : |ρ a - ρ b| ≤ 2 := by rw [abs_le] at habsa habsb ⊢; constructor <;> linarith
    have h2 := pow_le_pow_left₀ (abs_nonneg (ρ a - ρ b)) h3 2
    rw [sq_abs] at h2; norm_num at h2; exact h2
  -- the coordinatewise elementary inequality `(mᵢ)² ≤ 2 (kᵢ)² + 2 (mᵢ - kᵢ)²`
  have hQP : P ≤ 2*Q + 2*R := by
    rw [hP, hQ, hR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (2*(k i : ℝ) - (m i : ℝ))]
  have hmain : (1+P) * (ρ a - ρ b)^2 ≤ 64 * (1+L^2) * (1+R) := by
    by_cases hAc : A ≤ 2
    · -- `ε² * Σ mᵢ² ≤ 2`: the weight is at most `2/ε²`
      have hAP : ε^2 * P ≤ 2 := by linarith [hA', hAc]
      have h1P : (1+P)*ε^2 ≤ 4 + ε^2 + 2*ε^2*R := by
        nlinarith [hAP, hRnn, hε2pos, mul_nonneg hε2pos.le hRnn]
      exact wt_arith hRnn hε hε1 hPnn h1P hs4 hsL
    · push Not at hAc
      by_cases hBc : B ≤ 2
      · -- `ε² * Σ kᵢ² ≤ 2`: use `‖m‖² ≤ 2‖k‖² + 2‖m - k‖²`
        have hQle : ε^2 * Q ≤ 2 := by linarith [hB', hBc]
        have hQP' : P * ε^2 ≤ (2*Q + 2*R) * ε^2 := mul_le_mul_of_nonneg_right hQP hε2pos.le
        have h1P : (1+P)*ε^2 ≤ 4 + ε^2 + 2*ε^2*R := by
          nlinarith [hQP', hQle, hRnn, hε2pos]
        exact wt_arith hRnn hε hε1 hPnn h1P hs4 hsL
      · -- both `ε • m` and `ε • k` lie outside the ball of radius `√2`
        push Not at hBc
        have ha0 : ρ a = 0 := hρ0 a (by rw [← hA]; exact hAc)
        have hb0 : ρ b = 0 := hρ0 b (by rw [← hB]; exact hBc)
        rw [ha0, hb0, sub_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
        positivity
  rw [Work.Diff.STE.wt, Work.Diff.STE.wt]
  simp only [Pi.sub_apply, Int.cast_sub]
  exact hmain

end Work.Diff.STE.B3.SymCalcStep1
