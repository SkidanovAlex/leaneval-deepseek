import Mathlib
import Submission.Work.OffAxis.TF72Num103a
import Submission.Work.OffAxis.G72Sub2Aux
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.G72ImagReBound
import Submission.Work.OffAxis.LHFGridPoints

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.OffAxis

open Work.ZeroFreeTables Work.ZeroFreeTables.OffAxis

/-!
# `Rect10_3Sub2Numeric`

HB (1992) condition (10.12) at `λ = 6/7`, in the `tf72Fc` normalisation:

  `Re F(-a+im) - Re F(im) ≤ (7/24) f(0) = 4/15`  for `0 ≤ a ≤ 6/7` and `|m| ≥ 9/7`.

Scaling with `tf72Fc_scale` (`F_λ(z) = F_1(z/λ)`) and `tf72Fc 1 = G72` turns this into the
scale-free statement `LHF s σ ≤ 4/15` for `s = 7a/6 ∈ [0,1]`, `σ = 7m/6` with `|σ| ≥ 3/2`,
`LHF s σ = Re G72(-s+iσ) - Re G72(iσ)` (the quantity of `OffAxis/G72Sub2Aux`).

The proof splits at `σ = 7/2`:

* `σ ≥ 7/2`: `LHF = Isub + Re G72(iσ) ≤ 16/105 + 4/35 = 4/15`, by HB (10.8) at `λ = 6/7`
  (`Isub_le_all`) and the elementary tail bound `G72ImagReBound`;
* `3/2 ≤ σ ≤ 7/2`: two-point interpolation in `σ` (`LHF_sigma_interp`) and in `s`
  (`LHF_s_interp`) on the grid `σ ∈ {3/2,2,5/2,3,7/2}`, `s ∈ {0,1/2,1}`; the values at the
  grid points are bounded in `LHFGridPoints` (the only delicate one being
  `LHF 1 (3/2) < 0.172 ≤ 9/50`).  The two interpolation errors are `(1/2)²/8·(13/10) = 13/320`
  each, so `LHF ≤ 9/50 + 13/160 = 209/800 ≤ 4/15`.
-/

/-- `LHF s ·` is even in the second variable. -/
lemma LHF_even (s σ : ℝ) : LHF s (-σ) = LHF s σ := by
  rw [LHF_eq_integral, LHF_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  show (Real.exp (s*y) - 1) * Real.cos ((-σ)*y) * g72 y
      = (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y
  have harg : (-σ) * y = -(σ * y) := by ring
  rw [harg, Real.cos_neg]

/-- **The scale-free core bound.** `Re G72(-s+iσ) - Re G72(iσ) ≤ 4/15` for `0 ≤ s ≤ 1`,
`σ ≥ 3/2`. -/
theorem LHF_le (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 3/2 ≤ σ) : LHF s σ ≤ 4/15 := by
  rcases le_or_gt σ (7/2) with hσ7 | hσ7
  · -- `3/2 ≤ σ ≤ 7/2`: interpolation on the grid `{3/2,2,5/2,3,7/2} × {0,1/2,1}`
    have hs_interp : ∀ t : ℝ, (t = 3/2 ∨ t = 2 ∨ t = 5/2 ∨ t = 3 ∨ t = 7/2) →
        LHF s t ≤ 9/50 + 13/320 := by
      intro t ht
      rcases le_or_gt s (1/2) with hs2 | hs2
      · have h := LHF_s_interp s t 0 (1/2) (le_refl 0) (by norm_num) hs0 hs2
        have h0 : LHF 0 t = 0 := by simp [LHF]
        have hmax : max (LHF 0 t) (LHF (1/2) t) ≤ 9/50 := by
          rw [h0]
          exact max_le (by norm_num) (LHFGridPoints (1/2) t (Or.inr (Or.inl rfl)) ht)
        have hd : ((1:ℝ)/2 - 0)^2/8*(13/10) = 13/320 := by norm_num
        rw [hd] at h
        linarith
      · have h := LHF_s_interp s t (1/2) 1 (by norm_num) (by norm_num) (le_of_lt hs2) hs1
        have hmax : max (LHF (1/2) t) (LHF 1 t) ≤ 9/50 :=
          max_le (LHFGridPoints (1/2) t (Or.inr (Or.inl rfl)) ht)
                 (LHFGridPoints 1 t (Or.inr (Or.inr rfl)) ht)
        have hd : ((1:ℝ) - 1/2)^2/8*(13/10) = 13/320 := by norm_num
        rw [hd] at h
        linarith
    have sig_interp : ∀ t0 t1 : ℝ, t0 ≤ σ → σ ≤ t1 → t1 - t0 = 1/2 →
        (t0 = 3/2 ∨ t0 = 2 ∨ t0 = 5/2 ∨ t0 = 3 ∨ t0 = 7/2) →
        (t1 = 3/2 ∨ t1 = 2 ∨ t1 = 5/2 ∨ t1 = 3 ∨ t1 = 7/2) →
        LHF s σ ≤ 4/15 := by
      intro t0 t1 ht0 ht1 hd h0 h1
      have h := LHF_sigma_interp s σ t0 t1 hs0 hs1 ht0 ht1
      have hd' : (t1 - t0)^2/8*(13/10) = 13/320 := by rw [hd]; norm_num
      rw [hd'] at h
      have hm : max (LHF s t0) (LHF s t1) ≤ 9/50 + 13/320 :=
        max_le (hs_interp t0 h0) (hs_interp t1 h1)
      have hnum : (9:ℝ)/50 + (13:ℝ)/320 + 13/320 ≤ 4/15 := by norm_num
      linarith
    rcases le_or_gt σ 2 with h2 | h2
    · exact sig_interp (3/2) 2 hσ h2 (by norm_num) (Or.inl rfl) (Or.inr (Or.inl rfl))
    · rcases le_or_gt σ (5/2) with h52 | h52
      · exact sig_interp 2 (5/2) (le_of_lt h2) h52 (by norm_num)
          (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
      · rcases le_or_gt σ 3 with h3 | h3
        · exact sig_interp (5/2) 3 (le_of_lt h52) h3 (by norm_num)
            (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact sig_interp 3 (7/2) (le_of_lt h3) hσ7 (by norm_num)
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · -- `σ ≥ 7/2`: `LHF = Isub + Re G72(iσ)`
    have hQ : (G72 ((σ:ℂ)*Complex.I)).re ≤ 4/35 := G72ImagReBound σ (le_of_lt hσ7)
    have hIsub : Isub s σ ≤ 16/105 := Isub_le_all s σ hs0 hs1
    have heq : LHF s σ = Isub s σ + (G72 ((σ:ℂ)*Complex.I)).re := by
      unfold LHF Isub
      rw [← Complex.ofReal_neg]
      ring
    rw [heq]
    linarith

theorem Rect10_3Sub2Numeric : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 9/7 ≤ |m| →
    (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
      - (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) ((m : ℂ) * Complex.I)).re ≤ 7/24 * (32/35) := by
  intro a m ha0 ha6 hm
  have hlam : (0:ℝ) < 6/7 := by norm_num
  rw [tf72Fc_scale ((6:ℝ)/7) hlam (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I),
      tf72Fc_scale ((6:ℝ)/7) hlam ((m : ℂ) * Complex.I)]
  rw [tf72Fc_one_eq_G72, tf72Fc_one_eq_G72]
  have hpoint : ((((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ) : ℂ))
      = ((-(7*a/6) : ℝ) : ℂ) + ((7*m/6 : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  have hpoint2 : (((m : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ) : ℂ))
      = (((7*m/6 : ℝ)) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hpoint, hpoint2]
  have hLHF : (G72 (((-(7*a/6) : ℝ) : ℂ) + ((7*m/6 : ℝ) : ℂ) * Complex.I)).re
      - (G72 (((7*m/6 : ℝ) : ℂ) * Complex.I)).re = LHF (7*a/6) (7*m/6) := by
    unfold LHF
    rw [Complex.ofReal_neg]
  rw [hLHF]
  rw [show (7:ℝ)/24 * (32/35) = 4/15 by norm_num]
  have hs0 : 0 ≤ 7*a/6 := by linarith
  have hs1 : 7*a/6 ≤ 1 := by linarith
  rcases le_or_gt 0 m with hm0 | hm0
  · have hm' : 9/7 ≤ m := by rwa [abs_of_nonneg hm0] at hm
    exact LHF_le (7*a/6) (7*m/6) hs0 hs1 (by linarith)
  · have hm' : 9/7 ≤ -m := by
      rw [abs_of_neg hm0] at hm; linarith
    have hev : LHF (7*a/6) (7*m/6) = LHF (7*a/6) (7*(-m)/6) := by
      have harg : (7*m/6 : ℝ) = -(7*(-m)/6) := by ring
      rw [harg, LHF_even]
    rw [hev]
    exact LHF_le (7*a/6) (7*(-m)/6) hs0 hs1 (by linarith)

end Work.OffAxis
