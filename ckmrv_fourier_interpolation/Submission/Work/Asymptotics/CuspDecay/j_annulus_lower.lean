import Mathlib
import Submission.Work.Asymptotics.CuspDecay.PsiDefs
import Submission.Work.Asymptotics.CuspDecay.PsiBounds
import Submission.Work.Asymptotics.CuspDecay.j_sub_lower_lattice

/-!
# Lower bound for `j τ - j σ` on the annulus `{|Re τ| ≤ 1/2, Im τ ≥ 2}`

`j σ` is a modular function and `‖q σ‖ = e^{-2π Im σ}`; the statement below says that on the
region `Im ≥ 2`, `|Re τ - k| ≤ 1/2` (k the nearest integer to `Re τ`) and away from the
lattice point `σ + k` by distance `≥ 1/2`, the difference `j τ - j σ` dominates
`c / ‖q σ‖ = c · e^{2π Im σ}`.

The proof splits at `‖τ - σ - k‖ ≤ 2`:

* close to the lattice point, `j_sub_lower_lattice` gives `c₀ · ‖τ - σ - k‖ / ‖q σ‖ ≤ ‖j τ - j σ‖`
  for some `c₀ > 0`, and the hypothesis `1/2 ≤ ‖τ - σ - k‖` upgrades this to `(c₀/2)/‖q σ‖`;
* far from it (`2 < ‖τ - σ - k‖`), `|Re(τ - σ - k)| ≤ 1/2` forces `|Im(τ - σ)| > 1`, so the two
  points have imaginary parts differing by more than one.  Writing `j u = Ψ u / q u` with
  `Ψ = 1 + O(q)` (`3/4 ≤ ‖Ψ‖ ≤ 5/4` on `Im ≥ 2`) and using the monotonicity of
  `u ↦ exp (2π Im u)`, the larger of `‖j τ‖`, `‖j σ‖` dominates
  `(3/4) e^{2π Im σ} ≥ (3/4) e^{2π} / ‖q σ‖ ≥ (7/4)/‖q σ‖` while the smaller is at most
  `(5/4)/‖q σ‖`, giving the bound `(1/16)/‖q σ‖`.
-/

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- The reciprocal of `‖q u‖` is `e^{2π Im u}`. -/
lemma one_div_norm_qParamFun (u : UpperHalfPlane) :
    1 / ‖qParamFun u‖ = Real.exp (2 * Real.pi * u.im) := by
  rw [norm_qParamFun_eq_exp, Real.exp_neg, one_div, inv_inv]

/-- `‖j u‖ = ‖Ψ u‖ / ‖q u‖`. -/
lemma norm_jInvariantFun_eq (u : UpperHalfPlane) :
    ‖jInvariantFun u‖ = ‖Psi u‖ / ‖qParamFun u‖ := by
  have hq : qParamFun u ≠ 0 := qParamFun_ne_zero u
  have h : jInvariantFun u = Psi u / qParamFun u := by
    rw [Psi_apply]
    field_simp
  rw [h, norm_div]

/-- `‖j u‖ = ‖Ψ u‖ · e^{2π Im u}`. -/
lemma norm_jInvariantFun_eq_mul_exp (u : UpperHalfPlane) :
    ‖jInvariantFun u‖ = ‖Psi u‖ * Real.exp (2 * Real.pi * u.im) := by
  rw [norm_jInvariantFun_eq, div_eq_mul_one_div, one_div_norm_qParamFun u]

/-- `3/4 ≤ ‖Ψ u‖ ≤ 5/4` for `Im u ≥ 2`. -/
lemma Psi_norm_bounds (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    (3 / 4 : ℝ) ≤ ‖Psi u‖ ∧ ‖Psi u‖ ≤ 5 / 4 := by
  have h := Psi_sub_one_le_quarter u hu
  have h2 := abs_norm_sub_norm_le (Psi u) (1 : ℂ)
  rw [norm_one, abs_le] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- `‖j u‖ ≤ (5/4) e^{2π Im u}` for `Im u ≥ 2`. -/
lemma norm_jInvariantFun_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖jInvariantFun u‖ ≤ (5 / 4) * Real.exp (2 * Real.pi * u.im) := by
  rw [norm_jInvariantFun_eq_mul_exp u]
  exact mul_le_mul_of_nonneg_right (Psi_norm_bounds u hu).2 (le_of_lt (Real.exp_pos _))

/-- `(3/4) e^{2π Im u} ≤ ‖j u‖` for `Im u ≥ 2`. -/
lemma le_norm_jInvariantFun (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    (3 / 4) * Real.exp (2 * Real.pi * u.im) ≤ ‖jInvariantFun u‖ := by
  rw [norm_jInvariantFun_eq_mul_exp u]
  exact mul_le_mul_of_nonneg_right (Psi_norm_bounds u hu).1 (le_of_lt (Real.exp_pos _))

/-- `4 ≤ e^{2π}`. -/
lemma exp_two_pi_ge_four : (4 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have h1 : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]

/-- `e^{-2π} ≤ 1/4`. -/
lemma exp_neg_two_pi_le_quarter : Real.exp (-(2 * Real.pi)) ≤ 1 / 4 := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp_two_pi_ge_four

theorem j_annulus_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ σ : UpperHalfPlane) (k : ℤ),
      σ.re = 0 → 2 ≤ σ.im → 2 ≤ τ.im → |τ.re - (k : ℝ)| ≤ 1 / 2 →
      1 / 2 ≤ ‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ →
      c / ‖Work.Kernels.qParamFun σ‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := j_sub_lower_lattice
  refine ⟨min (c₀ / 2) (1 / 16), lt_min (by linarith) (by norm_num), ?_⟩
  intro τ σ k hσre hσim hτim hkre hdist
  have hqpos : 0 < ‖qParamFun σ‖ := by
    rw [norm_qParamFun_eq_exp]; exact Real.exp_pos _
  by_cases hnear : ‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ ≤ 2
  · -- close to the lattice point: use `j_sub_lower_lattice`
    have h := hc₀ τ σ k hσre hσim hτim hkre hnear
    calc min (c₀ / 2) (1 / 16) / ‖qParamFun σ‖
        ≤ (c₀ / 2) / ‖qParamFun σ‖ :=
          div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hqpos)
      _ ≤ c₀ * (‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ / ‖qParamFun σ‖) := by
          rw [← mul_div_assoc]
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hqpos)
          have h2 : c₀ * (1 / 2) ≤ c₀ * ‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ :=
            mul_le_mul_of_nonneg_left hdist (le_of_lt hc₀pos)
          linarith
      _ ≤ _ := h
  · -- far from the lattice point
    have hfar : 2 < ‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ := not_le.mp hnear
    set w : ℂ := (τ : ℂ) - (σ : ℂ) - (k : ℂ) with hwdef
    have hwre : |w.re| ≤ 1 / 2 := by
      have h : w.re = τ.re - (k : ℝ) := by
        rw [hwdef]; simp [Complex.sub_re, hσre]
      rw [h]; exact hkre
    have hwim : w.im = τ.im - σ.im := by
      rw [hwdef]; simp [Complex.sub_im]
    have hnorm2 : (4 : ℝ) < ‖w‖ ^ 2 := by nlinarith [hfar, norm_nonneg w]
    have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hwr2 : w.re ^ 2 ≤ 1 / 4 := by
      have h := pow_le_pow_left₀ (abs_nonneg w.re) hwre 2
      rw [sq_abs] at h
      norm_num at h
      linarith
    have hwim2 : (1 : ℝ) < w.im ^ 2 := by linarith [hsq, hnorm2, hwr2]
    have hltabs : (1 : ℝ) < |w.im| := by
      nlinarith [hwim2, sq_abs w.im, abs_nonneg w.im]
    rw [lt_abs] at hltabs
    rcases hltabs with hbig | hsmall
    · -- `τ.im > σ.im + 1`
      have hτim' : σ.im + 1 < τ.im := by linarith [hwim, hbig]
      have hexp_ge : Real.exp (2 * Real.pi) * Real.exp (2 * Real.pi * σ.im)
          ≤ Real.exp (2 * Real.pi * τ.im) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, hτim']
      have hExp : ((3 : ℝ) / 4 * Real.exp (2 * Real.pi) - 5 / 4)
              * Real.exp (2 * Real.pi * σ.im)
            ≤ (3 / 4) * Real.exp (2 * Real.pi * τ.im)
              - (5 / 4) * Real.exp (2 * Real.pi * σ.im) := by
        have h := mul_le_mul_of_nonneg_right hexp_ge
          (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
        nlinarith [h]
      have hcoef : (1 / 16 : ℝ) ≤ (3 : ℝ) / 4 * Real.exp (2 * Real.pi) - 5 / 4 := by
        nlinarith [exp_two_pi_ge_four]
      have hExp2 : (1 / 16) * Real.exp (2 * Real.pi * σ.im)
          ≤ ((3 : ℝ) / 4 * Real.exp (2 * Real.pi) - 5 / 4)
            * Real.exp (2 * Real.pi * σ.im) :=
        mul_le_mul_of_nonneg_right hcoef (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
      have hmain : (1 / 16) * Real.exp (2 * Real.pi * σ.im)
          ≤ ‖jInvariantFun τ - jInvariantFun σ‖ :=
        calc (1 / 16) * Real.exp (2 * Real.pi * σ.im)
            ≤ ((3 : ℝ) / 4 * Real.exp (2 * Real.pi) - 5 / 4)
                * Real.exp (2 * Real.pi * σ.im) := hExp2
          _ ≤ (3 / 4) * Real.exp (2 * Real.pi * τ.im)
                - (5 / 4) * Real.exp (2 * Real.pi * σ.im) := hExp
          _ ≤ ‖jInvariantFun τ‖ - ‖jInvariantFun σ‖ := by
              linarith [le_norm_jInvariantFun τ hτim, norm_jInvariantFun_le σ hσim]
          _ ≤ ‖jInvariantFun τ - jInvariantFun σ‖ :=
              (abs_le.mp (abs_norm_sub_norm_le (jInvariantFun τ) (jInvariantFun σ))).2
      have hstep : min (c₀ / 2) (1 / 16) / ‖qParamFun σ‖
          ≤ (1 / 16) * Real.exp (2 * Real.pi * σ.im) := by
        rw [div_eq_mul_one_div, one_div_norm_qParamFun σ]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _)
          (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
      exact le_trans hstep hmain
    · -- `σ.im > τ.im + 1`
      have hσim' : τ.im + 1 < σ.im := by linarith [hwim, hsmall]
      have hquarter : Real.exp (2 * Real.pi * τ.im)
          ≤ (1 / 4) * Real.exp (2 * Real.pi * σ.im) := by
        have h1 : Real.exp (2 * Real.pi * τ.im)
            ≤ Real.exp (2 * Real.pi * σ.im + -(2 * Real.pi)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, hσim']
        rw [Real.exp_add] at h1
        calc Real.exp (2 * Real.pi * τ.im)
            ≤ Real.exp (2 * Real.pi * σ.im) * Real.exp (-(2 * Real.pi)) := h1
          _ ≤ Real.exp (2 * Real.pi * σ.im) * (1 / 4) :=
              mul_le_mul_of_nonneg_left exp_neg_two_pi_le_quarter
                (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
          _ = (1 / 4) * Real.exp (2 * Real.pi * σ.im) := by ring
      have hjτ_le' : ‖jInvariantFun τ‖ ≤ (5 / 16) * Real.exp (2 * Real.pi * σ.im) := by
        have h := mul_le_mul_of_nonneg_left hquarter (by norm_num : (0 : ℝ) ≤ 5 / 4)
        linarith [norm_jInvariantFun_le τ hτim, h]
      have hmain : (1 / 16) * Real.exp (2 * Real.pi * σ.im)
          ≤ ‖jInvariantFun τ - jInvariantFun σ‖ :=
        calc (1 / 16) * Real.exp (2 * Real.pi * σ.im)
            ≤ (3 / 4) * Real.exp (2 * Real.pi * σ.im)
              - (5 / 16) * Real.exp (2 * Real.pi * σ.im) := by
              have hp := Real.exp_pos (2 * Real.pi * σ.im); linarith
          _ ≤ ‖jInvariantFun σ‖ - ‖jInvariantFun τ‖ := by
              linarith [le_norm_jInvariantFun σ hσim, hjτ_le']
          _ ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := by
              have h := abs_norm_sub_norm_le (jInvariantFun σ) (jInvariantFun τ)
              rw [norm_sub_rev] at h
              exact (abs_le.mp h).2
      have hstep : min (c₀ / 2) (1 / 16) / ‖qParamFun σ‖
          ≤ (1 / 16) * Real.exp (2 * Real.pi * σ.im) := by
        rw [div_eq_mul_one_div, one_div_norm_qParamFun σ]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _)
          (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
      exact le_trans hstep hmain

end Work.Asymptotics.CuspDecay
