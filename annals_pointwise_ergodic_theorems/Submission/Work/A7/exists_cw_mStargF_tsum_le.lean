import Mathlib
import Submission.Work.KMTAreas.A7.CwTsumLe
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds

/-!
# A uniform `ℓ¹`-bound for the Fourier coefficients of the §6 bump `mStargF d u`

`Work.KMTAreas.A7.mStargF d u = η_{≤ -2du}` is the rescaled KMT cutoff of inverse width
`R = 2^{2du}` — the second tensor factor `m_{*,g}` of the §6 model symbol of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022.

This module proves that the `ℓ¹`-mass `∑_j ‖cw (mStargF d u) j‖` of its Fourier coefficients is
bounded by a constant **independent of `u`**.  The mathematics is the crude multiplier bound
`Work.KMTAreas.A7.CwTsumLe`: a bump of inverse width `R ≥ 1` satisfies

  `∑_j ‖(𝓕⁻m)(j)‖ ≤ C·C₀`   whenever   `‖m‖_∞ ≤ C₀`, `‖m'‖_∞ ≤ C₀·R`, `‖m''‖_∞ ≤ C₀·R²`.

For `m = mStargF d u` one has `m θ = η(R θ)` with `R = 2^{2du}`, so the three bounds hold with
the single amplitude `C₀ = max 1 (max M₀ (max M₁ M₂))`, where `M₀, M₁, M₂` are the `C²`-bounds on
the KMT cutoff `η` (`Work.KMTAreas.A7.kmtEta_deriv_bounds`): the dilation contributes the factors
`R` and `R²` to the first and second derivative, exactly compensating the `1/R`, `1/R²` in the
hypotheses.  Hence the constant is uniform in `u`.

The statement's hypothesis `1 ≤ d` is not needed for the argument (`R = 1` at `d = 0` still
satisfies `1 ≤ R`); it is kept because the statement is fixed.

Everything below is sorry-free; the only imported inputs are `CwTsumLe` and
`kmtEta_deriv_bounds`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7

open Work.KMTContract (kmtEta)

/-! ## The chain rule for a dilation `θ ↦ f (c · θ)` -/

/-- `iteratedDeriv 2 = deriv ∘ deriv`. -/
private lemma iteratedDeriv_two_eq_deriv (f : ℝ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The derivative of a right dilation: `(θ ↦ f (c · θ))' = θ ↦ c · f' (c · θ)`
(the elementary case `deriv_comp_mul_left` of the chain rule, with the scalar action on `ℂ`
written as a product). -/
private lemma deriv_comp_mul_left' (f : ℝ → ℂ) (c : ℝ) :
    deriv (fun y : ℝ => f (c * y)) = fun y => (c : ℂ) * deriv f (c * y) := by
  funext y
  rw [deriv_comp_mul_left, Complex.real_smul]

/-- The second derivative of a right dilation: `(θ ↦ f (c · θ))'' (x) = c² · f'' (c · x)`.
Obtained from the first derivative by one more chain rule and the (differentiability-free)
rule `deriv_const_mul_field` for a constant multiple in a division ring. -/
private lemma deriv_deriv_comp_mul_left' (f : ℝ → ℂ) (c x : ℝ) :
    deriv (deriv (fun y : ℝ => f (c * y))) x
      = (c : ℂ) * ((c : ℂ) * deriv (deriv f) (c * x)) := by
  rw [deriv_comp_mul_left' f c, deriv_const_mul_field, deriv_comp_mul_left, Complex.real_smul]

/-! ## The main statement -/

/-- **The `ℓ¹`-mass of the Fourier coefficients of `mStargF d u` is bounded uniformly in `u`.**

The bump `mStargF d u` is `θ ↦ η(R θ)` with inverse width `R = 2^{2du} ≥ 1`; its sup-norm and its
first two derivatives are bounded by `C₀ = max 1 (max M₀ (max M₁ M₂))`,
`C₀ · R` and `C₀ · R²`, and `Work.KMTAreas.A7.CwTsumLe` turns these three bounds into the
`ℓ¹`-bound `∑_j ‖cw (mStargF d u) j‖ ≤ C* · C₀` with `C*` absolute. -/
theorem exists_cw_mStargF_tsum_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℕ,
      ∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ ≤ C := by
  -- the two imported ingredients: the crude multiplier bound and the `C²`-bounds on `η`
  obtain ⟨Cstar, hCstar_pos, hCstar⟩ := Work.KMTAreas.A7.CwTsumLe
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hcdEta, hb0, hb1, hb2, hz0, hz1, hz2, hdEta, hdEta2⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  -- `η` and its first two derivatives are *globally* bounded: they vanish off `[-1,1]`
  have gb0 : ∀ y : ℝ, ‖kmtEta y‖ ≤ M0 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hb0 y h
    · rw [hz0 y (not_le.mp h).le, norm_zero]
      exact hM0
  have gb1 : ∀ y : ℝ, ‖deriv kmtEta y‖ ≤ M1 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hb1 y h
    · rw [hz1 y (not_le.mp h).le, norm_zero]
      exact hM1
  have gb2 : ∀ y : ℝ, ‖deriv (deriv kmtEta) y‖ ≤ M2 := by
    intro y
    by_cases h : |y| ≤ 1
    · rw [← iteratedDeriv_two_eq_deriv kmtEta]
      exact hb2 y h
    · rw [← iteratedDeriv_two_eq_deriv kmtEta, hz2 y (not_le.mp h).le, norm_zero]
      exact hM2
  -- the single amplitude constant
  set C0 : ℝ := max 1 (max M0 (max M1 M2)) with hC0
  have hC0pos : 0 < C0 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC0nn : 0 ≤ C0 := hC0pos.le
  have hM0le : M0 ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM1le : M1 ≤ C0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right M0 _)) (le_max_right _ _)
  have hM2le : M2 ≤ C0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right M0 _)) (le_max_right _ _)
  refine ⟨Cstar * C0, mul_pos hCstar_pos hC0pos, fun u => ?_⟩
  -- the inverse width `R = 2^{2du}` and the closed form of the bump
  set R : ℝ := (2 : ℝ) ^ (2 * d * u) with hRdef
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRnn : 0 ≤ R := hRpos.le
  have hRC : ‖((R : ℝ) : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_of_nonneg hRnn]
  have hpow : (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) = R⁻¹ := by
    have hcast : ((d : ℤ) * 2 * (u : ℤ)) = ((2 * d * u : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, zpow_neg, zpow_natCast, hRdef]
  have hfun : Work.KMTAreas.A7.mStargF d u = fun θ : ℝ => kmtEta (R * θ) := by
    funext θ
    have h1 := (Work.KMTContract.etaCutRegular (-((d : ℤ) * 2 * (u : ℤ)))).2.1 θ
    show Work.Analysis.IonescuWainger.etaCut kmtEta (-((d : ℤ) * 2 * (u : ℤ))) θ
      = kmtEta (R * θ)
    rw [h1, hpow, div_inv_eq_mul, mul_comm R θ]
  -- the five hypotheses of `CwTsumLe`, all of them for the closed form `θ ↦ η (R · θ)`
  refine hCstar (Work.KMTAreas.A7.mStargF d u) C0 R hC0nn hR1 ?_ ?_ ?_ ?_ ?_
  · rw [hfun]
    exact hcdEta.comp (contDiff_const.mul contDiff_id)
  · intro θ
    rw [hfun]
    exact le_trans (gb0 (R * θ)) hM0le
  · intro θ
    rw [hfun, deriv_comp_mul_left', norm_mul, hRC]
    calc R * ‖deriv kmtEta (R * θ)‖ ≤ R * M1 := mul_le_mul_of_nonneg_left (gb1 (R * θ)) hRnn
      _ ≤ C0 * R := by rw [mul_comm C0 R]; exact mul_le_mul_of_nonneg_left hM1le hRnn
  · intro θ
    rw [hfun, deriv_deriv_comp_mul_left' kmtEta R θ, norm_mul, norm_mul, hRC]
    calc R * (R * ‖deriv (deriv kmtEta) (R * θ)‖) ≤ R * (R * M2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gb2 (R * θ)) hRnn) hRnn
      _ ≤ C0 * R ^ 2 := by nlinarith [hM2le, hRnn, sq_nonneg R]
  · intro θ hθ
    rw [hfun]
    show kmtEta (R * θ) = 0
    refine hz0 (R * θ) ?_
    rw [abs_mul, abs_of_nonneg hRnn]
    have h1 : (1 / R) * R < |θ| * R := mul_lt_mul_of_pos_right hθ hRpos
    rw [one_div_mul_cancel (ne_of_gt hRpos)] at h1
    rw [mul_comm R |θ|]
    exact h1.le

end Work.A7
