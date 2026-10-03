/-
# Derivative bounds for the rescaled cutoffs `η_{≤ j}`

This file proves `Work.KMTAreas.A4.offCutDeriv`: the rescaled Littlewood–Paley cutoff
`η_{≤j}(x) = η(x / 2^j)` (realised as the Schwartz function `etaMult_etaCutSch j`) satisfies the
*scaling* derivative bounds

  `‖η_{≤j}'  x‖ ≤ C · 2^{-j}`,   `‖η_{≤j}'' x‖ ≤ C · (2^{-j})²`

with a single constant `C > 0` for all `j : ℤ` and all `x : ℝ`.

## The mathematics

`η = kmtEta` is the complexification of a `ContDiffBump`, hence `C^∞` with compact support
contained in `[-1,1]` (`etaMult_kmtEta_contDiff`, `etaMult_kmtEta_supp`).  Consequently `η'` and
`η''` are continuous with compact support, so they are *bounded*: there are absolute constants
`C₁`, `C₂` with `‖η' y‖ ≤ C₁` and `‖η'' y‖ ≤ C₂` for every `y`.  The chain rule for a dilation
(`iteratedDeriv_comp_const_smul`) gives
`η_{≤j}^{(n)}(x) = (2^{-j})^n · η^{(n)}(x / 2^j)`, and the two estimates follow by taking
`C = max 1 (max C₁ C₂)`.

## Layout

1. `η` is smooth (`hdiff`) with compact support (`hcs`);
2. `∃ C₁, ∀ y, ‖η' y‖ ≤ C₁` and `∃ C₂, ∀ y, ‖η'' y‖ ≤ C₂` — continuity plus compact support
   (`Continuous.bounded_above_of_compact_support`, `HasCompactSupport.deriv`), together with
   `iteratedDeriv 2 η = deriv (deriv η)`;
3. the two pointwise bounds, by the dilation chain rule and `norm_smul`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.EtaMult

namespace Work.KMTAreas.A4

open Work.KMTContract (kmtEta)

/-- **Derivative bounds for the rescaled cutoffs `η_{≤j}`.**

There is a constant `C > 0` such that for every `j : ℤ` the rescaled cutoff
`η_{≤j} = etaMult_etaCutSch j` satisfies, for every `x : ℝ`,
`‖η_{≤j}'(x)‖ ≤ C · 2^{-j}` and `‖η_{≤j}''(x)‖ ≤ C · (2^{-j})²`. -/
theorem offCutDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (x : ℝ),
      ‖deriv ((Work.KMTAreas.A7.etaMult_etaCutSch j : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
          ≤ C * (2 : ℝ) ^ (-j) ∧
      ‖iteratedDeriv 2 ((Work.KMTAreas.A7.etaMult_etaCutSch j : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
          ≤ C * ((2 : ℝ) ^ (-j)) ^ 2 := by
  -- `η` is smooth with compact support
  have hdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) kmtEta :=
    Work.KMTAreas.A7.etaMult_kmtEta_contDiff
  have hcs : HasCompactSupport kmtEta :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 1)
      Work.KMTAreas.A7.etaMult_kmtEta_supp
  -- bounds for `η'` and `η''`
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ y : ℝ, ‖deriv kmtEta y‖ ≤ C :=
    (hdiff.continuous_deriv (by simp)).bounded_above_of_compact_support hcs.deriv
  have h2eq : iteratedDeriv 2 kmtEta = deriv (deriv kmtEta) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcs2 : HasCompactSupport (iteratedDeriv 2 kmtEta) := by
    rw [h2eq]; exact hcs.deriv.deriv
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, ∀ y : ℝ, ‖iteratedDeriv 2 kmtEta y‖ ≤ C :=
    ((ContDiff.continuous_iteratedDeriv (𝕜 := ℝ) (f := kmtEta) 2 hdiff
        (by exact WithTop.coe_le_coe.mpr le_top))).bounded_above_of_compact_support hcs2
  refine ⟨max 1 (max C₁ C₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro j x
  -- `etaMult_etaCutSch j` is the dilation `x ↦ η (x / 2^j)`
  have hfun : (⇑(Work.KMTAreas.A7.etaMult_etaCutSch j) : ℝ → ℂ)
      = fun y : ℝ => kmtEta (y / (2 : ℝ) ^ j) := by
    funext y
    rw [Work.KMTAreas.A7.etaMult_etaCutSch_coe]
    rfl
  -- `x / 2^j = 2^{-j} · x`
  have hdiv : (fun y : ℝ => kmtEta (y / (2 : ℝ) ^ j))
      = fun y : ℝ => kmtEta ((2 : ℝ) ^ (-j) * y) := by
    funext y
    rw [div_eq_inv_mul, ← zpow_neg]
  have hC₁le : C₁ ≤ max 1 (max C₁ C₂) := le_trans (le_max_left C₁ C₂) (le_max_right 1 _)
  have hC₂le : C₂ ≤ max 1 (max C₁ C₂) := le_trans (le_max_right C₁ C₂) (le_max_right 1 _)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-j) := zpow_pos (by norm_num) (-j)
  constructor
  · rw [hfun, hdiv]
    -- chain rule for the dilation, first derivative
    have hcomp := iteratedDeriv_comp_const_smul (f := kmtEta) (n := 1)
      (hdiff.of_le (by simp)) ((2 : ℝ) ^ (-j))
    have hy : deriv (fun y : ℝ => kmtEta ((2 : ℝ) ^ (-j) * y)) x
        = (2 : ℝ) ^ (-j) • deriv kmtEta ((2 : ℝ) ^ (-j) * x) := by
      rw [← iteratedDeriv_one (f := fun y : ℝ => kmtEta ((2 : ℝ) ^ (-j) * y)),
        hcomp, iteratedDeriv_one, pow_one]
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    calc (2 : ℝ) ^ (-j) * ‖deriv kmtEta ((2 : ℝ) ^ (-j) * x)‖
        ≤ (2 : ℝ) ^ (-j) * C₁ := mul_le_mul_of_nonneg_left (hC₁ _) (le_of_lt hpos)
      _ ≤ (2 : ℝ) ^ (-j) * max 1 (max C₁ C₂) :=
          mul_le_mul_of_nonneg_left hC₁le (le_of_lt hpos)
      _ = max 1 (max C₁ C₂) * (2 : ℝ) ^ (-j) := mul_comm _ _
  · rw [hfun, hdiv]
    -- chain rule for the dilation, second derivative
    have hcomp := iteratedDeriv_comp_const_smul (f := kmtEta) (n := 2)
      (hdiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)) ((2 : ℝ) ^ (-j))
    rw [hcomp, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (-j)) ^ 2)]
    calc ((2 : ℝ) ^ (-j)) ^ 2 * ‖iteratedDeriv 2 kmtEta ((2 : ℝ) ^ (-j) * x)‖
        ≤ ((2 : ℝ) ^ (-j)) ^ 2 * C₂ :=
          mul_le_mul_of_nonneg_left (hC₂ _) (by positivity)
      _ ≤ ((2 : ℝ) ^ (-j)) ^ 2 * max 1 (max C₁ C₂) :=
          mul_le_mul_of_nonneg_left hC₂le (by positivity)
      _ = max 1 (max C₁ C₂) * ((2 : ℝ) ^ (-j)) ^ 2 := mul_comm _ _

end Work.KMTAreas.A4
