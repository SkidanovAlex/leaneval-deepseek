import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Word
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.perBoxFWeight_square_arith` — the FS-parameter arithmetic used by the
refutation of `Work.BoseFixB1.perBoxFWeight_fWeight_le_square`

Companion computations of `FINDING_perBoxFWeight_fWeight_le_square_FALSE.md`.  All the
quantities below are at FS's own parameters `paramsAt μ a = fsParams (μa³)`
(`X = (μa³)^{1/323}`, `d = X⁶ = (μa³)^{6/323}`, `K_ℓ = X^{-3/2} = (μa³)^{-3/646}`,
`ℓ = sideAt μ a = K_ℓ(μa)^{-1/2}`), and are pure `rpow` algebra:

* `sideAt_eq_monomial`      : `ℓ = a·(μa³)^{-163/323}`;
* `paramsAt_d_eq`           : `d = (μa³)^{6/323}`;
* `sideAt_mul_d_eq`         : `ℓ·d = a·(μa³)^{-157/323}` (FS's small-box side `dℓ`);
* `mu_mul_ld_cube_eq`       : `μ·(ℓd)³ = (μa³)^{-148/323} → ∞` as `μa³ → 0+`;
* `mu_mul_ld_sq_eq`         : `μ·(ℓd)² = a⁻¹(μa³)^{9/323} → 0` as `μa³ → 0+`;
* `exists_diluteness_pow_ge` : for every `N` and every `ε > 0` there is `t₀ ∈ (0,ε]` with
  `N ≤ t^{-148/323}` for all `t ∈ (0,t₀]`.

The two limits are the numerical content of the refutation: the small box `B(u)` has side
`dℓ` and volume `V = (ℓd)³`, so `μV = μ(ℓd)³` is *unbounded* along the admissible
diluteness while `μ/(dℓ)² = μ(ℓd)^{-2}·(ℓ²/(ℓ²))`-type quantities are small.

(These are *not* the statement under refutation; the lemma file keeps its `sorry` verbatim
by the chapter's convention for refuted statements.)
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's box side at the admissible parameters, as a monomial in the diluteness:
`ℓ = sideAt μ a = a·(μa³)^{-163/323}`. -/
theorem sideAt_eq_monomial {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hμa : 0 < μ * a := by positivity
  have ha2 : (0 : ℝ) ≤ a ^ 2 := by positivity
  have h1 : (μ * a) ^ (-(1 / 2 : ℝ)) = a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) := by
    have h : μ * a ^ 3 = (μ * a) * a ^ 2 := by ring
    rw [h, Real.mul_rpow (le_of_lt hμa) ha2, ← Real.rpow_natCast a 2,
      ← Real.rpow_mul (le_of_lt ha), show (((2 : ℕ) : ℝ) * -(1 / 2)) = -1 by norm_num,
      Real.rpow_neg_one]
    field_simp
  simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
    Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [h1]
  rw [show (-(3 / 2 : ℝ)) / 323 = -(3 / 646) by norm_num]
  rw [show (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)))
      = a * ((μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a ^ 3) ^ (-(1 / 2 : ℝ))) by ring]
  rw [← Real.rpow_add ht, show (-(3 / 646 : ℝ)) + -(1 / 2) = -(163 / 323) by norm_num]

/-- FS's `d` at the admissible parameters: `d = (μa³)^{6/323}`. -/
theorem paramsAt_d_eq (μ a : ℝ) :
    (Work.BoseBox.paramsAt μ a).d = (μ * a ^ 3) ^ ((6 : ℝ) / 323) := by
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]

/-- FS's small-box side: `ℓ·d = a·(μa³)^{-157/323}`. -/
theorem sideAt_mul_d_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d
      = a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  rw [sideAt_eq_monomial hμ ha, paramsAt_d_eq,
    show a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) * (μ * a ^ 3) ^ ((6 : ℝ) / 323)
        = a * ((μ * a ^ 3) ^ (-(163 / 323 : ℝ)) * (μ * a ^ 3) ^ ((6 : ℝ) / 323)) by ring,
    ← Real.rpow_add ht, show (-(163 / 323 : ℝ)) + (6 : ℝ) / 323 = -(157 / 323) by norm_num]

/-- **The volume grows**: `μ·(ℓd)³ = (μa³)^{-148/323}`, which is unbounded as `μa³ → 0+`. -/
theorem mu_mul_ld_cube_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    μ * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 3
      = (μ * a ^ 3) ^ (-(148 / 323 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hpow : (((μ * a ^ 3) ^ (-(157 / 323 : ℝ))) ^ 3)
      = (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((μ * a ^ 3) ^ (-(157 / 323 : ℝ))) 3,
      ← Real.rpow_mul ht.le (-(157 / 323 : ℝ)) ((3 : ℕ) : ℝ)]
  have hsplit : (μ * a ^ 3) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ))
      = (μ * a ^ 3) ^ (1 : ℝ) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ)) := by
    rw [Real.rpow_one]
  rw [sideAt_mul_d_eq hμ ha, mul_pow, hpow,
    show μ * (a ^ 3 * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ)))
        = (μ * a ^ 3) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ)) by ring,
    hsplit, ← Real.rpow_add ht,
    show (1 : ℝ) + (-(157 / 323 : ℝ)) * ((3 : ℕ) : ℝ) = -(148 / 323) by norm_num]

/-- **The second moment is small**: `μ·(ℓd)² = a⁻¹(μa³)^{9/323} → 0` as `μa³ → 0+`. -/
theorem mu_mul_ld_sq_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    μ * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2
      = a⁻¹ * (μ * a ^ 3) ^ ((9 : ℝ) / 323) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hpow : (((μ * a ^ 3) ^ (-(157 / 323 : ℝ))) ^ 2)
      = (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((μ * a ^ 3) ^ (-(157 / 323 : ℝ))) 2,
      ← Real.rpow_mul ht.le (-(157 / 323 : ℝ)) ((2 : ℕ) : ℝ)]
  have hsplit : (μ * a ^ 3) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ))
      = (μ * a ^ 3) ^ (1 : ℝ) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ)) := by
    rw [Real.rpow_one]
  rw [sideAt_mul_d_eq hμ ha, mul_pow, hpow,
    show μ * (a ^ 2 * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ)))
        = a⁻¹ * ((μ * a ^ 3) * (μ * a ^ 3) ^ ((-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ))) by
      field_simp,
    hsplit, ← Real.rpow_add ht,
    show (1 : ℝ) + (-(157 / 323 : ℝ)) * ((2 : ℕ) : ℝ) = (9 : ℝ) / 323 by norm_num]

/-- **The unboundedness of `μ(ℓd)³` along the admissible diluteness.**  For every `N` and
every `ε > 0` there is `t₀ ∈ (0, ε]` such that for all `t ∈ (0, t₀]` the admissible
diluteness `t` satisfies `N ≤ t^{-148/323}` — i.e. `μ(ℓd)³ = (μa³)^{-148/323}` exceeds any
prescribed constant strictly inside the dilute regime. -/
theorem exists_diluteness_pow_ge {N ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ ε ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → N ≤ t ^ (-(148 / 323 : ℝ)) := by
  set M : ℝ := max N 1 + 1 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith [le_max_right N 1]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hNM : N ≤ M := by rw [hMdef]; linarith [le_max_left N 1]
  refine ⟨min ε (M ^ (-(323 / 148 : ℝ))), lt_min hε (Real.rpow_pos_of_pos hMpos _),
    min_le_left _ _, ?_⟩
  intro t ht0 hle
  have hle' : t ≤ M ^ (-(323 / 148 : ℝ)) := le_trans hle (min_le_right _ _)
  have hmono : (M ^ (-(323 / 148 : ℝ))) ^ (-(148 / 323 : ℝ)) ≤ t ^ (-(148 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht0 hle' (by norm_num)
  have hval : (M ^ (-(323 / 148 : ℝ))) ^ (-(148 / 323 : ℝ)) = M := by
    rw [← Real.rpow_mul hMpos.le,
      show (-(323 / 148 : ℝ)) * (-(148 / 323 : ℝ)) = 1 by norm_num, Real.rpow_one]
  rw [hval] at hmono
  exact le_trans hNM hmono

end Work.BoseFixB1
