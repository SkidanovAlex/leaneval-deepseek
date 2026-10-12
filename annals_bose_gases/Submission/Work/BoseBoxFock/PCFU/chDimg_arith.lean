import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chDimg_arith`

Pure arithmetic.  The constant prefactor produced by the `chDimg` norm bound,

`8·C·(1 + ℓ⁻³)·(1 + κ^{2M₀})·((κℓ)⁻¹)^{2M₀-3}·(μ·ℓ^{9/2})`,

is bounded by `K0 · a` uniformly over all admissible `(μ, κ, ℓ)` with
`ℓ = a·(μa³)^{-163/323}` and `κℓ = (μa³)^{-12/323}`.

Writing `t := μa³ ≤ ε₀` (`t > 0`), the two relations give `ℓ = a·t^{-163/323}` and `κℓ = t^{-12/323}`,
so that

`8C(1 + ℓ⁻³)(1 + κ^{2M₀})((κℓ)⁻¹)^{2M₀-3}μℓ^{9/2}
   = 8C·a^{3/2}·(1 + a⁻³t^{489/323})·(1 + a^{-2M₀}t^{302M₀/323})·t^{(48M₀-893)/646}`,

and every exponent of `t` occurring in the expansion is positive precisely because `M₀ ≥ 19` makes
`48M₀ - 893 ≥ 0`.  Each factor is therefore monotone increasing in `t > 0`, so the whole expression is
at most its value at `t = ε₀`, which is `K0·a` for

`K0 = 8C(1 + a⁻³ε₀^{489/323})(1 + a^{-2M₀}ε₀^{302M₀/323})ε₀^{(48M₀-893)/646}a^{1/2} + 1`.

The three exponent identities are established in the proof below (`hE1`, `hE2`, `hE3`) with
`Real.rpow_add` / `Real.rpow_mul` / `Real.rpow_neg` / `Real.mul_rpow` / `Real.div_rpow`.
-/

noncomputable section

namespace Work.BoseBoxFock.PCFU

set_option linter.unusedVariables false

/-- The constant of `chDimg_arith`. -/
noncomputable def chDimgK0 (M₀ : ℕ) (C a ε₀ : ℝ) : ℝ :=
  8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
    * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
    * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) * a ^ ((1 : ℝ) / 2) + 1

theorem chDimg_arith {M₀ : ℕ} (hM₀ : 19 ≤ M₀) {C a R ε₀ : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hR : 0 < R) (hε : 0 < ε₀) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ {μ κ ℓ : ℝ} (hμ : 0 < μ) (hμa : μ * a ^ 3 ≤ ε₀) (h2R : 2 * R ≤ ℓ)
      (hκℓ : κ * ℓ = (((μ * a ^ 3) ^ (6 / 323 : ℝ))⁻¹) ^ 2)
      (hℓ : ℓ = a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ)),
      8 * C * (1 + ℓ ^ (-3 : ℤ)) * (1 + κ ^ (2 * M₀)) * ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3)
        * (μ * ℓ ^ (9 / 2 : ℝ)) ≤ K0 * a := by
  refine ⟨chDimgK0 M₀ C a ε₀, ?_, ?_⟩
  · rw [chDimgK0]; positivity
  · intro μ κ ℓ hμ hμa h2R hκℓ hℓ
    have hμ3pos : 0 < μ * a ^ 3 := by positivity
    -- `κ * ℓ = (μa³)^{-12/323}`
    have hκℓ0 : κ * ℓ = (μ * a ^ 3) ^ (-(12 / 323) : ℝ) := by
      rw [hκℓ]
      rw [← Real.rpow_natCast]
      push_cast
      rw [← Real.rpow_neg (le_of_lt hμ3pos) (6 / 323)]
      rw [← Real.rpow_mul (le_of_lt hμ3pos) (-(6 / 323)) (2 : ℝ)]
      norm_num
    set t : ℝ := μ * a ^ 3 with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htle : t ≤ ε₀ := by rw [ht]; exact hμa
    have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
    have hκℓt : κ * ℓ = t ^ (-(12 / 323) : ℝ) := by rw [ht]; exact hκℓ0
    have hℓt : ℓ = a * t ^ (-(163 / 323) : ℝ) := by rw [ht]; exact hℓ
    have hκmℓ_pos : 0 < κ * ℓ := by rw [hκℓt]; positivity
    have hκpos : 0 < κ := by
      by_contra hcon
      rw [not_lt] at hcon
      have hle := mul_nonpos_of_nonpos_of_nonneg hcon hℓpos.le
      linarith
    -- **identity 1**: `ℓ^{-3} = a^{-3} t^{489/323}`
    have hE1 : ℓ ^ (-3 : ℤ) = a ^ (-3 : ℝ) * t ^ ((489 : ℝ) / 323) := by
      rw [hℓt, ← Real.rpow_intCast]
      push_cast
      rw [Real.mul_rpow ha.le (Real.rpow_nonneg htpos.le _)]
      rw [← Real.rpow_mul htpos.le]
      rw [show (-(163 / 323 : ℝ)) * (-3) = 489 / 323 by norm_num]
    -- **identity 2**: `κ^{2M₀} = a^{-2M₀} t^{302M₀/323}`
    have hE2 : κ ^ (2 * M₀) = a ^ (-(2 * M₀) : ℝ) * t ^ ((302 * M₀) / 323 : ℝ) := by
      have hκ : κ = t ^ (-(12 / 323) : ℝ) / ℓ := by
        rw [eq_div_iff (ne_of_gt hℓpos)]
        exact hκℓt
      rw [hκ, hℓt]
      rw [← Real.rpow_natCast]
      rw [Real.div_rpow (Real.rpow_nonneg htpos.le _) (by positivity)]
      rw [Real.mul_rpow (le_of_lt ha) (Real.rpow_nonneg htpos.le _)]
      rw [← Real.rpow_mul htpos.le, ← Real.rpow_mul htpos.le]
      rw [div_eq_mul_inv, mul_inv]
      rw [← Real.rpow_neg htpos.le ((-(163 / 323)) * ((2 * M₀ : ℕ) : ℝ))]
      rw [← Real.rpow_neg ha.le (((2 * M₀ : ℕ) : ℝ))]
      have hcomb : t ^ (-(12 / 323) * ((2 * M₀ : ℕ) : ℝ))
            * t ^ (-(-(163 / 323) * ((2 * M₀ : ℕ) : ℝ))) = t ^ ((302 * M₀) / 323 : ℝ) := by
        rw [← Real.rpow_add htpos]
        congr 1
        push_cast
        ring
      have hper : t ^ (-(12 / 323) * ((2 * M₀ : ℕ) : ℝ))
            * (a ^ (-((2 * M₀ : ℕ) : ℝ)) * t ^ (-(-(163 / 323) * ((2 * M₀ : ℕ) : ℝ))))
          = a ^ (-((2 * M₀ : ℕ) : ℝ)) * (t ^ (-(12 / 323) * ((2 * M₀ : ℕ) : ℝ))
            * t ^ (-(-(163 / 323) * ((2 * M₀ : ℕ) : ℝ)))) := by ring
      rw [hper, hcomb]
      congr 1
      push_cast
      ring
    -- **identity 3**: `((κℓ)⁻¹)^{2M₀-3}·μℓ^{9/2} = a^{3/2} t^{(48M₀-893)/646}`
    have hE3 : ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * (μ * ℓ ^ (9 / 2 : ℝ))
        = a ^ (3 / 2 : ℝ) * t ^ (((48 * M₀ - 893 : ℕ) : ℝ) / 646) := by
      have hm3 : (3 : ℕ) ≤ 2 * M₀ := by omega
      have h893 : (893 : ℕ) ≤ 48 * M₀ := by omega
      have hμt : μ = t / a ^ 3 := by rw [ht]; field_simp
      have hfirst : ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3)
          = t ^ (((12 : ℝ) / 323) * ((2 * M₀ - 3 : ℕ) : ℝ)) := by
        rw [hκℓt]
        rw [show (t ^ (-(12 / 323) : ℝ))⁻¹ = t ^ ((12 : ℝ) / 323) by
          rw [← Real.rpow_neg htpos.le (-(12 / 323) : ℝ)]
          congr 1
          ring]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul htpos.le ((12 : ℝ) / 323) ((2 * M₀ - 3 : ℕ) : ℝ)]
      have hsecond : μ * ℓ ^ (9 / 2 : ℝ) = a ^ ((3 : ℝ) / 2) * t ^ (-(821 / 646) : ℝ) := by
        rw [hμt, hℓt, div_eq_mul_inv]
        rw [← Real.rpow_natCast a 3, ← Real.rpow_neg ha.le ((3 : ℕ) : ℝ)]
        rw [Real.mul_rpow (le_of_lt ha) (Real.rpow_nonneg htpos.le _)]
        rw [← Real.rpow_mul htpos.le]
        have ha' : a ^ (-((3 : ℕ) : ℝ)) * a ^ ((9 : ℝ) / 2) = a ^ ((3 : ℝ) / 2) := by
          rw [← Real.rpow_add ha]; congr 1; norm_num
        have ht' : t ^ (1 : ℝ) * t ^ ((-(163 / 323)) * ((9 : ℝ) / 2))
            = t ^ (-(821 / 646) : ℝ) := by
          rw [← Real.rpow_add htpos]
          congr 1
          norm_num
        rw [show t * a ^ (-((3 : ℕ) : ℝ)) * (a ^ ((9 : ℝ) / 2) * t ^ ((-(163 / 323)) * ((9 : ℝ) / 2)))
              = (a ^ (-((3 : ℕ) : ℝ)) * a ^ ((9 : ℝ) / 2))
                * (t ^ (1 : ℝ) * t ^ ((-(163 / 323)) * ((9 : ℝ) / 2))) by
            rw [Real.rpow_one]; ring]
        rw [ha', ht']
      rw [hfirst, hsecond]
      have ht'' : t ^ (((12 : ℝ) / 323) * ((2 * M₀ - 3 : ℕ) : ℝ)) * t ^ (-(821 / 646) : ℝ)
          = t ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) := by
        rw [← Real.rpow_add htpos]
        congr 1
        rw [Nat.cast_sub hm3, Nat.cast_sub h893]
        push_cast
        ring
      rw [show t ^ (((12 : ℝ) / 323) * ((2 * M₀ - 3 : ℕ) : ℝ))
            * (a ^ ((3 : ℝ) / 2) * t ^ (-(821 / 646) : ℝ))
          = a ^ ((3 : ℝ) / 2)
            * (t ^ (((12 : ℝ) / 323) * ((2 * M₀ - 3 : ℕ) : ℝ)) * t ^ (-(821 / 646) : ℝ)) by ring]
      rw [ht'']
    -- comparison of each factor with its value at `t = ε₀`
    have hB2 : (1 + ℓ ^ (-3 : ℤ)) ≤ 1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323) := by
      rw [hE1]
      have h : t ^ ((489 : ℝ) / 323) ≤ ε₀ ^ ((489 : ℝ) / 323) :=
        Real.rpow_le_rpow htpos.le htle (by norm_num)
      have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha.le (-3 : ℝ))
      linarith
    have hB3 : (1 + κ ^ (2 * M₀))
        ≤ 1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ) := by
      rw [hE2]
      have h : t ^ ((302 * M₀) / 323 : ℝ) ≤ ε₀ ^ ((302 * M₀) / 323 : ℝ) :=
        Real.rpow_le_rpow htpos.le htle (by positivity)
      have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha.le (-(2 * M₀) : ℝ))
      linarith
    have hB4 : ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * (μ * ℓ ^ (9 / 2 : ℝ))
        ≤ a ^ ((3 : ℝ) / 2) * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) := by
      rw [hE3]
      have h : t ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646)
          ≤ ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) :=
        Real.rpow_le_rpow htpos.le htle (by exact div_nonneg (Nat.cast_nonneg _) (by norm_num))
      exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha.le ((3 : ℝ) / 2))
    have hDFnn : 0 ≤ ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * (μ * ℓ ^ (9 / 2 : ℝ)) := by
      apply mul_nonneg
      · exact pow_nonneg (inv_nonneg.mpr hκmℓ_pos.le) _
      · positivity
    -- multiply the three comparisons
    have hPD : 8 * C * (1 + ℓ ^ (-3 : ℤ)) * (1 + κ ^ (2 * M₀))
        ≤ 8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
          * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hB2 (by positivity)
      · exact hB3
      · positivity
      · positivity
    have hmul : 8 * C * (1 + ℓ ^ (-3 : ℤ)) * (1 + κ ^ (2 * M₀))
          * (((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * (μ * ℓ ^ (9 / 2 : ℝ)))
        ≤ 8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
          * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
          * (a ^ ((3 : ℝ) / 2) * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646)) :=
      mul_le_mul hPD hB4 hDFnn (by positivity)
    -- `a^{3/2} = a^{1/2}·a`
    have ha32 : a ^ ((3 : ℝ) / 2) = a ^ ((1 : ℝ) / 2) * a := by
      have h := Real.rpow_add ha ((1 : ℝ) / 2) (1 : ℝ)
      rw [Real.rpow_one] at h
      rw [show ((1 : ℝ) / 2 + 1) = (3 : ℝ) / 2 by norm_num] at h
      exact h
    have hfin : 8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
          * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
          * (a ^ ((3 : ℝ) / 2) * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646))
        ≤ chDimgK0 M₀ C a ε₀ * a := by
      rw [chDimgK0]
      calc 8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
            * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
            * (a ^ ((3 : ℝ) / 2) * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646))
          = (8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
            * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
            * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) * a ^ ((1 : ℝ) / 2)) * a := by
              rw [ha32]; ring
        _ ≤ (8 * C * (1 + a ^ (-3 : ℝ) * ε₀ ^ ((489 : ℝ) / 323))
            * (1 + a ^ (-(2 * M₀) : ℝ) * ε₀ ^ ((302 * M₀) / 323 : ℝ))
            * ε₀ ^ ((((48 * M₀ - 893 : ℕ) : ℝ)) / 646) * a ^ ((1 : ℝ) / 2) + 1) * a :=
              mul_le_mul_of_nonneg_right (by linarith) ha.le
    -- reassociate the goal's left-hand side and combine
    have hgoal : 8 * C * (1 + ℓ ^ (-3 : ℤ)) * (1 + κ ^ (2 * M₀)) * ((κ * ℓ)⁻¹) ^ (2 * M₀ - 3)
          * (μ * ℓ ^ (9 / 2 : ℝ))
        = 8 * C * (1 + ℓ ^ (-3 : ℤ)) * (1 + κ ^ (2 * M₀))
          * (((κ * ℓ)⁻¹) ^ (2 * M₀ - 3) * (μ * ℓ ^ (9 / 2 : ℝ))) := by
      rw [mul_assoc]
    exact le_trans (le_of_eq hgoal) (le_trans hmul hfin)

end Work.BoseBoxFock.PCFU
