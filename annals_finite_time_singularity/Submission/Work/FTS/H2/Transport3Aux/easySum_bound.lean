/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound of the "easy" (good) part of the `D_θ`-pairing

This file proves `Work.FTS.H2.Transport3Aux.easySum_bound`: there is a universal
constant `C > 0` such that for every `0 < α ≤ 1`, every `𝒲^{4,∞}` function `f` and
every `g`,

  `|EasySum α f g z θ| ≤ C · |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g z θ`   on `Iz × Iθ`.

`EasySum` (`GoodThetaDefs`) is the finite sum of the Leibniz summands `xD` and `yM` of
the flat `ℋ⁴`-pairing `(f D_θ g, g)_{ℋ⁴}` with the five "exceptional" summands — the
ones in which all four derivatives fall on `g` — removed.  In every remaining summand
one of the two following situations occurs:

* the factor coming from `f` is bounded pointwise by `|f|_{𝒲^{4,∞}}` up to a universal
  constant (`𝒲^{4,∞}`-bound of a `D_z`- or mixed `D`-derivative of order `≤ 4`), and
  the two factors coming from `g` are two genuine `HkIntegrand` blocks — a weighted
  mixed derivative `mixed j i g·W` with `i ≥ 1`, `i + j ≤ 4` and a weighted derivative
  `D_z^i g · w/√(sin 2θ)^η` with `i ≤ 4` (or two weighted mixed derivatives);
* the two factors coming from `g` are two blocks of the same type while the `f`-factor
  is paired against the second `g`-block.

The estimate is therefore a pointwise AM–GM (`2ab ≤ a² + b²`) applied to the two
`g`-blocks, together with the elementary weight comparison
`Whz² ≤ Wm · Whz` (i.e. `w² sin(2θ)^{-η} ≤ w² sin(2θ)^{-γ}` on `Iθ`, as `η < γ`).
The constant produced here is deliberately crude (`4806000`); nothing depends on its
size.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.Whz_Wm_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the weights and the norms -/

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_aux {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ

/-- The `η`-weight is nonnegative on the closed quadrant. -/
theorem whz_nonneg {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Whz z θ := by
  simp only [Whz]
  refine div_nonneg ?_ (Real.rpow_nonneg (sin_two_nonneg_aux hθ) _)
  simp only [Spaces.w]
  positivity

/-- The `γ`-weight is nonnegative on the closed quadrant. -/
theorem wm_nonneg (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Wm α z θ := by
  simp only [Wm, Spaces.Wt, Spaces.wTheta]
  refine mul_nonneg ?_ (Real.rpow_nonneg (sin_two_nonneg_aux hθ) _)
  simp only [Spaces.w]
  positivity

/-- On the closed quadrant the `η`-weight is dominated by the `γ`-weight: `Whz ≤ Wm`. -/
theorem whz_le_wm (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Whz z θ ≤ Wm α z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 ≤ Spaces.w z := by simp only [Spaces.w]; positivity
  have hle : Real.sin (2 * θ) ^ (-(Spaces.eta / 2))
      ≤ Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) := by
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, Real.zero_rpow (by intro h; have := Spaces.eta_pos; linarith),
        Real.zero_rpow (by intro h; have := Spaces.gam_pos hα; linarith)]
    · refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
      have h2 : Spaces.eta ≤ Spaces.gam α := by
        have h1 := Spaces.eta_lt_one
        have h3 := Spaces.one_lt_gam hα
        linarith
      linarith
  rw [Whz, Wm, Spaces.Wt, Spaces.wTheta, div_eq_mul_inv, ← Real.rpow_neg hs0 (Spaces.eta / 2)]
  exact mul_le_mul_of_nonneg_left hle hw

/-- `Whz² ≤ Whz · Wm` on the closed quadrant. -/
theorem whz_sq_le_wm_mul (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := by
  have h1 : Whz z θ ≤ Wm α z θ := whz_le_wm α hα hθ
  have h2 : 0 ≤ Whz z θ := whz_nonneg hθ
  nlinarith [h1, h2]

/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem wlInf_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.WlInfMem α 4 f) :
    0 ≤ Spaces.WlInf α 4 f := by
  rw [Spaces.WlInf]
  exact add_nonneg (Spaces.wlZSum_nonneg α 4 f hmem) (Spaces.wlThSum_nonneg α 4 f hmem)

/-- The angular weight of the mixed part is at most `2` on `Iθ` for `0 < α ≤ 1`. -/
theorem phi_le_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hp0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs0 _
  have hp1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by positivity)
  have ha : α + Real.sin (2 * θ) ≤ 2 := by linarith
  calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 * 1 :=
        mul_le_mul ha hp1 hp0 (by norm_num)
    _ = 2 := by norm_num

/-- `n.choose k ≤ 16` for `k ≤ n ≤ 4`. -/
theorem choose_le_sixteen {n k : ℕ} (hn : n ≤ 4) : (n.choose k : ℝ) ≤ 16 := by
  have h1 : ((n.choose k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_le_two_pow n k
  have h2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hn
  have h4 : (2 : ℝ) ^ 4 = 16 := by norm_num
  linarith

/-! ## Pointwise bounds for the `f`-factors, in terms of `|f|_{𝒲^{4,∞}}` -/

/-- `|D_z^b f| ≤ 15 |f|_𝒲` for `b ≤ 4`. -/
theorem abs_dzIter_le_wlInf (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hsmf : Spaces.SmoothNbhd f)
    (hfm : Spaces.WlInfMem α 4 f) {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : z ∈ Spaces.Iz)
    (hθ : θ ∈ Spaces.Iθ) :
    |Spaces.DzIter b f z θ| ≤ 15 * Spaces.WlInf α 4 f :=
  Spaces.DzIter_le_WlInf hα (Spaces.SmoothInt.of_SmoothNbhd hsmf) hfm (b := b) hb hz hθ

/-- `|D_z^b D_θ^a f| ≤ 30 |f|_𝒲` for `1 ≤ a`, `a + b ≤ 4`. -/
theorem abs_mixed_le_wlInf (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsmf : Spaces.SmoothNbhd f) (hfm : Spaces.WlInfMem α 4 f) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a + b ≤ 4) {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    |Spaces.mixed b a f z θ| ≤ 30 * Spaces.WlInf α 4 f := by
  have h := Spaces.mixed_le_WlInf hα (Spaces.SmoothInt.of_SmoothNbhd hsmf) hfm (a := a) (b := b)
    ha hab hz hθ
  have hW0 : 0 ≤ Spaces.WlInf α 4 f := wlInf_nonneg α f hfm
  have hphi := phi_le_two α hα hα1 hθ
  calc |Spaces.mixed b a f z θ|
      ≤ 15 * (Spaces.WlInf α 4 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := h
    _ ≤ 15 * (Spaces.WlInf α 4 f * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hphi hW0) (by norm_num)
    _ = 30 * Spaces.WlInf α 4 f := by ring

/-! ## The AM–GM slot bound -/

/-- If `a² ≤ H` and `b² ≤ H` with `a, b ≥ 0` then `a b ≤ H`. -/
theorem mul_self_le_of_sq_le {a b H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ^ 2 ≤ H)
    (hb2 : b ^ 2 ≤ H) : a * b ≤ H := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-- A `range (n+1)`-sum, `n ≤ 4`, of terms bounded by `c ≥ 0` is at most `5 c`. -/
theorem sum_range_succ_le {n : ℕ} (hn : n ≤ 4) {φ : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ Finset.range (n + 1), φ i ≤ c) :
    ∑ i ∈ Finset.range (n + 1), φ i ≤ 5 * c := by
  have h1 : (∑ i ∈ Finset.range (n + 1), φ i) ≤ ∑ i ∈ Finset.range (n + 1), c :=
    Finset.sum_le_sum h
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (by omega : n + 1 ≤ 5)
  exact mul_le_mul_of_nonneg_right h2 hc

/-! ## The absolute-value forms of the Leibniz summands -/

/-- `|xD|` is bounded by the binomial coefficient times its factored form. -/
theorem abs_xD_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (i b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    |xD f g i b z θ| ≤ (i.choose b : ℝ) * (|Spaces.DzIter b f z θ| *
      (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) * (|Spaces.DzIter i g z θ| * Whz z θ)) := by
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hW : (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := whz_sq_le_wm_mul α hα hθ
  have hXYZ : 0 ≤ |Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
      * |Spaces.DzIter i g z θ| := by positivity
  simp only [xD, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  calc (i.choose b : ℝ) * (|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
        * |Spaces.DzIter i g z θ| * Whz z θ ^ 2)
      = (i.choose b : ℝ) * ((|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
          * |Spaces.DzIter i g z θ|) * Whz z θ ^ 2) := by ring
    _ ≤ (i.choose b : ℝ) * ((|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
          * |Spaces.DzIter i g z θ|) * (Wm α z θ * Whz z θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hXYZ) hch
    _ = (i.choose b : ℝ) * (|Spaces.DzIter b f z θ|
          * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) * (|Spaces.DzIter i g z θ| * Whz z θ)) := by
        ring

/-- `|yM|` is bounded by the product of the binomial coefficients times its factored form. -/
theorem abs_yM_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    |yM α f g i j a b z θ| ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
      (|Spaces.mixed b a f z θ| * (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)) := by
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  simp only [yM, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  exact le_of_eq (by ring)

/-! ## The pointwise bound of the individual summands -/

/-- The `D_z`-slot summands `xD` are bounded by `240 |f|_𝒲 · HkIntegrand α 4 g`. -/
theorem xD_bound (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hsmf : Spaces.SmoothNbhd f)
    (hfm : Spaces.WlInfMem α 4 f) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i)
    (hne : ¬(i = 4 ∧ b = 0)) {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    |xD f g i b z θ| ≤ 240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by
  have hW0 : 0 ≤ Spaces.WlInf α 4 f := wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Spaces.HkIntegrand α 4 g z θ := Spaces.HkIntegrand_nonneg α 4 g z θ
  have hWH : 0 ≤ Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ := mul_nonneg hW0 hH0
  -- the order of the mixed `g`-factor
  have hmb : 1 + (i - b) ≤ 4 := by
    by_contra hc
    push_neg at hc
    have hb0 : b = 0 := by omega
    have hi4 : i = 4 := by omega
    exact hne ⟨hi4, hb0⟩
  have hF : |Spaces.DzIter b f z θ| ≤ 15 * Spaces.WlInf α 4 f :=
    abs_dzIter_le_wlInf α hα hsmf hfm (by omega) hz hθ
  have hsqA : (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) ^ 2
      ≤ Spaces.HkIntegrand α 4 g z θ := by
    have h := Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 (i - b) (le_refl 1) hmb
    simpa only [mul_pow, sq_abs, Wm, Spaces.Wt] using h
  have hsqB : (|Spaces.DzIter i g z θ| * Whz z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 g z θ := by
    have h := Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi
    simpa only [mul_pow, sq_abs, Whz] using h
  have hAB : (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Spaces.DzIter i g z θ| * Whz z θ) ≤ Spaces.HkIntegrand α 4 g z θ :=
    mul_self_le_of_sq_le (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
      (mul_nonneg (abs_nonneg _) (whz_nonneg hθ)) hsqA hsqB
  have hstep : |Spaces.DzIter b f z θ|
        * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Spaces.DzIter i g z θ| * Whz z θ)
      ≤ (15 * Spaces.WlInf α 4 f) * Spaces.HkIntegrand α 4 g z θ := by
    have hnn : 0 ≤ (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Spaces.DzIter i g z θ| * Whz z θ) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
        (mul_nonneg (abs_nonneg _) (whz_nonneg hθ))
    calc |Spaces.DzIter b f z θ| * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Spaces.DzIter i g z θ| * Whz z θ)
        = |Spaces.DzIter b f z θ| * ((|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
            * (|Spaces.DzIter i g z θ| * Whz z θ)) := by ring
      _ ≤ (15 * Spaces.WlInf α 4 f) * ((|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
            * (|Spaces.DzIter i g z θ| * Whz z θ)) := mul_le_mul_of_nonneg_right hF hnn
      _ ≤ (15 * Spaces.WlInf α 4 f) * Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul_of_nonneg_left hAB (by linarith)
  have hcoef : (i.choose b : ℝ) ≤ 16 := choose_le_sixteen (n := i) (k := b) hi
  have hnn : 0 ≤ |Spaces.DzIter b f z θ| * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ)))
      (mul_nonneg (abs_nonneg _) (whz_nonneg hθ))
  calc |xD f g i b z θ|
      ≤ (i.choose b : ℝ) * (|Spaces.DzIter b f z θ|
          * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Spaces.DzIter i g z θ| * Whz z θ)) := abs_xD_le α hα f g i b hθ
    _ ≤ 16 * ((15 * Spaces.WlInf α 4 f) * Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul hcoef hstep hnn (by norm_num)
    _ = 240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by ring

/-- The mixed-slot summands `yM` are bounded by `7680 |f|_𝒲 · HkIntegrand α 4 g`. -/
theorem yM_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hsmf : Spaces.SmoothNbhd f) (hfm : Spaces.WlInfMem α 4 f) (i j a b : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j) (hne : ¬(a = 0 ∧ b = 0 ∧ i + j = 4))
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    |yM α f g i j a b z θ| ≤ 7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by
  have hW0 : 0 ≤ Spaces.WlInf α 4 f := wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Spaces.HkIntegrand α 4 g z θ := Spaces.HkIntegrand_nonneg α 4 g z θ
  -- the order of the first mixed `g`-factor
  have hord : (i - a + 1) + (j - b) ≤ 4 := by
    have hle : a + b ≤ i + j := by omega
    by_cases hab : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hij3 : i + j ≤ 3 := by
        by_contra hc
        exact hne ⟨ha0, hb0, by omega⟩
      omega
    · omega
  -- the `f`-factor
  have hF : |Spaces.mixed b a f z θ| ≤ 30 * Spaces.WlInf α 4 f := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      rw [Spaces.mixed_zero_right]
      have h := abs_dzIter_le_wlInf α hα hsmf hfm (b := b) (by omega) hz hθ
      linarith
    · exact abs_mixed_le_wlInf α hα hα1 hsmf hfm hapos (by omega) hz hθ
  -- the two `g`-slots
  have hsqA : (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ) ^ 2
      ≤ Spaces.HkIntegrand α 4 g z θ := by
    have h := Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (i - a + 1) (j - b) (by omega) hord
    simpa only [mul_pow, sq_abs, Wm, Spaces.Wt] using h
  have hsqB : (|Spaces.mixed j i g z θ| * Wm α z θ) ^ 2
      ≤ Spaces.HkIntegrand α 4 g z θ := by
    have h := Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij
    simpa only [mul_pow, sq_abs, Wm, Spaces.Wt] using h
  have hAB : (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
      * (|Spaces.mixed j i g z θ| * Wm α z θ) ≤ Spaces.HkIntegrand α 4 g z θ :=
    mul_self_le_of_sq_le (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
      (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ)) hsqA hsqB
  have hstep : |Spaces.mixed b a f z θ|
        * ((|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Spaces.mixed j i g z θ| * Wm α z θ))
      ≤ (30 * Spaces.WlInf α 4 f) * Spaces.HkIntegrand α 4 g z θ := by
    have hnn : 0 ≤ (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
        (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
    exact le_trans (mul_le_mul_of_nonneg_right hF hnn)
      (mul_le_mul_of_nonneg_left hAB (by linarith))
  have hcoef : ((i.choose a : ℝ) * (j.choose b : ℝ)) ≤ 256 := by
    have h1 : (i.choose a : ℝ) ≤ 16 := choose_le_sixteen (n := i) (k := a) (by omega)
    have h2 : (j.choose b : ℝ) ≤ 16 := choose_le_sixteen (n := j) (k := b) (by omega)
    have h3 : (0 : ℝ) ≤ (i.choose a : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ (j.choose b : ℝ) := by positivity
    nlinarith [h1, h2, h3, h4]
  have hnn : 0 ≤ |Spaces.mixed b a f z θ|
      * ((|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)) :=
    mul_nonneg (abs_nonneg _)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ))
        (mul_nonneg (abs_nonneg _) (wm_nonneg α hθ)))
  calc |yM α f g i j a b z θ|
      ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Spaces.mixed b a f z θ|
            * ((|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
              * (|Spaces.mixed j i g z θ| * Wm α z θ))) := by
        simpa only [mul_assoc] using abs_yM_le α f g i j a b hθ
    _ ≤ 256 * ((30 * Spaces.WlInf α 4 f) * Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul hcoef hstep hnn (by norm_num)
    _ = 7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by ring

/-! ## The assembly -/

/-- The pointwise bound of `EasySum` at the explicit constant `4806000`. -/
theorem easySum_bound_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hfm : Spaces.WlInfMem α 4 f) {z : ℝ} (hz : z ∈ Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    |EasySum α f g z θ|
      ≤ 4806000 * Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ := by
  have hW0 : 0 ≤ Spaces.WlInf α 4 f := wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Spaces.HkIntegrand α 4 g z θ := Spaces.HkIntegrand_nonneg α 4 g z θ
  have hWH : 0 ≤ Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ := mul_nonneg hW0 hH0
  have h240 : 0 ≤ 240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (by norm_num) hWH
  have h7680 : 0 ≤ 7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (by norm_num) hWH
  have h1200 : 0 ≤ 5 * (240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)) :=
    mul_nonneg (by norm_num) h240
  have h38400 : 0 ≤ 5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)) :=
    mul_nonneg (by norm_num) h7680
  have h96000 : 0 ≤ 5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ))) :=
    mul_nonneg (by norm_num) h38400
  have h480000 : 0 ≤ 5 * (5 * (5 * (7680 * (Spaces.WlInf α 4 f
      * Spaces.HkIntegrand α 4 g z θ)))) :=
    mul_nonneg (by norm_num) h96000
  -- Step 1: the triangle inequality, term by term
  have hstep1 : |EasySum α f g z θ| ≤ EasyMajor α f g z θ := by
    rw [EasySum, EasyMajor]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro i _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro b _
      by_cases hc : i = 4 ∧ b = 0
      · rw [if_pos hc, if_pos hc]; simp
      · rw [if_neg hc, if_neg hc]
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro i _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro j _
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc, if_pos hc]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro a _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro b _
        by_cases hc2 : a = 0 ∧ b = 0 ∧ i + j = 4
        · rw [if_pos hc2, if_pos hc2]; simp
        · rw [if_neg hc2, if_neg hc2]
      · rw [if_neg hc, if_neg hc]; simp
  -- Step 2: the `D_z`-slot sum
  have hS1 : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
      (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
      ≤ 6000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by
    have hb : ∀ i : ℕ, i ≤ 4 → (∑ b ∈ Finset.range (i + 1),
        (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)) := by
      intro i hi4
      refine sum_range_succ_le hi4 h240 ?_
      intro b hb'
      have hbi : b ≤ i := by have := Finset.mem_range.mp hb'; omega
      by_cases hc : i = 4 ∧ b = 0
      · rw [if_pos hc]; exact h240
      · rw [if_neg hc]
        exact xD_bound α hα hsmf hfm i b hi4 hbi hc hz hθ
    have hpt : ∀ i ∈ Finset.range 5, (∑ b ∈ Finset.range (i + 1),
        (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)) :=
      fun i hi' => hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))
    have h1 := sum_range_succ_le (n := 4) (by norm_num) h1200 hpt
    calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (5 * (240 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ))) := h1
      _ = 6000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by ring
  -- Step 3: the mixed-slot sum
  have hS2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
        else 0))
      ≤ 4800000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by
    -- the innermost sum, over `b`, for fixed `i`, `j`, `a`
    have hb : ∀ (i j a : ℕ), i ≤ 4 → j ≤ 4 → 1 ≤ i → i + j ≤ 4 → a ≤ i →
        (∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|))
          ≤ 5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)) := by
      intro i j a hi4 hj4 hi1 hij hai
      refine sum_range_succ_le hj4 h7680 ?_
      intro b hb'
      have hbj : b ≤ j := by have := Finset.mem_range.mp hb'; omega
      by_cases hc : a = 0 ∧ b = 0 ∧ i + j = 4
      · rw [if_pos hc]; exact h7680
      · rw [if_neg hc]
        exact yM_bound α hα hα1 hsmf hfm i j a b hi1 hij hai hbj hc hz hθ
    -- the sum over `a`
    have ha : ∀ (i j : ℕ), i ≤ 4 → j ≤ 4 → 1 ≤ i → i + j ≤ 4 →
        (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|))
          ≤ 5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ))) := by
      intro i j hi4 hj4 hi1 hij
      exact sum_range_succ_le (n := i) hi4 h38400
        (fun a ha' => hb i j a hi4 hj4 hi1 hij (by have := Finset.mem_range.mp ha'; omega))
    -- the sum over `j`
    have hj : ∀ i : ℕ, i ≤ 4 →
        (∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
          ≤ 5 * (5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)))) := by
      intro i hi4
      have hpt : ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0)
          ≤ 5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ))) := by
        intro j hj'
        have hj4 : j ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hj')
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · rw [if_pos hc]
          exact ha i j hi4 hj4 hc.1 hc.2
        · rw [if_neg hc]
          exact h96000
      exact sum_range_succ_le (n := 4) (by norm_num) h96000 hpt
    -- the sum over `i`
    have hpt : ∀ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
        ≤ 5 * (5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)))) :=
      fun i hi' => hj i (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))
    have h1 := sum_range_succ_le (n := 4) (by norm_num) h480000 hpt
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
        ≤ 5 * (5 * (5 * (5 * (7680 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ))))) :=
          h1
      _ = 4800000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by ring
  have hMajor : EasyMajor α f g z θ
      ≤ 6000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)
        + 4800000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := by
    rw [EasyMajor]
    exact add_le_add hS1 hS2
  calc |EasySum α f g z θ| ≤ EasyMajor α f g z θ := hstep1
    _ ≤ 6000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ)
          + 4800000 * (Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ) := hMajor
    _ = 4806000 * Spaces.WlInf α 4 f * Spaces.HkIntegrand α 4 g z θ := by ring

theorem easySum_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd f → Work.Spaces.WlInfMem α 4 f →
    Work.Spaces.SmoothNbhd g → Work.Spaces.DecayAll 4 g → Work.Spaces.HkMem α 4 g →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.H2.Transport3Aux.EasySum α f g z θ|
        ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨4806000, by norm_num, ?_⟩
  intro α f g hα hα1 hsmf hfm _hsmg _hdg _hgm z hz θ hθ
  exact easySum_bound_aux α hα hα1 f g hsmf hfm hz hθ

end Work.FTS.H2.Transport3Aux
