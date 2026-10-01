/-
# ZeroFreeTables — XY/XySupInterp

**Interpolation of the sup-estimates of the order-2 `λ₁`-estimate.**

The two `lam`-dependent profiles of `XYDefs`,

  `xySup1 lam t = 14900·ReΦ(1,t) − 30480·ReΦ(1−lam,t)`,
  `xySup2 lam t =  1250·ReΦ(1,t) −  6000·ReΦ(1−lam,t)`,

are smooth in both `t` and `lam` (they are oscillatory Laplace transforms of the polynomial
test function `xyP` of HB Lemma 7.2 with `λ = 4/3`), and this file turns that smoothness
into the two interpolation estimates needed to reduce the certified sup-bounds
(`XY.SupBoundOrderTwo`) to finitely many grid points:

* in `t`: on `[c, c+h]` the profile stays below its chord by at most `h²·M/8`, with the
  second-derivative bounds `M = 13970` (`xySup1`) and `M = 4258` (`xySup2`);
* in `lam`: on `[a,b]` with `b - a ≤ 37/1000` the profile is bounded by the larger of its two
  endpoint values plus `11/5`, uniformly in `t` — so the four grid values
  `518, 555, 592, 628 / 1000` control the whole range `[518/1000, 628/1000]`.

## Proof

Everything is read off from the single-integral representation
`xySup1 lam t = ∫_0^{3/2} cos (t·u) · W₁(lam,u) du` (and likewise for `xySup2`), where
`W₁(lam,u) = (14900·e^u − 30480·e^{(1−lam)u})·xyP u`.  On the one hand the chord identity
(`chord_integral_identity`) writes the difference between the profile and its chord as the
integral of the difference of the integrands; on the other hand the pointwise chord error is
controlled by `LagrangeLinInterp` (applied to `y ↦ cos (y·u)` and to `y ↦ e^{(1−y)u}`) and the
integrand by the elementary bounds `e^{3/2} ≤ 9/2`, `e^{0.723} ≤ 207/100` and
`∫_0^{3/2} u²·xyP u = 1/5`.

The numerical constants are therefore the products of those three inputs, with

  `67050·(1/5) = 13410 ≤ 13970`, `12420·(1/5) = 2484 ≤ 4258`  (the `t`-direction), and
  `30480·(37/1000)²/8·(207/100)·(1/5) ≤ 11/5`, `6000·(37/1000)²/8·(207/100)·(1/5) ≤ 11/5`
  (the `lam`-direction).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.XY.xyMainLt

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- Transport a `HasDerivAt` statement across a pointwise identity of functions and a
rewriting of the derivative value.  (Mathlib's function-level combinators `HasDerivAt.add`,
`.sub`, `.mul` produce statements whose type-class arguments are not definitionally the ones
elaborated for a bare lambda; transporting through this lemma realigns them.) -/
lemma hasDerivAt_congr' {f g : ℝ → ℝ} {f' g' x : ℝ} (h : HasDerivAt f f' x) (hf : f = g)
    (hf' : f' = g') : HasDerivAt g g' x := by
  rw [hf, hf'] at h
  exact h

/-! ## §0  Lagrange's form of the linear-interpolation error -/

/-- **Lagrange's form of the linear-interpolation error.**  A function that is twice
differentiable on `[a,b]`, with second derivative bounded by `M`, stays within `(b-a)²M/8`
of its chord on `[a,b]`.  (An independent copy of the general fact; the sibling file
`XY.LagrangeLinInterp` states the same lemma.)

Proof (Rolle).  For `x ∈ (a,b)` put `g y = f y - L y - K·(y-a)·(y-b)` with `L` the chord and
`K` chosen so that `g x = 0`.  Then `g a = g x = g b = 0`; two Rolle applications give
`c₁ ∈ (a,x)`, `c₂ ∈ (x,b)` with `g' c₁ = g' c₂ = 0`; a third gives `c ∈ (c₁,c₂)` with
`g'' c = 0`, i.e. `f'' c = 2K`.  Hence `|K| ≤ M/2` and
`|f x - L x| = |K|·(x-a)·(b-x) ≤ (M/2)·(b-a)²/4`. -/
theorem linInterpAux (f f' f'' : ℝ → ℝ) (M a b x : ℝ) (hab : a < b)
    (hx : x ∈ Set.Icc a b)
    (h1 : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (h2 : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (h3 : ∀ y ∈ Set.Icc a b, |f'' y| ≤ M) :
    |f x - ((b - x)/(b - a) * f a + (x - a)/(b - a) * f b)| ≤ (b - a)^2/8 * M := by
  obtain ⟨hxa, hxb⟩ := hx
  have hM : 0 ≤ M := le_trans (abs_nonneg (f'' a)) (h3 a ⟨le_refl a, le_of_lt hab⟩)
  have hba : b - a ≠ 0 := by linarith
  rcases eq_or_lt_of_le hxa with hxaeq | hax
  · rw [← hxaeq, div_self hba]
    have hz : f a - (1 * f a + (a - a) / (b - a) * f b) = 0 := by ring
    rw [hz, abs_zero]
    exact mul_nonneg (by positivity) hM
  rcases eq_or_lt_of_le hxb with hxbeq | hxb'
  · rw [hxbeq, div_self hba]
    have hz : f b - ((b - b) / (b - a) * f a + 1 * f b) = 0 := by ring
    rw [hz, abs_zero]
    exact mul_nonneg (by positivity) hM
  -- main case `a < x < b`
  have hLderiv : ∀ y : ℝ,
      HasDerivAt (fun t : ℝ => (b - t)/(b - a) * f a + (t - a)/(b - a) * f b)
        ((f b - f a)/(b - a)) y := by
    intro y
    have hA : HasDerivAt (fun t : ℝ => (b - t)/(b - a)) ((-1:ℝ)/(b - a)) y := by
      have := ((hasDerivAt_const (x := y) b).sub (hasDerivAt_id y)).div_const (b - a)
      simpa using this
    have hB : HasDerivAt (fun t : ℝ => (t - a)/(b - a)) ((1:ℝ)/(b - a)) y := by
      have := ((hasDerivAt_id y).sub_const a).div_const (b - a)
      simpa using this
    have h := (hA.mul_const (f a)).add (hB.mul_const (f b))
    have hval : (-1:ℝ)/(b - a) * f a + (1:ℝ)/(b - a) * f b = (f b - f a)/(b - a) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hval] at h
    exact h
  have hqderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (t - a) * (t - b)) (2*y - a - b) y := by
    intro y
    have h := ((hasDerivAt_id y).sub_const a).mul ((hasDerivAt_id y).sub_const b)
    exact hasDerivAt_congr' h (by funext t; rfl) (by simp only [id_eq]; ring)
  set K : ℝ := (f x - ((b - x)/(b - a) * f a + (x - a)/(b - a) * f b)) / ((x - a) * (x - b))
    with hK
  have hqa : x - a ≠ 0 := by linarith
  have hqb : x - b ≠ 0 := by linarith
  have hqx : (x - a) * (x - b) ≠ 0 := mul_ne_zero hqa hqb
  set g : ℝ → ℝ :=
    fun y => (f y - ((b - y)/(b - a) * f a + (y - a)/(b - a) * f b)) - K * ((y - a) * (y - b))
    with hg
  set g' : ℝ → ℝ := fun y => (f' y - (f b - f a)/(b - a)) - K * (2*y - a - b) with hg'
  set g'' : ℝ → ℝ := fun y => f'' y - K * 2 with hg''
  have hga : g a = 0 := by
    rw [hg]
    simp only []
    rw [div_self hba]
    ring
  have hgb : g b = 0 := by
    rw [hg]
    simp only []
    rw [div_self hba]
    ring
  have hgx : g x = 0 := by
    rw [hg, hK]
    simp only []
    rw [div_mul_cancel₀ _ hqx]
    ring
  have hgderiv : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y := by
    intro y hy
    have hfy := h1 y hy
    have hLy := hLderiv y
    have hqy := hqderiv y
    have h := (hfy.sub hLy).sub (hqy.const_mul K)
    rw [hg, hg']
    exact h
  have hg'deriv : ∀ y ∈ Set.Icc a b, HasDerivAt g' (g'' y) y := by
    intro y hy
    have hfy := h2 y hy
    have hlin : HasDerivAt (fun t : ℝ => 2*t - a - b) 2 y := by
      have := ((hasDerivAt_id y).const_mul 2).sub_const (a + b)
      simpa using this
    have h := (hfy.sub_const ((f b - f a)/(b - a))).sub (hlin.const_mul K)
    exact hasDerivAt_congr' h (by rw [hg']; funext t; rfl) (by rw [hg''])
  have hgcont : ContinuousOn g (Set.Icc a b) :=
    fun y hy => (hgderiv y hy).continuousAt.continuousWithinAt
  have hg'cont : ContinuousOn g' (Set.Icc a b) :=
    fun y hy => (hg'deriv y hy).continuousAt.continuousWithinAt
  have hsub1 : Set.Icc a x ⊆ Set.Icc a b := fun y hy => ⟨hy.1, le_trans hy.2 (le_of_lt hxb')⟩
  have hsub2 : Set.Icc x b ⊆ Set.Icc a b := fun y hy => ⟨le_trans (le_of_lt hax) hy.1, hy.2⟩
  obtain ⟨c1, hc1, hc1z⟩ := exists_hasDerivAt_eq_zero hax (hgcont.mono hsub1)
    (by rw [hga, hgx]) (fun y hy => hgderiv y (hsub1 (Set.Ioo_subset_Icc_self hy)))
  obtain ⟨c2, hc2, hc2z⟩ := exists_hasDerivAt_eq_zero hxb' (hgcont.mono hsub2)
    (by rw [hgx, hgb]) (fun y hy => hgderiv y (hsub2 (Set.Ioo_subset_Icc_self hy)))
  have hc12 : c1 < c2 := lt_trans hc1.2 hc2.1
  have hsub12 : Set.Icc c1 c2 ⊆ Set.Icc a b :=
    fun y hy => ⟨le_trans (le_of_lt hc1.1) hy.1, le_trans hy.2 (le_of_lt hc2.2)⟩
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hc12 (hg'cont.mono hsub12)
    (by rw [hc1z, hc2z]) (fun y hy => hg'deriv y (hsub12 (Set.Ioo_subset_Icc_self hy)))
  have hcIcc : c ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hc1.1 hc.1), le_of_lt (lt_trans hc.2 hc2.2)⟩
  have hKc : f'' c = 2 * K := by
    have h := hcz
    rw [hg''] at h
    linarith
  have hKbound : |K| ≤ M / 2 := by
    have h := h3 c hcIcc
    rw [hKc, abs_mul, show |(2:ℝ)| = 2 by norm_num] at h
    linarith
  have hKq : K * ((x - a) * (x - b))
      = f x - ((b - x)/(b - a) * f a + (x - a)/(b - a) * f b) := by
    rw [hK]
    exact div_mul_cancel₀ _ hqx
  have hfinal : |f x - ((b - x)/(b - a) * f a + (x - a)/(b - a) * f b)|
      = |K| * ((x - a) * (b - x)) := by
    rw [← hKq, abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hax), abs_of_neg (sub_neg.mpr hxb')]
    ring
  rw [hfinal]
  have hxab : (0:ℝ) ≤ (x - a) * (b - x) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hax)) (sub_nonneg.mpr (le_of_lt hxb'))
  have hM2 : (0:ℝ) ≤ M / 2 := by linarith
  calc |K| * ((x - a) * (b - x))
      ≤ (M/2) * ((x - a) * (b - x)) := mul_le_mul_of_nonneg_right hKbound hxab
    _ ≤ (M/2) * ((b - a)^2/4) := by
        refine mul_le_mul_of_nonneg_left ?_ hM2
        nlinarith [sq_nonneg (2*x - a - b)]
    _ = (b - a)^2/8 * M := by ring

/-! ## §1  weights, continuity, numerics -/

/-- The `lam`-dependent weight of `xySup1`. -/
def xyW1 (lam u : ℝ) : ℝ := (14900*Real.exp u - 30480*Real.exp ((1-lam)*u)) * xyP u

/-- The `lam`-dependent weight of `xySup2`. -/
def xyW2 (lam u : ℝ) : ℝ := (1250*Real.exp u - 6000*Real.exp ((1-lam)*u)) * xyP u

lemma cont_xyW1 (lam : ℝ) : Continuous (xyW1 lam) := by
  unfold xyW1 xyP; fun_prop

lemma cont_xyW2 (lam : ℝ) : Continuous (xyW2 lam) := by
  unfold xyW2 xyP; fun_prop

lemma cont_cos_mul_W1 (lam z : ℝ) : Continuous (fun u : ℝ => Real.cos (z*u) * xyW1 lam u) := by
  have h := cont_xyW1 lam; fun_prop

lemma cont_cos_mul_W2 (lam z : ℝ) : Continuous (fun u : ℝ => Real.cos (z*u) * xyW2 lam u) := by
  have h := cont_xyW2 lam; fun_prop

lemma abs_sub_le_max_of_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ max a b := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith), max_eq_left h]; linarith
  · rw [abs_of_nonpos (by linarith), max_eq_right h]; linarith

lemma exp_three_halves_le : Real.exp (3/2 : ℝ) ≤ 9/2 := by
  have h := exp_le_taylor13 (3/2) (by norm_num) (by norm_num)
  norm_num at h
  linarith

lemma exp_723_le : Real.exp ((723:ℝ)/1000) ≤ 207/100 := by
  have h := exp_le_taylor13 ((723:ℝ)/1000) (by norm_num) (by norm_num)
  norm_num at h
  linarith

lemma xyP_moment_two : ∫ u in (0:ℝ)..(3/2), u^2 * xyP u = 1/5 := by
  rw [xyP_moment 2]
  norm_num [xyM]

/-- Pointwise bound for the weight of `xySup1`. -/
lemma xyW1_bound (lam u : ℝ) (hlam1 : 518/1000 ≤ lam) (hu : u ∈ Set.Icc (0:ℝ) (3/2)) :
    |xyW1 lam u| ≤ 67050 * xyP u := by
  have h0 : 0 ≤ u := hu.1
  have h1 : u ≤ 3/2 := hu.2
  have hP : 0 ≤ xyP u := xyP_nonneg u h0 h1
  have hA : 14900 * Real.exp u ≤ 67050 := by
    have h := Real.exp_le_exp.mpr h1
    have h2 := mul_le_mul_of_nonneg_left (le_trans h exp_three_halves_le) (by norm_num : (0:ℝ) ≤ 14900)
    linarith
  have hB : 30480 * Real.exp ((1-lam)*u) ≤ 67050 := by
    have h1' : 1 - lam ≤ 482/1000 := by linarith
    have hle : (1-lam)*u ≤ (723:ℝ)/1000 := by
      calc (1-lam)*u ≤ (482/1000)*u := mul_le_mul_of_nonneg_right h1' h0
        _ ≤ (482/1000)*(3/2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 723/1000 := by norm_num
    have hexp : Real.exp ((1-lam)*u) ≤ 207/100 := (Real.exp_le_exp.mpr hle).trans exp_723_le
    have h2 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 30480)
    linarith
  have hna : 0 ≤ 14900 * Real.exp u := by positivity
  have hnb : 0 ≤ 30480 * Real.exp ((1-lam)*u) := by positivity
  have habs := abs_sub_le_max_of_nonneg (14900*Real.exp u) (30480*Real.exp ((1-lam)*u)) hna hnb
  have hmax : max (14900*Real.exp u) (30480*Real.exp ((1-lam)*u)) ≤ 67050 := max_le hA hB
  unfold xyW1
  rw [abs_mul, abs_of_nonneg hP]
  exact mul_le_mul_of_nonneg_right (le_trans habs hmax) hP

/-- Pointwise bound for the weight of `xySup2`. -/
lemma xyW2_bound (lam u : ℝ) (hlam1 : 518/1000 ≤ lam) (hu : u ∈ Set.Icc (0:ℝ) (3/2)) :
    |xyW2 lam u| ≤ 12420 * xyP u := by
  have h0 : 0 ≤ u := hu.1
  have h1 : u ≤ 3/2 := hu.2
  have hP : 0 ≤ xyP u := xyP_nonneg u h0 h1
  have hA : 1250 * Real.exp u ≤ 12420 := by
    have h := Real.exp_le_exp.mpr h1
    have h2 := mul_le_mul_of_nonneg_left (le_trans h exp_three_halves_le) (by norm_num : (0:ℝ) ≤ 1250)
    linarith
  have hB : 6000 * Real.exp ((1-lam)*u) ≤ 12420 := by
    have h1' : 1 - lam ≤ 482/1000 := by linarith
    have hle : (1-lam)*u ≤ (723:ℝ)/1000 := by
      calc (1-lam)*u ≤ (482/1000)*u := mul_le_mul_of_nonneg_right h1' h0
        _ ≤ (482/1000)*(3/2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 723/1000 := by norm_num
    have hexp : Real.exp ((1-lam)*u) ≤ 207/100 := (Real.exp_le_exp.mpr hle).trans exp_723_le
    have h2 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 6000)
    linarith
  have hna : 0 ≤ 1250 * Real.exp u := by positivity
  have hnb : 0 ≤ 6000 * Real.exp ((1-lam)*u) := by positivity
  have habs := abs_sub_le_max_of_nonneg (1250*Real.exp u) (6000*Real.exp ((1-lam)*u)) hna hnb
  have hmax : max (1250*Real.exp u) (6000*Real.exp ((1-lam)*u)) ≤ 12420 := max_le hA hB
  unfold xyW2
  rw [abs_mul, abs_of_nonneg hP]
  exact mul_le_mul_of_nonneg_right (le_trans habs hmax) hP

/-! ## §2  the two sup-integrals as single oscillatory integrals -/

lemma xyTf_eq_xyP (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (3/2)) : xyT.f u = xyP u := by
  show tf72f (4/3) u = xyP u
  exact tf72f43_eq u hu

lemma xyRe_neg_one_int (t : ℝ) :
    xyRe (-1) t = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp u * xyP u) := by
  rw [xyRe_eq_integral (-1) t]
  apply intervalIntegral.integral_congr
  intro u hu
  simp only []
  have hu' : u ∈ Set.Icc (0:ℝ) (3/2) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hu
    exact hu
  have he : -((-1:ℝ)*u) = u := by ring
  rw [he, xyTf_eq_xyP u hu']

lemma xyRe_lam_int (lam t : ℝ) :
    xyRe (lam - 1) t = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u) := by
  rw [xyRe_eq_integral (lam - 1) t]
  apply intervalIntegral.integral_congr
  intro u hu
  simp only []
  have hu' : u ∈ Set.Icc (0:ℝ) (3/2) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hu
    exact hu
  have he : -((lam-1)*u) = (1-lam)*u := by ring
  rw [he, xyTf_eq_xyP u hu']

lemma xySup1_int (lam t : ℝ) :
    xySup1 lam t = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * xyW1 lam u := by
  rw [xySup1, xyRe_neg_one_int t, xyRe_lam_int lam t]
  have i1 : IntervalIntegrable (fun u : ℝ => Real.cos (t*u) * (Real.exp u * xyP u))
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
  have i2 : IntervalIntegrable (fun u : ℝ => Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
  calc 14900 * (∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp u * xyP u))
        - 30480 * (∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))
      = ∫ u in (0:ℝ)..(3/2), (14900 * (Real.cos (t*u) * (Real.exp u * xyP u))
            - 30480 * (Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_sub (i1.const_mul 14900) (i2.const_mul 30480)]
    _ = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * xyW1 lam u := by
        apply intervalIntegral.integral_congr
        intro u hu
        unfold xyW1
        ring

lemma xySup2_int (lam t : ℝ) :
    xySup2 lam t = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * xyW2 lam u := by
  rw [xySup2, xyRe_neg_one_int t, xyRe_lam_int lam t]
  have i1 : IntervalIntegrable (fun u : ℝ => Real.cos (t*u) * (Real.exp u * xyP u))
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
  have i2 : IntervalIntegrable (fun u : ℝ => Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
  calc 1250 * (∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp u * xyP u))
        - 6000 * (∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))
      = ∫ u in (0:ℝ)..(3/2), (1250 * (Real.cos (t*u) * (Real.exp u * xyP u))
            - 6000 * (Real.cos (t*u) * (Real.exp ((1-lam)*u) * xyP u))) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_sub (i1.const_mul 1250) (i2.const_mul 6000)]
    _ = ∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * xyW2 lam u := by
        apply intervalIntegral.integral_congr
        intro u hu
        unfold xyW2
        ring

/-! ## §3  the chord identity -/

lemma chord_integral_identity (Φ : ℝ → ℝ → ℝ) (w1 w2 a b lam : ℝ)
    (h1 : IntervalIntegrable (Φ lam) volume (0:ℝ) (3/2))
    (h2 : IntervalIntegrable (Φ a) volume (0:ℝ) (3/2))
    (h3 : IntervalIntegrable (Φ b) volume (0:ℝ) (3/2)) :
    (∫ u in (0:ℝ)..(3/2), Φ lam u)
        - (w1 * (∫ u in (0:ℝ)..(3/2), Φ a u) + w2 * (∫ u in (0:ℝ)..(3/2), Φ b u))
      = ∫ u in (0:ℝ)..(3/2), (Φ lam u - (w1 * Φ a u + w2 * Φ b u)) := by
  rw [← intervalIntegral.integral_const_mul w1 (Φ a),
      ← intervalIntegral.integral_const_mul w2 (Φ b),
      ← intervalIntegral.integral_add (h2.const_mul w1) (h3.const_mul w2),
      ← intervalIntegral.integral_sub h1 ((h2.const_mul w1).add (h3.const_mul w2))]

/-! ## §4  pointwise chord bounds (instances of `LagrangeLinInterp`) -/

lemma cos_chord_error (c h t u : ℝ) (hh : 0 < h) (hct : c ≤ t) (hth : t ≤ c + h) :
    |Real.cos (t*u) - ((c+h-t)/h * Real.cos (c*u) + (t-c)/h * Real.cos ((c+h)*u))|
      ≤ h^2 * u^2 / 8 := by
  have hab : c < c + h := by linarith
  have hx : t ∈ Set.Icc c (c+h) := ⟨hct, hth⟩
  have hd1 : ∀ y ∈ Set.Icc c (c+h),
      HasDerivAt (fun z : ℝ => Real.cos (z*u)) (Real.sin (y*u) * (-u)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z*u) u y := by
      simpa using (hasDerivAt_id y).mul_const u
    have h2 : HasDerivAt (fun z : ℝ => Real.cos (z*u)) ((-Real.sin (y*u)) * u) y := by
      have h := (Real.hasDerivAt_cos (y*u)).comp y h1
      simpa only [Function.comp_def] using h
    convert h2 using 1
    ring
  have hd2 : ∀ y ∈ Set.Icc c (c+h),
      HasDerivAt (fun z : ℝ => Real.sin (z*u) * (-u)) ((Real.cos (y*u)*u) * (-u)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z*u) u y := by
      simpa using (hasDerivAt_id y).mul_const u
    have h2 : HasDerivAt (fun z : ℝ => Real.sin (z*u)) (Real.cos (y*u) * u) y := by
      have h := (Real.hasDerivAt_sin (y*u)).comp y h1
      simpa only [Function.comp_def] using h
    have h3 := h2.mul_const (-u)
    simpa only [Function.comp_def] using h3
  have hb : ∀ y ∈ Set.Icc c (c+h), |(Real.cos (y*u)*u) * (-u)| ≤ u^2 := by
    intro y hy
    have hc : |Real.cos (y*u)| ≤ 1 := Real.abs_cos_le_one _
    rw [abs_mul, abs_mul, abs_neg]
    calc |Real.cos (y*u)| * |u| * |u| ≤ 1 * |u| * |u| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (abs_nonneg u)) (abs_nonneg u)
      _ = u^2 := by rw [one_mul, ← sq, sq_abs]
  have hL := linInterpAux (fun z : ℝ => Real.cos (z*u))
      (fun y => Real.sin (y*u) * (-u)) (fun y => (Real.cos (y*u)*u) * (-u)) (u^2)
      c (c+h) t hab hx hd1 hd2 hb
  rw [show (c+h) - c = h by ring] at hL
  convert hL using 1
  ring

lemma exp_chord_error (a b lam u : ℝ) (hab : a < b) (hal : a ≤ lam) (hlb : lam ≤ b)
    (hu : 0 ≤ u) :
    |Real.exp ((1-lam)*u) - ((b-lam)/(b-a) * Real.exp ((1-a)*u)
        + (lam-a)/(b-a) * Real.exp ((1-b)*u))|
      ≤ (b-a)^2/8 * (u^2 * Real.exp ((1-a)*u)) := by
  have hx : lam ∈ Set.Icc a b := ⟨hal, hlb⟩
  have hd1 : ∀ y ∈ Set.Icc a b,
      HasDerivAt (fun z : ℝ => Real.exp ((1-z)*u)) (Real.exp ((1-y)*u) * (-u)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => (1-z)*u) (-u) y := by
      simpa using ((hasDerivAt_const (x := y) (1:ℝ)).sub (hasDerivAt_id y)).mul_const u
    have h2 := (Real.hasDerivAt_exp ((1-y)*u)).comp y h1
    simpa only [Function.comp_def] using h2
  have hd2 : ∀ y ∈ Set.Icc a b,
      HasDerivAt (fun z : ℝ => Real.exp ((1-z)*u) * (-u))
        ((Real.exp ((1-y)*u) * (-u)) * (-u)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => (1-z)*u) (-u) y := by
      simpa using ((hasDerivAt_const (x := y) (1:ℝ)).sub (hasDerivAt_id y)).mul_const u
    have h2 := (Real.hasDerivAt_exp ((1-y)*u)).comp y h1
    have h3 := h2.mul_const (-u)
    simpa only [Function.comp_def] using h3
  have hb : ∀ y ∈ Set.Icc a b, |(Real.exp ((1-y)*u) * (-u)) * (-u)|
      ≤ u^2 * Real.exp ((1-a)*u) := by
    intro y hy
    have hle : (1-y)*u ≤ (1-a)*u := mul_le_mul_of_nonneg_right (by linarith [hy.1]) hu
    have hexp : Real.exp ((1-y)*u) ≤ Real.exp ((1-a)*u) := Real.exp_le_exp.mpr hle
    have hu2 : |u| * |u| = u*u := by rw [← sq, sq_abs]; ring
    have h1 : |(Real.exp ((1-y)*u) * (-u)) * (-u)| = Real.exp ((1-y)*u) * (|u| * |u|) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), mul_assoc]
    rw [h1, hu2]
    calc Real.exp ((1-y)*u) * (u*u) ≤ Real.exp ((1-a)*u) * (u*u) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = u^2 * Real.exp ((1-a)*u) := by ring
  have hL := linInterpAux (fun z : ℝ => Real.exp ((1-z)*u))
      (fun y => Real.exp ((1-y)*u) * (-u))
      (fun y => (Real.exp ((1-y)*u) * (-u)) * (-u))
      (u^2 * Real.exp ((1-a)*u)) a b lam hab hx hd1 hd2 hb
  exact hL

/-! ## §5  the four interpolation estimates -/

lemma xySup1_t_interp (lam c h t : ℝ) (hlam1 : 518/1000 ≤ lam) (hlam2 : lam ≤ 628/1000)
    (hh : 0 < h) (hct : c ≤ t) (hth : t ≤ c + h) :
    xySup1 lam t ≤ max (xySup1 lam c) (xySup1 lam (c+h)) + h^2 * (13970:ℝ)/8 := by
  set w1 : ℝ := (c+h-t)/h with hw1def
  set w2 : ℝ := (t-c)/h with hw2def
  have hw1 : 0 ≤ w1 := by rw [hw1def]; exact div_nonneg (by linarith) (le_of_lt hh)
  have hw2 : 0 ≤ w2 := by rw [hw2def]; exact div_nonneg (by linarith) (le_of_lt hh)
  have hwsum : w1 + w2 = 1 := by
    rw [hw1def, hw2def, ← add_div, show c + h - t + (t - c) = h by ring, div_self (ne_of_gt hh)]
  have hkey : xySup1 lam t - (w1 * xySup1 lam c + w2 * xySup1 lam (c+h))
      = ∫ u in (0:ℝ)..(3/2),
          (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u := by
    rw [xySup1_int lam t, xySup1_int lam c, xySup1_int lam (c+h), hw1def, hw2def]
    have hid := chord_integral_identity (fun p u => Real.cos (p*u) * xyW1 lam u)
      ((c+h-t)/h) ((t-c)/h) c (c+h) t
      ((cont_cos_mul_W1 lam t).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W1 lam c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W1 lam (c+h)).intervalIntegrable 0 (3/2))
    refine hid.trans ?_
    apply intervalIntegral.integral_congr
    intro u hu
    simp only []
    ring
  have hcos1 : ∀ u : ℝ, |Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)|
      ≤ h^2 * u^2 / 8 := by
    intro u
    have h := cos_chord_error c h t u hh hct hth
    rw [← hw1def, ← hw2def] at h
    convert h using 1
    ring
  have hmain : xySup1 lam t - (w1 * xySup1 lam c + w2 * xySup1 lam (c+h)) ≤ h^2 * 13410 / 8 := by
    rw [hkey]
    have hstep1 : |∫ u in (0:ℝ)..(3/2),
          (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u|
        ≤ ∫ u in (0:ℝ)..(3/2),
          |(Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have hstep2 : ∫ u in (0:ℝ)..(3/2),
          |(Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u|
        ≤ ∫ u in (0:ℝ)..(3/2), (h^2 * (67050:ℝ)/8) * (u^2 * xyP u) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact Continuous.intervalIntegrable (by unfold xyW1 xyP; fun_prop) 0 (3/2)
      · exact Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      · intro u hu
        have hc := hcos1 u
        have hW := xyW1_bound lam u hlam1 hu
        rw [abs_mul]
        calc |Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)| * |xyW1 lam u|
            ≤ (h^2 * u^2 / 8) * (67050 * xyP u) :=
              mul_le_mul hc hW (abs_nonneg _) (by positivity)
          _ = (h^2 * (67050:ℝ)/8) * (u^2 * xyP u) := by ring
    have hstep3 : ∫ u in (0:ℝ)..(3/2), (h^2 * (67050:ℝ)/8) * (u^2 * xyP u) = h^2 * 13410 / 8 := by
      rw [intervalIntegral.integral_const_mul, xyP_moment_two]
      ring
    calc (∫ u in (0:ℝ)..(3/2),
            (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u)
        ≤ |∫ u in (0:ℝ)..(3/2),
            (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW1 lam u| :=
          le_abs_self _
      _ ≤ h^2 * 13410 / 8 := by
          rw [hstep3] at hstep2
          exact hstep1.trans hstep2
  have hchord : w1 * xySup1 lam c + w2 * xySup1 lam (c+h)
      ≤ max (xySup1 lam c) (xySup1 lam (c+h)) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (xySup1 lam c) (xySup1 lam (c+h))) hw1
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (xySup1 lam c) (xySup1 lam (c+h))) hw2
    calc w1 * xySup1 lam c + w2 * xySup1 lam (c+h)
        ≤ w1 * max (xySup1 lam c) (xySup1 lam (c+h))
            + w2 * max (xySup1 lam c) (xySup1 lam (c+h)) := add_le_add h1 h2
      _ = (w1 + w2) * max (xySup1 lam c) (xySup1 lam (c+h)) := by ring
      _ = max (xySup1 lam c) (xySup1 lam (c+h)) := by rw [hwsum, one_mul]
  have hfin : h^2 * 13410 / 8 ≤ h^2 * (13970:ℝ)/8 := by
    have h := mul_le_mul_of_nonneg_left (by norm_num : (13410:ℝ) ≤ 13970) (sq_nonneg h)
    linarith
  linarith [hmain, hchord, hfin]

lemma xySup2_t_interp (lam c h t : ℝ) (hlam1 : 518/1000 ≤ lam) (hlam2 : lam ≤ 628/1000)
    (hh : 0 < h) (hct : c ≤ t) (hth : t ≤ c + h) :
    xySup2 lam t ≤ max (xySup2 lam c) (xySup2 lam (c+h)) + h^2 * (4258:ℝ)/8 := by
  set w1 : ℝ := (c+h-t)/h with hw1def
  set w2 : ℝ := (t-c)/h with hw2def
  have hw1 : 0 ≤ w1 := by rw [hw1def]; exact div_nonneg (by linarith) (le_of_lt hh)
  have hw2 : 0 ≤ w2 := by rw [hw2def]; exact div_nonneg (by linarith) (le_of_lt hh)
  have hwsum : w1 + w2 = 1 := by
    rw [hw1def, hw2def, ← add_div, show c + h - t + (t - c) = h by ring, div_self (ne_of_gt hh)]
  have hkey : xySup2 lam t - (w1 * xySup2 lam c + w2 * xySup2 lam (c+h))
      = ∫ u in (0:ℝ)..(3/2),
          (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u := by
    rw [xySup2_int lam t, xySup2_int lam c, xySup2_int lam (c+h), hw1def, hw2def]
    have hid := chord_integral_identity (fun p u => Real.cos (p*u) * xyW2 lam u)
      ((c+h-t)/h) ((t-c)/h) c (c+h) t
      ((cont_cos_mul_W2 lam t).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W2 lam c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W2 lam (c+h)).intervalIntegrable 0 (3/2))
    refine hid.trans ?_
    apply intervalIntegral.integral_congr
    intro u hu
    simp only []
    ring
  have hcos1 : ∀ u : ℝ, |Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)|
      ≤ h^2 * u^2 / 8 := by
    intro u
    have h := cos_chord_error c h t u hh hct hth
    rw [← hw1def, ← hw2def] at h
    convert h using 1
    ring
  have hmain : xySup2 lam t - (w1 * xySup2 lam c + w2 * xySup2 lam (c+h)) ≤ h^2 * 2484 / 8 := by
    rw [hkey]
    have hstep1 : |∫ u in (0:ℝ)..(3/2),
          (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u|
        ≤ ∫ u in (0:ℝ)..(3/2),
          |(Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have hstep2 : ∫ u in (0:ℝ)..(3/2),
          |(Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u|
        ≤ ∫ u in (0:ℝ)..(3/2), (h^2 * (12420:ℝ)/8) * (u^2 * xyP u) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact Continuous.intervalIntegrable (by unfold xyW2 xyP; fun_prop) 0 (3/2)
      · exact Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      · intro u hu
        have hc := hcos1 u
        have hW := xyW2_bound lam u hlam1 hu
        rw [abs_mul]
        calc |Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)| * |xyW2 lam u|
            ≤ (h^2 * u^2 / 8) * (12420 * xyP u) :=
              mul_le_mul hc hW (abs_nonneg _) (by positivity)
          _ = (h^2 * (12420:ℝ)/8) * (u^2 * xyP u) := by ring
    have hstep3 : ∫ u in (0:ℝ)..(3/2), (h^2 * (12420:ℝ)/8) * (u^2 * xyP u) = h^2 * 2484 / 8 := by
      rw [intervalIntegral.integral_const_mul, xyP_moment_two]
      ring
    calc (∫ u in (0:ℝ)..(3/2),
            (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u)
        ≤ |∫ u in (0:ℝ)..(3/2),
            (Real.cos (t*u) - w1 * Real.cos (c*u) - w2 * Real.cos ((c+h)*u)) * xyW2 lam u| :=
          le_abs_self _
      _ ≤ h^2 * 2484 / 8 := by
          rw [hstep3] at hstep2
          exact hstep1.trans hstep2
  have hchord : w1 * xySup2 lam c + w2 * xySup2 lam (c+h)
      ≤ max (xySup2 lam c) (xySup2 lam (c+h)) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (xySup2 lam c) (xySup2 lam (c+h))) hw1
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (xySup2 lam c) (xySup2 lam (c+h))) hw2
    calc w1 * xySup2 lam c + w2 * xySup2 lam (c+h)
        ≤ w1 * max (xySup2 lam c) (xySup2 lam (c+h))
            + w2 * max (xySup2 lam c) (xySup2 lam (c+h)) := add_le_add h1 h2
      _ = (w1 + w2) * max (xySup2 lam c) (xySup2 lam (c+h)) := by ring
      _ = max (xySup2 lam c) (xySup2 lam (c+h)) := by rw [hwsum, one_mul]
  have hfin : h^2 * 2484 / 8 ≤ h^2 * (4258:ℝ)/8 := by
    have h := mul_le_mul_of_nonneg_left (by norm_num : (2484:ℝ) ≤ 4258) (sq_nonneg h)
    linarith
  linarith [hmain, hchord, hfin]

lemma xySup1_lam_interp (a b c lam : ℝ) (ha : 518/1000 ≤ a) (hab : a < b)
    (hgap : b - a ≤ 37/1000) (hal : a ≤ lam) (hlb : lam ≤ b) :
    xySup1 lam c ≤ max (xySup1 a c) (xySup1 b c) + 11/5 := by
  set w1 : ℝ := (b-lam)/(b-a) with hw1def
  set w2 : ℝ := (lam-a)/(b-a) with hw2def
  have hw1 : 0 ≤ w1 := by rw [hw1def]; exact div_nonneg (by linarith) (by linarith)
  have hw2 : 0 ≤ w2 := by rw [hw2def]; exact div_nonneg (by linarith) (by linarith)
  have hwsum : w1 + w2 = 1 := by
    rw [hw1def, hw2def, ← add_div, show b - lam + (lam - a) = b - a by ring]
    exact div_self (by linarith : b - a ≠ 0)
  have hkey : xySup1 lam c - (w1 * xySup1 a c + w2 * xySup1 b c)
      = ∫ u in (0:ℝ)..(3/2),
          Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
            - 30480*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u) := by
    rw [xySup1_int lam c, xySup1_int a c, xySup1_int b c, hw1def, hw2def]
    have hid := chord_integral_identity (fun p u => Real.cos (c*u) * xyW1 p u)
      ((b-lam)/(b-a)) ((lam-a)/(b-a)) a b lam
      ((cont_cos_mul_W1 lam c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W1 a c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W1 b c).intervalIntegrable 0 (3/2))
    refine hid.trans ?_
    apply intervalIntegral.integral_congr
    intro u hu
    simp only []
    unfold xyW1
    ring
  have hsub0 : (1 - w1 - w2 : ℝ) = 0 := by linarith
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) (3/2),
      |Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
        - 30480*(Real.exp ((1-lam)*u)
          - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
      ≤ (30480 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) := by
    intro u hu
    have hyP : 0 ≤ xyP u := xyP_nonneg u hu.1 hu.2
    have hcos1 : |Real.cos (c*u)| ≤ 1 := Real.abs_cos_le_one _
    have hX : |Real.exp ((1-lam)*u) - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
        ≤ (b-a)^2/8 * (u^2 * Real.exp ((1-a)*u)) := by
      rw [hw1def, hw2def]
      exact exp_chord_error a b lam u hab hal hlb hu.1
    have hexp207 : Real.exp ((1-a)*u) ≤ 207/100 := by
      have h1a : 1 - a ≤ 482/1000 := by linarith
      have hle : (1-a)*u ≤ (723:ℝ)/1000 := by
        calc (1-a)*u ≤ (482/1000)*u := mul_le_mul_of_nonneg_right h1a hu.1
          _ ≤ (482/1000)*(3/2) := mul_le_mul_of_nonneg_left hu.2 (by norm_num)
          _ = 723/1000 := by norm_num
      exact (Real.exp_le_exp.mpr hle).trans exp_723_le
    have hX2 : |Real.exp ((1-lam)*u) - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
        ≤ (b-a)^2/8 * (u^2 * (207/100)) := by
      refine hX.trans ?_
      have h3 : 0 ≤ (b-a)^2/8 := by positivity
      have h4 : u^2 * Real.exp ((1-a)*u) ≤ u^2 * (207/100) :=
        mul_le_mul_of_nonneg_left hexp207 (sq_nonneg u)
      exact mul_le_mul_of_nonneg_left h4 h3
    have heq : Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
          - 30480*(Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)
        = (-30480 * (Real.cos (c*u) * (Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))))) * xyP u := by
      rw [hsub0]
      ring
    have habs : |(-30480 * (Real.cos (c*u) * (Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))))) * xyP u|
        = 30480 * (|Real.cos (c*u)| * |Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|) * xyP u := by
      rw [abs_mul, abs_of_nonneg hyP, abs_mul, abs_neg, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 30480)]
    rw [heq, habs]
    calc 30480 * (|Real.cos (c*u)| * |Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|) * xyP u
        ≤ 30480 * (1 * ((b-a)^2/8 * (u^2 * (207/100)))) * xyP u := by
          have h5 : |Real.cos (c*u)| * |Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
              ≤ 1 * ((b-a)^2/8 * (u^2 * (207/100))) :=
            mul_le_mul hcos1 hX2 (abs_nonneg _) (by norm_num)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h5 (by norm_num)) hyP
      _ = (30480 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) := by ring
  have hmain : xySup1 lam c - (w1 * xySup1 a c + w2 * xySup1 b c) ≤ 11/5 := by
    rw [hkey]
    have hbig : |∫ u in (0:ℝ)..(3/2),
          Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
            - 30480*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
        ≤ (30480 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) := by
      have hint1 : IntervalIntegrable (fun u : ℝ => |Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
            - 30480*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|)
          volume (0:ℝ) (3/2) :=
        Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      have hint2 : IntervalIntegrable
          (fun u : ℝ => (30480 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u)) volume (0:ℝ) (3/2) :=
        Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      calc |∫ u in (0:ℝ)..(3/2),
            Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
              - 30480*(Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
          ≤ ∫ u in (0:ℝ)..(3/2), |Real.cos (c*u) * ((14900*Real.exp u*(1 - w1 - w2)
              - 30480*(Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ u in (0:ℝ)..(3/2), (30480 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) :=
            intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hpt
        _ = (30480 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) := by
            rw [intervalIntegral.integral_const_mul]
    have hnum : (30480 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) ≤ 11/5 := by
      rw [xyP_moment_two]
      have h2 : (b-a)^2 ≤ (37/1000)^2 := by
        have h1 : 0 ≤ b - a := by linarith
        nlinarith [hgap, h1]
      nlinarith [h2]
    exact le_trans (le_abs_self _) (le_trans hbig hnum)
  have hchord : w1 * xySup1 a c + w2 * xySup1 b c ≤ max (xySup1 a c) (xySup1 b c) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (xySup1 a c) (xySup1 b c)) hw1
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (xySup1 a c) (xySup1 b c)) hw2
    calc w1 * xySup1 a c + w2 * xySup1 b c
        ≤ w1 * max (xySup1 a c) (xySup1 b c) + w2 * max (xySup1 a c) (xySup1 b c) :=
          add_le_add h1 h2
      _ = (w1 + w2) * max (xySup1 a c) (xySup1 b c) := by ring
      _ = max (xySup1 a c) (xySup1 b c) := by rw [hwsum, one_mul]
  linarith [hmain, hchord]

lemma xySup2_lam_interp (a b c lam : ℝ) (ha : 518/1000 ≤ a) (hab : a < b)
    (hgap : b - a ≤ 37/1000) (hal : a ≤ lam) (hlb : lam ≤ b) :
    xySup2 lam c ≤ max (xySup2 a c) (xySup2 b c) + 11/5 := by
  set w1 : ℝ := (b-lam)/(b-a) with hw1def
  set w2 : ℝ := (lam-a)/(b-a) with hw2def
  have hw1 : 0 ≤ w1 := by rw [hw1def]; exact div_nonneg (by linarith) (by linarith)
  have hw2 : 0 ≤ w2 := by rw [hw2def]; exact div_nonneg (by linarith) (by linarith)
  have hwsum : w1 + w2 = 1 := by
    rw [hw1def, hw2def, ← add_div, show b - lam + (lam - a) = b - a by ring]
    exact div_self (by linarith : b - a ≠ 0)
  have hkey : xySup2 lam c - (w1 * xySup2 a c + w2 * xySup2 b c)
      = ∫ u in (0:ℝ)..(3/2),
          Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
            - 6000*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u) := by
    rw [xySup2_int lam c, xySup2_int a c, xySup2_int b c, hw1def, hw2def]
    have hid := chord_integral_identity (fun p u => Real.cos (c*u) * xyW2 p u)
      ((b-lam)/(b-a)) ((lam-a)/(b-a)) a b lam
      ((cont_cos_mul_W2 lam c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W2 a c).intervalIntegrable 0 (3/2))
      ((cont_cos_mul_W2 b c).intervalIntegrable 0 (3/2))
    refine hid.trans ?_
    apply intervalIntegral.integral_congr
    intro u hu
    simp only []
    unfold xyW2
    ring
  have hsub0 : (1 - w1 - w2 : ℝ) = 0 := by linarith
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) (3/2),
      |Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
        - 6000*(Real.exp ((1-lam)*u)
          - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
      ≤ (6000 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) := by
    intro u hu
    have hyP : 0 ≤ xyP u := xyP_nonneg u hu.1 hu.2
    have hcos1 : |Real.cos (c*u)| ≤ 1 := Real.abs_cos_le_one _
    have hX : |Real.exp ((1-lam)*u) - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
        ≤ (b-a)^2/8 * (u^2 * Real.exp ((1-a)*u)) := by
      rw [hw1def, hw2def]
      exact exp_chord_error a b lam u hab hal hlb hu.1
    have hexp207 : Real.exp ((1-a)*u) ≤ 207/100 := by
      have h1a : 1 - a ≤ 482/1000 := by linarith
      have hle : (1-a)*u ≤ (723:ℝ)/1000 := by
        calc (1-a)*u ≤ (482/1000)*u := mul_le_mul_of_nonneg_right h1a hu.1
          _ ≤ (482/1000)*(3/2) := mul_le_mul_of_nonneg_left hu.2 (by norm_num)
          _ = 723/1000 := by norm_num
      exact (Real.exp_le_exp.mpr hle).trans exp_723_le
    have hX2 : |Real.exp ((1-lam)*u) - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
        ≤ (b-a)^2/8 * (u^2 * (207/100)) := by
      refine hX.trans ?_
      have h3 : 0 ≤ (b-a)^2/8 := by positivity
      have h4 : u^2 * Real.exp ((1-a)*u) ≤ u^2 * (207/100) :=
        mul_le_mul_of_nonneg_left hexp207 (sq_nonneg u)
      exact mul_le_mul_of_nonneg_left h4 h3
    have heq : Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
          - 6000*(Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)
        = (-6000 * (Real.cos (c*u) * (Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))))) * xyP u := by
      rw [hsub0]
      ring
    have habs : |(-6000 * (Real.cos (c*u) * (Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))))) * xyP u|
        = 6000 * (|Real.cos (c*u)| * |Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|) * xyP u := by
      rw [abs_mul, abs_of_nonneg hyP, abs_mul, abs_neg, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 6000)]
    rw [heq, habs]
    calc 6000 * (|Real.cos (c*u)| * |Real.exp ((1-lam)*u)
            - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|) * xyP u
        ≤ 6000 * (1 * ((b-a)^2/8 * (u^2 * (207/100)))) * xyP u := by
          have h5 : |Real.cos (c*u)| * |Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u))|
              ≤ 1 * ((b-a)^2/8 * (u^2 * (207/100))) :=
            mul_le_mul hcos1 hX2 (abs_nonneg _) (by norm_num)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h5 (by norm_num)) hyP
      _ = (6000 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) := by ring
  have hmain : xySup2 lam c - (w1 * xySup2 a c + w2 * xySup2 b c) ≤ 11/5 := by
    rw [hkey]
    have hbig : |∫ u in (0:ℝ)..(3/2),
          Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
            - 6000*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
        ≤ (6000 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) := by
      have hint1 : IntervalIntegrable (fun u : ℝ => |Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
            - 6000*(Real.exp ((1-lam)*u)
              - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|)
          volume (0:ℝ) (3/2) :=
        Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      have hint2 : IntervalIntegrable
          (fun u : ℝ => (6000 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u)) volume (0:ℝ) (3/2) :=
        Continuous.intervalIntegrable (by unfold xyP; fun_prop) 0 (3/2)
      calc |∫ u in (0:ℝ)..(3/2),
            Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
              - 6000*(Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)|
          ≤ ∫ u in (0:ℝ)..(3/2), |Real.cos (c*u) * ((1250*Real.exp u*(1 - w1 - w2)
              - 6000*(Real.exp ((1-lam)*u)
                - (w1*Real.exp ((1-a)*u) + w2*Real.exp ((1-b)*u)))) * xyP u)| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ u in (0:ℝ)..(3/2), (6000 * (b-a)^2/8 * (207/100)) * (u^2 * xyP u) :=
            intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hpt
        _ = (6000 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) := by
            rw [intervalIntegral.integral_const_mul]
    have hnum : (6000 * (b-a)^2/8 * (207/100)) * (∫ u in (0:ℝ)..(3/2), u^2 * xyP u) ≤ 11/5 := by
      rw [xyP_moment_two]
      have h2 : (b-a)^2 ≤ (37/1000)^2 := by
        have h1 : 0 ≤ b - a := by linarith
        nlinarith [hgap, h1]
      nlinarith [h2]
    exact le_trans (le_abs_self _) (le_trans hbig hnum)
  have hchord : w1 * xySup2 a c + w2 * xySup2 b c ≤ max (xySup2 a c) (xySup2 b c) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (xySup2 a c) (xySup2 b c)) hw1
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (xySup2 a c) (xySup2 b c)) hw2
    calc w1 * xySup2 a c + w2 * xySup2 b c
        ≤ w1 * max (xySup2 a c) (xySup2 b c) + w2 * max (xySup2 a c) (xySup2 b c) :=
          add_le_add h1 h2
      _ = (w1 + w2) * max (xySup2 a c) (xySup2 b c) := by ring
      _ = max (xySup2 a c) (xySup2 b c) := by rw [hwsum, one_mul]
  linarith [hmain, hchord]

/-! ## §6  the theorem -/

theorem XySupInterp :
    (∀ (lam : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → ∀ (c h t : ℝ), 0 < h → c ≤ t → t ≤ c+h →
      xySup1 lam t ≤ max (xySup1 lam c) (xySup1 lam (c+h)) + h^2 * (13970:ℝ)/8)
  ∧ (∀ (lam : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → ∀ (c h t : ℝ), 0 < h → c ≤ t → t ≤ c+h →
      xySup2 lam t ≤ max (xySup2 lam c) (xySup2 lam (c+h)) + h^2 * (4258:ℝ)/8)
  ∧ (∀ (c : ℝ) (lam : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 →
      xySup1 lam c ≤ max (max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c))
        (max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)) + (11:ℝ)/5)
  ∧ (∀ (c : ℝ) (lam : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 →
      xySup2 lam c ≤ max (max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c))
        (max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)) + (11:ℝ)/5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam h1 h2 c h t hh hct hth
    exact xySup1_t_interp lam c h t h1 h2 hh hct hth
  · intro lam h1 h2 c h t hh hct hth
    exact xySup2_t_interp lam c h t h1 h2 hh hct hth
  · intro c lam h1 h2
    by_cases hc1 : lam ≤ 555/1000
    · have h := xySup1_lam_interp (518/1000) (555/1000) c lam (by norm_num) (by norm_num)
        (by norm_num) (by linarith) hc1
      have hG : max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c)
          ≤ max (max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c))
              (max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)) := le_max_left _ _
      linarith
    · push_neg at hc1
      by_cases hc2 : lam ≤ 592/1000
      · have h := xySup1_lam_interp (555/1000) (592/1000) c lam (by norm_num) (by norm_num)
          (by norm_num) (by linarith) hc2
        have hB : xySup1 ((555:ℝ)/1000) c
            ≤ max (max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c))
                (max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)) :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        have hC : xySup1 ((592:ℝ)/1000) c
            ≤ max (max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c))
                (max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        linarith [max_le hB hC]
      · push_neg at hc2
        have h := xySup1_lam_interp (592/1000) (628/1000) c lam (by norm_num) (by norm_num)
          (by norm_num) (by linarith) h2
        have hG : max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)
            ≤ max (max (xySup1 (518/1000) c) (xySup1 ((555:ℝ)/1000) c))
                (max (xySup1 ((592:ℝ)/1000) c) (xySup1 ((628:ℝ)/1000) c)) := le_max_right _ _
        linarith
  · intro c lam h1 h2
    by_cases hc1 : lam ≤ 555/1000
    · have h := xySup2_lam_interp (518/1000) (555/1000) c lam (by norm_num) (by norm_num)
        (by norm_num) (by linarith) hc1
      have hG : max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c)
          ≤ max (max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c))
              (max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)) := le_max_left _ _
      linarith
    · push_neg at hc1
      by_cases hc2 : lam ≤ 592/1000
      · have h := xySup2_lam_interp (555/1000) (592/1000) c lam (by norm_num) (by norm_num)
          (by norm_num) (by linarith) hc2
        have hB : xySup2 ((555:ℝ)/1000) c
            ≤ max (max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c))
                (max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)) :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        have hC : xySup2 ((592:ℝ)/1000) c
            ≤ max (max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c))
                (max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        linarith [max_le hB hC]
      · push_neg at hc2
        have h := xySup2_lam_interp (592/1000) (628/1000) c lam (by norm_num) (by norm_num)
          (by norm_num) (by linarith) h2
        have hG : max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)
            ≤ max (max (xySup2 (518/1000) c) (xySup2 ((555:ℝ)/1000) c))
                (max (xySup2 ((592:ℝ)/1000) c) (xySup2 ((628:ℝ)/1000) c)) := le_max_right _ _
        linarith

end Work.ZeroFreeTables.XY
