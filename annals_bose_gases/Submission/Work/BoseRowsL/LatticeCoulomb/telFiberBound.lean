import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.telFiberBound`

The fibre bound for the telescoped lattice Coulomb sum: with `g x = 1/(x²+ρ²)` and `K` the
largest integer with `K² + ρ² ≤ R²` (so that `R² < (K+1)² + ρ²`), the second-difference
combination of `g` over the window `|k| ≤ K`, summed over the fibre
`k ∈ [-(K+1), K+1]`, is bounded by `27/(10ρ³) + min (10/R²) (4/ρ²)`.

The proof splits the fibre into the *interior* `|k| ≤ K-1`, where the summand is exactly the
second difference of `g`, and the four *boundary* points `k = ±K, ±(K+1)`, where the truncation
of the window leaves an extra contribution.  The interior part is bounded by the discrete
telescoping argument (`Σ_k |Δ²g(k)| ≤ ∫ |g''| ≤ 27/(5ρ³)`), and each boundary point contributes
at most `g(K+1) = 1/((K+1)²+ρ²)`, which is `≤ 1/R²` by `hK'` and `≤ 1/ρ²` trivially; there are
four of them.

## Contents

* `tfG`, `tfG1`, `tfG2` — the kernel `1/(x²+ρ²)` and its two derivatives;
* `tfAux` — the bounded antiderivative of the majorant `2(3u²+1)/(1+u²)³` (bounded by `13/10`);
* `tfG2_bound` — `∫_a^b |g''| ≤ 27/(5ρ³)` for `ρ ≥ 1` and all `a ≤ b`;
* `tf_secondDiff_le` — the pointwise second-difference bound (FTC twice);
* `tf_fiberSum` — the fibre sum ↔ interval-integral tiling (induction over `ℤ`);
* `tf_interiorSum` — the assembly `Σ_{k∈[c,d]} |Δ²g(k)| ≤ 27/(5ρ³)`;
* `telFiberBound` — the target.
-/

namespace Work.BoseRowsL.LatticeCoulomb

noncomputable section

open scoped Interval
open MeasureTheory

/-! ### The fibre kernel and its derivatives -/

/-- The fibre kernel `tfG ρ x = 1/(x²+ρ²)`. -/
def tfG (ρ : ℝ) (x : ℝ) : ℝ := 1 / (x ^ 2 + ρ ^ 2)

/-- The first derivative of the fibre kernel. -/
def tfG1 (ρ : ℝ) (x : ℝ) : ℝ := -(2 * x) / (x ^ 2 + ρ ^ 2) ^ 2

/-- The second derivative of the fibre kernel. -/
def tfG2 (ρ : ℝ) (x : ℝ) : ℝ := (6 * x ^ 2 - 2 * ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3

lemma tfG_denom_ne (ρ x : ℝ) (hρ : ρ ≠ 0) : x ^ 2 + ρ ^ 2 ≠ 0 := by
  have h := sq_pos_of_ne_zero hρ
  nlinarith [sq_nonneg x, h]

lemma tfG_denom_pos (ρ x : ℝ) (hρ : 0 < ρ) : 0 < x ^ 2 + ρ ^ 2 := by
  have h := sq_pos_of_ne_zero (ne_of_gt hρ)
  nlinarith [sq_nonneg x, h]

/-- `tfG ρ` has derivative `tfG1 ρ`. -/
lemma hasDerivAt_tfG (ρ x : ℝ) (hρ : ρ ≠ 0) : HasDerivAt (tfG ρ) (tfG1 ρ x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ρ ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (ρ ^ 2)
  have h2 : HasDerivAt (fun y : ℝ => (y ^ 2 + ρ ^ 2)⁻¹)
      (-(2 * x) / (x ^ 2 + ρ ^ 2) ^ 2) x :=
    h1.inv (tfG_denom_ne ρ x hρ)
  rw [show (fun y : ℝ => (y ^ 2 + ρ ^ 2)⁻¹) = tfG ρ from
    (funext fun y => by simp [tfG, one_div])] at h2
  exact h2

/-- `tfG1 ρ` has derivative `tfG2 ρ`. -/
lemma hasDerivAt_tfG1 (ρ x : ℝ) (hρ : ρ ≠ 0) : HasDerivAt (tfG1 ρ) (tfG2 ρ x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ρ ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (ρ ^ 2)
  have h2 : HasDerivAt (fun y : ℝ => (y ^ 2 + ρ ^ 2) ^ 2) (4 * x * (x ^ 2 + ρ ^ 2)) x := by
    have hm := h1.mul h1
    rw [show (fun y : ℝ => y ^ 2 + ρ ^ 2) * (fun y : ℝ => y ^ 2 + ρ ^ 2)
        = fun y : ℝ => (y ^ 2 + ρ ^ 2) ^ 2 from (funext fun y => by simp [pow_two])] at hm
    rw [show 2 * x * (x ^ 2 + ρ ^ 2) + (x ^ 2 + ρ ^ 2) * (2 * x)
        = 4 * x * (x ^ 2 + ρ ^ 2) from by ring] at hm
    exact hm
  have hnum : HasDerivAt (fun y : ℝ => -(2 * y)) (-2) x := by
    simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
  have h3 := hnum.div h2 (pow_ne_zero 2 (tfG_denom_ne ρ x hρ))
  rw [show (fun y : ℝ => -(2 * y)) / (fun y : ℝ => (y ^ 2 + ρ ^ 2) ^ 2)
      = tfG1 ρ from (funext fun y => by simp [tfG1, Pi.div_apply])] at h3
  refine h3.congr_deriv ?_
  simp only [tfG2]
  field_simp
  ring

lemma tfG_nonneg (ρ x : ℝ) : 0 ≤ tfG ρ x := by
  rw [tfG]
  exact div_nonneg zero_le_one (by positivity)

lemma continuous_tfG1 (ρ : ℝ) (hρ : ρ ≠ 0) : Continuous (tfG1 ρ) := by
  have h : tfG1 ρ = fun y : ℝ => (-(2 * y)) * ((y ^ 2 + ρ ^ 2) ^ 2)⁻¹ := by
    funext y
    simp [tfG1, div_eq_mul_inv]
  rw [h]
  exact Continuous.mul (by fun_prop)
    (Continuous.inv₀ (by fun_prop) fun y => pow_ne_zero 2 (tfG_denom_ne ρ y hρ))

lemma continuous_tfG2 (ρ : ℝ) (hρ : ρ ≠ 0) : Continuous (tfG2 ρ) := by
  have h : tfG2 ρ = fun y : ℝ => (6 * y ^ 2 - 2 * ρ ^ 2) * ((y ^ 2 + ρ ^ 2) ^ 3)⁻¹ := by
    funext y
    simp [tfG2, div_eq_mul_inv]
  rw [h]
  exact Continuous.mul (by fun_prop)
    (Continuous.inv₀ (by fun_prop) fun y => pow_ne_zero 3 (tfG_denom_ne ρ y hρ))

lemma continuous_abs_tfG2 (ρ : ℝ) (hρ : ρ ≠ 0) : Continuous fun y : ℝ => |tfG2 ρ y| :=
  (continuous_tfG2 ρ hρ).abs

/-! ### The bounded antiderivative of the majorant -/

/-- `tfAux` is an antiderivative of `(3u²+1)/(1+u²)³`; it is odd, monotone, and bounded by
`13/10 = 1.3` (its true supremum is `3π/8 = 1.178…`). -/
def tfAux (u : ℝ) : ℝ := (3 * u ^ 3 + u) / (4 * (1 + u ^ 2) ^ 2) + (3 / 4) * Real.arctan u

lemma hasDerivAt_tfAux (u : ℝ) :
    HasDerivAt tfAux ((3 * u ^ 2 + 1) / (1 + u ^ 2) ^ 3) u := by
  have hp3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * u ^ 2) u := by
    simpa using hasDerivAt_pow 3 u
  have hp : HasDerivAt (fun u : ℝ => 3 * u ^ 3 + u) (9 * u ^ 2 + 1) u := by
    have h := (hp3.const_mul 3).add (hasDerivAt_id u)
    rw [show ((fun u : ℝ => 3 * u ^ 3) + id) = fun u : ℝ => 3 * u ^ 3 + u from by
      funext y; simp] at h
    exact h.congr_deriv (by ring)
  have h02 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have h0 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * u) u := by
    simpa using h02.const_add 1
  have h1 : HasDerivAt (fun u : ℝ => (1 + u ^ 2) ^ 2) (4 * u * (1 + u ^ 2)) u := by
    have hm := h0.mul h0
    rw [show (fun u : ℝ => 1 + u ^ 2) * (fun u : ℝ => 1 + u ^ 2)
        = fun u : ℝ => (1 + u ^ 2) ^ 2 from by funext y; simp only [Pi.mul_apply]; ring] at hm
    exact hm.congr_deriv (by ring)
  have h2 : HasDerivAt (fun u : ℝ => 4 * (1 + u ^ 2) ^ 2) (16 * u * (1 + u ^ 2)) u := by
    have hm := h1.const_mul 4
    exact hm.congr_deriv (by ring)
  have h3 := hp.div h2 (by positivity : (4 : ℝ) * (1 + u ^ 2) ^ 2 ≠ 0)
  have h4 : HasDerivAt (fun u : ℝ => (3 / 4) * Real.arctan u)
      ((3 / 4) * (1 / (1 + u ^ 2))) u :=
    (Real.hasDerivAt_arctan u).const_mul (3 / 4)
  have h5 := h3.add h4
  have h6 : HasDerivAt (fun u : ℝ => (3 * u ^ 3 + u) / (4 * (1 + u ^ 2) ^ 2)
      + (3 / 4) * Real.arctan u) ((3 * u ^ 2 + 1) / (1 + u ^ 2) ^ 3) u :=
    h5.congr_deriv (by field_simp; ring)
  exact h6

lemma tfAux_neg (u : ℝ) : tfAux (-u) = -tfAux u := by
  unfold tfAux
  rw [Real.arctan_neg]
  ring

lemma monotone_tfAux : Monotone tfAux := by
  intro a b hab
  have hcont : Continuous fun s : ℝ => (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3 := by
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro s; positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) (f := tfAux)
    (f' := fun s : ℝ => (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3)
    (fun s _ => hasDerivAt_tfAux s) (hcont.intervalIntegrable _ _)
  have hnn : 0 ≤ ∫ s in a..b, (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3 := by
    refine intervalIntegral.integral_nonneg hab ?_
    intro s _
    positivity
  linarith

lemma tfAux_ten_le : tfAux 10 ≤ 1.256 := by
  have h1 : (3 * 10 ^ 3 + 10) / (4 * (1 + 10 ^ 2) ^ 2) = 3010 / 40804 := by norm_num
  have h2 : Real.arctan 10 < Real.pi / 2 := Real.arctan_lt_pi_div_two 10
  have h3 : Real.pi < 3.15 := Real.pi_lt_d2
  have h4 : (3 / 4) * Real.arctan 10 < (3 / 4) * 1.575 := by nlinarith [h2, h3]
  rw [tfAux]
  linarith [h1, h4]

/-- Tail bound: `tfAux u ≤ tfAux 10 + 1/500` for `u ≥ 10`. -/
lemma tfAux_tail (u : ℝ) (hu : 10 ≤ u) : tfAux u ≤ tfAux 10 + 1 / 500 := by
  have hcont1 : Continuous fun s : ℝ => (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3 := by
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro s; positivity
  have h1 : ∫ s in (10 : ℝ)..u, (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3 = tfAux u - tfAux 10 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := tfAux)
      (f' := fun s : ℝ => (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3)
      (fun s _ => hasDerivAt_tfAux s) (hcont1.intervalIntegrable _ _)
  have hcont2 : ContinuousOn (fun s : ℝ => 2 / (5 * s ^ 3)) (Set.uIcc (10 : ℝ) u) := by
    refine ContinuousOn.div continuous_const.continuousOn ?_ ?_
    · fun_prop
    · intro s hs
      have hs1 : (10 : ℝ) ≤ s := by
        have h := hs
        rw [Set.uIcc_of_le hu] at h
        exact h.1
      have : (0 : ℝ) < s := by linarith
      positivity
  have h2 : ∫ s in (10 : ℝ)..u, (3 * s ^ 2 + 1) / (1 + s ^ 2) ^ 3
      ≤ ∫ s in (10 : ℝ)..u, 2 / (5 * s ^ 3) := by
    refine intervalIntegral.integral_mono_on hu (hcont1.intervalIntegrable _ _)
      (ContinuousOn.intervalIntegrable hcont2) ?_
    intro s hs
    have hs1 : 10 ≤ s := hs.1
    have hspos : (0 : ℝ) < s := by linarith
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s ^ 2) ^ 3)
      (by positivity : (0 : ℝ) < 5 * s ^ 3)]
    have hA : 3 * s ^ 2 + 1 ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg s]
    have h20 : 20 * s ^ 5 ≤ 2 * s ^ 6 := by nlinarith [hspos, hs1, pow_pos hspos 5]
    have h6 : 2 * s ^ 6 ≤ 2 * (1 + s ^ 2) ^ 3 := by nlinarith [sq_nonneg s]
    calc (3 * s ^ 2 + 1) * (5 * s ^ 3) ≤ (4 * s ^ 2) * (5 * s ^ 3) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 20 * s ^ 5 := by ring
      _ ≤ 2 * s ^ 6 := h20
      _ ≤ 2 * (1 + s ^ 2) ^ 3 := h6
  have h3 : ∫ s in (10 : ℝ)..u, 2 / (5 * s ^ 3) ≤ 1 / 500 := by
    have hderiv : ∀ s : ℝ, s ≠ 0 →
        HasDerivAt (fun s : ℝ => -(1 / (5 * s ^ 2))) (2 / (5 * s ^ 3)) s := by
      intro s hs
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h2 : HasDerivAt (fun s : ℝ => 5 * s ^ 2) (10 * s) s :=
        (h1.const_mul 5).congr_deriv (by ring)
      have h4 : HasDerivAt (fun s : ℝ => (5 * s ^ 2)⁻¹) (-(10 * s) / (5 * s ^ 2) ^ 2) s :=
        h2.inv (by positivity : 5 * s ^ 2 ≠ 0)
      have h5 : HasDerivAt (fun s : ℝ => -((5 * s ^ 2)⁻¹)) (2 / (5 * s ^ 3)) s :=
        h4.neg.congr_deriv (by field_simp; ring)
      simpa [one_div] using h5
    have hcontA : ContinuousOn (fun s : ℝ => -(1 / (5 * s ^ 2))) (Set.uIcc (10 : ℝ) u) := by
      refine ContinuousOn.neg ?_
      refine ContinuousOn.div continuous_const.continuousOn ?_ ?_
      · fun_prop
      · intro s hs
        have hs1 : (10 : ℝ) ≤ s := by
          have h := hs
          rw [Set.uIcc_of_le hu] at h
          exact h.1
        have : (0 : ℝ) < s := by linarith
        positivity
    have hval : ∫ s in (10 : ℝ)..u, 2 / (5 * s ^ 3)
        = -(1 / (5 * u ^ 2)) - (-(1 / (5 * (10 : ℝ) ^ 2))) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ => -(1 / (5 * s ^ 2))) (f' := fun s : ℝ => 2 / (5 * s ^ 3))
        (fun s hs => hderiv s (by
          have hs1 : (10 : ℝ) ≤ s := by
            have h := hs
            rw [Set.uIcc_of_le hu] at h
            exact h.1
          linarith))
        (ContinuousOn.intervalIntegrable hcont2)
    rw [hval]
    have h10v : -(1 / (5 * (10 : ℝ) ^ 2)) = -(1 / 500) := by norm_num
    rw [h10v]
    have : (0 : ℝ) ≤ 1 / (5 * u ^ 2) := by positivity
    linarith
  linarith

lemma tfAux_le_13_10 (u : ℝ) : tfAux u ≤ 13 / 10 := by
  rcases le_or_gt u 10 with hu | hu
  · have := monotone_tfAux hu
    linarith [tfAux_ten_le]
  · have := tfAux_tail u (le_of_lt hu)
    linarith [tfAux_ten_le]

lemma abs_tfAux_le (u : ℝ) : |tfAux u| ≤ 13 / 10 := by
  refine abs_le.mpr ⟨?_, tfAux_le_13_10 u⟩
  have := tfAux_le_13_10 (-u)
  rw [tfAux_neg] at this
  linarith

/-! ### The second-derivative bound -/

theorem tfG2_bound (ρ : ℝ) (hρ : 1 ≤ ρ) (a b : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, |tfG2 ρ x| ≤ 27 / (5 * ρ ^ 3) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hpoint : ∀ x : ℝ, |tfG2 ρ x| ≤ 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3 := by
    intro x
    have hden : (0 : ℝ) < (x ^ 2 + ρ ^ 2) ^ 3 := by positivity
    have hnum : |6 * x ^ 2 - 2 * ρ ^ 2| ≤ 2 * (3 * x ^ 2 + ρ ^ 2) := by
      rw [show 6 * x ^ 2 - 2 * ρ ^ 2 = 2 * (3 * x ^ 2 - ρ ^ 2) from by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by nlinarith [sq_nonneg x, sq_nonneg ρ],
        by nlinarith [sq_nonneg x, sq_nonneg ρ]⟩) (by norm_num)
    rw [tfG2, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hden]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  let H : ℝ → ℝ := fun x => (2 / ρ ^ 3) * tfAux (x / ρ)
  have hH : ∀ x : ℝ, HasDerivAt H (2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y / ρ) (1 / ρ) x := by
      simpa using (hasDerivAt_id x).div_const ρ
    have h2 : HasDerivAt (fun y : ℝ => tfAux (y / ρ))
        ((3 * (x / ρ) ^ 2 + 1) / (1 + (x / ρ) ^ 2) ^ 3 * (1 / ρ)) x := by
      simpa only [Function.comp_def] using (hasDerivAt_tfAux (x / ρ)).comp x h1
    have h3 := h2.const_mul (2 / ρ ^ 3)
    refine h3.congr_deriv ?_
    show (2 / ρ ^ 3) * ((3 * (x / ρ) ^ 2 + 1) / (1 + (x / ρ) ^ 2) ^ 3 * (1 / ρ))
      = 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3
    field_simp
    ring
  have hcont : Continuous fun x : ℝ => 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3 := by
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro x; positivity
  have hFTC : ∫ x in a..b, 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3 = H b - H a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) (f := H)
      (f' := fun x : ℝ => 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3)
      (fun x _ => hH x) (hcont.intervalIntegrable _ _)
  have hHbd : |H b - H a| ≤ 26 / (5 * ρ ^ 3) := by
    have h1 : |(2 / ρ ^ 3) * tfAux (b / ρ) - (2 / ρ ^ 3) * tfAux (a / ρ)|
        = (2 / ρ ^ 3) * |tfAux (b / ρ) - tfAux (a / ρ)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have h2 : |tfAux (b / ρ) - tfAux (a / ρ)| ≤ 13 / 10 + 13 / 10 :=
      le_trans (abs_sub _ _) (add_le_add (abs_tfAux_le _) (abs_tfAux_le _))
    have h3 : (2 / ρ ^ 3) * |tfAux (b / ρ) - tfAux (a / ρ)|
        ≤ (2 / ρ ^ 3) * (13 / 10 + 13 / 10) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (2 / ρ ^ 3) * (13 / 10 + 13 / 10) = 26 / (5 * ρ ^ 3) := by ring
    show |H b - H a| ≤ 26 / (5 * ρ ^ 3)
    rw [show H b - H a = (2 / ρ ^ 3) * tfAux (b / ρ) - (2 / ρ ^ 3) * tfAux (a / ρ) from rfl, h1]
    linarith
  calc ∫ x in a..b, |tfG2 ρ x|
      ≤ ∫ x in a..b, 2 * (3 * x ^ 2 + ρ ^ 2) / (x ^ 2 + ρ ^ 2) ^ 3 :=
        intervalIntegral.integral_mono_on hab ((continuous_abs_tfG2 ρ hρne).intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _) (fun x _ => hpoint x)
    _ = H b - H a := hFTC
    _ ≤ 26 / (5 * ρ ^ 3) := le_trans (le_abs_self _) hHbd
    _ ≤ 27 / (5 * ρ ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        norm_num

/-! ### The pointwise second difference (FTC twice) and the fibre tiling -/

/-- Continuity in the parameter of a shifted interval integral. -/
lemma continuous_shift_interval {k : ℝ → ℝ} (hk : Continuous k) (a b : ℝ) :
    Continuous fun t : ℝ => ∫ y in a + t..b + t, k y := by
  have hP : Continuous fun u : ℝ => ∫ y in (0 : ℝ)..u, k y := by
    have hf : Continuous fun p : ℝ × ℝ => k p.2 := hk.comp continuous_snd
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun _ y => k y) (a₀ := 0) (s := fun u : ℝ => u) hf continuous_id
  have h1 : Continuous fun t : ℝ => ∫ y in (0 : ℝ)..(b + t), k y := hP.comp (by fun_prop)
  have h2 : Continuous fun t : ℝ => ∫ y in (0 : ℝ)..(a + t), k y := hP.comp (by fun_prop)
  have hsub : (fun t : ℝ => ∫ y in a + t..b + t, k y)
      = fun t : ℝ => (∫ y in (0 : ℝ)..(b + t), k y) - (∫ y in (0 : ℝ)..(a + t), k y) := by
    funext t
    exact (intervalIntegral.integral_interval_sub_left (hk.intervalIntegrable 0 (b + t))
      (hk.intervalIntegrable 0 (a + t))).symm
  rw [hsub]
  exact h1.sub h2

lemma continuous_shift_tfG2 (ρ : ℝ) (hρ : ρ ≠ 0) (x : ℝ) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s) := by
  have hf : Continuous fun p : ℝ × ℝ => tfG2 ρ (x - 1 + p.1 + p.2) :=
    (continuous_tfG2 ρ hρ).comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s => tfG2 ρ (x - 1 + t + s)) hf 0 1

lemma continuous_shift_abs_tfG2 (ρ : ℝ) (hρ : ρ ≠ 0) (x : ℝ) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..1, |tfG2 ρ (x - 1 + t + s)| := by
  have hf : Continuous fun p : ℝ × ℝ => |tfG2 ρ (x - 1 + p.1 + p.2)| :=
    (continuous_abs_tfG2 ρ hρ).comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s => |tfG2 ρ (x - 1 + t + s)|) hf 0 1

/-- The pointwise second difference of `tfG ρ` is bounded by the double integral of `|tfG2 ρ|`
over the unit square. -/
lemma tf_secondDiff_le (ρ : ℝ) (hρ : ρ ≠ 0) (x : ℝ) :
    |tfG ρ (x + 1) - 2 * tfG ρ x + tfG ρ (x - 1)|
      ≤ ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, |tfG2 ρ (x - 1 + t + s)| := by
  have hFTC1 : ∫ t in (0 : ℝ)..1, tfG1 ρ (x + t) = tfG ρ (x + 1) - tfG ρ x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + 1)
      (f := tfG ρ) (f' := tfG1 ρ) (fun y _ => hasDerivAt_tfG ρ y hρ)
      ((continuous_tfG1 ρ hρ).intervalIntegrable _ _)
    rw [← h, intervalIntegral.integral_comp_add_left (fun y => tfG1 ρ y) x,
      show x + 0 = x from by ring]
  have hFTC2 : ∫ t in (0 : ℝ)..1, tfG1 ρ (x - 1 + t) = tfG ρ x - tfG ρ (x - 1) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x - 1) (b := x)
      (f := tfG ρ) (f' := tfG1 ρ) (fun y _ => hasDerivAt_tfG ρ y hρ)
      ((continuous_tfG1 ρ hρ).intervalIntegrable _ _)
    rw [← h, intervalIntegral.integral_comp_add_left (fun y => tfG1 ρ y) (x - 1),
      show x - 1 + 0 = x - 1 from by ring, show x - 1 + 1 = x from by ring]
  have hinner : ∀ t : ℝ, tfG1 ρ (x + t) - tfG1 ρ (x - 1 + t)
      = ∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s) := by
    intro t
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x - 1 + t) (b := x + t)
      (f := tfG1 ρ) (f' := tfG2 ρ) (fun y _ => hasDerivAt_tfG1 ρ y hρ)
      ((continuous_tfG2 ρ hρ).intervalIntegrable _ _)
    rw [← h, intervalIntegral.integral_comp_add_left (fun y => tfG2 ρ y) (x - 1 + t),
      show x - 1 + t + 0 = x - 1 + t from by ring, show x - 1 + t + 1 = x + t from by ring]
  have hmain : tfG ρ (x + 1) - 2 * tfG ρ x + tfG ρ (x - 1)
      = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s) := by
    have hA : IntervalIntegrable (fun t : ℝ => tfG1 ρ (x + t)) volume 0 1 :=
      ((continuous_tfG1 ρ hρ).comp (by fun_prop)).intervalIntegrable 0 1
    have hB : IntervalIntegrable (fun t : ℝ => tfG1 ρ (x - 1 + t)) volume 0 1 :=
      ((continuous_tfG1 ρ hρ).comp (by fun_prop)).intervalIntegrable 0 1
    have h2 : (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s))
        = ∫ t in (0 : ℝ)..1, (tfG1 ρ (x + t) - tfG1 ρ (x - 1 + t)) := by
      congr 1
      funext t
      exact (hinner t).symm
    rw [h2, intervalIntegral.integral_sub (f := fun t : ℝ => tfG1 ρ (x + t))
      (g := fun t : ℝ => tfG1 ρ (x - 1 + t)) hA hB, hFTC1, hFTC2]
    ring
  rw [hmain]
  calc |∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s)|
      ≤ ∫ t in (0 : ℝ)..1, |∫ s in (0 : ℝ)..1, tfG2 ρ (x - 1 + t + s)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, |tfG2 ρ (x - 1 + t + s)| := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact (continuous_shift_tfG2 ρ hρ x).abs.intervalIntegrable _ _
        · exact (continuous_shift_abs_tfG2 ρ hρ x).intervalIntegrable _ _
        · intro t _
          exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)

/-- The substitution `∫ s in 0..1, |g''(m-1+t+s)| = ∫_{m-1+t}^{m+t} |g''|`. -/
lemma tf_fiber_term (ρ : ℝ) (m : ℤ) (t : ℝ) :
    (∫ s in (0 : ℝ)..1, |tfG2 ρ ((m : ℝ) - 1 + t + s)|)
      = ∫ y in ((m : ℝ) - 1 + t)..((m : ℝ) + t), |tfG2 ρ y| := by
  rw [intervalIntegral.integral_comp_add_left (fun y => |tfG2 ρ y|) ((m : ℝ) - 1 + t)]
  simp only [add_zero]
  congr 1
  ring

/-- Splitting off the top of a `ℤ`-interval sum. -/
lemma tf_sum_Icc_succ_top (f : ℤ → ℝ) (c d : ℤ) (hcd : c ≤ d + 1) :
    (∑ k ∈ Finset.Icc c (d + 1), f k) = (∑ k ∈ Finset.Icc c d, f k) + f (d + 1) := by
  have h1 : Finset.Icc c (d + 1) = insert (d + 1) (Finset.Icc c d) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨by omega, by omega⟩
      · exact ⟨h1, by omega⟩
  rw [h1, Finset.sum_insert (by
    intro hmem
    rw [Finset.mem_Icc] at hmem
    omega)]
  ring

/-- **The fibre tiling**: the sum over `k ∈ [c,d]` of the unit-square integrals is the integral
over the whole interval `[c-1+t, d+t]`. -/
lemma tf_fiberSum (ρ : ℝ) (hρ : 0 < ρ) (c d : ℤ) (hcd : c ≤ d) (t : ℝ) :
    (∑ k ∈ Finset.Icc c d, ∫ s in (0 : ℝ)..1, |tfG2 ρ ((k : ℝ) - 1 + t + s)|)
      = ∫ y in ((c : ℝ) - 1 + t)..((d : ℝ) + t), |tfG2 ρ y| := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have key : ∀ d : ℤ, c ≤ d →
      (∑ k ∈ Finset.Icc c d, ∫ s in (0 : ℝ)..1, |tfG2 ρ ((k : ℝ) - 1 + t + s)|)
        = ∫ y in ((c : ℝ) - 1 + t)..((d : ℝ) + t), |tfG2 ρ y| := by
    intro d hd
    induction d, hd using Int.leInduction with
    | base =>
        rw [Finset.Icc_self, Finset.sum_singleton]
        exact tf_fiber_term ρ c t
    | succ n hn ih =>
        rw [tf_sum_Icc_succ_top _ c n (by omega), ih, tf_fiber_term ρ (n + 1) t]
        have hcast : (((n + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        rw [show ((n : ℝ) + 1 - 1 + t) = (n : ℝ) + t from by ring]
        exact intervalIntegral.integral_add_adjacent_intervals
          ((continuous_abs_tfG2 ρ hρne).intervalIntegrable _ _)
          ((continuous_abs_tfG2 ρ hρne).intervalIntegrable _ _)
  exact key d hcd

/-- **The interior fibre bound**: the second-difference sum over any `ℤ`-interval is at most
`27/(5ρ³)` (twice the constant of the target). -/
theorem tf_interiorSum (ρ : ℝ) (hρ : 1 ≤ ρ) (c d : ℤ) (hcd : c ≤ d) :
    (∑ k ∈ Finset.Icc c d,
      |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|)
      ≤ 27 / (5 * ρ ^ 3) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hcdR : (c : ℝ) - 1 ≤ (d : ℝ) + 1 := by
    have h' : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
    linarith
  have hcd' : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
  calc (∑ k ∈ Finset.Icc c d,
        |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|)
      ≤ ∑ k ∈ Finset.Icc c d,
          ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, |tfG2 ρ ((k : ℝ) - 1 + t + s)| :=
        Finset.sum_le_sum (fun k _ => tf_secondDiff_le ρ hρne (k : ℝ))
    _ = ∫ t in (0 : ℝ)..1,
          ∑ k ∈ Finset.Icc c d, ∫ s in (0 : ℝ)..1, |tfG2 ρ ((k : ℝ) - 1 + t + s)| :=
        (intervalIntegral.integral_finsetSum
          (f := fun (k : ℤ) (t : ℝ) => ∫ s in (0 : ℝ)..1, |tfG2 ρ ((k : ℝ) - 1 + t + s)|)
          (fun k _ => (continuous_shift_abs_tfG2 ρ hρne (k : ℝ)).intervalIntegrable 0 1)).symm
    _ = ∫ t in (0 : ℝ)..1, ∫ y in ((c : ℝ) - 1 + t)..((d : ℝ) + t), |tfG2 ρ y| := by
        congr 1
        funext t
        exact tf_fiberSum ρ hρ0 c d hcd t
    _ ≤ ∫ t in (0 : ℝ)..1, ∫ y in ((c : ℝ) - 1)..((d : ℝ) + 1), |tfG2 ρ y| := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact (continuous_shift_interval (continuous_abs_tfG2 ρ hρne) ((c : ℝ) - 1)
            (d : ℝ)).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · intro t ht
          have ht0 : 0 ≤ t := ht.1
          have ht1 : t ≤ 1 := ht.2
          refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall (fun y => abs_nonneg (tfG2 ρ y)))
            ((continuous_abs_tfG2 ρ hρne).intervalIntegrable _ _)
    _ = ∫ y in ((c : ℝ) - 1)..((d : ℝ) + 1), |tfG2 ρ y| := by
        rw [intervalIntegral.integral_const]
        simp
    _ ≤ 27 / (5 * ρ ^ 3) := tfG2_bound ρ hρ _ _ hcdR

/-! ### The windowed second difference and the boundary corrections -/

lemma tf_if_nonneg {c : Prop} [Decidable c] {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (if c then x else 0) := by
  split <;> simp [hx]

lemma tf_if_nonneg' {c : Prop} [Decidable c] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (if c then (0 : ℝ) else x) := by
  split <;> simp [hx]

/-- The central term of the windowed second difference can be switched off only at `k = ±(K+1)`,
where its value is exactly `1/((K+1)²+ρ²)`. -/
lemma tf_corr1_le (ρ : ℝ) (hρ : 1 ≤ ρ) (K : ℕ) (k : ℤ)
    (hk : -(K : ℤ) - 1 ≤ k) (hk' : k ≤ (K : ℤ) + 1) :
    (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
      ≤ (if k = -(K : ℤ) - 1 then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0)
        + (if k = (K : ℤ) + 1 then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0) := by
  have hpos : (0 : ℝ) ≤ 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by positivity
  by_cases h : |k| ≤ (K : ℤ)
  · rw [if_pos h]
    linarith [tf_if_nonneg (c := k = -(K : ℤ) - 1) hpos,
      tf_if_nonneg (c := k = (K : ℤ) + 1) hpos]
  · rw [if_neg h]
    have hgt : (K : ℤ) < |k| := not_le.mp h
    rw [lt_abs] at hgt
    rcases hgt with hgt | hgt
    · have hkU : k = (K : ℤ) + 1 := by omega
      have hval : tfG ρ (k : ℝ) = 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
        rw [hkU]
        simp only [tfG]
        push_cast
        ring
      rw [hval, if_pos hkU]
      linarith [tf_if_nonneg (c := k = -(K : ℤ) - 1) hpos]
    · have hkL : k = -(K : ℤ) - 1 := by omega
      have hval : tfG ρ (k : ℝ) = 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
        rw [hkL]
        simp only [tfG]
        push_cast
        ring
      rw [hval, if_pos hkL]
      linarith [tf_if_nonneg (c := k = (K : ℤ) + 1) hpos]

/-- The left-neighbour term of the windowed second difference can be switched off only at
`k = -K-1` and `k = -K`, where its value is at most `1/((K+1)²+ρ²)`. -/
lemma tf_corr2_le (ρ : ℝ) (hρ : 1 ≤ ρ) (K : ℕ) (k : ℤ)
    (hk : -(K : ℤ) - 1 ≤ k) (hk' : k ≤ (K : ℤ) + 1) :
    (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
      ≤ (if k = -(K : ℤ) - 1 then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0)
        + (if k = -(K : ℤ) then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0) := by
  have hGnn : (0 : ℝ) ≤ 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by positivity
  have hle : 1 / (((K : ℝ) + 2) ^ 2 + ρ ^ 2) ≤ 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases h : |k - 1| ≤ (K : ℤ)
  · rw [if_pos h]
    linarith [tf_if_nonneg (c := k = -(K : ℤ) - 1) hGnn,
      tf_if_nonneg (c := k = -(K : ℤ)) hGnn]
  · rw [if_neg h]
    have hgt : (K : ℤ) < |k - 1| := not_le.mp h
    rw [lt_abs] at hgt
    rcases hgt with hgt | hgt
    · exfalso; omega
    · rcases (by omega : k = -(K : ℤ) - 1 ∨ k = -(K : ℤ)) with hkL | hkL
      · have hval : tfG ρ ((k : ℝ) - 1) = 1 / (((K : ℝ) + 2) ^ 2 + ρ ^ 2) := by
          rw [hkL]
          simp only [tfG]
          push_cast
          ring
        rw [hval, if_pos hkL]
        linarith [hle, tf_if_nonneg (c := k = -(K : ℤ)) hGnn]
      · have hval : tfG ρ ((k : ℝ) - 1) = 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
          rw [hkL]
          simp only [tfG]
          push_cast
          ring
        rw [hval, if_pos hkL]
        linarith [tf_if_nonneg (c := k = -(K : ℤ) - 1) hGnn]

/-- The right-neighbour term of the windowed second difference can be switched off only at
`k = K` and `k = K+1`, where its value is at most `1/((K+1)²+ρ²)`. -/
lemma tf_corr3_le (ρ : ℝ) (hρ : 1 ≤ ρ) (K : ℕ) (k : ℤ)
    (hk : -(K : ℤ) - 1 ≤ k) (hk' : k ≤ (K : ℤ) + 1) :
    (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1))
      ≤ (if k = (K : ℤ) then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0)
        + (if k = (K : ℤ) + 1 then 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) else 0) := by
  have hGnn : (0 : ℝ) ≤ 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by positivity
  have hle : 1 / (((K : ℝ) + 2) ^ 2 + ρ ^ 2) ≤ 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases h : |k + 1| ≤ (K : ℤ)
  · rw [if_pos h]
    linarith [tf_if_nonneg (c := k = (K : ℤ)) hGnn,
      tf_if_nonneg (c := k = (K : ℤ) + 1) hGnn]
  · rw [if_neg h]
    have hgt : (K : ℤ) < |k + 1| := not_le.mp h
    rw [lt_abs] at hgt
    rcases hgt with hgt | hgt
    · rcases (by omega : k = (K : ℤ) ∨ k = (K : ℤ) + 1) with hkU | hkU
      · have hval : tfG ρ ((k : ℝ) + 1) = 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) := by
          rw [hkU]
          simp only [tfG]
          push_cast
          ring
        rw [hval, if_pos hkU]
        linarith [tf_if_nonneg (c := k = (K : ℤ) + 1) hGnn]
      · have hval : tfG ρ ((k : ℝ) + 1) = 1 / (((K : ℝ) + 2) ^ 2 + ρ ^ 2) := by
          rw [hkU]
          simp only [tfG]
          push_cast
          ring
        rw [hval, if_pos hkU]
        linarith [hle, tf_if_nonneg (c := k = (K : ℤ)) hGnn]
    · exfalso; omega

/-- **The pointwise window bound**: the windowed second difference differs from the plain second
difference by the three "correction" terms, each of which is supported at the two ends of the
window. -/
lemma tf_window_pointwise (ρ : ℝ) (K : ℕ) (k : ℤ) :
    |(if |k| ≤ (K : ℤ) then tfG ρ (k : ℝ) else 0)
        - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) - 1) else 0)
        - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) + 1) else 0)|
      ≤ (1 / 2) * |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|
        + (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
        + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
        + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)) := by
  have h1 : (if |k| ≤ (K : ℤ) then tfG ρ (k : ℝ) else 0) - tfG ρ (k : ℝ)
      = -((if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))) := by
    by_cases h : |k| ≤ (K : ℤ) <;> simp [h]
  have h2 : (if |k - 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) - 1) else 0) - tfG ρ ((k : ℝ) - 1)
      = -((if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))) := by
    by_cases h : |k - 1| ≤ (K : ℤ) <;> simp [h]
  have h3 : (if |k + 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) + 1) else 0) - tfG ρ ((k : ℝ) + 1)
      = -((if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1))) := by
    by_cases h : |k + 1| ≤ (K : ℤ) <;> simp [h]
  have hid : (if |k| ≤ (K : ℤ) then tfG ρ (k : ℝ) else 0)
        - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) - 1) else 0)
        - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) + 1) else 0)
      = -((1 / 2) * (tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)))
        - (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
        + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
        + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)) := by
    linarith [h1, h2, h3]
  have hc1 : (0 : ℝ) ≤ (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ)) :=
    tf_if_nonneg' (tfG_nonneg ρ (k : ℝ))
  have hc2 : (0 : ℝ) ≤ (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)) :=
    tf_if_nonneg' (tfG_nonneg ρ ((k : ℝ) - 1))
  have hc3 : (0 : ℝ) ≤ (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)) :=
    tf_if_nonneg' (tfG_nonneg ρ ((k : ℝ) + 1))
  have htri : ∀ x y z w : ℝ, |x - y + z + w| ≤ |x| + |y| + |z| + |w| := by
    intro x y z w
    calc |x - y + z + w| = |(x - y) + (z + w)| := by
          rw [show x - y + z + w = (x - y) + (z + w) from by ring]
      _ ≤ |x - y| + |z + w| := abs_add_le _ _
      _ ≤ (|x| + |y|) + (|z| + |w|) := add_le_add (abs_sub _ _) (abs_add_le _ _)
      _ = |x| + |y| + |z| + |w| := by ring
  rw [hid]
  have key : |(-((1 / 2) * (tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1))))
        - (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
        + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
        + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1))|
      ≤ (1 / 2) * |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|
        + (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
        + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
        + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)) := by
    have h := htri
      (-((1 / 2) * (tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1))))
      (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
      ((1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)))
      ((1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)))
    rw [abs_neg] at h
    simp only [abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2, abs_of_nonneg hc3,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    exact h
  exact key

theorem telFiberBound (R ρ : ℝ) (hR : 1 ≤ R) (hρ : 1 ≤ ρ) (K : ℕ)
    (hK : ((K : ℝ)) ^ 2 + ρ ^ 2 ≤ R ^ 2)
    (hK' : R ^ 2 < (((K : ℝ)) + 1) ^ 2 + ρ ^ 2) :
    (∑ k ∈ Finset.Icc (-(K : ℤ) - 1) ((K : ℤ) + 1),
      |(if |k| ≤ (K : ℤ) then 1 / (((k : ℝ)) ^ 2 + ρ ^ 2) else 0)
        - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then 1 / (((k : ℝ) - 1) ^ 2 + ρ ^ 2) else 0)
        - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then 1 / (((k : ℝ) + 1) ^ 2 + ρ ^ 2) else 0)|)
      ≤ 27 / (10 * ρ ^ 3) + min (10 / R ^ 2) (4 / ρ ^ 2) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  set L : ℤ := -(K : ℤ) - 1 with hLdef
  set U : ℤ := (K : ℤ) + 1 with hUdef
  set G : ℝ := 1 / (((K : ℝ) + 1) ^ 2 + ρ ^ 2) with hGdef
  have hLU : L ≤ U := by rw [hLdef, hUdef]; omega
  have hmemL : L ∈ Finset.Icc L U := by rw [Finset.mem_Icc]; exact ⟨le_rfl, hLU⟩
  have hmemU : U ∈ Finset.Icc L U := by rw [Finset.mem_Icc]; exact ⟨hLU, le_rfl⟩
  have hmemL1 : (-(K : ℤ)) ∈ Finset.Icc L U := by
    rw [Finset.mem_Icc, hLdef, hUdef]; omega
  have hmemU1 : (K : ℤ) ∈ Finset.Icc L U := by
    rw [Finset.mem_Icc, hLdef, hUdef]; omega
  -- the three correction sums
  have hsum1 : (∑ k ∈ Finset.Icc L U, (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ)))
      ≤ 2 * G := by
    have hcongr : (∑ k ∈ Finset.Icc L U, (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ)))
        ≤ ∑ k ∈ Finset.Icc L U,
            ((if k = L then G else 0) + (if k = U then G else 0)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_Icc] at hk
      have h1 : -(K : ℤ) - 1 ≤ k := by rw [← hLdef]; exact hk.1
      have h2 : k ≤ (K : ℤ) + 1 := by rw [← hUdef]; exact hk.2
      have h3 := tf_corr1_le ρ hρ K k h1 h2
      rw [hGdef, hLdef, hUdef]
      exact h3
    calc (∑ k ∈ Finset.Icc L U, (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ)))
        ≤ ∑ k ∈ Finset.Icc L U, ((if k = L then G else 0) + (if k = U then G else 0)) := hcongr
      _ = (∑ k ∈ Finset.Icc L U, (if k = L then G else 0))
            + (∑ k ∈ Finset.Icc L U, (if k = U then G else 0)) := Finset.sum_add_distrib
      _ = 2 * G := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hmemL, if_pos hmemU]
          ring
  have hsum2 : (∑ k ∈ Finset.Icc L U, (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)))
      ≤ 2 * G := by
    have hcongr : (∑ k ∈ Finset.Icc L U,
          (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)))
        ≤ ∑ k ∈ Finset.Icc L U,
            ((if k = L then G else 0) + (if k = -(K : ℤ) then G else 0)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_Icc] at hk
      have h1 : -(K : ℤ) - 1 ≤ k := by rw [← hLdef]; exact hk.1
      have h2 : k ≤ (K : ℤ) + 1 := by rw [← hUdef]; exact hk.2
      have h3 := tf_corr2_le ρ hρ K k h1 h2
      rw [hGdef, hLdef]
      exact h3
    calc (∑ k ∈ Finset.Icc L U, (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)))
        ≤ ∑ k ∈ Finset.Icc L U, ((if k = L then G else 0) + (if k = -(K : ℤ) then G else 0)) := hcongr
      _ = (∑ k ∈ Finset.Icc L U, (if k = L then G else 0))
            + (∑ k ∈ Finset.Icc L U, (if k = -(K : ℤ) then G else 0)) := Finset.sum_add_distrib
      _ = 2 * G := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hmemL, if_pos hmemL1]
          ring
  have hsum3 : (∑ k ∈ Finset.Icc L U, (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)))
      ≤ 2 * G := by
    have hcongr : (∑ k ∈ Finset.Icc L U,
          (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)))
        ≤ ∑ k ∈ Finset.Icc L U,
            ((if k = (K : ℤ) then G else 0) + (if k = U then G else 0)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_Icc] at hk
      have h1 : -(K : ℤ) - 1 ≤ k := by rw [← hLdef]; exact hk.1
      have h2 : k ≤ (K : ℤ) + 1 := by rw [← hUdef]; exact hk.2
      have h3 := tf_corr3_le ρ hρ K k h1 h2
      rw [hGdef, hUdef]
      exact h3
    calc (∑ k ∈ Finset.Icc L U, (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)))
        ≤ ∑ k ∈ Finset.Icc L U, ((if k = (K : ℤ) then G else 0) + (if k = U then G else 0)) := hcongr
      _ = (∑ k ∈ Finset.Icc L U, (if k = (K : ℤ) then G else 0))
            + (∑ k ∈ Finset.Icc L U, (if k = U then G else 0)) := Finset.sum_add_distrib
      _ = 2 * G := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hmemU1, if_pos hmemU]
          ring
  have hdd : (∑ k ∈ Finset.Icc L U,
      |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|) ≤ 27 / (5 * ρ ^ 3) :=
    tf_interiorSum ρ hρ L U hLU
  have hpoint : ∀ k ∈ Finset.Icc L U,
      |(if |k| ≤ (K : ℤ) then tfG ρ (k : ℝ) else 0)
          - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) - 1) else 0)
          - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) + 1) else 0)|
        ≤ (1 / 2) * |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|
          + (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
          + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
          + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1)) :=
    fun k _ => tf_window_pointwise ρ K k
  have hGnn : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  have hR2pos : (0 : ℝ) < R ^ 2 := by
    have h1 : (0 : ℝ) < ((K : ℝ)) ^ 2 + ρ ^ 2 := by positivity
    linarith [hK]
  have hGR : G ≤ 1 / R ^ 2 := by
    rw [hGdef]
    rw [div_le_div_iff₀ (by positivity) hR2pos]
    linarith [le_of_lt hK']
  have hGρ : G ≤ 1 / ρ ^ 2 := by
    rw [hGdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((K : ℝ) + 1)]
  have hGmin : 4 * G ≤ min (10 / R ^ 2) (4 / ρ ^ 2) := by
    have hA : 4 * G ≤ 10 / R ^ 2 := by
      have h4 : (4 : ℝ) * G ≤ 4 * (1 / R ^ 2) := mul_le_mul_of_nonneg_left hGR (by norm_num)
      have h5 : (4 : ℝ) * (1 / R ^ 2) = 4 / R ^ 2 := by ring
      have h6 : (4 : ℝ) / R ^ 2 ≤ 10 / R ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith
    have hB : 4 * G ≤ 4 / ρ ^ 2 := by
      have h4 : (4 : ℝ) * G ≤ 4 * (1 / ρ ^ 2) := mul_le_mul_of_nonneg_left hGρ (by norm_num)
      have h5 : (4 : ℝ) * (1 / ρ ^ 2) = 4 / ρ ^ 2 := by ring
      linarith
    exact le_min hA hB
  calc (∑ k ∈ Finset.Icc L U,
        |(if |k| ≤ (K : ℤ) then tfG ρ (k : ℝ) else 0)
          - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) - 1) else 0)
          - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then tfG ρ ((k : ℝ) + 1) else 0)|)
      ≤ ∑ k ∈ Finset.Icc L U,
          ((1 / 2) * |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|
            + (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ))
            + (1 / 2) * (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1))
            + (1 / 2) * (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1))) :=
        Finset.sum_le_sum hpoint
    _ = (1 / 2) * (∑ k ∈ Finset.Icc L U,
            |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|)
          + (∑ k ∈ Finset.Icc L U, (if |k| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ (k : ℝ)))
          + (1 / 2) * (∑ k ∈ Finset.Icc L U,
              (if |k - 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) - 1)))
          + (1 / 2) * (∑ k ∈ Finset.Icc L U,
              (if |k + 1| ≤ (K : ℤ) then (0 : ℝ) else tfG ρ ((k : ℝ) + 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        try ring
    _ ≤ (1 / 2) * (27 / (5 * ρ ^ 3)) + (2 * G + (1 / 2) * (2 * G) + (1 / 2) * (2 * G)) := by
        have h1 : (1 / 2) * (∑ k ∈ Finset.Icc L U,
            |tfG ρ ((k : ℝ) + 1) - 2 * tfG ρ (k : ℝ) + tfG ρ ((k : ℝ) - 1)|)
            ≤ (1 / 2) * (27 / (5 * ρ ^ 3)) := mul_le_mul_of_nonneg_left hdd (by norm_num)
        linarith [h1, hsum1, hsum2, hsum3]
    _ ≤ 27 / (10 * ρ ^ 3) + min (10 / R ^ 2) (4 / ρ ^ 2) := by
        have h1 : (1 / 2) * (27 / (5 * ρ ^ 3)) = 27 / (10 * ρ ^ 3) := by
          field_simp
          ring
        have h2 : (2 : ℝ) * G + (1 / 2) * (2 * G) + (1 / 2) * (2 * G) = 4 * G := by ring
        rw [h1, h2]
        linarith [hGmin]

end

end Work.BoseRowsL.LatticeCoulomb
