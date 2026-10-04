import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

noncomputable section

/-!
# The phase data of the two-dimensional sphere theorem

We construct the six phase functions required by the `d = 2` branch of the proof.

The analytic content is the construction of a smooth, strictly increasing, bounded
function `phaseArgS : ℝ → ℝ` which is the identity on `[0, 3/4]`:

* `argWL`, `argWR` are the two flat weights: `argWL = 1` on `(-∞, -1/2]` and `0` on `[0, ∞)`;
  `argWR = 0` on `(-∞, 3/4]` and `1` on `[7/8, ∞)`;
* `argBL y = -1 + e^y/2` (a strictly increasing branch, bounded below by `-1`) is used where
  `argWL` is active, `argBR y = 1 - e^{6-8y}/4` (strictly increasing, values in `(3/4, 1)`) where
  `argWR` is active;
* `phaseArgS` is the convex combination
  `phaseArgS = argWL * argBL + (1 - argWL - argWR) * id + argWR * argBR`.

On `[0, 3/4]` both weights vanish, so `phaseArgS = id`; the two branches keep `phaseArgS` inside
`(-1, 1)`; and the derivative is positive everywhere because each weight is constant wherever its
branch would violate the corresponding inequality.

Given `S`, the required `Ξ` (resp. `ϑ`) is `arcsin ∘ S ∘ (· / 2a)` (resp. `g`), and the remaining
functions are flat steps (`Real.smoothTransition`).
-/

/-! ## The auxiliary bounded strictly increasing function -/

/-- Left branch of the interpolation: strictly increasing, values in `(-1, ∞)`. -/
def argBL (y : ℝ) : ℝ := -1 + Real.exp y / 2

/-- Right branch of the interpolation: strictly increasing, values in `(3/4, 1)`. -/
def argBR (y : ℝ) : ℝ := 1 - Real.exp (6 - 8 * y) / 4

/-- Left weight: `1` on `(-∞, -1/2]`, `0` on `[0, ∞)`. -/
def argWL (y : ℝ) : ℝ := Real.smoothTransition (-2 * y)

/-- Right weight: `0` on `(-∞, 3/4]`, `1` on `[7/8, ∞)`. -/
def argWR (y : ℝ) : ℝ := Real.smoothTransition (8 * y - 6)

/-- The explicit bounded strictly increasing function, equal to the identity on `[0, 3/4]`. -/
def phaseArgS : ℝ → ℝ := argWL * argBL + (1 - argWL - argWR) * id + argWR * argBR

/-- The (rearranged) derivative of `phaseArgS`. -/
def phaseArgSd (y : ℝ) : ℝ :=
  deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
    + argWL y * deriv argBL y + argWR y * deriv argBR y + (1 - argWL y - argWR y)

/-! ### Elementary properties of the weights and branches -/

lemma argWL_eq_one_of_le {y : ℝ} (h : y ≤ -1/2) : argWL y = 1 := by
  unfold argWL
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma argWL_eq_zero_of_nonneg {y : ℝ} (h : 0 ≤ y) : argWL y = 0 := by
  unfold argWL
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma argWL_nonneg (y : ℝ) : 0 ≤ argWL y := Real.smoothTransition.nonneg _

lemma argWL_le_one (y : ℝ) : argWL y ≤ 1 := Real.smoothTransition.le_one _

lemma argWL_lt_one_of_lt {y : ℝ} (h : -1/2 < y) : argWL y < 1 := by
  unfold argWL
  exact Real.smoothTransition.lt_one_of_lt_one (by linarith)

lemma argWR_eq_zero_of_le {y : ℝ} (h : y ≤ 3/4) : argWR y = 0 := by
  unfold argWR
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma argWR_eq_one_of_le {y : ℝ} (h : 7/8 ≤ y) : argWR y = 1 := by
  unfold argWR
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma argWR_nonneg (y : ℝ) : 0 ≤ argWR y := Real.smoothTransition.nonneg _

lemma argWR_le_one (y : ℝ) : argWR y ≤ 1 := Real.smoothTransition.le_one _

lemma argWR_lt_one_of_lt {y : ℝ} (h : y < 7/8) : argWR y < 1 := by
  unfold argWR
  exact Real.smoothTransition.lt_one_of_lt_one (by linarith)

lemma antitone_argWL : Antitone argWL := by
  intro x y hxy
  unfold argWL
  exact Real.smoothTransition.monotone (by linarith)

lemma monotone_argWR : Monotone argWR := by
  intro x y hxy
  unfold argWR
  exact Real.smoothTransition.monotone (by linarith)

lemma deriv_argWL_nonpos (y : ℝ) : deriv argWL y ≤ 0 := by
  simpa using antitone_argWL.deriv_nonpos (x := y)

lemma deriv_argWR_nonneg (y : ℝ) : 0 ≤ deriv argWR y := by
  simpa using monotone_argWR.deriv_nonneg (x := y)

lemma deriv_argWL_eq_zero_of_lt {y : ℝ} (h : y < -1/2) : deriv argWL y = 0 := by
  have hev : argWL =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with z hz
    exact argWL_eq_one_of_le hz.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_argWL_eq_zero_of_pos {y : ℝ} (h : 0 < y) : deriv argWL y = 0 := by
  have hev : argWL =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with z hz
    exact argWL_eq_zero_of_nonneg hz.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_argWR_eq_zero_of_lt {y : ℝ} (h : y < 3/4) : deriv argWR y = 0 := by
  have hev : argWR =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with z hz
    exact argWR_eq_zero_of_le hz.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_argWR_eq_zero_of_gt {y : ℝ} (h : 7/8 < y) : deriv argWR y = 0 := by
  have hev : argWR =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with z hz
    exact argWR_eq_one_of_le hz.le
  rw [hev.deriv_eq, deriv_const]

lemma contDiff_argWL : ContDiff ℝ ∞ argWL := by
  unfold argWL; fun_prop

lemma contDiff_argWR : ContDiff ℝ ∞ argWR := by
  unfold argWR; fun_prop

lemma contDiff_argBL : ContDiff ℝ ∞ argBL := by
  unfold argBL; fun_prop

lemma contDiff_argBR : ContDiff ℝ ∞ argBR := by
  unfold argBR; fun_prop

lemma hasDerivAt_argBL (y : ℝ) : HasDerivAt argBL (Real.exp y / 2) y := by
  unfold argBL
  have h : HasDerivAt (fun z : ℝ => Real.exp z / 2) (Real.exp y / 2) y :=
    (Real.hasDerivAt_exp y).div_const 2
  exact h.const_add (-1)

lemma deriv_argBL (y : ℝ) : deriv argBL y = Real.exp y / 2 := (hasDerivAt_argBL y).deriv

lemma deriv_argBL_pos (y : ℝ) : 0 < deriv argBL y := by
  rw [deriv_argBL]; positivity

lemma hasDerivAt_argBR (y : ℝ) : HasDerivAt argBR (2 * Real.exp (6 - 8 * y)) y := by
  unfold argBR
  have h1 : HasDerivAt (fun z : ℝ => 6 - 8 * z) (-8) y := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id y).const_mul (8)).const_sub 6
  have h2 : HasDerivAt (Real.exp ∘ fun z : ℝ => 6 - 8 * z) (Real.exp (6 - 8 * y) * (-8)) y :=
    (Real.hasDerivAt_exp (6 - 8 * y)).comp y h1
  rw [show (Real.exp ∘ fun z : ℝ => 6 - 8 * z) = fun z => Real.exp (6 - 8 * z) from rfl] at h2
  have h3 : HasDerivAt (fun z : ℝ => 1 - Real.exp (6 - 8 * z) / 4)
      (2 * Real.exp (6 - 8 * y)) y := by
    have h := (h2.div_const 4).const_sub 1
    have hd : -((Real.exp (6 - 8 * y) * (-8)) / 4) = 2 * Real.exp (6 - 8 * y) := by ring
    rw [hd] at h
    exact h
  exact h3

lemma deriv_argBR (y : ℝ) : deriv argBR y = 2 * Real.exp (6 - 8 * y) := (hasDerivAt_argBR y).deriv

lemma deriv_argBR_pos (y : ℝ) : 0 < deriv argBR y := by
  rw [deriv_argBR]; positivity

/-! ### The two pointwise inequalities relating the branches to the identity -/

lemma exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : (1 : ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos x) h1).mpr h2

/-- `argBL` lies below the identity on `[-1/2, 0]`. -/
lemma argBL_le_self_of_mem {y : ℝ} (h : y ∈ Icc (-1/2) 0) : argBL y ≤ y := by
  have hy1 : y ≤ 0 := h.2
  have hx : 0 ≤ -y := by linarith
  have hx1 : -y ≤ 1/2 := by linarith [h.1]
  have hexp : Real.exp y ≤ (1 + (-y))⁻¹ := by
    simpa using exp_neg_le_inv_one_add hx
  have hle : (1 + (-y))⁻¹ ≤ 2 * (y + 1) := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < 1 + (-y))]
    nlinarith [sq_nonneg (-y), hx1]
  calc argBL y = -1 + Real.exp y / 2 := rfl
    _ ≤ -1 + ((1 + (-y))⁻¹) / 2 := by linarith
    _ ≤ -1 + (2 * (y + 1)) / 2 := by linarith
    _ = y := by ring

/-- `argBR` lies above the identity on `[3/4, 7/8]`. -/
lemma self_le_argBR_of_mem {y : ℝ} (h : y ∈ Icc (3/4) (7/8)) : y ≤ argBR y := by
  have hu0 : 0 ≤ y - 3/4 := by linarith [h.1]
  have hu1 : y - 3/4 ≤ 1/8 := by linarith [h.2]
  have hpos : 0 < 1 + (8 * y - 6) := by linarith [h.1]
  have hexp : Real.exp (6 - 8 * y) ≤ (1 + (8 * y - 6))⁻¹ := by
    have := exp_neg_le_inv_one_add (x := 8 * y - 6) (by linarith [h.1])
    simpa only [neg_sub] using this
  have hle : (1 + (8 * y - 6))⁻¹ ≤ 4 * (1 - y) := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [hu0, hu1]
  calc y = 1 - (4 * (1 - y)) / 4 := by ring
    _ ≤ 1 - (1 + (8 * y - 6))⁻¹ / 4 := by linarith
    _ ≤ 1 - Real.exp (6 - 8 * y) / 4 := by linarith
    _ = argBR y := rfl

lemma deriv_argWL_mul_nonneg (y : ℝ) : 0 ≤ deriv argWL y * (argBL y - y) := by
  rcases lt_trichotomy y (-1/2) with h | h | h
  · rw [deriv_argWL_eq_zero_of_lt h, zero_mul]
  · have hbl : argBL y ≤ y := argBL_le_self_of_mem ⟨by linarith, by linarith⟩
    have hd : deriv argWL y ≤ 0 := deriv_argWL_nonpos y
    nlinarith
  · by_cases hy : y < 0
    · have hbl : argBL y ≤ y := argBL_le_self_of_mem ⟨le_of_lt h, le_of_lt hy⟩
      have hd : deriv argWL y ≤ 0 := deriv_argWL_nonpos y
      nlinarith
    · rw [not_lt] at hy
      rcases eq_or_lt_of_le hy with h0 | h0
      · have hbl : argBL y - y = -1/2 := by rw [← h0]; norm_num [argBL]
        rw [hbl]
        have hd : deriv argWL y ≤ 0 := deriv_argWL_nonpos y
        nlinarith
      · rw [deriv_argWL_eq_zero_of_pos h0, zero_mul]

lemma deriv_argWR_mul_nonneg (y : ℝ) : 0 ≤ deriv argWR y * (argBR y - y) := by
  rcases lt_trichotomy y (3/4) with h | h | h
  · rw [deriv_argWR_eq_zero_of_lt h, zero_mul]
  · have hbr : argBR y - y = 0 := by rw [h]; norm_num [argBR]
    rw [hbr, mul_zero]
  · rcases lt_trichotomy y (7/8) with h2 | h2 | h2
    · have hbr : y ≤ argBR y := self_le_argBR_of_mem ⟨le_of_lt h, le_of_lt h2⟩
      have hd : 0 ≤ deriv argWR y := deriv_argWR_nonneg y
      nlinarith
    · have hbr : y ≤ argBR y := by
        rw [h2]; exact self_le_argBR_of_mem ⟨by norm_num, le_rfl⟩
      have hd : 0 ≤ deriv argWR y := deriv_argWR_nonneg y
      nlinarith
    · rw [deriv_argWR_eq_zero_of_gt h2, zero_mul]

/-! ### The derivative of `phaseArgS` -/

lemma deriv_phaseArgS (y : ℝ) : deriv phaseArgS y = phaseArgSd y := by
  have hWL : HasDerivAt argWL (deriv argWL y) y :=
    (contDiff_argWL.differentiable (by simp) y).hasDerivAt
  have hWR : HasDerivAt argWR (deriv argWR y) y :=
    (contDiff_argWR.differentiable (by simp) y).hasDerivAt
  have hBL : HasDerivAt argBL (deriv argBL y) y :=
    (contDiff_argBL.differentiable (by simp) y).hasDerivAt
  have hBR : HasDerivAt argBR (deriv argBR y) y :=
    (contDiff_argBR.differentiable (by simp) y).hasDerivAt
  have h1 : HasDerivAt (argWL * argBL)
      (deriv argWL y * argBL y + argWL y * deriv argBL y) y := hWL.mul hBL
  have h2 : HasDerivAt ((1 - argWL - argWR) * id)
      ((0 - deriv argWL y - deriv argWR y) * id y + ((1 - argWL - argWR) : ℝ → ℝ) y * 1) y :=
    (((hasDerivAt_const y 1).sub hWL).sub hWR).mul (hasDerivAt_id y)
  have h3 : HasDerivAt (argWR * argBR)
      (deriv argWR y * argBR y + argWR y * deriv argBR y) y := hWR.mul hBR
  have htot : HasDerivAt phaseArgS
      ((deriv argWL y * argBL y + argWL y * deriv argBL y)
        + ((0 - deriv argWL y - deriv argWR y) * id y + ((1 - argWL - argWR) : ℝ → ℝ) y * 1)
        + (deriv argWR y * argBR y + argWR y * deriv argBR y)) y := by
    unfold phaseArgS
    exact (h1.add h2).add h3
  rw [htot.deriv]
  unfold phaseArgSd
  simp only [id_eq, Pi.sub_apply, Pi.one_apply, zero_sub]
  ring

lemma phaseArgSd_pos (y : ℝ) : 0 < phaseArgSd y := by
  have h1 : 0 ≤ deriv argWL y * (argBL y - y) := deriv_argWL_mul_nonneg y
  have h2 : 0 ≤ deriv argWR y * (argBR y - y) := deriv_argWR_mul_nonneg y
  have h3 : 0 ≤ argWL y * deriv argBL y := mul_nonneg (argWL_nonneg y) (deriv_argBL_pos y).le
  have h4 : 0 ≤ argWR y * deriv argBR y := mul_nonneg (argWR_nonneg y) (deriv_argBR_pos y).le
  rcases le_or_gt y (-1/2) with hy | hy
  · have hwL : argWL y = 1 := argWL_eq_one_of_le hy
    have hwR : argWR y = 0 := argWR_eq_zero_of_le (by linarith)
    have e : phaseArgSd y = deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
        + deriv argBL y + 0 + 0 := by
      unfold phaseArgSd; rw [hwL, hwR]; ring
    rw [e]
    nlinarith [h1, h2, deriv_argBL_pos y]
  · rcases lt_or_ge y 0 with hy0 | hy0
    · have hwR : argWR y = 0 := argWR_eq_zero_of_le (by linarith)
      have hwL : argWL y < 1 := argWL_lt_one_of_lt hy
      have e : phaseArgSd y = deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
          + argWL y * deriv argBL y + 0 + (1 - argWL y) := by
        unfold phaseArgSd; rw [hwR]; ring
      rw [e]
      nlinarith [h1, h2, h3]
    · rcases le_or_gt y (3/4) with hy34 | hy34
      · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg hy0
        have hwR : argWR y = 0 := argWR_eq_zero_of_le hy34
        have e : phaseArgSd y = deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
            + 0 + 0 + 1 := by
          unfold phaseArgSd; rw [hwL, hwR]; ring
        rw [e]
        nlinarith [h1, h2]
      · rcases lt_or_ge y (7/8) with hy78 | hy78
        · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg (by linarith)
          have hwR : argWR y < 1 := argWR_lt_one_of_lt hy78
          have e : phaseArgSd y = deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
              + 0 + argWR y * deriv argBR y + (1 - argWR y) := by
            unfold phaseArgSd; rw [hwL]; ring
          rw [e]
          nlinarith [h1, h2, h4]
        · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg (by linarith)
          have hwR : argWR y = 1 := argWR_eq_one_of_le hy78
          have e : phaseArgSd y = deriv argWL y * (argBL y - y) + deriv argWR y * (argBR y - y)
              + 0 + deriv argBR y + 0 := by
            unfold phaseArgSd; rw [hwL, hwR]; ring
          rw [e]
          nlinarith [h1, h2, deriv_argBR_pos y]

lemma deriv_phaseArgS_pos (y : ℝ) : 0 < deriv phaseArgS y := by
  rw [deriv_phaseArgS]; exact phaseArgSd_pos y

/-! ### Value and range properties of `phaseArgS` -/

lemma phaseArgS_eq_self {y : ℝ} (h : y ∈ Icc 0 (3/4)) : phaseArgS y = y := by
  have h1 : argWL y = 0 := argWL_eq_zero_of_nonneg h.1
  have h2 : argWR y = 0 := argWR_eq_zero_of_le h.2
  unfold phaseArgS
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, h1, h2]
  ring

lemma argBL_mem_of_nonpos {y : ℝ} (h : y ≤ 0) : -1 < argBL y ∧ argBL y < 1 := by
  have he : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr h
  constructor
  · unfold argBL; have := Real.exp_pos y; linarith
  · unfold argBL; linarith

lemma argBR_mem_of_lt {y : ℝ} (h : 3/4 < y) : 3/4 < argBR y ∧ argBR y < 1 := by
  have h6 : 6 - 8 * y < 0 := by linarith
  have he : Real.exp (6 - 8 * y) < 1 := Real.exp_lt_one_iff.mpr h6
  constructor
  · unfold argBR; have := Real.exp_pos (6 - 8 * y); linarith
  · unfold argBR; have := Real.exp_pos (6 - 8 * y); linarith

lemma convex_combo_mem {a u v : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hu : -1 < u) (hu' : u < 1)
    (hv : -1 < v) (hv' : v < 1) :
    -1 < a * u + (1 - a) * v ∧ a * u + (1 - a) * v < 1 := by
  have h1a : 0 ≤ 1 - a := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hu.le ha0, mul_le_mul_of_nonneg_left hv.le h1a]
  · nlinarith [mul_le_mul_of_nonneg_left hu'.le ha0, mul_le_mul_of_nonneg_left hv'.le h1a]

lemma phaseArgS_mem (y : ℝ) : -1 < phaseArgS y ∧ phaseArgS y < 1 := by
  rcases le_or_gt y (-1/2) with hy | hy
  · have hwL : argWL y = 1 := argWL_eq_one_of_le hy
    have hwR : argWR y = 0 := argWR_eq_zero_of_le (by linarith)
    have hb := argBL_mem_of_nonpos (by linarith : y ≤ 0)
    have e : phaseArgS y = argBL y := by
      unfold phaseArgS
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, hwL, hwR]
      ring
    rw [e]; exact hb
  · rcases lt_or_ge y 0 with hy0 | hy0
    · have hwR : argWR y = 0 := argWR_eq_zero_of_le (by linarith)
      have hb := argBL_mem_of_nonpos (le_of_lt hy0)
      have e : phaseArgS y = argWL y * argBL y + (1 - argWL y) * y := by
        unfold phaseArgS
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, hwR]
        ring
      rw [e]
      exact convex_combo_mem (argWL_nonneg y) (argWL_le_one y) hb.1 hb.2 (by linarith) (by linarith)
    · rcases le_or_gt y (3/4) with hy34 | hy34
      · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg hy0
        have hwR : argWR y = 0 := argWR_eq_zero_of_le hy34
        have e : phaseArgS y = y := by
          unfold phaseArgS
          simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, hwL, hwR]
          ring
        rw [e]; constructor <;> linarith
      · have hb := argBR_mem_of_lt hy34
        rcases lt_or_ge y (7/8) with hy78 | hy78
        · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg (by linarith)
          have e : phaseArgS y = argWR y * argBR y + (1 - argWR y) * y := by
            unfold phaseArgS
            simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, hwL]
            ring
          rw [e]
          exact convex_combo_mem (argWR_nonneg y) (argWR_le_one y) (by linarith [hb.1]) hb.2
            (by linarith) (by linarith)
        · have hwL : argWL y = 0 := argWL_eq_zero_of_nonneg (by linarith)
          have hwR : argWR y = 1 := argWR_eq_one_of_le hy78
          have e : phaseArgS y = argBR y := by
            unfold phaseArgS
            simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Pi.one_apply, hwL, hwR]
            ring
          rw [e]; exact ⟨by linarith [hb.1], hb.2⟩

lemma contDiff_phaseArgS : ContDiff ℝ ∞ phaseArgS := by
  unfold phaseArgS
  have h1 : ContDiff ℝ ∞ ((1 : ℝ → ℝ) - argWL - argWR) :=
    (contDiff_const.sub contDiff_argWL).sub contDiff_argWR
  exact ((contDiff_argWL.mul contDiff_argBL).add (h1.mul contDiff_id)).add
    (contDiff_argWR.mul contDiff_argBR)

lemma phaseArgS_nonneg {y : ℝ} (h : 0 ≤ y) : 0 ≤ phaseArgS y := by
  have hmono : StrictMono phaseArgS :=
    strictMono_of_deriv_pos fun z => deriv_phaseArgS_pos z
  have h0 : phaseArgS 0 = 0 := by
    rw [phaseArgS_eq_self (by constructor <;> norm_num)]
  calc (0 : ℝ) = phaseArgS 0 := h0.symm
    _ ≤ phaseArgS y := hmono.monotone (by linarith)

/-! ## The `arcsin`-extension of a suitable argument map -/

/-- `arcsin ∘ S ∘ (· / 2α)`. -/
def phaseArc (S : ℝ → ℝ) (α : ℝ) : ℝ → ℝ := fun r => Real.arcsin (S (r / (2 * α)))

lemma contDiff_phaseArc {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    (hrange : ∀ y : ℝ, -1 < S y ∧ S y < 1) (α : ℝ) : ContDiff ℝ ∞ (phaseArc S α) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  have h1 : S (r / (2 * α)) ≠ -1 := ne_of_gt (hrange _).1
  have h2 : S (r / (2 * α)) ≠ 1 := ne_of_lt (hrange _).2
  have hinner : ContDiffAt ℝ ∞ (fun r : ℝ => S (r / (2 * α))) r :=
    hS.contDiffAt.comp r (by fun_prop)
  exact (Real.contDiffAt_arcsin h1 h2).comp r hinner

lemma deriv_phaseArc_pos {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    (hrange : ∀ y : ℝ, -1 < S y ∧ S y < 1) (hpos : ∀ y : ℝ, 0 < deriv S y)
    {α : ℝ} (hα : 0 < α) (r : ℝ) : 0 < deriv (phaseArc S α) r := by
  have hdiff : DifferentiableAt ℝ S (r / (2 * α)) := hS.differentiable (by simp) _
  have hinner : HasDerivAt (fun r : ℝ => r / (2 * α)) ((2 * α)⁻¹) r := by
    simpa using (hasDerivAt_id r).div_const (2 * α)
  have hcomp : HasDerivAt (fun r : ℝ => S (r / (2 * α)))
      (deriv S (r / (2 * α)) * (2 * α)⁻¹) r := hdiff.hasDerivAt.comp r hinner
  have h1 : S (r / (2 * α)) ≠ -1 := ne_of_gt (hrange _).1
  have h2 : S (r / (2 * α)) ≠ 1 := ne_of_lt (hrange _).2
  have houter : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (S (r / (2 * α))) ^ 2))
      (S (r / (2 * α))) := Real.hasDerivAt_arcsin h1 h2
  have htot := houter.comp r hcomp
  rw [show (Real.arcsin ∘ fun r : ℝ => S (r / (2 * α))) = phaseArc S α from rfl] at htot
  rw [htot.deriv]
  have hs : 0 < Real.sqrt (1 - (S (r / (2 * α))) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have hb := hrange (r / (2 * α))
    nlinarith
  have h2α : 0 < (2 * α)⁻¹ := inv_pos.mpr (by linarith)
  have hp := hpos (r / (2 * α))
  exact mul_pos (div_pos one_pos hs) (mul_pos hp h2α)

lemma phaseArc_eq_arcsin {S : ℝ → ℝ} (hid : ∀ y : ℝ, 0 ≤ y → y ≤ 3/4 → S y = y)
    {α r : ℝ} (hα : 0 < α) (hr0 : 0 ≤ r) (hr1 : r ≤ 3 * α / 2) :
    phaseArc S α r = Real.arcsin (r / (2 * α)) := by
  have h : S (r / (2 * α)) = r / (2 * α) := by
    apply hid
    · positivity
    · rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * α)]
      linarith
  rw [phaseArc, h]

lemma phaseArc_lt_pi (S : ℝ → ℝ) (α r : ℝ) : phaseArc S α r < Real.pi := by
  have h := Real.arcsin_le_pi_div_two (S (r / (2 * α)))
  rw [phaseArc]
  linarith [Real.pi_pos]

lemma phaseArc_bounds {S : ℝ → ℝ} (hnn : ∀ y : ℝ, 0 ≤ y → 0 ≤ S y)
    {α r : ℝ} (hα : 0 < α) (hr0 : 0 ≤ r) :
    0 ≤ phaseArc S α r ∧ phaseArc S α r ≤ Real.pi / 2 := by
  have hm : 0 ≤ r / (2 * α) := by positivity
  have hS0 : 0 ≤ S (r / (2 * α)) := hnn _ hm
  constructor
  · rw [phaseArc]; exact Real.arcsin_nonneg.mpr hS0
  · rw [phaseArc]; exact Real.arcsin_le_pi_div_two _

/-! ## The phase data -/

theorem phase_data
    {a g D e S : ℝ} (ha : 0 < a) (hg : 0 < g) (he : 0 < e) (hS : 0 < S) :
    ∃ Ξ ϑ Θ β ψp ψq : ℝ → ℝ,
      ContDiff ℝ ∞ Ξ ∧ ContDiff ℝ ∞ ϑ ∧ ContDiff ℝ ∞ Θ ∧
      ContDiff ℝ ∞ β ∧ ContDiff ℝ ∞ ψp ∧ ContDiff ℝ ∞ ψq ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 3 * a / 4 → Ξ r = Real.arcsin (r / (2 * a))) ∧
      (∀ r : ℝ, 0 < deriv Ξ r) ∧
      (∀ r : ℝ, Ξ r < Real.pi) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 3 * g / 2 → ϑ r = Real.arcsin (r / (2 * g))) ∧
      (∀ r : ℝ, 0 ≤ r → 0 ≤ ϑ r ∧ ϑ r ≤ Real.pi / 2) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 3 * g / 2 + e → 0 < deriv ϑ r) ∧
      (∀ t : ℝ, 0 < deriv Θ t) ∧
      (∀ t : ℝ, Ξ (a + t) ≤ Θ t) ∧
      (∀ t : ℝ, Θ t ≤ Real.pi - ϑ (3 * g / 2 + e)) ∧
      (∀ t : ℝ, t ≤ 0 → β t = 0) ∧
      (∀ t : ℝ, S ≤ t → β t = 1) ∧
      (∀ t : ℝ, 0 ≤ β t ∧ β t ≤ 1) ∧
      (∀ r : ℝ, r ≤ 3 * a / 4 → ψp r = 1) ∧
      (∀ r : ℝ, a ≤ r → ψp r = 0) ∧
      (∀ r : ℝ, 0 ≤ ψp r ∧ ψp r ≤ 1) ∧
      (∀ r : ℝ, r ≤ 3 * g / 2 → ψq r = 1) ∧
      (∀ r : ℝ, 3 * g / 2 + e ≤ r → ψq r = 0) ∧
      (∀ r : ℝ, 0 ≤ ψq r ∧ ψq r ≤ 1) := by
  have hSsm : ContDiff ℝ ∞ phaseArgS := contDiff_phaseArgS
  have hSrange : ∀ y : ℝ, -1 < phaseArgS y ∧ phaseArgS y < 1 := phaseArgS_mem
  have hSpos : ∀ y : ℝ, 0 < deriv phaseArgS y := deriv_phaseArgS_pos
  have hSid : ∀ y : ℝ, 0 ≤ y → y ≤ 3 / 4 → phaseArgS y = y :=
    fun y h0 h1 => phaseArgS_eq_self ⟨h0, h1⟩
  have hSnn : ∀ y : ℝ, 0 ≤ y → 0 ≤ phaseArgS y := fun y h => phaseArgS_nonneg h
  have hΞsm : ContDiff ℝ ∞ (phaseArc phaseArgS a) := contDiff_phaseArc hSsm hSrange a
  have hΞd : ∀ r : ℝ, 0 < deriv (phaseArc phaseArgS a) r :=
    fun r => deriv_phaseArc_pos hSsm hSrange hSpos ha r
  have hΞπ : ∀ r : ℝ, phaseArc phaseArgS a r < Real.pi := fun r => phaseArc_lt_pi _ _ _
  have hΞarc : ∀ r : ℝ, 0 ≤ r → r ≤ 3 * a / 4 →
      phaseArc phaseArgS a r = Real.arcsin (r / (2 * a)) :=
    fun r h0 h1 => phaseArc_eq_arcsin hSid ha h0 (by linarith)
  have hϑsm : ContDiff ℝ ∞ (phaseArc phaseArgS g) := contDiff_phaseArc hSsm hSrange g
  have hϑd : ∀ r : ℝ, 0 < deriv (phaseArc phaseArgS g) r :=
    fun r => deriv_phaseArc_pos hSsm hSrange hSpos hg r
  have hϑarc : ∀ r : ℝ, 0 ≤ r → r ≤ 3 * g / 2 →
      phaseArc phaseArgS g r = Real.arcsin (r / (2 * g)) :=
    fun r h0 h1 => phaseArc_eq_arcsin hSid hg h0 (by linarith)
  have hϑb : ∀ r : ℝ, 0 ≤ r →
      0 ≤ phaseArc phaseArgS g r ∧ phaseArc phaseArgS g r ≤ Real.pi / 2 :=
    fun r h0 => phaseArc_bounds hSnn hg h0
  have hΘsm : ContDiff ℝ ∞ (fun t : ℝ => phaseArc phaseArgS a (a + t)) :=
    hΞsm.comp (by fun_prop)
  have hΞdiff : Differentiable ℝ (phaseArc phaseArgS a) := hΞsm.differentiable (by simp)
  have hΘd : ∀ t : ℝ, 0 < deriv (fun t : ℝ => phaseArc phaseArgS a (a + t)) t := by
    intro t
    have hcomp : HasDerivAt (fun t : ℝ => phaseArc phaseArgS a (a + t))
        (deriv (phaseArc phaseArgS a) (a + t) * 1) t := by
      have hinner : HasDerivAt (fun t : ℝ => a + t) 1 t := by
        simpa using (hasDerivAt_id t).const_add a
      exact (hΞdiff (a + t)).hasDerivAt.comp t hinner
    rw [hcomp.deriv]
    simpa using hΞd (a + t)
  have hΞΘ : ∀ t : ℝ, phaseArc phaseArgS a (a + t) ≤ phaseArc phaseArgS a (a + t) :=
    fun t => le_rfl
  have hΘϑ : ∀ t : ℝ, phaseArc phaseArgS a (a + t) ≤
      Real.pi - phaseArc phaseArgS g (3 * g / 2 + e) := by
    intro t
    have h1 : phaseArc phaseArgS a (a + t) ≤ Real.pi / 2 :=
      Real.arcsin_le_pi_div_two _
    have h2 : phaseArc phaseArgS g (3 * g / 2 + e) ≤ Real.pi / 2 :=
      (hϑb (3 * g / 2 + e) (by linarith)).2
    linarith
  have hβsm : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t / S)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hβ0 : ∀ t : ℝ, t ≤ 0 → Real.smoothTransition (t / S) = 0 := by
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hS.le)
  have hβ1 : ∀ t : ℝ, S ≤ t → Real.smoothTransition (t / S) = 1 := by
    intro t ht
    exact Real.smoothTransition.one_of_one_le (by rw [one_le_div hS]; exact ht)
  have hβr : ∀ t : ℝ, 0 ≤ Real.smoothTransition (t / S) ∧ Real.smoothTransition (t / S) ≤ 1 :=
    fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hψpsm : ContDiff ℝ ∞ (fun r : ℝ => Real.smoothTransition ((a - r) / (a / 4))) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hψp1 : ∀ r : ℝ, r ≤ 3 * a / 4 → Real.smoothTransition ((a - r) / (a / 4)) = 1 := by
    intro r hr
    refine Real.smoothTransition.one_of_one_le ?_
    rw [one_le_div (by linarith : (0 : ℝ) < a / 4)]
    linarith
  have hψp0 : ∀ r : ℝ, a ≤ r → Real.smoothTransition ((a - r) / (a / 4)) = 0 := by
    intro r hr
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hψpr : ∀ r : ℝ, 0 ≤ Real.smoothTransition ((a - r) / (a / 4)) ∧
      Real.smoothTransition ((a - r) / (a / 4)) ≤ 1 :=
    fun r => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hψqsm : ContDiff ℝ ∞ (fun r : ℝ => Real.smoothTransition ((3 * g / 2 + e - r) / e)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hψq1 : ∀ r : ℝ, r ≤ 3 * g / 2 →
      Real.smoothTransition ((3 * g / 2 + e - r) / e) = 1 := by
    intro r hr
    refine Real.smoothTransition.one_of_one_le ?_
    rw [one_le_div he]
    linarith
  have hψq0 : ∀ r : ℝ, 3 * g / 2 + e ≤ r →
      Real.smoothTransition ((3 * g / 2 + e - r) / e) = 0 := by
    intro r hr
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) he.le)
  have hψqr : ∀ r : ℝ, 0 ≤ Real.smoothTransition ((3 * g / 2 + e - r) / e) ∧
      Real.smoothTransition ((3 * g / 2 + e - r) / e) ≤ 1 :=
    fun r => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  exact ⟨phaseArc phaseArgS a, phaseArc phaseArgS g, fun t : ℝ => phaseArc phaseArgS a (a + t),
    fun t : ℝ => Real.smoothTransition (t / S), fun r : ℝ => Real.smoothTransition ((a - r) / (a / 4)),
    fun r : ℝ => Real.smoothTransition ((3 * g / 2 + e - r) / e),
    hΞsm, hϑsm, hΘsm, hβsm, hψpsm, hψqsm, hΞarc, hΞd, hΞπ, hϑarc, hϑb,
    (fun r _ _ => hϑd r),
    hΘd, hΞΘ, hΘϑ, hβ0, hβ1, hβr, hψp1, hψp0, hψpr, hψq1, hψq0, hψqr⟩

end

end Work.Diff.Dim2
