/-
# `Work.StabilityFar.Decay.norm_kDerivCLM_sub_le`

The Biot–Savart kernel calculus `b ↦ kf b = b/‖b‖³` has second derivative `D²kf = D(kDerivCLM)`,
which away from the origin is homogeneous of degree `-4`.  This file proves the resulting
Lipschitz bound for the *derivative* of the kernel, uniformly on the exterior of the ball of
radius `m`:

  `‖kDerivCLM b - kDerivCLM c‖ ≤ 64/m⁴ ‖b - c‖`   whenever  `m ≤ ‖b‖`, `m ≤ ‖c‖`.

The constant `64` is not sharp (the argument actually gives `24`), but the bound is the
`O(m⁻⁴)` Lipschitz estimate needed for the far-field `C^{1,1}` step of `St4`.

The structure of the proof is the standard one for such homogeneous kernels.  Writing

  `kDerivCLM b = (‖b‖³)⁻¹ • angK (‖b‖⁻¹ • b)`,
  `angK u = id - 3 • dirProj u`,  `dirProj u = v ↦ ⟪u, v⟫ • u`,

one splits the difference with the *normalised* arguments `u = b/‖b‖`, `v = c/‖c‖`, which are
unit vectors:

  `kDerivCLM b - kDerivCLM c
     = (‖b‖³)⁻¹ • (angK u - angK v) + ((‖b‖³)⁻¹ - (‖c‖³)⁻¹) • angK v`.

The first summand is bounded using that `angK` is `6`-Lipschitz on the unit sphere and that the
normalisation map `b ↦ b/‖b‖` is `2/‖b‖`-Lipschitz; the second using the elementary scalar bound
`|a⁻³ - b⁻³| ≤ 3 m⁻⁴ |a - b|` on `[m,∞)` and `‖angK v‖ ≤ 4`.  Both contribute at most
`12/m⁴ ‖b - c‖`, giving `24/m⁴ ‖b - c‖ ≤ 64/m⁴ ‖b - c‖`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar.Decay

open Work.LWP

/-! ## The two building blocks of `kDerivCLM` -/

/-- The rank-one operator `u ↦ ⟪u, ·⟫ • u`, i.e. `InnerProductSpace.rankOne ℝ u u`; for a unit
vector `u` this is the orthogonal projection onto `ℝ • u`. -/
noncomputable def dirProj (u : R3) : R3 →L[ℝ] R3 := (innerSL ℝ u).smulRight u

/-- The angular part `id - 3 • dirProj u` of the Newtonian derivative `kDerivCLM u`; for a unit
vector `u` it has operator norm `2` and its eigenvalues are `-2` (along `u`) and `1`
(orthogonally), so `‖angK u‖ ≤ 4` is a very generous bound. -/
noncomputable def angK (u : R3) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3 - (3 : ℝ) • dirProj u

/-- `dirProj` is homogeneous of degree `2`, hence `angK (b/‖b‖)` is the normalised version of
`kDerivCLM b` up to the scalar `‖b‖⁻³`. -/
lemma dirProj_smul (a : ℝ) (u : R3) : dirProj (a • u) = (a * a) • dirProj u := by
  ext z
  simp only [dirProj, smul_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul]
  ring_nf

/-- The diagonalisation `dirProj u - dirProj v = (u-v)⊗u + v⊗(u-v)` used for the Lipschitz bound
of `dirProj`. -/
lemma dirProj_sub (u v : R3) : dirProj u - dirProj v =
    (innerSL ℝ (u - v)).smulRight u + (innerSL ℝ v).smulRight (u - v) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [dirProj, sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, map_sub]
  module

/-- The operator norm of the rank-one operator `dirProj u` is `‖u‖²`. -/
lemma norm_dirProj_apply (u : R3) : ‖dirProj u‖ = ‖u‖ * ‖u‖ := by
  rw [dirProj, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

/-- `dirProj` is Lipschitz with the natural bound `(‖u‖ + ‖v‖) ‖u - v‖`. -/
lemma norm_dirProj_sub_le (u v : R3) : ‖dirProj u - dirProj v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [dirProj_sub]
  calc ‖(innerSL ℝ (u - v)).smulRight u + (innerSL ℝ v).smulRight (u - v)‖
      ≤ ‖(innerSL ℝ (u - v)).smulRight u‖ + ‖(innerSL ℝ v).smulRight (u - v)‖ := norm_add_le _ _
    _ = ‖u - v‖ * ‖u‖ + ‖v‖ * ‖u - v‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
          innerSL_apply_norm, innerSL_apply_norm]
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- **The key normal form of `kDerivCLM`**: pulling out the degree-`-3` homogeneity leaves the
*angular* part `angK` evaluated at the unit vector `b/‖b‖`. -/
lemma kDerivCLM_eq (b : R3) : kDerivCLM b = (‖b‖^3)⁻¹ • angK (‖b‖⁻¹ • b) := by
  have h : (3 * (‖b‖ ^ 5)⁻¹) = (‖b‖ ^ 3)⁻¹ * (3 * (‖b‖⁻¹ * ‖b‖⁻¹)) := by ring_nf
  show (‖b‖^3)⁻¹ • ContinuousLinearMap.id ℝ R3 - (3 * (‖b‖^5)⁻¹) • dirProj b
      = (‖b‖^3)⁻¹ • (ContinuousLinearMap.id ℝ R3 - (3:ℝ) • dirProj (‖b‖⁻¹ • b))
  rw [dirProj_smul, h]
  simp only [smul_sub, smul_smul]

/-- On the unit sphere, `angK` is `6`-Lipschitz. -/
lemma norm_angK_sub_le_of_unit {u v : R3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖angK u - angK v‖ ≤ 6 * ‖u - v‖ := by
  have h : angK u - angK v = (-3:ℝ) • (dirProj u - dirProj v) := by
    unfold angK; module
  rw [h, norm_smul]
  have h3 : ‖(-3:ℝ)‖ = 3 := by norm_num
  rw [h3]
  calc (3:ℝ) * ‖dirProj u - dirProj v‖
      ≤ 3 * ((‖u‖ + ‖v‖) * ‖u - v‖) := by
        gcongr; exact norm_dirProj_sub_le u v
    _ = 6 * ‖u - v‖ := by rw [hu, hv]; ring

/-- At a unit vector, `‖angK u‖ ≤ 4` (the sharp value is `2`). -/
lemma norm_angK_le_of_unit {v : R3} (hv : ‖v‖ = 1) : ‖angK v‖ ≤ 4 := by
  calc ‖angK v‖ = ‖ContinuousLinearMap.id ℝ R3 - (3:ℝ) • dirProj v‖ := rfl
    _ ≤ ‖ContinuousLinearMap.id ℝ R3‖ + ‖(3:ℝ) • dirProj v‖ := norm_sub_le _ _
    _ ≤ 1 + 3 * ‖dirProj v‖ := by
        gcongr
        · exact ContinuousLinearMap.norm_id_le
        · rw [norm_smul]; norm_num
    _ = 1 + 3 * (‖v‖ * ‖v‖) := by rw [norm_dirProj_apply]
    _ ≤ 4 := by rw [hv]; norm_num

/-! ## Two elementary estimates -/

/-- The map `t ↦ t⁻³` is Lipschitz on `[m, ∞)` with constant `3/m⁴`. -/
lemma abs_inv_cube_sub_le (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |(a ^ 3)⁻¹ - (b ^ 3)⁻¹| ≤ 3 / m ^ 4 * |a - b| := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have h1 : (a^3)⁻¹ - (b^3)⁻¹ = (a⁻¹ - b⁻¹) * ((a⁻¹)^2 + a⁻¹ * b⁻¹ + (b⁻¹)^2) := by
    rw [inv_pow, inv_pow]; ring
  have hA : |a⁻¹ - b⁻¹| ≤ |a - b| / m^2 := by
    have key : a⁻¹ - b⁻¹ = (b - a) * (a*b)⁻¹ := by field_simp
    rw [key, abs_mul, abs_sub_comm b a, abs_of_pos (inv_pos.mpr (mul_pos ha0 hb0)), div_eq_mul_inv]
    gcongr
    nlinarith [ha, hb, hm]
  have hB : |(a⁻¹)^2 + a⁻¹ * b⁻¹ + (b⁻¹)^2| ≤ 3 / m^2 := by
    have ha2 : (a⁻¹)^2 ≤ (m^2)⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ (by positivity) (by nlinarith [ha, hm])
    have hb2 : (b⁻¹)^2 ≤ (m^2)⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ (by positivity) (by nlinarith [hb, hm])
    have hab2 : a⁻¹ * b⁻¹ ≤ (m^2)⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (by positivity) (by nlinarith [ha, hb, hm])
    calc |(a⁻¹)^2 + a⁻¹ * b⁻¹ + (b⁻¹)^2|
        ≤ |(a⁻¹)^2 + a⁻¹ * b⁻¹| + |(b⁻¹)^2| := abs_add_le _ _
      _ ≤ (|(a⁻¹)^2| + |a⁻¹ * b⁻¹|) + |(b⁻¹)^2| := by
            gcongr; exact abs_add_le _ _
      _ = (a⁻¹)^2 + a⁻¹ * b⁻¹ + (b⁻¹)^2 := by
            rw [abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hb0.le)),
              abs_of_nonneg (sq_nonneg _)]
      _ ≤ 3 / m^2 := by rw [div_eq_mul_inv]; linarith
  calc |(a^3)⁻¹ - (b^3)⁻¹|
      = |a⁻¹ - b⁻¹| * |(a⁻¹)^2 + a⁻¹ * b⁻¹ + (b⁻¹)^2| := by rw [h1, abs_mul]
    _ ≤ (|a - b| / m^2) * (3 / m^2) := by
        exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    _ = 3 / m^4 * |a - b| := by field_simp

/-- The normalisation map `b ↦ b/‖b‖` is `2/‖b‖`-Lipschitz, for `b ≠ 0`. -/
lemma norm_inv_smul_sub_le (b c : R3) (hb : 0 < ‖b‖) (hc : 0 < ‖c‖) :
    ‖‖b‖⁻¹ • b - ‖c‖⁻¹ • c‖ ≤ 2 * ‖b - c‖ / ‖b‖ := by
  have hkey : ‖b‖⁻¹ • b - ‖c‖⁻¹ • c = ‖b‖⁻¹ • (b - c) + (‖b‖⁻¹ - ‖c‖⁻¹) • c := by
    module
  rw [hkey]
  have hsecond : |‖b‖⁻¹ - ‖c‖⁻¹| * ‖c‖ ≤ ‖b - c‖ / ‖b‖ := by
    calc |‖b‖⁻¹ - ‖c‖⁻¹| * ‖c‖
        = |(‖b‖⁻¹ - ‖c‖⁻¹) * ‖c‖| := by rw [abs_mul, abs_of_nonneg (norm_nonneg c)]
      _ = |(‖c‖ - ‖b‖) / ‖b‖| := by
            congr 1
            field_simp
      _ = |‖c‖ - ‖b‖| / ‖b‖ := by rw [abs_div, abs_of_pos hb]
      _ ≤ ‖b - c‖ / ‖b‖ := by
            gcongr
            rw [abs_sub_comm]
            exact abs_norm_sub_norm_le b c
  calc ‖‖b‖⁻¹ • (b - c) + (‖b‖⁻¹ - ‖c‖⁻¹) • c‖
      ≤ ‖‖b‖⁻¹ • (b - c)‖ + ‖(‖b‖⁻¹ - ‖c‖⁻¹) • c‖ := norm_add_le _ _
    _ = ‖b‖⁻¹ * ‖b - c‖ + |‖b‖⁻¹ - ‖c‖⁻¹| * ‖c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg b))]
    _ ≤ ‖b‖⁻¹ * ‖b - c‖ + ‖b - c‖ / ‖b‖ := by linarith [hsecond]
    _ = 2 * ‖b - c‖ / ‖b‖ := by field_simp; ring

/-! ## The Lipschitz bound for `kDerivCLM` -/

theorem norm_kDerivCLM_sub_le (b c : Work.LWP.R3) (m : ℝ) (hm : 0 < m)
    (hb : m ≤ ‖b‖) (hc : m ≤ ‖c‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM b - Work.StabilityFar.Decay.kDerivCLM c‖
      ≤ 64 / m ^ 4 * ‖b - c‖ := by
  have hbpos : 0 < ‖b‖ := lt_of_lt_of_le hm hb
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le hm hc
  have hu1 : ‖‖b‖⁻¹ • b‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg b)),
      inv_mul_cancel₀ (ne_of_gt hbpos)]
  have hv1 : ‖‖c‖⁻¹ • c‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg c)),
      inv_mul_cancel₀ (ne_of_gt hcpos)]
  have hdiff : kDerivCLM b - kDerivCLM c =
      (‖b‖^3)⁻¹ • (angK (‖b‖⁻¹ • b) - angK (‖c‖⁻¹ • c))
      + ((‖b‖^3)⁻¹ - (‖c‖^3)⁻¹) • angK (‖c‖⁻¹ • c) := by
    rw [kDerivCLM_eq b, kDerivCLM_eq c]
    module
  have h1 : ‖(‖b‖^3)⁻¹ • (angK (‖b‖⁻¹ • b) - angK (‖c‖⁻¹ • c))‖
      ≤ 12 / m^4 * ‖b - c‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg b) 3))]
    calc (‖b‖^3)⁻¹ * ‖angK (‖b‖⁻¹ • b) - angK (‖c‖⁻¹ • c)‖
        ≤ (‖b‖^3)⁻¹ * (6 * ‖‖b‖⁻¹ • b - ‖c‖⁻¹ • c‖) := by
          gcongr
          exact norm_angK_sub_le_of_unit hu1 hv1
      _ ≤ (‖b‖^3)⁻¹ * (6 * (2 * ‖b - c‖ / ‖b‖)) := by
          gcongr
          exact norm_inv_smul_sub_le b c hbpos hcpos
      _ = 12 / ‖b‖^4 * ‖b - c‖ := by field_simp; ring
      _ ≤ 12 / m^4 * ‖b - c‖ := by
          gcongr
  have h2 : ‖((‖b‖^3)⁻¹ - (‖c‖^3)⁻¹) • angK (‖c‖⁻¹ • c)‖
      ≤ 12 / m^4 * ‖b - c‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hA : |(‖b‖^3)⁻¹ - (‖c‖^3)⁻¹| ≤ 3 / m^4 * ‖b - c‖ := by
      calc |(‖b‖^3)⁻¹ - (‖c‖^3)⁻¹| ≤ 3 / m^4 * |‖b‖ - ‖c‖| :=
            abs_inv_cube_sub_le ‖b‖ ‖c‖ m hm hb hc
        _ ≤ 3 / m^4 * ‖b - c‖ := by gcongr; exact abs_norm_sub_norm_le b c
    have hB : ‖angK (‖c‖⁻¹ • c)‖ ≤ 4 := norm_angK_le_of_unit hv1
    calc |(‖b‖^3)⁻¹ - (‖c‖^3)⁻¹| * ‖angK (‖c‖⁻¹ • c)‖
        ≤ (3 / m^4 * ‖b - c‖) * 4 := mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = 12 / m^4 * ‖b - c‖ := by ring
  rw [hdiff]
  calc ‖(‖b‖^3)⁻¹ • (angK (‖b‖⁻¹ • b) - angK (‖c‖⁻¹ • c))
        + ((‖b‖^3)⁻¹ - (‖c‖^3)⁻¹) • angK (‖c‖⁻¹ • c)‖
      ≤ ‖(‖b‖^3)⁻¹ • (angK (‖b‖⁻¹ • b) - angK (‖c‖⁻¹ • c))‖
        + ‖((‖b‖^3)⁻¹ - (‖c‖^3)⁻¹) • angK (‖c‖⁻¹ • c)‖ := norm_add_le _ _
    _ ≤ 12 / m^4 * ‖b - c‖ + 12 / m^4 * ‖b - c‖ := add_le_add h1 h2
    _ = 24 / m^4 * ‖b - c‖ := by ring
    _ ≤ 64 / m^4 * ‖b - c‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

end Work.StabilityFar.Decay
