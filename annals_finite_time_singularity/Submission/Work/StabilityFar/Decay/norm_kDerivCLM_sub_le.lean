import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.StabilityFar.Decay.KernelDefs
-- ===== merged: Submission.Work.StabilityFar.Decay.kf_hasFDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open Work.LWP

/-- Scalar multiplication of a **scalar-valued** continuous linear map commutes with
`smulRight`: `(a • L).smulRight x = a • L.smulRight x`. -/
private lemma smulRight_smul_scalar (a : ℝ) (L : R3 →L[ℝ] ℝ) (x : R3) :
    (a • L).smulRight x = a • L.smulRight x := by
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply]
  simp [smul_eq_mul, mul_comm, mul_left_comm]

theorem kf_hasFDerivAt (b : Work.LWP.R3) (hb : b ≠ 0) :
    HasFDerivAt Work.StabilityFar.Decay.kf (Work.StabilityFar.Decay.kDerivCLM b) b := by
  -- The scalar identity `(-3/2) * (‖b‖²)^(-3/2 - 1) * 2 = -(3 * (‖b‖⁵)⁻¹)`.
  have hscalar : ((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1) * 2)
      = -(3 * (‖b‖ ^ 5)⁻¹) := by
    rw [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num]
    rw [← Real.rpow_natCast_mul (norm_nonneg b) 2 (-5 / 2)]
    rw [show ((2 : ℕ) : ℝ) * (-5 / 2 : ℝ) = -5 by norm_num]
    rw [Real.rpow_neg (norm_nonneg b) (5 : ℝ)]
    simp
    ring
  -- Differentiate `x ↦ ‖x‖²` and compose with `(·)^(-3/2)`.
  have hcp : HasFDerivAt (fun x : R3 => (‖x‖ ^ 2) ^ (-3 / 2 : ℝ))
      (((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1)) • ((2 : ℕ) • innerSL ℝ b)) b :=
    (hasStrictFDerivAt_norm_sq b).hasFDerivAt.rpow_const (Or.inl (by positivity))
  -- `(‖x‖²)^(-3/2) = (‖x‖³)⁻¹`.
  have hc : HasFDerivAt (fun x : R3 => (‖x‖ ^ (3 : ℕ))⁻¹)
      (((-3 / 2 : ℝ) * (‖b‖ ^ 2) ^ ((-3 / 2 : ℝ) - 1)) • ((2 : ℕ) • innerSL ℝ b)) b := by
    refine hcp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => ?_))
    show (‖x‖ ^ (3 : ℕ))⁻¹ = (‖x‖ ^ 2) ^ (-3 / 2 : ℝ)
    rw [← Real.rpow_natCast_mul (norm_nonneg x) 2 (-3 / 2)]
    rw [show ((2 : ℕ) : ℝ) * (-3 / 2 : ℝ) = -3 by norm_num]
    rw [Real.rpow_neg (norm_nonneg x) (3 : ℝ)]
    simp
  -- Put the derivative of the scalar factor into its final shape.
  have hc' : HasFDerivAt (fun x : R3 => (‖x‖ ^ (3 : ℕ))⁻¹)
      (-(3 * (‖b‖ ^ 5)⁻¹) • innerSL ℝ b) b := by
    refine hc.congr_fderiv ?_
    rw [← hscalar]
    rw [← Nat.cast_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ b)]
    rw [smul_smul]
    norm_num
  -- Product rule with the identity.
  have hsmul := hc'.smul (hasFDerivAt_id b)
  have h1 : HasFDerivAt Work.StabilityFar.Decay.kf
      ((‖b‖ ^ (3 : ℕ))⁻¹ • (1 : R3 →L[ℝ] R3)
        + (-(3 * (‖b‖ ^ 5)⁻¹) • innerSL ℝ b).smulRight b) b :=
    hsmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => rfl))
  exact h1.congr_fderiv (by
    rw [Work.StabilityFar.Decay.kDerivCLM]
    rw [smulRight_smul_scalar]
    rw [ContinuousLinearMap.one_def]
    rw [show ((-(3 * (‖b‖ ^ 5)⁻¹)) • ((innerSL ℝ b).smulRight b))
          = -((3 * (‖b‖ ^ 5)⁻¹) • ((innerSL ℝ b).smulRight b)) from neg_smul _ _]
    rw [sub_eq_add_neg])

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.norm_crossL_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- The operator norm of the continuous linear map `v ↦ u × v` is at most `‖u‖`.

This is the vector identity `‖u × v‖ = ‖u‖ ‖v‖ sin θ ≤ ‖u‖ ‖v‖` fed into the operator-norm
characterization `‖f‖ ≤ M ↔ ∀ v, ‖f v‖ ≤ M ‖v‖`. -/
theorem norm_crossL_le (u : Work.LWP.R3) : ‖Work.StabilityFar.Decay.crossL u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (crossL u) (norm_nonneg _) (fun v => ?_)
  rw [crossL_apply, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- Pointwise bound for the derivative kernel `kDerivCLM b`: for every `v`,
`‖kDerivCLM b v‖ ≤ (4 / ‖b‖³) ‖v‖`, since
`kDerivCLM b v = ‖b‖⁻³ v - 3 ‖b‖⁻⁵ (b·v) b`. -/
private theorem norm_kDerivCLM_apply_le (b v : Work.LWP.R3) (hb : 0 < ‖b‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM b v‖ ≤ (4 / ‖b‖ ^ 3) * ‖v‖ := by
  have hE : Work.StabilityFar.Decay.kDerivCLM b v =
      (‖b‖ ^ (3 : ℕ))⁻¹ • v - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b) := by
    simp only [Work.StabilityFar.Decay.kDerivCLM, sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  calc ‖Work.StabilityFar.Decay.kDerivCLM b v‖
      = ‖(‖b‖ ^ (3 : ℕ))⁻¹ • v - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b)‖ := by
        rw [hE]
    _ ≤ ‖(‖b‖ ^ (3 : ℕ))⁻¹ • v‖ + ‖(3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b)‖ :=
        norm_sub_le _ _
    _ = (‖b‖ ^ (3 : ℕ))⁻¹ * ‖v‖ + 3 * (‖b‖ ^ (5 : ℕ))⁻¹ * (‖inner ℝ b v‖ * ‖b‖) := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ (‖b‖ ^ (3 : ℕ))⁻¹ * ‖v‖ + 3 * (‖b‖ ^ (5 : ℕ))⁻¹ * ((‖b‖ * ‖v‖) * ‖b‖) := by
        gcongr
        exact norm_inner_le_norm b v
    _ = (4 / ‖b‖ ^ 3) * ‖v‖ := by
        field_simp
        ring

theorem norm_kDerivCLM_le (b : Work.LWP.R3) (m : ℝ) (hm : 0 < m) (hb : m ≤ ‖b‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM b‖ ≤ 4 / m ^ 3 := by
  have hr : 0 < ‖b‖ := lt_of_lt_of_le hm hb
  have hmain : ∀ v : Work.LWP.R3,
      ‖Work.StabilityFar.Decay.kDerivCLM b v‖ ≤ (4 / ‖b‖ ^ 3) * ‖v‖ :=
    fun v => norm_kDerivCLM_apply_le b v hr
  have hbnd : ‖Work.StabilityFar.Decay.kDerivCLM b‖ ≤ 4 / ‖b‖ ^ 3 :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hmain
  have hmono : 4 / ‖b‖ ^ 3 ≤ 4 / m ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ (le_of_lt hm) hb 3
  linarith

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le =====
section

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
end
