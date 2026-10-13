import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# Basic facts about the cylindrical frame on ℝ³

Elementary API for the coordinate functions and the frame `e_r, e_θ, e₃` of
`Work.Cyl.Coords`, plus the coordinate expressions of the components of a field.
-/

noncomputable section

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

variable {x : R3}

/-! ## The radial coordinate -/

lemma radSq_nonneg (x : R3) : 0 ≤ radSq x := by simp only [radSq]; positivity

lemma radial_nonneg (x : R3) : 0 ≤ radial x := Real.sqrt_nonneg _

lemma radial_sq (x : R3) : radial x ^ 2 = radSq x := Real.sq_sqrt (radSq_nonneg x)

lemma radSq_eq_zero_iff (x : R3) : radSq x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [radSq]
  constructor
  · intro h
    have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    exact ⟨(pow_eq_zero_iff (n := 2) (by norm_num)).mp h0,
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1⟩
  · rintro ⟨h0, h1⟩; simp [h0, h1]

lemma radial_eq_zero_iff (x : R3) : radial x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [radial, Real.sqrt_eq_zero']
  exact ⟨fun h => (radSq_eq_zero_iff x).mp (le_antisymm h (radSq_nonneg x)),
    fun h => le_of_eq ((radSq_eq_zero_iff x).mpr h)⟩

lemma radial_pos_iff (x : R3) : 0 < radial x ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  rw [radial, Real.sqrt_pos, radSq]
  constructor
  · intro h; by_contra hc
    simp only [not_or, not_not] at hc
    rw [hc.1, hc.2] at h; norm_num at h
  · rintro (h | h)
    · nlinarith [sq_pos_iff.mpr h, sq_nonneg (x 1)]
    · nlinarith [sq_pos_iff.mpr h, sq_nonneg (x 0)]

lemma radial_pos_of_ne (h : x 0 ≠ 0 ∨ x 1 ≠ 0) : 0 < radial x := (radial_pos_iff x).mpr h

/-! ## Coordinates and inner products -/

@[simp] lemma axial_eq (x : R3) : axial x = x 2 := rfl

@[simp] lemma radialVec_apply_zero (x : R3) : (radialVec x) 0 = x 0 := by simp [radialVec]
@[simp] lemma radialVec_apply_one (x : R3) : (radialVec x) 1 = x 1 := by simp [radialVec]
@[simp] lemma radialVec_apply_two (x : R3) : (radialVec x) 2 = 0 := by simp [radialVec]
@[simp] lemma angularVec_apply_zero (x : R3) : (angularVec x) 0 = -x 1 := by simp [angularVec]
@[simp] lemma angularVec_apply_one (x : R3) : (angularVec x) 1 = x 0 := by simp [angularVec]
@[simp] lemma angularVec_apply_two (x : R3) : (angularVec x) 2 = 0 := by simp [angularVec]
@[simp] lemma eZ_apply_zero : (eZ : R3) 0 = 0 := by simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma eZ_apply_one : (eZ : R3) 1 = 0 := by simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma eZ_apply_two : (eZ : R3) 2 = 1 := by simp [eZ, FiniteTimeSingularity.e]

@[simp] lemma eR_apply_zero (x : R3) : (eR x) 0 = x 0 / radial x := by
  simp [eR, div_eq_inv_mul]
@[simp] lemma eR_apply_one (x : R3) : (eR x) 1 = x 1 / radial x := by
  simp [eR, div_eq_inv_mul]
@[simp] lemma eR_apply_two (x : R3) : (eR x) 2 = 0 := by simp [eR]
@[simp] lemma eTheta_apply_zero (x : R3) : (eTheta x) 0 = -x 1 / radial x := by
  simp [eTheta, div_eq_inv_mul]
@[simp] lemma eTheta_apply_one (x : R3) : (eTheta x) 1 = x 0 / radial x := by
  simp [eTheta, div_eq_inv_mul]
@[simp] lemma eTheta_apply_two (x : R3) : (eTheta x) 2 = 0 := by simp [eTheta]

/-- The inner product in coordinates. -/
lemma inner_eq (a b : R3) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- Extensionality by coordinates. -/
lemma ext_coord {a b : R3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> assumption

lemma inner_radialVec_self (x : R3) : inner ℝ (radialVec x) (radialVec x) = radSq x := by
  rw [inner_eq]; simp [radSq]; ring

lemma inner_angularVec_self (x : R3) : inner ℝ (angularVec x) (angularVec x) = radSq x := by
  rw [inner_eq]; simp [radSq]; ring

lemma inner_radialVec_angularVec (x : R3) : inner ℝ (radialVec x) (angularVec x) = 0 := by
  rw [inner_eq]; simp; ring

lemma inner_radialVec_eZ (x : R3) : inner ℝ (radialVec x) eZ = 0 := by rw [inner_eq]; simp

lemma inner_angularVec_eZ (x : R3) : inner ℝ (angularVec x) eZ = 0 := by rw [inner_eq]; simp

/-! ## The frame `e_r, e_θ, e₃` off the axis -/

lemma inner_eR_eR (x : R3) (hr : radial x ≠ 0) : inner ℝ (eR x) (eR x) = 1 := by
  rw [eR, real_inner_smul_left, real_inner_smul_right, inner_radialVec_self]
  field_simp
  exact (radial_sq x).symm

lemma inner_eTheta_eTheta (x : R3) (hr : radial x ≠ 0) : inner ℝ (eTheta x) (eTheta x) = 1 := by
  rw [eTheta, real_inner_smul_left, real_inner_smul_right, inner_angularVec_self]
  field_simp
  exact (radial_sq x).symm

lemma inner_eR_eTheta (x : R3) : inner ℝ (eR x) (eTheta x) = 0 := by
  rw [eR, eTheta, real_inner_smul_left, real_inner_smul_right, inner_radialVec_angularVec]
  ring

lemma inner_eR_eZ (x : R3) : inner ℝ (eR x) eZ = 0 := by
  rw [eR, real_inner_smul_left, inner_radialVec_eZ]; ring

lemma inner_eTheta_eZ (x : R3) : inner ℝ (eTheta x) eZ = 0 := by
  rw [eTheta, real_inner_smul_left, inner_angularVec_eZ]; ring

lemma norm_eR (x : R3) (hr : radial x ≠ 0) : ‖eR x‖ = 1 := by
  have h : ‖eR x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, inner_eR_eR x hr]
  nlinarith [norm_nonneg (eR x)]

lemma norm_eTheta (x : R3) (hr : radial x ≠ 0) : ‖eTheta x‖ = 1 := by
  have h : ‖eTheta x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, inner_eTheta_eTheta x hr]
  nlinarith [norm_nonneg (eTheta x)]

/-! ## Components of a field -/

lemma compR_eq (u : R3 → R3) (x : R3) :
    compR u x = (u x 0 * x 0 + u x 1 * x 1) / radial x := by
  rw [compR, inner_eq]; simp; ring

lemma compT_eq (u : R3 → R3) (x : R3) :
    compT u x = (u x 1 * x 0 - u x 0 * x 1) / radial x := by
  rw [compT, inner_eq]; simp; ring

lemma compZ_eq (u : R3 → R3) (x : R3) : compZ u x = u x 2 := by
  rw [compZ, inner_eq]; simp

/-- Off the axis, `e_r, e_θ, e₃` is an orthonormal frame: the orthogonal decomposition of any
vector field in cylindrical components. -/
lemma decomposition (u : R3 → R3) (x : R3) (hr : radial x ≠ 0) :
    u x = compR u x • eR x + compT u x • eTheta x + compZ u x • eZ := by
  have hr2 : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := radial_sq x
  refine ext_coord ?_ ?_ ?_
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_zero, eR_apply_one, eR_apply_two, eTheta_apply_zero,
      eTheta_apply_one, eTheta_apply_two, eZ_apply_zero, eZ_apply_one, eZ_apply_two, mul_zero,
      add_zero]
    field_simp
    linear_combination (u x 0) * hr2
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_zero, eR_apply_one, eR_apply_two, eTheta_apply_zero,
      eTheta_apply_one, eTheta_apply_two, eZ_apply_zero, eZ_apply_one, eZ_apply_two, mul_zero,
      add_zero]
    field_simp
    linear_combination (u x 1) * hr2
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_two, eTheta_apply_two, eZ_apply_zero, eZ_apply_one,
      eZ_apply_two, mul_zero, add_zero, mul_one, zero_add]

/-! ## Components of `cylField` -/

@[simp] lemma cylField_zero (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 0 = ur (radial x) (axial x) * x 0 / radial x := by
  simp only [cylField, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, radialVec_apply_zero, radialVec_apply_two, eZ_apply_zero, eZ_apply_two,
    mul_zero, mul_one, add_zero]
  ring

@[simp] lemma cylField_one (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 1 = ur (radial x) (axial x) * x 1 / radial x := by
  simp only [cylField, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, radialVec_apply_one, radialVec_apply_two, eZ_apply_one, eZ_apply_two,
    mul_zero, mul_one, add_zero]
  ring

@[simp] lemma cylField_two (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 2 = uz (radial x) (axial x) := by
  simp [cylField]

lemma compR_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3) (hr : radial x ≠ 0) :
    compR (cylField ur uz) x = ur (radial x) (axial x) := by
  have hr2 : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := radial_sq x
  rw [compR_eq, cylField_zero, cylField_one]
  field_simp
  rw [hr2]

lemma compT_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3) (hr : radial x ≠ 0) :
    compT (cylField ur uz) x = 0 := by
  rw [compT_eq, cylField_zero, cylField_one]
  field_simp
  ring

lemma compZ_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    compZ (cylField ur uz) x = uz (radial x) (axial x) := by
  rw [compZ_eq, cylField_two]

lemma cylField_eq_axiField (ur uz : ℝ → ℝ → ℝ) :
    cylField ur uz =
      axiField (fun s z => ur (Real.sqrt s) z / Real.sqrt s) (fun s z => uz (Real.sqrt s) z) := by
  funext x
  simp only [cylField, axiField, radial]

lemma isAxiNoSwirl_cylField (ur uz : ℝ → ℝ → ℝ) : IsAxiNoSwirl (cylField ur uz) :=
  ⟨ur, uz, rfl⟩

/-! ## The three dimensional radius and angle -/

lemma rho_nonneg (x : R3) : 0 ≤ rho x := Real.sqrt_nonneg _

lemma rho_sq (x : R3) : rho x ^ 2 = radSq x + axial x ^ 2 :=
  Real.sq_sqrt (add_nonneg (radSq_nonneg x) (sq_nonneg _))

lemma rho_eq_norm (x : R3) : rho x = ‖x‖ := by
  have h : rho x ^ 2 = ‖x‖ ^ 2 := by
    rw [rho_sq, ← real_inner_self_eq_norm_sq, inner_eq]
    simp [radSq]; ring
  rw [← abs_of_nonneg (rho_nonneg x), ← abs_of_nonneg (norm_nonneg x)]
  exact (sq_eq_sq_iff_abs_eq_abs _ _).mp h

lemma rho_pos_iff (x : R3) : 0 < rho x ↔ x ≠ 0 := by
  rw [rho_eq_norm, norm_pos_iff]

lemma radSq_le_rho_sq (x : R3) : radSq x ≤ rho x ^ 2 := by
  rw [rho_sq]; nlinarith [sq_nonneg (axial x)]

lemma axial_sq_le_rho_sq (x : R3) : axial x ^ 2 ≤ rho x ^ 2 := by
  rw [rho_sq]; nlinarith [radSq_nonneg x]

lemma abs_axial_le_rho (x : R3) : |axial x| ≤ rho x := by
  have h := axial_sq_le_rho_sq x
  have h2 : (|axial x| : ℝ) ^ 2 ≤ rho x ^ 2 := by rwa [sq_abs]
  nlinarith [abs_nonneg (axial x), rho_nonneg x]

lemma radial_le_rho (x : R3) : radial x ≤ rho x := by
  have h := radSq_le_rho_sq x
  have h2 : radial x ^ 2 ≤ rho x ^ 2 := by rwa [radial_sq]
  nlinarith [radial_nonneg x, rho_nonneg x]

/-! ## The polar coordinates `(ρ, θ)` on the `(r, x₃)` half plane -/

lemma rhoP_nonneg (r z : ℝ) : 0 ≤ rhoP r z := Real.sqrt_nonneg _

lemma rhoP_pos {r : ℝ} (hr : 0 < r) (z : ℝ) : 0 < rhoP r z :=
  Real.sqrt_pos.mpr (by positivity)

lemma rhoP_sq (r z : ℝ) : rhoP r z ^ 2 = r ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)

lemma rhoP_ne_zero {r : ℝ} (hr : 0 < r) (z : ℝ) : rhoP r z ≠ 0 := ne_of_gt (rhoP_pos hr z)

/-- `sin θ = z/ρ`. -/
lemma sin_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) : Real.sin (thetaP r z) = z / rhoP r z := by
  have h1 : (1:ℝ) + (z / r) ^ 2 = (r ^ 2 + z ^ 2) / r ^ 2 := by field_simp
  have h2 : Real.sqrt ((r ^ 2 + z ^ 2) / r ^ 2) = Real.sqrt (r ^ 2 + z ^ 2) / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  rw [thetaP, Real.sin_arctan, h1, h2, rhoP]
  field_simp

/-- `cos θ = r/ρ`; in particular `cos θ > 0` for `r > 0`. -/
lemma cos_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) : Real.cos (thetaP r z) = r / rhoP r z := by
  have h1 : (1:ℝ) + (z / r) ^ 2 = (r ^ 2 + z ^ 2) / r ^ 2 := by field_simp
  have h2 : Real.sqrt ((r ^ 2 + z ^ 2) / r ^ 2) = Real.sqrt (r ^ 2 + z ^ 2) / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  rw [thetaP, Real.cos_arctan, h1, h2, rhoP]
  field_simp

lemma cos_thetaP_pos {r : ℝ} (hr : 0 < r) (z : ℝ) : 0 < Real.cos (thetaP r z) := by
  rw [cos_thetaP hr z]; exact div_pos hr (rhoP_pos hr z)

lemma thetaP_neg (r z : ℝ) : thetaP r (-z) = -thetaP r z := by
  rw [thetaP, thetaP, neg_div, Real.arctan_neg]

lemma rhoP_neg (r z : ℝ) : rhoP r (-z) = rhoP r z := by rw [rhoP, rhoP, neg_sq]

end Work.Cyl
