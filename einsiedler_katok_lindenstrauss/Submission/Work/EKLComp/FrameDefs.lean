import Mathlib
import Submission.Work.EKLComp.EucDefs

/-!
# Building blocks for `Work.EKLComp.exists_orthonormal_frame`

We want, for every nonzero `v : Fin 3 → ℝ`, a linear equivalence `T` of `Fin 3 → ℝ` which is an
orientation preserving Euclidean isometry (`det = 1`) with `T v = enorm3 v • e3 0`.

The construction is the composition of two planar (Givens) rotations:
* `MA` rotates in the `(e₁, e₂)`-plane so as to send `(v 1, v 2)` to `(sv v, 0)`;
* `MB` rotates in the `(e₀, e₁)`-plane so as to send `(v 0, sv v)` to `(enorm3 v, 0)`.

Here `sv v = sqrt (v 1 ^ 2 + v 2 ^ 2)` and the coefficients `ca, cb, cc, cd` are the normalized
entries of the two rotation blocks.  This file collects the definitions and the elementary scalar
identities that they satisfy.
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Matrix

noncomputable section

/-- Second component of the norm: `sqrt (v 1 ^ 2 + v 2 ^ 2)`. -/
def sv (v : Fin 3 → ℝ) : ℝ := Real.sqrt (v 1 ^ 2 + v 2 ^ 2)

/-- `cos` of the rotation in the `(e₁, e₂)`-plane. -/
def ca (v : Fin 3 → ℝ) : ℝ := if sv v = 0 then 1 else v 1 / sv v

/-- `sin` of the rotation in the `(e₁, e₂)`-plane. -/
def cb (v : Fin 3 → ℝ) : ℝ := if sv v = 0 then 0 else v 2 / sv v

/-- `cos` of the rotation in the `(e₀, e₁)`-plane. -/
def cc (v : Fin 3 → ℝ) : ℝ := v 0 / enorm3 v

/-- `sin` of the rotation in the `(e₀, e₁)`-plane. -/
def cd (v : Fin 3 → ℝ) : ℝ := sv v / enorm3 v

/-- Rotation in the `(e₁, e₂)`-plane: `x ↦ (x 0, ca * x 1 + cb * x 2, -cb * x 1 + ca * x 2)`. -/
def MA (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, ca v, cb v; 0, -cb v, ca v]

/-- Rotation in the `(e₀, e₁)`-plane: `x ↦ (cc * x 0 + cd * x 1, -cd * x 0 + cc * x 1, x 2)`. -/
def MB (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![cc v, cd v, 0; -cd v, cc v, 0; 0, 0, 1]

/-- The composed rotation `MB * MA`. -/
def Mmat (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := MB v * MA v

lemma sv_sq (v : Fin 3 → ℝ) : (sv v) ^ 2 = v 1 ^ 2 + v 2 ^ 2 := by
  rw [sv, Real.sq_sqrt]; positivity

lemma enorm3_sq (v : Fin 3 → ℝ) : (enorm3 v) ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  unfold enorm3
  rw [Real.sq_sqrt (by
    unfold dot3; rw [Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])]
  simp [dot3, Fin.sum_univ_three]; ring

lemma sv_eq_zero (v : Fin 3 → ℝ) (h : sv v = 0) : v 1 = 0 ∧ v 2 = 0 := by
  have h2 : (sv v) ^ 2 = 0 := by rw [h]; ring
  rw [sv_sq] at h2
  constructor <;> nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

lemma enorm3_eq_zero (v : Fin 3 → ℝ) (h : enorm3 v = 0) : v = 0 := by
  have h2 : (enorm3 v) ^ 2 = 0 := by rw [h]; ring
  rw [enorm3_sq] at h2
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h3 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  funext i; fin_cases i <;> simp [h0, h1, h3]

lemma ca_sq_add_cb_sq (v : Fin 3 → ℝ) : ca v ^ 2 + cb v ^ 2 = 1 := by
  unfold ca cb
  by_cases h : sv v = 0
  · simp [h]
  · simp only [h, if_false]
    have h2 : v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by rw [← sv_sq]; exact pow_ne_zero 2 h
    rw [div_pow, div_pow, ← add_div, sv_sq]
    field_simp

lemma cc_sq_add_cd_sq (v : Fin 3 → ℝ) (hv : v ≠ 0) : cc v ^ 2 + cd v ^ 2 = 1 := by
  have hr : enorm3 v ≠ 0 := fun h => hv (enorm3_eq_zero v h)
  unfold cc cd
  have h2 : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by rw [← enorm3_sq]; exact pow_ne_zero 2 hr
  rw [div_pow, div_pow, ← add_div, enorm3_sq]
  field_simp
  rw [sv_sq]; ring

lemma ca_mul_v_one_add_cb_mul_v_two (v : Fin 3 → ℝ) : ca v * v 1 + cb v * v 2 = sv v := by
  unfold ca cb
  by_cases h : sv v = 0
  · obtain ⟨h1, h2⟩ := sv_eq_zero v h
    simp [h, h1, h2]
  · simp only [h, if_false]
    have h2 : v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by rw [← sv_sq]; exact pow_ne_zero 2 h
    field_simp
    rw [sv_sq]

lemma neg_cb_mul_v_one_add_ca_mul_v_two (v : Fin 3 → ℝ) : -cb v * v 1 + ca v * v 2 = 0 := by
  unfold ca cb
  by_cases h : sv v = 0
  · obtain ⟨h1, h2⟩ := sv_eq_zero v h
    simp [h, h1, h2]
  · simp only [h, if_false]
    have h2 : v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by rw [← sv_sq]; exact pow_ne_zero 2 h
    field_simp; ring

lemma cc_mul_v_zero_add_cd_mul_sv (v : Fin 3 → ℝ) : cc v * v 0 + cd v * sv v = enorm3 v := by
  have h3 : (v 0) ^ 2 + (sv v) ^ 2 = (enorm3 v) ^ 2 := by rw [sv_sq, enorm3_sq]; ring
  unfold cc cd
  by_cases hr : enorm3 v = 0
  · simp [hr]
  · field_simp
    rw [h3]

lemma neg_cd_mul_v_zero_add_cc_mul_sv (v : Fin 3 → ℝ) : -cd v * v 0 + cc v * sv v = 0 := by
  unfold cc cd; field_simp; ring

lemma abs_ca_le_one (v : Fin 3 → ℝ) : |ca v| ≤ 1 := by
  rw [abs_le]; constructor <;>
    nlinarith [ca_sq_add_cb_sq v, sq_nonneg (cb v)]

lemma abs_cb_le_one (v : Fin 3 → ℝ) : |cb v| ≤ 1 := by
  rw [abs_le]; constructor <;>
    nlinarith [ca_sq_add_cb_sq v, sq_nonneg (ca v)]

lemma abs_cc_le_one (v : Fin 3 → ℝ) (hv : v ≠ 0) : |cc v| ≤ 1 := by
  rw [abs_le]; constructor <;>
    nlinarith [cc_sq_add_cd_sq v hv, sq_nonneg (cd v)]

lemma abs_cd_le_one (v : Fin 3 → ℝ) (hv : v ≠ 0) : |cd v| ≤ 1 := by
  rw [abs_le]; constructor <;>
    nlinarith [cc_sq_add_cd_sq v hv, sq_nonneg (cc v)]

end

end Work.EKLComp
