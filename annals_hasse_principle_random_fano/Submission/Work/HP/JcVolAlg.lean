import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.JcVolDelta

/-!
# The two-dimensional algebra of the plane `P = ℝw ⊕ ℝz`
-/

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP
namespace JcVolAlg

variable {ι : Type*} [Fintype ι]

lemma deltaV_ne_zero {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) : deltaV w z ≠ 0 :=
  (JcVolDelta h).ne'

/-- Norm squared of a two-term linear combination. -/
lemma norm_add_smul_sq (p q : ℝ) (X Y : EuclideanSpace ℝ ι) :
    ‖p • X + q • Y‖ ^ 2 = p ^ 2 * ‖X‖ ^ 2 + 2 * p * q * inner ℝ X Y + q ^ 2 * ‖Y‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, real_inner_smul_left, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
    sq_abs]
  ring

/-- Norm squared of a two-term difference. -/
lemma norm_sub_smul_sq (p q : ℝ) (X Y : EuclideanSpace ℝ ι) :
    ‖p • X - q • Y‖ ^ 2 = p ^ 2 * ‖X‖ ^ 2 - 2 * p * q * inner ℝ X Y + q ^ 2 * ‖Y‖ ^ 2 := by
  rw [norm_sub_sq_real]
  simp only [norm_smul, real_inner_smul_left, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
    sq_abs]
  ring

@[simp] lemma inner_w_self (w : EuclideanSpace ℝ ι) : inner ℝ w w = ‖w‖ ^ 2 :=
  real_inner_self_eq_norm_sq w

/-- `⟪w, c₁⟫ = 1`. -/
lemma inner_w_c1V {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) : inner ℝ w (c1V w z) = 1 := by
  have hδ := deltaV_ne_zero h
  rw [c1V, inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [inv_mul_eq_iff_eq_mul₀ hδ, deltaV]
  ring

/-- `⟪z, c₁⟫ = 0`. -/
lemma inner_z_c1V {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) : inner ℝ z (c1V w z) = 0 := by
  rw [c1V, inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  ring

/-- `⟪w, c₂⟫ = 0`. -/
lemma inner_w_c2V {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) : inner ℝ w (c2V w z) = 0 := by
  rw [c2V, inner_smul_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- `⟪z, c₂⟫ = 1`. -/
lemma inner_z_c2V {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) : inner ℝ z (c2V w z) = 1 := by
  have hδ := deltaV_ne_zero h
  rw [c2V, inner_smul_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [inv_mul_eq_iff_eq_mul₀ hδ, deltaV]
  simp only [real_inner_comm]
  ring

/-- The coordinate map inverts `cComb`: `Λ (u₀c₁ + u₁c₂) = u`. -/
lemma lam_cComb {w z : EuclideanSpace ℝ ι} (h : IsIndep w z)
    (u : EuclideanSpace ℝ (Fin 2)) :
    lamP w z ⟨cComb w z u, cComb_mem w z u⟩ = u := by
  ext i
  fin_cases i
  · show inner ℝ w (cComb w z u) = u 0
    rw [cComb, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_w_c1V h, inner_w_c2V h]
    ring
  · show inner ℝ z (cComb w z u) = u 1
    rw [cComb, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_z_c1V h, inner_z_c2V h]
    ring

/-- `cComb u = δ⁻¹ • ((u₀‖z‖² - u₁⟪w,z⟫)w + (u₁‖w‖² - u₀⟪w,z⟫)z)`. -/
lemma cComb_eq {w z : EuclideanSpace ℝ ι} (u : EuclideanSpace ℝ (Fin 2)) :
    cComb w z u = (deltaV w z)⁻¹ • ((u 0 * ‖z‖ ^ 2 - u 1 * inner ℝ w z) • w +
      (u 1 * ‖w‖ ^ 2 - u 0 * inner ℝ w z) • z) := by
  simp only [cComb, c1V, c2V, smul_add, smul_sub, smul_smul]
  module

/-- The quadratic identity `δ‖u₀c₁ + u₁c₂‖² = ‖u₀z - u₁w‖²`. -/
lemma norm_cComb_mul {w z : EuclideanSpace ℝ ι} (h : IsIndep w z)
    (u : EuclideanSpace ℝ (Fin 2)) :
    deltaV w z * ‖cComb w z u‖ ^ 2 = ‖(u 0) • z - (u 1) • w‖ ^ 2 := by
  have hδ := deltaV_ne_zero h
  rw [cComb_eq u, norm_smul, mul_pow]
  simp only [norm_inv, Real.norm_eq_abs, sq_abs, inv_pow]
  rw [norm_add_smul_sq, norm_sub_smul_sq]
  field_simp
  rw [deltaV]
  simp only [real_inner_comm]
  ring

/-- For `a ∈ P`, `δ‖a‖² = ‖⟪w,a⟫ z - ⟪z,a⟫ w‖²`. -/
lemma norm_eq_pairing {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) {a : EuclideanSpace ℝ ι}
    (ha : a ∈ planeP w z) :
    deltaV w z * ‖a‖ ^ 2 = ‖(inner ℝ w a) • z - (inner ℝ z a) • w‖ ^ 2 := by
  obtain ⟨c, d, rfl⟩ := (Submodule.mem_span_pair).mp (by simpa [planeP] using ha)
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, norm_add_smul_sq, norm_sub_smul_sq]
  rw [deltaV]
  simp only [real_inner_comm]
  ring

/-- `qform w z (Λ a) = ‖a‖²` for `a ∈ P`. -/
lemma qform_lam {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) (a : ↥(planeP w z)) :
    qform w z (lamP w z a) = ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 := by
  have hδ := deltaV_ne_zero h
  have h0 : (lamP w z a) 0 = inner ℝ w (a : EuclideanSpace ℝ ι) := rfl
  have h1 : (lamP w z a) 1 = inner ℝ z (a : EuclideanSpace ℝ ι) := rfl
  rw [qform, h0, h1, div_eq_iff hδ]
  simpa [mul_comm] using (norm_eq_pairing h a.2).symm

end JcVolAlg
end Work.HP
