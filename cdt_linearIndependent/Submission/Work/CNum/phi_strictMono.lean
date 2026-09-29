import Mathlib
import Submission.Work.CNum.Basic

/-!
# Strict monotonicity of `phiR` on the arc `(-α, α)`

`phiR θ = θ/2 + π + arctan (QR θ / PR θ)` is the argument of the contour map
`psiC` on the unit-circle arc `C₁`, parametrised by the angle `θ ∈ (-α, α)`
where `α = arccos γ` is the cusp half-angle.  We prove that `phiR` is strictly
increasing there.

The key observation is that on the arc the two quantities `PR θ` and `QR θ`
satisfy `PR θ ^ 2 + QR θ ^ 2 = 2·A·(1-γ)` *independently of `θ`* (because
`A = (1+c²)²`), so that

  `arctan (QR θ / PR θ) = arcsin (QR θ / √(2·A·(1-γ)))`,

and `QR θ = 2(1+c²) sin(θ/2)` is strictly increasing in `θ` on `(-α, α)`.
Adding the strictly increasing term `θ/2 + π` yields the result.
-/

namespace Work.CNum

/-! ## Elementary facts about the constants -/

lemma gamR_lt_one : gamR < 1 := by norm_num [gamR, cR, AR]
lemma gamR_gt_neg_one : -1 < gamR := by norm_num [gamR, cR, AR]
lemma alpR_pos_phi_strictMono : 0 < alpR := by rw [alpR, Real.arccos_pos]; exact gamR_lt_one
lemma alpR_lt_pi_phi_strictMono : alpR < Real.pi := by rw [alpR, Real.arccos_lt_pi]; exact gamR_gt_neg_one
lemma cos_alpR_phi_strictMono : Real.cos alpR = gamR :=
  Real.cos_arccos (le_of_lt gamR_gt_neg_one) (le_of_lt gamR_lt_one)

lemma AR_pos : 0 < AR := by norm_num [AR, cR]

lemma two_AR_one_sub_gamR_pos : 0 < 2 * AR * (1 - gamR) := by
  norm_num [AR, cR, gamR]

/-! ## A general tangent/arcsine identity -/

/-- For `P > 0`, `arctan (Q/P) = arcsin (Q/√(P²+Q²))`. -/
lemma arctan_div_eq_arcsin_div {P Q : ℝ} (hP : 0 < P) :
    Real.arctan (Q / P) = Real.arcsin (Q / Real.sqrt (P^2 + Q^2)) := by
  rw [Real.arctan_eq_arcsin]
  congr 1
  have h1 : (1 + (Q/P)^2) = (P^2+Q^2)/P^2 := by field_simp
  rw [h1, Real.sqrt_div (by positivity : (0:ℝ) ≤ P^2+Q^2) (P^2), Real.sqrt_sq (le_of_lt hP)]
  field_simp

/-! ## The geometry of the arc -/

lemma cos_gt_gamR {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) : gamR < Real.cos θ := by
  have habs : |θ| < alpR := abs_lt.mpr hθ
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) (le_of_lt alpR_lt_pi_phi_strictMono) habs
  rw [Real.cos_abs] at h
  rwa [← cos_alpR_phi_strictMono]

lemma PR_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) : 0 < PR θ := by
  unfold PR
  rw [Real.sqrt_pos]
  have h1 : 0 < 2 * AR := by linarith [AR_pos]
  have h2 : 0 < Real.cos θ - gamR := by linarith [cos_gt_gamR hθ]
  exact mul_pos h1 h2

lemma PR_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    PR θ ^ 2 = 2 * AR * (Real.cos θ - gamR) := by
  unfold PR
  refine Real.sq_sqrt ?_
  have h1 : 0 < 2 * AR := by linarith [AR_pos]
  have h2 : 0 < Real.cos θ - gamR := by linarith [cos_gt_gamR hθ]
  exact le_of_lt (mul_pos h1 h2)

lemma QR_sq (θ : ℝ) : QR θ ^ 2 = 4 * AR * Real.sin (θ / 2) ^ 2 := by
  unfold QR AR
  ring

lemma cos_eq_one_sub_two_sin_sq (θ : ℝ) :
    Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring, Real.cos_sq'] at h
  linarith

/-- `PR θ ^ 2 + QR θ ^ 2` is constant on the arc. -/
lemma PR_sq_add_QR_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    PR θ ^ 2 + QR θ ^ 2 = 2 * AR * (1 - gamR) := by
  rw [PR_sq hθ, QR_sq θ, cos_eq_one_sub_two_sin_sq θ]
  ring

/-- The `arctan` part of `phiR`, rewritten as an `arcsin` of a strictly
increasing function. -/
lemma arctan_QR_div_PR {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    Real.arctan (QR θ / PR θ) =
      Real.arcsin (QR θ / Real.sqrt (2 * AR * (1 - gamR))) := by
  rw [arctan_div_eq_arcsin_div (PR_pos hθ), PR_sq_add_QR_sq hθ]

lemma abs_QR_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    |QR θ| ≤ Real.sqrt (2 * AR * (1 - gamR)) := by
  rw [← Real.sqrt_sq_eq_abs (QR θ)]
  apply Real.sqrt_le_sqrt
  have h1 : (0:ℝ) ≤ PR θ ^ 2 := sq_nonneg _
  have h2 := PR_sq_add_QR_sq hθ
  linarith

/-! ## The main theorem -/

theorem phi_strictMono : StrictMonoOn phiR (Set.Ioo (-alpR) alpR) := by
  intro a ha b hb hab
  have hρ : 0 < Real.sqrt (2 * AR * (1 - gamR)) := Real.sqrt_pos.mpr two_AR_one_sub_gamR_pos
  have ha2 : -(Real.pi / 2) ≤ a / 2 := by have := alpR_lt_pi_phi_strictMono; linarith [ha.1]
  have hb2 : b / 2 ≤ Real.pi / 2 := by have := alpR_lt_pi_phi_strictMono; linarith [hb.2]
  have hsin : Real.sin (a / 2) < Real.sin (b / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two ha2 hb2 (by linarith)
  have hQR : QR a < QR b := by
    unfold QR
    exact mul_lt_mul_of_pos_left hsin (by positivity)
  have hdiv : QR a / Real.sqrt (2 * AR * (1 - gamR)) <
      QR b / Real.sqrt (2 * AR * (1 - gamR)) := div_lt_div_of_pos_right hQR hρ
  have hlow : -(1:ℝ) ≤ QR a / Real.sqrt (2 * AR * (1 - gamR)) := by
    rw [le_div_iff₀ hρ]
    have := (abs_le.mp (abs_QR_le ha)).1
    linarith
  have hhigh : QR b / Real.sqrt (2 * AR * (1 - gamR)) ≤ 1 := by
    rw [div_le_iff₀ hρ]
    have := (abs_le.mp (abs_QR_le hb)).2
    linarith
  have harcsin := Real.arcsin_lt_arcsin hlow hdiv hhigh
  show a / 2 + Real.pi + Real.arctan (QR a / PR a) <
      b / 2 + Real.pi + Real.arctan (QR b / PR b)
  rw [arctan_QR_div_PR ha, arctan_QR_div_PR hb]
  linarith

end Work.CNum
