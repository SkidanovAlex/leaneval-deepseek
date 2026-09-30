import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.bprod_real_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! ### Auxiliary estimates for the per-pair lower bound

`bfac R k z = R(z − k)/(R² − kz)`.  On the circle `‖z − l‖ = η`, writing `z = l + t + iy` with
`t² + y² = η²` and `t = (z − l).re`, the squared modulus of one factor is
`‖β(z;κ)‖² = R²(A + Bt)/(P + Qt)` with `A = (l−κ)² + η²`, `B = 2(l−κ)`,
`P = (R²−κl)² + κ²η²`, `Q = −2κ(R²−κl)`.  A ratio of linear functions of `t` is monotone, with
derivative of sign `BP − AQ = 2(R²−κ²)((l−κ)(R²−κl) + κη²)`; hence the minimum of `‖β(·;κ)‖` over
the circle is attained at `t = ±η`, i.e. at the real point `z = l ∓ η`.  This is the tool for the
per-pair bound: depending on whether `k ≤ l` or `k > l`, the two factors `κ = k` and `κ = −k`
are bounded at the same or at different endpoints, and evaluating at a real point turns
`R²|z²−k²|/|R⁴−k²z²|` into the algebraic factor of BW p. 51. -/

/-- Norm of a real cast. -/
lemma norm_ofReal_cast (r : ℝ) : ‖((r:ℝ):ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- Square of the norm of a real cast. -/
lemma norm_ofReal_cast_sq (r : ℝ) : ‖((r:ℝ):ℂ)‖^2 = r^2 := by
  rw [show ‖((r:ℝ):ℂ)‖ = |r| from RCLike.norm_ofReal r, sq_abs]

/-- `‖z − κ‖²` on the circle `‖z − l‖ = η`, expanded around `l`. -/
lemma normSq_sub_k (η l : ℝ) (κ : ℤ) (z : ℂ) (hz : ‖z - (l:ℂ)‖ = η) :
    Complex.normSq (z - (κ:ℂ)) = ((l-(κ:ℝ))^2 + η^2 + 2*(l-(κ:ℝ))*((z-(l:ℂ)).re)) := by
  have h1 : z - (κ:ℂ) = (z - (l:ℂ)) + ((l - (κ:ℝ) : ℝ):ℂ) := by push_cast; ring
  rw [h1, Complex.normSq_add, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, hz]
  have h2 : ((z - (l:ℂ)) * (starRingEnd ℂ) ((l - (κ:ℝ) : ℝ):ℂ)).re
      = (l-(κ:ℝ))*((z-(l:ℂ)).re) := by
    rw [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2]; ring

/-- `‖R² − κz‖²` on the circle `‖z − l‖ = η`, expanded around `l`. -/
lemma normSq_R2_sub_k (R η l : ℝ) (κ : ℤ) (z : ℂ) (hz : ‖z - (l:ℂ)‖ = η) :
    Complex.normSq ((R:ℂ)^2 - (κ:ℂ)*z)
      = (R^2 - (κ:ℝ)*l)^2 + (κ:ℝ)^2*η^2 - 2*(κ:ℝ)*(R^2-(κ:ℝ)*l)*((z-(l:ℂ)).re) := by
  have h1 : (R:ℂ)^2 - (κ:ℂ)*z = (((R^2 - (κ:ℝ)*l : ℝ)):ℂ) - ((κ:ℝ):ℂ)*(z - (l:ℂ)) := by
    push_cast; ring
  rw [h1, Complex.normSq_sub, Complex.normSq_ofReal, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq, hz]
  have h2 : ((((R^2 - (κ:ℝ)*l : ℝ)):ℂ) * (starRingEnd ℂ) (((κ:ℝ):ℂ) * (z - (l:ℂ)))).re
      = (R^2-(κ:ℝ)*l) * ((κ:ℝ)*((z-(l:ℂ)).re)) := by
    rw [map_mul, Complex.conj_ofReal]
    have h4 : (((R^2 - (κ:ℝ)*l : ℝ)):ℂ) * (((κ:ℝ):ℂ) * (starRingEnd ℂ) (z - (l:ℂ)))
        = ((((R^2-(κ:ℝ)*l)*(κ:ℝ)):ℝ):ℂ) * (starRingEnd ℂ) (z - (l:ℂ)) := by
      push_cast; ring
    rw [h4, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.conj_re]
    simp only [Complex.sub_re, Complex.ofReal_re]
    ring
  rw [h2]; ring

/-- The squared modulus of one Blaschke factor on the circle, written with
`A = (l−κ)² + η²`, `B = 2(l−κ)`, `P = (R²−κl)² + κ²η²`, `Q = −2κ(R²−κl)` and `t = (z − l).re`. -/
lemma bfac_normSq_circle (R η l : ℝ) (κ : ℤ) (z : ℂ) (hz : ‖z - (l:ℂ)‖ = η) :
    ‖bfac R κ z‖^2 = R^2 * (((l-(κ:ℝ))^2 + η^2 + 2*(l-(κ:ℝ))*(z-(l:ℂ)).re)
      / ((R^2 - (κ:ℝ)*l)^2 + (κ:ℝ)^2*η^2 - 2*(κ:ℝ)*(R^2-(κ:ℝ)*l)*(z-(l:ℂ)).re)) := by
  have hL : ‖bfac R κ z‖^2
      = R^2 * Complex.normSq (z - (κ:ℂ)) / Complex.normSq ((R:ℂ)^2 - (κ:ℂ)*z) := by
    rw [← Complex.normSq_eq_norm_sq, bfac, Complex.normSq_div, Complex.normSq_mul,
        Complex.normSq_ofReal]
    ring
  rw [hL, normSq_sub_k η l κ z hz, normSq_R2_sub_k R η l κ z hz]
  rw [mul_div_assoc]

/-- `bfac_normSq_circle` written as `R²` times a single quotient of linear functions of `t`. -/
lemma bfac_sq_circle (R η l : ℝ) (κ : ℤ) (z : ℂ) (hz : ‖z - (l:ℂ)‖ = η) :
    ‖bfac R κ z‖^2 = R^2 * ((((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
      / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))) := by
  have hD : (R^2 - (κ:ℝ)*l)^2 + (κ:ℝ)^2*η^2 - 2*(κ:ℝ)*(R^2-(κ:ℝ)*l)*(z-(l:ℂ)).re
      = ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re) := by ring
  rw [bfac_normSq_circle R η l κ z hz, hD]

/-- The squared modulus of `β(·;κ)` at `z = l − η`, as `R²` times `(A − Bη)/(P − Qη)`. -/
lemma bfac_sq_left (R η l : ℝ) (κ : ℤ) :
    ‖bfac R κ ((l-η:ℝ):ℂ)‖^2 = R^2 * ((((l-(κ:ℝ))^2+η^2) - (2*(l-(κ:ℝ)))*η)
      / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η)) := by
  rw [bfac_ofReal, norm_ofReal_cast_sq, div_pow, mul_pow]
  rw [show l - η - (κ:ℝ) = (l - (κ:ℝ)) - η by ring,
      show R^2 - (κ:ℝ)*(l-η) = (R^2 - (κ:ℝ)*l) + (κ:ℝ)*η by ring]
  rw [show ((l - (κ:ℝ)) - η)^2 = ((l-(κ:ℝ))^2+η^2) - (2*(l-(κ:ℝ)))*η by ring,
      show ((R^2 - (κ:ℝ)*l) + (κ:ℝ)*η)^2
        = ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η by ring]
  rw [mul_div_assoc]

/-- The squared modulus of `β(·;κ)` at `z = l + η`, as `R²` times `(A + Bη)/(P + Qη)`. -/
lemma bfac_sq_right (R η l : ℝ) (κ : ℤ) :
    ‖bfac R κ ((l+η:ℝ):ℂ)‖^2 = R^2 * ((((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*η)
      / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η)) := by
  rw [bfac_ofReal, norm_ofReal_cast_sq, div_pow, mul_pow]
  rw [show l + η - (κ:ℝ) = (l - (κ:ℝ)) + η by ring,
      show R^2 - (κ:ℝ)*(l+η) = (R^2 - (κ:ℝ)*l) - (κ:ℝ)*η by ring]
  rw [show ((l - (κ:ℝ)) + η)^2 = ((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*η by ring,
      show ((R^2 - (κ:ℝ)*l) - (κ:ℝ)*η)^2
        = ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η by ring]
  rw [mul_div_assoc]

/-- **Endpoint lower bound for one factor.**  If `BP − AQ = 2(R²−κ²)((l−κ)(R²−κl) + κη²) ≥ 0`,
the modulus of `β(·;κ)` on the circle `‖z − l‖ = η` is minimal at the real point `z = l − η`. -/
lemma bfac_le_left_endpoint (R η l : ℝ) (κ : ℤ) (z : ℂ) (hR : 0 < R)
    (hz : ‖z - (l:ℂ)‖ = η) (hzR : ‖z‖ ≤ R) (hlηR : |l - η| ≤ R) (hκR : |(κ:ℝ)| < R)
    (hsgn : 0 ≤ (R^2 - (κ:ℝ)^2) * ((l - (κ:ℝ))*(R^2 - (κ:ℝ)*l) + (κ:ℝ)*η^2)) :
    ‖bfac R κ ((l - η : ℝ):ℂ)‖ ≤ ‖bfac R κ z‖ := by
  have ht : -η ≤ (z - (l:ℂ)).re := by
    have h1 : |(z - (l:ℂ)).re| ≤ η := (Complex.abs_re_le_norm (z - (l:ℂ))).trans_eq hz
    exact (abs_le.mp h1).1
  have hκnorm : ‖(κ:ℂ)‖ = |(κ:ℝ)| := by
    rw [← Complex.ofReal_intCast κ]; exact RCLike.norm_ofReal _
  have hnz : ((R:ℂ)^2 - (κ:ℂ)*z) ≠ 0 := by
    have hlt : ‖(κ:ℂ)*z‖ < ‖(R:ℂ)^2‖ := by
      have h1 : ‖(κ:ℂ)*z‖ = |(κ:ℝ)| * ‖z‖ := by rw [norm_mul, hκnorm]
      have h2 : ‖(R:ℂ)^2‖ = R^2 := by
        rw [norm_pow, show ‖((R:ℝ):ℂ)‖ = |R| from RCLike.norm_ofReal R, abs_of_pos hR]
      rw [h1, h2]
      have hstep1 : |(κ:ℝ)| * ‖z‖ ≤ |(κ:ℝ)| * R := mul_le_mul_of_nonneg_left hzR (abs_nonneg _)
      have hstep2 : |(κ:ℝ)| * R < R^2 := by
        have h3 := mul_lt_mul_of_pos_right hκR hR
        nlinarith [h3]
      linarith
    intro h0
    have h3 : ‖(R:ℂ)^2‖ = ‖(κ:ℂ)*z‖ := by rw [sub_eq_zero.mp h0]
    linarith
  have hD : 0 < ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re) := by
    have hbridge : ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re)
        = Complex.normSq ((R:ℂ)^2 - (κ:ℂ)*z) := by
      rw [normSq_R2_sub_k R η l κ z hz]; ring
    rw [hbridge, Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hnz) 2
  have hDx : 0 < ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η := by
    have h : ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η
        = (R^2 - (κ:ℝ)*(l-η))^2 := by ring
    rw [h]
    apply sq_pos_of_ne_zero
    intro h0
    have h1 : |(κ:ℝ)*(l-η)| = |(κ:ℝ)| * |l-η| := abs_mul _ _
    have h2 : |(κ:ℝ)| * |l-η| ≤ |(κ:ℝ)| * R := mul_le_mul_of_nonneg_left hlηR (abs_nonneg _)
    have h3 : |(κ:ℝ)| * R < R*R := mul_lt_mul_of_pos_right hκR hR
    have h5 : (κ:ℝ)*(l-η) = R^2 := by linarith [sub_eq_zero.mp h0]
    have h6 : |(κ:ℝ)| * |l-η| = R^2 := by
      rw [← h1, h5, abs_of_pos (pow_pos hR 2)]
    nlinarith [h6, h2, h3]
  have hBP : 0 ≤ (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)
      - ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l)) := by
    have h : (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)
        - ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))
        = 2 * ((R^2 - (κ:ℝ)^2) * ((l - (κ:ℝ))*(R^2 - (κ:ℝ)*l) + (κ:ℝ)*η^2)) := by ring
    rw [h]; linarith
  have hident : (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η)
      - (((l-(κ:ℝ))^2+η^2) - (2*(l-(κ:ℝ)))*η)
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))
      = (((z-(l:ℂ)).re) + η)
        * ((2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)
            - ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))) := by ring
  have hcross : (((l-(κ:ℝ))^2+η^2) - (2*(l-(κ:ℝ)))*η)
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))
      ≤ (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η) := by
    nlinarith [hident, mul_nonneg (by linarith : (0:ℝ) ≤ (z-(l:ℂ)).re + η) hBP]
  have hinner : ((((l-(κ:ℝ))^2+η^2) - (2*(l-(κ:ℝ)))*η)
        / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) - (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η))
      ≤ ((((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))) := by
    rw [div_le_div_iff₀ hDx hD]
    exact hcross
  have hsq : ‖bfac R κ ((l-η:ℝ):ℂ)‖^2 ≤ ‖bfac R κ z‖^2 := by
    rw [bfac_sq_left R η l κ, bfac_sq_circle R η l κ z hz]
    exact mul_le_mul_of_nonneg_left hinner (sq_nonneg R)
  calc ‖bfac R κ ((l-η:ℝ):ℂ)‖ = Real.sqrt (‖bfac R κ ((l-η:ℝ):ℂ)‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖bfac R κ z‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖bfac R κ z‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Endpoint lower bound for one factor, other endpoint.**  If
`BP − AQ = 2(R²−κ²)((l−κ)(R²−κl) + κη²) ≤ 0`, the modulus of `β(·;κ)` on the circle
`‖z − l‖ = η` is minimal at the real point `z = l + η`. -/
lemma bfac_le_right_endpoint (R η l : ℝ) (κ : ℤ) (z : ℂ) (hR : 0 < R)
    (hz : ‖z - (l:ℂ)‖ = η) (hzR : ‖z‖ ≤ R) (hlηR : |l + η| ≤ R) (hκR : |(κ:ℝ)| < R)
    (hsgn : (R^2 - (κ:ℝ)^2) * ((l - (κ:ℝ))*(R^2 - (κ:ℝ)*l) + (κ:ℝ)*η^2) ≤ 0) :
    ‖bfac R κ ((l + η : ℝ):ℂ)‖ ≤ ‖bfac R κ z‖ := by
  have ht : (z - (l:ℂ)).re ≤ η := by
    have h1 : |(z - (l:ℂ)).re| ≤ η := (Complex.abs_re_le_norm (z - (l:ℂ))).trans_eq hz
    exact (abs_le.mp h1).2
  have hκnorm : ‖(κ:ℂ)‖ = |(κ:ℝ)| := by
    rw [← Complex.ofReal_intCast κ]; exact RCLike.norm_ofReal _
  have hnz : ((R:ℂ)^2 - (κ:ℂ)*z) ≠ 0 := by
    have hlt : ‖(κ:ℂ)*z‖ < ‖(R:ℂ)^2‖ := by
      have h1 : ‖(κ:ℂ)*z‖ = |(κ:ℝ)| * ‖z‖ := by rw [norm_mul, hκnorm]
      have h2 : ‖(R:ℂ)^2‖ = R^2 := by
        rw [norm_pow, show ‖((R:ℝ):ℂ)‖ = |R| from RCLike.norm_ofReal R, abs_of_pos hR]
      rw [h1, h2]
      have hstep1 : |(κ:ℝ)| * ‖z‖ ≤ |(κ:ℝ)| * R := mul_le_mul_of_nonneg_left hzR (abs_nonneg _)
      have hstep2 : |(κ:ℝ)| * R < R^2 := by
        have h3 := mul_lt_mul_of_pos_right hκR hR
        nlinarith [h3]
      linarith
    intro h0
    have h3 : ‖(R:ℂ)^2‖ = ‖(κ:ℂ)*z‖ := by rw [sub_eq_zero.mp h0]
    linarith
  have hD : 0 < ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re) := by
    have hbridge : ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re)
        = Complex.normSq ((R:ℂ)^2 - (κ:ℂ)*z) := by
      rw [normSq_R2_sub_k R η l κ z hz]; ring
    rw [hbridge, Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hnz) 2
  have hDx : 0 < ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η := by
    have h : ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η
        = (R^2 - (κ:ℝ)*(l+η))^2 := by ring
    rw [h]
    apply sq_pos_of_ne_zero
    intro h0
    have h1 : |(κ:ℝ)*(l+η)| = |(κ:ℝ)| * |l+η| := abs_mul _ _
    have h2 : |(κ:ℝ)| * |l+η| ≤ |(κ:ℝ)| * R := mul_le_mul_of_nonneg_left hlηR (abs_nonneg _)
    have h3 : |(κ:ℝ)| * R < R*R := mul_lt_mul_of_pos_right hκR hR
    have h5 : (κ:ℝ)*(l+η) = R^2 := by linarith [sub_eq_zero.mp h0]
    have h6 : |(κ:ℝ)| * |l+η| = R^2 := by
      rw [← h1, h5, abs_of_pos (pow_pos hR 2)]
    nlinarith [h6, h2, h3]
  have hBP : (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)
      - ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l)) ≤ 0 := by
    have h : (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)
        - ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))
        = 2 * ((R^2 - (κ:ℝ)^2) * ((l - (κ:ℝ))*(R^2 - (κ:ℝ)*l) + (κ:ℝ)*η^2)) := by ring
    rw [h]; linarith
  have hident : (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η)
      - (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*η)
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))
      = (η - (z-(l:ℂ)).re)
        * (((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))
            - (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2)) := by ring
  have hcross : (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*η)
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))
      ≤ (((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        * (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η) := by
    have h1 : (0:ℝ) ≤ η - (z-(l:ℂ)).re := by linarith
    have h2 : (0:ℝ) ≤ ((l-(κ:ℝ))^2+η^2) * (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))
        - (2*(l-(κ:ℝ))) * ((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) := by linarith [hBP]
    nlinarith [hident, mul_nonneg h1 h2]
  have hinner : ((((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*η)
        / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*η))
      ≤ ((((l-(κ:ℝ))^2+η^2) + (2*(l-(κ:ℝ)))*((z-(l:ℂ)).re))
        / (((R^2-(κ:ℝ)*l)^2+(κ:ℝ)^2*η^2) + (-2*(κ:ℝ)*(R^2-(κ:ℝ)*l))*((z-(l:ℂ)).re))) := by
    rw [div_le_div_iff₀ hDx hD]
    exact hcross
  have hsq : ‖bfac R κ ((l+η:ℝ):ℂ)‖^2 ≤ ‖bfac R κ z‖^2 := by
    rw [bfac_sq_right R η l κ, bfac_sq_circle R η l κ z hz]
    exact mul_le_mul_of_nonneg_left hinner (sq_nonneg R)
  calc ‖bfac R κ ((l+η:ℝ):ℂ)‖ = Real.sqrt (‖bfac R κ ((l+η:ℝ):ℂ)‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖bfac R κ z‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖bfac R κ z‖ := Real.sqrt_sq (norm_nonneg _)

/-- Modulus of `bfac` at a real point. -/
lemma bfac_norm_ofReal (R : ℝ) (hR : 0 < R) (κ : ℤ) (x : ℝ) :
    ‖bfac R κ (x:ℂ)‖ = R * |x - (κ:ℝ)| / |R^2 - (κ:ℝ)*x| := by
  rw [bfac_ofReal]
  rw [show ‖(((R * (x - (κ:ℝ)) / (R^2 - (κ:ℝ)*x)) : ℝ):ℂ)‖
        = |R * (x - (κ:ℝ)) / (R^2 - (κ:ℝ)*x)| from RCLike.norm_ofReal _]
  rw [abs_div, abs_mul, abs_of_pos hR]

/-- Pairing `k` and `−k` at the same real point `x`: the product of the two moduli is at least
`|x−k| · |x+k| / R²`. -/
lemma bfac_pair_real_ge (R : ℝ) (hR : 0 < R) (k : ℤ) (x : ℝ) (hx : |x| ≤ R)
    (hk : |(k:ℝ)| < R) :
    |x - (k:ℝ)| * |x + (k:ℝ)| / R^2 ≤ ‖bfac R k (x:ℂ) * bfac R (-k) (x:ℂ)‖ := by
  have hA : 0 < R^2 - (k:ℝ)*x := by
    have h4 : |(k:ℝ)*x| ≤ |(k:ℝ)| * R := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have h5 : |(k:ℝ)| * R < R*R := mul_lt_mul_of_pos_right hk hR
    have h6 : (k:ℝ)*x ≤ |(k:ℝ)*x| := le_abs_self _
    nlinarith [h4, h5, h6]
  have hB : 0 < R^2 + (k:ℝ)*x := by
    have h4 : |(k:ℝ)*x| ≤ |(k:ℝ)| * R := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have h5 : |(k:ℝ)| * R < R*R := mul_lt_mul_of_pos_right hk hR
    have h6 : -((k:ℝ)*x) ≤ |(k:ℝ)*x| := neg_le_abs _
    nlinarith [h4, h5, h6]
  have hden : 0 < R^4 - (k:ℝ)^2*x^2 := by
    have h : R^4 - (k:ℝ)^2*x^2 = (R^2-(k:ℝ)*x)*(R^2+(k:ℝ)*x) := by ring
    rw [h]; exact mul_pos hA hB
  have hden_le : R^4 - (k:ℝ)^2*x^2 ≤ R^4 := by nlinarith [sq_nonneg ((k:ℝ)*x)]
  rw [norm_mul, bfac_norm_ofReal R hR k x, bfac_norm_ofReal R hR (-k) x, Int.cast_neg]
  rw [show x - -(k:ℝ) = x + (k:ℝ) by ring,
      show R^2 - -(k:ℝ)*x = R^2 + (k:ℝ)*x by ring]
  rw [abs_of_pos hA, abs_of_pos hB]
  rw [div_mul_div_comm]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < R^2) (mul_pos hA hB)]
  have ha : (0:ℝ) ≤ |x - (k:ℝ)| * |x + (k:ℝ)| := by positivity
  have hstep : (|x - (k:ℝ)| * |x + (k:ℝ)|) * (R^4 - (k:ℝ)^2*x^2)
      ≤ (|x - (k:ℝ)| * |x + (k:ℝ)|) * R^4 := mul_le_mul_of_nonneg_left hden_le ha
  nlinarith [hstep]

/-- Pairing `k` and `−k` at the two real points `l+η` and `l−η` (`l ≥ 0`, `η < R`). -/
lemma bfac_pair_split_ge (R η l : ℝ) (k : ℤ) (hR : 0 < R) (hη : 0 < η) (hl0 : 0 ≤ l)
    (hk1 : 0 < (k:ℝ)) (hkR : |(k:ℝ)| < R) (hηR : η < R)
    (hxp : |l + η| ≤ R) (hxm : |l - η| ≤ R) :
    |(l + η) - (k:ℝ)| * |(l - η) + (k:ℝ)| / R^2
      ≤ ‖bfac R k ((l+η:ℝ):ℂ) * bfac R (-k) ((l-η:ℝ):ℂ)‖ := by
  have hklt : (k:ℝ) < R := (le_abs_self _).trans_lt hkR
  have hA : 0 < R^2 - (k:ℝ)*(l+η) := by
    have h1 : (k:ℝ)*(l+η) ≤ (k:ℝ)*R := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hk1)
      exact (le_abs_self _).trans hxp
    have h2 : (k:ℝ)*R < R*R := mul_lt_mul_of_pos_right hklt hR
    nlinarith [h1, h2]
  have hB : 0 < R^2 + (k:ℝ)*(l-η) := by
    have h4 : -R ≤ l - η := by linarith [neg_abs_le (l-η), hxm]
    have h3 : -((k:ℝ)*R) ≤ (k:ℝ)*(l-η) := by nlinarith [h4, hk1]
    have h6 : (k:ℝ)*R < R*R := mul_lt_mul_of_pos_right hklt hR
    nlinarith [h3, h6]
  have hprod : (R^2 - (k:ℝ)*(l+η))*(R^2 + (k:ℝ)*(l-η)) ≤ R^4 := by
    have hm : 0 < (k:ℝ)*η := mul_pos hk1 hη
    have h7 : (k:ℝ)*η < R^2 := by
      have h8 : (k:ℝ)*η < R*η := mul_lt_mul_of_pos_right hklt hη
      have h9 : R*η < R*R := mul_lt_mul_of_pos_left hηR hR
      linarith
    have hm4 : ((k:ℝ)*η)^2 ≤ 2*(k:ℝ)*η*R^2 := by
      have h10 : ((k:ℝ)*η) ≤ 2*R^2 := by linarith [h7]
      calc ((k:ℝ)*η)^2 = ((k:ℝ)*η)*((k:ℝ)*η) := by ring
        _ ≤ ((k:ℝ)*η)*(2*R^2) := mul_le_mul_of_nonneg_left h10 (le_of_lt hm)
        _ = 2*(k:ℝ)*η*R^2 := by ring
    have h11 : 0 ≤ 2*(k:ℝ)*η*R^2 + ((k:ℝ)*l)^2 - ((k:ℝ)*η)^2 := by
      nlinarith [hm4, sq_nonneg ((k:ℝ)*l)]
    have h12 : R^4 - (R^2 - (k:ℝ)*(l+η))*(R^2 + (k:ℝ)*(l-η))
        = 2*(k:ℝ)*η*R^2 + ((k:ℝ)*l)^2 - ((k:ℝ)*η)^2 := by ring
    linarith [h11, h12]
  rw [norm_mul, bfac_norm_ofReal R hR k (l+η), bfac_norm_ofReal R hR (-k) (l-η), Int.cast_neg]
  rw [show (l-η) - -(k:ℝ) = (l-η) + (k:ℝ) by ring,
      show R^2 - -(k:ℝ)*(l-η) = R^2 + (k:ℝ)*(l-η) by ring]
  rw [abs_of_pos hA, abs_of_pos hB]
  rw [div_mul_div_comm]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < R^2) (mul_pos hA hB)]
  have ha : (0:ℝ) ≤ |(l + η) - (k:ℝ)| * |(l - η) + (k:ℝ)| := by positivity
  have hstep : (|(l + η) - (k:ℝ)| * |(l - η) + (k:ℝ)|) * ((R^2 - (k:ℝ)*(l+η))*(R^2 + (k:ℝ)*(l-η)))
      ≤ (|(l + η) - (k:ℝ)| * |(l - η) + (k:ℝ)|) * R^4 := mul_le_mul_of_nonneg_left hprod ha
  nlinarith [hstep]

/-- Case `k ≤ l`: both factors are bounded at `l − η`. -/
lemma pair_caseA_bound (R η l : ℝ) (k : ℤ) (hR : 0 < R) (hη' : η < 1/2)
    (hkl : (k:ℝ) ≤ l) (hk1 : 1 ≤ (k:ℝ)) (hxm : |l - η| ≤ R) (hkR : |(k:ℝ)| < R) :
    |(|l - (k:ℝ)|) - η| * (l + (k:ℝ) - η) / R^2
      ≤ ‖bfac R k ((l-η:ℝ):ℂ) * bfac R (-k) ((l-η:ℝ):ℂ)‖ := by
  have hpair := bfac_pair_real_ge R hR k (l-η) hxm hkR
  have hLM : |(|l - (k:ℝ)|) - η| * (l + (k:ℝ) - η) / R^2
      = |(l-η) - (k:ℝ)| * |(l-η) + (k:ℝ)| / R^2 := by
    have h1 : |l - (k:ℝ)| = l - (k:ℝ) := abs_of_nonneg (by linarith)
    have h3 : 0 ≤ (l-η) + (k:ℝ) := by linarith
    rw [h1, abs_of_nonneg h3]
    rw [show l - (k:ℝ) - η = l - η - (k:ℝ) by ring]
    ring
  rw [hLM]; exact hpair

/-- Case `k > l`: `β(·;k)` is bounded at `l + η` and `β(·;−k)` at `l − η`. -/
lemma pair_caseB_bound (R η l : ℝ) (k : ℤ) (hR : 0 < R) (hη : 0 < η) (hη' : η < 1/2)
    (hlk : l < (k:ℝ)) (hk1 : 1 ≤ (k:ℝ)) (hl0 : 0 ≤ l) (hηR : η < R) (hkR : |(k:ℝ)| < R)
    (hxp : |l + η| ≤ R) (hxm : |l - η| ≤ R) :
    |(|l - (k:ℝ)|) - η| * (l + (k:ℝ) - η) / R^2
      ≤ ‖bfac R k ((l+η:ℝ):ℂ) * bfac R (-k) ((l-η:ℝ):ℂ)‖ := by
  have hpair := bfac_pair_split_ge R η l k hR hη hl0 (by linarith) hkR hηR hxp hxm
  have hLM : |(|l - (k:ℝ)|) - η| * (l + (k:ℝ) - η) / R^2
      = |(l+η) - (k:ℝ)| * |(l-η) + (k:ℝ)| / R^2 := by
    have e1 : |l - (k:ℝ)| = (k:ℝ) - l := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) - l)]
    have h3 : 0 ≤ (l-η) + (k:ℝ) := by linarith
    rw [e1, abs_of_nonneg h3]
    rw [show (k:ℝ) - l - η = -(l + η - (k:ℝ)) by ring, abs_neg]
    ring
  rw [hLM]; exact hpair

/-- BW p. 51, per-pair lower bound, for `l ≥ 0`; the general case follows by `z ↦ −z`,
`l ↦ −l`. -/
theorem bprod_pair_lower_nonneg (R η : ℝ) (hη : 0 < η) (hη' : η < 1 / 2) (X : ℕ)
    (hXR : (X : ℝ) + η ≤ R) (l : ℤ) (hl0 : 0 ≤ l) (hlX : l ≤ (X : ℤ))
    (z : ℂ) (hz : ‖z - (l : ℂ)‖ = η) (k : ℤ) (hk1 : 1 ≤ k) (hkX : k ≤ (X : ℤ)) :
    |(|(l : ℝ) - (k : ℝ)|) - η| * ((l : ℝ) + (k : ℝ) - η) / R ^ 2 ≤
      ‖bfac R k z * bfac R (-k) z‖ := by
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hkXR : (k:ℝ) ≤ (X:ℝ) := by exact_mod_cast hkX
  have hl0R : (0:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl0
  have hlXR : (l:ℝ) ≤ (X:ℝ) := by exact_mod_cast hlX
  have hX0R : (0:ℝ) ≤ (X:ℝ) := le_trans (by linarith : (0:ℝ) ≤ (k:ℝ)) hkXR
  have hk0R : (0:ℝ) ≤ (k:ℝ) := by linarith
  have hR : 0 < R := by linarith
  have hXltR : (X:ℝ) < R := by linarith
  have hkltR : (k:ℝ) < R := by linarith
  have hηR : η < R := by linarith
  have hkap : |(k:ℝ)| < R := by rw [abs_of_pos (by linarith)]; linarith
  have hkam : |((((-k:ℤ))):ℝ)| < R := by
    rw [Int.cast_neg, abs_neg, abs_of_pos (by linarith)]; linarith
  have hzR : ‖z‖ ≤ R := by
    calc ‖z‖ = ‖(l:ℂ) + (z - (l:ℂ))‖ := by congr 1; ring
      _ ≤ ‖(l:ℂ)‖ + ‖z - (l:ℂ)‖ := norm_add_le _ _
      _ = (l:ℝ) + η := by
          rw [hz]
          rw [show ‖(l:ℂ)‖ = |(l:ℝ)| from RCLike.norm_ofReal _, abs_of_nonneg hl0R]
      _ ≤ R := by linarith
  have hk2R : (k:ℝ)^2 < R^2 := (sq_lt_sq₀ hk0R (le_of_lt hR)).mpr hkltR
  have hX2R : (X:ℝ)^2 < R^2 := (sq_lt_sq₀ hX0R (le_of_lt hR)).mpr hXltR
  have hη2R : η^2 < R^2 := (sq_lt_sq₀ (le_of_lt hη) (le_of_lt hR)).mpr hηR
  have hklsq : (k:ℝ)*(l:ℝ) ≤ (X:ℝ)^2 := by
    have h := mul_le_mul hkXR hlXR hl0R hX0R
    simpa [pow_two] using h
  rcases le_or_gt (k:ℝ) (l:ℝ) with hkl | hkl
  · have hxm : |(l:ℝ) - η| ≤ R := by rw [abs_le]; constructor <;> linarith
    have hsgn_k : 0 ≤ (R^2 - (k:ℝ)^2) * ((l - (k:ℝ))*(R^2 - (k:ℝ)*l) + (k:ℝ)*η^2) := by
      have h1 : 0 ≤ R^2 - (k:ℝ)^2 := by linarith
      have ha : 0 ≤ (l:ℝ) - (k:ℝ) := by linarith
      have hb : 0 ≤ R^2 - (k:ℝ)*l := by linarith
      have hc : 0 ≤ (k:ℝ)*η^2 := mul_nonneg (by linarith) (sq_nonneg η)
      have h2 : 0 ≤ (l - (k:ℝ))*(R^2 - (k:ℝ)*l) + (k:ℝ)*η^2 := by
        nlinarith [mul_nonneg ha hb, hc]
      exact mul_nonneg h1 h2
    have hsgn_mk : 0 ≤ (R^2 - (((-k:ℤ)):ℝ)^2) *
        ((l - (((-k:ℤ)):ℝ))*(R^2 - (((-k:ℤ)):ℝ)*l) + (((-k:ℤ)):ℝ)*η^2) := by
      rw [Int.cast_neg]
      have h1 : 0 ≤ R^2 - (-(k:ℝ))^2 := by rw [neg_sq]; linarith
      have h2 : 0 ≤ (l - -(k:ℝ))*(R^2 - -(k:ℝ)*l) + (-(k:ℝ))*η^2 := by
        have e : (l - -(k:ℝ))*(R^2 - -(k:ℝ)*l) + (-(k:ℝ))*η^2
            = (l + (k:ℝ))*(R^2 + (k:ℝ)*l) - (k:ℝ)*η^2 := by ring
        rw [e]
        have hkl0 : 0 ≤ (k:ℝ)*l := mul_nonneg hk0R hl0R
        have hkR2 : (k:ℝ)*R^2 ≤ (l + (k:ℝ))*(R^2 + (k:ℝ)*l) := by
          have h2' : R^2 ≤ R^2 + (k:ℝ)*l := by linarith
          have h1' : (k:ℝ) ≤ l + (k:ℝ) := by linarith [hl0R]
          exact mul_le_mul h1' h2' (sq_nonneg R) (by linarith : (0:ℝ) ≤ l + (k:ℝ))
        have h3 : (k:ℝ)*η^2 ≤ (k:ℝ)*R^2 := mul_le_mul_of_nonneg_left (le_of_lt hη2R) hk0R
        linarith
      exact mul_nonneg h1 h2
    have h1 := bfac_le_left_endpoint R η (l:ℝ) k z hR hz hzR hxm hkap hsgn_k
    have h2 := bfac_le_left_endpoint R η (l:ℝ) (-k) z hR hz hzR hxm hkam hsgn_mk
    have h3 := pair_caseA_bound R η (l:ℝ) k hR hη' hkl hk1R hxm hkap
    calc |(|(l:ℝ) - (k:ℝ)|) - η| * ((l:ℝ) + (k:ℝ) - η) / R^2
        ≤ ‖bfac R k ((l-η:ℝ):ℂ) * bfac R (-k) ((l-η:ℝ):ℂ)‖ := h3
      _ ≤ ‖bfac R k z * bfac R (-k) z‖ := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  · have hxp : |(l:ℝ) + η| ≤ R := by rw [abs_le]; constructor <;> linarith
    have hxm : |(l:ℝ) - η| ≤ R := by rw [abs_le]; constructor <;> linarith
    have hsgn_k : (R^2 - (k:ℝ)^2) * ((l - (k:ℝ))*(R^2 - (k:ℝ)*l) + (k:ℝ)*η^2) ≤ 0 := by
      have h1 : 0 ≤ R^2 - (k:ℝ)^2 := by linarith
      have hkl1 : (1:ℝ) ≤ (k:ℝ) - l := by
        have hhZ : l < k := by exact_mod_cast hkl
        have hh : (1:ℤ) ≤ k - l := by omega
        exact_mod_cast hh
      have h3 : 0 ≤ R^2 - (X:ℝ)^2 := by linarith
      have h4 : R^2 - (X:ℝ)^2 ≤ R^2 - (k:ℝ)*l := by linarith
      have h5 : (R^2 - (X:ℝ)^2) ≤ ((k:ℝ)-l)*(R^2-(k:ℝ)*l) := by
        calc (R^2-(X:ℝ)^2) = 1*(R^2-(X:ℝ)^2) := by ring
          _ ≤ ((k:ℝ)-l)*(R^2-(k:ℝ)*l) := mul_le_mul hkl1 h4 h3 (by linarith)
      have h6 : 2*(X:ℝ)*η + η^2 ≤ R^2 - (X:ℝ)^2 := by
        have hh : 0 ≤ (R - ((X:ℝ)+η)) * (R + ((X:ℝ)+η)) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hh]
      have h7 : (k:ℝ)*η^2 ≤ 2*(X:ℝ)*η + η^2 := by
        have hXk : 0 ≤ (X:ℝ) - (k:ℝ) := by linarith
        have hh1 : 0 ≤ 2*η*((X:ℝ) - (k:ℝ)) :=
          mul_nonneg (by linarith : (0:ℝ) ≤ 2*η) hXk
        have hh2 : 0 ≤ (k:ℝ)*(2-η) := mul_nonneg hk0R (by linarith : (0:ℝ) ≤ 2-η)
        have hh3 : 0 ≤ η*((k:ℝ)*(2-η) + η) := mul_nonneg (le_of_lt hη) (by linarith)
        nlinarith [hh1, hh3]
      have hkeyB : (k:ℝ)*η^2 ≤ ((k:ℝ)-l)*(R^2-(k:ℝ)*l) := by linarith
      have h2 : (l - (k:ℝ))*(R^2 - (k:ℝ)*l) + (k:ℝ)*η^2 ≤ 0 := by nlinarith [hkeyB]
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    have hsgn_mk : 0 ≤ (R^2 - (((-k:ℤ)):ℝ)^2) *
        ((l - (((-k:ℤ)):ℝ))*(R^2 - (((-k:ℤ)):ℝ)*l) + (((-k:ℤ)):ℝ)*η^2) := by
      rw [Int.cast_neg]
      have h1 : 0 ≤ R^2 - (-(k:ℝ))^2 := by rw [neg_sq]; linarith
      have h2 : 0 ≤ (l - -(k:ℝ))*(R^2 - -(k:ℝ)*l) + (-(k:ℝ))*η^2 := by
        have e : (l - -(k:ℝ))*(R^2 - -(k:ℝ)*l) + (-(k:ℝ))*η^2
            = (l + (k:ℝ))*(R^2 + (k:ℝ)*l) - (k:ℝ)*η^2 := by ring
        rw [e]
        have hkl0 : 0 ≤ (k:ℝ)*l := mul_nonneg hk0R hl0R
        have hkR2 : (k:ℝ)*R^2 ≤ (l + (k:ℝ))*(R^2 + (k:ℝ)*l) := by
          have h2' : R^2 ≤ R^2 + (k:ℝ)*l := by linarith
          have h1' : (k:ℝ) ≤ l + (k:ℝ) := by linarith [hl0R]
          exact mul_le_mul h1' h2' (sq_nonneg R) (by linarith : (0:ℝ) ≤ l + (k:ℝ))
        have h3 : (k:ℝ)*η^2 ≤ (k:ℝ)*R^2 := mul_le_mul_of_nonneg_left (le_of_lt hη2R) hk0R
        linarith
      exact mul_nonneg h1 h2
    have h1 := bfac_le_right_endpoint R η (l:ℝ) k z hR hz hzR hxp hkap hsgn_k
    have h2 := bfac_le_left_endpoint R η (l:ℝ) (-k) z hR hz hzR hxm hkam hsgn_mk
    have h3 := pair_caseB_bound R η (l:ℝ) k hR hη hη' hkl hk1R hl0R hηR hkap hxp hxm
    calc |(|(l:ℝ) - (k:ℝ)|) - η| * ((l:ℝ) + (k:ℝ) - η) / R^2
        ≤ ‖bfac R k ((l+η:ℝ):ℂ) * bfac R (-k) ((l-η:ℝ):ℂ)‖ := h3
      _ ≤ ‖bfac R k z * bfac R (-k) z‖ := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

/-- **BW p. 51, per-pair lower bound.** For `0 < η < 1/2`, `1 ≤ X`, `X + η ≤ R`, integer `l` with `|l| ≤ X`, `z` on the circle `C_l : ‖z − l‖ = η`, and `1 ≤ k ≤ X`:
`‖β(z;k)·β(z;−k)‖ ≥ |‖l| − k| − η|·(|l| + k − η)/R²`, where `β(z;k) = R(z−k)/(R²−kz)`.
Proved by: writing `z = l + w`, `‖w‖ = η`, `c = Re w ∈ [−η,η]`, so that
`‖β(z;k)‖² = R²(A+Bc)/(P+Qc)` with `A = (l−k)²+η²`, `B = 2(l−k)`, `P = (R²−kl)²+k²η²`, `Q = −2k(R²−kl)`;
a ratio of linear functions has derivative of constant sign, so the minimum over the circle is attained at `c = ±η`, i.e. at `z = l±η`; evaluating and pairing the two rational factors gives the bound. Equivalent to BW's `∏(k+l′−η)(|k−l′|−η)/R²`. -/
theorem bprod_pair_lower (R η : ℝ) (hη : 0 < η) (hη' : η < 1 / 2) (X : ℕ) (hXR : (X : ℝ) + η ≤ R)
    (l : ℤ) (hl : |l| ≤ (X : ℤ)) (z : ℂ) (hz : ‖z - (l : ℂ)‖ = η) (k : ℤ) (hk1 : 1 ≤ k)
    (hkX : k ≤ (X : ℤ)) :
    |(|(|l| : ℝ) - (k : ℝ)|) - η| * ((|l| : ℝ) + (k : ℝ) - η) / R ^ 2 ≤
      ‖bfac R k z * bfac R (-k) z‖ := by
  rcases le_or_gt 0 l with hl0 | hl0
  · have hlX : l ≤ (X:ℤ) := (abs_le.mp hl).2
    have h1 : (|l| : ℝ) = (l:ℝ) := abs_of_nonneg (by exact_mod_cast hl0)
    rw [h1]
    exact bprod_pair_lower_nonneg R η hη hη' X hXR l hl0 hlX z hz k hk1 hkX
  · have hlX : -l ≤ (X:ℤ) := by
      have h2 : |l| = -l := abs_of_neg hl0
      rw [h2] at hl
      exact hl
    have hzn : ‖(-z) - (((-l:ℤ)):ℂ)‖ = η := by
      rw [show (((-l:ℤ)):ℂ) = -(l:ℂ) by push_cast; ring]
      rw [show -z - -(l:ℂ) = -(z - (l:ℂ)) by ring, norm_neg, hz]
    have hkey := bprod_pair_lower_nonneg R η hη hη' X hXR (-l) (by omega) hlX (-z) hzn k hk1 hkX
    have hbfac : ∀ κ : ℤ, bfac R κ (-z) = - bfac R (-κ) z := by
      intro κ
      rw [bfac, bfac]; push_cast; ring
    have hprod : ‖bfac R k (-z) * bfac R (-k) (-z)‖ = ‖bfac R k z * bfac R (-k) z‖ := by
      rw [hbfac k, hbfac (-k), show (-(-k) : ℤ) = k by ring, neg_mul_neg, mul_comm]
    have hlabs : (|l| : ℝ) = (((-l:ℤ)):ℝ) := by
      rw [abs_of_neg (by exact_mod_cast hl0 : (l:ℝ) < 0), Int.cast_neg]
    rw [hlabs, ← hprod]
    exact hkey

end Work.BW
