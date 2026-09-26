import Mathlib
import Submission.Work.CKFinal.U0Defs

namespace Work.CKFinal.Socket

/-- Squared distance in `ℍ` from `τ` to a point `c : ℂ`, in terms of the coordinates of `τ`. -/
lemma sq_norm_sub (τ : UpperHalfPlane) (c : ℂ) :
    ‖(τ : ℂ) - c‖ ^ 2 = (τ.re - c.re) ^ 2 + (τ.im - c.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- **The left half of the strip.**  If `τ` has `-1 < Re τ < 1`, `Re τ ≤ 0` and `τ` lies on or
outside the closed Farey disc `|τ + 1/2| ≤ 1/2` (i.e. `-Re τ ≤ Re τ ^ 2 + Im τ ^ 2`), then `τ`
avoids all four closed Farey discs of radius `1/4` about `±1/4`, `±3/4`, hence lies in `U₀`. -/
lemma mem_U0_of_re_nonpos {τ : UpperHalfPlane} (hlo : -1 < τ.re) (hhi : τ.re < 1)
    (hneg : τ.re ≤ 0) (hP : -τ.re ≤ τ.re ^ 2 + τ.im ^ 2) : τ ∈ Work.CKFinal.U0 := by
  rw [Work.CKFinal.mem_U0_iff]
  have hy : 0 < τ.im := τ.im_pos
  refine ⟨hlo, hhi, ?_, ?_, ?_, ?_⟩
  -- Disc about `1/4`.
  · have hs : ‖(τ : ℂ) - (1/4 : ℂ)‖ ^ 2 = (τ.re - 1/4) ^ 2 + τ.im ^ 2 := by
      rw [sq_norm_sub]; norm_num
    have hlt : ((1 : ℝ) / 4) ^ 2 < ‖(τ : ℂ) - (1/4 : ℂ)‖ ^ 2 := by
      rw [hs]
      nlinarith [sq_nonneg τ.re, sq_pos_of_pos hy, hneg]
    nlinarith [hlt, norm_nonneg ((τ : ℂ) - (1/4 : ℂ))]
  -- Disc about `-1/4`; here `hP` is used.
  · have hs : ‖(τ : ℂ) - (-(1/4) : ℂ)‖ ^ 2 = (τ.re + 1/4) ^ 2 + τ.im ^ 2 := by
      rw [sq_norm_sub]; norm_num
    have hlt : ((1 : ℝ) / 4) ^ 2 < ‖(τ : ℂ) - (-(1/4) : ℂ)‖ ^ 2 := by
      rw [hs, show (τ.re + 1/4 : ℝ) = (τ.re - (-(1/4) : ℝ)) by ring]
      nlinarith [hP, hneg]
    have he : ‖(τ : ℂ) - (-(1/4) : ℂ)‖ = ‖(τ : ℂ) + (1/4 : ℂ)‖ := by
      congr 1; ring
    rw [← he]
    nlinarith [hlt, norm_nonneg ((τ : ℂ) - (-(1/4) : ℂ))]
  -- Disc about `3/4`.
  · have hs : ‖(τ : ℂ) - (3/4 : ℂ)‖ ^ 2 = (τ.re - 3/4) ^ 2 + τ.im ^ 2 := by
      rw [sq_norm_sub]; norm_num
    have hlt : ((1 : ℝ) / 4) ^ 2 < ‖(τ : ℂ) - (3/4 : ℂ)‖ ^ 2 := by
      rw [hs]
      have h3 : (3/4 : ℝ) ^ 2 ≤ (τ.re - 3/4) ^ 2 := by
        nlinarith [sq_nonneg (3/4 - τ.re)]
      nlinarith [h3, hy, sq_nonneg τ.im]
    nlinarith [hlt, norm_nonneg ((τ : ℂ) - (3/4 : ℂ))]
  -- Disc about `-3/4`; here `hlo` is used.
  · have hs : ‖(τ : ℂ) - (-(3/4) : ℂ)‖ ^ 2 = (τ.re + 3/4) ^ 2 + τ.im ^ 2 := by
      rw [sq_norm_sub]; norm_num
    have hlt : ((1 : ℝ) / 4) ^ 2 < ‖(τ : ℂ) - (-(3/4) : ℂ)‖ ^ 2 := by
      rw [hs, show (τ.re + 3/4 : ℝ) = (τ.re - (-(3/4) : ℝ)) by ring]
      nlinarith [hP, hlo]
    have he : ‖(τ : ℂ) - (-(3/4) : ℂ)‖ = ‖(τ : ℂ) + (3/4 : ℂ)‖ := by
      congr 1; ring
    rw [← he]
    nlinarith [hlt, norm_nonneg ((τ : ℂ) - (-(3/4) : ℂ))]

end Work.CKFinal.Socket
