import Mathlib
import Submission.Work.EQ.LocModelDefs
import Submission.Work.EQ.lmSqrtLipschitz
import Submission.Work.EQ.lmInvLipschitz
import Submission.Work.EQ.lmAxisFixed
import Submission.Work.EQ.lmSigBounds
import Submission.Work.EQ.lmVBounds
import Submission.Work.EQ.lmLamBounds

set_option maxHeartbeats 4000000

namespace Work.EQ

open Complex

noncomputable section

/-- The standing hypotheses on the parameters `a, a₀`. -/
structure lmData (a a₀ : ℝ) : Prop where
  ha : 0 < a
  ha1 : a < 1
  h1 : a/2 - 1 < a₀
  h2 : a₀ < -(a/2)

section Constants

def kX1 (a a₀ : ℝ) : ℝ := 1 + 10/lmS a a₀
def kY1 (a a₀ : ℝ) : ℝ := 1 + 3/lmS a a₀
def kTau (a a₀ : ℝ) : ℝ := 2 + 13/lmS a a₀
def kG1 (a a₀ : ℝ) : ℝ := 4/(lmS a a₀)^2
def kG2 (a a₀ : ℝ) : ℝ := 4/(lmT a a₀)^2 * (2 + 13/lmS a a₀)
def kA1 (a a₀ : ℝ) : ℝ := 8 * lmS a a₀
def kA2 (a a₀ : ℝ) : ℝ := 6 * kTau a a₀ + (3 * kX1 a a₀ + 2 * lmT a a₀ * kTau a a₀)

/-- Pointwise bound constant for `Φ = F/η²`. -/
def lmMPhi (a a₀ : ℝ) : ℝ := 4/(lmS a a₀)^2 + 4*(1 + 2/lmS a a₀)^2/(lmT a a₀)^2

/-- Lipschitz constant for `Φ = F/η²`. -/
def lmKPhi (a a₀ : ℝ) : ℝ :=
  16 * kA1 a a₀ / (lmS a a₀)^4
    + (1 + 2/lmS a a₀)^2 * kA2 a a₀ * (16/(lmT a a₀)^4)
    + 2 * (1 + 2/lmS a a₀) * kG1 a a₀ * (4/(lmT a a₀)^2)

def lmKF (a a₀ : ℝ) : ℝ := lmKPhi a a₀ + lmMPhi a a₀
def lmKG (a a₀ : ℝ) : ℝ := (1 + 2/lmS a a₀) * kG2 a a₀ + (1 + 2/lmT a a₀) * kG1 a a₀

/-- The model constant. -/
def lmC (a a₀ : ℝ) : ℝ := 1 + max (max (lmMPhi a a₀) (lmKF a a₀)) (lmKG a a₀)

/-- The model radius. -/
def lmEps (a a₀ : ℝ) : ℝ := min (lmH a a₀/8) ((1 - lmLam a a₀)/(8*lmC a a₀))

variable {a a₀ : ℝ}

/-- The reduced horizontal deviation: `F = η² Φ` on the box. -/
def lmPhi (a a₀ ξ η : ℝ) : ℝ :=
  (lmG1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η))
    - 1/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ))

lemma lmMPhi_le_lmC (a a₀ : ℝ) : lmMPhi a a₀ ≤ lmC a a₀ := by
  have h : lmMPhi a a₀ ≤ max (max (lmMPhi a a₀) (lmKF a a₀)) (lmKG a a₀) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  simp only [lmC]; linarith

lemma lmKF_le_lmC (a a₀ : ℝ) : lmKF a a₀ ≤ lmC a a₀ := by
  have h : lmKF a a₀ ≤ max (max (lmMPhi a a₀) (lmKF a a₀)) (lmKG a a₀) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  simp only [lmC]; linarith

lemma lmKG_le_lmC (a a₀ : ℝ) : lmKG a a₀ ≤ lmC a a₀ := by
  have h : lmKG a a₀ ≤ max (max (lmMPhi a a₀) (lmKF a a₀)) (lmKG a a₀) := le_max_right _ _
  simp only [lmC]; linarith

lemma lmMPhi_nonneg (a a₀ : ℝ) : 0 ≤ lmMPhi a a₀ := by
  have h1 : 0 ≤ 4/(lmS a a₀)^2 := div_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ 4*(1 + 2/lmS a a₀)^2/(lmT a a₀)^2 :=
    div_nonneg (by nlinarith [sq_nonneg (1 + 2/lmS a a₀)]) (sq_nonneg _)
  simp only [lmMPhi]; linarith

lemma lmKPhi_nonneg (h : lmData a a₀) : 0 ≤ lmKPhi a a₀ := by
  have hs : 0 < lmS a a₀ := by
    obtain ⟨ha0, ha1, h1, h2⟩ := h; simp only [lmS]; linarith
  have ht : 0 < lmT a a₀ := by
    obtain ⟨ha0, ha1, h1, h2⟩ := h; simp only [lmT]; linarith
  have h1 : 0 < kA1 a a₀ := by simp only [kA1]; linarith
  have h2 : 0 < kTau a a₀ := by simp only [kTau]; positivity
  have h3 : 0 < kX1 a a₀ := by simp only [kX1]; positivity
  have h4 : 0 < kA2 a a₀ := by simp only [kA2]; nlinarith [h2, h3, ht]
  have h5 : 0 < kG1 a a₀ := by simp only [kG1]; positivity
  have h6 : 0 < 1 + 2/lmS a a₀ := by positivity
  have h7 : 0 < 16/(lmT a a₀)^4 := by positivity
  have h8 : 0 < (lmT a a₀)^4 := by positivity
  have h9 : 0 < (lmS a a₀)^4 := by positivity
  have h10 : 0 ≤ 16 * kA1 a a₀ / (lmS a a₀)^4 := div_nonneg (by linarith) (le_of_lt h9)
  have h11 : 0 ≤ (1 + 2/lmS a a₀)^2 * kA2 a a₀ * (16/(lmT a a₀)^4) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt h4)) (le_of_lt h7)
  have h12 : 0 ≤ 2 * (1 + 2/lmS a a₀) * kG1 a a₀ * (4/(lmT a a₀)^2) :=
    mul_nonneg (mul_nonneg (by linarith) (le_of_lt h5)) (by positivity)
  simp only [lmKPhi]; linarith

lemma lmC_pos (a a₀ : ℝ) : 0 < lmC a a₀ := by
  have h := lmMPhi_nonneg a a₀
  have h2 : lmMPhi a a₀ ≤ max (max (lmMPhi a a₀) (lmKF a a₀)) (lmKG a a₀) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  simp only [lmC]; linarith

end Constants

section Basic

variable {a a₀ : ℝ}

lemma lmS_pos (h : lmData a a₀) : 0 < lmS a a₀ := by
  have h1 := h.ha; have h2 := h.h2; simp only [lmS]; linarith

lemma lmT_pos (h : lmData a a₀) : 0 < lmT a a₀ := by
  have h1 := h.ha; have h2 := h.h1; simp only [lmT]; linarith

lemma lmS_lt_one (h : lmData a a₀) : lmS a a₀ < 1 := by
  have h2 := h.h1; simp only [lmS]; linarith

lemma lmT_lt_one (h : lmData a a₀) : lmT a a₀ < 1 := by
  have h2 := h.h2; simp only [lmT]; linarith

lemma lmS_add_lmT (a a₀ : ℝ) : lmS a a₀ + lmT a a₀ = 1 + a := by
  simp only [lmS, lmT]; ring

lemma lmH_pos (h : lmData a a₀) : 0 < lmH a a₀ := by
  have hs := lmS_pos h; have ht := lmT_pos h
  simp only [lmH]
  exact div_pos (lt_min hs ht) (by norm_num)

lemma lmH_le_lmS (a a₀ : ℝ) : lmH a a₀ ≤ lmS a a₀ / 16 := by
  simp only [lmH]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

lemma lmH_le_lmT (a a₀ : ℝ) : lmH a a₀ ≤ lmT a a₀ / 16 := by
  simp only [lmH]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

lemma lmH_lt_one (h : lmData a a₀) : lmH a a₀ < 1 := by
  have hs := lmS_pos h
  have h1 : lmH a a₀ ≤ lmS a a₀ / 16 := lmH_le_lmS a a₀
  have h3 : lmS a a₀ < 1 := lmS_lt_one h
  linarith

lemma abs_le_lmS (a a₀ ξ η : ℝ) (h : lmBox a a₀ ξ η) : |ξ| ≤ lmS a a₀ / 16 :=
  le_trans h.1 (lmH_le_lmS a a₀)

lemma abs_eta_le_lmS (a a₀ ξ η : ℝ) (h : lmBox a a₀ ξ η) : |η| ≤ lmS a a₀ / 16 :=
  le_trans h.2 (lmH_le_lmS a a₀)

lemma abs_le_lmT (a a₀ ξ η : ℝ) (h : lmBox a a₀ ξ η) : |ξ| ≤ lmT a a₀ / 16 :=
  le_trans h.1 (lmH_le_lmT a a₀)

lemma abs_eta_le_lmT (a a₀ ξ η : ℝ) (h : lmBox a a₀ ξ η) : |η| ≤ lmT a a₀ / 16 :=
  le_trans h.2 (lmH_le_lmT a a₀)

lemma lmU_abs_le (h : lmData a a₀) {ξ η : ℝ} (hbox : lmBox a a₀ ξ η) :
    |lmU a a₀ ξ| ≤ 2 * lmS a a₀ := by
  have hs := lmS_pos h
  have h1 := abs_le_lmS a a₀ ξ η hbox
  rw [lmU_eq]
  calc |ξ - lmS a a₀| ≤ |ξ| + |lmS a a₀| := abs_sub _ _
    _ = |ξ| + lmS a a₀ := by rw [abs_of_pos hs]
    _ ≤ lmS a a₀ / 16 + lmS a a₀ := by linarith
    _ ≤ 2 * lmS a a₀ := by linarith

lemma lmS_sub_xi_pos (h : lmData a a₀) {ξ η : ℝ} (hbox : lmBox a a₀ ξ η) :
    0 < lmS a a₀ - ξ := by
  have hs := lmS_pos h
  have h1 := abs_le_lmS a a₀ ξ η hbox
  have h2 : ξ ≤ lmS a a₀ / 16 := le_trans (le_abs_self ξ) h1
  linarith

lemma lmU_neg (h : lmData a a₀) {ξ η : ℝ} (hbox : lmBox a a₀ ξ η) :
    lmU a a₀ ξ < 0 := by
  rw [lmU_eq]; linarith [lmS_sub_xi_pos h hbox]

lemma lm_mul_sub_mul (x y x' y' : ℝ) : |x*y - x'*y'| ≤ |x| * |y-y'| + |y'| * |x-x'| := by
  have h : x*y - x'*y' = x*(y-y') + y'*(x-x') := by ring
  rw [h]
  calc |x*(y-y') + y'*(x-x')| ≤ |x*(y-y')| + |y'*(x-x')| := abs_add_le _ _
    _ = |x| * |y-y'| + |y'| * |x-x'| := by rw [abs_mul, abs_mul]

lemma lmBox_zero (h : lmData a a₀) : lmBox a a₀ 0 0 := by
  refine ⟨?_, ?_⟩ <;> rw [abs_zero] <;> exact le_of_lt (lmH_pos h)

end Basic

section Accessors

variable {a a₀ ξ η : ℝ}

lemma lmSig_ge (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmS a a₀ / 2 ≤ lmSig a a₀ ξ η := (lmSigBounds ha0 ha1 h1 h2 hξ hη).1

lemma lmSig_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmSig a a₀ ξ η ≤ 2 * lmS a a₀ := (lmSigBounds ha0 ha1 h1 h2 hξ hη).2.1

lemma lmG1_abs_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    |lmG1 a a₀ ξ η| ≤ 1 + 2/lmS a a₀ := (lmSigBounds ha0 ha1 h1 h2 hξ hη).2.2.1

lemma lmY1_abs_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    |lmY1 a a₀ ξ η| ≤ 3/16 := (lmSigBounds ha0 ha1 h1 h2 hξ hη).2.2.2

lemma lmV_ge (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmT a a₀ / 2 ≤ lmV a a₀ ξ η := (lmVBounds ha0 ha1 h1 h2 hξ hη).1

lemma lmV_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmV a a₀ ξ η ≤ 2 * lmT a a₀ := (lmVBounds ha0 ha1 h1 h2 hξ hη).2.1

lemma lmTau_ge (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmT a a₀ / 2 ≤ lmTau a a₀ ξ η := (lmVBounds ha0 ha1 h1 h2 hξ hη).2.2.1

lemma lmTau_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    lmTau a a₀ ξ η ≤ 3 := (lmVBounds ha0 ha1 h1 h2 hξ hη).2.2.2.1

lemma lmG2_abs_le (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ lmH a a₀) (hη : |η| ≤ lmH a a₀) :
    |lmG2 a a₀ ξ η| ≤ 1 + 2/lmT a a₀ := (lmVBounds ha0 ha1 h1 h2 hξ hη).2.2.2.2

lemma lmLam_eq_G00 (ha0 : 0 < a) (ha1 : a < 1) (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2)) :
    lmLam a a₀ = lmG a a₀ 0 0 := (lmLamBounds ha0 ha1 h1 h2).2.2

end Accessors

section Decomp

variable {a a₀ ξ η : ℝ}

lemma lmF_decomp (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    lmF a a₀ ξ η =
      -η^2/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ))
        + (lmY1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have ht := lmT_pos hdata
  have hσ2 : lmS a a₀ / 2 ≤ lmSig a a₀ ξ η := lmSig_ge ha0 ha1 h1 h2 hbox.1 hbox.2
  have hσpos : 0 < lmSig a a₀ ξ η := by linarith
  have hA : 0 < lmS a a₀ - ξ := lmS_sub_xi_pos hdata hbox
  have hv : lmT a a₀ / 2 ≤ lmV a a₀ ξ η := lmV_ge ha0 ha1 h1 h2 hbox.1 hbox.2
  have hvpos : 0 < lmV a a₀ ξ η := by linarith
  have hτ : lmT a a₀ / 2 ≤ lmTau a a₀ ξ η := lmTau_ge ha0 ha1 h1 h2 hbox.1 hbox.2
  have hτpos : 0 < lmTau a a₀ ξ η := by linarith
  have hS : (lmSig a a₀ ξ η)^2 = (lmS a a₀ - ξ)^2 + η^2 := by
    rw [lmSig_sq, lmU_eq]; ring
  have hT : (lmTau a a₀ ξ η)^2 = (lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2 := lmTau_sq a a₀ ξ η
  have hc1 : lmSig a a₀ ξ η ≠ 0 := ne_of_gt hσpos
  have hc2 : lmSig a a₀ ξ η + lmS a a₀ - ξ ≠ 0 :=
    ne_of_gt (by linarith : 0 < lmSig a a₀ ξ η + lmS a a₀ - ξ)
  have hd1 : lmTau a a₀ ξ η ≠ 0 := ne_of_gt hτpos
  have hd2 : lmTau a a₀ ξ η + lmV a a₀ ξ η ≠ 0 :=
    ne_of_gt (by linarith : 0 < lmTau a a₀ ξ η + lmV a a₀ ξ η)
  have key1 : (lmS a a₀ - ξ)/lmSig a a₀ ξ η
      = 1 - η^2/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ)) := by
    have k : (lmS a a₀ - ξ)*(lmSig a a₀ ξ η + (lmS a a₀ - ξ)) + η^2
        = lmSig a a₀ ξ η * (lmSig a a₀ ξ η + (lmS a a₀ - ξ)) := by nlinarith [hS]
    rw [eq_sub_iff_add_eq]
    rw [div_add_div _ _ hc1 (mul_ne_zero hc1 hc2),
      div_eq_one_iff_eq (mul_ne_zero hc1 (mul_ne_zero hc1 hc2))]
    linear_combination (lmSig a a₀ ξ η) * k
  have key2 : lmV a a₀ ξ η/lmTau a a₀ ξ η
      = 1 - (lmY1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)) := by
    have k : (lmV a a₀ ξ η)*(lmTau a a₀ ξ η + (lmV a a₀ ξ η)) + (lmY1 a a₀ ξ η)^2
        = lmTau a a₀ ξ η * (lmTau a a₀ ξ η + (lmV a a₀ ξ η)) := by nlinarith [hT]
    rw [eq_sub_iff_add_eq]
    rw [div_add_div _ _ hd1 (mul_ne_zero hd1 hd2),
      div_eq_one_iff_eq (mul_ne_zero hd1 (mul_ne_zero hd1 hd2))]
    linear_combination (lmTau a a₀ ξ η) * k
  rw [lmF_eq, key1, key2]
  ring

lemma lmF_eq_eta2_phi (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    lmF a a₀ ξ η = η^2 * lmPhi a a₀ ξ η := by
  rw [lmF_decomp h hbox]
  simp only [lmPhi, lmY1_eq]
  ring

lemma lm_den1_ge (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    lmS a a₀^2/4 ≤ lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hσ2 := lmSig_ge ha0 ha1 h1 h2 hbox.1 hbox.2
  have hσpos : 0 < lmSig a a₀ ξ η := by linarith
  have hA := lmS_sub_xi_pos hdata hbox
  have h1' : (lmS a a₀/2)^2 ≤ (lmSig a a₀ ξ η)^2 := pow_le_pow_left₀ (by linarith) hσ2 2
  have h2' : (lmS a a₀/2)^2 = lmS a a₀^2/4 := by ring
  nlinarith [h1', h2', hσpos, hA, mul_pos hσpos hA]

lemma lm_den2_ge (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    lmT a a₀^2/4 ≤ lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have ht := lmT_pos hdata
  have hτ2 := lmTau_ge ha0 ha1 h1 h2 hbox.1 hbox.2
  have hτpos : 0 < lmTau a a₀ ξ η := by linarith
  have hv : 0 < lmV a a₀ ξ η := by linarith [lmV_ge ha0 ha1 h1 h2 hbox.1 hbox.2]
  have h1' : (lmT a a₀/2)^2 ≤ (lmTau a a₀ ξ η)^2 := pow_le_pow_left₀ (by linarith) hτ2 2
  have h2' : (lmT a a₀/2)^2 = lmT a a₀^2/4 := by ring
  nlinarith [h1', h2', hτpos, hv, mul_pos hτpos hv]

lemma lm_den1_pos (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    0 < lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hσpos : 0 < lmSig a a₀ ξ η := by linarith [lmSig_ge ha0 ha1 h1 h2 hbox.1 hbox.2]
  exact mul_pos hσpos (by linarith [lmS_sub_xi_pos hdata hbox])

lemma lm_den2_pos (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    0 < lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have ht := lmT_pos ⟨ha0, ha1, h1, h2⟩
  have hτpos : 0 < lmTau a a₀ ξ η := by linarith [lmTau_ge ha0 ha1 h1 h2 hbox.1 hbox.2]
  have hv : 0 < lmV a a₀ ξ η := by linarith [lmV_ge ha0 ha1 h1 h2 hbox.1 hbox.2]
  exact mul_pos hτpos (by linarith)

lemma lmPhi_bound (h : lmData a a₀) (hbox : lmBox a a₀ ξ η) :
    |lmPhi a a₀ ξ η| ≤ lmMPhi a a₀ := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have ht := lmT_pos hdata
  have hden1 := lm_den1_ge hdata hbox
  have hden2 := lm_den2_ge hdata hbox
  have hden1pos := lm_den1_pos hdata hbox
  have hden2pos := lm_den2_pos hdata hbox
  have hG1 := lmG1_abs_le ha0 ha1 h1 h2 hbox.1 hbox.2
  have hBub : 1/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ)) ≤ 4/(lmS a a₀)^2 := by
    rw [div_le_div_iff₀ hden1pos (by positivity : (0:ℝ) < (lmS a a₀)^2)]
    nlinarith [hden1]
  have hAub : (lmG1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η))
      ≤ (1 + 2/lmS a a₀)^2 * (4/(lmT a a₀)^2) := by
    have hinv2 : 1/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)) ≤ 4/(lmT a a₀)^2 := by
      rw [div_le_div_iff₀ hden2pos (by positivity : (0:ℝ) < (lmT a a₀)^2)]
      nlinarith [hden2]
    have hG1sq : (lmG1 a a₀ ξ η)^2 ≤ (1 + 2/lmS a a₀)^2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) hG1 2
      simpa only [sq_abs] using hh
    calc (lmG1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η))
        = (lmG1 a a₀ ξ η)^2 * (1/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η))) := by
          ring
      _ ≤ (1 + 2/lmS a a₀)^2 * (4/(lmT a a₀)^2) :=
          mul_le_mul hG1sq hinv2 (by positivity) (sq_nonneg _)
  have hAnn : 0 ≤ (lmG1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)) :=
    div_nonneg (sq_nonneg _) hden2pos.le
  have hBnn : 0 ≤ 1/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ)) :=
    div_nonneg (by norm_num) hden1pos.le
  calc |lmPhi a a₀ ξ η|
      = |(lmG1 a a₀ ξ η)^2/(lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η))
          - 1/(lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ))| := by simp only [lmPhi]
    _ ≤ (1 + 2/lmS a a₀)^2 * (4/(lmT a a₀)^2) + 4/(lmS a a₀)^2 := by
        rw [abs_sub_le_iff]
        constructor <;> linarith
    _ ≤ lmMPhi a a₀ := le_of_eq (by simp only [lmMPhi]; ring)

end Decomp

section Lipschitz

variable {a a₀ ξ η ξ' η' : ℝ}

lemma lmSig_lip (a a₀ ξ η ξ' η' : ℝ) :
    |lmSig a a₀ ξ η - lmSig a a₀ ξ' η'| ≤ |ξ - ξ'| + |η - η'| := by
  have h2 : |lmU a a₀ ξ - lmU a a₀ ξ'| = |ξ - ξ'| := by
    have hh : lmU a a₀ ξ - lmU a a₀ ξ' = ξ - ξ' := by simp only [lmU]; ring
    rw [hh]
  have h := lmSqrtLipschitz (lmU a a₀ ξ) η (lmU a a₀ ξ') η'
  rw [h2] at h
  simpa only [lmSig] using h

lemma lm_lip_sqrt2 {u v u' v' b c : ℝ} (h1 : |u - u'| ≤ b) (h2 : |v - v'| ≤ c) :
    |Real.sqrt (u^2 + v^2) - Real.sqrt (u'^2 + v'^2)| ≤ b + c := by
  have := lmSqrtLipschitz u v u' v'
  linarith

lemma lm_lip_sub {f g f' g' Bf Bg : ℝ} (hf : |f - f'| ≤ Bf) (hg : |g - g'| ≤ Bg) :
    |(f - g) - (f' - g')| ≤ Bf + Bg := by
  have h : (f - g) - (f' - g') = (f - f') - (g - g') := by ring
  rw [h]
  refine le_trans (abs_sub_le_iff.mpr ⟨?_, ?_⟩) (add_le_add hf hg) <;>
    linarith [le_abs_self (f - f'), neg_le_abs (f - f'), le_abs_self (g - g'), neg_le_abs (g - g')]

lemma lm_lip_mul {f g f' g' Bf Bg Mf Mg : ℝ} (hf : |f - f'| ≤ Bf) (hg : |g - g'| ≤ Bg)
    (hMf : |f| ≤ Mf) (hMg : |g'| ≤ Mg) : |f * g - f' * g'| ≤ Mf * Bg + Mg * Bf := by
  have h1 := lm_mul_sub_mul f g f' g'
  have h2 : |f| * |g - g'| ≤ Mf * Bg :=
    mul_le_mul hMf hg (abs_nonneg (g - g')) (le_trans (abs_nonneg f) hMf)
  have h3 : |g'| * |f - f'| ≤ Mg * Bf :=
    mul_le_mul hMg hf (abs_nonneg (f - f')) (le_trans (abs_nonneg g') hMg)
  linarith

lemma lm_lip_inv {f f' Bf c : ℝ} (hc : 0 < c) (hx : c ≤ f) (hy : c ≤ f')
    (hf : |f - f'| ≤ Bf) : |f⁻¹ - f'⁻¹| ≤ Bf / c^2 := by
  have hfx : 0 < f := lt_of_lt_of_le hc hx
  have hfy : 0 < f' := lt_of_lt_of_le hc hy
  rw [inv_sub_inv (ne_of_gt hfx) (ne_of_gt hfy), abs_div, abs_of_pos (mul_pos hfx hfy),
    abs_sub_comm]
  have hc2 : c^2 ≤ f * f' := by nlinarith [hx, hy, hc]
  exact le_trans (div_le_div_of_nonneg_left (abs_nonneg (f - f')) (by positivity) hc2)
    (div_le_div_of_nonneg_right hf (by positivity))

lemma lmInvSig_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |(lmSig a a₀ ξ η)⁻¹ - (lmSig a a₀ ξ' η')⁻¹| ≤ kG1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hA := lmSig_ge ha0 ha1 h1 h2 hb.1 hb.2
  have hB := lmSig_ge ha0 ha1 h1 h2 hb'.1 hb'.2
  have hsig := lmSig_lip a a₀ ξ η ξ' η'
  have h := lm_lip_inv (f := lmSig a a₀ ξ η) (f' := lmSig a a₀ ξ' η')
    (c := lmS a a₀/2) (by linarith) hA hB hsig
  calc |(lmSig a a₀ ξ η)⁻¹ - (lmSig a a₀ ξ' η')⁻¹|
      ≤ (|ξ - ξ'| + |η - η'|) / (lmS a a₀/2)^2 := h
    _ = kG1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
        simp only [kG1]; field_simp; ring

lemma lmX1_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmX1 a a₀ ξ η - lmX1 a a₀ ξ' η'| ≤ kX1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hU := lmU_abs_le hdata hb
  have hUdiff : |lmU a a₀ ξ - lmU a a₀ ξ'| ≤ |ξ - ξ'| := by
    have hh : lmU a a₀ ξ - lmU a a₀ ξ' = ξ - ξ' := by simp only [lmU]; ring
    rw [hh]
  have hinv := lmInvSig_lip hdata hb hb'
  have hsig' := lmSig_ge ha0 ha1 h1 h2 hb'.1 hb'.2
  have hsig'pos : 0 < lmSig a a₀ ξ' η' := by linarith
  have hinvbound : |(lmSig a a₀ ξ' η')⁻¹| ≤ 2/lmS a a₀ := by
    rw [abs_of_pos (inv_pos.mpr hsig'pos)]
    have hpos : (0:ℝ) < lmS a a₀/2 := by linarith
    have hh : 1/lmSig a a₀ ξ' η' ≤ 1/(lmS a a₀/2) := one_div_le_one_div_of_le hpos hsig'
    have h2' : 1/(lmS a a₀/2) = 2/lmS a a₀ := by field_simp
    simpa only [one_div, h2'] using hh
  have hmul := lm_lip_mul hUdiff hinv hU hinvbound
  have hdec : lmX1 a a₀ ξ η - lmX1 a a₀ ξ' η'
      = (ξ - lmU a a₀ ξ * (lmSig a a₀ ξ η)⁻¹)
          - (ξ' - lmU a a₀ ξ' * (lmSig a a₀ ξ' η')⁻¹) := by
    simp only [lmX1]; ring
  rw [hdec]
  have hstep := lm_lip_sub (f := ξ) (g := lmU a a₀ ξ * (lmSig a a₀ ξ η)⁻¹)
    (f' := ξ') (g' := lmU a a₀ ξ' * (lmSig a a₀ ξ' η')⁻¹)
    (Bf := |ξ - ξ'|) (Bg := 2 * lmS a a₀ * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|))
      + (2/lmS a a₀) * |ξ - ξ'|) (le_refl _) hmul
  refine le_trans hstep ?_
  simp only [kX1]
  have hD := abs_nonneg (ξ - ξ'); have hE := abs_nonneg (η - η')
  have hfield : 2 * lmS a a₀ * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|))
      = 8/lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by
    simp only [kG1]; field_simp; ring
  rw [hfield]
  have hkey : (1 + 10/lmS a a₀) * (|ξ - ξ'| + |η - η'|)
      - (|ξ - ξ'| + (8/lmS a a₀ * (|ξ - ξ'| + |η - η'|) + 2/lmS a a₀ * |ξ - ξ'|))
      = |η - η'| + 2/lmS a a₀ * |η - η'| := by ring
  have hpos : 0 ≤ |η - η'| + 2/lmS a a₀ * |η - η'| := by positivity
  linarith [hkey, hpos]

lemma lmY1_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmY1 a a₀ ξ η - lmY1 a a₀ ξ' η'| ≤ kY1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hG1 := lmG1_abs_le ha0 ha1 h1 h2 hb.1 hb.2
  have hG1' := lmG1_abs_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have heta := abs_eta_le_lmS a a₀ ξ η hb
  have hG1diff : |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'| ≤ kG1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have hh : lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'
        = (lmSig a a₀ ξ' η')⁻¹ - (lmSig a a₀ ξ η)⁻¹ := by simp only [lmG1]; ring
    rw [hh, abs_sub_comm]
    exact lmInvSig_lip hdata hb hb'
  have hprod := lm_mul_sub_mul η (lmG1 a a₀ ξ η) η' (lmG1 a a₀ ξ' η')
  rw [lmY1_eq, lmY1_eq]
  have h1' : |η| * |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'|
      ≤ (lmS a a₀/16) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) :=
    mul_le_mul heta hG1diff (abs_nonneg _) (by linarith [hs])
  have h2' : |lmG1 a a₀ ξ' η'| * |η - η'| ≤ (1 + 2/lmS a a₀) * |η - η'| :=
    mul_le_mul_of_nonneg_right hG1' (abs_nonneg (η - η'))
  calc |η * lmG1 a a₀ ξ η - η' * lmG1 a a₀ ξ' η'|
      ≤ |η| * |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'| + |lmG1 a a₀ ξ' η'| * |η - η'| := hprod
    _ ≤ (lmS a a₀/16) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) + (1 + 2/lmS a a₀) * |η - η'| := by
        linarith [h1', h2']
    _ ≤ kY1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
        simp only [kY1]
        have hfield : (lmS a a₀/16) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|))
            = (1/(4 * lmS a a₀)) * (|ξ - ξ'| + |η - η'|) := by
          simp only [kG1]; field_simp; ring
        rw [hfield]
        have hkey : (1 + 3/lmS a a₀) * (|ξ - ξ'| + |η - η'|)
            - ((1/(4 * lmS a a₀)) * (|ξ - ξ'| + |η - η'|) + (1 + 2/lmS a a₀) * |η - η'|)
            = (1 + 11/(4*lmS a a₀)) * |ξ - ξ'| + (3/(4*lmS a a₀)) * |η - η'| := by ring
        have hpos : 0 ≤ (1 + 11/(4*lmS a a₀)) * |ξ - ξ'| + (3/(4*lmS a a₀)) * |η - η'| := by
          have h11 : (0:ℝ) < 11/(4*lmS a a₀) := by positivity
          have h3 : (0:ℝ) < 3/(4*lmS a a₀) := by positivity
          nlinarith [abs_nonneg (ξ - ξ'), abs_nonneg (η - η')]
        linarith [hkey, hpos]

lemma lmV_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmV a a₀ ξ η - lmV a a₀ ξ' η'| ≤ kX1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  have hx := lmX1_lip h hb hb'
  have hh : lmV a a₀ ξ η - lmV a a₀ ξ' η'
      = lmX1 a a₀ ξ η - lmX1 a a₀ ξ' η' := by simp only [lmV]; ring
  rw [hh]; exact hx

lemma lmTau_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmTau a a₀ ξ η - lmTau a a₀ ξ' η'| ≤ kTau a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hv := lmV_lip hdata hb hb'
  have hy := lmY1_lip hdata hb hb'
  have h := lm_lip_sqrt2 (u := lmV a a₀ ξ η) (v := lmY1 a a₀ ξ η)
    (u' := lmV a a₀ ξ' η') (v' := lmY1 a a₀ ξ' η')
    (b := kX1 a a₀ * (|ξ - ξ'| + |η - η'|)) (c := kY1 a a₀ * (|ξ - ξ'| + |η - η'|)) hv hy
  simp only [lmTau] at h ⊢
  refine le_trans h ?_
  have hkey : kTau a a₀ * (|ξ - ξ'| + |η - η'|)
      - (kX1 a a₀ * (|ξ - ξ'| + |η - η'|) + kY1 a a₀ * (|ξ - ξ'| + |η - η'|)) = 0 := by
    simp only [kX1, kY1, kTau]; ring
  linarith [hkey]

lemma lmInvTau_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |(lmTau a a₀ ξ η)⁻¹ - (lmTau a a₀ ξ' η')⁻¹| ≤ kG2 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have ht := lmT_pos hdata
  have htau := lmTau_lip hdata hb hb'
  have hA := lmTau_ge ha0 ha1 h1 h2 hb.1 hb.2
  have hB := lmTau_ge ha0 ha1 h1 h2 hb'.1 hb'.2
  have h := lm_lip_inv (f := lmTau a a₀ ξ η) (f' := lmTau a a₀ ξ' η')
    (c := lmT a a₀/2) (by linarith) hA hB htau
  calc |(lmTau a a₀ ξ η)⁻¹ - (lmTau a a₀ ξ' η')⁻¹|
      ≤ (kTau a a₀ * (|ξ - ξ'| + |η - η'|)) / (lmT a a₀/2)^2 := h
    _ = kG2 a a₀ * (|ξ - ξ'| + |η - η'|) := by
        simp only [kG2, kTau]; field_simp; ring

lemma lmG_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmG a a₀ ξ η - lmG a a₀ ξ' η'| ≤ lmKG a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have ht := lmT_pos hdata
  have hG1 := lmG1_abs_le ha0 ha1 h1 h2 hb.1 hb.2
  have hG2 := lmG2_abs_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have hg2 : |lmG2 a a₀ ξ η - lmG2 a a₀ ξ' η'| ≤ kG2 a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have hh : lmG2 a a₀ ξ η - lmG2 a a₀ ξ' η'
        = (lmTau a a₀ ξ' η')⁻¹ - (lmTau a a₀ ξ η)⁻¹ := by simp only [lmG2]; ring
    rw [hh, abs_sub_comm]; exact lmInvTau_lip hdata hb hb'
  have hg1 : |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'| ≤ kG1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have hh : lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'
        = (lmSig a a₀ ξ' η')⁻¹ - (lmSig a a₀ ξ η)⁻¹ := by simp only [lmG1]; ring
    rw [hh, abs_sub_comm]; exact lmInvSig_lip hdata hb hb'
  have hprod := lm_mul_sub_mul (lmG1 a a₀ ξ η) (lmG2 a a₀ ξ η)
    (lmG1 a a₀ ξ' η') (lmG2 a a₀ ξ' η')
  simp only [lmG]
  have h1' : |lmG1 a a₀ ξ η| * |lmG2 a a₀ ξ η - lmG2 a a₀ ξ' η'|
      ≤ (1 + 2/lmS a a₀) * (kG2 a a₀ * (|ξ - ξ'| + |η - η'|)) :=
    mul_le_mul hG1 hg2 (abs_nonneg (lmG2 a a₀ ξ η - lmG2 a a₀ ξ' η')) (by positivity)
  have h2' : |lmG2 a a₀ ξ' η'| * |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'|
      ≤ (1 + 2/lmT a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) :=
    mul_le_mul hG2 hg1 (abs_nonneg (lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η')) (by positivity)
  have hmid : |lmG1 a a₀ ξ η * lmG2 a a₀ ξ η - lmG1 a a₀ ξ' η' * lmG2 a a₀ ξ' η'|
      ≤ (1 + 2/lmS a a₀) * (kG2 a a₀ * (|ξ - ξ'| + |η - η'|))
        + (1 + 2/lmT a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) := by
    linarith [hprod, h1', h2']
  exact le_trans hmid (le_of_eq (by simp only [lmKG]; ring))

end Lipschitz

section Bounds

variable {a a₀ ξ η ξ' η' : ℝ}

lemma lmF_bound (h : lmData a a₀) (hb : lmBox a a₀ ξ η) :
    |lmF a a₀ ξ η| ≤ lmMPhi a a₀ * η^2 := by
  rw [lmF_eq_eta2_phi h hb, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc η^2 * |lmPhi a a₀ ξ η| ≤ η^2 * lmMPhi a a₀ :=
        mul_le_mul_of_nonneg_left (lmPhi_bound h hb) (sq_nonneg η)
    _ = lmMPhi a a₀ * η^2 := by ring

lemma lmG_bound (h : lmData a a₀) (hb : lmBox a a₀ ξ η) :
    |lmG a a₀ ξ η - lmLam a a₀| ≤ lmKG a a₀ * (|ξ| + |η|) := by
  have h0 : lmBox a a₀ 0 0 := lmBox_zero h
  have hlip := lmG_lip h hb h0
  rw [lmLam_eq_G00 h.ha h.ha1 h.h1 h.h2]
  simpa using hlip

lemma lm_den1_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ)
      - lmSig a a₀ ξ' η' * (lmSig a a₀ ξ' η' + lmS a a₀ - ξ')|
      ≤ kA1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have hσU := lmSig_le ha0 ha1 h1 h2 hb.1 hb.2
  have hσU' := lmSig_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have hσnn : 0 ≤ lmSig a a₀ ξ η := by linarith [lmSig_ge ha0 ha1 h1 h2 hb.1 hb.2, hs]
  have hσ'nn : 0 ≤ lmSig a a₀ ξ' η' := by linarith [lmSig_ge ha0 ha1 h1 h2 hb'.1 hb'.2, hs]
  have hsig := lmSig_lip a a₀ ξ η ξ' η'
  have hxi := abs_le_lmS a a₀ ξ' η' hb'
  have hp : 0 ≤ lmS a a₀ - ξ' := by
    have h2' : ξ' ≤ lmS a a₀ / 16 := le_trans (le_abs_self ξ') hxi
    linarith
  have hDnn : 0 ≤ |ξ - ξ'| + |η - η'| := by positivity
  have hsplit : lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ)
      - lmSig a a₀ ξ' η' * (lmSig a a₀ ξ' η' + lmS a a₀ - ξ')
      = ((lmSig a a₀ ξ η)^2 - (lmSig a a₀ ξ' η')^2)
        + (lmSig a a₀ ξ η * (lmS a a₀ - ξ) - lmSig a a₀ ξ' η' * (lmS a a₀ - ξ')) := by
    ring
  rw [hsplit]
  have hsq : |(lmSig a a₀ ξ η)^2 - (lmSig a a₀ ξ' η')^2|
      ≤ 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have he : (lmSig a a₀ ξ η)^2 - (lmSig a a₀ ξ' η')^2
        = (lmSig a a₀ ξ η - lmSig a a₀ ξ' η')
          * (lmSig a a₀ ξ η + lmSig a a₀ ξ' η') := by ring
    rw [he, abs_mul,
      abs_of_nonneg (show (0:ℝ) ≤ lmSig a a₀ ξ η + lmSig a a₀ ξ' η' by linarith)]
    calc |lmSig a a₀ ξ η - lmSig a a₀ ξ' η'| * (lmSig a a₀ ξ η + lmSig a a₀ ξ' η')
        ≤ (|ξ - ξ'| + |η - η'|) * (2 * lmS a a₀ + 2 * lmS a a₀) :=
          mul_le_mul hsig (by linarith) (by linarith) hDnn
      _ = 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by ring
  have hcross : |lmSig a a₀ ξ η * (lmS a a₀ - ξ) - lmSig a a₀ ξ' η' * (lmS a a₀ - ξ')|
      ≤ 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have hprod := lm_mul_sub_mul (lmSig a a₀ ξ η) (lmS a a₀ - ξ)
      (lmSig a a₀ ξ' η') (lmS a a₀ - ξ')
    have hdiff : |(lmS a a₀ - ξ) - (lmS a a₀ - ξ')| = |ξ - ξ'| := by
      have hh : (lmS a a₀ - ξ) - (lmS a a₀ - ξ') = -(ξ - ξ') := by ring
      rw [hh, abs_neg]
    have h1' : |lmSig a a₀ ξ η| * |(lmS a a₀ - ξ) - (lmS a a₀ - ξ')| ≤ 2 * lmS a a₀ * |ξ - ξ'| := by
      rw [hdiff, abs_of_nonneg hσnn]
      exact mul_le_mul_of_nonneg_right hσU (abs_nonneg _)
    have h2' : |lmS a a₀ - ξ'| * |lmSig a a₀ ξ η - lmSig a a₀ ξ' η'|
        ≤ 2 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by
      rw [abs_of_nonneg hp]
      exact mul_le_mul (by linarith [neg_le_abs ξ', hxi, hs]) hsig (abs_nonneg _) (by linarith [hs])
    calc |lmSig a a₀ ξ η * (lmS a a₀ - ξ) - lmSig a a₀ ξ' η' * (lmS a a₀ - ξ')|
        ≤ |lmSig a a₀ ξ η| * |(lmS a a₀ - ξ) - (lmS a a₀ - ξ')|
            + |lmS a a₀ - ξ'| * |lmSig a a₀ ξ η - lmSig a a₀ ξ' η'| := hprod
      _ ≤ 2 * lmS a a₀ * |ξ - ξ'| + 2 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) :=
          add_le_add h1' h2'
      _ ≤ 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) := by
          have hD := abs_nonneg (ξ - ξ'); have hE := abs_nonneg (η - η')
          nlinarith [hs, hD, hE]
  calc |(lmSig a a₀ ξ η)^2 - (lmSig a a₀ ξ' η')^2
        + (lmSig a a₀ ξ η * (lmS a a₀ - ξ) - lmSig a a₀ ξ' η' * (lmS a a₀ - ξ'))|
      ≤ |(lmSig a a₀ ξ η)^2 - (lmSig a a₀ ξ' η')^2|
        + |lmSig a a₀ ξ η * (lmS a a₀ - ξ) - lmSig a a₀ ξ' η' * (lmS a a₀ - ξ')| :=
        abs_add_le _ _
    _ ≤ 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) + 4 * lmS a a₀ * (|ξ - ξ'| + |η - η'|) :=
        add_le_add hsq hcross
    _ = kA1 a a₀ * (|ξ - ξ'| + |η - η'|) := by simp only [kA1]; ring

lemma lm_den2_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)
      - lmTau a a₀ ξ' η' * (lmTau a a₀ ξ' η' + lmV a a₀ ξ' η')|
      ≤ kA2 a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have ht := lmT_pos hdata
  have hτU := lmTau_le ha0 ha1 h1 h2 hb.1 hb.2
  have hτU' := lmTau_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have hτnn : 0 ≤ lmTau a a₀ ξ η := by linarith [lmTau_ge ha0 ha1 h1 h2 hb.1 hb.2, ht]
  have hτ'nn : 0 ≤ lmTau a a₀ ξ' η' := by linarith [lmTau_ge ha0 ha1 h1 h2 hb'.1 hb'.2, ht]
  have hvU := lmV_le ha0 ha1 h1 h2 hb.1 hb.2
  have hvU' := lmV_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have hvnn' : 0 ≤ lmV a a₀ ξ' η' := by linarith [lmV_ge ha0 ha1 h1 h2 hb'.1 hb'.2, ht]
  have htau := lmTau_lip hdata hb hb'
  have hV := lmV_lip hdata hb hb'
  have hDnn : 0 ≤ |ξ - ξ'| + |η - η'| := by positivity
  have hsplit : lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η)
      - lmTau a a₀ ξ' η' * (lmTau a a₀ ξ' η' + lmV a a₀ ξ' η')
      = ((lmTau a a₀ ξ η)^2 - (lmTau a a₀ ξ' η')^2)
        + (lmTau a a₀ ξ η * lmV a a₀ ξ η - lmTau a a₀ ξ' η' * lmV a a₀ ξ' η') := by ring
  rw [hsplit]
  have hsq : |(lmTau a a₀ ξ η)^2 - (lmTau a a₀ ξ' η')^2|
      ≤ 6 * kTau a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have he : (lmTau a a₀ ξ η)^2 - (lmTau a a₀ ξ' η')^2
        = (lmTau a a₀ ξ η - lmTau a a₀ ξ' η')
          * (lmTau a a₀ ξ η + lmTau a a₀ ξ' η') := by ring
    rw [he, abs_mul,
      abs_of_nonneg (show (0:ℝ) ≤ lmTau a a₀ ξ η + lmTau a a₀ ξ' η' by linarith)]
    calc |lmTau a a₀ ξ η - lmTau a a₀ ξ' η'| * (lmTau a a₀ ξ η + lmTau a a₀ ξ' η')
        ≤ (kTau a a₀ * (|ξ - ξ'| + |η - η'|)) * (3 + 3) :=
          mul_le_mul htau (by linarith) (by linarith)
            (mul_nonneg (le_of_lt (by simp only [kTau]; positivity)) hDnn)
      _ = 6 * kTau a a₀ * (|ξ - ξ'| + |η - η'|) := by ring
  have hcross : |lmTau a a₀ ξ η * lmV a a₀ ξ η - lmTau a a₀ ξ' η' * lmV a a₀ ξ' η'|
      ≤ (3 * kX1 a a₀ + 2 * lmT a a₀ * kTau a a₀) * (|ξ - ξ'| + |η - η'|) := by
    have hprod := lm_mul_sub_mul (lmTau a a₀ ξ η) (lmV a a₀ ξ η)
      (lmTau a a₀ ξ' η') (lmV a a₀ ξ' η')
    have h1' : lmTau a a₀ ξ η * |lmV a a₀ ξ η - lmV a a₀ ξ' η'|
        ≤ 3 * (kX1 a a₀ * (|ξ - ξ'| + |η - η'|)) :=
      mul_le_mul hτU hV (abs_nonneg _) (by norm_num)
    have h2' : lmV a a₀ ξ' η' * |lmTau a a₀ ξ η - lmTau a a₀ ξ' η'|
        ≤ (2 * lmT a a₀) * (kTau a a₀ * (|ξ - ξ'| + |η - η'|)) :=
      mul_le_mul hvU' htau (abs_nonneg _) (by linarith)
    calc |lmTau a a₀ ξ η * lmV a a₀ ξ η - lmTau a a₀ ξ' η' * lmV a a₀ ξ' η'|
        ≤ |lmTau a a₀ ξ η| * |lmV a a₀ ξ η - lmV a a₀ ξ' η'|
            + |lmV a a₀ ξ' η'| * |lmTau a a₀ ξ η - lmTau a a₀ ξ' η'| := hprod
      _ ≤ 3 * (kX1 a a₀ * (|ξ - ξ'| + |η - η'|))
            + (2 * lmT a a₀) * (kTau a a₀ * (|ξ - ξ'| + |η - η'|)) := by
          rw [abs_of_nonneg hτnn, abs_of_nonneg hvnn']
          linarith [h1', h2']
      _ = (3 * kX1 a a₀ + 2 * lmT a a₀ * kTau a a₀) * (|ξ - ξ'| + |η - η'|) := by ring
  calc |(lmTau a a₀ ξ η)^2 - (lmTau a a₀ ξ' η')^2
        + (lmTau a a₀ ξ η * lmV a a₀ ξ η - lmTau a a₀ ξ' η' * lmV a a₀ ξ' η')|
      ≤ |(lmTau a a₀ ξ η)^2 - (lmTau a a₀ ξ' η')^2|
        + |lmTau a a₀ ξ η * lmV a a₀ ξ η - lmTau a a₀ ξ' η' * lmV a a₀ ξ' η'| :=
        abs_add_le _ _
    _ ≤ 6 * kTau a a₀ * (|ξ - ξ'| + |η - η'|)
        + (3 * kX1 a a₀ + 2 * lmT a a₀ * kTau a a₀) * (|ξ - ξ'| + |η - η'|) :=
        add_le_add hsq hcross
    _ = kA2 a a₀ * (|ξ - ξ'| + |η - η'|) := by simp only [kA2]; ring

lemma lmPhi_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmPhi a a₀ ξ η - lmPhi a a₀ ξ' η'| ≤ lmKPhi a a₀ * (|ξ - ξ'| + |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hs := lmS_pos hdata
  have ht := lmT_pos hdata
  simp only [lmPhi]
  set A1 := lmSig a a₀ ξ η * (lmSig a a₀ ξ η + lmS a a₀ - ξ) with hA1def
  set A1' := lmSig a a₀ ξ' η' * (lmSig a a₀ ξ' η' + lmS a a₀ - ξ') with hA1'def
  set A2 := lmTau a a₀ ξ η * (lmTau a a₀ ξ η + lmV a a₀ ξ η) with hA2def
  set A2' := lmTau a a₀ ξ' η' * (lmTau a a₀ ξ' η' + lmV a a₀ ξ' η') with hA2'def
  have hA1ge : lmS a a₀^2/4 ≤ A1 := by rw [hA1def]; exact lm_den1_ge hdata hb
  have hA1ge' : lmS a a₀^2/4 ≤ A1' := by rw [hA1'def]; exact lm_den1_ge hdata hb'
  have hA2ge : lmT a a₀^2/4 ≤ A2 := by rw [hA2def]; exact lm_den2_ge hdata hb
  have hA2ge' : lmT a a₀^2/4 ≤ A2' := by rw [hA2'def]; exact lm_den2_ge hdata hb'
  have hA1pos : 0 < A1 := by rw [hA1def]; exact lm_den1_pos hdata hb
  have hA2pos' : 0 < A2' := by rw [hA2'def]; exact lm_den2_pos hdata hb'
  have hdA1 : |A1 - A1'| ≤ kA1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
    rw [hA1def, hA1'def]; exact lm_den1_lip hdata hb hb'
  have hdA2 : |A2 - A2'| ≤ kA2 a a₀ * (|ξ - ξ'| + |η - η'|) := by
    rw [hA2def, hA2'def]; exact lm_den2_lip hdata hb hb'
  have hG1 := lmG1_abs_le ha0 ha1 h1 h2 hb.1 hb.2
  have hG1' := lmG1_abs_le ha0 ha1 h1 h2 hb'.1 hb'.2
  have hgg1 : |(lmG1 a a₀ ξ η)^2 - (lmG1 a a₀ ξ' η')^2|
      ≤ 2 * (1 + 2/lmS a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) := by
    have hg1 : |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'| ≤ kG1 a a₀ * (|ξ - ξ'| + |η - η'|) := by
      have hh : lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'
          = (lmSig a a₀ ξ' η')⁻¹ - (lmSig a a₀ ξ η)⁻¹ := by simp only [lmG1]; ring
      rw [hh, abs_sub_comm]; exact lmInvSig_lip hdata hb hb'
    have hprod := lm_mul_sub_mul (lmG1 a a₀ ξ η) (lmG1 a a₀ ξ η)
      (lmG1 a a₀ ξ' η') (lmG1 a a₀ ξ' η')
    have hEq : (lmG1 a a₀ ξ η)^2 - (lmG1 a a₀ ξ' η')^2
        = lmG1 a a₀ ξ η * lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η' * lmG1 a a₀ ξ' η' := by ring
    rw [hEq]
    calc |lmG1 a a₀ ξ η * lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η' * lmG1 a a₀ ξ' η'|
        ≤ |lmG1 a a₀ ξ η| * |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'|
            + |lmG1 a a₀ ξ' η'| * |lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'| := hprod
      _ ≤ (1 + 2/lmS a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|))
            + (1 + 2/lmS a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) := by
          have h1' := mul_le_mul hG1 hg1 (abs_nonneg (lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'))
            (by positivity)
          have h2' := mul_le_mul hG1' hg1 (abs_nonneg (lmG1 a a₀ ξ η - lmG1 a a₀ ξ' η'))
            (by positivity)
          linarith [h1', h2']
      _ = 2 * (1 + 2/lmS a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|)) := by ring
  have h11 : |1/A1 - 1/A1'| ≤ (16 * kA1 a a₀ / (lmS a a₀)^4) * (|ξ - ξ'| + |η - η'|) := by
    have hc : (0:ℝ) < (lmS a a₀/2)^2 := by positivity
    have hx : (lmS a a₀/2)^2 ≤ A1 := by nlinarith [hA1ge]
    have hy : (lmS a a₀/2)^2 ≤ A1' := by nlinarith [hA1ge']
    have hinv := lm_lip_inv hc hx hy hdA1
    calc |1/A1 - 1/A1'| ≤ (kA1 a a₀ * (|ξ - ξ'| + |η - η'|)) / ((lmS a a₀/2)^2)^2 := by
          simpa only [one_div] using hinv
      _ = (16 * kA1 a a₀ / (lmS a a₀)^4) * (|ξ - ξ'| + |η - η'|) := by
          simp only [kA1]; field_simp; ring
  have hA2inv' : |(A2')⁻¹| ≤ 4/(lmT a a₀)^2 := by
    rw [abs_of_pos (inv_pos.mpr hA2pos')]
    have hc : (0:ℝ) < (lmT a a₀/2)^2 := by positivity
    have hy : (lmT a a₀/2)^2 ≤ A2' := by nlinarith [hA2ge']
    have hh : 1/A2' ≤ 1/((lmT a a₀/2)^2) := one_div_le_one_div_of_le hc hy
    have hh' : (A2')⁻¹ ≤ ((lmT a a₀/2)^2)⁻¹ := by simpa only [one_div] using hh
    have h2' : ((lmT a a₀/2)^2)⁻¹ = 4/(lmT a a₀)^2 := by field_simp; ring
    linarith [hh', h2']
  have hinv2 : |A2⁻¹ - (A2')⁻¹| ≤ (16 * kA2 a a₀ / (lmT a a₀)^4) * (|ξ - ξ'| + |η - η'|) := by
    have hc : (0:ℝ) < (lmT a a₀/2)^2 := by positivity
    have hx : (lmT a a₀/2)^2 ≤ A2 := by nlinarith [hA2ge]
    have hy : (lmT a a₀/2)^2 ≤ A2' := by nlinarith [hA2ge']
    have hinv := lm_lip_inv hc hx hy hdA2
    calc |A2⁻¹ - (A2')⁻¹| ≤ (kA2 a a₀ * (|ξ - ξ'| + |η - η'|)) / ((lmT a a₀/2)^2)^2 := hinv
      _ = (16 * kA2 a a₀ / (lmT a a₀)^4) * (|ξ - ξ'| + |η - η'|) := by
          simp only [kA2]; field_simp; ring
  have hsq1 : (lmG1 a a₀ ξ η)^2 ≤ (1 + 2/lmS a a₀)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hG1 2
    simpa only [sq_abs] using hh
  have hGG : |(lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹|
      ≤ ((1 + 2/lmS a a₀)^2 * (16 * kA2 a a₀ / (lmT a a₀)^4)
          + (4/(lmT a a₀)^2) * (2 * (1 + 2/lmS a a₀) * kG1 a a₀))
        * (|ξ - ξ'| + |η - η'|) := by
    have hprod := lm_mul_sub_mul ((lmG1 a a₀ ξ η)^2) (A2⁻¹) ((lmG1 a a₀ ξ' η')^2) (A2')⁻¹
    have hp1 : (0:ℝ) ≤ (1 + 2/lmS a a₀)^2 := sq_nonneg _
    have hp2 : (0:ℝ) ≤ 4/(lmT a a₀)^2 := div_nonneg (by norm_num) (sq_nonneg _)
    have h1' := mul_le_mul hsq1 hinv2 (abs_nonneg (A2⁻¹ - (A2')⁻¹)) hp1
    have h2' := mul_le_mul hA2inv' hgg1 (abs_nonneg ((lmG1 a a₀ ξ η)^2 - (lmG1 a a₀ ξ' η')^2)) hp2
    have hsum : ((1 + 2/lmS a a₀)^2 * ((16 * kA2 a a₀ / (lmT a a₀)^4) * (|ξ - ξ'| + |η - η'|))
        + (4/(lmT a a₀)^2) * (2 * (1 + 2/lmS a a₀) * (kG1 a a₀ * (|ξ - ξ'| + |η - η'|))))
        = ((1 + 2/lmS a a₀)^2 * (16 * kA2 a a₀ / (lmT a a₀)^4)
          + (4/(lmT a a₀)^2) * (2 * (1 + 2/lmS a a₀) * kG1 a a₀))
          * (|ξ - ξ'| + |η - η'|) := by ring
    rw [abs_of_nonneg (sq_nonneg (lmG1 a a₀ ξ η))] at hprod
    rw [← hsum]
    linarith [hprod, h1', h2']
  have hmain : |(lmG1 a a₀ ξ η)^2 * A2⁻¹ - 1/A1
      - ((lmG1 a a₀ ξ' η')^2 * (A2')⁻¹ - 1/A1')|
      ≤ lmKPhi a a₀ * (|ξ - ξ'| + |η - η'|) := by
    have hsplit : (lmG1 a a₀ ξ η)^2 * A2⁻¹ - 1/A1
        - ((lmG1 a a₀ ξ' η')^2 * (A2')⁻¹ - 1/A1')
        = ((lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹) - (1/A1 - 1/A1') := by
      ring
    rw [hsplit]
    have hb2 : |((lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹) - (1/A1 - 1/A1')|
        ≤ |(lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹| + |1/A1 - 1/A1'| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [le_abs_self ((lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹),
        neg_le_abs ((lmG1 a a₀ ξ η)^2 * A2⁻¹ - (lmG1 a a₀ ξ' η')^2 * (A2')⁻¹),
        le_abs_self (1/A1 - 1/A1'), neg_le_abs (1/A1 - 1/A1')]
    refine le_trans hb2 ?_
    have hsum : ((1 + 2/lmS a a₀)^2 * (16 * kA2 a a₀ / (lmT a a₀)^4)
          + (4/(lmT a a₀)^2) * (2 * (1 + 2/lmS a a₀) * kG1 a a₀))
          * (|ξ - ξ'| + |η - η'|)
        + (16 * kA1 a a₀ / (lmS a a₀)^4) * (|ξ - ξ'| + |η - η'|)
        = lmKPhi a a₀ * (|ξ - ξ'| + |η - η'|) := by
      simp only [lmKPhi]; ring
    rw [← hsum]
    exact add_le_add hGG h11
  rw [show (lmG1 a a₀ ξ η)^2/A2 - 1/A1 - ((lmG1 a a₀ ξ' η')^2/A2' - 1/A1')
      = (lmG1 a a₀ ξ η)^2 * A2⁻¹ - 1/A1 - ((lmG1 a a₀ ξ' η')^2 * (A2')⁻¹ - 1/A1') by ring]
  exact hmain

lemma lmF_lip (h : lmData a a₀) (hb : lmBox a a₀ ξ η) (hb' : lmBox a a₀ ξ' η') :
    |lmF a a₀ ξ η - lmF a a₀ ξ' η'|
      ≤ lmKF a a₀ * (η^2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|) := by
  obtain ⟨ha0, ha1, h1, h2⟩ := h
  have hdata : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hH := lmH_lt_one hdata
  have hk := lmPhi_lip hdata hb hb'
  have hbPhi := lmPhi_bound hdata hb'
  rw [lmF_eq_eta2_phi hdata hb, lmF_eq_eta2_phi hdata hb']
  have hprod := lm_mul_sub_mul (η^2) (lmPhi a a₀ ξ η) (η'^2) (lmPhi a a₀ ξ' η')
  have h2' : |η^2 - η'^2| ≤ (|η| + |η'|) * |η - η'| := by
    have hh : η^2 - η'^2 = (η - η') * (η + η') := by ring
    rw [hh, abs_mul]
    have := abs_add_le η η'
    nlinarith [abs_nonneg (η - η'), abs_nonneg (η + η')]
  have hmid : |η^2 * lmPhi a a₀ ξ η - η'^2 * lmPhi a a₀ ξ' η'|
      ≤ η^2 * (lmKPhi a a₀ * (|ξ - ξ'| + |η - η'|))
        + lmMPhi a a₀ * ((|η| + |η'|) * |η - η'|) := by
    rw [abs_of_nonneg (sq_nonneg η)] at hprod
    have h1' := mul_le_mul_of_nonneg_left hk (sq_nonneg η)
    have h2'' := mul_le_mul hbPhi h2' (abs_nonneg (η^2 - η'^2)) (lmMPhi_nonneg a a₀)
    linarith [hprod, h1', h2'']
  refine le_trans hmid ?_
  have hkey : lmKF a a₀ * (η^2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|)
      - (η^2 * (lmKPhi a a₀ * (|ξ - ξ'| + |η - η'|))
        + lmMPhi a a₀ * ((|η| + |η'|) * |η - η'|))
      = lmMPhi a a₀ * η^2 * |ξ - ξ'| + lmKPhi a a₀ * |η - η'| * ((|η| + |η'|) - η^2) := by
    simp only [lmKF]; ring
  have h1n : 0 ≤ lmMPhi a a₀ := lmMPhi_nonneg a a₀
  have h2n : 0 ≤ lmKPhi a a₀ := lmKPhi_nonneg hdata
  have h3n : 0 ≤ (|η| + |η'|) - η^2 := by
    nlinarith [hb.2, hH, abs_nonneg η, abs_nonneg η', sq_nonneg η, sq_abs η]
  have hpos : 0 ≤ lmMPhi a a₀ * η^2 * |ξ - ξ'| + lmKPhi a a₀ * |η - η'| * ((|η| + |η'|) - η^2) :=
    add_nonneg (mul_nonneg (mul_nonneg h1n (sq_nonneg η)) (abs_nonneg _))
      (mul_nonneg (mul_nonneg h2n (abs_nonneg _)) h3n)
  linarith [hkey, hpos]

section Assembly

theorem eqT_localModel {a a₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2)) :
    ∃ lam C ε : ℝ, LocalModel (eqT a) ((a₀ : ℝ) : ℂ) lam C ε := by
  have hD : lmData a a₀ := ⟨ha0, ha1, h1, h2⟩
  have hlam0 : 0 < lmLam a a₀ := (lmLamBounds ha0 ha1 h1 h2).1
  have hlam1 : lmLam a a₀ < 1 := (lmLamBounds ha0 ha1 h1 h2).2.1
  have hCpos : 0 < lmC a a₀ := lmC_pos a a₀
  have hHpos : 0 < lmH a a₀ := lmH_pos hD
  have heps_pos : 0 < lmEps a a₀ := by
    simp only [lmEps]
    exact lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have h4eps : 4 * lmEps a a₀ ≤ lmH a a₀ := by
    have hle := min_le_left (lmH a a₀/8) ((1 - lmLam a a₀)/(8*lmC a a₀))
    have hHnn : 0 ≤ lmH a a₀ := le_of_lt hHpos
    simp only [lmEps] at hle ⊢
    linarith
  have hCeps : lmC a a₀ * lmEps a a₀ ≤ (1 - lmLam a a₀)/4 := by
    have hle := min_le_right (lmH a a₀/8) ((1 - lmLam a a₀)/(8*lmC a a₀))
    have h2' : lmC a a₀ * ((1 - lmLam a a₀)/(8*lmC a a₀)) = (1 - lmLam a a₀)/8 := by
      field_simp
    have h3' := mul_le_mul_of_nonneg_left hle (le_of_lt hCpos)
    simp only [lmEps] at h3' ⊢
    rw [h2'] at h3'
    linarith
  refine ⟨lmLam a a₀, lmC a a₀, lmEps a a₀, by simp, heps_pos, hCpos, hlam0, hlam1, hCeps, ?_, ?_⟩
  · intro ξ hξ
    have hb : |ξ| ≤ lmH a a₀ := le_trans hξ h4eps
    have hξle : ξ ≤ lmH a a₀ := le_trans (le_abs_self ξ) hb
    have hξge : -lmH a a₀ ≤ ξ := by have := neg_le_abs ξ; linarith
    have h2' : a₀ + ξ < a/2 := by
      have hh1 : lmH a a₀ ≤ lmS a a₀/16 := lmH_le_lmS a a₀
      have : a₀ + ξ ≤ a₀ + lmH a a₀ := by linarith
      have hfin : a₀ + lmS a a₀/16 < a/2 := by simp only [lmS]; linarith
      linarith
    have h1' : -1 - a/2 < a₀ + ξ := by
      have hh1 : lmH a a₀ ≤ lmT a a₀/16 := lmH_le_lmT a a₀
      have : a₀ - lmH a a₀ ≤ a₀ + ξ := by linarith
      have hfin : -1 - a/2 < a₀ - lmT a a₀/16 := by simp only [lmT]; linarith
      linarith
    have hax := lmAxisFixed h1' h2'
    have hAs : ((a₀ : ℝ) : ℂ) + (ξ : ℂ) = ((a₀ + ξ : ℝ) : ℂ) := by push_cast; ring
    rw [hAs, hax]
  · refine ⟨lmF a a₀, lmG a a₀, ?_, ?_, ?_, ?_, ?_⟩
    · intro ξ η hξ hη
      exact eqT_rep a a₀ ξ η
    · intro ξ η hξ hη
      have hb : lmBox a a₀ ξ η := ⟨le_trans hξ h4eps, le_trans hη h4eps⟩
      exact le_trans (lmF_bound hD hb)
        (mul_le_mul_of_nonneg_right (lmMPhi_le_lmC a a₀) (sq_nonneg η))
    · intro ξ η hξ hη
      have hb : lmBox a a₀ ξ η := ⟨le_trans hξ h4eps, le_trans hη h4eps⟩
      exact le_trans (lmG_bound hD hb)
        (mul_le_mul_of_nonneg_right (lmKG_le_lmC a a₀) (by positivity))
    · intro ξ η ξ' η' hξ hη hξ' hη'
      have hb : lmBox a a₀ ξ η := ⟨le_trans hξ h4eps, le_trans hη h4eps⟩
      have hb' : lmBox a a₀ ξ' η' := ⟨le_trans hξ' h4eps, le_trans hη' h4eps⟩
      exact le_trans (lmF_lip hD hb hb')
        (mul_le_mul_of_nonneg_right (lmKF_le_lmC a a₀) (by positivity))
    · intro ξ η ξ' η' hξ hη hξ' hη'
      have hb : lmBox a a₀ ξ η := ⟨le_trans hξ h4eps, le_trans hη h4eps⟩
      have hb' : lmBox a a₀ ξ' η' := ⟨le_trans hξ' h4eps, le_trans hη' h4eps⟩
      exact le_trans (lmG_lip hD hb hb')
        (mul_le_mul_of_nonneg_right (lmKG_le_lmC a a₀) (by positivity))

end Assembly

end Bounds

end

end Work.EQ
