import Mathlib
import Submission.Work.EQ.LocModelDefs

/-!
# Bounds for the vertical multiplier `λ` of the local model

Setting: `O₁ = -a/2`, `O₂ = a/2`, and `A = a₀` a real base point with
`a/2 - 1 < a₀ < -a/2`, `0 < a < 1`.  The two distances from `A` to the foci are

* `s = lmS a a₀ = a/2 - a₀` (distance to `O₂`), and
* `t = lmT a a₀ = a₀ + 1 + a/2` (distance from the first image `A+1` to `O₁`),

and the vertical multiplier at `A` is `λ = (1 - 1/s)(1 - 1/t) = lmLam a a₀`.

Here we prove that this multiplier satisfies `0 < λ < 1`, and that it coincides with the
value of the vertical multiplier function `lmG` at the base point `(ξ,η) = (0,0)`:
`lmG a a₀ 0 0 = lmSig`/`lmTau` at `(0,0)` reduce to `s`/`t` respectively.
-/

namespace Work.EQ

open Complex

noncomputable section

/-- At the base point, `σ = ‖P - O₂‖` equals `s = lmS a a₀`. -/
lemma lmSig_zero_zero {a a₀ : ℝ} (hs : 0 < lmS a a₀) : lmSig a a₀ 0 0 = lmS a a₀ := by
  have h : lmU a a₀ 0 = -lmS a a₀ := by simp only [lmU, lmS]; ring
  rw [lmSig, h]
  rw [show (-lmS a a₀)^2 + 0^2 = (lmS a a₀)^2 by ring, Real.sqrt_sq hs.le]

/-- At the base point, `Y₁ = Im (chordMap O₂ P)` vanishes. -/
lemma lmY1_zero_zero (a a₀ : ℝ) : lmY1 a a₀ 0 0 = 0 := by
  rw [lmY1]; ring

/-- At the base point, `v = Re (chordMap O₂ P) - O₁` equals `t = lmT a a₀`. -/
lemma lmV_zero_zero {a a₀ : ℝ} (hs : 0 < lmS a a₀) : lmV a a₀ 0 0 = lmT a a₀ := by
  have hu : lmU a a₀ 0 = -lmS a a₀ := by simp only [lmU, lmS]; ring
  rw [lmV, lmX1, lmT]
  simp only [add_zero]
  rw [hu, lmSig_zero_zero hs]
  field_simp
  ring

/-- At the base point, `τ = ‖(v, Y₁)‖` equals `t = lmT a a₀`. -/
lemma lmTau_zero_zero {a a₀ : ℝ} (hs : 0 < lmS a a₀) (ht : 0 < lmT a a₀) :
    lmTau a a₀ 0 0 = lmT a a₀ := by
  rw [lmTau, lmV_zero_zero hs, lmY1_zero_zero]
  rw [show (lmT a a₀)^2 + (0:ℝ)^2 = (lmT a a₀)^2 by ring, Real.sqrt_sq ht.le]

/-- The vertical multiplier `lmLam` at the base point reads
`(1 - s)(1 - t)/(st)` with `s = lmS a a₀`, `t = lmT a a₀`. -/
lemma lmLam_eq {a a₀ : ℝ} (hs : 0 < lmS a a₀) (ht : 0 < lmT a a₀) :
    lmLam a a₀ = ((1 - lmS a a₀) * (1 - lmT a a₀)) / (lmS a a₀ * lmT a a₀) := by
  rw [lmLam]; field_simp; ring

theorem lmLamBounds {a a₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2)) :
    0 < Work.EQ.lmLam a a₀ ∧ Work.EQ.lmLam a a₀ < 1 ∧
    Work.EQ.lmLam a a₀ = Work.EQ.lmG a a₀ 0 0 := by
  have hs : 0 < lmS a a₀ := by simp only [lmS]; linarith
  have ht : 0 < lmT a a₀ := by simp only [lmT]; linarith
  have hs1 : lmS a a₀ < 1 := by simp only [lmS]; linarith
  have ht1 : lmT a a₀ < 1 := by simp only [lmT]; linarith
  have hst : lmS a a₀ + lmT a a₀ = 1 + a := by simp only [lmS, lmT]; ring
  have hsig : lmSig a a₀ 0 0 = lmS a a₀ := lmSig_zero_zero hs
  have htau : lmTau a a₀ 0 0 = lmT a a₀ := lmTau_zero_zero hs ht
  have hG : lmLam a a₀ = lmG a a₀ 0 0 := by
    simp only [lmG, lmG1, lmG2, lmLam, hsig, htau]
  have hstp : 0 < lmS a a₀ * lmT a a₀ := mul_pos hs ht
  refine ⟨?_, ?_, hG⟩
  · rw [lmLam_eq hs ht]
    exact div_pos (mul_pos (by linarith) (by linarith)) hstp
  · rw [lmLam_eq hs ht, div_lt_one hstp]
    nlinarith [hst]

end

end Work.EQ
