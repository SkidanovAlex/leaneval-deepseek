import Mathlib
import Submission.Work.KT.Fund.SpectralAux

namespace Work.KT.Fund

/-- With `P = Proj b ρ` the idempotent spectral projection and `Y = Out b ρ` the "outside
inverse", the relations `b * Y = Y * b = 1 - P` force `P` to commute with `b` (and `Y`),
and then `(1 - P) * b + P` is a unit with inverse `(1 - P) * Y + P`. -/
theorem spectral_unit_d {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (hbY : b * Out b ρ = 1 - Proj b ρ) (hYb : Out b ρ * b = 1 - Proj b ρ)
    (hidem : Proj b ρ * Proj b ρ = Proj b ρ) :
    IsUnit ((1 - Proj b ρ) * b + Proj b ρ) := by
  set P := Proj b ρ with hPdef
  set Y := Out b ρ with hYdef
  have hbY' : b * Y = 1 - P := hbY
  have hYb' : Y * b = 1 - P := hYb
  have hPP : P * P = P := hidem
  set e := 1 - P with hedef
  -- If `a * t = t * a = c` then `a * c = c * a`.
  have key : ∀ (a t c : A), a * t = c → t * a = c → a * c = c * a := by
    intro a t c hat hta
    calc a * c = a * (t * a) := by rw [hta]
      _ = (a * t) * a := by rw [mul_assoc]
      _ = c * a := by rw [hat]
  have hbYe : b * Y = e := hbY'
  have hYbe : Y * b = e := hYb'
  have hbe : b * e = e * b := key b Y e hbYe hYbe
  have hYe : Y * e = e * Y := key Y b e hYbe hbYe
  have heP : e * P = 0 := by
    rw [hedef]
    have h : (1 - P) * P = P - P * P := by noncomm_ring
    rw [h, hPP]
    abel
  have hPe : P * e = 0 := by
    rw [hedef]
    have h : P * (1 - P) = P - P * P := by noncomm_ring
    rw [h, hPP]
    abel
  have hee : e * e = e := by
    rw [hedef]
    have h : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [h, hPP]
    abel
  have hone : (1 : A) - e = P := by
    rw [hedef]; abel
  have heP1 : e + P = 1 := by
    rw [hedef]; abel
  have hPb : P * b = b * P := by
    calc P * b = ((1 : A) - e) * b := by rw [hone]
      _ = b - e * b := by noncomm_ring
      _ = b - b * e := by rw [← hbe]
      _ = b * ((1 : A) - e) := by noncomm_ring
      _ = b * P := by rw [hone]
  have hPY : Y * P = P * Y := by
    calc Y * P = Y * ((1 : A) - e) := by rw [hone]
      _ = Y - Y * e := by noncomm_ring
      _ = Y - e * Y := by rw [hYe]
      _ = ((1 : A) - e) * Y := by noncomm_ring
      _ = P * Y := by rw [hone]
  have hxw : (e * b + P) * (e * Y + P) = 1 := by
    have ex : (e * b + P) * (e * Y + P)
        = e * b * e * Y + e * b * P + P * e * Y + P * P := by noncomm_ring
    rw [ex]
    have t1 : e * b * e * Y = e := by
      calc e * b * e * Y = e * (b * e) * Y := by rw [mul_assoc e b e]
        _ = e * (e * b) * Y := by rw [hbe]
        _ = (e * e) * b * Y := by rw [← mul_assoc e e b]
        _ = e * b * Y := by rw [hee]
        _ = e * (b * Y) := by rw [mul_assoc e b Y]
        _ = e * e := by rw [hbYe]
        _ = e := hee
    have t2 : e * b * P = 0 := by
      calc e * b * P = e * (b * P) := by rw [mul_assoc e b P]
        _ = e * (P * b) := by rw [hPb]
        _ = (e * P) * b := by rw [← mul_assoc e P b]
        _ = 0 := by rw [heP, zero_mul]
    have t3 : P * e * Y = 0 := by rw [hPe, zero_mul]
    rw [t1, t2, t3, hPP]
    simpa using heP1
  have hwx : (e * Y + P) * (e * b + P) = 1 := by
    have ex : (e * Y + P) * (e * b + P)
        = e * Y * e * b + e * Y * P + P * e * b + P * P := by noncomm_ring
    rw [ex]
    have t1 : e * Y * e * b = e := by
      calc e * Y * e * b = e * (Y * e) * b := by rw [mul_assoc e Y e]
        _ = e * (e * Y) * b := by rw [hYe]
        _ = (e * e) * Y * b := by rw [← mul_assoc e e Y]
        _ = e * Y * b := by rw [hee]
        _ = e * (Y * b) := by rw [mul_assoc e Y b]
        _ = e * e := by rw [hYbe]
        _ = e := hee
    have t2 : e * Y * P = 0 := by
      calc e * Y * P = e * (Y * P) := by rw [mul_assoc e Y P]
        _ = e * (P * Y) := by rw [hPY]
        _ = (e * P) * Y := by rw [← mul_assoc e P Y]
        _ = 0 := by rw [heP, zero_mul]
    have t3 : P * e * b = 0 := by rw [hPe, zero_mul]
    rw [t1, t2, t3, hPP]
    simpa using heP1
  exact ⟨⟨e * b + P, e * Y + P, hxw, hwx⟩, rfl⟩

end Work.KT.Fund
