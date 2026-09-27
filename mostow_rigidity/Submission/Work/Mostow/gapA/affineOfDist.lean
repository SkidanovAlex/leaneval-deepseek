import Mathlib

namespace Work.Mostow.gapA

theorem affineOfDist {φ : ℝ → ℝ} {ℓ : ℝ}
    (h : ∀ s t : ℝ, |φ s - φ t| = |s - t|) (h' : ∀ s : ℝ, |φ s - s| = ℓ) :
    ∃ c : ℝ, |c| = ℓ ∧ ∀ s : ℝ, φ s = c + s := by
  -- Squared form of the isometry relation.
  have hsq : ∀ s t : ℝ, (φ s - φ t)^2 = (s - t)^2 := by
    intro s t
    rw [← sq_abs (φ s - φ t), ← sq_abs (s - t), h s t]
  -- Distance from φ 0, squared.
  have hψsq : ∀ s, (φ s - φ 0)^2 = s^2 := by
    intro s
    simpa using hsq s 0
  -- Polarization/product identity: (φ s - φ 0)(φ t - φ 0) = s t.
  have hmul : ∀ s t, (φ s - φ 0) * (φ t - φ 0) = s * t := by
    intro s t
    nlinarith [hsq s t, hψsq s, hψsq t]
  have hψ1 : (φ 1 - φ 0)^2 = 1 := by
    simpa using hψsq 1
  have hprod : ∀ s, (φ s - φ 0) * (φ 1 - φ 0) = s := by
    intro s
    simpa using hmul s 1
  have hbb : (φ 1 - φ 0) * (φ 1 - φ 0) = 1 := by
    simpa [pow_two] using hψ1
  -- φ is affine: φ s = φ 0 + s * (φ 1 - φ 0).
  have hlin : ∀ s, φ s - φ 0 = s * (φ 1 - φ 0) := by
    intro s
    calc φ s - φ 0 = (φ s - φ 0) * ((φ 1 - φ 0) * (φ 1 - φ 0)) := by rw [hbb, mul_one]
      _ = ((φ s - φ 0) * (φ 1 - φ 0)) * (φ 1 - φ 0) := by ring
      _ = s * (φ 1 - φ 0) := by rw [hprod s]
  have hphi : ∀ s, φ s = φ 0 + s * (φ 1 - φ 0) := by
    intro s
    linarith [hlin s]
  have h0 : |φ 0| = ℓ := by simpa using h' 0
  -- The displacement from the identity has constant modulus:
  have hsqL : ∀ s, (φ s - s)^2 = (φ 0)^2 := by
    intro s
    have h1 : |φ s - s| = |φ 0| := by rw [h' s, h0]
    calc (φ s - s)^2 = |φ s - s|^2 := (sq_abs _).symm
      _ = |φ 0|^2 := by rw [h1]
      _ = (φ 0)^2 := sq_abs _
  have hpol : ∀ s, (φ 0 + s * (φ 1 - φ 0) - s)^2 = (φ 0)^2 := by
    intro s
    have := hsqL s
    rw [hphi s] at this
    exact this
  -- Two evaluations in `s` force the slope φ 1 - φ 0 to be 1, i.e. φ is a translation.
  have hv : (φ 1 - φ 0 - 1)^2 = 0 := by nlinarith [hpol 1, hpol 2]
  have hb : φ 1 - φ 0 = 1 := by
    have := sq_eq_zero_iff.mp hv
    linarith
  refine ⟨φ 0, h0, ?_⟩
  intro s
  rw [hphi s, hb, mul_one]

end Work.Mostow.gapA
