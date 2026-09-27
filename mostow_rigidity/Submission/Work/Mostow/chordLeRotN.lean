import Mathlib
import Submission.Work.Mostow.rescaledPoint
import Submission.Work.Mostow.chord_sq_eq

/-!
# The chord of a block angle is at most the operator distance of the rotation to the identity

If a linear isometry `R` of `E m` acts on the `i`-th two-dimensional block
`span {e (i,0), e (i,1)}` of an orthonormal basis as the rotation by the circular angle `φ i`,
then the chord length `chord (φ i) = 2 sin (‖φ i‖ / 2)` of that angle is bounded by the operator
norm `rotN R = ‖R - id‖` of the distance of `R` to the identity.

The proof is a one-line computation on the first basis vector `u = e (i, 0)` of the block:
`R u = cos (φ i) • u + sin (φ i) • e (i,1)`, so
`‖R u - u‖² = ‖R u‖² - 2 ⟪R u, u⟫ + ‖u‖² = 1 - 2 cos (φ i) + 1 = 2 - 2 cos (φ i) = chord (φ i)²`,
while `‖R u - u‖ ≤ ‖R - id‖ ‖u‖ = rotN R` because `u` is a unit vector.
-/

namespace Work.Mostow

open Submission.Mostow

theorem chordLeRotN (m : ℕ) (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1)) :
    ∀ i, Submission.Mostow.chord (φ i) ≤ Submission.Mostow.rotN R := by
  intro i
  -- Step 1: the block hypothesis, with `cos` and `sin` read on the circle `ℝ/2πℤ`
  have hblock' : ∀ (j : Fin (m / 2)) (x y : ℝ),
      R (x • e (j, Fin.castSucc 0) + y • e (j, 1)) =
        (Real.Angle.cos (φ j) * x - Real.Angle.sin (φ j) * y) • e (j, Fin.castSucc 0) +
          (Real.Angle.sin (φ j) * x + Real.Angle.cos (φ j) * y) • e (j, 1) := by
    intro j x y
    obtain ⟨t, ht, hR⟩ := hblock j x y
    have hcos : Real.cos t = Real.Angle.cos (φ j) := by
      rw [← ht]; exact (Real.Angle.cos_coe t).symm
    have hsin : Real.sin t = Real.Angle.sin (φ j) := by
      rw [← ht]; exact (Real.Angle.sin_coe t).symm
    rw [hcos, hsin] at hR
    exact hR
  -- Step 2: the image of the first basis vector of the `i`-th block
  have hR0 : R (e (i, Fin.castSucc 0)) =
      Real.Angle.cos (φ i) • e (i, Fin.castSucc 0) + Real.Angle.sin (φ i) • e (i, 1) := by
    have h := hblock' i 1 0
    simpa using h
  -- Step 3: orthonormality of the two vectors of the block
  have hu : ‖e (i, Fin.castSucc 0)‖ = 1 := e.norm_eq_one _
  have hne : (i, Fin.castSucc (0 : Fin 1)) ≠ (i, 1) := by
    intro h
    have h2 : Fin.castSucc (0 : Fin 1) = (1 : Fin 2) :=
      congrArg (fun p : Fin (m / 2) × Fin 2 => p.2) h
    exact absurd h2 (by decide)
  have hwu : inner ℝ (e (i, 1)) (e (i, Fin.castSucc 0)) = 0 := by
    rw [e.inner_eq_ite]
    simp
  -- Step 4: the norm of the displacement of the basis vector
  have hn2 : ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ ^ 2
      = 2 - 2 * Real.Angle.cos (φ i) := by
    rw [norm_sub_sq_real]
    have hnorm : ‖R (e (i, Fin.castSucc 0))‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, hu]
    have hinner : inner ℝ (R (e (i, Fin.castSucc 0))) (e (i, Fin.castSucc 0))
        = Real.Angle.cos (φ i) := by
      rw [hR0, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      rw [real_inner_self_eq_norm_sq, hu, hwu]
      ring
    rw [hnorm, hinner, hu]
    ring
  -- Step 5: the chord is the displacement
  have hchord_nonneg : 0 ≤ Submission.Mostow.chord (φ i) := by
    have hnormle : ‖φ i‖ ≤ Real.pi := by
      have h := AddCircle.norm_le_half_period (p := 2 * Real.pi) (x := φ i) (by positivity)
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
      linarith
    have hs : 0 ≤ Real.sin (‖φ i‖ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    rw [Submission.Mostow.chord]
    nlinarith
  have hchord_sq : (Submission.Mostow.chord (φ i)) ^ 2 = 2 - 2 * Real.Angle.cos (φ i) := by
    rw [Submission.Mostow.chord]
    exact chord_sq_eq (φ i)
  have hsq : (Submission.Mostow.chord (φ i)) ^ 2
      = ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ ^ 2 :=
    hchord_sq.trans hn2.symm
  have heq : Submission.Mostow.chord (φ i)
      = ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have h2 : 0 ≤ ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ := norm_nonneg _
      linarith [hchord_nonneg, h2, h]
  -- Step 6: the displacement is bounded by the operator norm
  have hop : ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ ≤ Submission.Mostow.rotN R := by
    change ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖ ≤
      ‖(R.toLinearIsometry.toContinuousLinearMap : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
        - ContinuousLinearMap.id ℝ (Submission.Mostow.E m)‖
    have hsub : ((R.toLinearIsometry.toContinuousLinearMap : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
        - ContinuousLinearMap.id ℝ (Submission.Mostow.E m)) (e (i, Fin.castSucc 0))
        = R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0) := rfl
    calc ‖R (e (i, Fin.castSucc 0)) - e (i, Fin.castSucc 0)‖
        = ‖((R.toLinearIsometry.toContinuousLinearMap : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
            - ContinuousLinearMap.id ℝ (Submission.Mostow.E m)) (e (i, Fin.castSucc 0))‖ := by
          rw [hsub]
      _ ≤ ‖(R.toLinearIsometry.toContinuousLinearMap : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
            - ContinuousLinearMap.id ℝ (Submission.Mostow.E m)‖ * ‖e (i, Fin.castSucc 0)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(R.toLinearIsometry.toContinuousLinearMap : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
            - ContinuousLinearMap.id ℝ (Submission.Mostow.E m)‖ := by rw [hu, mul_one]
  rw [heq]
  exact hop

end Work.Mostow
