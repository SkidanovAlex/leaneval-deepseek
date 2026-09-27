import Mathlib

namespace Work.KT.EG.KLG

/-- For a field `𝕜`, a nonzero scalar times a unit matrix is a unit matrix. Here over `ℂ`. -/
lemma isUnit_smul_matrix {n : ℕ} (c : ℂ) (hc : c ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ)
    (hN : IsUnit N) : IsUnit (c • N) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hN ⊢
  rw [Matrix.det_smul]
  rw [isUnit_iff_ne_zero] at hN ⊢
  exact mul_ne_zero (pow_ne_zero _ hc) hN

/-- The Möbius-type scalar identity: for `1 + t*z ≠ 0`,
`z*(a + t*b) + t*a + b = (1 + t*z) * ((z+t)/(1+t*z) * a + b)`. -/
lemma mobius_scalar_identity (a b z t : ℂ) (h : 1 + t * z ≠ 0) :
    z * (a + t * b) + t * a + b = (1 + t * z) * ((z + t) / (1 + t * z) * a + b) := by
  have hscalar : (1 + t * z) * ((z + t) / (1 + t * z)) = z + t := by field_simp
  calc z * (a + t * b) + t * a + b
      = (z + t) * a + (1 + t * z) * b := by ring
    _ = (1 + t * z) * ((z + t) / (1 + t * z) * a + b) := by
          rw [mul_add, ← mul_assoc, hscalar]

/-- Matrix form of the Möbius identity: if `(z+t)/(1+t*z) • A + B` is a unit, then so is
`z • (A + t • B) + t • A + B`. -/
lemma isUnit_mobius {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (z t : ℂ)
    (htz : 1 + t * z ≠ 0)
    (h : IsUnit (((z + t) / (1 + t * z)) • A + B)) :
    IsUnit (z • (A + t • B) + t • A + B) := by
  have heq : z • (A + t • B) + t • A + B
      = (1 + t * z) • (((z + t) / (1 + t * z)) • A + B) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    exact mobius_scalar_identity (A i j) (B i j) z t htz
  rw [heq]
  exact isUnit_smul_matrix (1 + t * z) htz _ h

/-- Norm of a real number viewed as a complex number. -/
lemma norm_ofReal_complex (t : ℝ) : ‖(t : ℂ)‖ = |t| := by
  have h : ‖(t : ℂ)‖ ^ 2 = |t| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [norm_nonneg (t : ℂ), abs_nonneg t]

/-- For `‖z‖ = 1` and real `t`, the numerator and denominator of the Möbius map
`z ↦ (z + t)/(1 + t*z)` have equal `normSq`. -/
lemma normSq_mobius (z : ℂ) (t : ℝ) (hz : ‖z‖ = 1) :
    Complex.normSq (z + (t : ℂ)) = Complex.normSq (1 + (t : ℂ) * z) := by
  have hnz : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, hnz]; norm_num
  have hfac : z * (1 + (t : ℂ) * (starRingEnd ℂ) z) = z + (t : ℂ) := by
    calc z * (1 + (t : ℂ) * (starRingEnd ℂ) z)
        = z + (t : ℂ) * (z * (starRingEnd ℂ) z) := by ring
      _ = z + (t : ℂ) * 1 := by rw [hzz]
      _ = z + (t : ℂ) := by ring
  have hconj : 1 + (t : ℂ) * (starRingEnd ℂ) z = (starRingEnd ℂ) (1 + (t : ℂ) * z) := by
    simp only [map_add, map_mul, map_one, Complex.conj_ofReal]
  calc Complex.normSq (z + (t : ℂ))
      = Complex.normSq (z * (1 + (t : ℂ) * (starRingEnd ℂ) z)) := by rw [hfac]
    _ = Complex.normSq z * Complex.normSq (1 + (t : ℂ) * (starRingEnd ℂ) z) := by
          rw [Complex.normSq_mul]
    _ = Complex.normSq z * Complex.normSq ((starRingEnd ℂ) (1 + (t : ℂ) * z)) := by rw [hconj]
    _ = Complex.normSq ((starRingEnd ℂ) (1 + (t : ℂ) * z)) := by rw [hnz, one_mul]
    _ = Complex.normSq (1 + (t : ℂ) * z) := by rw [Complex.normSq_conj]

theorem isUnit_mobius_family (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (a b : Matrix (Fin n) (Fin n) C(X, ℂ)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hu : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (a.map (fun f => f x)) + b.map (fun f => f x)))
    (x : X) (z : ℂ) (hz : ‖z‖ = 1) :
    IsUnit (z • ((a + t • b).map (fun f => f x)) + t • (a.map (fun f => f x))
      + b.map (fun f => f x)) := by
  -- Evaluate the matrix of continuous functions pointwise at `x`.
  have hmap : (a + t • b).map (fun f => f x)
      = a.map (fun f => f x) + t • b.map (fun f => f x) := by
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
  -- Turn real scalar multiplications on `ℂ`-matrices into complex ones.
  have hrealA : t • a.map (fun f => f x) = (t : ℂ) • a.map (fun f => f x) := by
    ext i j
    simp [Matrix.smul_apply]
  have hrealB : t • b.map (fun f => f x) = (t : ℂ) • b.map (fun f => f x) := by
    ext i j
    simp [Matrix.smul_apply]
  -- The Möbius point never hits the pole.
  have htz : 1 + (t : ℂ) * z ≠ 0 := by
    intro hzero
    have h1 : (t : ℂ) * z = -1 := by linear_combination hzero
    have h2 : ‖(t : ℂ) * z‖ = 1 := by rw [h1]; norm_num
    rw [norm_mul, hz, mul_one] at h2
    have ht : ‖(t : ℂ)‖ = t := by rw [norm_ofReal_complex, abs_of_nonneg ht0]
    rw [ht] at h2
    linarith
  -- The Möbius point lies on the unit circle.
  have hζ : ‖(z + (t : ℂ)) / (1 + (t : ℂ) * z)‖ = 1 := by
    have hsq := normSq_mobius z t hz
    have hne : Complex.normSq (1 + (t : ℂ) * z) ≠ 0 :=
      fun h => htz (Complex.normSq_eq_zero.mp h)
    have hmain : Complex.normSq ((z + (t : ℂ)) / (1 + (t : ℂ) * z)) = 1 := by
      rw [Complex.normSq_div, hsq, div_self hne]
    rw [Complex.normSq_eq_norm_sq] at hmain
    nlinarith [norm_nonneg ((z + (t : ℂ)) / (1 + (t : ℂ) * z))]
  rw [hmap, hrealB, hrealA]
  exact isUnit_mobius _ _ z (t : ℂ) htz
    (hu x ((z + (t : ℂ)) / (1 + (t : ℂ) * z)) hζ)

end Work.KT.EG.KLG
