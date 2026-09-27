import Mathlib
import Submission.Work.Mostow.nearId_blk

namespace Work.Mostow

/-- If a linear isometry of `E m` acts on each two-dimensional block of an orthonormal basis
`e : OrthonormalBasis (Fin (m/2) × Fin 2) ℝ (E m)` by the rotation of angle `φ i`, and all the
angles `φ i` are `0` in `AddCircle (2 * π)`, then the isometry is the identity. -/
theorem eqOneOfPhiEqZero (m : ℕ) (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (c : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      c (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (h0 : ∀ i, φ i = 0) : c = 1 := by
  classical
  -- Every block rotation angle is congruent to `0` mod `2π`, hence has `cos = 1`, `sin = 0`,
  -- and so the rotation is the identity on its block.
  have hblock' : ∀ i (x y : ℝ), c (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
      x • e (i, Fin.castSucc 0) + y • e (i, 1) := by
    intro i x y
    obtain ⟨t, ht, htx⟩ := hblock i x y
    have ht0 : (t : AddCircle (2 * Real.pi)) = 0 := by rw [ht, h0 i]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp ht0
    have hc : Real.cos t = 1 := by
      rw [← hn, zsmul_eq_mul]; exact Real.cos_int_mul_two_pi n
    have hs : Real.sin t = 0 := by
      rw [← hn, zsmul_eq_mul]
      have h2 : (↑n * (2 * Real.pi)) = (↑(2 * n) * Real.pi) := by push_cast; ring
      rw [h2, Real.sin_int_mul_pi]
    rw [htx, hc, hs]
    simp
  -- In particular `c` fixes the two basis vectors of every block.
  have hfix0 : ∀ i0 : Fin (m / 2), c (e (i0, Fin.castSucc 0)) = e (i0, Fin.castSucc 0) :=
    fun i0 => by simpa using hblock' i0 1 0
  have hfix1 : ∀ i0 : Fin (m / 2), c (e (i0, 1)) = e (i0, 1) :=
    fun i0 => by simpa using hblock' i0 0 1
  -- `Fin 2` has exactly the two elements `Fin.castSucc 0` and `1`.
  have hfix : ∀ j : Fin (m / 2) × Fin 2, c (e j) = e j := fun j => by
    obtain ⟨i0, k⟩ := j
    have hk : k = Fin.castSucc 0 ∨ k = 1 := by fin_cases k <;> decide
    rcases hk with hk | hk
    · rw [hk]; exact hfix0 i0
    · rw [hk]; exact hfix1 i0
  -- Two linear maps agreeing on a basis are equal.
  apply LinearIsometryEquiv.ext
  intro v
  rw [← e.sum_repr v]
  simp only [map_sum, map_smul, hfix]
  simp

end Work.Mostow
