import Mathlib

/-!
# An orthogonal non-zero direction

In `EuclideanSpace ℝ (Fin n)` with `n ≥ 2`, every non-zero vector has a non-zero orthogonal
vector.  This is the `finrank ≥ 2` input of the transverse step of the ray construction.

The proof is explicit: if `v.ofLp i ≠ 0` and `j ≠ i`, then `w := v j • e i - v i • e j` is
orthogonal to `v` (the two inner products cancel) and has `j`-th coordinate `-v i ≠ 0`, so `w ≠ 0`.

API notes: `EuclideanSpace` is a `WithLp`-wrapper, so `PiLp.ext` (not `funext`) is the
extensionality principle, coordinates are read with `.ofLp`,
`EuclideanSpace.single_apply` computes them, and `EuclideanSpace.inner_single_left` computes the
inner product against a standard basis vector.
-/

open scoped RealInnerProductSpace

namespace Work.Noncompact.ProperLine

/-- In `EuclideanSpace ℝ (Fin n)` with `n ≥ 2`, a non-zero vector has a non-zero orthogonal
vector. -/
theorem exists_ne_zero_inner_eq_zero {n : ℕ} (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 ∧ inner ℝ w v = 0 := by
  classical
  have hne : ∃ i : Fin n, v.ofLp i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (PiLp.ext fun i => by simp [h i])
  obtain ⟨i, hi⟩ := hne
  have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  refine ⟨(v.ofLp j) • EuclideanSpace.single i (1 : ℝ)
      - (v.ofLp i) • EuclideanSpace.single j (1 : ℝ), ?_, ?_⟩
  · intro hzero
    have hj : ((v.ofLp j) • EuclideanSpace.single i (1 : ℝ)
        - (v.ofLp i) • EuclideanSpace.single j (1 : ℝ)).ofLp j = 0 := by
      rw [hzero]; rfl
    rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.smul_apply,
      PiLp.single_apply, PiLp.single_apply,
      if_neg hij, if_pos rfl] at hj
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero] at hj
    exact hi (by linarith)
  · rw [inner_sub_left, inner_smul_left, inner_smul_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp [mul_comm]

end Work.Noncompact.ProperLine
