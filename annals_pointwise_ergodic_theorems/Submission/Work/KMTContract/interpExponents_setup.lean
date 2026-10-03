import Mathlib

namespace Work.KMTContract

/-- **The choice of the auxiliary exponents for the interpolation step of the composition.**
Given `x, y ∈ (0,1)` with `x + y ≤ 1` (the latter is `p₁⁻¹ + p₂⁻¹ ≤ 1` for the exponents of
Theorem 1.17), there is a small `ε > 0` such that the perturbed exponents

`x' = x + ε(x - 1/2)`,  `y' = y + ε(y - 1/2)`

still lie in `(0,1)`, satisfy `x' + y' ≤ 1`, and satisfy the exact interpolation identities with
`θ = 1/(1+ε)`:

`x = (1-θ)/2 + θ x'`,  `y = (1-θ)/2 + θ y'`,  `x + y = (1-θ) + θ(x' + y')`.

(The perturbation moves `x` *away* from the critical value `1/2`; it also guarantees that
`x' ≠ 1/2` whenever `x ≠ 1/2`, which is what keeps the two endpoint exponents `a₁ = 1/x'`,
`b₁ = 1/y'` away from the excluded value `2`. A suitable choice is
`ε = min(min x (1-x)) (min y (1-y)) / 2`.) -/
theorem interpExponents_setup {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : x + y ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < 1 / (1 + ε) ∧ 1 / (1 + ε) < 1 ∧
      0 < x + ε * (x - 1 / 2) ∧ x + ε * (x - 1 / 2) < 1 ∧
      0 < y + ε * (y - 1 / 2) ∧ y + ε * (y - 1 / 2) < 1 ∧
      (x + ε * (x - 1 / 2)) + (y + ε * (y - 1 / 2)) ≤ 1 ∧
      x = (1 - 1 / (1 + ε)) / 2 + 1 / (1 + ε) * (x + ε * (x - 1 / 2)) ∧
      y = (1 - 1 / (1 + ε)) / 2 + 1 / (1 + ε) * (y + ε * (y - 1 / 2)) ∧
      x + y = (1 - 1 / (1 + ε))
        + 1 / (1 + ε) * ((x + ε * (x - 1 / 2)) + (y + ε * (y - 1 / 2))) := by
  -- The perturbation `ε = min(min x (1-x)) (min y (1-y)) / 2` moves `x` and `y` *away* from
  -- the critical value `1/2` while keeping the pair inside the triangle `(0,1)² ∩ {x+y ≤ 1}`.
  set M : ℝ := min (min x (1 - x)) (min y (1 - y)) with hM
  set ε : ℝ := M / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    have : 0 < M := by
      rw [hM]
      exact lt_min (lt_min hx0 (by linarith)) (lt_min hy0 (by linarith))
    linarith
  -- the four defining bounds of `M`, hence the four bounds `2ε ≤ ⋯`
  have hMx : M ≤ x := by rw [hM]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hM1x : M ≤ 1 - x := by rw [hM]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hMy : M ≤ y := by rw [hM]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hM1y : M ≤ 1 - y := by rw [hM]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have h2εx : 2 * ε ≤ x := by rw [hε]; linarith
  have h2ε1x : 2 * ε ≤ 1 - x := by rw [hε]; linarith
  have h2εy : 2 * ε ≤ y := by rw [hε]; linarith
  have h2ε1y : 2 * ε ≤ 1 - y := by rw [hε]; linarith
  refine ⟨ε, hεpos, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `θ = 1/(1+ε) < 1` since `ε > 0`
    rw [div_lt_one (by linarith : (0:ℝ) < 1 + ε)]; linarith
  · -- `x' > 0`: the perturbation is at worst `-ε/2 ≥ -x/4`
    have h : ε * (-(1/2)) ≤ ε * (x - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hεpos)
    nlinarith [h, h2εx, hx0]
  · -- `x' < 1`: the perturbation is at most `ε/2 ≤ (1-x)/4`
    have h : ε * (x - 1 / 2) ≤ ε * (1/2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hεpos)
    nlinarith [h, h2ε1x, hx1]
  · have h : ε * (-(1/2)) ≤ ε * (y - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hεpos)
    nlinarith [h, h2εy, hy0]
  · have h : ε * (y - 1 / 2) ≤ ε * (1/2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hεpos)
    nlinarith [h, h2ε1y, hy1]
  · -- `x' + y' = x + y + ε(x + y - 1) ≤ x + y ≤ 1`
    have h : ε * ((x - 1 / 2) + (y - 1 / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hεpos) (by linarith)
    nlinarith [h, hxy]
  · -- exact interpolation identity for `x`
    field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

end Work.KMTContract
