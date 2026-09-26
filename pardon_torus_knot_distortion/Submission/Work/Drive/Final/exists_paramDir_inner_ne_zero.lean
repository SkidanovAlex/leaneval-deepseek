import Mathlib

namespace Work.Drive.Final

/-- If `d : ℝ² → ℝ³` is injective and the (nonzero) linear functional `ℓ` vanishes on
`range d`, then every nonzero `v` in `ker ℓ` has a nonzero inner product with some value of `d`.
Indeed `range d` and `ker ℓ` are both 2-dimensional subspaces of `ℝ³`, hence equal, so
`v = d w` for some `w` and `⟪v, d w⟫ = ⟪v, v⟫ ≠ 0`. -/
theorem exists_paramDir_inner_ne_zero
    (d : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (hd : Function.Injective d)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (hℓ : ℓ ≠ 0) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hker : ∀ w : ℝ × ℝ, ℓ (d w) = 0) :
    ∃ w : ℝ × ℝ, inner ℝ v (d w) ≠ 0 := by
  -- `range d ≤ ker ℓ`
  have hle : LinearMap.range d.toLinearMap ≤ LinearMap.ker ℓ.toLinearMap := by
    rintro x ⟨w, rfl⟩
    exact hker w
  -- `finrank (range d) = 2` since `d` is injective and `finrank ℝ² = 2`
  have h1 : Module.finrank ℝ (LinearMap.range d.toLinearMap) = 2 := by
    rw [LinearMap.finrank_range_of_inj hd, Module.finrank_prod, Module.finrank_self]
  -- `finrank (ker ℓ) = 2` since `ℓ ≠ 0` forces `range ℓ = ⊤`, so `finrank (range ℓ) = 1`
  have h2 : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 2 := by
    have hx : ∃ x, ℓ x ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hℓ (ContinuousLinearMap.ext h)
    obtain ⟨x, hx⟩ := hx
    have htop : LinearMap.range ℓ.toLinearMap = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨(y / ℓ x) • x, ?_⟩
      show ℓ ((y / ℓ x) • x) = y
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ y hx]
    have hfin : Module.finrank ℝ (LinearMap.range ℓ.toLinearMap) = 1 := by
      rw [htop, finrank_top, Module.finrank_self]
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
    have hsum := ℓ.toLinearMap.finrank_range_add_finrank_ker
    rw [hfin, hE] at hsum
    omega
  -- equal finite-dimensional subspaces of equal rank
  have hEq : LinearMap.range d.toLinearMap = LinearMap.ker ℓ.toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])
  -- hence `v ∈ range d`
  have hvker : v ∈ LinearMap.range d.toLinearMap := by
    rw [hEq]
    exact LinearMap.mem_ker.mpr hℓv
  obtain ⟨w, hw⟩ := hvker
  refine ⟨w, ?_⟩
  show inner ℝ v (d.toLinearMap w) ≠ 0
  rw [hw]
  exact inner_self_ne_zero.mpr hv

end Work.Drive.Final
