import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Geometry.Convex.Hadwiger.interior_empty_iff_affineSpan_ne_top
import Submission.Commons.Geometry.Convex.Hadwiger.exists_lie_unit_to_unit

namespace Commons.Geometry.Convex.Hadwiger

open scoped Classical

/-- A convex body in `ℝⁿ` (`n > 0`) with empty interior is contained in an affine hyperplane:
there is a linear isometry `e` and a translation `t` such that `e K + t` lies in the coordinate
hyperplane `{y | y 0 = 0}`.  Equivalently, `K` is not full-dimensional, so it lies in a level set
of some nonzero linear functional, and that functional can be rotated onto the first coordinate. -/
theorem exists_isometry_add_subset_hyperplane (n : ℕ) (hn : 0 < n)
    (K : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hK : interior (K : Set (EuclideanSpace ℝ (Fin n))) = ∅) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), ∃ t : EuclideanSpace ℝ (Fin n),
      ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin n))), (e x + t) ⟨0, hn⟩ = 0 := by
  let E : Type := EuclideanSpace ℝ (Fin n)
  -- `K` is nonempty and not full-dimensional.
  have hne : (K : Set E).Nonempty := K.nonempty
  have haff : affineSpan ℝ (K : Set E) ≠ ⊤ :=
    (interior_empty_iff_affineSpan_ne_top K).mp hK
  have hW : vectorSpan ℝ (K : Set E) ≠ ⊤ := by
    intro h
    exact haff ((AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hne).mpr h)
  -- Pick a nonzero vector `nv` orthogonal to the direction of `K`.
  obtain ⟨nv, hnv_mem, hnv_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (p := (vectorSpan ℝ (K : Set E))ᗮ) (by
      intro hbot
      exact hW ((Submodule.orthogonal_eq_bot_iff).mp hbot))
  have hnv_orth : ∀ w ∈ vectorSpan ℝ (K : Set E), inner ℝ w nv = 0 := by
    intro w hw
    exact (Submodule.mem_orthogonal _ nv).mp hnv_mem w hw
  -- Hence `x ↦ ⟪x, nv⟫` is constant on `K`.
  obtain ⟨x0, hx0⟩ := hne
  have hconst : ∀ x ∈ (K : Set E), inner ℝ x nv = inner ℝ x0 nv := by
    intro x hx
    have hmem : x - x0 ∈ vectorSpan ℝ (K : Set E) := by
      simpa using vsub_mem_vectorSpan ℝ hx hx0
    have h0 : inner ℝ (x - x0) nv = 0 := hnv_orth (x - x0) hmem
    rw [inner_sub_left] at h0
    linarith
  -- Normalise `nv` to a unit vector `u`.
  let u : E := ‖nv‖⁻¹ • nv
  have hu : ‖u‖ = 1 := by
    have hnv_norm_ne : ‖nv‖ ≠ 0 := norm_ne_zero_iff.mpr hnv_ne
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg nv)]
    exact inv_mul_cancel₀ hnv_norm_ne
  -- The coordinate functional is `extracted` by pairing with `v = single 0 1`.
  let v : E := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)
  have hvv : inner ℝ v v = 1 := by
    rw [show v = EuclideanSpace.single ⟨0, hn⟩ (1:ℝ) from rfl]
    rw [EuclideanSpace.inner_single_left, PiLp.single_eq_same, map_one, one_mul]
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hvv]
    nlinarith [norm_nonneg v]
  have hv_ne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv_norm
    exact one_ne_zero hv_norm.symm
  -- Rotate `u` onto `v`.
  obtain ⟨ρ, hρ⟩ := exists_lie_unit_to_unit (V := E) u hu v hv_ne
  have hρ' : ρ u = v := by
    rw [hρ, hv_norm, inv_one, one_smul]
  let c' : ℝ := ‖nv‖⁻¹ * inner ℝ x0 nv
  have hu_const : ∀ x ∈ (K : Set E), inner ℝ u x = c' := by
    intro x hx
    rw [← real_inner_comm u x]
    simp only [u, c', inner_smul_right]
    rw [hconst x hx]
  -- Translate along `v` to put the level set at coordinate zero.
  let t : E := (-c') • v
  refine ⟨ρ, t, ?_⟩
  intro x hx
  have hinner : ∀ y : E, inner ℝ v y = y ⟨0, hn⟩ := by
    intro y
    have h1 := EuclideanSpace.inner_single_left ⟨0, hn⟩ (1:ℝ) y
    simpa [v] using h1
  rw [← hinner (ρ x + t), inner_add_right]
  have hmain : inner ℝ v (ρ x) = inner ℝ u x := by
    have hmap := LinearIsometryEquiv.inner_map_map ρ (ρ.symm v) x
    rw [ρ.apply_symm_apply] at hmap
    have hsymm : ρ.symm v = u := by
      rw [← hρ', LinearIsometryEquiv.symm_apply_apply]
    rw [hsymm] at hmap
    exact hmap
  have h2 : inner ℝ v t = -c' := by
    simp only [t, inner_smul_right]
    rw [hvv]
    ring
  rw [hmain, h2, hu_const x hx]
  ring

end Commons.Geometry.Convex.Hadwiger