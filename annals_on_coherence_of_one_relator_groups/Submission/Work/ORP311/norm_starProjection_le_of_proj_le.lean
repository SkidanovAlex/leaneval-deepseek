import Mathlib
import Submission.Work.ORP311.P311Defs

open scoped InnerProductSpace

namespace Work.ORP311

/-- If `V ≤ W`, and `W`'s orthogonal projection maps `K` into `V`, then for `v ∈ W` the
orthogonal projection of `v` onto `K` is no longer than onto `V`.

Write `p := K.starProjection v`, `v₀ := V.starProjection v` and `q := W.starProjection p`.
From `hKV` we get `q ∈ V`.  Since `p ∈ K` and `v - p ⊥ K` we have `⟪v, p⟫ = ‖p‖²`, and the
decompositions `p = q + (p - q)` (with `p - q ⊥ W`) and `v = v₀ + (v - v₀)` (with
`v - v₀ ⊥ V` and `v - v₀ ∈ W`) give `⟪v, p⟫ = ⟪v₀, q⟫`.  Taking real parts and applying
Cauchy–Schwarz plus `‖q‖ ≤ ‖p‖` yields `‖p‖² ≤ ‖p‖‖v₀‖`, whence `‖p‖ ≤ ‖v₀‖`. -/
theorem norm_starProjection_le_of_proj_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (K W V : Submodule ℂ E) [K.HasOrthogonalProjection] [W.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hVW : V ≤ W) (hKV : ∀ x ∈ K, W.starProjection x ∈ V) {v : E} (hv : v ∈ W) : ‖K.starProjection v‖ ≤ ‖V.starProjection v‖ := by
  set p := K.starProjection v with hpdef
  set v0 := V.starProjection v with hv0def
  set q := W.starProjection p with hqdef
  have hp : p ∈ K := K.starProjection_apply_mem v
  have hq : q ∈ V := hKV p hp
  have hqW : q ∈ W := hVW hq
  have hv0 : v0 ∈ V := V.starProjection_apply_mem v
  have hv0W : v0 ∈ W := hVW hv0
  have hpq_orth : p - q ∈ Wᗮ := W.sub_starProjection_mem_orthogonal p
  have hvv0_orth : v - v0 ∈ Vᗮ := V.sub_starProjection_mem_orthogonal v
  have hvv0_W : v - v0 ∈ W := W.sub_mem hv hv0W
  have hpdecomp : p = q + (p - q) := by abel
  have hvdecomp : v = v0 + (v - v0) := by abel
  have h1 : ⟪p, v - v0⟫_ℂ = 0 := by
    rw [hpdecomp, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal hq hvv0_orth,
      Submodule.inner_left_of_mem_orthogonal hvv0_W hpq_orth, add_zero]
  have h2 : ⟪p, v0⟫_ℂ = ⟪q, v0⟫_ℂ := by
    rw [hpdecomp, inner_add_left, Submodule.inner_left_of_mem_orthogonal hv0W hpq_orth, add_zero]
  have hmain : ⟪p, v⟫_ℂ = ⟪q, v0⟫_ℂ := by
    rw [hvdecomp, inner_add_right, h2, h1, add_zero]
  have hpp : ⟪v, p⟫_ℂ = ⟪p, p⟫_ℂ := by
    have h := K.starProjection_inner_eq_zero v p hp
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have hre : RCLike.re ⟪p, v⟫_ℂ = ‖p‖ ^ 2 := by
    rw [inner_re_symm, hpp, inner_self_eq_norm_sq]
  have hle : ‖p‖ ^ 2 ≤ ‖p‖ * ‖v0‖ := by
    calc ‖p‖ ^ 2 = RCLike.re ⟪q, v0⟫_ℂ := by rw [← hre, hmain]
      _ ≤ ‖q‖ * ‖v0‖ := re_inner_le_norm q v0
      _ ≤ ‖p‖ * ‖v0‖ := mul_le_mul_of_nonneg_right (W.norm_starProjection_apply_le p) (norm_nonneg v0)
  rcases eq_or_lt_of_le (norm_nonneg p) with h0 | hpos
  · rw [← h0]; exact norm_nonneg v0
  · have hle' : ‖p‖ * ‖p‖ ≤ ‖p‖ * ‖v0‖ := by rw [pow_two] at hle; exact hle
    exact le_of_mul_le_mul_left hle' hpos

end Work.ORP311
