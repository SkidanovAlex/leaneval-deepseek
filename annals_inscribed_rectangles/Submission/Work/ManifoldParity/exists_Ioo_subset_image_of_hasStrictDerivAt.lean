import Mathlib

/-!
# A strictly differentiable map with nonzero derivative is locally surjective

If `ℓ : ℝ → ℝ` has a strict derivative `c ≠ 0` at `t₀`, then `ℓ` maps a neighborhood
of `t₀` onto a neighborhood of `ℓ t₀`: for every `ε > 0` there is `δ > 0` with
`Ioo (ℓ t₀ - δ) (ℓ t₀ + δ) ⊆ ℓ '' Ioo (t₀ - ε) (t₀ + ε)`.

This is the one-dimensional inverse function theorem in the form used by the
mod-2 intersection-counting development: an essential arc through a transverse
zero of the defining function can be pushed to a locally surjective chart.
The proof rests on `HasStrictDerivAt.map_nhds_eq`, which states that a strict
derivative with nonzero value is an open map at the point: `map ℓ (𝓝 t₀) = 𝓝 (ℓ t₀)`.
-/

namespace Work.ManifoldParity

open Filter
open scoped Topology

theorem exists_Ioo_subset_image_of_hasStrictDerivAt {ℓ : ℝ → ℝ} {t₀ c : ℝ}
    (hd : HasStrictDerivAt ℓ c t₀) (hc : c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, Set.Ioo (ℓ t₀ - δ) (ℓ t₀ + δ) ⊆ ℓ '' Set.Ioo (t₀ - ε) (t₀ + ε) := by
  -- The interval `(t₀ - ε, t₀ + ε)` is a neighborhood of `t₀`.
  have hU : Set.Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  -- Push it forward: `map ℓ (𝓝 t₀) = 𝓝 (ℓ t₀)` and `(t₀ - ε, t₀ + ε)` is a neighborhood
  -- of `t₀`, hence its image is a neighborhood of `ℓ t₀`.
  have himage : ℓ '' Set.Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 (ℓ t₀) := by
    rw [← hd.map_nhds_eq hc, Filter.mem_map]
    exact mem_of_superset hU (Set.subset_preimage_image _ _)
  -- `Ioo (ℓ t₀ - δ) (ℓ t₀ + δ)` is a neighborhood basis of `ℓ t₀`.
  obtain ⟨δ, hδ, hsub⟩ := (nhds_basis_Ioo_pos (ℓ t₀)).mem_iff.mp himage
  exact ⟨δ, hδ, hsub⟩

end Work.ManifoldParity
