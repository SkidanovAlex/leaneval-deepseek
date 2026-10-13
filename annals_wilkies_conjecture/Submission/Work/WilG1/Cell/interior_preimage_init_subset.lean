import Mathlib

namespace Work.WilG1.Cell

/-- The inclusion `interior (init ⁻¹' T) ⊆ init ⁻¹' interior T`, where `init` drops the
last coordinate.  It holds because `init` admits a continuous section `y ↦ snoc y a`: if a
neighbourhood of `x` is mapped into `T` by `init`, pulling it back along the section through
`x` exhibits a neighbourhood of `init x` inside `T`. -/
theorem interior_preimage_init_subset {n : ℕ} (T : Set (Fin n → ℝ)) :
    interior ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' T) ⊆
      (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' interior T := by
  intro x hx
  rw [mem_interior_iff_mem_nhds] at hx
  rw [Set.mem_preimage, mem_interior_iff_mem_nhds]
  -- `g` is a continuous section of `Fin.init` passing through `x`.
  let g : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => Fin.snoc y (x (Fin.last n))
  have hg : Continuous g := by
    exact Continuous.finSnoc continuous_id continuous_const
  have hgx : g (Fin.init x) = x := by
    simp only [g, Fin.snoc_init_self]
  have hmem : g ⁻¹' (Fin.init ⁻¹' T) ∈ nhds (Fin.init x) := by
    rw [← hgx] at hx
    exact (hg.continuousAt (x := Fin.init x)).preimage_mem_nhds hx
  have hset : (g ⁻¹' (Fin.init ⁻¹' T)) = T := by
    ext y
    simp only [Set.mem_preimage, g, Fin.init_snoc]
  rwa [hset] at hmem

end Work.WilG1.Cell
