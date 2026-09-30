import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If each `L i` is a `ℤ`-submodule of `E` whose `ℝ`-span is all of `E`, then the
`ℝ`-span of the product `Submodule.pi Set.univ L ⊆ (ι → E)` is all of `ι → E`.

This is used to reduce statements about a product of `ℤ`-lattices (each spanning `E` over `ℝ`)
to statements about the whole product `ι → E`. -/
theorem pi_span_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (L : ι → Submodule ℤ E)
    (h : ∀ i, Submodule.span ℝ (L i : Set E) = ⊤) :
    Submodule.span ℝ (Submodule.pi Set.univ L : Set (ι → E)) = ⊤ := by
  classical
  apply le_antisymm le_top
  -- The product of the `ℝ`-spans is everything.
  have hpi : Submodule.pi Set.univ (fun i => Submodule.span ℝ (L i : Set E)) = ⊤ := by
    have hfun : (fun i => Submodule.span ℝ (L i : Set E)) =
        (fun _ : ι => (⊤ : Submodule ℝ E)) := funext h
    rw [hfun, Submodule.pi_top]
  rw [← hpi]
  -- The product is the supremum of the coordinate images.
  rw [← Submodule.iSup_map_single (R := ℝ) (φ := fun _ : ι => E)
        (p := fun i => Submodule.span ℝ (L i : Set E))]
  apply iSup_le
  intro i
  -- Each coordinate image of `span ℝ (L i)` lands in the span of `pi univ L`.
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  intro x hx
  change (LinearMap.single ℝ (fun _ : ι => E) i) x ∈ Submodule.span ℝ ↑(Submodule.pi Set.univ L)
  apply Submodule.subset_span
  change Pi.single i x ∈ Submodule.pi Set.univ L
  rw [Submodule.mem_pi]
  intro j _
  rcases eq_or_ne j i with rfl | hne
  · rw [Pi.single_eq_same]; exact hx
  · rw [Pi.single_eq_of_ne hne]; exact (L j).zero_mem

end Work.BW
