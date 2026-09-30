import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- A cycle of a chain complex of `R`-modules whose homology class vanishes is a boundary.
The target degree `j` is the source of the differential into degree `n`, i.e.
`(ComplexShape.down ℕ).prev n` (which is `n + 1`). -/
theorem boundary_of_homologypi_zero {R : Type} [CommRing R] (K : ChainComplex (ModuleCat R) ℕ)
    [∀ i, K.HasHomology i] (n j : ℕ) (hj : (ComplexShape.down ℕ).prev n = j) (z : K.cycles n)
    (h : K.homologyπ n z = 0) :
    ∃ y : K.X j, (ModuleCat.Hom.hom (K.d j n)) y = (ModuleCat.Hom.hom (K.iCycles n)) z := by
  -- The short complex `K.X j ⟶ K.cycles n ⟶ K.homology n` is exact: `K.homology n` is the
  -- cokernel of `K.toCycles j n` (which is the boundary map `K.X j → K.cycles n` followed by the
  -- inclusion of cycles into `K.X n`).
  let T' := ShortComplex.mk (K.toCycles j n) (K.homologyπ n) (K.toCycles_comp_homologyπ j n)
  have hT : T'.Exact :=
    ShortComplex.exact_of_g_is_cokernel T' (K.homologyIsCokernel j n hj)
  -- Unfold exactness into elements: a cycle killed by `homologyπ` is in the image of the
  -- boundary map into the cycles.
  have key := (ShortComplex.exact_iff_of_hasForget (S := T')).1 hT
  have hz : (forget₂ (ModuleCat R) Ab).map T'.g z = 0 := h
  obtain ⟨y, hy⟩ := key z hz
  refine ⟨y, ?_⟩
  have hy' : (K.toCycles j n) y = z := hy
  rw [← hy', ← K.toCycles_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]

end Work.Pi6.MSS
