import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-!
# The slope `σ_v` is a lattice vector

`σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` (`slope`), and `Λ_v` is the subgroup of `ℝ³` generated
by the three vectors `κ_{v,i}` (`lattice = AddSubgroup.closure (range (kv v))`).  Since `b_v` and
`c_v` are integers (`slopeB`, `slopeC` are `ℤ`-valued), each summand is an integer multiple of a
generator, hence in `Λ_v`; a subgroup is closed under sums and integer multiples, so `σ_v ∈ Λ_v`.

This is what makes the meridian `σ_v` a well-defined loop on the cusp torus `T³_v = ℝ³/Λ_v` and
the disk `D² × (ℝ/ℤ)² → T³_v`, `p ↦ u(p)σ_v + y`, a well-defined map: the `σ`-coordinate advances
by `σ_v ∈ Λ_v` when `u` advances by `1`.
-/

/-- **`σ_v` lies in the cusp lattice `Λ_v`.**  It is a `ℤ`-linear combination of the generators
`κ_{v,1}, κ_{v,2}, κ_{v,3}` of `lattice v`. -/
theorem beta_lattice_mem_slope (v : Fin 5) : slope v ∈ lattice v := by
  have h0 : kv v 0 ∈ lattice v :=
    AddSubgroup.subset_closure (⟨0, rfl⟩ : kv v 0 ∈ Set.range (kv v))
  have h1 : kv v 1 ∈ lattice v :=
    AddSubgroup.subset_closure (⟨1, rfl⟩ : kv v 1 ∈ Set.range (kv v))
  have h2 : kv v 2 ∈ lattice v :=
    AddSubgroup.subset_closure (⟨2, rfl⟩ : kv v 2 ∈ Set.range (kv v))
  have hb : (slopeB v : ℝ) • kv v 1 ∈ lattice v := by
    have := AddSubgroup.zsmul_mem (lattice v) h1 (slopeB v)
    rwa [Int.cast_smul_eq_zsmul]
  have hc : (slopeC v : ℝ) • kv v 2 ∈ lattice v := by
    have := AddSubgroup.zsmul_mem (lattice v) h2 (slopeC v)
    rwa [Int.cast_smul_eq_zsmul]
  rw [slope]
  exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h0 hb) hc

end Work.Cusp
