import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.Transgression.vzQuotAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.Transgression

/-- Every element `z` of the `s`-th step `V_s = ∂(F_s C_{t+1}) ∩ Z_t(F_0)` of the left column is
the boundary (in `C`) of a chain `x` of `F_s` in degree `t+1` whose boundary lies in `F_0`, i.e.
`x ∈ Wrel ξ s (t+1)`.  Equivalently, the map `Wrel ξ s (t+1) → V_s`, `x ↦ d x`, is surjective; this
is the surjectivity of the transgression `d_s` onto `V_s/V_{s-1}`. -/
theorem exists_wrel_of_mem_V {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t s : ℕ)
    (z : C.X t) (hz : z ∈ V ξ t s) :
    ∃ x : (ξ.F.obj s).X (t + 1),
      x ∈ Wrel ξ s (t + 1) ∧ Cincl ξ s t (dFs ξ s (t + 1) t x) = z := by
  -- `z` is a boundary of a chain of `F_s` and a cycle of `F_0`
  rw [V, Submodule.mem_inf] at hz
  obtain ⟨hzB, hzZ⟩ := hz
  rw [Zof, Submodule.mem_inf] at hzZ
  -- lift the chain of `F_s` producing `z`
  rw [Submodule.mem_map] at hzB
  obtain ⟨y, hy, hyz⟩ := hzB
  rw [mem_Fch] at hy
  obtain ⟨w, hw⟩ := hy
  refine ⟨w, ?_, ?_⟩
  · rw [Wrel, Submodule.mem_comap, Submodule.mem_comap]
    rw [show t + 1 - 1 = t from rfl]
    rw [Cincl_dFs_apply, hw, hyz]
    exact hzZ.2
  · rw [Cincl_dFs_apply, hw, hyz]

end Work.SSS.Transgression
