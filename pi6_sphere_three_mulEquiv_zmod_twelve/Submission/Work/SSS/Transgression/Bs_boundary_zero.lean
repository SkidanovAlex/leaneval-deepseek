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

open CategoryTheory CategoryTheory.Limits

/-- An element `u` of `(F_{k+1})_{t+1}` which satisfies the lifting condition defining the model
`B^s` (namely `F_{k+1} → F_{2(k+1)-1}` sends `u` to the boundary `d z` of a chain `z` of
`F_{2(k+1)-1}` in degree `t+2` whose own boundary lifts to `F_{k+1}`) has vanishing boundary in `C`:
`d (F_{k+1} → C) u = 0`.  This is the statement that the transgression `d_s` kills the model `B^s`
of its kernel. -/
theorem Bs_boundary_zero {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t k : ℕ)
    (u : (ξ.F.obj (k + 1)).X (t + 1))
    (hu : Finc ξ (k + 1) (2 * (k + 1) - 1) (by omega) (t + 1) u ∈
      Submodule.map (dFs ξ (2 * (k + 1) - 1) ((t + 1) + 1) (t + 1))
        (Submodule.comap (dFs ξ (2 * (k + 1) - 1) ((t + 1) + 1) (t + 1))
          (LinearMap.range (Finc ξ (k + 1) (2 * (k + 1) - 1) (by omega) (t + 1))))) :
    Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t u) = 0 := by
  -- Membership in the image of `dFs` supplies a chain `z` of `F_{2(k+1)-1}` in degree `t+2`
  -- whose boundary is the image of `u` in `F_{2(k+1)-1}`.
  obtain ⟨z, -, hz⟩ := hu
  have hle : k + 1 ≤ 2 * (k + 1) - 1 := by omega
  -- Pushing the identity `d z = Finc u` to the ambient complex `C`.
  have h1 : Cincl ξ (k + 1) (t + 1) u =
      dC C ((t + 1) + 1) (t + 1) (Cincl ξ (2 * (k + 1) - 1) ((t + 1) + 1) z) := by
    rw [← Cincl_Finc_apply ξ hle (t + 1) u, ← hz, Cincl_dFs_apply]
  rw [Cincl_dFs_apply, h1]
  simpa using dC_dC (t + 1) (Cincl ξ (2 * (k + 1) - 1) ((t + 1) + 1) z)

end Work.SSS.Transgression
