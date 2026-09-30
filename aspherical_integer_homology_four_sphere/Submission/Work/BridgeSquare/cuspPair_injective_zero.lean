/-
# `BridgeSquare/cuspPair_injective_zero.lean` — injectivity of the cusp pair in degree `0`

The cusp pair `F_k = cuspPair k = biprod.lift (H_k τ) (H_k π)` of `BridgeSquare/CuspPair.lean`
has, in degree `0`, the two components

* `T_0 = H_0(τ) : H_0(⊔_v ∂[-1,1]² × T²_v) → H_0(M̄)`,
* `P_0 = H_0(π) : H_0(⊔_v ∂[-1,1]² × T²_v) → H_0(⊔_v T²_v)`.

`P_0` is a **split epimorphism** (`Work.BridgeSquare.cuspPair_P_surjective`): the projection
`π` forgetting the boundary coordinate admits the section
`s p₀ : ⟨v, y⟩ ↦ ⟨v, (p₀, y)⟩` at any basepoint `p₀` of the square boundary
(`Work.BridgeSquare.secMap`), whence `H_0(π) ∘ H_0(s p₀) = 𝟙`.  Its source and its target are
abstractly `ℤ^5` (`H_0` of a five-fold disjoint union of connected spaces), so a surjection
between them is injective (`Work.BridgeSquare.injective_of_surjective_of_rank`).

Since the second component of a `biprod.lift` already detects the kernel
(`biprod.lift f g ≫ biprod.snd = g`), the injectivity of `P_0` is exactly the injectivity of
`F_0 = cuspPair 0`.  This is the degree-`0` half of the degree bookkeeping of
`NOTES_LEAD_aspherical_bridge.md` §2.2 ("deg 0: injective, from the `B`-half alone").
-/
import Mathlib
import Submission.Work.BridgeSquare.CuspPair
import Submission.Work.BridgeSquare.cuspPair_P_surjective
import Submission.Work.BridgeSquare.injective_of_surjective_of_rank

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.Topology CategoryTheory CategoryTheory.Limits

namespace Work.BridgeSquare

theorem cuspPair_injective_zero [rt : Work.Space.RTData]
    (eC : LeanEval.Topology.intHomology 0 (Work.BridgeSquare.Cop (rt := rt)) ≃ₗ[ℤ] (Fin 5 → ℤ))
    (eT : LeanEval.Topology.intHomology 0 (Work.BridgeSquare.Top (rt := rt)) ≃ₗ[ℤ] (Fin 5 → ℤ)) :
    Function.Injective (Work.BridgeSquare.cuspPair (rt := rt) 0).hom := by
  -- The second component `H_0(π)` is surjective (it is split by `H_0(secMap p₀)`), hence
  -- injective because its source and target are both abstractly `ℤ^5`.
  have hP : Function.Injective (homMap (projMap (rt := rt)) 0).hom :=
    injective_of_surjective_of_rank eC eT _ (cuspPair_P_surjective (rt := rt) 0)
  -- `cuspPair 0 = biprod.lift (H_0 τ) (H_0 π)`, and `biprod.snd` extracts the second component.
  have hsnd : cuspPair (rt := rt) 0 ≫ biprod.snd = homMap (projMap (rt := rt)) 0 :=
    biprod.lift_snd _ _
  have hkey : ∀ z : LeanEval.Topology.intHomology 0 (Cop (rt := rt)),
      (homMap (projMap (rt := rt)) 0).hom z
        = (biprod.snd : LeanEval.Topology.intHomology 0 (Mop (rt := rt)) ⊞
            LeanEval.Topology.intHomology 0 (Top (rt := rt)) ⟶
            LeanEval.Topology.intHomology 0 (Top (rt := rt))).hom
          ((cuspPair (rt := rt) 0).hom z) := by
    intro z
    have h := ConcreteCategory.congr_hom hsnd z
    simp only [ModuleCat.comp_apply] at h
    exact h.symm
  intro x y hxy
  apply hP
  rw [hkey x, hkey y]
  exact congrArg
    (fun w => (biprod.snd : LeanEval.Topology.intHomology 0 (Mop (rt := rt)) ⊞
        LeanEval.Topology.intHomology 0 (Top (rt := rt)) ⟶
        LeanEval.Topology.intHomology 0 (Top (rt := rt))).hom w) hxy

end Work.BridgeSquare
