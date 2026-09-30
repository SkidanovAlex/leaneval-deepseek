/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.ComapChain
import Submission.Work.Subdivision.comapChain_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The canonical isomorphism between a comap subcomplex and its base

For degreewise submodules `T k ≤ S.sub k` closed under the differential, the
subcomplex `SubData.comapChain S T hT hTd` of `S.chain` and the subcomplex
`SubData.mk T hTd` of `C` record the same chains, viewed in `S` or in `C`.  They
are identified by `SubData.comapChainIso`, whose components are
`Submodule.comapSubtypeEquivOfLe (hT k)`; the chain-map square is
`SubData.comapChain_comm`.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

/-- The canonical isomorphism between the subcomplex of `S.chain` cut out by the
degreewise submodules `T k ≤ S.sub k` and the subcomplex of `C` with the same
submodules: both record the same chains, viewed in `S` or in `C`. -/
noncomputable def comapChainIso (S : SubData C) (T : ∀ k, Submodule ℤ (C.X k))
    (hT : ∀ k, T k ≤ S.sub k)
    (hTd : ∀ k (x : C.X (k + 1)), x ∈ T (k + 1) → (C.d (k + 1) k).hom x ∈ T k) :
    (S.comapChain T hT hTd).chain ≅ (SubData.mk T hTd).chain := by
  let f : (S.comapChain T hT hTd).chain ⟶ (SubData.mk T hTd).chain :=
    ChainComplex.ofHom (fun k => ModuleCat.ofHom
        ((Submodule.comapSubtypeEquivOfLe (hT k)).toLinearMap :
          ↥((S.comapChain T hT hTd).sub k) →ₗ[ℤ] ↥(T k)))
      fun k => Work.Subdivision.comapChain_comm S T hT hTd k
  haveI hf : ∀ k, IsIso (f.f k) := fun k => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Submodule.comapSubtypeEquivOfLe (hT k)).bijective
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

end SubData

end

end Work.Subdivision
