/-
# The coproduct of `n` copies of `ℤ` is the free module `ℤⁿ`

The `Δ`-chain complex of a finite `Δ`-complex `K` has chain groups which are *copowers*
`∐_{σ : Fin (K.card k)} ℤ`, while every matrix presentation of a finite free complex
(`Work.Certificates.FinChainCx`) uses the *product* form `Fin n → ℤ`.  This module supplies the
degreewise identification

`(∐_{i : Fin n} ℤ) ≅ (Fin n → ℤ)`  (`coprodIsoFreeMod n`),

together with the description of its inverse on the coproduct injections:

`Sigma.ι i ≫ (coprodIsoFreeMod n).hom = ModuleCat.ofHom (LinearMap.single ℤ _ i)`,

i.e. the `i`-th coproduct injection `Sigma.ι i 1` is the `i`-th standard basis vector
`Pi.single i 1` of `ℤⁿ`.

The isomorphism is the composite of the two standard identifications

* `Work.Subdivision.PolyCW.freeIso` — the coproduct of `n` copies of `ℤ` is the finitely supported
  functions `Fin n →₀ ℤ` (`Submission/Work/Subdivision/exists_sd_deltaCx.lean`);
* `Finsupp.linearEquivFunOnFinite` — a finitely supported function on a finite type is a
  function.

Both are already in the workspace/Mathlib, so nothing is reproved here: this module only
composes them and records the computation on the injections, which is what a comparison of
`K.chain` with a matrix presentation needs degree by degree.
-/
import Mathlib
import Submission.Work.PieceHomology.Basic
import Submission.Work.Subdivision.exists_sd_deltaCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.PieceHomology

noncomputable section

/-- **The coproduct of `n` copies of `ℤ` is the free module `ℤⁿ`.** -/
def coprodIsoFreeMod (n : ℕ) :
    (∐ (fun _ : Fin n => Work.Homology.ZMod)) ≅ ModuleCat.of ℤ (Fin n → ℤ) :=
  Work.Subdivision.PolyCW.freeIso (Equiv.refl (Fin n)) ≪≫
    LinearEquiv.toModuleIso (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

/-- The morphism of `Work.Subdivision.PolyCW.freeIso`, unfolded. -/
theorem freeIso_hom_eq (n : ℕ) :
    (Work.Subdivision.PolyCW.freeIso (Equiv.refl (Fin n))).hom
      = Limits.Sigma.desc
          (fun a : Fin n => ModuleCat.ofHom (Finsupp.lsingle (Equiv.refl (Fin n) a))) := rfl

/-- The coproduct injection of `Work.Subdivision.PolyCW.freeIso`: the `i`-th basis vector of the
coproduct is the finitely supported function `Finsupp.single i 1`. -/
theorem freeIso_hom_ι (n : ℕ) (i : Fin n) :
    Sigma.ι (fun _ : Fin n => Work.Homology.ZMod) i
      ≫ (Work.Subdivision.PolyCW.freeIso (Equiv.refl (Fin n))).hom
      = ModuleCat.ofHom (Finsupp.lsingle i) := by
  rw [freeIso_hom_eq, Limits.Sigma.ι_comp_desc]
  rfl

/-- The `i`-th coproduct injection `Sigma.ι i 1` is the `i`-th standard basis vector of `ℤⁿ`
under `coprodIsoFreeMod`. -/
theorem coprodIsoFreeMod_ι (n : ℕ) (i : Fin n) :
    Sigma.ι (fun _ : Fin n => Work.Homology.ZMod) i ≫ (coprodIsoFreeMod n).hom
      = ModuleCat.ofHom (LinearMap.single ℤ (fun _ : Fin n => ℤ) i) := by
  rw [show (coprodIsoFreeMod n).hom
      = (Work.Subdivision.PolyCW.freeIso (Equiv.refl (Fin n))).hom
        ≫ (LinearEquiv.toModuleIso (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))).hom
      from rfl]
  rw [← Category.assoc, freeIso_hom_ι, LinearEquiv.toModuleIso_hom, ← ModuleCat.ofHom_comp]
  congr 1
  apply LinearMap.ext_ring
  simp [LinearMap.single_apply, Finsupp.lsingle_apply]

end

end Work.PieceHomology
