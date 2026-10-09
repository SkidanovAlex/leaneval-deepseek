import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.PT.archSwapHalf
import Submission.Work.SSGRoute.extHMap_gammaHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Work.SSGRoute.PT

/-- **The restricted class of a level-`L` cocycle depends only on its restriction to `D_u`.**
This is the independence half of the `Classical.choose` defining `G1⁺`'s pairing at `⟨c⟩`: v6's
`hpairArch` is quantified over *every* level-`L` `1`-cocycle `ψ` factoring `b` on `⟨c⟩`, so the value
`χ_L (ι_u (levelPair … (extHRestrict D_u (levelClassOf ψ))))` must not depend on `ψ`.

Route (measured, both reviewers): `levelClassOf ψ = ExtH1.gammaHom … (H1π ⟨ψ, hψ⟩)` and
`extHRestrict D = extHMap D.subtype 𝟙`; the proved `Work.SSGRoute.extHMap_gammaHom_eq` turns
`extHMap D.subtype 𝟙 (gammaHom G (H1π ψ))` into `gammaHom D (H1π ⟨ψ ∘ D.subtype, ·⟩)`, and the
hypothesis `h` makes the two pulled-back cocycles equal as functions (then `Subtype.ext`/`funext`
plus proof irrelevance finishes).  No injectivity of `gammaHom` is needed. -/
theorem extHRestrict_levelClassOf_eq_of_eqOn (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L)
    (ψ ψ' : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g)
    (hψ' : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ' (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ' h + ψ' g)
    (h : ∀ g : ↥L ≃ₐ[k] ↥L, g ∈ SSGRoute.PTExt.decompK (k := k) u → ψ g = ψ' g) :
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)
      = SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ' hψ') := by
  -- `levelClassOf` evaluates a cocycle through `ExtH1.gammaHom` for the `Gal(L/k)`-action on `M'`
  -- pulled back from `Gal(K/k)` along `galRes`.  We install the very same instance locally so that
  -- the class unfolds to a `gammaHom` in the context of this proof.
  letI hActL : DistribMulAction (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) :=
    DistribMulAction.compHom (Work.SSGRoute.PT.VFcoef p M T) (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZL : SMulCommClass (↥L ≃ₐ[k] ↥L) ℤ (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCL : SMulCommClass (↥L ≃ₐ[k] ↥L) SSGRoute.PTExt.Coeff
      (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  show SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
          (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) ⟨ψ, hψ⟩))
      = SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
          (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) ⟨ψ', hψ'⟩))
  -- `extHRestrict D = extHMap D.subtype 𝟙`, and `extHMap_gammaHom_eq` rewrites the restriction of
  -- the bridge as the bridge of the pulled-back cocycle.
  conv_lhs => rw [SSGRoute.PTExt.extHRestrict, Work.SSGRoute.extHMap_gammaHom_eq]
  conv_rhs => rw [SSGRoute.PTExt.extHRestrict, Work.SSGRoute.extHMap_gammaHom_eq]
  -- the two pulled-back cocycles agree on `D_u`, so their classes (hence their bridges) agree.
  congr 1
  congr 1
  exact Subtype.ext (funext fun d => by simpa using h d.1 d.2)

end Work.SSGRoute.PT
