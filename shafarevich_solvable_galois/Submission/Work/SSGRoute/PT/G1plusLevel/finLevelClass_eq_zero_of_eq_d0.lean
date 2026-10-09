import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open SSGRoute.PTExt

namespace Work.SSGRoute.PT.G1plusLevel

/-- **The level class of a factorised cocycle that is a coboundary vanishes.**

`Work.SSGRoute.PT.finLevelClass` is the class `[b]_L ∈ Ext¹_{D_w}(ℤ, M^∨(1))` of the `1`-cocycle
`g ↦ b₀ (g : L ≃ₐ[k] L)` on the decomposition group `D_w = decompK w`, for the coefficient action
pulled back along `φ₀ = (decompK q).subtype ∘ f`.  If that cocycle is the coboundary
`g ↦ (f g) • m - m` of an element `m`, then the class is `0` (its representative in
`H¹(D_w, M^∨(1))` lies in `B¹`, so it dies under the degree-one bridge `ExtH1.gammaZ1`).

Route: `rw [finLevelClass]` (the body ends in `ExtH1.gammaHom (H1π ⟨…⟩)`), `rw [ExtH1.gammaHom_H1π]`,
then `ExtH1.gammaZ1_eq_zero_iff` and `Work.GroupCohomology.mem_B1_iff`, with `m` as the witness
(`Work.GroupCohomology.d0_apply` computes `d0 m g = g • m - m`, which is `↑(f g) • m - m` because
the local instance is `DistribMulAction.compHom _ ((decompK q).subtype.comp f)`). -/
theorem finLevelClass_eq_zero_of_eq_d0 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {T : Type} [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {L : IntermediateField k Ω} [FiniteDimensional k L] [IsGalois k L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
        ↥K ≃ₐ[k] ↥K) = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hcrossed : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ ((g * h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) :
          ↥L ≃ₐ[k] ↥L)
        = b₀ (g : ↥L ≃ₐ[k] ↥L) +
          (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) •
            b₀ (h : ↥L ≃ₐ[k] ↥L))
    (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hm : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (g : ↥L ≃ₐ[k] ↥L)
        = ((f g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
            ↥K ≃ₐ[k] ↥K) • m - m) :
    Work.SSGRoute.PT.finLevelClass p k Ω K T M L q w f hf b₀ hcrossed = 0 := by
  classical
  -- the coefficient with its `D_w`-action pulled back along the place glue `φ₀ = subtype_q ∘ f`
  let X := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  let φ₀ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      (↥K ≃ₐ[k] ↥K) :=
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f
  letI : DistribMulAction
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) X :=
    DistribMulAction.compHom X φ₀
  -- state the class at the `modRep`-spelling of the coefficient, so that the `ExtH1` bridge
  -- (`gammaZ1`, whose value lives at that spelling) can be rewritten into
  show (Work.SSGRoute.PT.finLevelClass p k Ω K T M L q w f hf b₀ hcrossed :
      extH (modRep ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite w)) X) 1) = 0
  -- the `Rep`-transport in the body of `finLevelClass` is along a *definitional* equality, so
  -- unfolding leaves the bridge `gammaHom (H1π ⟨b₀|D_w, _⟩)`
  simp only [Work.SSGRoute.PT.finLevelClass]
  rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  -- `gammaHom (H1π ψ) = gammaZ1 ψ`, at the same spelling of the coefficient
  show (Work.SSGRoute.ExtH1.gammaZ1
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) X
      (Work.SSGRoute.augSES_shortExact _) _ : extH (modRep ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite w)) X) 1) = 0
  -- `gammaZ1` dies on coboundaries: exhibit `m` with `d⁰ m = b₀|D_w`
  rw [Work.SSGRoute.ExtH1.gammaZ1_eq_zero_iff, Work.GroupCohomology.mem_B1_iff]
  refine ⟨m, ?_⟩
  funext g
  show g • m - m = b₀ (g : ↥L ≃ₐ[k] ↥L)
  rw [hm g]
  rfl

end Work.SSGRoute.PT.G1plusLevel
