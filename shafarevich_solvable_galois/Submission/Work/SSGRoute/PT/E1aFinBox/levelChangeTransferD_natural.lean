import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.E1aClean.phiCanDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the level-change transfer `levelChangeTransferD` in the coefficients

`E1aClean.levelChangeTransferD` is the `H¹`-transfer along the level change from the decomposition
subgroup `D_A = (k^h).fixingSubgroup ≤ Gal(Ω/k)` to `Gal(Ω/k^h)`, with coefficients transported by
`levelTwoCoeffEquiv`.  The first (naturality) obligation of `E1aClean.finPlaceDict_holds` is that
this transfer commutes with the coefficient change induced by an equivariant morphism
`g : R ⟶ R₂` of `Coeff`-representations — through `g` at the decomposition subgroup and through
`Rep.res φ g` at the henselian level `Gal(Ω/k^h)`.

The general statement is that the `H¹`-transfer of `H1Transfer.lean` is natural in the
coefficients along an equivariant additive map (`h1TransferAddHom_mapH1_natural` below); the
level-change instance is then *definitional*, because

* `levelTwoCoeffEquiv` is the identity on the common underlying additive group, and
* `Rep.resMap` (restriction of scalars) does not change the underlying map,

so the required commuting square `levelTwoCoeffEquiv A R φ ∘ precomp (Rep.res φ g) =
precomp g ∘ levelTwoCoeffEquiv A R₂ φ` is `rfl`.
-/

namespace Work.SSGRoute.PT.E1aFinBox

open Work.AbsoluteKummer

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Naturality of the `H¹`-transfer in the coefficients.**

For `Φ : G' ≃* G` a homeomorphic isomorphism (`hΦc` the continuity of `Φ.symm`) and two compatible
coefficient isomorphisms `Ψ : M' ≃+ M`, `Ψ₂ : N' ≃+ N` (`G'`-modules on the primed side,
`G`-modules on the unprimed side), the transfer commutes with an equivariant coefficient change
`f' : N' →+ M'`, `f : N →+ M`: the only extra input is the commuting square
`Ψ ∘ f' = f ∘ Ψ₂` on the nose. -/
theorem h1TransferAddHom_mapH1_natural
    {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    {M M' N N' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    [AddCommGroup N] [DistribMulAction G N] [AddCommGroup N'] [DistribMulAction G' N']
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (Ψ₂ : N' ≃+ N) (hΨ₂ : ∀ (g' : G') (n' : N'), Ψ₂ (g' • n') = Φ g' • Ψ₂ n')
    (f' : N' →+ M') (hf' : Work.GroupCohomology.IsEquivariant G' f')
    (f : N →+ M) (hf : Work.GroupCohomology.IsEquivariant G f)
    (hsq : ∀ n' : N', Ψ (f' n') = f (Ψ₂ n'))
    (y : Work.AbsoluteKummer.H1 G' N') :
    Work.SSGRoute.PT.h1TransferAddHom Φ hΦc Ψ hΨ (Work.AbsoluteKummer.mapH1 f' hf' y)
      = Work.AbsoluteKummer.mapH1 f hf
          (Work.SSGRoute.PT.h1TransferAddHom Φ hΦc Ψ₂ hΨ₂ y) := by
  refine Work.AbsoluteKummer.SES.H1_induction_on
    (C := fun y => Work.SSGRoute.PT.h1TransferAddHom Φ hΦc Ψ hΨ
        (Work.AbsoluteKummer.mapH1 f' hf' y)
      = Work.AbsoluteKummer.mapH1 f hf
        (Work.SSGRoute.PT.h1TransferAddHom Φ hΦc Ψ₂ hΨ₂ y)) y ?_
  intro c
  rw [Work.AbsoluteKummer.mapH1_H1π, Work.SSGRoute.PT.h1TransferAddHom_mk,
    Work.SSGRoute.PT.h1TransferAddHom_mk, Work.AbsoluteKummer.mapH1_H1π]
  congr 1
  apply Subtype.ext
  funext g
  simp only [Work.AbsoluteKummer.mapZ1_apply, Work.SSGRoute.PT.z1Transfer_coe,
    Work.SSGRoute.PT.cochainTransfer_apply]
  exact hsq _

end

theorem levelChangeTransferD_natural
    (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω)
    (R R₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Finite ℤ R₂.V]
    (φ : (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) →* (K ≃ₐ[k] K))
    [CharZero ↥(Work.SSGRoute.E1aClean.decompField k Ω A)] [IsAlgClosure ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Ω]
    [FiniteDimensional ↥(Work.SSGRoute.E1aClean.decompField k Ω A) ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    [IsGalois ↥(Work.SSGRoute.E1aClean.decompField k Ω A) ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A) (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant ↥((Work.SSGRoute.E1aClean.decompField k Ω A).fixingSubgroup)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (hg' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H1 ↥((Work.SSGRoute.E1aClean.decompField k Ω A).fixingSubgroup)
      (Work.SSGRoute.homCoind k Ω K R₂)) :
    Work.SSGRoute.E1aClean.levelChangeTransferD p k Ω K A R φ hφres
        (Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y) =
      Work.AbsoluteKummer.mapH1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom) hg'
        (Work.SSGRoute.E1aClean.levelChangeTransferD p k Ω K A R₂ φ hφres y) := by
  simp only [Work.SSGRoute.E1aClean.levelChangeTransferD]
  exact h1TransferAddHom_mapH1_natural
    (G := Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω)
    (G' := ↥((Work.SSGRoute.E1aClean.decompField k Ω A).fixingSubgroup))
    (Φ := IntermediateField.fixingSubgroupEquiv (Work.SSGRoute.E1aClean.decompField k Ω A))
    (hΦc := _)
    (Ψ := Work.SSGRoute.E1aClean.levelTwoCoeffEquiv A R φ) (hΨ := _)
    (Ψ₂ := Work.SSGRoute.E1aClean.levelTwoCoeffEquiv A R₂ φ) (hΨ₂ := _)
    (f' := Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) (hf' := hg)
    (f := Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom) (hf := hg')
    (hsq := fun n' => rfl) (y := y)

end Work.SSGRoute.PT.E1aFinBox
