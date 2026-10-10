import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.E1aClean.archimedeanKillClauseLinked
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two ingredients of the archimedean crux in the shape the target needs

1. `resH1_mapH1`: restriction to a subgroup commutes with transport along an equivariant additive
   isomorphism of coefficients (both are defined cocycle-wise).
2. `archCruxA_gen_linked`: `E1aClean.archimedeanKillClauseLinked` (the archimedean crux with an
   *explicit* seam `φ : Ω →+* ℂ`) holds with an **arbitrary** `ℤ`-finite coefficient as first
   variable.  Every ingredient of its proof (`PhiE_surjective`,
   `exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf`, `localPushOfSeam`,
   `extRes_PhiEgen_comp_mk₀_eq_zero`) is stated for an arbitrary `R`, so the syzygy restriction
   `kernel (freeCover N)` was doing no work.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- **Restriction commutes with the coefficient transport.** -/
theorem resH1_mapH1 {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {M N : Type} [AddCommGroup M] [DistribMulAction Γ M] [AddCommGroup N] [DistribMulAction Γ N]
    (Nsub : Subgroup Γ) (θ : M →+ N) (hθ : Work.GroupCohomology.IsEquivariant Γ θ)
    (hθ' : Work.GroupCohomology.IsEquivariant ↥Nsub θ) :
    ∀ x : Work.AbsoluteKummer.H1 Γ M,
      Work.SSGRoute.PT.H2Fin.resH1 Nsub N (Work.AbsoluteKummer.mapH1 θ hθ x)
        = Work.AbsoluteKummer.mapH1 (G := ↥Nsub) θ hθ'
            (Work.SSGRoute.PT.H2Fin.resH1 Nsub M x) := by
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change Work.SSGRoute.PT.H2Fin.resH1 Nsub N
        (Work.AbsoluteKummer.mapH1 θ hθ (Work.AbsoluteKummer.H1π Γ M f))
      = Work.AbsoluteKummer.mapH1 (G := ↥Nsub) θ hθ'
          (Work.SSGRoute.PT.H2Fin.resH1 Nsub M (Work.AbsoluteKummer.H1π Γ M f))
  rw [Work.AbsoluteKummer.mapH1_H1π, Work.SSGRoute.PT.H2Fin.resH1_H1π,
    Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.mapH1_H1π]
  rw [show Work.SSGRoute.PT.H2Fin.resZ1 Nsub N (Work.AbsoluteKummer.mapZ1 θ hθ f)
      = Work.AbsoluteKummer.mapZ1 θ hθ' (Work.SSGRoute.PT.H2Fin.resZ1 Nsub M f) from by
    apply Subtype.ext
    funext n
    rfl]

/-- **A cocycle which is a coboundary on `H` restricts to an element of `B¹(H)`.**

The two shapes involved are `IsCoboundaryOn act H b` (the target's notation) and membership in
`Work.AbsoluteKummer.B1 ↥H M` (the shape consumed by `resH1`); the witness is the same `m`. -/
theorem resZ1_mem_absB1_of_isCoboundaryOn {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {M : Type} [AddCommGroup M] [DistribMulAction Γ M]
    (H : Subgroup Γ) (b : Γ → M)
    (hbZ : b ∈ Work.AbsoluteKummer.Z1 Γ M)
    (hcob : SSGRoute.IsCoboundaryOn (MonoidHom.id Γ) H b) :
    ((Work.SSGRoute.PT.H2Fin.resZ1 H M ⟨b, hbZ⟩ : Work.AbsoluteKummer.Z1 ↥H M) : ↥H → M)
      ∈ Work.AbsoluteKummer.B1 ↥H M := by
  obtain ⟨m, hm⟩ := hcob
  rw [Work.AbsoluteKummer.mem_B1_iff]
  refine ⟨m, ?_⟩
  funext g
  rw [Work.GroupCohomology.d0_apply]
  exact (hm g g.2).symm

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The archimedean crux with an explicit seam, for an arbitrary coefficient as first variable.**

This is `Work.SSGRoute.E1aClean.archimedeanKillClauseLinked` with the canonical syzygy
`kernel (freeCover N)` replaced by an arbitrary `ℤ`-finite `Gal(K/k)`-representation `R`; the
trivial-decomposition-group case is replaced by the hypothesis `hne` (which is what the consumer
`ArchDictionary.archimedeanDictNonsplit` supplies). -/
theorem archCruxA_gen_linked
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hne : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) R z) = 0) :
    (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w)).subtype z).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w)))
      (add_zero 1) = 0 := by
  classical
  haveI hFintypeG : Fintype (K ≃ₐ[k] K) := inferInstance
  haveI hFintypeD : Fintype ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite w)) := Fintype.ofFinite _
  -- write `z` as a `PhiE`-generator
  obtain ⟨y, hy⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K) R z
  rw [← hy] at h ⊢
  -- the `⟨σ⟩`-invariant primitive over `Ωˣ`
  obtain ⟨Φ, hΦ, hκ⟩ :=
    Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
      (k := k) (Ω := Ω) (K := K) R (Subgroup.zpowers σ) y h
  -- the local primitive over `K_wˣ`, by the explicit seam
  obtain ⟨Φ₁, hΦ₁⟩ := Work.SSGRoute.E1aClean.localPushOfSeam k Ω K w σ hσ φ hφK hlink hle hne
    R y Φ hΦ hκ
  -- the `δ`-step: a local lift kills the localised class
  refine Work.SSGRoute.E1aClean.extRes_PhiEgen_comp_mk₀_eq_zero
    (f := (SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite w)).subtype)
    (M := R)
    (R := SSGRoute.PTExt.unitsK k ↥K)
    (Z := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
      (NK.GlobalCFT.Place.ofInfinite w))
    (ι := NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w))
    (w := y) (φ := Φ₁) ?_
  intro r
  exact hΦ₁ r

end

end Work.SSGRoute.ArchDictionary
