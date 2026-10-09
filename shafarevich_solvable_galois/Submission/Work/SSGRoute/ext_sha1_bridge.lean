import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.ExtH1
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.sha1_descent_H1
import Submission.Work.SSGRoute.sha1_descent_range
import Submission.Work.SSGRoute.augSES_shortExact
import Submission.Work.SSGRoute.glue_fin_decomp
import Submission.Work.SSGRoute.glue_fin_decomp_ex
import Submission.Work.SSGRoute.glue_involution_place
import Submission.Work.SSGRoute.glue_infinite_place
import Submission.Work.SSGRoute.glue_local_of_sha1_conditions
import Submission.Work.SSGRoute.extHRestrict_gammaHom_eq_zero_iff
import Submission.Work.SSGRoute.gammaHom_natural_coeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E1b `ext_sha1_bridge` — `Ш¹(k,M)` lives at level `K`

**Statement.** There are injective additive maps `Ш¹(k,M) → extH_{Gal(K/k)}(M) 1`, natural in `M`.
The image is exactly the classes that are locally trivial at every place of `K` (`IsLocTrivial`,
infinite places included).

**Route.**
1. **Inflation–restriction** gives `0 → H¹(G,M) → H¹(k,M) → H¹(K,M)`.
2. **The image in `H¹(K,M)` is in `Ш¹(K,M)`.** `M` is a trivial `G_K`-module, so this is a group of
   homomorphisms `G_K → M` that vanish on every decomposition group. Chebotarev makes them 0:
   every element of a finite quotient is a Frobenius. Reuse `bauer_of_chebotarev`,
   `eq_zero_on_fixingSubgroup_of_eq_zero_on_split` and `NK.NUV2.chebotarev_all0`.
3. **Local triviality matches.** It agrees on the two sides because inflation
   `H¹(D_w, M) → H¹(D_A, M)` is injective (inflation–restriction again).
4. **Place glue.** `ValuationSubring Ω` places against NK `Place ↥K`: `place_transport`,
   `localGaloisEquiv`. Real places are the `zpowers c` for involutions `c` against infinite `w`.

**Deps.** E0b.

**Size.** 1–2k. **Risk:** medium; the glue dominates.

**Imports.** `Submission.Work.SSGRoute.PTDefs Submission.Work.SSGRoute.Interfaces Submission.Work.SSGRoute.ShaCocycles`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- **Place glue, forward direction.**  If a cochain `ψ : Gal(K/k) → M` is a coboundary on the
decomposition group `D_w` of *every* place `w` of `K`, then it is a coboundary on the image
`(decomp k A).map (res k K)` of the decomposition group of every *finite* place `A` of `Ω`, and on
the image `(zpowers σ).map (res k K)` of every involution `σ` of `G_k = Ω ≃ₐ[k] Ω`.

This is the direction of the place glue used for the inclusion "range of the descent ⊆ locally
trivial": `IsCoboundaryOn` is monotone in the subgroup, and
`Work.SSGRoute.glue_fin_decomp` / `Work.SSGRoute.glue_involution_place` exhibit every subgroup on
the left as a subgroup of a decomposition group `decompK w`.

(Kept local to this file: the sibling module `Submission.Work.SSGRoute.glue_sha1_conditions_of_local`
proves the same statement but declares a public `isCoboundaryOn_mono`, which clashes with the
existing copy in `Submission.Work.SSGRoute.ShaCocycles` as soon as both are imported.) -/
lemma glue_fin_involution_of_local (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (M : Type) [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M]
    (ψ : (K ≃ₐ[k] K) → M)
    (h : ∀ w : NK.GlobalCFT.Place ↥K,
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        (SSGRoute.PTExt.decompK (k := k) w) ψ) :
    (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ) := by
  have mono : ∀ {H H' : Subgroup (K ≃ₐ[k] K)}, H ≤ H' →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K)) H' ψ →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K)) H ψ := by
    rintro H H' hle ⟨m, hm⟩
    exact ⟨m, fun g hg => hm g (hle hg)⟩
  constructor
  · intro A hA
    obtain ⟨q, hq⟩ := glue_fin_decomp k Ω K A hA
    exact mono hq (h (NK.GlobalCFT.Place.ofFinite q))
  · intro σ hσ
    obtain ⟨w, hw⟩ := glue_involution_place k Ω K σ hσ
    exact mono hw (h w)

/-- **The bridge between local triviality and the cocycle conditions of the Hasse descent.**

For a `1`-cocycle `ψ : Z¹(Gal(K/k), M)`, the `Ext`-class `γ(H1π ψ)` (the degree-one avatar of the
cohomology class of `ψ`) is locally trivial at every place `w` of `K` if and only if `ψ` is a
coboundary on the image in `Gal(K/k)` of the decomposition group of every finite place of `Ω` and
on the image of every involution of `G_k`.  This is the description of the range of the Hasse
descent `sha1_descent_range`, transported across the bridge `γ` by
`extHRestrict_gammaHom_eq_zero_iff` and the place glue. -/
lemma isLocTrivial_gammaHom_H1π_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (hS : (Work.SSGRoute.ExtH1.augSES (K ≃ₐ[k] K)).ShortExact)
    (ψ : ↥(Work.GroupCohomology.Z1 (K ≃ₐ[k] K) M)) :
    IsLocTrivial (k := k) (K := K)
        (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS
          (Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ))
      ↔ (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
          SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
            ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ.1) ∧
        (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
          SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
            ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ.1) := by
  have h1 : ψ.1 1 = 0 := Work.GroupCohomology.Z1.map_one (K ≃ₐ[k] K) M ψ.2
  have hiff : ∀ w : NK.GlobalCFT.Place ↥K,
      SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w)
          (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS
            (Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ)) = 0
        ↔ SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
            (SSGRoute.PTExt.decompK (k := k) w) ψ.1 := by
    intro w
    rw [extHRestrict_gammaHom_eq_zero_iff (G := K ≃ₐ[k] K) (M := M) hS
      (SSGRoute.PTExt.decompK (k := k) w) ψ]
    simp only [SSGRoute.IsCoboundaryOn, MonoidHom.id_apply]
  rw [SSGRoute.PTExt.IsLocTrivial, SSGRoute.PTExt.IsLocTrivialOn]
  constructor
  · intro hloc
    exact glue_fin_involution_of_local k Ω K M ψ.1 (fun w => (hiff w).mp (hloc w))
  · rintro ⟨hfin, hinf⟩
    exact fun w => (hiff w).mpr (glue_local_of_sha1_conditions k Ω K M ψ.1 h1 hfin hinf w)

/-- **E1b.** `Ш¹(k, M)` lives at the level `K`: for a finite `Gal(K/k)`-module `M` there are
injective additive maps `Ш¹(k,M) → H¹(Gal(K/k), M)` (inflation, read in `Ext`-cohomology),
natural in `M`, whose image is exactly the classes that are locally trivial at every place of `K`
(inflation–restriction plus Chebotarev: `Ш¹(K, M) = 0` for the trivial `G_K`-module `M`). -/
theorem ext_sha1_bridge (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] :
    ∃ β : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Sha1 p k Ω K M →+ extH (modRep (K ≃ₐ[k] K) M) 1,
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M], Function.Injective (β M)) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (h : extH (modRep (K ≃ₐ[k] K) M) 1), (∃ b, β M b = h) ↔ IsLocTrivial h) ∧
      ∀ (M₁ : Type) [AddCommGroup M₁] [Module (ZMod p) M₁] [DistribMulAction (K ≃ₐ[k] K) M₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₁] [Finite M₁]
        (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
        (f : M₁ →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M₁), f (g • m) = g • f m)
        (F : modRep (K ≃ₐ[k] K) M₁ ⟶ modRep (K ≃ₐ[k] K) M₂) (hF : ∀ m : M₁, F.hom m = f m)
        (b : Sha1 p k Ω K M₁),
        β M₂ (Sha1Map p k Ω K M₁ M₂ f hf b) = (β M₁ b).comp (Abelian.Ext.mk₀ F) (add_zero 1) := by
  -- `Gal(K/k)` is finite, so `H¹(Gal(K/k), M)` is `Work.GroupCohomology.H1`.
  haveI : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k K
  -- Short exactness of the augmentation sequence `0 → I → k[G] → k → 0`.
  have hS : (Work.SSGRoute.ExtH1.augSES (K ≃ₐ[k] K)).ShortExact :=
    Work.SSGRoute.augSES_shortExact (K ≃ₐ[k] K)
  -- The bridge: Hasse descent `Ш¹(k,M) →+ H¹(Gal(K/k),M)` followed by the degree-one
  -- `Ext`-bridge `γ : H¹(Gal(K/k),M) ≅ Ext¹_{Gal(K/k)}(ℤ,M)`.
  let β : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Sha1 p k Ω K M →+ extH (modRep (K ≃ₐ[k] K) M) 1 :=
    fun M _ _ _ _ _ =>
      (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS).comp
        (sha1DescentHom p k Ω K M)
  refine ⟨β, ?_, ?_, ?_⟩
  · -- (i) injectivity: a composite of injective maps.
    intro M _ _ _ _ _
    show Function.Injective
      ((Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS).comp
        (sha1DescentHom p k Ω K M))
    exact (Work.SSGRoute.ExtH1.gammaHom_injective (G := K ≃ₐ[k] K) (M := M) hS).comp
      (sha1DescentHom_injective p k Ω K M)
  · -- (ii) range: `h` is in the range of `β` iff it is locally trivial at every place of `K`.
    intro M _ _ _ _ _ h
    constructor
    · rintro ⟨b, hb⟩
      have hrange := sha1_descent_range p k Ω K M
      have hmem : (sha1DescentHom p k Ω K M b) ∈ Set.range (sha1DescentHom p k Ω K M) :=
        ⟨b, rfl⟩
      rw [hrange] at hmem
      obtain ⟨ψ, hψ, hcond⟩ := hmem
      have hgamma : h = Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS
          (Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ) := by
        rw [← hb]
        show (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS)
            ((sha1DescentHom p k Ω K M) b) = _
        rw [← hψ]
      rw [hgamma]
      exact (isLocTrivial_gammaHom_H1π_iff p k Ω K M hS ψ).mpr hcond
    · intro hloc
      obtain ⟨y, hy⟩ :=
        Work.SSGRoute.ExtH1.gammaHom_surjective (G := K ≃ₐ[k] K) (M := M) hS h
      obtain ⟨ψ, hψ⟩ := QuotientAddGroup.mk'_surjective
        ((Work.GroupCohomology.B1 (K ≃ₐ[k] K) M).comap
          (Work.GroupCohomology.Z1 (K ≃ₐ[k] K) M).subtype) y
      have hloc' : IsLocTrivial (k := k) (K := K)
          (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M) hS
            (Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ)) := by
        rw [show Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ = y from hψ, hy]
        exact hloc
      obtain ⟨hfin, hinf⟩ := (isLocTrivial_gammaHom_H1π_iff p k Ω K M hS ψ).mp hloc'
      have hrange := sha1_descent_range p k Ω K M
      have hmem : y ∈ Set.range (sha1DescentHom p k Ω K M) := by
        rw [hrange]
        exact ⟨ψ, hψ, hfin, hinf⟩
      obtain ⟨b, hb⟩ := hmem
      refine ⟨b, ?_⟩
      rw [← hy, ← hb]
      rfl
  · -- (iii) naturality in the coefficient module.
    intro M₁ _ _ _ _ _ M₂ _ _ _ _ _ f hf F hF b
    show (Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M₂) hS)
          ((sha1DescentHom p k Ω K M₂) (Sha1Map p k Ω K M₁ M₂ f hf b)) =
        ((Work.SSGRoute.ExtH1.gammaHom (G := K ≃ₐ[k] K) (M := M₁) hS)
          ((sha1DescentHom p k Ω K M₁) b)).comp (Abelian.Ext.mk₀ F) (add_zero 1)
    rw [sha1DescentHom_natural p k Ω K M₁ M₂ f hf b]
    exact gammaHom_natural_coeff (G := K ≃ₐ[k] K) (M := M₁) (N := M₂) hS
      f.toAddMonoidHom hf F hF (sha1DescentHom p k Ω K M₁ b)

end Work.SSGRoute
