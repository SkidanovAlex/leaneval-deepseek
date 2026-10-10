import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.bridge_isCocycle2_mem_Z2
import Submission.Work.SSGRoute.bridge_isLocConst2_isLocallyConstant
import Submission.Work.SSGRoute.bridge_mem_B2_isCoboundary2On
import Submission.Work.SSGRoute.sha2_coords.subsingleton_of_coordinates
import Submission.Work.SSGRoute.sha2_hasse.hasseUnits
import Submission.Work.SSGRoute.sha2_kummer.kummerIota_mapH2_injective
import Submission.Work.SSGRoute.sha2_transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ш²(k,M) = 0` for finite `𝔽_p`-modules with trivial `Gal(K/k)`-action

The main theorem: if `μ_p ⊆ k` and a finite `𝔽_p[Gal(K/k)]`-module `M` carries the trivial
`Gal(K/k)`-action, then `Ш²(k,M) = 0`; the local conditions are at all finite places and all
involutions.

The proof works with the coefficient module `Triv p = 𝔽_p` and the exact sequence
`1 → μ_p → k̄ˣ →^p k̄ˣ → 1`:

* the coordinate reduction `sha2_coords.subsingleton_of_coordinates` reduces the statement to the
  claim that every locally trivial continuous `2`-cocycle with values in `𝔽_p` is a global
  coboundary (`hZ` below);
* the arithmetic is transported from an arbitrary algebraic closure `Ω` of `k` to
  `k̄ = AlgebraicClosure k` along a `k`-isomorphism `e : Ω ≃ₐ[k] k̄` (`sha2_transport`);
* in `k̄`, the cocycle is pushed along `𝔽_p ≅ μ_p` into `H²(G_k, k̄ˣ)`; Hasse's theorem for the
  Brauer group (`sha2_hasse.hasseUnits`) makes it locally trivial, and the Kummer injection
  (`sha2_kummer.kummerIota_mapH2_injective`) pulls the triviality back to `H²(G_k, μ_p)`.
-/

set_option linter.ambiguousOpen false
set_option maxHeartbeats 800000

namespace Work.SSGRoute

open scoped Pointwise Topology

open Filter

theorem sha2_trivial_vanish (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (htriv : ∀ (g : K ≃ₐ[k] K) (m : M), g • m = m) :
    Subsingleton (Work.SSGRoute.Sha2 p k Ω K M) := by
  classical
  refine Work.SSGRoute.sha2_coords.subsingleton_of_coordinates p k Ω K ?_ M htriv
  intro c hc
  -- untangle the four components of `c ∈ Z2loc`
  obtain ⟨hcCyc, hcLoc, hcFin, hcInv⟩ := hc
  -- the algebra isomorphism Ω ≃ₐ[k] k̄ and the induced isomorphism of Galois groups
  let e : Ω ≃ₐ[k] AlgebraicClosure k := IsAlgClosure.equiv k Ω (AlgebraicClosure k)
  let ψ : (Ω ≃ₐ[k] Ω) ≃* (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) := conjAlgEquiv e
  -- the transported cocycle
  let cA : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Triv p :=
    fun σ τ => c (ψ.symm σ) (ψ.symm τ)
  -- the coefficient map 𝔽_p → μ_p → k̄ˣ
  have hφ : Work.GroupCohomology.IsEquivariant
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k))) :=
    muAddEquiv_equivariant k p hμ
  have hφ' : Work.GroupCohomology.IsEquivariant
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      ((muAddEquiv k p hμ).symm : Additive (rootsOfUnity p (AlgebraicClosure k)) →+ Triv p) :=
    muAddEquiv_symm_equivariant k p hμ
  have hι : Work.GroupCohomology.IsEquivariant
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p) :=
    Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p
  let χ : Triv p →+ Additive (AlgebraicClosure k)ˣ :=
    (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p).comp
      (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k)))
  have hχ : Work.GroupCohomology.IsEquivariant
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) χ := hι.comp hφ
  let d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ :=
    fun σ τ => χ (cA σ τ)
  -- ## `cA` is a continuous `2`-cocycle over `Gal(k̄/k)`
  have hcA_Z2 : (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2) ∈
      Work.AbsoluteKummer.Z2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (Triv p) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    refine ⟨?_, ?_⟩
    · intro σ τ ρ
      have H := hcCyc (ψ.symm σ) (ψ.symm τ) (ψ.symm ρ)
      simp only [← map_mul] at H
      have htriv : (SSGRoute.res k K (ψ.symm σ)) • c (ψ.symm τ) (ψ.symm ρ) =
          c (ψ.symm τ) (ψ.symm ρ) := rfl
      rw [htriv] at H
      show c (ψ.symm (σ * τ)) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm τ) =
        c (ψ.symm τ) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm (τ * ρ))
      have h2 : c (ψ.symm (σ * τ)) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm τ) -
          (c (ψ.symm τ) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm (τ * ρ))) =
          -(c (ψ.symm τ) (ψ.symm ρ) - c (ψ.symm (σ * τ)) (ψ.symm ρ) +
            c (ψ.symm σ) (ψ.symm (τ * ρ)) - c (ψ.symm σ) (ψ.symm τ)) := by abel
      have H' : c (ψ.symm (σ * τ)) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm τ) -
          (c (ψ.symm τ) (ψ.symm ρ) + c (ψ.symm σ) (ψ.symm (τ * ρ))) = 0 := by
        rw [h2, H, neg_zero]
      exact sub_eq_zero.mp H'
    · have hcLoc2 : SSGRoute.IsLocConst2 cA :=
        isLocConst2_conjAlgEquiv e hcLoc
      exact Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
        (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
          (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2) hcLoc2
  -- ## the `k̄ˣ`-valued cocycle is in `Z²`
  have hdZ2 : (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) ∈
      Work.AbsoluteKummer.Z2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Additive (AlgebraicClosure k)ˣ) := by
    exact (Work.AbsoluteKummer.mapZ2 χ hχ
      ⟨fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2, hcA_Z2⟩).2
  -- ## the local conditions for `d`
  have hd_fin : ∀ B : ValuationSubring (AlgebraicClosure k), SSGRoute.IsFinPlace k B →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (SSGRoute.decomp k B) b ∧
        ∀ g ∈ SSGRoute.decomp k B, ∀ h ∈ SSGRoute.decomp k B,
          d g h = g • b h - b (g * h) + b g := by
    intro B hB
    let B' : ValuationSubring Ω := B.comap (e : Ω →+* AlgebraicClosure k)
    have hB' : SSGRoute.IsFinPlace k B' := (isFinPlace_comap e B).mpr hB
    obtain ⟨bΩ, hbΩ_loc, hbΩ_cob⟩ := hcFin B' hB'
    have hH : ∀ σ : Ω ≃ₐ[k] Ω,
        ψ σ ∈ SSGRoute.decomp k B ↔ σ ∈ SSGRoute.decomp k B' :=
      fun σ => mem_decomp_comap e B σ
    refine ⟨fun σ => χ (bΩ (ψ.symm σ)), ?_, ?_⟩
    · obtain ⟨U, hU, hUf⟩ :=
        isLocConstOn_conjAlgEquiv e hH hbΩ_loc
      exact ⟨U, hU, fun g hg u hu huH => by
        show χ (bΩ (ψ.symm (g * u))) = χ (bΩ (ψ.symm g))
        have h1 : bΩ (ψ.symm (g * u)) = bΩ (ψ.symm g) := hUf g hg u hu huH
        rw [h1]⟩
    · intro g hg h hh
      have hg' : ψ.symm g ∈ SSGRoute.decomp k B' := (hH (ψ.symm g)).mp (by
        rw [MulEquiv.apply_symm_apply]; exact hg)
      have hh' : ψ.symm h ∈ SSGRoute.decomp k B' := (hH (ψ.symm h)).mp (by
        rw [MulEquiv.apply_symm_apply]; exact hh)
      have H := hbΩ_cob (ψ.symm g) hg' (ψ.symm h) hh'
      simp only [← map_mul] at H
      have htriv : (SSGRoute.res k K (ψ.symm g)) • bΩ (ψ.symm h) = bΩ (ψ.symm h) := rfl
      rw [htriv] at H
      have hfix : g • χ (bΩ (ψ.symm h)) = χ (bΩ (ψ.symm h)) := by
        show g • (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p)
          (muAddEquiv k p hμ (bΩ (ψ.symm h))) = _
        exact smul_kummerIota_eq k p hμ g (muAddEquiv k p hμ (bΩ (ψ.symm h)))
      have H2 : d g h = χ (bΩ (ψ.symm h)) - χ (bΩ (ψ.symm (g * h))) + χ (bΩ (ψ.symm g)) := by
        show χ (c (ψ.symm g) (ψ.symm h)) = _
        rw [H, map_add, map_sub]
      show d g h = g • χ (bΩ (ψ.symm h)) - χ (bΩ (ψ.symm (g * h))) + χ (bΩ (ψ.symm g))
      rw [H2, hfix]
  -- ## the involution conditions for `d`
  have hd_inv : ∀ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, τ ^ 2 = 1 →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (Subgroup.zpowers τ) b ∧
        ∀ g ∈ Subgroup.zpowers τ, ∀ h ∈ Subgroup.zpowers τ,
          d g h = g • b h - b (g * h) + b g := by
    intro τ hτ
    set σ₀ : Ω ≃ₐ[k] Ω := ψ.symm τ with hσ₀
    have hσ₀2 : σ₀ ^ 2 = 1 := by
      have h1 : ψ (σ₀ ^ 2) = 1 := by rw [map_pow, hσ₀, MulEquiv.apply_symm_apply, hτ]
      exact ψ.injective (by rw [h1, map_one])
    obtain ⟨bΩ, hbΩ_loc, hbΩ_cob⟩ := hcInv σ₀ hσ₀2
    have hH : ∀ σ : Ω ≃ₐ[k] Ω,
        ψ σ ∈ Subgroup.zpowers τ ↔ σ ∈ Subgroup.zpowers σ₀ := by
      intro σ
      have : Subgroup.zpowers τ = Subgroup.zpowers (ψ σ₀) := by rw [hσ₀, MulEquiv.apply_symm_apply]
      rw [this]
      exact conjAlgEquiv_mem_zpowers e σ₀ σ
    refine ⟨fun σ => χ (bΩ (ψ.symm σ)), ?_, ?_⟩
    · obtain ⟨U, hU, hUf⟩ :=
        isLocConstOn_conjAlgEquiv e hH hbΩ_loc
      exact ⟨U, hU, fun g hg u hu huH => by
        show χ (bΩ (ψ.symm (g * u))) = χ (bΩ (ψ.symm g))
        have h1 : bΩ (ψ.symm (g * u)) = bΩ (ψ.symm g) := hUf g hg u hu huH
        rw [h1]⟩
    · intro g hg h hh
      have hg' : ψ.symm g ∈ Subgroup.zpowers σ₀ := (hH (ψ.symm g)).mp (by
        rw [MulEquiv.apply_symm_apply]; exact hg)
      have hh' : ψ.symm h ∈ Subgroup.zpowers σ₀ := (hH (ψ.symm h)).mp (by
        rw [MulEquiv.apply_symm_apply]; exact hh)
      have H := hbΩ_cob (ψ.symm g) hg' (ψ.symm h) hh'
      simp only [← map_mul] at H
      have htriv : (SSGRoute.res k K (ψ.symm g)) • bΩ (ψ.symm h) = bΩ (ψ.symm h) := rfl
      rw [htriv] at H
      have hfix : g • χ (bΩ (ψ.symm h)) = χ (bΩ (ψ.symm h)) := by
        show g • (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p)
          (muAddEquiv k p hμ (bΩ (ψ.symm h))) = _
        exact smul_kummerIota_eq k p hμ g (muAddEquiv k p hμ (bΩ (ψ.symm h)))
      have H2 : d g h = χ (bΩ (ψ.symm h)) - χ (bΩ (ψ.symm (g * h))) + χ (bΩ (ψ.symm g)) := by
        show χ (c (ψ.symm g) (ψ.symm h)) = _
        rw [H, map_add, map_sub]
      show d g h = g • χ (bΩ (ψ.symm h)) - χ (bΩ (ψ.symm (g * h))) + χ (bΩ (ψ.symm g))
      rw [H2, hfix]
  -- ## Hasse's theorem for the Brauer group
  have hd_B2 : (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) ∈
      Work.AbsoluteKummer.B2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Additive (AlgebraicClosure k)ˣ) :=
    Work.SSGRoute.sha2_hasse.hasseUnits k d hdZ2 hd_fin hd_inv
  -- ## the class of `d` dies
  have hd_zero : Work.AbsoluteKummer.H2π (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (Additive (AlgebraicClosure k)ˣ)
      ⟨(fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
          (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2), hdZ2⟩ = 0 :=
    (Work.AbsoluteKummer.H2π_eq_zero_iff _).mpr hd_B2
  -- ## push forward along `kummerIota ∘ φ` and use the Kummer injection
  have hkey : Work.AbsoluteKummer.mapH2
      (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p) hι
      (Work.AbsoluteKummer.mapH2 (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k))) hφ
        (Work.AbsoluteKummer.H2π (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (Triv p)
          ⟨fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
            (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2, hcA_Z2⟩)) = 0 := by
    rw [← Work.AbsoluteKummer.mapH2_comp_H2π (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k)))
      (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p) hφ hι
      ⟨fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2, hcA_Z2⟩]
    rw [Work.AbsoluteKummer.mapH2_H2π]
    exact hd_zero
  have hφzero : Work.AbsoluteKummer.mapH2
      (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k))) hφ
      (Work.AbsoluteKummer.H2π (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (Triv p)
        ⟨fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
          (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2, hcA_Z2⟩) = 0 :=
    Work.SSGRoute.kummerIota_mapH2_injective k p hμ (by rw [hkey, map_zero])
  have hcA_zero : Work.AbsoluteKummer.H2π (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (Triv p)
      ⟨fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2, hcA_Z2⟩ = 0 :=
    mapH2_injective_of_addEquiv (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (muAddEquiv k p hμ) hφ hφ' (by rw [hφzero, map_zero])
  have hcA_B2 : (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2) ∈
      Work.AbsoluteKummer.B2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (Triv p) :=
    (Work.AbsoluteKummer.H2π_eq_zero_iff _).mp hcA_zero
  -- ## pull back to `Ω`
  have hcA_cob : SSGRoute.IsCoboundary2On
      (MonoidHom.id (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) ⊤
      (fun g h => cA g h) :=
    (Work.SSGRoute.bridge_mem_B2_isCoboundary2On
      (MonoidHom.id (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))
      (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => cA p.1 p.2)).mp hcA_B2
  obtain ⟨bA, hbA_loc, hbA_cob⟩ := hcA_cob
  have hHtop : ∀ σ : Ω ≃ₐ[k] Ω,
      ψ σ ∈ (⊤ : Subgroup (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) ↔
        σ ∈ (⊤ : Subgroup (Ω ≃ₐ[k] Ω)) := by
    intro σ; simp
  refine ⟨fun g => bA (ψ g), ?_, ?_⟩
  · exact isLocConstOn_conjAlgEquiv_symm e hHtop hbA_loc
  · intro g hg h hh
    have H := hbA_cob (ψ g) trivial (ψ h) trivial
    simp only [← map_mul] at H
    have htriv : (MonoidHom.id (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) (ψ g) •
        bA (ψ h) = bA (ψ h) := rfl
    rw [htriv] at H
    show c g h = (SSGRoute.res k K g) • (fun g => bA (ψ g)) h -
      (fun g => bA (ψ g)) (g * h) + (fun g => bA (ψ g)) g
    rw [show (SSGRoute.res k K g) • bA (ψ h) = bA (ψ h) from rfl]
    show c g h = bA (ψ h) - bA (ψ (g * h)) + bA (ψ g)
    simp only [cA, MulEquiv.symm_apply_apply] at H
    exact H

end Work.SSGRoute
