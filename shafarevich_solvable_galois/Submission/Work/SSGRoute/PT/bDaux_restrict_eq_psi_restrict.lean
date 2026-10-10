import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.archPairLocal
import Submission.Work.SSGRoute.PT.hpairArch_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

theorem bDaux_restrict_eq_psi_restrict
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (Lc : IntermediateField k Ω) [NumberField ↥Lc] [FiniteDimensional k ↥Lc] [IsGalois k ↥Lc]
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (L' : IntermediateField k Ω) [NumberField ↥L'] [FiniteDimensional k ↥L'] [IsGalois k ↥L']
    (hKLc : K ≤ Lc) (hKL : K ≤ L) (hKLL' : K ≤ L')
    [Algebra ↥K ↥Lc] [IsScalarTower k ↥K ↥Lc] [IsScalarTower ↥K ↥Lc Ω]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥Lc ↥L'] [IsScalarTower k ↥Lc ↥L'] [IsScalarTower ↥Lc ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    [IsScalarTower ↥K ↥Lc ↥L'] [IsScalarTower ↥K ↥L ↥L']
    (hresLc : SSGRoute.res k Lc c ≠ 1)
    (uc : NK.GlobalCFT.Place ↥Lc) (u : NK.GlobalCFT.Place ↥L) (u' : NK.GlobalCFT.Place ↥L')
    (huc : NK.GlobalCFT.Place.LiesOver uc (Work.SSGRoute.PT.archW k Ω K φ))
    (hu : NK.GlobalCFT.Place.LiesOver u (Work.SSGRoute.PT.archW k Ω K φ))
    (hu'c : NK.GlobalCFT.Place.LiesOver u' uc)
    (hu'L : NK.GlobalCFT.Place.LiesOver u' u)
    (hDuc : SSGRoute.PTExt.decompK (k := k) uc = (Subgroup.zpowers c).map (SSGRoute.res k Lc))
    (hDu' : SSGRoute.PTExt.decompK (k := k) u' = (Subgroup.zpowers c).map (SSGRoute.res k L'))
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g)
    (hresb : ∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) :
    ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u'),
      Work.SSGRoute.PT.bDaux p k Ω K T M c hc2 Lc hKLc hresLc uc hDuc b hb
          (Work.SSGRoute.PT.archW k Ω K φ) huc
          (Work.SSGRoute.decompKRestrict k ↥Lc ↥L' uc u' hu'c g)
        = ψ ((Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'L g : ↥(SSGRoute.PTExt.decompK (k := k) u))) := by
  intro g
  -- `g` lies in `D_{u'} = ⟨c⟩.map res_{L'}`, so `g = res_{L'} σ` for some `σ ∈ ⟨c⟩`.
  have hg : (g : ↥L' ≃ₐ[k] ↥L') ∈ (Subgroup.zpowers c).map (SSGRoute.res k L') := by
    rw [← hDu']
    exact g.2
  obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hg
  have hge : g = ⟨SSGRoute.res k L' σ, by rw [hDu']; exact Subgroup.mem_map_of_mem _ hσ⟩ :=
    Subtype.ext hσeq.symm
  rw [hge]
  -- the restriction `D_{u'} → D_{u_c}` sends `res_{L'} σ` to `res_{L_c} σ`
  have hres_eq : Work.SSGRoute.decompKRestrict k ↥Lc ↥L' uc u' hu'c
      ⟨SSGRoute.res k L' σ, by rw [hDu']; exact Subgroup.mem_map_of_mem _ hσ⟩
      = ⟨SSGRoute.res k Lc σ, by rw [hDuc]; exact Subgroup.mem_map_of_mem _ hσ⟩ :=
    Subtype.ext (by
      rw [Work.SSGRoute.decompKRestrict_coe]
      exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (F := k) (↥Lc) (↥L')
        (K₃ := Ω) σ).symm)
  rw [hres_eq, (bDaux_spec p k Ω K T M c hc2 Lc hKLc hresLc uc hDuc b hb
    (Work.SSGRoute.PT.archW k Ω K φ) huc).2 ⟨σ, hσ⟩, hresb σ hσ]
  -- both sides are `ψ` applied to `res_{L'} σ` restricted to `L`
  congr 1
  rw [Work.SSGRoute.decompKRestrict_coe]
  exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (F := k) (↥L) (↥L') (K₃ := Ω) σ

end Work.SSGRoute.PT
