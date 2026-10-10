import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.archPairLocalClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

namespace Work.SSGRoute.PT

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

/-! ## The descended class `PT.zLocal` of a coboundary is zero

`PT.zLocal` is the class in `H¹(D_{u_c}, zRep)` of the descended cocycle `PT.bDaux`.  If the local
`⟨c⟩`-cocycle `b` is a coboundary `σ ↦ res_{K} σ • m - m`, then `bDaux` is the coboundary
`g ↦ ρ g m - m` of the `D_{u_c}`-module `zRep`: the two actions agree because
`galRes k K L (res_L σ) = res_K σ` (`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`), and
`bDaux` is determined on all of `D_{u_c}` by its values on `res_L ⟨c⟩` (`PT.bDaux_spec`, using
`D_{u_c} = (⟨c⟩).map (res_L)`).  Hence `bDaux` lies in the `D_{u_c}`-coboundaries, `H1π` kills it,
and `eCoh` carries `0` to `0`. -/
theorem zLocal_eq_zero_of_isCoboundaryOn
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hbob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu = 0 := by
  obtain ⟨m, hm⟩ := hbob
  -- `mz` is `m` viewed in `zRep`, so that `ρ g mz - mz` is a subtraction of two elements of the
  -- coefficient module of `zRep` (the two types are definitionally equal but not syntactically).
  let mz : (zRep p k Ω K T M L u w hu : Type) := m
  -- `bDaux` is `g ↦ ρ g mz - mz` pointwise.
  have hkey : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu g
        = (groupCohomology.d₀₁ (zRep p k Ω K T M L u w hu)).hom mz g := by
    intro g
    rw [groupCohomology.d₀₁_hom_apply]
    -- every `g ∈ D_u` is `res_L σ` for some `σ ∈ ⟨c⟩`
    have hg : (g : ↥L ≃ₐ[k] ↥L) ∈ (Subgroup.zpowers c).map (SSGRoute.res k L) := by
      rw [← hDu]; exact g.2
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hg
    have h1 : bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu g = b σ := by
      have hthis : g = ⟨SSGRoute.res k L σ,
          by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ := Subtype.ext hσeq.symm
      rw [hthis, (bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu b hb w hu).2 ⟨σ, hσ⟩]
    -- the two actions on the coefficient module agree
    have h3 : (SSGRoute.res k K) σ • m - m
        = (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • m - m := by
      rw [hσeq.symm, IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥K) (↥L) σ]
    have h4 : (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • m - m
        = (zRep p k Ω K T M L u w hu).ρ g mz - mz := rfl
    exact h1.trans ((hm σ hσ).trans (h3.trans h4))
  -- hence the chosen representative of `zLocal … b` is the image of `mz` under `d₀₁`
  have hmem : (⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
      bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩ :
        groupCohomology.cocycles₁ (zRep p k Ω K T M L u w hu))
      = ⟨(groupCohomology.d₀₁ (zRep p k Ω K T M L u w hu)).hom mz,
          groupCohomology.d₀₁_apply_mem_cocycles₁ mz⟩ := by
    apply groupCohomology.cocycles₁_ext
    intro g
    exact hkey g
  have hπ : (groupCohomology.H1π (zRep p k Ω K T M L u w hu)).hom
      ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
        bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩ = 0 := by
    rw [groupCohomology.H1π_eq_zero_iff, hmem]
    exact ⟨mz, rfl⟩
  rw [zLocal, hπ, map_zero]

/-- **Clause (3) at the involution for the local single-level archimedean pairing
`PT.archPairLocal`**: the value vanishes when either argument is a coboundary on the group generated
by the involution.

Route.  Unfold with `PT.archPairLocal_unfold` and install the instances for the named level
`PT.archPairLocalL k Ω K c hc1` exactly as `PT.archPairLocal_add_left` does.  First disjunct (the
first argument a coboundary): `PT.archβc_eq_zero_iff` (needs only `ha`) gives `archβc … a = 0`, then
`Work.SSGRoute.levelPair_zero` and `PT.iota_zero` reduce the value to `χ L hKL 0 = 0`, which follows
from `hχadd` as in the hub's `hχ0`.  Second disjunct (the second argument a coboundary of
`m : VFcoef p M T`): it descends to the coboundary `g ↦ ρ g m - m` on `D_u` (the actions agree
because `PTExt.galRes k (K) (L) (res k L σ) = res k K σ`), so the chosen `PT.bDaux` represents the
zero class and one gets the new lemma `PT.zLocal … b = 0`: `bDaux` is determined by
`bDaux (res σ) = b σ` on the whole of `D_u`, hence it is `g ↦ ρ g m - m` pointwise, hence it lies in
the coboundaries of `D_u`, and `eCoh ∘ H1π` kills them.  Then `Work.SSGRoute.levelPair_zero_h` and
`PT.iota_zero` finish. -/
theorem archPairLocal_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∨
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b = 0 := by
  rcases hcob with hacob | hbcob
  · -- first argument a coboundary: `archβc c a = 0`
    rw [archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b hb]
    haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
    haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
    haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
    have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
    letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) :=
      (IntermediateField.inclusion hKL').toAlgebra
    letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [archPairValueZ,
      (archβc_eq_zero_iff p k Ω K ζ hζ hζK T hT M c hc2 hc1 φ hφ a ha).mpr hacob,
      Work.SSGRoute.levelPair_zero, Work.SSGRoute.PT.pt_iota_zero]
    exact chi_zero p k Ω K χ hχadd (archPairLocalL k Ω K c hc1) hKL'
  · -- second argument a coboundary: `zLocal … b = 0`
    rw [archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b hb]
    haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
    haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
    haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
    have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
    letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) :=
      (IntermediateField.inclusion hKL').toAlgebra
    letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [archPairValueZ,
      zLocal_eq_zero_of_isCoboundaryOn p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL'
        (archPairLocalL_res k Ω K c hc1)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
        (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ) b hb
        (archW k Ω K φ) (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ) hbcob,
      Work.SSGRoute.levelPair_zero_h, Work.SSGRoute.PT.pt_iota_zero]
    exact chi_zero p k Ω K χ hχadd (archPairLocalL k Ω K c hc1) hKL'

end Work.SSGRoute.PT
