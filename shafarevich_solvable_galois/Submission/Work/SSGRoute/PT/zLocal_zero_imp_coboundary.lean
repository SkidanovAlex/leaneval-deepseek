import Mathlib
import Submission.Work.SSGRoute.PT.archPairLocal
import Submission.Work.SSGRoute.PT.archPairLocal_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

/-- **The converse of `PT.zLocal_eq_zero_of_isCoboundaryOn`.**  If the descended class of a
`⟨c⟩`-cocycle `b` is zero in `H¹(D_u, PT.zRep …)`, then `b` is already a `⟨c⟩`-coboundary.

Reason: `zLocal b = 0` means `bDaux_b` is a `D_u`-coboundary (through the injective `eCoh` and the
cokernel description of `H1π`), say `bDaux_b = g ↦ ρ g m - m` for some `m` in the coefficient
module; evaluating at `g = res_L σ` (which exhausts `D_u` by `hDu`) and using `bDaux_spec` gives
`b σ = res_K σ • m - m`, i.e. `b` is a coboundary for the *same* `m`.  This is the hypothesis
`(eps)` of the clause-(4) perfectness assembly `PT.archPairLocal_perfect`.

Route (both reviewers confirmed, and it is the forward lemma `zLocal_eq_zero_of_isCoboundaryOn`
read backwards).  `zLocal b = eCoh 1 (decompK u) zRep (H1π ⟨bDaux b, _⟩)` with `eCoh` an `AddEquiv`
(hence injective), so `H1π ⟨bDaux b, _⟩ = 0`; `GroupCohomology.H1π_eq_zero_iff` resp. `mem_B1_iff`
then give `m` with `bDaux b = groupCohomology.d₀₁ (zRep …) m` — exactly the shape the forward proof
computes.  For `g = res k L σ` (`σ ∈ ⟨c⟩`) evaluate both sides
(`groupCohomology.d₀₁_hom_apply`, `bDaux_spec.2`) and use
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` to rewrite the `zRep`-action as `res k K σ • ·`,
giving `b σ = res k K σ • m - m`; this is `IsCoboundaryOn (res k K) (zpowers c) b` with witness `m`.
`hDu` is used only through `res k L σ ∈ D_u`. -/
theorem zLocal_zero_imp_coboundary
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
    (hzero : zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  -- `zLocal b = eCoh (H1π ⟨bDaux, _⟩)`, and `eCoh` is an additive equivalence
  have hπ : (groupCohomology.H1π (zRep p k Ω K T M L u w hu)).hom
      ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
        bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩ = 0 := by
    have h := hzero
    rw [zLocal] at h
    exact (AddEquiv.map_eq_zero_iff (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
      (zRep p k Ω K T M L u w hu))).mp h
  -- hence `bDaux` is a coboundary of the `D_u`-module `zRep`, with witness `mz`
  have hmem : bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu ∈
      LinearMap.range (groupCohomology.d₀₁ (zRep p k Ω K T M L u w hu)).hom := by
    have h := (groupCohomology.H1π_eq_zero_iff (A := zRep p k Ω K T M L u w hu)
      ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
        bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩).mp hπ
    rwa [groupCohomology.coboundaries₁] at h
  rw [LinearMap.mem_range] at hmem
  obtain ⟨mz, hmz⟩ := hmem
  -- `bDaux` agrees with `d₀₁ mz` on the whole of `D_u`
  have hfun : ∀ x : ↥(SSGRoute.PTExt.decompK (k := k) u),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu x
        = (groupCohomology.d₀₁ (zRep p k Ω K T M L u w hu)).hom mz x :=
    fun x => (congrFun hmz x).symm
  -- the coefficient module of `zRep` is definitionally `VFcoef p M T`
  let m : VFcoef p M T := mz
  refine ⟨m, fun g hg => ?_⟩
  have hspec := (bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu b hb w hu).2
    (⟨g, hg⟩ : ↥(Subgroup.zpowers c))
  have hpt := hfun (⟨SSGRoute.res k L g,
    by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩ :
      ↥(SSGRoute.PTExt.decompK (k := k) u))
  rw [← hspec, hpt, groupCohomology.d₀₁_hom_apply]
  -- the two actions agree: `zRep` acts through `galRes`, and
  -- `galRes k K L (res k L g) = res k K g`
  have hρ : (zRep p k Ω K T M L u w hu).ρ ⟨SSGRoute.res k L g,
      by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩ mz = (SSGRoute.res k K) g • m := by
    rw [show (zRep p k Ω K T M L u w hu).ρ ⟨SSGRoute.res k L g,
        by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩ mz
        = (SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L g)) • m from rfl]
    exact congrArg (fun x => x • m)
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥K) (↥L) g).symm
  rw [hρ]

end Work.SSGRoute.PT
