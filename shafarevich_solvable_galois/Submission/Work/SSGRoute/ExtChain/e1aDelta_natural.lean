import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 4000000

/-!
# Naturality of the `E1a` connecting map `δ` in the coefficient

The map `e1aDelta N = (e1aSES N).deltaH2` of `ExtChain/ChainGamma.lean` is the connecting map of
the dualised canonical resolution.  The present file proves its naturality in the coefficient: for
a morphism `F : N₂ ⟶ N₁` of representations (the syzygies and covers of `F` are the canonical ones
of `ExtChain/FreeCover.lean`), the squares of the comparison of the two canonical presentations
make the connecting maps commute.  Equivalently, the `Hom`-side chain `e1aChainHom` — and hence the
full chain `e1aChain` — is natural in the coefficient.

The mathematical content is the naturality of the connecting map `δ : H¹(G,P) → H²(G,M)` of a
short exact sequence of (discrete) `G`-modules in a morphism `(α,β,γ)` of short exact sequences,
which is the workspace's `probeB8`: with lifts `b` of `c` and `b'` of `γ ∘ c`, the difference
`b' - β b` takes values in `ker π' = range ι'`, so `k := ι'⁻¹(b' - β b)` is a locally constant
`1`-cochain and `d¹ k = δ'(γ c) - α (δ c)`; injectivity of `ι'` finishes.  This is stated and
proved as `deltaH2_natural` below and then applied to the canonical resolutions.
-/

/-- **Naturality of the connecting map `δ : H¹(G,P) → H²(G,M)` of a short exact sequence of
discrete `G`-modules** in a morphism `(α, β, γ)` of short exact sequences (the commuting of the two
squares being the hypotheses `hβι` and `hγπ`). -/
theorem deltaH2_natural {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P M' N' P' : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [DistribMulAction G M'] [DistribMulAction G N'] [DistribMulAction G P']
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (S' : Work.AbsoluteKummer.ShortExactSeq G M' N' P')
    (α : M →+ M') (β : N →+ N') (γ : P →+ P')
    (hα : Work.GroupCohomology.IsEquivariant G α)
    (hβ : Work.GroupCohomology.IsEquivariant G β)
    (hγ : Work.GroupCohomology.IsEquivariant G γ)
    (hβι : ∀ m : M, β (S.iota m) = S'.iota (α m))
    (hγπ : ∀ n : N, γ (S.pi n) = S'.pi (β n))
    (x : Work.AbsoluteKummer.H1 G P) :
    S'.deltaH2 (Work.AbsoluteKummer.mapH1 γ hγ x) =
      Work.AbsoluteKummer.mapH2 α hα (S.deltaH2 x) := by
  induction x using Work.AbsoluteKummer.SES.H1_induction_on with
  | h c =>
    rw [Work.AbsoluteKummer.mapH1_H1π, S'.deltaH2_H1π, S.deltaH2_H1π,
      Work.AbsoluteKummer.mapH2_H2π]
    rw [Work.AbsoluteKummer.H2π_eq_iff]
    -- The chosen lift `b'` of `γ ∘ c` and `β` of the chosen lift `b` of `c` agree after `π'`
    have hlift : ∀ g : G, S'.pi (S'.liftCochainC ((Work.AbsoluteKummer.mapZ1 γ hγ c :
        Work.AbsoluteKummer.Z1 G P') : G → P') g - β (S.liftCochainC (c : G → P) g)) = 0 := by
      intro g
      rw [map_sub, S'.pi_liftCochainC, ← hγπ (S.liftCochainC (c : G → P) g),
        S.pi_liftCochainC, Work.AbsoluteKummer.mapZ1_apply, sub_self]
    let k : G → M' := fun g => S'.iotaInv (S'.liftCochainC ((Work.AbsoluteKummer.mapZ1 γ hγ c :
        Work.AbsoluteKummer.Z1 G P') : G → P') g - β (S.liftCochainC (c : G → P) g))
    have hk : ∀ g, S'.iota (k g) = S'.liftCochainC ((Work.AbsoluteKummer.mapZ1 γ hγ c :
        Work.AbsoluteKummer.Z1 G P') : G → P') g - β (S.liftCochainC (c : G → P) g) :=
      fun g => S'.iota_iotaInv (S'.mem_range_of_mem_ker (hlift g))
    have hklc : k ∈ Work.AbsoluteKummer.C1c G M' :=
      Work.AbsoluteKummer.IsLocallyConstant.map S'.iotaInv
        ((S'.isLocallyConstant_liftCochainC (Work.AbsoluteKummer.isLocallyConstant_of_mem_Z1
            (Work.AbsoluteKummer.mapZ1 γ hγ c).2)).sub
          (Work.AbsoluteKummer.IsLocallyConstant.map β
            (S.isLocallyConstant_liftCochainC
              (Work.AbsoluteKummer.isLocallyConstant_of_mem_Z1 c.2))))
    refine (Work.AbsoluteKummer.mem_B2_iff _).mpr ⟨k, hklc, ?_⟩
    have hmap : Work.GroupCohomology.mapCochain1 G S'.iota k
        = S'.liftCochainC ((Work.AbsoluteKummer.mapZ1 γ hγ c : Work.AbsoluteKummer.Z1 G P') :
              G → P')
          - Work.GroupCohomology.mapCochain1 G β (S.liftCochainC (c : G → P)) := by
      funext g
      rw [Work.GroupCohomology.mapCochain1_apply, Pi.sub_apply,
        Work.GroupCohomology.mapCochain1_apply, hk g]
    funext p
    obtain ⟨g, h⟩ := p
    apply S'.iota_injective
    rw [AddSubgroup.coe_sub, Pi.sub_apply, map_sub]
    have hA : S'.iota ((Work.GroupCohomology.d1 G M') k (g, h))
        = (Work.GroupCohomology.d1 G N') (Work.GroupCohomology.mapCochain1 G S'.iota k) (g, h) := by
      have hh := congrFun (Work.GroupCohomology.mapCochain2_d1 G S'.iota S'.iota_equivariant k)
        (g, h)
      rwa [Work.GroupCohomology.mapCochain2_apply] at hh
    rw [hA, hmap, map_sub, Pi.sub_apply]
    congr 1
    · rw [S'.iota_deltaCocycleC (Work.AbsoluteKummer.mapZ1 γ hγ c) g h]
    · have hb2 : S'.iota ((Work.AbsoluteKummer.mapZ2 α hα (S.deltaCocycleC c) : G × G → M')
            (g, h)) = β ((Work.GroupCohomology.d1 G N) (S.liftCochainC (c : G → P)) (g, h)) := by
        rw [Work.AbsoluteKummer.mapZ2_apply, ← hβι ((S.deltaCocycleC c : G × G → M) (g, h)),
          S.iota_deltaCocycleC c g h]
      have hb3 : β ((Work.GroupCohomology.d1 G N) (S.liftCochainC (c : G → P)) (g, h))
          = (Work.GroupCohomology.d1 G N')
              (Work.GroupCohomology.mapCochain1 G β (S.liftCochainC (c : G → P))) (g, h) := by
        have hh := congrFun (Work.GroupCohomology.mapCochain2_d1 G β hβ
          (S.liftCochainC (c : G → P))) (g, h)
        rw [Work.GroupCohomology.mapCochain2_apply] at hh
        exact hh
      rw [hb2, hb3]

/-- **Naturality of the `E1a` connecting map in the coefficient.**  For `F : N₂ ⟶ N₁`, the
connecting maps of the dualised canonical resolutions of `N₁` and `N₂` commute with the maps
induced on `H¹`/`H²` by the (precomposition) maps of the comparison of the canonical presentations
`freeCover`/`freeMap`/`freeMapKernel`. -/
theorem e1aDelta_natural {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (N₁ N₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N₁.V] [Finite N₂.V]
    (F : N₂ ⟶ N₁)
    (hg₁ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom))
    (hg₃ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (Work.SSGRoute.freeMapKernel F)).toAddMonoidHom))
    (z : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N₁)))) :
    Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) N₂
        (Work.AbsoluteKummer.mapH1
          (Work.SSGRoute.precompAddHom
            (Rep.Hom.hom (Work.SSGRoute.freeMapKernel F)).toAddMonoidHom) hg₃ z)
      = Work.AbsoluteKummer.mapH2
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom) hg₁
          (Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) N₁ z) := by
  -- the comparison on the middle terms of the two canonical resolutions
  let β : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ↑N₁ →+
      Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ↑N₂ :=
    Work.SSGRoute.precompAddHom
      ((Rep.Hom.hom (Work.SSGRoute.freeMap F)).toAddMonoidHom :
        (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₂.V).V →+
          (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₁.V).V)
  have hβ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) β := by
    intro σ ψ
    dsimp only [β]
    apply AddMonoidHom.ext
    intro v
    rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    rw [Work.SSGRoute.homCoind.smul_apply]
    rw [Work.SSGRoute.homCoind.smul_apply]
    rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    congr 1
    congr 1
    exact (Rep.hom_comm_apply (Work.SSGRoute.freeMap F) ((SSGRoute.res k K) σ)⁻¹ v).symm
  -- the `iota`-square of the comparison, from `freeMap_freeCover`
  have hβι : ∀ m : Work.SSGRoute.homCoind k Ω K N₁,
      β ((Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₁).iota m) =
        (Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₂).iota
          ((Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom) m) := by
    intro m
    have hι₁ : (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) N₁).iota =
        Work.SSGRoute.precompAddHom
          (Rep.Hom.hom (Work.SSGRoute.freeCover N₁)).toAddMonoidHom :=
      (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
        (ι := N₁.V) (M := N₁) (f := Work.SSGRoute.freeCover N₁)
        (hf := Work.SSGRoute.freeCover_surjective N₁))).1
    have hι₂ : (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) N₂).iota =
        Work.SSGRoute.precompAddHom
          (Rep.Hom.hom (Work.SSGRoute.freeCover N₂)).toAddMonoidHom :=
      (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
        (ι := N₂.V) (M := N₂) (f := Work.SSGRoute.freeCover N₂)
        (hf := Work.SSGRoute.freeCover_surjective N₂))).1
    rw [hι₁, hι₂]
    dsimp only [β]
    apply AddMonoidHom.ext
    intro x
    rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply,
      Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    have hc := congrFun (congrArg
      (fun (g : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₂.V ⟶ N₁) => ⇑(Rep.Hom.hom g))
      (Work.SSGRoute.freeMap_freeCover F)) x
    rw [Rep.comp_apply, Rep.comp_apply] at hc
    exact congrArg m hc
  -- the `pi`-square of the comparison, from `freeMapKernel_ι`
  have hγπ : ∀ n : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ↑N₁,
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Work.SSGRoute.freeMapKernel F)).toAddMonoidHom)
          ((Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₁).pi n) =
        (Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₂).pi (β n) := by
    intro n
    have hπ₁ : (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) N₁).pi =
        Work.SSGRoute.precompAddHom
          (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover N₁))).toAddMonoidHom :=
      (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
        (ι := N₁.V) (M := N₁) (f := Work.SSGRoute.freeCover N₁)
        (hf := Work.SSGRoute.freeCover_surjective N₁))).2
    have hπ₂ : (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) N₂).pi =
        Work.SSGRoute.precompAddHom
          (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover N₂))).toAddMonoidHom :=
      (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
        (ι := N₂.V) (M := N₂) (f := Work.SSGRoute.freeCover N₂)
        (hf := Work.SSGRoute.freeCover_surjective N₂))).2
    rw [hπ₁, hπ₂]
    dsimp only [β]
    apply AddMonoidHom.ext
    intro x
    rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply,
      Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply,
      Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    have hc := congrFun (congrArg
      (fun (g : CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N₂) ⟶
          Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₁.V) => ⇑(Rep.Hom.hom g))
      (Work.SSGRoute.freeMapKernel_ι F)) x
    rw [Rep.comp_apply, Rep.comp_apply] at hc
    exact congrArg n hc
  -- the two canonical resolutions are compared by `(precomp F, β, precomp (freeMapKernel F))`
  exact deltaH2_natural (S := Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₁)
    (S' := Work.SSGRoute.ExtChain.e1aSES (k:=k) (Ω:=Ω) (K:=K) N₂)
    (α := Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom)
    (β := β)
    (γ := Work.SSGRoute.precompAddHom
      (Rep.Hom.hom (Work.SSGRoute.freeMapKernel F)).toAddMonoidHom)
    hg₁ hβ hg₃ hβι hγπ z

end Work.SSGRoute.ExtChain
