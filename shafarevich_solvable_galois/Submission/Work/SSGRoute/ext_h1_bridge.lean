import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.selfdual
import Submission.Work.SSGRoute.homCoindDefs
import Submission.Work.SSGRoute.homCoind_H1_free
import Submission.Work.SSGRoute.addUnits_injective
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.homRepFormulaAux
import Submission.Work.SSGRoute.homRep_unitsK_formula
import Submission.Work.SSGRoute.homRep_unitsK_formula_natural
import Submission.Work.SSGRoute.isDiscreteModule_homCoind
import Submission.Work.SSGRoute.bridge_mem_B2_isCoboundary2On
import Submission.Work.SSGRoute.cohomology_bridge
import Submission.Work.SSGRoute.h1_equiv_of_equiv
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.SSGRoute.homCoind_H0_restrict_ker_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E1c `ext_h1_bridge` — `H¹(k,E) ≅ Ext¹_G(E', Kˣ)` -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

universe u v

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct
open scoped Classical
open Filter
open scoped Topology

/-! ## Generic exactness lemmas -/

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- **Ext side.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₂` projective, the
connecting map `Ext⁰(X₁,Y) → Ext¹(X₃,Y)` is surjective with kernel the image of the map
`Ext⁰(X₂,Y) → Ext⁰(X₁,Y)`. -/
theorem ext_connecting_range_ker {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] :
    (hS.extClass.precomp Y (by norm_num : 1 + 0 = 1)).range = ⊤ ∧
    (hS.extClass.precomp Y (by norm_num : 1 + 0 = 1)).ker =
      ((Abelian.Ext.mk₀ S.f).precomp Y (by norm_num : 0 + 0 = 0)).range := by
  haveI : Subsingleton (Abelian.Ext S.X₂ Y 1) := Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  constructor
  · rw [AddMonoidHom.range_eq_top]
    intro y
    have hzero : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hzero
      (n₀ := 0) (by norm_num : 1 + 0 = 1)
    exact ⟨x, by simpa using hx⟩
  · apply le_antisymm
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x
        (n₁ := 1) (by norm_num : 1 + 0 = 1) hx
      exact ⟨w, by simpa using hw⟩
    · rintro x ⟨w, rfl⟩
      rw [AddMonoidHom.mem_ker]
      simpa using hS.extClass_comp_assoc (Y := Y) w

end Generic

/-- **Cohomology side.** For a short exact sequence `0 → M → N → P → 0` of discrete `G`-modules
with `H¹(G,N) = 0`, the connecting map `δ : H⁰(G,P) → H¹(G,M)` is surjective with kernel the image
of `H⁰(G,N) → H⁰(G,P)`. -/
theorem coh_connecting_range_ker {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    [Subsingleton (Work.AbsoluteKummer.H1 G N)] :
    S.delta.range = ⊤ ∧
      S.delta.ker = (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range := by
  have hzero : Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant = 0 :=
    AddMonoidHom.ext (fun x => Subsingleton.elim _ _)
  constructor
  · have h : S.delta.range = (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).ker :=
      le_antisymm S.range_delta_le_ker_mapH1 (Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta S)
    rw [h, hzero, AddMonoidHom.ker_zero]
  · exact le_antisymm (Work.AbsoluteKummer.SES.ker_le_range_mapH0 S) S.range_mapH0_le_ker_delta

/-! ## The units of `Ω` as a discrete Galois module -/






/-! ## The action on `Ωˣ` and Hilbert 90 for `Gal(Ω/K)` -/



section H90
variable {kk : Type} [Field kk] {ΩΩ : Type} [Field ΩΩ] [Algebra kk ΩΩ] [IsGalois kk ΩΩ]

/-- Noether's Hilbert 90 for `Gal(Ω/K)`: a locally constant crossed homomorphism into `Ωˣ` is a
coboundary. -/
theorem exists_div_gal_omega (f : (ΩΩ ≃ₐ[kk] ΩΩ) → ΩΩˣ)
    (hf : ∀ σ τ : ΩΩ ≃ₐ[kk] ΩΩ, f (σ * τ) = f σ * umap kk ΩΩ σ (f τ))
    (hc : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ b : ΩΩˣ, ∀ σ : ΩΩ ≃ₐ[kk] ΩΩ, f σ = umap kk ΩΩ σ b / b := by
  have hf1 : f 1 = 1 := by
    have h := hf 1 1
    rw [one_mul, umap_one] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  obtain ⟨U, hUopen, h1U, hUc⟩ := hc 1
  have hfU : ∀ y ∈ U, f y = 1 := fun y hy => by rw [hUc y hy, hf1]
  have hUn : U ∈ 𝓝 (1 : ΩΩ ≃ₐ[kk] ΩΩ) := hUopen.mem_nhds h1U
  haveI hNor : Normal kk ΩΩ := IsGalois.to_normal
  obtain ⟨M, hMfin, hMnorm, hMsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal kk ΩΩ U).mp hUn
  haveI := hMfin
  haveI := hMnorm
  have hker : (AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M).ker = M.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker M
  have hNnormal : M.fixingSubgroup.Normal := by
    rw [← hker]; exact MonoidHom.normal_ker _
  have hfN : ∀ n ∈ M.fixingSubgroup, f n = 1 := fun n hn => hfU n (hMsub hn)
  have hNinv : ∀ (a n : ΩΩ ≃ₐ[kk] ΩΩ), n ∈ M.fixingSubgroup → f (a * n) = f a := by
    intro a n hn
    rw [hf a n, hfN n hn, map_one, mul_one]
  have hmem : ∀ a : ΩΩ ≃ₐ[kk] ΩΩ, (f a : ΩΩ) ∈ M := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro n hn
    show n (f a : ΩΩ) = (f a : ΩΩ)
    have h1 : umap kk ΩΩ n (f a) = f (n * a) := by rw [hf n a, hfN n hn, one_mul]
    have h2 : f (n * a) = f a := by
      have heq : n * a = a * (a⁻¹ * n * a) := by group
      rw [heq, hNinv a (a⁻¹ * n * a) (hNnormal.conj_mem n hn a⁻¹)]
    have h3 := (umap_coe kk ΩΩ n (f a)).symm
    rw [h1, h2] at h3
    exact h3
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M) :=
    AlgEquiv.restrictNormalHom_surjective ΩΩ
  let lift : (↥M ≃ₐ[kk] ↥M) → (ΩΩ ≃ₐ[kk] ΩΩ) := fun χ => Classical.choose (hsurj χ)
  have hlift : ∀ χ, AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M (lift χ) = χ :=
    fun χ => Classical.choose_spec (hsurj χ)
  have happ : ∀ (χ : ↥M ≃ₐ[kk] ↥M) (x : ↥M),
      (((χ x) : ↥M) : ΩΩ) = (lift χ) (x : ΩΩ) := by
    intro χ x
    conv_lhs => rw [← hlift χ]
    exact AlgEquiv.restrictNormalHom_apply (F := kk) (K₁ := ΩΩ) M (lift χ) x
  let g : (↥M ≃ₐ[kk] ↥M) → (↥M)ˣ := fun χ =>
    Units.mk0 ⟨(f (lift χ) : ΩΩ), hmem (lift χ)⟩ (by
      intro h0
      have h1 : (f (lift χ) : ΩΩ) = 0 := congrArg (fun x : ↥M => (x : ΩΩ)) h0
      exact Units.ne_zero (f (lift χ)) h1)
  have hgcoc : ∀ χ ψ,
      ((g (χ * ψ) : (↥M)ˣ) : ↥M) = ((g χ : (↥M)ˣ) : ↥M) * χ ((g ψ : (↥M)ˣ) : ↥M) := by
    intro χ ψ
    apply Subtype.ext
    have hK : (f (lift (χ * ψ)) : ΩΩ) =
        (f (lift χ) : ΩΩ) * (lift χ) (f (lift ψ) : ΩΩ) := by
      have hn : (lift (χ * ψ))⁻¹ * (lift χ * lift ψ) ∈ M.fixingSubgroup := by
        rw [← hker, MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hlift]
        group
      have hA : f (lift (χ * ψ)) = f (lift χ * lift ψ) := by
        have h := hNinv (lift (χ * ψ)) ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) hn
        have heq : lift (χ * ψ) * ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) =
            lift χ * lift ψ := by group
        rw [heq] at h
        exact h.symm
      rw [hA, hf (lift χ) (lift ψ)]
      rfl
    simp only [g, Units.val_mk0, Subtype.coe_mk] at hK ⊢
    push_cast
    rw [hK]
    congr 1
    push_cast
    exact (happ χ ⟨(f (lift ψ) : ΩΩ), hmem (lift ψ)⟩).symm
  obtain ⟨β, hβ⟩ := Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom g hgcoc
  refine ⟨Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β, fun σ => ?_⟩
  set χ := AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M σ with hχ
  have hmemσ : (lift χ)⁻¹ * σ ∈ M.fixingSubgroup := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hlift, hχ]
    group
  have hσ : f σ = f (lift χ) := by
    conv_lhs => rw [show σ = lift χ * ((lift χ)⁻¹ * σ) by group]
    rw [hf (lift χ) ((lift χ)⁻¹ * σ), hfN ((lift χ)⁻¹ * σ) hmemσ, map_one, mul_one]
  rw [hσ]
  apply Units.ext
  have hL : (f (lift χ) : ΩΩ) = algebraMap ↥M ΩΩ ((g χ : (↥M)ˣ) : ↥M) := rfl
  have h := congrArg (algebraMap ↥M ΩΩ) (hβ χ)
  simp only [map_div₀] at h
  rw [hL, h, Units.val_div_eq_div_val]
  congr 1
  · rw [show ((umap kk ΩΩ σ (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β) : ΩΩˣ) : ΩΩ) =
        σ (Units.val (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β)) from umap_coe kk ΩΩ _ _]
    rw [show Units.val (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β) = ((↑β : ↥M) : ΩΩ) from by
      rw [Units.coe_map]; rfl]
    exact AlgEquiv.restrictNormalHom_apply M σ (↑β : ↥M)

end H90


section EAct

/-- The `Gal(Ω/k)`-action on `E` through `Gal(K/k)`. -/
noncomputable def resActE (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (E : Type) [AddCommGroup E]
    [DistribMulAction (K ≃ₐ[k] K) E] : DistribMulAction (Ω ≃ₐ[k] Ω) E where
  smul σ e := (SSGRoute.res k K σ) • e
  one_smul e := by
    show (SSGRoute.res k K 1) • e = e
    rw [map_one]; exact one_smul _ e
  mul_smul σ τ e := by
    show (SSGRoute.res k K (σ * τ)) • e = (SSGRoute.res k K σ) • (SSGRoute.res k K τ) • e
    rw [map_mul]; exact mul_smul _ _ e
  smul_zero σ := smul_zero _
  smul_add σ e e' := smul_add _ _ _

end EAct





attribute [local instance 10000] homCoind.instDistribMulActionAlgEquiv

/-! ## Forcing the conjugation action on `homCoind`

`homCoind k Ω K M` is an abbreviation for `M.V →+ Additive Ωˣ`, so type class search sometimes
finds the *pointwise* `DistribMulAction` on `AddMonoidHom` (`(σ • φ) x = σ • φ x`) rather than the
conjugation action `(σ • φ) x = σ • φ (σ⁻¹ • x)` defined in `homCoindDefs`.  Every lemma of the
`homCoind` chapter (`homRep_unitsK_formula`, `homCoind_H0_restrict_ker`, …) is stated for the
conjugation action, so we re-declare it here at high priority: in this file both `H⁰` and `•`
then always mean the conjugation action. -/



/-! ## Auxiliary `Ext`-calculus -/

section ExtCalc

/-- The canonical identification `Ext⁰(X,Y) ≃+ (X ⟶ Y)` sends `mk₀ f` back to `f`. -/
lemma ext_addEquiv₀_mk₀_ehb {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C}
    (f : X ⟶ Y) :
    Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f :=
  (Abelian.Ext.mk₀_bijective X Y).1 (by rw [Abelian.Ext.mk₀_addEquiv₀_apply])

/-- Precomposition with `mk₀ u` on `Ext⁰` is precomposition with `u` on morphisms. -/
lemma ext_precomp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z : C}
    (u : X ⟶ Y) (f : Y ⟶ Z) :
    (Abelian.Ext.mk₀ u).precomp Z (by norm_num : 0 + 0 = 0) (Abelian.Ext.mk₀ f) =
      Abelian.Ext.mk₀ (u ≫ f) := by
  change (Abelian.Ext.mk₀ u).comp (Abelian.Ext.mk₀ f) (zero_add 0) = Abelian.Ext.mk₀ (u ≫ f)
  exact Abelian.Ext.mk₀_comp_mk₀ u f

end ExtCalc

/-! ## Bridging the cocycle predicates with the cohomology groups -/

section CohBridge2

/-- A cocycle which is invariant under an open subgroup is a continuous `1`-cocycle. -/
lemma mem_absZ1_of_isCocycleOn_isLocConstOn {Γ G M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [Group G] [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G)
    {b : Γ → M} (hb : SSGRoute.IsCocycleOn act ⊤ b)
    (hl : SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) b) :
    b ∈ @Work.AbsoluteKummer.Z1 Γ M _ _ _ (DistribMulAction.compHom M act) := by
  show b ∈ (@Work.GroupCohomology.Z1 Γ M _ _ (DistribMulAction.compHom M act)) ⊓
    Work.AbsoluteKummer.C1c Γ M
  exact ⟨(isCocycleOn_iff_mem_Z1 act b).mp hb,
    Work.SSGRoute.top_isLocallyConstant_of_isLocConstOn hl⟩

/-- `b ∈ B¹` iff its class in `Z¹` vanishes. -/
lemma mem_absB1_iff_exists {Γ M : Type} [TopologicalSpace Γ] [Group Γ] [AddCommGroup M]
    [DistribMulAction Γ M] (b : Γ → M) :
    b ∈ Work.AbsoluteKummer.B1 Γ M ↔
      ∃ (hf : b ∈ Work.GroupCohomology.Z1 Γ M),
        Work.GroupCohomology.H1π Γ M ⟨b, hf⟩ = 0 := by
  show b ∈ Work.GroupCohomology.B1 Γ M ↔ _
  constructor
  · intro hb
    have hbZ := Work.GroupCohomology.B1_le_Z1 Γ M hb
    exact ⟨hbZ, (h1pi_eq_zero_iff ⟨b, hbZ⟩).mpr hb⟩
  · rintro ⟨hf, h0⟩
    exact (h1pi_eq_zero_iff ⟨b, hf⟩).mp h0

end CohBridge2

/-! ## The duality `E ≃+ Hom(E^∨(1), Ωˣ)` in `homCoind` shape -/

section Duality

/-- `dualPairingEquiv` in the shape needed by the assembly: an equivariant additive isomorphism
`E ≃+ homCoind k Ω K (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗ T)))`. -/
theorem dualPairingEquiv_homCoind (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∃ Φ : E ≃+ homCoind k Ω K (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))),
      ∀ (σ : Ω ≃ₐ[k] Ω) (e : E), Φ ((SSGRoute.res k K σ) • e) = σ • Φ e := by
  obtain ⟨Φ, hΦ⟩ := SelfDual.dualPairingEquiv p k Ω K ζ hζ hζK T hT E
  exact ⟨Φ, fun σ e => by
    apply AddMonoidHom.ext
    intro x
    rw [homCoind.smul_apply]
    exact hΦ σ e x⟩

end Duality

/-! ## The target -/

/-- **E1c.** `H¹(k, E) ≅ Ext¹_{Gal(K/k)}(E', Kˣ)` for `E' = DualMod p (E ⊗ T) = E^∨(1)`
(Hochschild–Serre for `Ext_{G_k}(E', Ω̄ˣ)` with Hilbert 90): there is a map from continuous
`1`-cochains of `G_k` to `Ext¹_G(E', Kˣ)`, additive on cocycles, whose kernel on cocycles is the
coboundaries and which is onto. -/
theorem ext_h1_bridge (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∃ β : ((Ω ≃ₐ[k] Ω) → E) →
        Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
          β (b + b') = β b + β b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b)) ∧
      ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
        SSGRoute.IsLocConstOn ⊤ b ∧ β b = y := by
  classical
  -- ===== the Ext side =====
  let E' : Type := DualMod p (E ⊗[ZMod p] T)
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hTf : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  haveI hATf : Module.Finite (ZMod p) (E ⊗[ZMod p] T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI hE'fin : Finite E' :=
    (Module.finite_iff_finite (R := ZMod p)).mp
      (Module.Finite.linearMap (ZMod p) (ZMod p) (E ⊗[ZMod p] T) (ZMod p))
  let F : Rep.{0} Coeff (K ≃ₐ[k] K) := Rep.free Coeff (K ≃ₐ[k] K) E'
  let X3 : Rep.{0} Coeff (K ≃ₐ[k] K) := modRep (K ≃ₐ[k] K) E'
  let pic : F ⟶ X3 := Rep.freeLift Coeff (K ≃ₐ[k] K) X3 (fun e => e)
  have hpic : Epi pic := by
    rw [Rep.epi_iff_surjective]
    intro a
    refine ⟨Finsupp.single a (MonoidAlgebra.single 1 1), ?_⟩
    show Rep.Hom.hom pic (Finsupp.single a (MonoidAlgebra.single 1 1)) = a
    rw [show Rep.Hom.hom pic = Representation.freeLift X3.ρ (fun e => e) from rfl]
    erw [Representation.freeLift_single_single]
    simp only [map_one]
    exact one_smul _ a
  let S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) :=
    ShortComplex.mk (Limits.kernel.ι pic) pic (Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  have hExt := ext_connecting_range_ker hS (unitsK k K)
  -- the connecting map `Ext⁰(R,Kˣ) ↠ Ext¹(E',Kˣ)` and its kernel
  let ΦE : Abelian.Ext S.X₁ (unitsK k K) 0 →+ Abelian.Ext X3 (unitsK k K) 1 :=
    hS.extClass.precomp (unitsK k K) (by norm_num : 1 + 0 = 1)
  have hΦEsurj : Function.Surjective ΦE := (AddMonoidHom.range_eq_top).mp hExt.1
  let pre : Abelian.Ext S.X₂ (unitsK k K) 0 →+ Abelian.Ext S.X₁ (unitsK k K) 0 :=
    (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
  have hΦEker : ΦE.ker = pre.range := hExt.2
  -- ===== the cohomology side =====
  have hfsurj : Function.Surjective (Rep.Hom.hom pic) := (Rep.epi_iff_surjective pic).mp hpic
  let uHom : S.X₁.V →+ S.X₂.V :=
    { toFun := fun x => Rep.Hom.hom S.f x
      map_zero' := map_zero (Rep.Hom.hom S.f)
      map_add' := fun a b => map_add (Rep.Hom.hom S.f) a b }
  let gFun : homCoind k Ω K S.X₂ →+ homCoind k Ω K S.X₁ :=
    { toFun := fun φ => φ.comp uHom
      map_zero' := by ext x; rfl
      map_add' := by intro a b; ext x; rfl }
  have hG : ∀ (ψ : homCoind k Ω K S.X₂) (y : S.X₁.V),
      gFun ψ y = ψ (Rep.Hom.hom S.f y) := fun ψ y => rfl
  have gFun_mem : ∀ φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)),
      gFun φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) := by
    intro φ hφ
    intro σ
    apply AddMonoidHom.ext
    intro x
    rw [show (σ • (gFun φ)) x
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)) from rfl]
    have h1 : gFun φ (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)
        = φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)) := by
      rw [hG, Rep.hom_comm_apply]
    have h3 : homCoind.smulHom (k := k) (Ω := Ω) σ
          ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x))
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x))) := by
      rw [h1]
    have h2 : homCoind.smulHom (k := k) (Ω := Ω) σ
          (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)))
        = φ (Rep.Hom.hom S.f x) :=
      DFunLike.congr_fun (hφ σ) (Rep.Hom.hom S.f x)
    rw [h3, h2]
    exact (hG φ x).symm
  let g : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) →+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (gFun.comp (AddSubgroup.subtype _)).codRestrict _ (fun φ => gFun_mem φ.1 φ.2)
  have hg : ∀ (ψ : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)))
      (x : S.X₁.V), Subtype.val (g ψ) x = Subtype.val ψ (Rep.Hom.hom S.f x) := by
    intro ψ x
    exact hG (ψ : homCoind k Ω K S.X₂) x
  haveI hsub : Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) E')) _ _
      (homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) E'))
      (homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) E'))) :=
    homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := E')
  obtain ⟨δ, hδsurj, hδker⟩ :=
    homCoind_H0_restrict_ker_conj (k := k) (Ω := Ω) (K := K) (ι := E') pic hfsurj g hg
  -- ===== the two `H⁰`'s are the same =====
  obtain ⟨ΦR, hΦR⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₁
  obtain ⟨ΦF, hΦF⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₂
  have hnat := homRep_unitsK_formula_natural (k := k) (Ω := Ω) (K := K) S.f ΦR ΦF hΦR hΦF g hg
  let ΨR : Abelian.Ext S.X₁ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (Abelian.Ext.addEquiv₀).trans ΦR
  let ΨF : Abelian.Ext S.X₂ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) :=
    (Abelian.Ext.addEquiv₀).trans ΦF
  have hpre1 : ∀ f : S.X₂ ⟶ unitsK k K,
      pre (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f) := by
    intro f
    change (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
        (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f)
    rw [ext_precomp_mk₀]
  have hΨR : ∀ f : S.X₁ ⟶ unitsK k K, ΨR (Abelian.Ext.mk₀ f) = ΦR f := by
    intro f
    show ΦR (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦR f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hΨF : ∀ f : S.X₂ ⟶ unitsK k K, ΨF (Abelian.Ext.mk₀ f) = ΦF f := by
    intro f
    show ΦF (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦF f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hpre : ∀ x : Abelian.Ext S.X₂ (unitsK k K) 0, ΨR (pre x) = g (ΨF x) := by
    intro x
    rw [show x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) from
      (Abelian.Ext.mk₀_addEquiv₀_apply x).symm]
    rw [hpre1 (Abelian.Ext.addEquiv₀ x), hΨR (S.f ≫ Abelian.Ext.addEquiv₀ x),
      hΨF (Abelian.Ext.addEquiv₀ x)]
    exact hnat (Abelian.Ext.addEquiv₀ x)
  have hmap : AddSubgroup.map ΨR.toAddMonoidHom ΦE.ker = δ.ker := by
    rw [hΦEker, hδker]
    have h1 : AddSubgroup.map ΨR.toAddMonoidHom pre.range =
        (ΨR.toAddMonoidHom.comp pre).range := by
      rw [AddMonoidHom.range_eq_map pre, AddSubgroup.map_map,
        ← AddMonoidHom.range_eq_map (ΨR.toAddMonoidHom.comp pre)]
    rw [h1]
    have h2 : ΨR.toAddMonoidHom.comp pre = g.comp ΨF.toAddMonoidHom := by
      apply AddMonoidHom.ext
      intro y
      exact hpre y
    rw [h2, AddMonoidHom.range_eq_map (g.comp ΨF.toAddMonoidHom), ← AddSubgroup.map_map,
      ← AddMonoidHom.range_eq_map ΨF.toAddMonoidHom,
      (AddMonoidHom.range_eq_top).mpr ΨF.surjective]
    exact (AddMonoidHom.range_eq_map g).symm
  -- ===== collecting the isomorphism `Ext¹ ≃+ H¹(Γ, homCoind (E'))` =====
  let e1 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+ Abelian.Ext X3 (unitsK k K) 1 :=
    QuotientAddGroup.quotientKerEquivOfSurjective ΦE hΦEsurj
  let e2 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker :=
    QuotientAddGroup.congr _ _ ΨR hmap
  let e3 : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X3) _ _
          (homCoind.instAddCommGroup X3) (homCoind.instDistribMulActionAlgEquiv X3) :=
    QuotientAddGroup.quotientKerEquivOfSurjective δ hδsurj
  have hExtHomCoind : Abelian.Ext X3 (unitsK k K) 1 ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X3) _ _
          (homCoind.instAddCommGroup X3) (homCoind.instDistribMulActionAlgEquiv X3) :=
    e1.symm.trans (e2.trans e3)
  -- ===== the coefficient change `H¹(Γ,E) ≃+ H¹(Γ, homCoind (E'))` =====
  obtain ⟨Φd, hΦd⟩ := dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  obtain ⟨e0⟩ := h1_equiv_of_equiv Φd hΦd
  let Ψ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) E ≃+ Abelian.Ext X3 (unitsK k K) 1 :=
    e0.trans hExtHomCoind.symm
  -- ===== the map `β` =====
  let β : ((Ω ≃ₐ[k] Ω) → E) → Abelian.Ext X3 (unitsK k K) 1 := fun b =>
    if h : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E then
      Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, h⟩)
    else 0
  have hβ_eq : ∀ z : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E,
      β z.1 = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E z) := by
    intro z
    exact dif_pos z.2
  refine ⟨β, ?_, ?_, ?_⟩
  · intro b b' hb hbl hb' hbl'
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hbl
    have hbZ' : b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb' hbl'
    have hbbZ : b + b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).add_mem hbZ hbZ'
    have h1 : β (b + b') = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b + b', hbbZ⟩) :=
      dif_pos hbbZ
    have h2 : β b = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := dif_pos hbZ
    have h3 : β b' = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b', hbZ'⟩) := dif_pos hbZ'
    have hπ : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b + b', hbbZ⟩
        = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩
          + Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b', hbZ'⟩ := by
      rw [show (⟨b + b', hbbZ⟩ : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E) =
          ⟨b, hbZ⟩ + ⟨b', hbZ'⟩ from Subtype.ext rfl, map_add]
    rw [h1, h2, h3, hπ]
    exact map_add Ψ _ _
  · intro b hb hbl
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hbl
    have h1 : β b = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := dif_pos hbZ
    rw [h1, show Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) = 0 ↔
        Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩ = 0 from Ψ.map_eq_zero_iff]
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff]
    rw [mem_absB1_iff_exists]
    exact (isCoboundaryOn_top_iff_class_eq_zero (SSGRoute.res k K) b).symm
  · intro y
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) E).comap
        (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).subtype) (Ψ.symm y)
    refine ⟨z.1, ?_, ?_, ?_⟩
    · exact (isCocycleOn_iff_mem_Z1 (SSGRoute.res k K) z.1).mpr z.2.1
    · exact Work.SSGRoute.top_isLocConstOn_of_isLocallyConstant z.2.2
    · rw [hβ_eq z]
      have hz' : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E z = Ψ.symm y := hz
      rw [hz', AddEquiv.apply_symm_apply]

end Work.SSGRoute
