import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.AbsoluteKummer.All
import Submission.Work.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.sha2ToH2_restrict_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary material for the landing clause `PT.e1aBetaCan_le_ker`

Two ingredients, both used by the reduction of the landing clause
`∀ b, extToIdeles (β b) = 0` (clause 2 of E1a, the `D_A`-side local triviality):

* `akToGCH2` — the forgetful map from the *continuous* cohomology `Work.AbsoluteKummer.H2`
  (the codomain of the canonical chain `e1aChainC` and of the bridge `sha2_to_H2AK`) to the
  *abstract* cohomology `Work.GroupCohomology.H2` (the model in which the restriction maps
  `resH2` to a subgroup are available), together with its computation rule on classes of
  cocycles.

* `sha2ToH2AK_restrict_decomp_eq_zero` / `..._zpowers_eq_zero` — the *place-by-place* form of
  `Work.SSGRoute.sha2ToH2_restrict_eq_zero`.  There the bridge `Ш²(k,M) → H²(G_k,M)` is shown to
  die on the *open* subgroup `G_K = K.fixingSubgroup`; here we show — for the bridge with values in
  the continuous cohomology used by E1a, and for an **arbitrary** bridge with the computation rule
  — that it dies on the decomposition group `decomp k A` of every *finite* place `A` of `Ω` and on
  `⟨σ⟩` for every *involution* `σ`, i.e. exactly on the classes of the local conditions of
  `Z2loc`.  This is the `res_{D_A}(φ b) = 0` half of the localisation statement

    `extToIdeles y = 0  ⟺  ∀ A, res_{D_A}(e1aChainC y) = 0`

  recorded in `NOTE_e1a_next_steps.md` §2 (a) as half of the degree-2 local dictionary.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## The forgetful map `AbsoluteKummer.H2 → GroupCohomology.H2` -/

section Forget

variable (G : Type) [TopologicalSpace G] [Group G] (M : Type) [AddCommGroup M]
  [DistribMulAction G M]

/-- Every locally constant `2`-cocycle is a `2`-cocycle in the abstract sense: the forgetful map
`Z²_c(G,M) → Z²(G,M)`. -/
def akZ2ToGCZ2 : ↥(Work.AbsoluteKummer.Z2 G M) →+ ↥(Work.GroupCohomology.Z2 G M) where
  toFun c := ⟨(c : G × G → M), (AddSubgroup.mem_inf.mp c.2).1⟩
  map_zero' := by ext p; rfl
  map_add' c c' := by ext p; rfl

@[simp] theorem akZ2ToGCZ2_coe (c : ↥(Work.AbsoluteKummer.Z2 G M)) :
    ((akZ2ToGCZ2 G M c : ↥(Work.GroupCohomology.Z2 G M)) : G × G → M) = (c : G × G → M) := rfl

/-- The continuous coboundaries are abstract coboundaries. -/
theorem akB2_le_gcB2 : Work.AbsoluteKummer.B2 G M ≤ Work.GroupCohomology.B2 G M := by
  intro f hf
  obtain ⟨g, _hg, hgf⟩ := hf
  rw [Work.GroupCohomology.mem_B2_iff]
  exact ⟨g, hgf⟩

/-- **The forgetful map on cohomology**: the class of a locally constant `2`-cocycle is the class of
the same cocycle in abstract cohomology. -/
def akToGCH2 : Work.AbsoluteKummer.H2 G M →+ Work.GroupCohomology.H2 G M :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype)
    ((Work.GroupCohomology.H2π G M).comp (akZ2ToGCZ2 G M))
    (by
      intro x hx
      have hx' : ((x : ↥(Work.AbsoluteKummer.Z2 G M)) : G × G → M) ∈
          Work.AbsoluteKummer.B2 G M := AddSubgroup.mem_comap.mp hx
      have hmem : ((akZ2ToGCZ2 G M x : ↥(Work.GroupCohomology.Z2 G M)) : G × G → M) ∈
          Work.GroupCohomology.B2 G M := akB2_le_gcB2 G M hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.GroupCohomology.H2π,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hmem)

/-- Computation rule of the forgetful map: it sends the class of a locally constant `2`-cocycle to
the class of the same cocycle. -/
theorem akToGCH2_H2π (c : ↥(Work.AbsoluteKummer.Z2 G M)) :
    akToGCH2 G M (Work.AbsoluteKummer.H2π G M c) =
      Work.GroupCohomology.H2π G M (akZ2ToGCZ2 G M c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Forget

/-! ## The place-by-place restriction of the Sha bridge -/

section Restrict

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
variable [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
variable (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
variable (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
variable [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
variable (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- The `2`-cocycle of a locally trivial `2`-cocycle, as an element of the *continuous* `2`-cocycles
`AbsoluteKummer.Z2` of `G_k`.  (The membership is the two bridges
`bridge_isCocycle2_mem_Z2`/`bridge_isLocConst2_isLocallyConstant`.) -/
theorem mem_AbsoluteKummer_Z2_of_mem_Z2loc
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (x : ↥(Z2loc p k Ω K M)) :
    (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2) ∈
      @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  rw [Work.AbsoluteKummer.mem_Z2_iff]
  exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
      (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2)).mp x.2.1,
    Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
      (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2) x.2.2.1⟩

variable (M : Type) [AddCommGroup M] [Module (ZMod p) M]
variable [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

/-- **The bridge `Ш²(k,M) → H²_c(G_k,M)` dies on the decomposition group of every finite place.**

For any additive map `φ` out of `Ш²(k,M)` into the *continuous* second cohomology of
`G_k = Ω ≃ₐ[k] Ω` whose value on the class of a locally trivial `2`-cocycle `c` is `H2π c`, the
class `φ b` has vanishing image in `H²(decomp k A, M)` for every finite place `A` of `Ω`.

This is the place-by-place companion of `Work.SSGRoute.sha2ToH2_restrict_eq_zero` (which treats the
open subgroup `G_K`): the local condition in `Z2loc` at `A` is exactly a coboundary on
`decomp k A`, so the restricted cocycle is a coboundary there. -/
theorem sha2ToH2AK_restrict_decomp_eq_zero
    (φ : Sha2 p k Ω K M →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M)
        (h : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
            (DistribMulAction.compHom M (SSGRoute.res k K))),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M _ _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, h⟩)
    (b : Sha2 p k Ω K M) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) M _ _
        (DistribMulAction.compHom M (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@akToGCH2 (Ω ≃ₐ[k] Ω) _ _ M _
          (DistribMulAction.compHom M (SSGRoute.res k K)) (φ b)) = 0 := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  refine Submodule.Quotient.induction_on
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype) b fun x => ?_
  rw [hφ x.1 x.2 (mem_AbsoluteKummer_Z2_of_mem_Z2loc p k Ω K M x), akToGCH2_H2π,
    Work.GroupCohomology.resH2_H2π,
    Work.GroupCohomology.H2pi_eq_zero_iff, Work.GroupCohomology.mem_B2_iff]
  obtain ⟨a, _ha_loc, ha_eq⟩ := x.2.2.2.1 A hA
  refine ⟨fun h : SSGRoute.decomp k A => a (h : Ω ≃ₐ[k] Ω), ?_⟩
  funext q
  obtain ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ := q
  rw [Work.GroupCohomology.resZ2_coe, Work.GroupCohomology.resCochain2_apply]
  simp only [Work.GroupCohomology.d1_apply, Subgroup.smul_def]
  exact (ha_eq g hg h hh).symm

/-- **The bridge `Ш²(k,M) → H²_c(G_k,M)` dies on every involution** (the local condition at the
real places of `Ω`). -/
theorem sha2ToH2AK_restrict_zpowers_eq_zero
    (φ : Sha2 p k Ω K M →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M)
        (h : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
            (DistribMulAction.compHom M (SSGRoute.res k K))),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M _ _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, h⟩)
    (b : Sha2 p k Ω K M) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) :
    @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) M _ _
        (DistribMulAction.compHom M (SSGRoute.res k K))
        (Subgroup.zpowers σ)
        (@akToGCH2 (Ω ≃ₐ[k] Ω) _ _ M _
          (DistribMulAction.compHom M (SSGRoute.res k K)) (φ b)) = 0 := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  refine Submodule.Quotient.induction_on
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype) b fun x => ?_
  rw [hφ x.1 x.2 (mem_AbsoluteKummer_Z2_of_mem_Z2loc p k Ω K M x), akToGCH2_H2π,
    Work.GroupCohomology.resH2_H2π,
    Work.GroupCohomology.H2pi_eq_zero_iff, Work.GroupCohomology.mem_B2_iff]
  obtain ⟨a, _ha_loc, ha_eq⟩ := x.2.2.2.2 σ hσ
  refine ⟨fun h : Subgroup.zpowers σ => a (h : Ω ≃ₐ[k] Ω), ?_⟩
  funext q
  obtain ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ := q
  rw [Work.GroupCohomology.resZ2_coe, Work.GroupCohomology.resCochain2_apply]
  simp only [Work.GroupCohomology.d1_apply, Subgroup.smul_def]
  exact (ha_eq g hg h hh).symm

end Restrict

/-! ## The canonical bridge `sha2_to_H2AK` (the one entering `e1aBetaCan`) -/

section Canonical

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
variable [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
variable (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
variable (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
variable [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
variable (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
variable (E : Type) [AddCommGroup E] [Module (ZMod p) E]
variable [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]

/-- **The canonical bridge `Ш²(k,E) →+ H²_c(G_k,E)` dies on the decomposition group of every
finite place** — the instance of `sha2ToH2AK_restrict_decomp_eq_zero` at the bridge
`Classical.choose (sha2_to_H2AK …)` used by `e1aBetaCan`.  This is the `res_{D_A}(φ b) = 0` half of
the localisation statement used by the landing clause `PT.e1aBetaCan_le_ker`. -/
theorem sha2_to_H2AK_restrict_decomp_eq_zero
    (b : Sha2 p k Ω K E) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Classical.choose (sha2_to_H2AK p k Ω K E) b)) = 0 :=
  sha2ToH2AK_restrict_decomp_eq_zero p k Ω K E
    (Classical.choose (sha2_to_H2AK p k Ω K E))
    (Classical.choose_spec (sha2_to_H2AK p k Ω K E)).2 b A hA

/-- **The canonical bridge dies on every involution** of `G_k` (the local condition at the real
places of `Ω`), for the bridge entering `e1aBetaCan`. -/
theorem sha2_to_H2AK_restrict_zpowers_eq_zero
    (b : Sha2 p k Ω K E) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) :
    @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Subgroup.zpowers σ)
        (@akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Classical.choose (sha2_to_H2AK p k Ω K E) b)) = 0 :=
  sha2ToH2AK_restrict_zpowers_eq_zero p k Ω K E
    (Classical.choose (sha2_to_H2AK p k Ω K E))
    (Classical.choose_spec (sha2_to_H2AK p k Ω K E)).2 b σ hσ

end Canonical

end

end Work.SSGRoute.PT
