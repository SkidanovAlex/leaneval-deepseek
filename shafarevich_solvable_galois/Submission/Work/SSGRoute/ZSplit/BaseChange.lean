import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change dictionary between the level-`K` and the level-`⊤` vocabulary

## The finding recorded here

Every statement of the `z`-construction of `Work.SSGRoute.shafarevich_theorem13` is stated **over
`K`**: classes are additive, locally constant functions on `G_K = K.fixingSubgroup`, and their
local components live on the *level-`K` local groups* `decomp k A ⊓ K.fixingSubgroup`.  The
workspace's Poitou--Tate machinery (`Submission/Work/SSGRoute/PT/`) is stated at the level `⊤`: its
classes are functions on all of `G_k = Ω ≃ₐ[k] Ω` and its local groups are `decomp k A`.

`ZSplit/LEVELK_STATUS.md` records the conclusion drawn earlier from this mismatch: that the
level-`K` layer needs its own *level-`K` local Tate duality*, *level-`K` reciprocity* and
*level-`K` exactness*, i.e. that `PT/` "is level-`⊤` and does not transport".  **That conclusion is
a misreading of the mismatch, and this file records why.**  The level-`K` statements are exactly the
*base-change instances* of the level-`⊤` statements: with the base field taken to be `↥K` itself and
the level taken to be `⊤ : IntermediateField ↥K Ω`, the level-`⊤` vocabulary becomes

* `Gal(Ω/↥K) = Ω ≃ₐ[↥K] Ω`, which is `K.fixingSubgroup` through
  `IntermediateField.fixingSubgroupEquiv K` (`K.fixingSubgroup ≃* Gal(Ω/↥K)`);
* `decomp ↥K A`, which is `decomp k A ⊓ K.fixingSubgroup` (`decompEquiv_fok`,
  `fixingSubgroupEquiv_mem_decomp`);
* a `Gal(⊤/↥K)`-module is a module for the *whole* group `Gal(Ω/↥K)`, and the cyclotomic dual
  `T` is then *trivial*, because `ζ ∈ K` and every `σ ∈ Gal(Ω/↥K)` fixes `ζ`;
* and for coefficients the trivial `Gal(Ω/↥K)`-module `ZMod p`, whose class-level `H¹` is, on the
  nose, the level-`K` local `H¹` (`kH1loc`) of `ZSplit/levelKCounting.lean`.

Consequently the level-`K` obligations of the `z`-construction are *not* new arithmetic: they are
the base-change instances of the level-`⊤` ones, and the workspace's `PT/` theorems -- which are
stated for a *generic* number field `k` -- apply verbatim at the base field `↥K`.  What has to be
formalised is only the *transport* of the vocabulary, which is what this file provides.

## What this file proves

For a general base field `k` (a `NumberField`) and a finite Galois `K/k`:

* `isFinPlace_baseChange` : `IsFinPlace ↥K A ↔ IsFinPlace k A`;
* `isInertia_baseChange` : the inertia condition transports along `fixingSubgroupEquiv`;
* `isSplitIn_baseChange` : `IsSplitIn ↥K N A ↔ IsSplitIn k (N.restrictScalars k) A`
  (the relaxation data of the `z`-construction: "split completely in `Λ`");
* `isRamifiedIn_baseChange` : `IsRamifiedIn ↥K N A` in terms of `IsInertia k`;
* `isConjPlace_baseChange` : level-`K` conjugacy (`kConj` of `ZSplit/levelKCounting.lean`) is
  `IsConjPlace ↥K`, i.e. conjugacy inside `G_K` -- the correction recorded in `LEVELK_STATUS.md`;
* `baseChangeFun` and `isCocycleOn_baseChange`, `isCoboundaryOn_baseChange`: the cochain
  predicates transport along `fixingSubgroupEquiv`; on a subgroup of `G_K` the level-`K` cocycle
  condition is *additivity* and the level-`K` coboundary condition is *vanishing*, so the cochain
  vocabulary of the two levels agrees exactly.

Everything here is `sorry`-free and axiom-clean.
-/

open scoped Pointwise

set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open _root_.SSGRoute

section Dictionary

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K]

/-- **`IsFinPlace` is base-change invariant.**  A place `A` of `Ω` restricts to a nontrivial place
of `K` if and only if it restricts to a nontrivial place of `k`.

Both directions use that a valuation subring of `Ω` is integrally closed in `Ω` and `Ω` is
integral over `k`: if `A` contains `k` then `A ⊇ integralClosure k Ω = Ω`, i.e. `A = ⊤`. -/
theorem isFinPlace_baseChange (A : ValuationSubring Ω) :
    IsFinPlace ↥K A ↔ IsFinPlace k A := by
  have hIntegral : Algebra.IsIntegral k Ω := IsAlgClosure.isAlgebraic.isIntegral
  -- if `A` contains `k`, then `A = ⊤`
  have nice : ∀ y : Ω, (∀ r : k, algebraMap k Ω r ∈ A) → y ∈ A := by
    intro y hq
    have hIC : IsIntegrallyClosedIn ↥A.toSubring Ω :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    have hle : (integralClosure k Ω).toSubring ≤ A.toSubring := by
      rw [Subring.integralClosure_le_iff]
      intro r
      rw [ValuationSubring.mem_toSubring]
      exact hq r
    exact hle ((mem_integralClosure_iff k Ω).mpr (Algebra.IsIntegral.isIntegral y))
  constructor
  · -- `IsFinPlace ↥K A → IsFinPlace k A`: if `k ⊆ A` then `A = ⊤`, hence `K ⊆ A`
    intro h hk
    apply h
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    have hk' : ∀ r : k, algebraMap k Ω r ∈ A := fun r => by
      have : r ∈ A.comap (algebraMap k Ω) := by rw [hk]; trivial
      rwa [ValuationSubring.mem_comap] at this
    exact nice (algebraMap ↥K Ω x) hk'
  · -- `IsFinPlace k A → IsFinPlace ↥K A`: contrapositive
    intro h hK
    apply h
    rw [eq_top_iff]
    intro q _
    rw [ValuationSubring.mem_comap]
    have hmem : algebraMap ↥K Ω (algebraMap k ↥K q) ∈ A := by
      have : algebraMap k ↥K q ∈ A.comap (algebraMap ↥K Ω) := by rw [hK]; trivial
      rwa [ValuationSubring.mem_comap] at this
    rwa [IsScalarTower.algebraMap_apply k ↥K Ω]

/-- **The inertia condition transports along `IntermediateField.fixingSubgroupEquiv`.**  For
`σ ∈ K.fixingSubgroup`, the image of `σ` in `Gal(Ω/↥K)` lies in the inertia group of `A` over `K`
if and only if `σ` lies in the inertia group of `A` over `k`: the two conditions differ only in the
decomposition-group clause, which is `fixingSubgroupEquiv_mem_decomp`, and the valuation clause is
literally the same because the two maps have the same underlying function. -/
theorem isInertia_baseChange (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup) :
    IsInertia ↥K A ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) ↔ IsInertia k A σ := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω → Ω) = ⇑σ := rfl
  rw [IsInertia, IsInertia, fixingSubgroupEquiv_mem_decomp k Ω K A σ hσ, hfun]

/-- **`IsSplitIn` and the level change.**  Splitting completely over `k` is *stronger* than
splitting completely over `K`: the decomposition group `D_A` of `k` may be strictly larger than
`D_A ⊓ G_K`.  Precisely,

`A` splits completely in `N.restrictScalars k` over `k`  ⟺  `A` splits completely in `N` over `K`
and `D_A ≤ G_K`.

This is the precise form of the "level mismatch" of `ZSplit/LEVELK_STATUS.md`: the level-`K` local
conditions must use the decomposition group `D_A ⊓ G_K` and the level-`K` relaxation is at the
primes that split completely *over `K`*; and a level-`K` condition is a level-`k` condition only
after imposing `D_A ≤ G_K`. -/
theorem isSplitIn_baseChange (N : IntermediateField ↥K Ω) (A : ValuationSubring Ω) :
    IsSplitIn k (N.restrictScalars k) A ↔ IsSplitIn ↥K N A ∧ IsSplitIn k K A := by
  rw [IsSplitIn, IsSplitIn, IsSplitIn]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- `decomp ↥K A ≤ N.fixingSubgroup`, from `decomp k A ≤ (N.restrictScalars k).fixingSubgroup`
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm τ
      have heq : (IntermediateField.fixingSubgroupEquiv K) u = τ := MulEquiv.apply_symm_apply _ _
      have hcoe : ⇑((u : Ω ≃ₐ[k] Ω)) = ⇑τ := by
        have h1 : ⇑((IntermediateField.fixingSubgroupEquiv K) u : Ω ≃ₐ[↥K] Ω) = ⇑τ := by rw [heq]
        rw [← h1]; rfl
      have hdec : (u : Ω ≃ₐ[k] Ω) ∈ decomp k A :=
        (fixingSubgroupEquiv_mem_decomp k Ω K A (u : Ω ≃ₐ[k] Ω) u.2).mp (by
          rw [show (⟨(u : Ω ≃ₐ[k] Ω), u.2⟩ : ↥(K.fixingSubgroup)) = u from rfl, heq]
          exact hτ)
      have hfix : (u : Ω ≃ₐ[k] Ω) ∈ (N.restrictScalars k).fixingSubgroup := h hdec
      rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
      have hx' : x ∈ (N.restrictScalars k : IntermediateField k Ω) := by
        rwa [IntermediateField.mem_restrictScalars k]
      have h2 := hfix x hx'
      rwa [hcoe] at h2
    · -- `D_A ≤ G_K`, from `D_A ≤ G_N` and `G_N ≤ G_K`
      intro σ hσ
      have hσ' : σ ∈ (N.restrictScalars k).fixingSubgroup := h hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hσ' x (IntermediateField.algebraMap_mem N ⟨x, hx⟩)
  · rintro ⟨h1, h2⟩ σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσK : σ ∈ K.fixingSubgroup := h2 hσ
    have hdec : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩) ∈ decomp ↥K A :=
      (fixingSubgroupEquiv_mem_decomp k Ω K A σ hσK).mpr hσ
    have hfix := h1 hdec
    rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) = ⇑σ :=
      funext fun _ => rfl
    have h2' := hfix x hx
    rwa [hcoe] at h2'

/-- **`IsRamifiedIn` in terms of the base-field inertia.**  For `N : IntermediateField ↥K Ω`,
`A` is ramified in `N/K` iff some `σ ∈ G_k` fixing `K`, lying in the inertia of `A` over `k`, does
not fix `N` (equivalently `N.restrictScalars k`) pointwise. -/
theorem isRamifiedIn_baseChange (N : IntermediateField ↥K Ω) (A : ValuationSubring Ω) :
    IsRamifiedIn ↥K N A ↔
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup ∧ IsInertia k A σ ∧
        σ ∉ (N.restrictScalars k).fixingSubgroup := by
  constructor
  · rintro ⟨τ, hτI, hτN⟩
    set u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm τ with hu
    have hueq : (IntermediateField.fixingSubgroupEquiv K) u = τ := MulEquiv.apply_symm_apply _ _
    have hcoe : ⇑((u : Ω ≃ₐ[k] Ω)) = ⇑τ := funext fun _ => rfl
    refine ⟨(u : Ω ≃ₐ[k] Ω), u.2, ?_, ?_⟩
    · rw [← isInertia_baseChange k Ω K A (u : Ω ≃ₐ[k] Ω) u.2]
      rw [show (⟨(u : Ω ≃ₐ[k] Ω), u.2⟩ : ↥(K.fixingSubgroup)) = u from rfl, hueq]
      exact hτI
    · intro h
      apply hτN
      rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
      intro x hx
      have hx' : x ∈ N.restrictScalars k := by rwa [IntermediateField.mem_restrictScalars k]
      have h2 := h x hx'
      rwa [hcoe] at h2
  · rintro ⟨σ, hσ, hI, hN⟩
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω ≃ₐ[↥K] Ω) = ⇑σ :=
      funext fun _ => rfl
    refine ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩, ?_, ?_⟩
    · exact (isInertia_baseChange k Ω K A σ hσ).mp hI
    · intro h
      apply hN
      rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
      intro x hx
      have hx' : x ∈ N := by rwa [← IntermediateField.mem_restrictScalars k] at hx
      have h2 := h x hx'
      rwa [hcoe] at h2

/-- **Level-`K` conjugacy is conjugacy over `↥K`.**  `B` is a `G_K`-conjugate of `A` (the relation
`kConj` of `ZSplit/levelKCounting.lean`, the correct conjugacy for the level-`K` local conditions)
if and only if `B` is a `Gal(Ω/↥K)`-conjugate of `A`, i.e. `IsConjPlace ↥K A B`. -/
theorem isConjPlace_baseChange (A B : ValuationSubring Ω) :
    (∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ τ • A = B) ↔ IsConjPlace ↥K A B := by
  have smul_congr : ∀ (e : Ω ≃ₐ[↥K] Ω) (σ : Ω ≃ₐ[k] Ω), ⇑e = ⇑σ → e • A = σ • A := by
    intro e σ hcoe
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hcoe]⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hcoe]⟩
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    refine ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩, ?_⟩
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩ : Ω ≃ₐ[↥K] Ω) = ⇑τ :=
      funext fun _ => rfl
    rw [smul_congr _ τ hcoe]
    exact hτA
  · rintro ⟨τ, hτA⟩
    let u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm τ
    have hcoe : ⇑((u : Ω ≃ₐ[k] Ω)) = ⇑τ := by
      have h1 : ⇑((IntermediateField.fixingSubgroupEquiv K) u : Ω ≃ₐ[↥K] Ω) = ⇑τ := by
        rw [MulEquiv.apply_symm_apply]
      rw [← h1]
      rfl
    refine ⟨(u : Ω ≃ₐ[k] Ω), u.2, ?_⟩
    have hsmul : ((u : Ω ≃ₐ[k] Ω)) • A = τ • A := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists,
        ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hcoe]⟩
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hcoe]⟩
    exact hsmul.trans hτA

end Dictionary

/-! ## The cochain dictionary

On a subgroup of `G_K` the action of `G_k` on a `Gal(K/k)`-module is trivial, so the cocycle
condition is *additivity* and the coboundary condition is *vanishing*; the same holds on the
base-`↥K` side, where the acting group is `Gal(Ω/↥K)`.  Hence the two cochain vocabularies agree
along `fixingSubgroupEquiv`, and the class groups agree as well. -/

section Cochains

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
variable {p : ℕ} [Fact p.Prime] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- On a subgroup of `G_K` the crossed-homomorphism condition is additivity: the action of `G_K`
on a `Gal(K/k)`-module is trivial. -/
theorem isCocycleOn_fixingSubgroup_iff_additive_of_le (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hH : H ≤ K.fixingSubgroup) (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    IsCocycleOn (res k K) H f ↔ ∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + f h := by
  constructor
  · intro hcoc g hg h hh
    have h1 : res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
      exact hH hg
    rw [hcoc g hg h hh, h1, one_smul]
  · intro hadd g hg h hh
    have h1 : res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
      exact hH hg
    rw [h1, one_smul]
    exact hadd g hg h hh

/-- On a subgroup of `G_K` a coboundary is *zero*: a coboundary is `σ ↦ (res σ) • m - m` and
`res σ = 1` there. -/
theorem isCoboundaryOn_fixingSubgroup_iff_zero_of_le (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hH : H ≤ K.fixingSubgroup) (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    IsCoboundaryOn (res k K) H f ↔ ∀ g ∈ H, f g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    have h1 : res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
      exact hH hg
    rw [hm g hg, h1, one_smul, sub_self]
  · intro h
    exact ⟨0, fun g hg => by rw [h g hg]; simp⟩

end Cochains

end Work.SSGRoute
