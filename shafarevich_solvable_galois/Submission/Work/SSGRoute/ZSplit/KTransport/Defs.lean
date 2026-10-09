import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelKCounting
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base change `k → ↥K`: the dictionary's static half

The level-`K` localisation vocabulary of `Submission/Work/SSGRoute/ZSplit/levelKCounting.lean` is
phrased inside the profinite group `G_k = Ω ≃ₐ[k] Ω` with the level-`K` local groups
`decomp k A ⊓ K.fixingSubgroup`.  The level-`⊤` Poitou–Tate vocabulary
(`Submission/Work/SSGRoute/PT/`) is phrased for a base field `k` with the *full* decomposition groups
`decomp k A`.  The two agree after the base change `k ↝ ↥K`, through the group isomorphism

  `IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* (Ω ≃ₐ[↥K] Ω)`,

which is the identity on the underlying functions.  This file contains the *static* part of that
dictionary:

* `isAlgClosure_over` — `Ω` is an algebraic closure of `↥K`;
* `kOver` — an intermediate field `Λ ≥ K` of `Ω/k`, seen over `↥K` (the `↥K`-analogue of
  `Work.SSGRoute.overK`), together with `FiniteDimensional ↥K (kOver …)` and
  `IsGalois ↥K (kOver …)`;
* `trivialDistribMulAction` — the trivial action of a subsingleton group (the coefficient module
  `ZMod p` for the *trivial* extension `⊥ : IntermediateField ↥K Ω` of `↥K`);
* `mapFix`, `restrFun`, `extendFun` — the correspondence of subgroups of `G_k` contained in `G_K`
  with subgroups of `G_K`, the restriction of cochains, and the extension by zero.

The dynamic half (the transport of `IsLocConstOn`/`IsCocycleOn`/`IsCoboundaryOn` and of the local
`H¹`-classes) is filed separately; see `KTransport/PlaceDictionary.lean` and
`KTransport/CochainDictionary.lean`.
-/

namespace Work.SSGRoute.ZSplit

open _root_.SSGRoute
open scoped Pointwise TensorProduct

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1600000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## 1. `Ω` as an algebraic closure of `↥K`, and the base change of intermediate fields -/

/-- `Ω` is an algebraic closure of the number field `↥K`: it is algebraically closed, and algebraic
over `↥K` because it is algebraic over `k ≤ ↥K`. -/
theorem isAlgClosure_over (K : IntermediateField k Ω) [FiniteDimensional k K] :
    IsAlgClosure ↥K Ω :=
  (isAlgClosure_iff ↥K Ω).mpr
    ⟨IsAlgClosure.isAlgClosed (R := k) (K := Ω), inferInstance⟩

/-- The base change of an intermediate field `Λ ≥ K` of `Ω/k` to `Ω/↥K`.  The underlying set is
unchanged (this is the `↥K`-analogue of `Work.SSGRoute.overK`). -/
noncomputable def kOver (K : IntermediateField k Ω) [FiniteDimensional k K]
    (Λ : IntermediateField k Ω) (hKΛ : K ≤ Λ) : IntermediateField ↥K Ω where
  carrier := (Λ : Set Ω)
  mul_mem' := Λ.mul_mem'
  one_mem' := Λ.one_mem'
  add_mem' := Λ.add_mem'
  zero_mem' := Λ.zero_mem'
  inv_mem' := Λ.inv_mem'
  algebraMap_mem' := fun r => hKΛ (Subtype.coe_prop r)

/-- `kOver` does not change the underlying set. -/
@[simp] theorem kOver_coe (K : IntermediateField k Ω) [FiniteDimensional k K]
    (Λ : IntermediateField k Ω) (hKΛ : K ≤ Λ) :
    ((kOver k Ω K Λ hKΛ : IntermediateField ↥K Ω) : Set Ω) = (Λ : Set Ω) := rfl

/-- `kOver` is Galois over `k` when `Λ` is: the two fields have the same underlying set, so the
identity is a `k`-algebra isomorphism. -/
theorem isGalois_kOver_over_base (K : IntermediateField k Ω) [FiniteDimensional k K]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ) :
    IsGalois k ↥(kOver k Ω K Λ hKΛ) :=
  IsGalois.of_algEquiv (f := (AlgEquiv.refl : (↥Λ) ≃ₐ[k] (↥(kOver k Ω K Λ hKΛ))))

/-- `kOver K Λ` is finite dimensional over `↥K`: this is the tower formula
`[Λ : k] = [K : k] * [Λ : K]` together with the finiteness of `[Λ : k]`. -/
theorem finiteDimensional_kOver (K : IntermediateField k Ω) [FiniteDimensional k K]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] (hKΛ : K ≤ Λ) :
    FiniteDimensional ↥K (kOver k Ω K Λ hKΛ) := by
  haveI : FiniteDimensional k ↥(kOver k Ω K Λ hKΛ) := (inferInstance : FiniteDimensional k ↥Λ)
  haveI : Module.Free ↥K ↥(kOver k Ω K Λ hKΛ) := Module.Free.of_divisionRing _ _
  have h := Module.finrank_mul_finrank k ↥K ↥(kOver k Ω K Λ hKΛ)
  have h2 : 0 < Module.finrank k ↥K * Module.finrank ↥K ↥(kOver k Ω K Λ hKΛ) := by
    rw [h]; exact Module.finrank_pos
  exact FiniteDimensional.of_finrank_pos (Nat.pos_of_mul_pos_left h2)

/-- `kOver K Λ` is Galois over `↥K` when `Λ` is Galois over `k`. -/
theorem isGalois_kOver (K : IntermediateField k Ω) [FiniteDimensional k K]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ) :
    IsGalois ↥K (kOver k Ω K Λ hKΛ) := by
  haveI : IsGalois k ↥(kOver k Ω K Λ hKΛ) := isGalois_kOver_over_base k Ω K Λ hKΛ
  exact IsGalois.tower_top_of_isGalois k ↥K ↥(kOver k Ω K Λ hKΛ)

/-! ## 2. The trivial action of a subsingleton group

The coefficient module of the level-`K` statement is `ZMod p` with the *trivial* action, and after
the base change `k ↝ ↥K` the relevant group is `⊥ ≃ₐ[↥K] ⊥` (the trivial extension, so that the
cyclotomic character is trivial as well).  That group is a subsingleton, and a subsingleton group
acts trivially on anything. -/

/-- The trivial `DistribMulAction` of a subsingleton group. -/
def trivialDistribMulAction (G : Type*) [Group G] [Subsingleton G] (M : Type*) [AddMonoid M] :
    DistribMulAction G M where
  smul := fun _ m => m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance (priority := 2000) instDistribMulActionSubsingleton (G : Type*) [Group G]
    [Subsingleton G] (M : Type*) [AddMonoid M] : DistribMulAction G M :=
  trivialDistribMulAction G M

instance (priority := 2000) instSMulCommClassSubsingleton (G : Type*) [Group G]
    [Subsingleton G] (R M : Type*) [SMul R M] [AddMonoid M] : SMulCommClass G R M where
  smul_comm := fun g r m => by
    have h : g = 1 := Subsingleton.elim _ _
    rw [h, one_smul, one_smul]

/-- The trivial extension `⊥ : IntermediateField ↥K Ω` (the image of `↥K` in `Ω`) has no non-trivial
`↥K`-algebra automorphism: every element of `⊥` is `algebraMap ↥K Ω x`, which an `↥K`-algebra
equivalence fixes. -/
instance instSubsingletonBotAlgEquiv (K : IntermediateField k Ω) [FiniteDimensional k K] :
    Subsingleton ((⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K] (⊥ : IntermediateField ↥K Ω)) where
  allEq f g := AlgEquiv.ext fun x => by
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp x.2
    have hx : x = algebraMap ↥K (↥(⊥ : IntermediateField ↥K Ω)) y := Subtype.ext hy.symm
    rw [hx, f.commutes, g.commutes]

/-! ## 3. The correspondence of subgroups and of cochains -/

/-- The subgroup of `G_K = Ω ≃ₐ[↥K] Ω` corresponding to a subgroup `H ≤ G_k` contained in `G_K`,
through `IntermediateField.fixingSubgroupEquiv K`. -/
def mapFix (K : IntermediateField k Ω) (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup) :
    Subgroup (Ω ≃ₐ[↥K] Ω) :=
  (H.subgroupOf K.fixingSubgroup).map (IntermediateField.fixingSubgroupEquiv K)

/-- The restriction of a cochain on `G_k` to `G_K`, through `IntermediateField.fixingSubgroupEquiv`
(which is the identity on the underlying functions). -/
def restrFun (K : IntermediateField k Ω) (M : Type*) (f : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[↥K] Ω) → M :=
  fun σ => f ((IntermediateField.fixingSubgroupEquiv K).symm σ)

/-- The extension of a cochain on `G_K` to `G_k`, by zero outside `G_K`. -/
def extendFun (K : IntermediateField k Ω) (M : Type*) [Zero M] (f : (Ω ≃ₐ[↥K] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → M := by
  classical
  exact fun τ => if h : τ ∈ K.fixingSubgroup then
    f ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, h⟩) else 0

/-- The extension by zero of a restricted cochain is the cochain itself. -/
theorem restrFun_extendFun (K : IntermediateField k Ω) (M : Type*) [Zero M]
    (f : (Ω ≃ₐ[↥K] Ω) → M) : restrFun k Ω K M (extendFun k Ω K M f) = f := by
  classical
  funext σ
  have hmem : ((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup :=
    ((IntermediateField.fixingSubgroupEquiv K).symm σ).2
  have happly : (IntermediateField.fixingSubgroupEquiv K)
      ⟨((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω), hmem⟩ = σ :=
    (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply σ
  simp only [restrFun, extendFun]
  rw [dif_pos hmem, happly]

end

end Work.SSGRoute.ZSplit
