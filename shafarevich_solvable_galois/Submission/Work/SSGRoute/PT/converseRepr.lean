import Mathlib
import Submission.Work.SSGRoute.PT.pt_canonical_assembly
import Submission.Work.SSGRoute.PT.pt_counting_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# G1⁺'s clause (8) implies the *class-level* converse `hconv` (node-free)

This module carries the part of the `COUNT ⟸ G1⁺` wiring that needs **nothing from the node file**
`PT/pt_counting_identity_h1.lean`:
`PT.ConverseRepr` (G1⁺'s clause (8) at the node's data, copied verbatim from the `.stmt` of
`Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`) and `PT.hconv_of_converse` (that
clause plus the pairing clauses give the class-level `hconv` of
`PT.countingIdentity_of_reciprocity_and_converse`).

It is deliberately a *separate module* so that the node file can import it (and the dispatched G1⁺)
without a cycle, and so close `COUNT` through `G1⁺` — see `PT/pt_counting_from_G1plus.lean` for the
full wiring and `PT/PING_count_faces_and_routes.md` §9–§10 for the record.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω))
  (C : Finset (Ω ≃ₐ[k] Ω))

local instance instConverseReprDualAC :
    AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instConverseReprDualMod :
    Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instConverseReprDualDMA :
    DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance instConverseReprDualSMC :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

/-- **G1⁺'s clause (8) at the node's data** (the representative-form converse), copied verbatim
from the `.stmt` of `canonical_localPairing_reciprocity_converse` with `pair` specialized to `M`.

Local data `(α, β)` at `S ∪ C` whose `pair`-sum vanishes against every relaxed dual Selmer class
`b` is realized by a global locally constant cocycle `ε` unramified outside `S ∪ cs(N)` — i.e. it is
`PT.IsRealizableClass`. -/
def ConverseRepr
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p) : Prop :=
  ∀ (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
    (∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A)) →
    (∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) →
    (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S, pair (SSGRoute.decomp k A) (α A) b +
        ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) →
    ∃ ε : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
      (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0

/-- **The class-level converse `hconv` from G1⁺'s clause (8).**

This is the wiring `COUNT` needs: the hypothesis of `PT.countingIdentity_of_reciprocity_and_converse`
is the *class-level* converse `W^⊥ ⊆ V`, and G1⁺ supplies it in *representative* form.  The
translation is the proved `PT.productFormFun_primalClassOf` (classes to representatives) plus
`PT.localPairingFun_toClass` (the descended local pairing computes on representatives), and the
representative choice for an arbitrary `x : primalClasses` is `toClass_surjective`. -/
theorem hconv_of_converse
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hconv8 : ConverseRepr p k Ω K N hKN T M S C pair) :
    ∀ x : primalClasses p k Ω K M S C,
      (∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
        y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
          (S := S) (C := C) →
        productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
          (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
          x y = 0) →
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
        (C := C) := by
  classical
  intro x horth
  -- representatives of `x` at the places of `S` and the involutions of `C`
  have hexS : ∀ A : {A : ValuationSubring Ω // A ∈ S}, ∃ α : (Ω ≃ₐ[k] Ω) → M,
      α ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A.1) ∧
        toClass p k Ω K M (SSGRoute.decomp k A.1) α = x.1 A :=
    fun A => toClass_surjective p k Ω K M (SSGRoute.decomp k A.1) (x.1 A)
  choose αc hαc using hexS
  have hexC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C}, ∃ β : (Ω ≃ₐ[k] Ω) → M,
      β ∈ lcCocycles p k Ω K M (Subgroup.zpowers c.1) ∧
        toClass p k Ω K M (Subgroup.zpowers c.1) β = x.2 c :=
    fun c => toClass_surjective p k Ω K M (Subgroup.zpowers c.1) (x.2 c)
  choose βc hβc using hexC
  -- extend to all of `ValuationSubring Ω`
  let αf : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M :=
    fun A => if h : A ∈ S then αc ⟨A, h⟩ else 0
  let βf : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
    fun c => if h : c ∈ C then βc ⟨c, h⟩ else 0
  have hαf : ∀ A ∈ S, αf A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) := by
    intro A hA
    have : αf A = αc ⟨A, hA⟩ := dif_pos hA
    rw [this]
    exact (hαc ⟨A, hA⟩).1
  have hβf : ∀ c ∈ C, βf c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) := by
    intro c hc
    have : βf c = βc ⟨c, hc⟩ := dif_pos hc
    rw [this]
    exact (hβc ⟨c, hc⟩).1
  -- `x` is the class of `(αf, βf)`
  have hxα : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      toClass p k Ω K M (SSGRoute.decomp k A.1) (αf A.1) = x.1 A := by
    intro A
    have : αf A.1 = αc A := dif_pos A.2
    rw [this]
    exact (hαc A).2
  have hxβ : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      toClass p k Ω K M (Subgroup.zpowers c.1) (βf c.1) = x.2 c := by
    intro c
    have : βf c.1 = βc c := dif_pos c.2
    rw [this]
    exact (hβc c).2
  have hxclass : primalClassOf p k Ω K M S C αf βf = x := by
    refine Prod.ext ?_ ?_
    · funext A
      exact hxα A
    · funext c
      exact hxβ c
  -- apply G1⁺'s clause (8)
  have hrepr : ConverseRepr p k Ω K N hKN T M S C pair := hconv8
  have hreal : IsRealizableClass p k Ω K N hKN M S C x := by
    refine ⟨αf, βf, ?_⟩
    refine (hrepr αf βf ?_ ?_ ?_).imp fun ε hε => ⟨hxclass, hε.1, hε.2.1, hε.2.2.1, hε.2.2.2.1,
      hε.2.2.2.2⟩
    · intro A hA
      exact ⟨(hαf A hA).1, (hαf A hA).2⟩
    · intro c hc
      exact (hβf c hc).1
    · -- the `pair`-sum vanishes against every relaxed dual Selmer class: clause (8) ↔ clause (8)
      intro b hb1 hb2 hb3 hb4
      have hb : b ∈ dualSelmer p k Ω K N T M S := ⟨hb1, hb2, hb3, hb4⟩
      have hbcl : dualClassMap p k Ω K T M S C b ∈
          dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
            (S := S) (C := C) :=
        LinearMap.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩
      have h0 := horth (dualClassMap p k Ω K T M S C b) hbcl
      have hprod := productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K)
        (N := N) (T := T) (M := M) (S := S) (C := C) (pair := pair)
        (B := localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
        (hB := fun A hA a b ha hb => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K)
          (T := T) (M := M) pair hloc (H := SSGRoute.decomp k A)
          (Or.inl ⟨A, hSfin A hA, rfl⟩) a b ha hb)
        (hBc := fun c hc a b ha hb => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K)
          (T := T) (M := M) pair hloc (H := Subgroup.zpowers c)
          (Or.inr ⟨c, hCinv c hc, rfl⟩) a b ha hb)
        (α := αf) (β := βf) (hα := hαf) (hβ := hβf) (b := b) (hb := hb)
      rw [← hxclass] at h0
      rw [hprod] at h0
      rw [Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (αf A) b),
        Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (βf c) b)] at h0
      exact h0
  exact (mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
    (M := M) (S := S) (C := C) hCinv x).mpr hreal

end

end Work.SSGRoute.PT
