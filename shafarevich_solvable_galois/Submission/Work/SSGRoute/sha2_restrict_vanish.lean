import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.sha2_restrict_aux
import Submission.Work.SSGRoute.sha2_restrict_assemble
import Submission.Work.SSGRoute.sha2_trivial_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as
Submission/Work/SSGRoute/DESIGN2.md).  Interfaces: Submission/Work/SSGRoute/Interfaces.lean
(namespace SSGRoute; do NOT edit).  NK.* CFT library available.  Siblings in parallel.

# sha2_restrict_vanish  (Ш²(k,E) dies on G_K)

**Statement.** Every `c ∈ Z2loc p k Ω K E` is a continuous coboundary on `G_K = K.fixingSubgroup`.

**Proof (base change `k → K`).**  On `G_K` the action is trivial (`res k K σ = 1` for
`σ ∈ K.fixingSubgroup`), the places of `Ω` over `K` have decomposition groups `D_A ∩ G_K`, the
involutions of `G_K` are involutions of `G_k`, and every finite place over `K` is a finite place
over `k`.  Hence the restriction of `c` to `Ω ≃ₐ[K] Ω` satisfies the four `Z2loc`-at-base-`K`
conditions with the trivially acted module `E`, so the base-field statement
(`Subsingleton (Sha2 p ↥K Ω ⊥ E)`, i.e. `Work.SSGRoute.sha2_trivial_vanish` at the base field
`↥K` with the bottom intermediate field) produces a primitive, which is transported back to `G_k`
by `isLocConstOn_extract`.

The base-change reduction is `Work.SSGRoute.sha2_restrict_vanish_of_base`
(`sha2_restrict_assemble.lean`), resting on `sha2_restrict_aux.lean`: the identification
`toGkHom : Gal(Ω/↥K) →* G_k` and the transport of decomposition groups, of the "finite place"
predicate, of local constancy and of the cocycle/coboundary conditions.
-/

set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise Classical

theorem sha2_restrict_vanish (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K E) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) K.fixingSubgroup c := by
  -- the (trivial) action of the one-element Galois group `Gal(K/K) = (⊥) ≃ₐ[↥K] ⊥`
  letI : DistribMulAction ((⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K] (⊥ : IntermediateField ↥K Ω)) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass ((⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K] (⊥ : IntermediateField ↥K Ω))
      (ZMod p) E := ⟨fun _ _ _ => rfl⟩
  have htriv : ∀ (g : (⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K] (⊥ : IntermediateField ↥K Ω)) (m : E),
      g • m = m := fun g m => by rw [Subsingleton.elim g 1, one_smul]
  -- `μ_p ⊆ ↥K` because `ζ ∈ K`
  have key : ∀ l : ℕ, (⟨ζ, hζK⟩ : ↥K) ^ l = 1 ↔ ζ ^ l = 1 := by
    intro l
    constructor
    · intro h
      have h' := congrArg (fun x : ↥K => (x : Ω)) h
      simpa using h'
    · intro h
      exact Subtype.ext (by simpa using h)
  have hμ : ∃ ζ' : ↥K, IsPrimitiveRoot ζ' p :=
    ⟨⟨ζ, hζK⟩, ⟨(key p).mpr hζ.pow_eq_one,
      fun l hl => hζ.dvd_of_pow_eq_one l ((key l).mp hl)⟩⟩
  -- `↥K` is a number field (a finite extension of the number field `k`)
  haveI hNF : NumberField ↥K := by
    haveI : FiniteDimensional ℚ ↥K := FiniteDimensional.trans ℚ k ↥K
    exact { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  -- `Ω` is an algebraic closure of `↥K` as well
  haveI hAC : IsAlgClosure ↥K Ω := by
    have hAlg : Algebra.IsAlgebraic ↥K Ω :=
      ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic_iff k ↥K).mp
        (Algebra.IsAlgebraic.isAlgebraic (R := k) (A := Ω) x)⟩
    exact IsAlgClosure.mk (IsAlgClosure.isAlgClosed (R := k)) hAlg
  -- the base case at `↥K`: `Sha2 p ↥K Ω ⊥ E` is a subsingleton
  haveI hsub : Subsingleton (Work.SSGRoute.Sha2 p (↥K) Ω (⊥ : IntermediateField ↥K Ω) E) :=
    Work.SSGRoute.sha2_trivial_vanish p (↥K) Ω (⊥ : IntermediateField ↥K Ω) hμ E htriv
  have hbase : ∀ c' : (Ω ≃ₐ[↥K] Ω) → (Ω ≃ₐ[↥K] Ω) → E,
      c' ∈ Work.SSGRoute.Z2loc p (↥K) Ω (⊥ : IntermediateField ↥K Ω) E →
        SSGRoute.IsCoboundary2On (SSGRoute.res (↥K) (⊥ : IntermediateField ↥K Ω)) ⊤ c' := by
    intro c' hc'
    refine (Work.SSGRoute.sha2Class_eq_zero_iff p (↥K) Ω (⊥ : IntermediateField ↥K Ω) E
      hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2).mp ?_
    exact Subsingleton.elim (Work.SSGRoute.sha2Class p (↥K) Ω (⊥ : IntermediateField ↥K Ω) E
      hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2) 0
  exact Work.SSGRoute.sha2_restrict_vanish_of_base p k Ω K E htriv hbase c hc

end Work.SSGRoute
