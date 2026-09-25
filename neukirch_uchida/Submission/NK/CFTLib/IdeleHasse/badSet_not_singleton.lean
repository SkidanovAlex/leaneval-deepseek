import Mathlib
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.hilbertReciprocity_cyclic

/-!
# `badSet_not_singleton` — Hasse's norm theorem with one place omitted

## The statement

For a cyclic extension `L / K` of number fields, an `x ∈ Kˣ` which is a local norm at every place
`v ≠ v₀` is a *global* idèle norm:

  `badSet_not_singleton : (∀ v ≠ v₀, ∃ y : 𝕀[L], P_K(x) v = N_{L/K}(y) v) → P_K(x) ∈ N_{L/K} 𝕀_L`.

By the (proved, sorry-free) local–global principle `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`
this is exactly

> the set of places at which `x` fails to be a local norm is never a singleton

(Milne, *CFT*, VIII.2 Example 2.2(ii)), which the name records.

## Position in the theory

The statement is *equivalent* to the local faithfulness of the global Artin map (Milne, *CFT*,
V.5.3(a) = VII.8.1(a)), i.e. to Hilbert's reciprocity law `∑_v inv_v(x) = 0` for `x ∈ Kˣ`.  The two
directions of the equivalence are proved and sorry-free on disk; the reductions are reviewed in
`Submission/Work/CFTLib/IdeleHasse/NOTES_badSet_not_singleton.md` together with the routes, the
traps (the normalisation of the local Artin map at the ramified primes) and the dead ends.

## Wiring (as of this session)

The consolidated form of the crux is the `Prop`

  `NK.CFTLib.HilbertReciprocityOnePlace`
  (`Submission/Work/CFTLib/hilbertReciprocityCyclicAux.lean`): for cyclic `L/K` and `a : Kˣ`,
  `a` a local norm at every `v ≠ v₀` implies `a` a local norm at `v₀`.

It is owned by `NK.CFTLib.HR.hilbertReciprocityOnePlace_proof`
(`Submission/Work/CFTLib/HR/hilbertReciprocityOnePlace_proof.lean`), whose proof is the consolidated
assembly `NK.CFTLib.Existence.hilbertReciprocityOnePlace_of_concrete_inputs`.

**Import cycle (important).**  This file cannot import the HR endpoint directly: the import closure
of `NK.CFTLib.HR.hilbertReciprocityOnePlace_proof` contains *this* module (via
`NK.CFTLib.Existence.classField_exists_primeIndex` and
`NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles`, which import
`NK.CFTLib.IdeleHasse.badSet_not_singleton`), so importing it here would be a cycle.  The target is
therefore wired to the *cycle-free* placeholder `NK.CFTLib.hilbertReciprocity_onePlace_aux`
(`Submission/Work/CFTLib/hilbertReciprocity_cyclic.lean`, not in the HR closure), through the
sorry-free reduction `badSet_not_singleton_of_HilbertReciprocityOnePlace`.  The target becomes
proven — with no edit to this file — as soon as (i) that placeholder is rewired to
`NK.CFTLib.HR.hilbertReciprocityOnePlace_proof` *and* (ii) the two `Existence` files above stop
importing `Submission.NK.CFTLib.IdeleHasse.badSet_not_singleton` (the natural fix: they should
consume the crux in the `NK.CFTLib.HilbertReciprocityOnePlace` form, e.g. as a hypothesis or from
the placeholder module, since `badSet_not_singleton` *is* the crux and must be upstream of them,
not downstream).  Equivalently, rewire the last line of `badSet_not_singleton` to
`NK.CFTLib.HR.hilbertReciprocityOnePlace_proof` once the cycle is broken.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

/-- **The target, from the consolidated form of the crux.**

Given `H : NK.CFTLib.HilbertReciprocityOnePlace` — a global element `a ∈ Kˣ` which is a local norm
at every place `≠ v₀` is a local norm at `v₀` — the "bad set is not a singleton" statement follows:
the hypothesis of the target is the local-norm condition at every `v ≠ v₀`
(`normIdeleFun_mem_localNormSubgroup`), the crux supplies it at `v₀`, and the local–global
principle `mem_normImage_iff_localNorm` assembles a single witnessing idèle.

The proof is sorry-free; it consumes nothing but `HilbertReciprocityOnePlace`. -/
theorem badSet_not_singleton_of_HilbertReciprocityOnePlace
    (H : NK.CFTLib.HilbertReciprocityOnePlace)
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {x : Kˣ} {v₀ : Place K}
    (h : ∀ v : Place K, v ≠ v₀ → ∃ y : Idele L,
      Idele.principalIdele K x v = Idele.normIdeleFun K L y v) :
    Idele.principalIdele K x ∈ Idele.normImage K L := by
  classical
  haveI : IsCyclic (L ≃ₐ[K] L) := hcyc
  -- the target's hypothesis is exactly the local-norm condition at every place `≠ v₀`
  have hloc : ∀ v : Place K, v ≠ v₀ →
      NK.CFTLib.localImageHom (K := K) v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    intro v hv
    obtain ⟨y, hy⟩ := h v hv
    have hy' : NK.CFTLib.localImageHom (K := K) v x = Idele.normIdeleFun K L y v := by
      simpa [NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply] using hy
    rw [hy']
    exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y v
  -- Hilbert reciprocity supplies the missing place
  have h₀ := H x v₀ hloc
  -- and the local–global principle assembles the witnessing idèle
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
  intro v
  by_cases hv : v = v₀
  · subst hv
    exact NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) h₀
  · exact h v hv

/-- **Hasse's norm theorem with one place omitted** (Milne, *CFT*, VIII.2 Example 2.2(ii)): for a
cyclic extension `L / K` of number fields, the set of places at which `x ∈ Kˣ` fails to be a local
norm is never a singleton.  Equivalently: an `x ∈ Kˣ` which is a local norm at every place except
possibly `v₀` is a global idèle norm.

The proof is the reduction above applied to the consolidated crux
`NK.CFTLib.HilbertReciprocityOnePlace`; see the module docstring for the wiring and the state of
each ingredient of the crux. -/
theorem badSet_not_singleton
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {x : Kˣ} {v₀ : NK.GlobalCFT.Place K}
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) :
    NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L :=
  badSet_not_singleton_of_HilbertReciprocityOnePlace
    NK.CFTLib.hilbertReciprocity_onePlace_aux hcyc h

end NK.CFTLib.IdeleHasse
