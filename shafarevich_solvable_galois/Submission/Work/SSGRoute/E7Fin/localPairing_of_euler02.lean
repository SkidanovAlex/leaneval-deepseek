/-
# Local Tate duality in degree one from the Euler characteristic and the degree `0`/`2` duality

The `LTDDefs`/`PTembedding` lanes lost their assembly from the tree: the two arithmetic inputs are
*stated* (`Work.SSGRoute.local_tate_duality_euler`, `Work.SSGRoute.local_tate_duality_02`), but the
reduction "Euler characteristic + duality in degrees 0 and 2 ⟹ the local Tate pairing in degree 1" is
no longer in the source tree (only references to the missing declarations
`Work.SSGRoute.hasPerfectLocalPairing_of_inputs`, `Work.SSGRoute.local_tate_duality_of_inputs`
survive).

This file restates the dimension step of that assembly:

1. `finrank_H1loc_eq_finrank_H1loc_tateDual`: `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))`.  Apply the
   Euler characteristic (with a *single* constant `ε`, as in `local_tate_duality_euler`) at `M` and at
   `M^∨(1)`; the degree `0`/`2` duality (as in `local_tate_duality_02`) identifies `h²(M)` with
   `h⁰(M^∨(1))` and `h²(M^∨(1))` with `h⁰(M)`, and `IsCyclotomicDual` makes `dim M^∨(1) = dim M`.

The companion clause-bundle lemma `pairClauses_of_perfect_pairing` used to be restated (unproved) in
this file; the *proved* copy lives in
`Submission/Work/SSGRoute/E7Fin/pairClauses_of_perfect_pairing.lean` (namespace
`Work.SSGRoute.E7Fin`), and `Submission/Work/SSGRoute/E7Fin/pairClauses_of_euler02.lean` assembles it
with the dimension equality below into the finite-place half of `G1`.
-/
import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.H1Pair.Clauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open H1Pair

/-- **The two local `H¹`-spaces of a decomposition group have the same dimension.** -/
theorem finrank_H1loc_eq_finrank_H1loc_tateDual
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hE : ∃ ε : ℕ, ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ∧
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) +
            Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) +
            ε * Module.finrank (ZMod p) M)
    (h02 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) ∧
      Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  obtain ⟨ε, hε⟩ := hE
  have hdT : Module.finrank (ZMod p) T = 1 := hT.1
  haveI : Finite T := finite_of_finrank_eq_one T hdT
  haveI : Finite (M ⊗[ZMod p] T) := finite_tensor M T
  haveI : Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    finite_dualMod (M ⊗[ZMod p] T)
  have hdim : Module.finrank (ZMod p) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) =
      Module.finrank (ZMod p) M := by
    rw [finrank_dualMod (M ⊗[ZMod p] T), finrank_tensor_rankOne M T hdT]
  have h1 := (hε M).2
  have h2 := (hε (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))).2
  have h3 := (h02 M).1
  have h4 := (h02 M).2
  rw [h1, h2, h3, h4, hdim]
  ring

end Work.SSGRoute
