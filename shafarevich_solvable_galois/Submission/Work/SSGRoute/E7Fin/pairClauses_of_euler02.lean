/-
# The finite-place half of `G1` from the Euler characteristic and the degree `0`/`2` duality

This file *completes* the reduction stated in
`Submission/Work/SSGRoute/E7Fin/localPairing_of_euler02.lean`: it glues the two proved pieces

* `Work.SSGRoute.finrank_H1loc_eq_finrank_H1loc_tateDual` — the dimension form of local Tate
  duality at a finite place,
  `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))` (`M^∨(1) = DualMod p (M ⊗ T)`), proved there from the two
  arithmetic inputs `hE` (the local Euler characteristic, `local_tate_duality_euler`) and `h02`
  (Tate duality in degrees `0` and `2`, `local_tate_duality_02`);
* `Work.SSGRoute.E7Fin.pairClauses_of_perfect_pairing` — a perfect pairing of the two local
  `H¹`-spaces (`B` with trivial left and right kernels) packages, through the class map `toClass`,
  into the clause bundle `H1Pair.PairClauses` at the decomposition group.

Together they give, at every finite place `A` and every finite coefficient module `M`, a pairing on
locally constant cochains at `D_A` satisfying clauses (1)–(4) of `G1` (additivity in each variable,
vanishing on coboundaries, perfectness on both sides), *conditionally on* `(E)` and `(02)`.

## What is deliberately *not* claimed here

The pairing produced by `exists_perfect_pairing` is the linear-algebra pairing obtained from
`LinearEquiv.ofFinrankEq`; it depends on the dimension-equality proof, not on the arithmetic of the
place.  Such a pairing has no reason to be **natural** in the coefficient module (clause (5) of
`G1`, the `hnat` slot of the global assembly): naturality is a property of the canonical
construction `inv ∘ cup` (`Work.SSGRoute.H1Pair.pairFromCup`), and it is precisely the reason the
design (`DESIGN_PT.md`) rejects the manufactured pairing for the *global* family.  So the statement
below is the honest per-module content of the finite-place half: clause (5), orthogonality (6) and
reciprocity (7) stay with the canonical construction.
-/
import Mathlib
import Submission.Work.SSGRoute.E7Fin.localPairing_of_euler02
import Submission.Work.SSGRoute.E7Fin.pairClauses_of_perfect_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

/-- **The finite-place half of `G1`, from the Euler characteristic and the degree `0`/`2` duality.**
For a finite place `A` of `Ω` over `k`, the two arithmetic inputs `hE` (Euler characteristic, with
the finiteness of `H¹`) and `h02` (duality in degrees `0` and `2`) produce, for every finite
`𝔽_p[Gal(K/k)]`-module `M`, a pairing of `H¹(D_A, M)` with `H¹(D_A, M^∨(1))` with trivial kernel in
each variable, hence — through `toClass` — the clause bundle `H1Pair.PairClauses` at `D_A`. -/
theorem pairClauses_of_euler02
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
      ∃ B : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A) →ₗ[ZMod p]
          Work.SSGRoute.H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A) →ₗ[ZMod p]
          ZMod p,
        (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        Work.SSGRoute.H1Pair.PairClauses p K T M
          (fun a b => B (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a)
            (Work.SSGRoute.toClass p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (SSGRoute.decomp k A) b))
          (SSGRoute.decomp k A) := by
  intro M _ _ _ _ _
  -- the dimension equality of local Tate duality at `M`
  have hdim := Work.SSGRoute.finrank_H1loc_eq_finrank_H1loc_tateDual
    p k Ω K ζ hζ hζK T hT A hA hE h02 M
  -- finiteness of the two local `H¹`-spaces
  haveI hfinT : Finite T := finite_of_finrank_eq_one T hT.1
  haveI hfinMT : Finite (M ⊗[ZMod p] T) := finite_tensor M T
  haveI hfinD : Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := finite_dualMod (M ⊗[ZMod p] T)
  haveI hfin1 : Module.Finite (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) := (hE.choose_spec M).1
  haveI hfin2 : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
    (hE.choose_spec (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))).1
  -- a perfect pairing of the two `H¹`-spaces (a dimension count)
  obtain ⟨B, hndL, hndR⟩ :=
    Work.SSGRoute.exists_perfect_pairing p
      (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A))
      (Work.SSGRoute.H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) hdim
  exact ⟨B, hndL, hndR,
    pairClauses_of_perfect_pairing p k Ω K T M (SSGRoute.decomp k A) B hndL hndR⟩

end Work.SSGRoute.E7Fin
