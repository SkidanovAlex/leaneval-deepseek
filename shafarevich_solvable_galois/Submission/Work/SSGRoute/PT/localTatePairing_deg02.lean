import Mathlib
import Submission.Work.SSGRoute.PT.HomFormReduction
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.ld02_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local Tate duality in degrees `0` and `2` for a decomposition group

`Work.SSGRoute.PT.localTatePairing_deg02` — Milne, *Arithmetic Duality Theorems*, Cor. I.2.3 at
`r = 0`: for a number field `k`, an algebraic closure `Ω`, a finite Galois `K/k` containing a
primitive `p`-th root of unity `ζ`, a cyclotomic dual `T` (`IsCyclotomicDual`), every finite place
`A` of `Ω` over `k` and every finite `𝔽_p[Gal(K/k)]`-module `M`,

  `dim H²(D_A, M) = dim H⁰(D_A, DualMod p (M ⊗ T))`,   `D_A = decomp k A`.

## Structure of the file

All the *reductions* of the target (the model bridges `H2locEquivH2_decomp`, `h0loc_dualMod_tensor`,
`instModuleH2`, `finiteness` lemmas, and the reduction `localTatePairing_deg02_of_hom_form`) live in
the lower module `Submission.Work.SSGRoute.PT.HomFormReduction`; the proof of the target itself is
assembled in `Submission.Work.SSGRoute.PT.ld02_assembly`, which this file imports.

## The proof

The route is Milne's class-formation theorem (ADT Theorem I.1.8) at `r = 2` for the local class
formation `(D_A, \bar k_v^×)`: for the Tate-dual coefficient module `N = M^∨(1) = DualMod p (M ⊗ T)`
the cup-product map

  `α² : H²(D_A, Hom_ℤ(N, Ωˣ)) → Hom_{D_A}(N, H²(D_A, Ωˣ))`

is bijective (`PT.ld02_alphaTwo_bijective` in `PT/ld02_assembly.lean`), assembled from

* the dévissage `PT.alphaTwo_bijective_of_devissage` along `0 → N → Coind_U^{D_A} N → N₁ → 0`;
* the base case `PT.mkb_alphaTwo_base_of_trivAction` / `PT.mkb_alphaTwo_coind_bijective` at the
  level subgroup `U = levelFixSub k Ω A K`, i.e. Kummer theory plus Hilbert 90 at `U`;
* Milne's class-formation axiom (1.1b) on the `p`-torsion,
  `PT.ltdCorH2_bijective_units_openSubgroup`;
* the `Ext³`-input `PT.ld02_hhtop`, i.e. `H³(D_A, Hom_ℤ(N₁,Ωˣ)) = 0`, from `cd_p(D_A) ≤ 2`
  (`PT.h3loc_decomp_subsingleton`);
* the exactness of the dual of the invariants sequence (the retraction lemmas).

The twist `Hom_ℤ(N, Ωˣ) ≅ M`, the identification `N^{D_A} ≅ H⁰_loc(D_A, N^∨(1))`
(`PT.h0loc_dualMod_tensor`) and the count `#H²(D_A,Ωˣ)[p] = p` (`Nakayama.br_pTorsion`) turn the
bijectivity of `α²` into the dimension identity
(`PT.finrank_eq_of_alphaTwo_bijective`); the resulting statement is `PT.ld02_dimform`.
-/

open Classical
open scoped TensorProduct

namespace Work.SSGRoute.PT

noncomputable section

/-- **Local Tate duality in degrees `0` and `2` for a decomposition group** (Milne, *Arithmetic
Duality Theorems*, Cor. I.2.3 at `r = 0`). -/
theorem localTatePairing_deg02
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
  Work.SSGRoute.PT.ld02_dimform p k Ω K ζ hζ hζK T hT

end

end Work.SSGRoute.PT
