import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.PTembedding.h3_triv_subsingleton_decomp_inf_sylow
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_finiteIndex_subgroup
import Submission.Work.SSGRoute.PT.h3loc_decomp_subsingleton
import Submission.Work.SSGRoute.PTCore.h3loc_decomp_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(D_A, M) = 0` for the decomposition group of a finite place and a finite `𝔽_p[Gal(K/k)]`-module

This file restates, in the standard continuous-cohomology model `H³(-, M)` of
`kummerBase_euler_h3_absKummer`, the local vanishing `cd_p(D_A) ≤ 2` for a finite place:
for a number field `k`, an algebraic closure `Ω`, a finite Galois intermediate field `K`,
a finite place `A` of `Ω` over `k`, and every finite `𝔽_p[Gal(K/k)]`-module `M` (acting on
`D_A = decomp k A` through the restriction `res k K : G_k →* Gal(K/k)`,
`decompDistribMulAction K M A`), the third cohomology `H³(D_A, M)` vanishes.

The companion statement in the locally constant model `H3loc`,
`Work.SSGRoute.PT.h3loc_decomp_subsingleton` (`cd_p(G_{k_v}) ≤ 2`; Serre, *Cohomologie
galoisienne*, II §5; Neukirch–Schmidt–Wingberg 7.1.8), is already proved in the tree: its proof is
the `p`-Sylow reduction `EulerSymm.exists_sylowDatum` (an open subgroup `U ≤ D_A` of index prime to
`p` acting through a finite `p`-group, with `H³(U, 𝔽_p) = 0` by the base case
`EulerSymm.h3triv_subsingleton_fixingSubgroup` at a finite level containing `ζ_p`), followed by the
dévissage `PTembedding.h3_subsingleton_of_pgroup_action` and the transfer
`EulerSymm.subsingleton_H3_decomp_of_subsingleton_H3_subgroup`.

The hypothesis data `ζ`, `P` of the statement record that exactly the same `p`-Sylow input is at
hand (any Sylow `P` of `Gal(K/k)` has `p`-power order, hence fixes `ζ_p`, so its fixed field
contains `ζ_p`); the conclusion, however, does not depend on the particular choice of `P`.

The remaining formal content here is then the model bridge: `H3loc p k Ω K M (decomp k A)` is the
standard model `H³(↥(decomp k A), M)` for the canonical action
(`PTCore.subsingleton_h3loc_iff_subsingleton_H3`, a transport of `LTDDefs.H3locEquivH3`).
-/

namespace Work.SSGRoute.PTembedding

theorem h3_decomp_subsingleton (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (P : Sylow p (K ≃ₐ[k] K)) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      letI : DistribMulAction ↥(SSGRoute.decomp k A) M :=
        Work.SSGRoute.decompDistribMulAction K M A
      Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  -- the canonical action of `D_A = decomp k A` on `M` through `res k K`
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M :=
    Work.SSGRoute.decompDistribMulAction K M A
  -- the decomposition group is closed in the Krull topology, so the model bridge applies
  have hH : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A
  have hcompat : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m :=
    fun h m => Work.SSGRoute.decomp_smul_eq_res K M A h m
  -- `H3loc` vanishes by the local theorem, and the bridge turns this into `H³(↥D_A, M) = 0`
  exact (Work.SSGRoute.PTCore.subsingleton_h3loc_iff_subsingleton_H3 p k Ω K M
    (SSGRoute.decomp k A) hH hcompat).mp
    (Work.SSGRoute.PT.h3loc_decomp_subsingleton p k Ω K A hA M)

end Work.SSGRoute.PTembedding
