import Mathlib
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
import Submission.Work.AbsoluteKummer.SES.ker_deltaH2_le_range_mapH1
import Submission.Work.AbsoluteKummer.SES.ker_le_range_mapH0
import Submission.Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta
import Submission.Work.AbsoluteKummer.SES.range_mapH0_eq_ker_mapH0
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
import Submission.Work.AbsoluteKummer.SES.ker_mapH2_le_range_deltaH2
import Submission.Work.AbsoluteKummer.SES.deltaH2_forward
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
import Submission.Work.SSGRoute.range_mapH2_eq_ker_mapH2
import Submission.Work.SSGRoute.range_mapH2_eq_ker_deltaH3
import Submission.Work.SSGRoute.natCard_alternating_nine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Additivity (multiplicativity) of the Euler characteristic over a short exact sequence

This file assembles the **first step of Milne's proof of the local Euler characteristic**
(*Arithmetic Duality Theorems*, I.2.8): the multiplicativity of

  `χ(G,M) = |H⁰(G,M)| · |H²(G,M)| / |H¹(G,M)|`

over a short exact sequence `0 → M → N → P → 0` of discrete `G`-modules.

The long exact sequence

`0 → H⁰(M) → H⁰(N) → H⁰(P) → H¹(M) → H¹(N) → H¹(P) → H²(M) → H²(N) → H²(P) → 0`

is exact if `H³(G,M) = 0` (cohomological dimension `≤ 2`, the arithmetic input for
`G = D_A = G_{k_v}`).  Its nine terms are finite when `M` is finite, and the alternating-product
identity for a finite exact sequence (`Work.SSGRoute.natCard_alternating_nine`) then gives
`|H⁰(M)||H⁰(P)||H¹(N)||H²(M)||H²(P)| = |H⁰(N)||H¹(M)||H¹(P)||H²(N)|`, which is exactly
`χ(N) = χ(M)·χ(P)`.

All terms of the sequence here are *additive groups* (the workspace's model
`Work.AbsoluteKummer` does not register a `ZMod p`-module structure on `H1`/`H2`), so the count is
performed with `Nat.card` rather than `Module.finrank`; the passage to `finrank` is done by
`Module.natCard_eq_pow_finrank` in the coefficient model of `LTDDefs/Basic.lean`.
-/

open Work

namespace Work.SSGRoute

/-- The map on invariants induced by the inclusion of a short exact sequence is injective. -/
theorem mapH0_iota_injective {G : Type*} [TopologicalSpace G] [Group G] {M N P : Type _}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M]
    [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    Function.Injective (Work.GroupCohomology.mapH0 G S.iota S.iota_equivariant) := by
  intro a b hab
  refine Subtype.ext (S.iota_injective ?_)
  exact congrArg Subtype.val hab

/-- **Multiplicativity of `χ` over a short exact sequence** (Milne, *ADT*, I.2.8, first step), in
`Nat.card` form: if `H³(G,M) = 0` and all nine terms of the long exact sequence are finite, then

`|H⁰(M)||H⁰(P)||H¹(N)||H²(M)||H²(P)| = |H⁰(N)||H¹(M)||H¹(P)||H²(N)|`.

Equivalently `χ(N) = χ(M)·χ(P)` for `χ(X) = |H⁰(X)|·|H²(X)|/|H¹(X)|`. -/
theorem eulerChar_alternating_natCard {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (h3M : Subsingleton (Work.SSGRoute.H3 (M := M) G))
    [Finite (Work.AbsoluteKummer.H0 G M)] [Finite (Work.AbsoluteKummer.H1 G M)]
    [Finite (Work.AbsoluteKummer.H2 G M)]
    [Finite (Work.AbsoluteKummer.H0 G N)] [Finite (Work.AbsoluteKummer.H1 G N)]
    [Finite (Work.AbsoluteKummer.H2 G N)]
    [Finite (Work.AbsoluteKummer.H0 G P)] [Finite (Work.AbsoluteKummer.H1 G P)]
    [Finite (Work.AbsoluteKummer.H2 G P)] :
    Nat.card (Work.AbsoluteKummer.H0 G M) * Nat.card (Work.AbsoluteKummer.H0 G P) *
        Nat.card (Work.AbsoluteKummer.H1 G N) * Nat.card (Work.AbsoluteKummer.H2 G M) *
        Nat.card (Work.AbsoluteKummer.H2 G P) =
      Nat.card (Work.AbsoluteKummer.H0 G N) * Nat.card (Work.AbsoluteKummer.H1 G M) *
        Nat.card (Work.AbsoluteKummer.H1 G P) * Nat.card (Work.AbsoluteKummer.H2 G N) := by
  have hsurj : Function.Surjective (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) := by
    rw [← AddMonoidHom.range_eq_top, Work.SSGRoute.range_mapH2_eq_ker_deltaH3 S]
    refine eq_top_iff.mpr fun x _ => AddMonoidHom.mem_ker.mpr ?_
    exact Subsingleton.elim _ _
  exact natCard_alternating_nine (X₁ := Work.AbsoluteKummer.H0 G M)
    (X₂ := Work.AbsoluteKummer.H0 G N) (X₃ := Work.AbsoluteKummer.H0 G P)
    (X₄ := Work.AbsoluteKummer.H1 G M) (X₅ := Work.AbsoluteKummer.H1 G N)
    (X₆ := Work.AbsoluteKummer.H1 G P) (X₇ := Work.AbsoluteKummer.H2 G M)
    (X₈ := Work.AbsoluteKummer.H2 G N) (X₉ := Work.AbsoluteKummer.H2 G P)
    (f₁₂ := Work.GroupCohomology.mapH0 G S.iota S.iota_equivariant)
    (f₂₃ := Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant)
    (f₃₄ := S.delta)
    (f₄₅ := Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant)
    (f₅₆ := Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant)
    (f₆₇ := S.deltaH2)
    (f₇₈ := Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant)
    (f₈₉ := Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant)
    (mapH0_iota_injective S)
    (Work.AbsoluteKummer.SES.range_mapH0_eq_ker_mapH0 S)
    (le_antisymm (Work.AbsoluteKummer.ShortExactSeq.range_mapH0_le_ker_delta S)
      (Work.AbsoluteKummer.SES.ker_le_range_mapH0 S))
    (le_antisymm (Work.AbsoluteKummer.ShortExactSeq.range_delta_le_ker_mapH1 S)
      (Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta S))
    (Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1 S)
    (Work.AbsoluteKummer.SES.range_mapH1_eq_ker_deltaH2 S)
    (Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S)
    (Work.SSGRoute.range_mapH2_eq_ker_mapH2 S)
    hsurj

end Work.SSGRoute
