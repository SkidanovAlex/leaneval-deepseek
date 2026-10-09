import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.SSGRoute.PT.DevissageSESDiscrete
import Submission.Work.SSGRoute.PT.isDiscreteModule_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 0

/-!
# The dévissage short exact sequence

For an open finite-index subgroup `U ≤ G` acting discretely on `M`, the sequence

  `0 → M →ᵢ Coind^G_U M →^π M₁ = (Coind^G_U M) ⧸ range ι → 0`

is a short exact sequence of discrete `G`-modules — the input of Milne's dévissage for Theorem 1.8.
(`devissageM1` is an `abbrev`, which is load-bearing: instance search unfolds it.)
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- **The dévissage short exact sequence** `0 → M → Coind^G_U M → M₁ → 0`. -/
theorem devissageSES {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    {M : Type u} [AddCommGroup M] [DistribMulAction G M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (Work.AbsoluteKummer.ShortExactSeq G M (Coind G U M)
      (devissageM1 (M := M) U)) :=
  ⟨{ iota := devissageIota U
   , pi := devissagePi U
   , iota_equivariant := devissageIota_equivariant U
   , pi_equivariant := devissagePi_equivariant U
   , iota_injective := devissageIota_injective U
   , pi_surjective := QuotientAddGroup.mk'_surjective _
   , range_iota_eq_ker_pi := devissage_range_iota_eq_ker_pi U
   , isDiscreteM := hM
   , isDiscreteN := isDiscreteModule_coind U hU hMU
   , isDiscreteP := devissage_isDiscreteModule_m1 U (isDiscreteModule_coind U hU hMU) }⟩

end

end Work.SSGRoute.PT
