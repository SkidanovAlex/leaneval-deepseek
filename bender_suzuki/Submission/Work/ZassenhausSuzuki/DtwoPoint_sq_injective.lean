import Mathlib
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Squaring is injective on the two-point stabiliser `D = H ∩ Hᵗ`

Suzuki 1962, §8 (see also Peterfalvi II Ch. V §1): for `H` strongly embedded with
`t ∉ H` an involution, the two-point stabiliser `D = H ⊓ Hᵗ` has **odd** order — this is
exactly the `Odd` clause of `IsStronglyEmbedded` applied to the element `t ∉ H`.  Hence any
element of `D` is determined by its square: `x ↦ x²` is injective on `D`.

Together with `DtwoPoint_regular_on_involutions` this gives the `D`-action on the involutions
of the root group `Q` as a regular action whose point stabilisers are the squares — so that
the map `x ↦ x²` really is the "canonical" parametrisation `D → Inv(Q)` used in the
Bender–Suzuki analysis.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

/-- **Squaring injects on `D = twoPoint H t`.**  `D` has odd order (strong embedding applied
to `t ∉ H`), so `x ↦ x²` is a bijection of `D`. -/
theorem DtwoPoint_sq_injective {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d e' : ↥(Submission.Blueprint.twoPoint H t)} (h : d * d = e' * e') : d = e' := by
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    hsplit.stronglyEmbedded.2.2 t hsplit.not_mem
  have hcop : (Nat.card ↥(Submission.Blueprint.twoPoint H t)).Coprime 2 :=
    hodd.coprime_two_left.symm
  have hinj : Function.Injective
      (fun x : ↥(Submission.Blueprint.twoPoint H t) => x ^ 2) :=
    (hcop.pow_left_bijective (G := ↥(Submission.Blueprint.twoPoint H t)) (n := 2)).injective
  exact hinj (by simpa [pow_two] using h)

end Work.ZassenhausSuzuki
