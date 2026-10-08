import Mathlib
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = H ∩ H^t` is regular on the involutions of the root group `Q`

In the split rank-one Zassenhaus configuration (`IsSplitRankOne H Q t`, `IsZassenhaus H`, `Q` a
`2`-group), the two-point stabiliser `D = twoPoint H t` acts by conjugation *sharply
transitively* on the non-trivial involutions of the regular normal subgroup `Q`: for any two
involutions `z, w ∈ Q ∖ {1}` there is exactly one `d ∈ D` with `d z d⁻¹ = w`.

* **Existence** is the transitivity of `D` on `Inv(H)` (Peterfalvi I, Ch. I §2 Prop. 2 (b),
  `Work.ThmF.Bender.DTransitiveInv`): since `Q ≤ H` the involutions `z, w` of `Q` are involutions
  of `H`.
* **Uniqueness** is the fixed-point-freeness of `D` on `Q#` coming from Zassenhausness
  (`Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q`): if `d z d⁻¹ = e z e⁻¹` then `e⁻¹ d ∈ D` fixes
  `z ≠ 1`, hence `e⁻¹ d = 1`.

Together with the cardinality identity `|D| = #Inv(Q)` (`twoPoint_card_eq_involutions`) this is
Suzuki Prop. 3 / the semiregularity input of L2 of `NOTES_LEAD_probe1630.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem DtwoPoint_regular_on_involutions {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {z w : Q} (hz1 : z ≠ 1) (hz2 : z * z = 1) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    ∃! d : ↥(Submission.Blueprint.twoPoint H t),
      (d : G) * (z : G) * (d : G)⁻¹ = (w : G) := by
  -- the two involutions, transported from `Q` to `H`
  have hz2G : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rwa [pow_two]) hz1
  have hw2G : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rwa [pow_two]) hw1
  -- existence: `D` is transitive on `Inv(H)` (Peterfalvi I Ch. I §2 Prop. 2 (b))
  obtain ⟨d, hd, hdz⟩ :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
      (z : G) ⟨hsplit.le z.2, hz2G⟩ (w : G) ⟨hsplit.le w.2, hw2G⟩
  refine ⟨⟨d, hd⟩, hdz, ?_⟩
  intro e he
  -- uniqueness: `e⁻¹ d ∈ D` fixes `z ≠ 1`, so `e⁻¹ d = 1`
  have hfix : ((e : G)⁻¹ * d) * (z : G) * ((e : G)⁻¹ * d)⁻¹ = (z : G) := by
    have h1 : ((e : G)⁻¹ * d) * (z : G) * ((e : G)⁻¹ * d)⁻¹
        = (e : G)⁻¹ * (d * (z : G) * d⁻¹) * (e : G) := by group
    rw [h1, hdz, ← he]
    group
  have hc : (e : G)⁻¹ * d ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).inv_mem e.2) hd
  have hde : (d : G) = (e : G) := by
    by_contra hne
    have hc1 : (e : G)⁻¹ * d ≠ 1 := fun h =>
      hne (inv_mul_eq_one.mp h).symm
    have hz1' := Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hzass
      ((e : G)⁻¹ * d) hc hc1 (z : G) z.2 hfix
    exact hz1 (Subtype.ext (by simpa using hz1'))
  exact Subtype.ext hde.symm

end Work.ZassenhausSuzuki
