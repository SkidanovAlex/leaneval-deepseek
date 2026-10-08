import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V: `K̄ = ⟨J(D,t)⟩` is a complement of `V = C_D(t)` in `D`

In the split rank-one situation `H = Q ⋊ D`, `D = twoPoint H t`, `K = J(D,t) = Kset H t`,
`K̄ = ⟨K⟩ = Ksub H t` and `V = C_D(t) = centD H t`, Ch. V Prop. 2 (`ChV12.Ksub_cyclic_normal`)
gives `K̄ = K = {x ∈ D | t x t⁻¹ = x⁻¹}`; hence:

* `K̄ ⊓ V = ⊥`: an element of `K̄` is inverted by `t`, while an element of `V` is fixed by `t`;
  so `x = x⁻¹`, `x² = 1`; since `K̄ ⊆ D` has odd order, `x = 1`.
* `|K̄| · |V| = |D|`: `|K| · |V| = |D|` is Peterfalvi I App. I (1)(b) for `d = 2`
  (`Bender.cardInvertedMulCardCentralizer`, packaged as `Work.ThmF.card_centD_mul_card_Kset`)
  and `|K̄| = |K|` since `K̄ = K` as sets.
-/

namespace Work.ThmF.ChV3.Prove

theorem Ksub_inf_centD_and_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Work.ThmF.Ksub H t ⊓ Submission.Blueprint.centD H t = ⊥ ∧
      Nat.card ↥(Work.ThmF.Ksub H t) * Nat.card ↥(Submission.Blueprint.centD H t)
        = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
  classical
  -- Ch. V Prop. 2: `K̄ = ⟨J(D,t)⟩` is the set `J(D,t)` itself.
  obtain ⟨-, hKset, -⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 c.sit c.split
  -- `D = twoPoint H t` has odd order.
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint c.split
  -- `|K̄| = |K|`, since `K̄ = K` as sets.
  have hcardK : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    show Nat.card ↥((Work.ThmF.Ksub H t : Set G)) = (Work.ThmF.Kset H t).ncard
    rw [Nat.card_coe_set_eq, hKset]
  refine ⟨?_, ?_⟩
  · -- `K̄ ⊓ V = ⊥`
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxK, hxV⟩ := hx
    have hxKset : x ∈ Work.ThmF.Kset H t := by
      have h : x ∈ (Work.ThmF.Ksub H t : Set G) := hxK
      rwa [hKset] at h
    -- `t` inverts `x` (as `x ∈ K̄ = K`) ...
    have hxinv : t * x * t⁻¹ = x⁻¹ := (Work.ThmF.mem_Kset_iff.mp hxKset).2
    -- ... and fixes `x` (as `x ∈ V = C_D(t)`).
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxV).2
    have hxfix : t * x * t⁻¹ = x := by rw [← hxt]; group
    have h1 : x⁻¹ = x := by rw [← hxinv, hxfix]
    have hsq : x * x = 1 := by
      calc x * x = x⁻¹ * x := by rw [h1]
        _ = 1 := inv_mul_cancel x
    -- so `orderOf x ∣ 2`, while `x ∈ D` gives `Odd (orderOf x)`; hence `x = 1`.
    have hdvd : orderOf x ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
    have hoddx : Odd (orderOf x) :=
      Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard (Submission.Blueprint.twoPoint H t)
        (Work.ThmF.Kset_subset H t hxKset))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd hoddx (by rw [h]; exact Nat.not_odd_iff_even.mpr even_two)
  · -- `|K̄| · |V| = |D|`
    have hmain := Work.ThmF.card_centD_mul_card_Kset (Work.ThmF.IsSplitRankOne.toData c.split)
    rw [hcardK, mul_comm]
    exact hmain

end Work.ThmF.ChV3.Prove
