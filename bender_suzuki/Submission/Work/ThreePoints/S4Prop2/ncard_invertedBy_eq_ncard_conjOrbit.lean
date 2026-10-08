import Mathlib
import Submission.Work.DoubleTransitivity.App1.app1_1b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.S4Prop2

/-- Peterfalvi I, Appendix I (1)(b): for an involution `t` normalising a subgroup `X` of odd
order, the number of elements of `X` inverted by `t` equals the size of the orbit of `t` under
conjugation by `X`.

Indeed `Work.DoubleTransitivity.App1.app1_1b` gives `commutatorSet t X = invertedBy X t`, and
`u ↦ t⁻¹ * u` is a bijection from `conjOrbit X t` onto `commutatorSet t X`. -/
theorem ncard_invertedBy_eq_ncard_conjOrbit {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (ht : orderOf t = 2) (hodd : Odd (Nat.card ↥X))
    (hnorm : t ∈ Subgroup.normalizer (X : Set G)) :
    (Submission.Blueprint.invertedBy X t).ncard =
      (Work.DoubleTransitivity.conjOrbit X t).ncard := by
  -- the set of inverted elements is the commutator set `{[t,x] | x ∈ X}`
  have hK : Work.DoubleTransitivity.commutatorSet t X = Submission.Blueprint.invertedBy X t :=
    (Work.DoubleTransitivity.App1.app1_1b (X := X) (t := t) ht hodd hnorm).1
  -- and the orbit of `t` maps bijectively onto the commutator set via `u ↦ t⁻¹ * u`
  rw [← hK, ← Work.DoubleTransitivity.image_conjOrbit_eq_commutatorSet X t]
  exact Set.ncard_image_of_injective _
    (fun a b h => mul_left_cancel h)

end Work.ThreePoints.S4Prop2
