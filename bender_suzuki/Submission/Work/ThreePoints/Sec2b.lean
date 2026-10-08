/-
# `Work.ThreePoints.Sec2b` — Peterfalvi I Ch. I §2 Prop. 2: the two-point stabiliser

With `D = H ⊓ H^t = twoPoint H t` (an involution `t ∉ H`), `V = C_D(t) = centD H t` and
`K = J(D,t) = invertedBy D t`, Appendix I (1)(b) (proved in
`Submission.Work.ThreePoints.card_eq_mul_ncard_invertedBy`) gives

  `|D| = |V| · |K|,`

the cardinality input of Ch. I §2 Prop. 2(b) (`|K| = |D : V| = n = |Inv H|`).
-/
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.card_eq_mul_ncard_invertedBy

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- `t` normalises the two-point stabiliser `D = H ⊓ H^t`. -/
theorem mem_normalizer_twoPoint (H : Subgroup G) {t : G} (ht : orderOf t = 2) :
    t ∈ Subgroup.normalizer (twoPoint H t : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have key : ∀ y : G, t * y * t⁻¹ = t⁻¹ * y * t := by
    intro y
    rw [htinv]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [twoPoint_eq, Subgroup.mem_inf, Subgroup.mem_inf, mem_conj_iff, mem_conj_iff]
  have hz : t⁻¹ * (t⁻¹ * y * t) * t = y := by
    rw [← key (t⁻¹ * y * t)]
    group
  rw [key y, hz]
  tauto

/-- **Peterfalvi I Ch. I §2 Prop. 2(b), cardinality part.**  `|D| = |V| · |K|` for
`D = H ⊓ H^t`, `V = C_D(t)`, `K = J(D,t)`. -/
theorem card_twoPoint_eq_card_centD_mul_ncard_invertedBy [Finite G] {H : Subgroup G}
    (h : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) :
    Nat.card (twoPoint H t) =
      Nat.card (centD H t : Subgroup G) *
        (invertedBy (twoPoint H t) t).ncard := by
  have hodd : Odd (Nat.card (twoPoint H t)) := by
    rw [twoPoint_eq]
    exact IsStronglyEmbedded.odd_card_inf_conj h htH
  have := card_eq_mul_ncard_invertedBy (G := G) (X := twoPoint H t) (t := t) ht hodd
    (mem_normalizer_twoPoint H ht)
  simpa only [centD_eq] using this

end Work.ThreePoints
