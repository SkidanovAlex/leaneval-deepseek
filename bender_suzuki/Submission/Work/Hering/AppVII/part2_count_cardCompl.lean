import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.Hering.AppVII

/-- If `Q` is normal in `H`, `P ⊓ Q = ⊥` and `P ⊔ Q = ⊤`, then `H` is the internal direct
product of `Q` and `P`, so `|H| = |Q| * |P|`.

Indeed `Q` and `P` are disjoint subgroups whose product set is all of `H` (normality of `Q`
turns the join into the set product), i.e. they are complementary subgroups; the cardinality
identity is `Subgroup.IsComplement'.card_mul_card`. -/
theorem part2_count_cardCompl {H : Type*} [Group H] [Fintype H] (Q P : Subgroup H)
    (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) :
    Nat.card H = Nat.card ↥Q * Nat.card ↥P := by
  -- `Q` and `P` are disjoint.
  have hdisj : Disjoint Q P := by
    rw [disjoint_iff, inf_comm]
    exact hinf
  -- Because `Q` is normal, every element of `Q ⊔ P = ⊤` is a product `q * p` with `q ∈ Q`,
  -- `p ∈ P`, i.e. the set product `↑Q * ↑P` is all of `H`.
  have hmul : (Q : Set H) * (P : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_mul]
    have hx : x ∈ Q ⊔ P := by rw [sup_comm, hsup]; exact Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left (s := Q) (t := P) (hs := hQn)] at hx
    exact hx
  -- Hence `Q` and `P` are complementary subgroups.
  have hcompl : Subgroup.IsComplement' Q P :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  exact (Subgroup.IsComplement'.card_mul_card hcompl).symm

end Work.Hering.AppVII
