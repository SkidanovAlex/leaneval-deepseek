import Mathlib
import Submission.Work.PGroup.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped BigOperators Pointwise

namespace Work.Hering.AppVII

/-- When `Q` is normal, `P ⊓ Q = ⊥` and `P ⊔ Q = ⊤`, every element of `H` factors uniquely as
`q * s` with `q ∈ Q`, `s ∈ P`; hence the multiplication map `↥Q × ↥P → H` is a bijection
(`Subgroup.IsComplement'`).  Reindexing gives the stated identity of sums. -/
theorem part2_sum_bijection {H : Type*} [Group H] [Fintype H] (Q P : Subgroup H) [Fintype ↥Q]
    [Fintype ↥P] (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (f : H → ℝ) :
    ∑ y : H, f y = ∑ s : ↥P, ∑ q : ↥Q, f ((q : H) * (s : H)) := by
  -- `Q` and `P` are disjoint subgroups.
  have hdisj : Disjoint Q P := by
    rw [disjoint_iff, inf_comm]
    exact hinf
  -- Because `Q` is normal, every element of `Q ⊔ P = ⊤` is a product `q * p` with `q ∈ Q`, `p ∈ P`,
  -- i.e. the set product `↑Q * ↑P` is all of `H`.
  have hmul : (Q : Set H) * (P : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_mul]
    have hx : x ∈ Q ⊔ P := by rw [sup_comm, hsup]; exact Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left (s := Q) (t := P) (hs := hQn)] at hx
    exact hx
  -- Hence `Q` and `P` are complements, so `(q, p) ↦ q * p` is a bijection.
  have hcompl : Subgroup.IsComplement' Q P :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hbij : Function.Bijective (fun x : ↥Q × ↥P => (x.1 : H) * (x.2 : H)) :=
    (Subgroup.isComplement_iff_bijective Q P).mp hcompl
  -- Reversing the two factors gives bijectivity of `(s, q) ↦ q * s`.
  have hbij' : Function.Bijective (fun x : ↥P × ↥Q => (x.2 : H) * (x.1 : H)) := by
    have h := hbij.comp (Equiv.prodComm (α := ↥P) (β := ↥Q)).bijective
    simpa using h
  -- Reindex the sum over `H` by this bijection, then split the sum over the product type.
  rw [← Fintype.sum_prod_type (f := fun x : ↥P × ↥Q => f ((x.2 : H) * (x.1 : H)))]
  exact (Fintype.sum_bijective (fun x : ↥P × ↥Q => (x.2 : H) * (x.1 : H)) hbij'
    (fun x => f ((x.2 : H) * (x.1 : H))) f (fun _ => rfl)).symm

end Work.Hering.AppVII
