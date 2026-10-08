import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem fin_sum_split {M : Type*} [AddCommMonoid M] (n : ℕ) (g : Fin n → Fin n → M) :
    (∑ i, ∑ j, g i j)
      = (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.1 p.2)
        + (∑ i, g i i)
        + (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.2 p.1) := by
  classical
  -- The diagonal part: the filter `p.1 = p.2` picks out exactly the terms `g i i`.
  have hDsum :
      (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2), g p.1 p.2)
        = ∑ i, g i i := by
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp
  -- The strict lower-triangular part reindexes to the strict upper-triangular part
  -- with the arguments of `g` swapped.
  have hLsum :
      (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), g p.1 p.2)
        = (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.2 p.1) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun i j => if i < j then g j i else 0)]
  -- The complement of `p.1 < p.2` is the disjoint union of `p.2 < p.1` and `p.1 = p.2`.
  have hVeq : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)
      = (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)
        ∪ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro p _
    omega
  have hdsj : Disjoint ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1))
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2)) := by
    rw [Finset.disjoint_left]
    intro p hpL hpD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpL hpD
    omega
  -- Sum over the complement of `p.1 < p.2`.
  have hVsum :
      (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2), g p.1 p.2)
        = (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.2 p.1)
          + (∑ i, g i i) := by
    rw [hVeq, Finset.sum_union hdsj, hLsum, hDsum]
  -- Rewrite the double sum as a single sum over all ordered pairs.
  rw [(Fintype.sum_prod_type (fun p : Fin n × Fin n => g p.1 p.2)).symm]
  -- Split off the strictly upper-triangular pairs.
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
        (p := fun p : Fin n × Fin n => p.1 < p.2) (f := fun p : Fin n × Fin n => g p.1 p.2)]
  rw [hVsum]
  ac_rfl

end Work.Higman
