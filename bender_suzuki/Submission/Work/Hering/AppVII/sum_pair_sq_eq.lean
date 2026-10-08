import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- The sum-of-squared-differences identity: for a finite family of integers, the double sum of
squared differences is twice the "total variance" expression.  (Expand `(n i - n j)^2 =
n i^2 - 2 * n i * n j + n j^2` and sum over `i` and `j`.) -/
theorem sum_pair_sq_eq {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    (∑ i, ∑ j, (n i - n j) ^ 2)
      = 2 * ((Fintype.card ι : ℤ) * ∑ i, n i ^ 2 - (∑ i, n i) ^ 2) := by
  -- Expand the square and split the inner sums term by term.
  have hconst : ∀ i : ι, (∑ j : ι, n i ^ 2) = (Fintype.card ι : ℤ) * n i ^ 2 := by
    intro i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcross : ∀ i : ι, (∑ j : ι, 2 * (n i * n j)) = 2 * n i * (∑ j : ι, n j) := by
    intro i
    rw [show (∑ j : ι, 2 * (n i * n j)) = ∑ j : ι, (2 * n i) * n j from
      Finset.sum_congr rfl (fun j _ => by ring)]
    rw [Finset.mul_sum]
  calc (∑ i, ∑ j, (n i - n j) ^ 2)
      = ∑ i, ∑ j, (n i ^ 2 + n j ^ 2 - 2 * (n i * n j)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = ∑ i, ((∑ j : ι, n i ^ 2) + (∑ j : ι, n j ^ 2) - (∑ j : ι, 2 * (n i * n j))) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ i, ((Fintype.card ι : ℤ) * n i ^ 2 + (∑ j : ι, n j ^ 2)
            - 2 * n i * (∑ j : ι, n j)) := by
        apply Finset.sum_congr rfl; intro i _
        rw [hconst i, hcross i]
    _ = (Fintype.card ι : ℤ) * (∑ i, n i ^ 2) + (Fintype.card ι : ℤ) * (∑ j, n j ^ 2)
          - 2 * (∑ i, n i) * (∑ j, n j) := by
        have h1 : (∑ i : ι, (Fintype.card ι : ℤ) * n i ^ 2)
            = (Fintype.card ι : ℤ) * ∑ i, n i ^ 2 := by
          rw [Finset.mul_sum]
        have h2 : (∑ i : ι, (∑ j : ι, n j ^ 2))
            = (Fintype.card ι : ℤ) * (∑ j : ι, n j ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have h3 : (∑ i : ι, 2 * n i * (∑ j : ι, n j))
            = 2 * (∑ i, n i) * (∑ j : ι, n j) := by
          rw [show (∑ i : ι, 2 * n i * (∑ j : ι, n j))
              = ∑ i : ι, (2 * (∑ j : ι, n j)) * n i from
            Finset.sum_congr rfl (fun i _ => by ring)]
          rw [← Finset.mul_sum]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2, h3]
    _ = 2 * ((Fintype.card ι : ℤ) * ∑ i, n i ^ 2 - (∑ i, n i) ^ 2) := by
        have hswap1 : (∑ j : ι, n j) = ∑ i : ι, n i := Finset.sum_congr rfl (fun _ _ => rfl)
        have hswap2 : (∑ j : ι, n j ^ 2) = ∑ i : ι, n i ^ 2 :=
          Finset.sum_congr rfl (fun _ _ => rfl)
        rw [hswap1, hswap2]
        ring

end Work.Hering.AppVII
