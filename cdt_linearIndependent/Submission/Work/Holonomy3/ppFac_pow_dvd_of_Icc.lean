import Mathlib
import Submission.Work.Holonomy3.log_den_defs

namespace Work.Holonomy3

open scoped BigOperators

/-- **`ppFac` collects every proper prime power in the window.**  If `p` is prime and for every
`j ∈ [a,b]` the power `p^j` satisfies `l < p^j ≤ n`, then `p` occurs in the inner product of
`ppFac l n` at the index `j`, for each of the `b + 1 - a` values of `j`; hence
`p ^ (b + 1 - a) ∣ ppFac l n`. -/
lemma ppFac_pow_dvd_of_Icc {l n p a b : ℕ} (hp : p.Prime) (hpn : p ≤ n) (ha : 2 ≤ a)
    (hb : b ≤ n) (hcond : ∀ j ∈ Finset.Icc a b, l < p ^ j ∧ p ^ j ≤ n) :
    p ^ (b + 1 - a) ∣ Work.Holonomy3.ppFac l n := by
  have hsub : Finset.Icc a b ⊆ Finset.Icc 2 n := by
    intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨le_trans ha hj.1, le_trans hj.2 hb⟩
  have hinner : ∀ j ∈ Finset.Icc a b,
      p ∣ ∏ q ∈ (Finset.Icc 1 n).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ n), q := by
    intro j hj
    refine Finset.dvd_prod_of_mem (fun q => q) ?_
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_lt.le, hpn⟩, hp, (hcond j hj).1, (hcond j hj).2⟩
  have h1 : (∏ _j ∈ Finset.Icc a b, p) ∣ ∏ j ∈ Finset.Icc a b,
      (∏ q ∈ (Finset.Icc 1 n).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ n), q) :=
    Finset.prod_dvd_prod_of_dvd _ _ hinner
  have h2 : (∏ j ∈ Finset.Icc a b,
      (∏ q ∈ (Finset.Icc 1 n).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ n), q)) ∣
      ∏ j ∈ Finset.Icc 2 n,
      (∏ q ∈ (Finset.Icc 1 n).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ n), q) :=
    Finset.prod_dvd_prod_of_subset (Finset.Icc a b) (Finset.Icc 2 n) _ hsub
  rw [ppFac]
  rw [show p ^ (b + 1 - a) = ∏ _j ∈ Finset.Icc a b, p by
    rw [Finset.prod_const, Nat.card_Icc]]
  exact dvd_trans h1 h2

end Work.Holonomy3
