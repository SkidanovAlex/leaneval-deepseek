import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- If `b i ≡ u i [ZMOD p^k]` for all `i`, then the `j`-th power sums agree modulo `p^j`
for every `j ≤ k`; subtracting the same integer `H j` from both sides is harmless. -/
lemma pow_sum_sub_modEq {k : ℕ} (p : ℕ) (u b : Fin k → ℤ) (H : ℕ → ℕ)
    (h : ∀ i, b i ≡ u i [ZMOD (p : ℤ) ^ k]) (j : ℕ) (hjk : j ≤ k) :
    ((∑ i, b i ^ j) - (H j : ℤ)) ≡ ((∑ i, u i ^ j) - (H j : ℤ)) [ZMOD (p : ℤ) ^ j] := by
  have hsum : (∑ i, b i ^ j) ≡ (∑ i, u i ^ j) [ZMOD (p : ℤ) ^ j] :=
    Int.ModEq.sum (s := Finset.univ) (f := fun i => b i ^ j) (g := fun i => u i ^ j)
      (fun i _ => ((h i).of_dvd (pow_dvd_pow (p : ℤ) hjk)).pow j)
  exact hsum.sub (Int.ModEq.refl (H j : ℤ))

end Work.BMF.recursion
