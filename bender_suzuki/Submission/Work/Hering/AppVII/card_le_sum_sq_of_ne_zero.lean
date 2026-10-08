import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

theorem card_le_sum_sq_of_ne_zero {p : ℕ} (f : Fin p → ℤ) (hf : ∀ i, 0 ≤ f i) :
    ((Finset.univ.filter (fun i => f i ≠ 0)).card : ℤ) ≤
      ∑ i ∈ Finset.univ.filter (fun i => f i ≠ 0), (f i) ^ 2 := by
  set s := Finset.univ.filter (fun i => f i ≠ 0) with hs
  -- Each nonzero entry is at least `1`, hence contributes at least `1` to the sum.
  have h1 : ∀ i ∈ s, (1 : ℤ) ≤ f i := by
    intro i hi
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have := hf i
    omega
  have h2 : (s.card : ℤ) ≤ ∑ i ∈ s, f i := by
    have : (∑ i ∈ s, (1 : ℤ)) ≤ ∑ i ∈ s, f i := Finset.sum_le_sum h1
    simpa using this
  -- Each entry dominates its square once it is at least `1`.
  have h3 : ∑ i ∈ s, f i ≤ ∑ i ∈ s, (f i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h1i := h1 i hi
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ f i) (by linarith : (0 : ℤ) ≤ f i - 1)]
  linarith

end Work.Hering.AppVII
