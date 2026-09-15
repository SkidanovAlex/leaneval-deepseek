import Mathlib

namespace Commons.Combinatorics.Additive.Szemeredi

/-- Multiplying each value of `f` by a constant `t` multiplies the length-`k` AP count
(sum over starts `x` and common differences `r` of the product along the progression)
by `t ^ k`. -/
lemma sum_ap_mul_const {p : ℕ} [NeZero p] (f : ZMod p → ℝ) (t : ℝ) (k : ℕ) :
    (∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, (t * f (x + (j : ZMod p) * r)))
      = t ^ k * ∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k,
          f (x + (j : ZMod p) * r) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem ap_count_lower_of_dense_scaled {δ c η : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hη : 0 ≤ η)
    {k : ℕ} (hk : 2 ≤ k) {P₀ : ℕ}
    (hDense : ∀ (p : ℕ) [NeZero p], Nat.Prime p → P₀ ≤ p → ∀ g : ZMod p → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δ * (p : ℝ) ≤ ∑ x, g x →
      c * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod p) * r))
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpP : P₀ ≤ p)
    {f : ZMod p → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1 + η)
    (hfm : δ * (1 + η) * (p : ℝ) ≤ ∑ x, f x) :
    ((1 + η) ^ k * c) * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
      ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) := by
  have hpos : 0 < 1 + η := by linarith
  have hg0 : ∀ x, 0 ≤ f x / (1 + η) := fun x => div_nonneg (hf0 x) (le_of_lt hpos)
  have hg1 : ∀ x, f x / (1 + η) ≤ 1 := by
    intro x; rw [div_le_one hpos]; linarith [hf1 x]
  have hgm : δ * (p : ℝ) ≤ ∑ x, f x / (1 + η) := by
    rw [← Finset.sum_div]
    rw [le_div_iff₀ hpos]
    nlinarith [hfm]
  have H := hDense p hp hpP (fun x => f x / (1 + η)) hg0 hg1 hgm
  have hA : (∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r))
      = (1 + η) ^ k * (∑ x : ZMod p, ∑ r : ZMod p,
          ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) / (1 + η)) := by
    rw [← sum_ap_mul_const (fun y => f y / (1 + η)) (1 + η) k]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro r _
    apply Finset.prod_congr rfl; intro j _
    field_simp
  have H' : c * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
      ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) / (1 + η) := H
  rw [hA]
  calc ((1 + η) ^ k * c) * (p : ℝ) ^ 2
      = (1 + η) ^ k * (c * (p : ℝ) ^ 2) := by ring
    _ ≤ (1 + η) ^ k * (∑ x : ZMod p, ∑ r : ZMod p,
          ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) / (1 + η)) :=
        mul_le_mul_of_nonneg_left H' (pow_nonneg (le_of_lt hpos) k)

end Commons.Combinatorics.Additive.Szemeredi
