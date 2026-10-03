/-
# The elementary quadratic-bound for a summable kernel on `ℤ`

For a nonnegative summable kernel `κ : ℤ → ℝ` and any real weight `a : ℤ → ℝ`, the symmetric
quadratic form built from the Toeplitz kernel `(i, j) ↦ κ (i - j)` is bounded by the product of
the `ℓ¹`-mass of the kernel and the `ℓ²`-mass of the weight on any finite set `S`:

`∑_{i ∈ S} ∑_{j ∈ S} κ (i - j) a_i a_j ≤ (∑'_m κ m) (∑_{i ∈ S} a_i^2)`.

This is the elementary Schur/Young input used by `Work.KMTAreas.A4Z.schur_finite`: it is the
discrete form of `⟨f, κ * f⟩ ≤ ‖κ‖₁ ‖f‖₂²` for the convolution quadratic form.

## Proof

The pointwise arithmetic–geometric mean inequality (`two_mul_le_add_sq`)

`κ (i - j) a i a j ≤ (1/2) (κ (i - j) (a i)^2 + κ (i - j) (a j)^2)`

(valid because `κ (i - j) ≥ 0`) splits the double sum into the two "diagonal" sums

`D₁ = ∑_{i ∈ S} ∑_{j ∈ S} κ (i - j) (a i)^2`,  `D₂ = ∑_{i ∈ S} ∑_{j ∈ S} κ (i - j) (a j)^2`.

Each of them is bounded by `(∑'_m κ m) ∑_{i ∈ S} (a i)^2`: for fixed `i` (resp. `j`) the inner
sum `∑_{j ∈ S} κ (i - j)` is the sum of the nonnegative summable `κ` over the translated finite
set `S - i` (resp. `S` shifted by `-j`), hence at most the total mass `∑'_m κ m`
(`Summable.sum_le_tsum`, after reindexing by the injective map `x ↦ i - x` resp. `x ↦ x - j`).

Note that the hypothesis `0 ≤ a` is not needed: the estimate holds for every real weight `a`, by
the AM–GM inequality applied to `a i` and `a j`.
-/
import Mathlib

namespace Work.KMTAreas.A4Z

open scoped BigOperators

/-- The sum of a nonnegative summable function over the image of a finite set under an injective
map is at most the total sum. -/
private lemma sum_comp_le_tsum {κ : ℤ → ℝ} (hκ : ∀ m, 0 ≤ κ m) (hκsum : Summable κ)
    {g : ℤ → ℤ} (hg : Function.Injective g) (S : Finset ℤ) :
    ∑ j ∈ S, κ (g j) ≤ ∑' m : ℤ, κ m := by
  rw [← Finset.sum_image hg.injOn]
  exact hκsum.sum_le_tsum _ (fun m _ => hκ m)

theorem kappa_sum_le (S : Finset ℤ) (a κ : ℤ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hκ : ∀ m, 0 ≤ κ m) (hκsum : Summable κ) :
    ∑ i ∈ S, ∑ j ∈ S, κ (i - j) * a i * a j ≤ (∑' m : ℤ, κ m) * ∑ i ∈ S, (a i) ^ 2 := by
  have _ : (0 : ℝ) ≤ a 0 := ha 0
  set K : ℝ := ∑' m : ℤ, κ m with hK
  -- The two diagonal sums are each bounded by `K` times the `ℓ²`-mass.
  have hfirst : ∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a i) ^ 2 ≤ K * ∑ i ∈ S, (a i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (sum_comp_le_tsum hκ hκsum (sub_right_injective (b := i)) S) (sq_nonneg (a i))
  have hsecond : ∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a j) ^ 2 ≤ K * ∑ i ∈ S, (a i) ^ 2 := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (sum_comp_le_tsum hκ hκsum (sub_left_injective (b := j)) S) (sq_nonneg (a j))
  have hmid : ∑ i ∈ S, ∑ j ∈ S,
        (1/2) * (κ (i - j) * (a i)^2 + κ (i - j) * (a j)^2)
      = (1/2) * (∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a i)^2)
        + (1/2) * (∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a j)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ i ∈ S, ∑ j ∈ S, κ (i - j) * a i * a j
      ≤ ∑ i ∈ S, ∑ j ∈ S, (1/2) * (κ (i - j) * (a i)^2 + κ (i - j) * (a j)^2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h := hκ (i - j)
        nlinarith [sq_nonneg (a i - a j)]
    _ = (1/2) * (∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a i)^2)
        + (1/2) * (∑ i ∈ S, ∑ j ∈ S, κ (i - j) * (a j)^2) := hmid
    _ ≤ (1/2) * (K * ∑ i ∈ S, (a i)^2) + (1/2) * (K * ∑ i ∈ S, (a i)^2) := by
        linarith [hfirst, hsecond]
    _ = K * ∑ i ∈ S, (a i)^2 := by ring

end Work.KMTAreas.A4Z
