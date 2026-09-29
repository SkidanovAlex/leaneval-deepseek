import Mathlib
import Submission.Work.KronP.kdefs

/-!
# `Work.KronP.packMul`: the Kronecker packing is multiplicative

The packing `pack l b = Σ_j l[j]·2^{b·j}` turns the product of two packed integers into the
convolution of their coefficient lists:

`pack l₁ b * pack l₂ b = Σ_{m < |l₁|+|l₂|} convCoef l₁ l₂ m · 2^{b·m}`.

This is the arithmetic content of the first half of paper Lemma 2.5: the base-`2^b` digits of
the product of the two packings are the convolution coefficients (once nonnegativity is fixed
by the offset `digitOffset`; that step is `Work.KronP.digitsId`).

Route.  `pack` and the RHS are first rewritten as `Finset` sums; the product of two finite sums
is expanded with `Finset.sum_mul`/`Finset.mul_sum` into a sum over the product finset, which is
then grouped by the value of `j + k` (`Finset.sum_fiberwise_of_maps_to`).  The single remaining
combinatorial step is that the pairs `(j,k)` with `j + k = m`, `j < |l₁|`, `k < |l₂|` are the
antidiagonal of `m` intersected with the product of the two ranges; since `getD` is `0` outside
the list, the discarded terms vanish and the sum collapses to `Σ_{j ≤ m} l₁[j]·l₂[m-j]`, which
is `convCoef` (whose definition filters by exactly those two conditions).
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## Bridging list sums and finset sums -/

/-- A sum over `List.range` is a `Finset` sum. -/
theorem list_sum_map_range (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A sum over a filtered `List.range` is a sum over the filtered `Finset.range`
(the index list has no repetitions). -/
theorem sum_filter_map_range {k : ℕ} (p : ℕ → Bool) (f : ℕ → ℤ) :
    (((List.range k).filter p).map f).sum =
      ∑ x ∈ (Finset.range k).filter (fun x => p x = true), f x := by
  rw [← List.sum_toFinset f (List.Nodup.filter p (List.nodup_range (n := k)))]
  rw [List.toFinset_filter, List.toFinset_range]

/-! ## `convCoef` as a plain range sum -/

/-- `convCoef` as a `Finset` sum over the filtered range of admissible `j`. -/
theorem convCoef_eq_finset (l₁ l₂ : List ℤ) (m : ℕ) :
    convCoef l₁ l₂ m =
      ∑ j ∈ (Finset.range (min l₁.length (m + 1))).filter (fun j => m - j < l₂.length),
        l₁.getD j 0 * l₂.getD (m - j) 0 := by
  rw [convCoef, sum_filter_map_range]
  refine Finset.sum_congr ?_ (fun j _ => rfl)
  ext j
  simp [Finset.mem_filter, decide_eq_true_eq]

/-- Since `getD` is `0` past the end of a list, `convCoef l₁ l₂ m` is simply the sum of
`l₁[j]·l₂[m-j]` for `j ≤ m`. -/
theorem convCoef_eq_range (l₁ l₂ : List ℤ) (m : ℕ) :
    convCoef l₁ l₂ m = ∑ j ∈ Finset.range (m + 1), l₁.getD j 0 * l₂.getD (m - j) 0 := by
  rw [convCoef_eq_finset]
  refine Finset.sum_subset ?hsub ?hzero
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min] at hj
    exact Finset.mem_range.mpr hj.1.2
  · intro x hx hxn
    have hx' : x < m + 1 := Finset.mem_range.mp hx
    by_cases h1 : x < l₁.length
    · have h2 : ¬ (m - x < l₂.length) := by
        intro h2
        exact hxn (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_min.mpr ⟨h1, hx'⟩), h2⟩)
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h2), mul_zero]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h1), zero_mul]

/-- The pairs `(j,k)` of indices with `j+k = m`, `j < |l₁|`, `k < |l₂|`, summed with the
coefficient products, give the range form of `convCoef`: the terms with an index past the end
of a list are `0`, so the filters `j < |l₁|`, `k < |l₂|` can be dropped. -/
theorem sum_filter_prod_eq_range (l₁ l₂ : List ℤ) (m : ℕ) :
    (∑ p ∈ ((Finset.range l₁.length) ×ˢ (Finset.range l₂.length)).filter
        (fun p => p.1 + p.2 = m), l₁.getD p.1 0 * l₂.getD p.2 0) =
      ∑ j ∈ Finset.range (m + 1), l₁.getD j 0 * l₂.getD (m - j) 0 := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => l₁.getD a 0 * l₂.getD b 0) m]
  refine Finset.sum_subset ?hsub ?hzero
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact (Finset.mem_filter.mp hp).2
  · intro x hx hxn
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : x.1 < l₁.length
    · have h2 : ¬ x.2 < l₂.length := by
        intro h2
        exact hxn (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩, hx⟩)
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h2), mul_zero]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h1), zero_mul]

/-! ## Multiplying two packed sums -/

/-- The product of two geometric-like sums, grouped by the value of the exponent sum: this is
the generating-function form of the convolution identity. -/
theorem mul_sum_pow (A Bs : Finset ℕ) (f g : ℕ → ℤ) (B : ℤ) (N : ℕ)
    (hN : ∀ a ∈ A, ∀ c ∈ Bs, a + c < N) :
    (∑ a ∈ A, f a * B ^ a) * (∑ c ∈ Bs, g c * B ^ c) =
      ∑ m ∈ Finset.range N,
        (∑ p ∈ (A ×ˢ Bs).filter (fun p => p.1 + p.2 = m), f p.1 * g p.2) * B ^ m := by
  have hmain : (∑ a ∈ A, f a * B ^ a) * (∑ c ∈ Bs, g c * B ^ c)
      = ∑ p ∈ A ×ˢ Bs, (f p.1 * g p.2) * B ^ (p.1 + p.2) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun c hc => ?_))
    rw [pow_add]; ring
  rw [hmain]
  rw [← Finset.sum_fiberwise_of_maps_to (s := A ×ˢ Bs) (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2)
    (fun p hp => Finset.mem_range.mpr
      (hN p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2))
    (fun p => (f p.1 * g p.2) * B ^ (p.1 + p.2))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [(Finset.mem_filter.mp hp).2]

/-! ## The target -/

theorem packMul (l₁ l₂ : List ℤ) (b : ℕ) :
    Work.KronP.pack l₁ b * Work.KronP.pack l₂ b =
      ((List.range (l₁.length + l₂.length)).map
        (fun m => Work.KronP.convCoef l₁ l₂ m * (2 : ℤ) ^ (b * m))).sum := by
  have hpack : ∀ l : List ℤ,
      pack l b = ∑ j ∈ Finset.range l.length, l.getD j 0 * ((2 : ℤ) ^ b) ^ j := by
    intro l
    rw [pack, list_sum_map_range]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [pow_mul]
  have hrhs : ((List.range (l₁.length + l₂.length)).map
        (fun m => convCoef l₁ l₂ m * (2 : ℤ) ^ (b * m))).sum
      = ∑ m ∈ Finset.range (l₁.length + l₂.length),
          convCoef l₁ l₂ m * ((2 : ℤ) ^ b) ^ m := by
    rw [list_sum_map_range]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [pow_mul]
  rw [hpack l₁, hpack l₂, hrhs]
  rw [mul_sum_pow (Finset.range l₁.length) (Finset.range l₂.length) (fun j => l₁.getD j 0)
        (fun k => l₂.getD k 0) ((2 : ℤ) ^ b) (l₁.length + l₂.length) ?_]
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [sum_filter_prod_eq_range, convCoef_eq_range]
  · intro a ha c hc
    simp only [Finset.mem_range] at ha hc
    omega

end Work.KronP
