/-
  WilG2 : the multinomial domination of the weighted sum over compositions.

  For `a b : ℕ → ℝ` with `a ≥ 0`, `b ≥ 0`, one has
  `Σ_{n ≤ r} Σ_{c : Composition n} b(|c|) ∏_i a(c_i) ≤ Σ_{p ≤ r} b(p) (a_1 + ... + a_r)^p`.

  The proof is a pure "no double counting" argument.  Each composition `c` of `n ≤ r` with `|c| = p`
  is sent to the tuple `(c_0 - 1, ..., c_{p-1} - 1) ∈ (Fin r)^p`; this is injective and its weight
  `∏_i a(c_i) = ∏_i a(f_i + 1)` matches the expansion `(a_1 + ... + a_r)^p = Σ_{f : Fin p → Fin r} ∏_i a(f_i + 1)`.
  Since the terms are nonnegative and there are no repeated images, the LHS sum is dominated by the
  full multinomial expansion.

  The map is packaged as `phiMap`, defined on the dependent sigma type
  `LIdx r = Σ n : Fin (r+1), Composition n` and valued in `RIdx r = Σ p : Fin (r+1), (Fin p → Fin r)`,
  so that the two sides of the inequality are sums over a single index type and the domination
  reduces to `Finset.sum_le_sum_of_subset_of_nonneg`.
-/
import Mathlib

open Finset

namespace Work.WilG2

/-- Index type of the composition sum: a natural number `n ≤ r` (as an element of `Fin (r+1)`)
together with a composition of `n`. -/
abbrev LIdx (r : ℕ) := Σ n : Fin (r + 1), Composition (n : ℕ)

/-- Index type of the multinomial expansion: `p ≤ r` together with a function `Fin p → Fin r`. -/
abbrev RIdx (r : ℕ) := Σ p : Fin (r + 1), (Fin (p : ℕ) → Fin r)

/-- A composition `c` of `n ≤ r` with `p` blocks is sent to the tuple of its parts minus one,
which is a function `Fin p → Fin r` because every part is positive and at most `n ≤ r`. -/
def phiMap (r : ℕ) (x : LIdx r) : RIdx r :=
  ⟨⟨x.2.length, lt_of_le_of_lt x.2.length_le x.1.isLt⟩,
   fun i => ⟨x.2.blocksFun i - 1, by
      have h1 : 1 ≤ x.2.blocksFun i := x.2.one_le_blocksFun i
      have h2 : x.2.blocksFun i ≤ (x.1 : ℕ) := x.2.blocksFun_le i
      have h3 : (x.1 : ℕ) < r + 1 := x.1.isLt
      omega⟩⟩

/-- The list of blocks is recovered from the image under `phiMap`, by adding one to every entry.
In particular `phiMap` is injective. -/
lemma recover_phiMap (r : ℕ) (x : LIdx r) :
    List.ofFn (fun i => ((phiMap r x).2 i : ℕ) + 1) = x.2.blocks := by
  simp only [phiMap]
  rw [← Composition.ofFn_blocksFun]
  rw [List.ofFn_inj]
  funext i
  exact Nat.sub_add_cancel (x.2.one_le_blocksFun i)

lemma phiMap_injective (r : ℕ) : Function.Injective (phiMap r) := by
  rintro ⟨n, c⟩ ⟨n', c'⟩ h
  have hb : c.blocks = c'.blocks := by
    rw [← recover_phiMap r ⟨n, c⟩, h, recover_phiMap r ⟨n', c'⟩]
  have hn : (n : ℕ) = (n' : ℕ) := by rw [← c.blocks_sum, hb, c'.blocks_sum]
  have hnn : n = n' := Fin.ext hn
  subst hnn
  exact Sigma.ext rfl (heq_of_eq (Composition.ext hb))

/-- Rewriting the composition sum as a sum over the sigma type `LIdx r`. -/
lemma lhs_eq (r : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ Finset.range (r + 1),
        ∑ c : Composition n, b c.length * ∏ i : Fin c.length, a (c.blocksFun i))
      = ∑ x : LIdx r, b x.2.length * ∏ i : Fin x.2.length, a (x.2.blocksFun i) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun n => ∑ c : Composition n, b c.length * ∏ i : Fin c.length, a (c.blocksFun i)) (r + 1)]
  rw [← Finset.univ_sigma_univ (κ := fun n : Fin (r + 1) => Composition (n : ℕ))]
  rw [Finset.sum_sigma]

/-- The right hand side is the multinomial expansion over the sigma type `RIdx r`. -/
lemma rhs_eq (r : ℕ) (a b : ℕ → ℝ) :
    (∑ y : RIdx r, b (y.1 : ℕ) * ∏ i : Fin (y.1 : ℕ), a ((y.2 i : ℕ) + 1))
      = ∑ p ∈ Finset.range (r + 1), b p * (∑ j : Fin r, a (j + 1)) ^ p := by
  have h1 : (∑ y : RIdx r, b (y.1 : ℕ) * ∏ i : Fin (y.1 : ℕ), a ((y.2 i : ℕ) + 1))
      = ∑ p : Fin (r + 1), ∑ f : Fin (p : ℕ) → Fin r,
          b (p : ℕ) * ∏ i : Fin (p : ℕ), a ((f i : ℕ) + 1) := by
    rw [← Finset.univ_sigma_univ (κ := fun p : Fin (r + 1) => (Fin (p : ℕ) → Fin r))]
    rw [Finset.sum_sigma]
  rw [h1]
  rw [← Fin.sum_univ_eq_sum_range (fun p => b p * (∑ j : Fin r, a (j + 1)) ^ p) (r + 1)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Fintype.sum_pow (f := fun j : Fin r => a ((j : ℕ) + 1)) (n := (p : ℕ))]
  rw [Finset.mul_sum]

/-- The weight of a composition equals the weight of its image under `phiMap`. -/
lemma phi_point (r : ℕ) (a b : ℕ → ℝ) (x : LIdx r) :
    b x.2.length * ∏ i : Fin x.2.length, a (x.2.blocksFun i)
      = b ((phiMap r x).1 : ℕ) *
          ∏ i : Fin ((phiMap r x).1 : ℕ), a (((phiMap r x).2 i : ℕ) + 1) := by
  simp only [phiMap]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [Nat.sub_add_cancel (x.2.one_le_blocksFun i)]

theorem sum_composition_mul_prod_le (r : ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    (∑ n ∈ Finset.range (r + 1),
        ∑ c : Composition n, b c.length * ∏ i : Fin c.length, a (c.blocksFun i))
      ≤ ∑ p ∈ Finset.range (r + 1), b p * (∑ j : Fin r, a (j + 1)) ^ p := by
  classical
  rw [lhs_eq r a b, ← rhs_eq r a b]
  calc (∑ x : LIdx r, b x.2.length * ∏ i : Fin x.2.length, a (x.2.blocksFun i))
      = ∑ x : LIdx r, b ((phiMap r x).1 : ℕ) *
          ∏ i : Fin ((phiMap r x).1 : ℕ), a (((phiMap r x).2 i : ℕ) + 1) :=
        Finset.sum_congr rfl (fun x _ => phi_point r a b x)
    _ = ∑ y ∈ (Finset.univ : Finset (LIdx r)).image (phiMap r),
          b (y.1 : ℕ) * ∏ i : Fin (y.1 : ℕ), a ((y.2 i : ℕ) + 1) := by
        rw [Finset.sum_image]
        intro x _ y _ h
        exact phiMap_injective r h
    _ ≤ ∑ y ∈ (Finset.univ : Finset (RIdx r)),
          b (y.1 : ℕ) * ∏ i : Fin (y.1 : ℕ), a ((y.2 i : ℕ) + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intro y _ _
          exact mul_nonneg (hb _) (Finset.prod_nonneg (fun i _ => ha _))
    _ = ∑ y : RIdx r, b (y.1 : ℕ) * ∏ i : Fin (y.1 : ℕ), a ((y.2 i : ℕ) + 1) := rfl

end Work.WilG2
