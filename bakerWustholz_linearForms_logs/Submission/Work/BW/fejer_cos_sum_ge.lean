import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- Incrementing the bound of a double `range` sum peels off the last row, the last
column and the corner term. -/
private lemma sum_double_succ {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1), f j l)
      = (∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, f j l)
        + (∑ j ∈ Finset.range n, f j n) + (∑ l ∈ Finset.range n, f n l) + f n n := by
  rw [Finset.sum_range_succ]
  simp only [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib]
  abel

/-- Reflection of a sum: `∑_{l<n} g(n-l) = ∑_{k<n} g(k+1)`. -/
private lemma cos_reflect_sum (n : ℕ) (ψ : ℝ) :
    (∑ l ∈ Finset.range n, Real.cos (((n - l : ℕ) : ℝ) * ψ))
      = ∑ k ∈ Finset.range n, Real.cos (((k:ℝ)+1) * ψ) := by
  rw [← Finset.sum_range_reflect (fun k => Real.cos (((k:ℝ)+1)*ψ)) n]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l < n := Finset.mem_range.mp hl
  congr 1
  have hcast : ((n - 1 - l : ℕ) : ℝ) + 1 = ((n - l : ℕ) : ℝ) := by
    have h1 : n - 1 - l + 1 = n - l := by omega
    rw [← h1]; push_cast; ring
  rw [← hcast]

/-- The column sum of the Fejér double sum. -/
private lemma cos_col_sum (n : ℕ) (ψ : ℝ) :
    (∑ l ∈ Finset.range n, Real.cos ((n:ℝ)*ψ - (l:ℝ)*ψ))
      = ∑ k ∈ Finset.range n, Real.cos (((k:ℝ)+1) * ψ) := by
  have h1 : ∀ l ∈ Finset.range n,
      Real.cos ((n:ℝ)*ψ - (l:ℝ)*ψ) = Real.cos (((n-l:ℕ):ℝ)*ψ) := by
    intro l hl
    have hl' : l < n := Finset.mem_range.mp hl
    congr 1
    rw [Nat.cast_sub (le_of_lt hl')]; ring
  rw [Finset.sum_congr rfl h1, cos_reflect_sum]

/-- The row sum of the Fejér double sum. -/
private lemma cos_row_sum (n : ℕ) (ψ : ℝ) :
    (∑ j ∈ Finset.range n, Real.cos ((j:ℝ)*ψ - (n:ℝ)*ψ))
      = ∑ k ∈ Finset.range n, Real.cos (((k:ℝ)+1) * ψ) := by
  have h1 : ∀ j ∈ Finset.range n,
      Real.cos ((j:ℝ)*ψ - (n:ℝ)*ψ) = Real.cos (((n-j:ℕ):ℝ)*ψ) := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [show (j:ℝ)*ψ - (n:ℝ)*ψ = -(((n-j:ℕ):ℝ)*ψ) by
      rw [Nat.cast_sub (le_of_lt hj')]; ring]
    rw [Real.cos_neg]
  rw [Finset.sum_congr rfl h1, cos_reflect_sum]

/-- The Fejér kernel identity in `range` form: the double cosine sum of the first
`K+1` terms equals `(K+1) + 2 ∑_{k<K} (K-k) cos((k+1)ψ)`. -/
private lemma fejer_aux (K : ℕ) (ψ : ℝ) :
    (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (K+1), Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ))
      = ((K:ℝ)+1) + 2 * ∑ k ∈ Finset.range K, (((K:ℝ) - (k:ℝ)) * Real.cos (((k:ℝ)+1)*ψ)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hF : (∑ j ∈ Finset.range (K+1+1), ∑ l ∈ Finset.range (K+1+1),
          Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ))
        = (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (K+1),
            Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ))
          + (1 + 2 * ∑ k ∈ Finset.range (K+1), Real.cos (((k:ℝ)+1)*ψ)) := by
      rw [sum_double_succ (fun j l => Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ)) (K+1)]
      rw [cos_row_sum (K+1) ψ, cos_col_sum (K+1) ψ]
      rw [show Real.cos ((((K+1:ℕ)):ℝ)*ψ - (((K+1:ℕ)):ℝ)*ψ) = 1 by
        rw [sub_self, Real.cos_zero]]
      ring
    have hG : ((K:ℝ)+1+1) + 2 * ∑ k ∈ Finset.range (K+1),
          (((K:ℝ)+1 - (k:ℝ)) * Real.cos (((k:ℝ)+1)*ψ))
        = (((K:ℝ)+1) + 2 * ∑ k ∈ Finset.range K,
            (((K:ℝ) - (k:ℝ)) * Real.cos (((k:ℝ)+1)*ψ)))
          + (1 + 2 * ∑ k ∈ Finset.range (K+1), Real.cos (((k:ℝ)+1)*ψ)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsplit : ∑ k ∈ Finset.range K, (((K:ℝ)+1 - (k:ℝ)) * Real.cos (((k:ℝ)+1)*ψ))
          = ∑ k ∈ Finset.range K, (((K:ℝ) - (k:ℝ)) * Real.cos (((k:ℝ)+1)*ψ))
            + ∑ k ∈ Finset.range K, Real.cos (((k:ℝ)+1)*ψ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hsplit]
      ring
    push_cast
    rw [hF, hG, ih]

/-- The Fejér double cosine sum is a sum of two squares, hence nonnegative. -/
private lemma fejer_sumsq (n : ℕ) (ψ : ℝ) :
    (∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ))
      = (∑ j ∈ Finset.range n, Real.cos ((j:ℝ)*ψ))^2
        + (∑ j ∈ Finset.range n, Real.sin ((j:ℝ)*ψ))^2 := by
  have h : ∀ j l : ℕ, Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ)
      = Real.cos ((j:ℝ)*ψ)*Real.cos ((l:ℝ)*ψ) + Real.sin ((j:ℝ)*ψ)*Real.sin ((l:ℝ)*ψ) :=
    fun j l => Real.cos_sub _ _
  simp_rw [h, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
  ring

/-- Rewriting a sum over `Icc 1 n` as a sum over `range n` shifted by one. -/
private lemma Icc_sum_eq_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 n, f m = ∑ k ∈ Finset.range n, f (k+1) := by
  rw [← Finset.Ico_succ_right_eq_Icc (1:ℕ) n]
  rw [show Order.succ n = n + 1 from by simp]
  rw [Finset.sum_Ico_eq_sum_range f 1 (n+1)]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring

/-- **Fejér kernel bound.** The cosine Fejér sum `∑_{k=1}^K (1 - k/(K+1)) cos(2πkθ)` is bounded
below by `-1/2`. Equivalently `1 + 2 * (that sum) = (K+1)⁻¹ * ‖∑_{j=0}^K exp(2πi j θ)‖² ≥ 0`. -/
theorem fejer_cos_sum_ge (K : ℕ) (θ : ℝ) :
    -(1 / 2 : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (1 - (k : ℝ) / (K + 1)) * Real.cos (2 * Real.pi * k * θ) := by
  set ψ : ℝ := 2 * Real.pi * θ with hψ
  -- The Fejér identity in `Icc` form.
  have hIcc : (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (K+1),
        Real.cos ((j:ℝ)*ψ - (l:ℝ)*ψ))
      = ((K:ℝ)+1) + 2 * ∑ m ∈ Finset.Icc 1 K,
          (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ) := by
    rw [fejer_aux K ψ]
    have hconv : (∑ m ∈ Finset.Icc 1 K, (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ))
        = ∑ k ∈ Finset.range K, (((K:ℝ)-(k:ℝ))*Real.cos (((k:ℝ)+1)*ψ)) := by
      rw [Icc_sum_eq_range K (fun m => (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ))]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    rw [hconv]
  -- The same expression equals a sum of squares, hence is nonnegative.
  have key : (∑ j ∈ Finset.range (K+1), Real.cos ((j:ℝ)*ψ))^2
        + (∑ j ∈ Finset.range (K+1), Real.sin ((j:ℝ)*ψ))^2
      = ((K:ℝ)+1) + 2 * ∑ m ∈ Finset.Icc 1 K,
          (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ) := by
    rw [← fejer_sumsq (K+1) ψ, hIcc]
  have hsq : (0:ℝ) ≤ (∑ j ∈ Finset.range (K+1), Real.cos ((j:ℝ)*ψ))^2
        + (∑ j ∈ Finset.range (K+1), Real.sin ((j:ℝ)*ψ))^2 := by positivity
  have hnn : (0:ℝ) ≤ ((K:ℝ)+1) + 2 * ∑ m ∈ Finset.Icc 1 K,
        (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ) := by
    rw [← key]; exact hsq
  -- Factor out `K+1`.
  have hfac : ∑ m ∈ Finset.Icc 1 K, (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ)
      = ((K:ℝ)+1) * ∑ m ∈ Finset.Icc 1 K,
          (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    field_simp
  have hprod : (0:ℝ) ≤ ((K:ℝ)+1) * (1 + 2 * ∑ m ∈ Finset.Icc 1 K,
        (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ)) := by
    have hthis : ((K:ℝ)+1) * (1 + 2 * ∑ m ∈ Finset.Icc 1 K,
          (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ))
        = ((K:ℝ)+1) + 2 * ∑ m ∈ Finset.Icc 1 K,
            (((K:ℝ)+1)-(m:ℝ))*Real.cos ((m:ℝ)*ψ) := by
      rw [hfac]; ring
    rw [hthis]; exact hnn
  have hK : (0:ℝ) < (K:ℝ)+1 := by positivity
  have hlin : (0:ℝ) ≤ 1 + 2 * ∑ m ∈ Finset.Icc 1 K,
        (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ) :=
    nonneg_of_mul_nonneg_right hprod hK
  have hL : -(1/2:ℝ) ≤ ∑ m ∈ Finset.Icc 1 K,
        (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ) := by linarith
  -- Rewrite the cosine sum in the statement into the form used above.
  have hLeq : (∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/(K+1))*Real.cos (2*Real.pi*k*θ))
      = ∑ m ∈ Finset.Icc 1 K, (1 - (m:ℝ)/((K:ℝ)+1))*Real.cos ((m:ℝ)*ψ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hcos : Real.cos (2 * Real.pi * (m:ℝ) * θ) = Real.cos ((m:ℝ) * ψ) := by
      rw [hψ]; congr 1; ring
    rw [hcos]
  rw [hLeq]; exact hL

end Work.BW
