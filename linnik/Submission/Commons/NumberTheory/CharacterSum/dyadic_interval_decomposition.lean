import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star

namespace Commons.NumberTheory.CharacterSum

open Finset

/-- **Dyadic (binary) decomposition of a sum over an interval.**
For any function `f : ℤ → ℂ`, any `t : ℕ`, any starting point `a : ℤ` and any length `k ≤ 2^t`,
the sum over the interval `(a, a+k]` is bounded in norm by the sum of the norms of the
dyadic pieces `(a + v·2^(t-d), a + v·2^(t-d) + 2^(t-d)]` over `d ≤ t` and `v < 2^(d+1)`. -/
theorem dyadic_interval_decomposition (f : ℤ → ℂ) (t : ℕ) (a : ℤ) (k : ℕ) (hk : k ≤ 2 ^ t) :
    ‖∑ m ∈ Finset.Ioc a (a + k), f m‖ ≤
      ∑ d ∈ Finset.range (t + 1), ∑ v ∈ Finset.range (2 ^ (d + 1)),
        ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - d))
            (a + v * (2 : ℤ) ^ (t - d) + (2 : ℤ) ^ (t - d)), f m‖ := by
  -- A single dyadic piece of length `1` is a singleton, so its sum is a single value.
  have key : ∀ x : ℤ, ∑ m ∈ Finset.Ioc x (x + 1), f m = f (x + 1) := by
    intro x
    have h : Finset.Ioc x (x + 1) = {x + 1} := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro rfl; omega
    rw [h, Finset.sum_singleton]
  -- The interval `(a, a+k]` sits inside the full dyadic interval `(a, a + 2^(t+1)]`.
  have hsub : Finset.Ioc a (a + k) ⊆ Finset.Ioc a (a + (2 : ℤ) ^ (t + 1)) := by
    intro x hx
    rw [Finset.mem_Ioc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨h1, ?_⟩
    have hle : (k : ℤ) ≤ (2 : ℤ) ^ (t + 1) := by
      have h₁ : k ≤ 2 ^ (t + 1) :=
        le_trans hk (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ t))
      have h₂ : (k : ℤ) ≤ ((2 : ℕ) ^ (t + 1) : ℤ) := Nat.cast_le.mpr h₁
      simpa using h₂
    linarith [h2]
  -- Reindex the sum over `(a, a + 2^(t+1)]` as a sum over `range (2^(t+1))`.
  have hreindex :
      (∑ m ∈ Finset.Ioc a (a + (2 : ℤ) ^ (t + 1)), ‖f m‖)
        = ∑ i ∈ Finset.range (2 ^ (t + 1)), ‖f (a + 1 + i)‖ := by
    rw [Int.Ioc_eq_finset_map]
    have htoNat : ((a + (2 : ℤ) ^ (t + 1)) - a).toNat = 2 ^ (t + 1) := by
      have : (a + (2 : ℤ) ^ (t + 1)) - a = ((2 ^ (t + 1) : ℕ) : ℤ) := by
        rw [add_sub_cancel_left]; push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [htoNat, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  -- Each finest (`d = t`) dyadic piece is a singleton contributing `‖f (a·+1+v)‖`.
  have hv : ∀ v : ℕ,
      ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - t))
          (a + v * (2 : ℤ) ^ (t - t) + (2 : ℤ) ^ (t - t)), f m‖ = ‖f (a + 1 + v)‖ := by
    intro v
    rw [Nat.sub_self, pow_zero, mul_one]
    rw [key (a + ↑v)]
    congr 1
    ring_nf
  -- The `d = t` block of the right-hand side already dominates the reindexed sum.
  have hFt :
      (fun d => ∑ v ∈ Finset.range (2 ^ (d + 1)),
          ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - d))
              (a + v * (2 : ℤ) ^ (t - d) + (2 : ℤ) ^ (t - d)), f m‖) t
        ≤ ∑ d ∈ Finset.range (t + 1),
            (fun d => ∑ v ∈ Finset.range (2 ^ (d + 1)),
              ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - d))
                  (a + v * (2 : ℤ) ^ (t - d) + (2 : ℤ) ^ (t - d)), f m‖) d :=
    Finset.single_le_sum
      (f := fun d => ∑ v ∈ Finset.range (2 ^ (d + 1)),
        ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - d))
            (a + v * (2 : ℤ) ^ (t - d) + (2 : ℤ) ^ (t - d)), f m‖)
      (fun b _ => Finset.sum_nonneg (fun v _ => norm_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self t))
  calc
    ‖∑ m ∈ Finset.Ioc a (a + k), f m‖
        ≤ ∑ m ∈ Finset.Ioc a (a + k), ‖f m‖ := norm_sum_le _ _
    _   ≤ ∑ m ∈ Finset.Ioc a (a + (2 : ℤ) ^ (t + 1)), ‖f m‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => norm_nonneg _)
    _   = ∑ i ∈ Finset.range (2 ^ (t + 1)), ‖f (a + 1 + i)‖ := hreindex
    _   ≤ ∑ d ∈ Finset.range (t + 1), ∑ v ∈ Finset.range (2 ^ (d + 1)),
            ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - d))
                (a + v * (2 : ℤ) ^ (t - d) + (2 : ℤ) ^ (t - d)), f m‖ := by
          rw [show (∑ i ∈ Finset.range (2 ^ (t + 1)), ‖f (a + 1 + i)‖)
                = ∑ v ∈ Finset.range (2 ^ (t + 1)),
                    ‖∑ m ∈ Finset.Ioc (a + v * (2 : ℤ) ^ (t - t))
                        (a + v * (2 : ℤ) ^ (t - t) + (2 : ℤ) ^ (t - t)), f m‖ from by
              apply Finset.sum_congr rfl
              intro w _
              rw [hv w]]
          exact hFt

end Commons.NumberTheory.CharacterSum