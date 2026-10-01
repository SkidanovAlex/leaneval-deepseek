import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.Moebius

/-- Exchange the order of summation between a sum over `d ∈ Icc (R+1) N` of a sum over the
divisors `b | d` of `f b (d/b)`, and a double sum over pairs `(b, n) ∈ [1,N]²` with
`R < b*n ≤ N` of `f b n`.  This is the change of variables `d = b * n`. -/
theorem sum_Icc_divisors_bijection (R N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc (R+1) N, ∑ b ∈ d.divisors, f b (d/b))
      = ∑ b ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if R < b*n ∧ b*n ≤ N then f b n else 0) := by
  -- Rewrite the left-hand side as a sum over the sigma-`Finset` of pairs `⟨d, b⟩` with `b ∣ d`.
  have hL : (∑ d ∈ Finset.Icc (R+1) N, ∑ b ∈ d.divisors, f b (d / b))
      = ∑ x ∈ (Finset.Icc (R + 1) N).sigma (fun d => d.divisors), f x.snd (x.fst / x.snd) := by
    rw [Finset.sum_sigma']
  -- Rewrite the right-hand side as a sum over pairs `(b, n)`, with the condition as a filter.
  have hR : (∑ b ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if R < b * n ∧ b * n ≤ N then f b n else 0))
      = ∑ y ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun y => R < y.1 * y.2 ∧ y.1 * y.2 ≤ N), f y.1 y.2 := by
    rw [Finset.sum_filter]
    rw [Finset.sum_product' (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
          (f := fun u v => if R < u * v ∧ u * v ≤ N then f u v else 0)]
  -- The change of variables `⟨d, b⟩ ↦ (b, d / b)` (inverse `(b, n) ↦ ⟨b * n, b⟩`).
  have hmain : (∑ x ∈ (Finset.Icc (R + 1) N).sigma (fun d => d.divisors), f x.snd (x.fst / x.snd))
      = ∑ y ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun y => R < y.1 * y.2 ∧ y.1 * y.2 ≤ N), f y.1 y.2 := by
    apply Finset.sum_bij'
      (i := fun x _ => (x.snd, x.fst / x.snd))
      (j := fun y _ => ⟨y.1 * y.2, y.1⟩)
    · -- `⟨d, b⟩ ↦ (b, d/b) ↦ ⟨b * (d/b), b⟩ = ⟨d, b⟩`.
      intro x hx
      obtain ⟨d, b⟩ := x
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hR1, hN⟩, hdvd, hdne⟩ := hx
      show (⟨b * (d / b), b⟩ : Sigma fun _ : ℕ => ℕ) = ⟨d, b⟩
      rw [Nat.mul_div_cancel' hdvd]
    · -- `(b, n) ↦ ⟨b * n, b⟩ ↦ (b, (b*n)/b) = (b, n)`.
      intro y hy
      obtain ⟨b, n⟩ := y
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy
      obtain ⟨⟨⟨h1b, _⟩, _⟩, _, _⟩ := hy
      show (b, b * n / b) = (b, n)
      rw [Nat.mul_div_right n (by omega : 0 < b)]
    · -- The summands agree under the change of variables.
      intro x hx
      rfl
    · -- `(b, d/b)` lies in the target set when `R + 1 ≤ d ≤ N` and `b ∣ d`.
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_Icc,
        Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨hR1, hN⟩, hdvd, hdne⟩ := hx
      have hbpos : 0 < x.snd := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hble : x.snd ≤ x.fst := Nat.le_of_dvd (by omega) hdvd
      have hbN : x.snd ≤ N := le_trans hble hN
      have hdivle : x.fst / x.snd ≤ N := le_trans (Nat.div_le_self x.fst x.snd) hN
      have hdivpos : 0 < x.fst / x.snd := Nat.div_pos hble hbpos
      have hmul : x.snd * (x.fst / x.snd) = x.fst := Nat.mul_div_cancel' hdvd
      refine ⟨⟨⟨by omega, hbN⟩, ⟨by omega, hdivle⟩⟩, ?_, ?_⟩
      · rw [hmul]; omega
      · rw [hmul]; exact hN
    · -- `⟨b*n, b⟩` lies in the source set when `R < b*n ≤ N`, `1 ≤ b, n ≤ N`.
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_Icc,
        Nat.mem_divisors] at hy ⊢
      obtain ⟨⟨⟨h1y, hNy⟩, ⟨h1n, hNn⟩⟩, hRlt, hNle⟩ := hy
      refine ⟨⟨by omega, hNle⟩, dvd_mul_right y.1 y.2, ?_⟩
      exact Nat.mul_ne_zero (by omega) (by omega)
  exact hL.trans (hmain.trans hR.symm)

end Commons.NumberTheory.Moebius