import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

namespace Work.Peluse.Fourier

open Finset

/-- `ee` of a natural multiple: `ee (n * θ) = (ee θ)^n`. -/
private lemma ee_nat_mul (θ : ℝ) (n : ℕ) : ee ((n : ℝ) * θ) = ee θ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ := by push_cast; ring
    rw [h, ee_add, ih, pow_succ]

theorem dftOrthogonality (L : ℕ) (hL : 1 ≤ L) (m : ℤ) :
    ∑ k ∈ Finset.range L, Work.Peluse.ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) =
      if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := Nat.lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast this
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  set z : ℂ := ee ((m : ℝ) / (L : ℝ)) with hz
  -- the summand is the `k`-th power of the root of unity `z`
  have hpow : ∀ k : ℕ, ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) = z ^ k := by
    intro k
    rw [mul_div_assoc, ee_nat_mul, hz]
  -- `z` is an `L`-th root of unity
  have hzL : z ^ L = 1 := by
    rw [hz]
    have h : ee ((L : ℝ) * ((m : ℝ) / (L : ℝ))) = ee ((m : ℝ) / (L : ℝ)) ^ L :=
      ee_nat_mul _ L
    rw [← h]
    have hm : (L : ℝ) * ((m : ℝ) / (L : ℝ)) = (m : ℝ) := by field_simp
    rw [hm, ee_int]
  -- `z = 1` exactly when `L ∣ m`
  have hsplit : ((L : ℤ) ∣ m) ↔ z = 1 := by
    constructor
    · rintro ⟨n, hn⟩
      have hmn : (m : ℝ) / (L : ℝ) = (n : ℝ) := by
        rw [hn]; push_cast; field_simp
      rw [hz, hmn, ee_int]
    · intro hz1
      have h1 : ee ((m : ℝ) / (L : ℝ)) = 1 := by rw [← hz]; exact hz1
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).mp h1
      have h2 : (m : ℝ) = (n : ℝ) * (L : ℝ) := by
        rw [div_eq_iff hLne] at hn; exact hn
      have h3 : m = n * L := by exact_mod_cast h2
      exact ⟨n, by rw [h3]; ring⟩
  have hsum : ∑ k ∈ Finset.range L, ee ((k : ℝ) * (m : ℝ) / (L : ℝ))
      = ∑ k ∈ Finset.range L, z ^ k := Finset.sum_congr rfl (fun k _ => hpow k)
  rw [hsum]
  by_cases hz1 : z = 1
  · rw [if_pos (hsplit.mpr hz1), hz1]
    simp
  · rw [if_neg (fun h => hz1 (hsplit.mp h))]
    have h := geom_sum_mul z L
    rw [hzL, sub_self] at h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact h0
    · exact absurd h1 (sub_ne_zero.mpr hz1)

end Work.Peluse.Fourier
