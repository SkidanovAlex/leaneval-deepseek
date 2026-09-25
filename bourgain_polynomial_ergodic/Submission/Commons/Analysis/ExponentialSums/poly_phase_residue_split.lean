import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- Arithmetic form of the division-with-remainder index set: for `0 < q` and `r < q`, the
numbers `p` with `p * q + r < N` are exactly those below `(N + q - 1 - r) / q`. -/
lemma lt_div_iff_mul_add_lt (N q r p : ℕ) (hq : 0 < q) (hr : r < q) :
    p < (N + q - 1 - r) / q ↔ p * q + r < N := by
  rcases lt_or_ge r N with hrN | hNr
  · have hM : N + q - 1 - r = (N - 1 - r) + q := by omega
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
    rw [hM, Nat.add_comm (N - 1 - r) q, Nat.add_div_of_dvd_right (dvd_refl q), Nat.div_self hq,
      Nat.add_comm 1 ((N - 1 - r) / q), Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hq,
      Nat.le_sub_iff_add_le (show r ≤ N - 1 by omega), Nat.le_sub_one_iff_lt hN]
  · have hM : N + q - 1 - r < q := by omega
    rw [Nat.div_eq_of_lt hM]
    exact ⟨fun h => absurd h (Nat.not_lt_zero p), fun h => by omega⟩

/-- Splitting a sum over `range N` into residue classes modulo `q`: the sum of `g` over
`n < N` equals the sum over residues `r < q` of the sum over `p` with `p * q + r < N`. -/
theorem sum_range_residue_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N q : ℕ)
    (hq : 0 < q) :
    (∑ n ∈ Finset.range N, g n)
      = ∑ r ∈ Finset.range q,
          ∑ p ∈ Finset.range ((N + q - 1 - r) / q), g (p * q + r) := by
  classical
  have hset : Finset.range N
      = (Finset.range q).biUnion
          (fun r => (Finset.range ((N + q - 1 - r) / q)).image (fun p => p * q + r)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hn
      refine ⟨n % q, Nat.mod_lt n hq, n / q, ?_, ?_⟩
      · rw [lt_div_iff_mul_add_lt N q (n % q) (n / q) hq (Nat.mod_lt n hq)]
        rw [Nat.mul_comm (n / q) q, Nat.div_add_mod]
        exact hn
      · rw [Nat.mul_comm (n / q) q, Nat.div_add_mod]
    · rintro ⟨r, hr, p, hp, rfl⟩
      exact (lt_div_iff_mul_add_lt N q r p hq hr).1 hp
  have hdisj : (Finset.range q : Set ℕ).PairwiseDisjoint
      (fun r => (Finset.range ((N + q - 1 - r) / q)).image (fun p => p * q + r)) := by
    intro r hr s hs hrs
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxr hxs
    rw [Finset.mem_image] at hxr hxs
    obtain ⟨p₁, -, hp₁⟩ := hxr
    obtain ⟨p₂, -, hp₂⟩ := hxs
    have hr' : r < q := by simpa using hr
    have hs' : s < q := by simpa using hs
    have h₁ : (p₁ * q + r) % q = r := by
      rw [Nat.add_comm (p₁ * q) r, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
    have h₂ : (p₂ * q + s) % q = s := by
      rw [Nat.add_comm (p₂ * q) s, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs']
    have hx₁ : x % q = r := by rw [← hp₁]; exact h₁
    have hx₂ : x % q = s := by rw [← hp₂]; exact h₂
    exact hrs (hx₁.symm.trans hx₂)
  rw [hset, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_image (f := g) (s := Finset.range ((N + q - 1 - r) / q))
    (g := fun p => p * q + r) (fun p₁ _ p₂ _ heq => Nat.mul_right_cancel hq (Nat.add_right_cancel heq))]

/-- Splitting a polynomial exponential sum into residue classes modulo `q`: for
`P : ℤ[X]`, `q ≥ 1`, the sum over `n < N` of `e(α P(n))` equals the sum over residues
`r < q` of the sum over `p` with `p q + r < N` of `e(α P (p q + r))`.  This is the first
step of the circle-method analysis of the polynomial Weyl sums. -/
theorem poly_phase_residue_split (P : Polynomial ℤ) (N q : ℕ) (hq : 0 < q) (α : ℝ) :
    (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (α * ((P.eval (n : ℤ) : ℤ) : ℂ))))
      = ∑ r ∈ Finset.range q,
          ∑ p ∈ Finset.range ((N + q - 1 - r) / q),
            Complex.exp (2 * Real.pi * Complex.I *
              (α * ((P.eval ((p * q + r : ℕ) : ℤ) : ℤ) : ℂ))) := by
  exact sum_range_residue_split
    (fun n : ℕ => Complex.exp (2 * Real.pi * Complex.I * (α * ((P.eval (n : ℤ) : ℤ) : ℂ))))
    N q hq

end Commons.Analysis.ExponentialSums