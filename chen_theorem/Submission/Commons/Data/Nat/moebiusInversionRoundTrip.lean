import Mathlib.Data.Real.Basic
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat

namespace Commons.Data.Nat

/-- The divisor sum of the Möbius function over `ℝ`: `∑_{e | m} μ e` equals `1`
if `m = 1` and `0` otherwise. -/
private lemma sum_moebius_real (m : ℕ) :
    (∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ)) = if m = 1 then (1 : ℝ) else 0 := by
  have hz := Commons.NumberTheory.Moebius.sum_moebius_divisors m
  rw [← Int.cast_sum (R := ℝ) (s := m.divisors) (f := fun e => ArithmeticFunction.moebius e)]
  rw [hz]
  by_cases h : m = 1 <;> simp [h]

/-- Same divisor sum of Möbius, but evaluated at `m / e`: `∑_{e | m} μ (m / e)` is `1`
if `m = 1` and `0` otherwise. -/
private lemma sum_moebius_div_real (m : ℕ) :
    (∑ e ∈ m.divisors, (ArithmeticFunction.moebius (m / e) : ℝ)) = if m = 1 then (1 : ℝ) else 0 := by
  calc
    (∑ e ∈ m.divisors, (ArithmeticFunction.moebius (m / e) : ℝ))
        = m.divisors.sum (fun e => (ArithmeticFunction.moebius e : ℝ)) := by
          exact Nat.sum_div_divisors m (fun e : ℕ => (ArithmeticFunction.moebius e : ℝ))
    _ = ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) := rfl
    _ = if m = 1 then (1 : ℝ) else 0 := sum_moebius_real m

/-- Coefficient collapse on the divisor lattice of `P`: for divisors `l`, `l'` of `P`,
`∑_{d : l | d | l'} μ (l' / d)` is `1` when `l' = l` and `0` otherwise. -/
private lemma coeff_moebius {P l l' : ℕ} (hP0 : P ≠ 0) (hlP : l ∣ P) (hl'P : l' ∣ P) :
    (∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l'),
      (ArithmeticFunction.moebius (l' / d) : ℝ)) = if l' = l then (1 : ℝ) else 0 := by
  classical
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hlP (Nat.pos_of_ne_zero hP0)
  have hl0 : l ≠ 0 := ne_of_gt hlpos
  have hl'pos : 0 < l' := Nat.pos_of_dvd_of_pos hl'P (Nat.pos_of_ne_zero hP0)
  have hl'0 : l' ≠ 0 := ne_of_gt hl'pos
  by_cases hdiv : l ∣ l'
  · -- case l | l'
    calc
      (∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l'), (ArithmeticFunction.moebius (l' / d) : ℝ))
          = ∑ e ∈ (l' / l).divisors, (ArithmeticFunction.moebius ((l' / l) / e) : ℝ) := by
            refine Finset.sum_bij (fun d _ => d / l) ?hi ?hinj ?hsurj ?hterm
            · intro d hd
              rcases (Finset.mem_filter.mp hd) with ⟨hdP, ⟨hld, hdl'⟩⟩
              rw [Nat.mem_divisors]
              constructor
              · exact Nat.div_dvd_div (k := l) (m := d) (n := l') hld hdl'
              · intro hq
                exact hl'0 (by
                  calc
                    l' = l * (l' / l) := (Nat.mul_div_cancel' hdiv).symm
                    _ = l * 0 := by rw [hq]
                    _ = 0 := by simp)
            · intro a₁ ha₁ a₂ ha₂ h
              rcases (Finset.mem_filter.mp ha₁) with ⟨_, ⟨hld₁, _⟩⟩
              rcases (Finset.mem_filter.mp ha₂) with ⟨_, ⟨hld₂, _⟩⟩
              calc
                a₁ = (a₁ / l) * l := (Nat.div_mul_cancel hld₁).symm
                _ = (a₂ / l) * l := by rw [h]
                _ = a₂ := Nat.div_mul_cancel hld₂
            · intro b hb
              refine ⟨l * b, ?_, ?_⟩
              · -- l * b ∈ P.divisors.filter (fun d => l | d ∧ d | l')
                have hb' : b ∣ l' / l := Nat.dvd_of_mem_divisors hb
                have hdl' : l * b ∣ l' := by
                  rw [← Nat.mul_div_cancel' hdiv]
                  exact Nat.mul_dvd_mul_left l hb'
                rw [Finset.mem_filter, Nat.mem_divisors]
                exact ⟨⟨dvd_trans hdl' hl'P, hP0⟩, ⟨dvd_mul_right l b, hdl'⟩⟩
              · -- (l * b) / l = b
                exact Nat.mul_div_right b hlpos
            · intro d hd
              rcases (Finset.mem_filter.mp hd) with ⟨_, ⟨hld, _⟩⟩
              have hmain : l' / d = (l' / l) / (d / l) := by
                calc
                  l' / d = (l * (l' / l)) / (l * (d / l)) := by
                    rw [Nat.mul_div_cancel' hdiv, Nat.mul_div_cancel' hld]
                  _ = (l' / l) / (d / l) := by
                    rw [mul_comm l (l' / l), mul_comm l (d / l)]
                    exact Nat.mul_div_mul_right (l' / l) (d / l) hlpos
              rw [hmain]
      _ = (if l' / l = 1 then (1 : ℝ) else 0) := sum_moebius_div_real (l' / l)
      _ = if l' = l then (1 : ℝ) else 0 := by
          by_cases hq : l' / l = 1
          · have hll' : l' = l := by
              calc
                l' = l * (l' / l) := (Nat.mul_div_cancel' hdiv).symm
                _ = l * 1 := by rw [hq]
                _ = l := by simp
            have hdiv1 : l / l = 1 := Nat.div_self hlpos
            simp [hll', hdiv1]
          · have hne : l' ≠ l := by
              intro hll'
              exact hq (by
                calc
                  l' / l = l / l := by rw [hll']
                  _ = 1 := Nat.div_self hlpos)
            simp [hq, hne]
  · -- case ¬ l | l'
    have hA : P.divisors.filter (fun d => l ∣ d ∧ d ∣ l') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd h
      exact hdiv (dvd_trans h.1 h.2)
    have hne : l' ≠ l := by
      intro hll'
      rw [hll'] at hdiv
      exact hdiv dvd_rfl
    rw [hA]
    simp [hne]

theorem moebiusInversionRoundTrip (P : ℕ) (hP : Squarefree P) (y : ℕ → ℝ) (l : ℕ)
    (hlP : l ∣ P) :
    (∑ d ∈ divisors P, if l ∣ d then
        (∑ l' ∈ divisors P, if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * y l' else 0)
      else 0) = y l := by
  classical
  have hP0 : P ≠ 0 := hP.ne_zero
  calc
    (∑ d ∈ divisors P, if l ∣ d then
        (∑ l' ∈ divisors P, if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * y l' else 0)
      else 0)
        = ∑ d ∈ P.divisors, ∑ l' ∈ P.divisors,
            if l ∣ d then (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * y l' else 0)
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          by_cases hld : l ∣ d <;> simp [hld]
    _ = ∑ l' ∈ P.divisors, ∑ d ∈ P.divisors,
            if l ∣ d then (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * y l' else 0)
            else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ l' ∈ P.divisors,
            ∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l'),
              (ArithmeticFunction.moebius (l' / d) : ℝ) * y l' := by
          refine Finset.sum_congr rfl ?_
          intro l' hl'
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro d hd
          by_cases h₁ : l ∣ d <;> by_cases h₂ : d ∣ l' <;> simp [h₁, h₂]
    _ = ∑ l' ∈ P.divisors,
            y l' * (∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l'),
              (ArithmeticFunction.moebius (l' / d) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro l' hl'
          rw [← Finset.sum_mul]
          exact mul_comm (∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l'),
            (ArithmeticFunction.moebius (l' / d) : ℝ)) (y l')
    _ = ∑ l' ∈ P.divisors, y l' * (if l' = l then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro l' hl'
          rw [coeff_moebius hP0 hlP (Nat.dvd_of_mem_divisors hl')]
    _ = ∑ l' ∈ P.divisors, (if l' = l then y l' else 0) := by
          refine Finset.sum_congr rfl ?_
          intro l' hl'
          by_cases h : l' = l <;> simp [h]
    _ = y l := by
          rw [Finset.sum_ite_eq']
          simp [Nat.mem_divisors.mpr ⟨hlP, hP0⟩]

end Commons.Data.Nat