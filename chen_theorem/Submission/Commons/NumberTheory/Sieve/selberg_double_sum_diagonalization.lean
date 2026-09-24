import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient

namespace Commons.NumberTheory.Sieve

open Finset

/-- For positive `d`, `e`, the lcm can be written as `d * e / gcd d e` over `ℝ`. -/
lemma lcm_gcd_real {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    ((Nat.lcm d e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) / (Nat.gcd d e : ℝ) := by
  have hgcd : (Nat.gcd d e : ℝ) ≠ 0 := by
    have : Nat.gcd d e ≠ 0 := fun h => hd (Nat.gcd_eq_zero_iff.mp h).1
    exact_mod_cast this
  rw [eq_div_iff hgcd]
  rw [mul_comm (Nat.lcm d e : ℝ) (Nat.gcd d e : ℝ)]
  exact_mod_cast Nat.gcd_mul_lcm d e

/-- Pointwise reformulation of `1 / lcm d e` in terms of `1/d`, `1/e` and `gcd d e`. -/
lemma lcm_term (lam : ℕ → ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    lam d * lam e / (Nat.lcm d e : ℝ)
      = lam d / (d : ℝ) * (lam e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
  have hgcd : (Nat.gcd d e : ℝ) ≠ 0 := by
    have : Nat.gcd d e ≠ 0 := fun h => hd (Nat.gcd_eq_zero_iff.mp h).1
    exact_mod_cast this
  rw [lcm_gcd_real hd he]
  field_simp

/-- The classical identity `gcd d e = ∑_{l ∣ d, l ∣ e} φ(l)`, phrased with a finite set `T`
that is closed under divisors and contains only positive elements. -/
lemma totient_sum_eq_gcd {T : Finset ℕ} (hTpos : ∀ d ∈ T, 0 < d)
    (hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T)
    {d e : ℕ} (hd : d ∈ T) (he : e ∈ T) :
    (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) = (Nat.gcd d e : ℝ) := by
  have hgpos : 0 < Nat.gcd d e := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d e) (hTpos d hd)
  have hgne : Nat.gcd d e ≠ 0 := hgpos.ne'
  have hset : T.filter (fun l => l ∣ d ∧ l ∣ e) = (Nat.gcd d e).divisors := by
    ext l
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hlT, hld, hle⟩
      exact ⟨⟨hld, hle⟩, hgne⟩
    · rintro ⟨⟨hld, hle⟩, _⟩
      exact ⟨hTclosed hld hd, hld, hle⟩
  calc (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0)
      = ∑ l ∈ T.filter (fun l => l ∣ d ∧ l ∣ e), (Nat.totient l : ℝ) := by rw [sum_filter]
    _ = ∑ l ∈ (Nat.gcd d e).divisors, (Nat.totient l : ℝ) := by rw [hset]
    _ = (Nat.gcd d e : ℝ) := by rw [← Nat.cast_sum, Nat.sum_totient]

/-- Factoring a double sum of an indicator into a product of two (filtered) one-variable sums. -/
lemma sum_sum_ite (T : Finset ℕ) (a : ℕ → ℝ) (l : ℕ) (c : ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, (if (l ∣ d ∧ l ∣ e) then a d * a e * c else 0))
      = c * (∑ d ∈ T.filter (fun d => l ∣ d), a d) * (∑ e ∈ T.filter (fun e => l ∣ e), a e) := by
  have point : ∀ d e : ℕ,
      (if (l ∣ d ∧ l ∣ e) then a d * a e * c else 0)
        = c * (if l ∣ d then a d else 0) * (if l ∣ e then a e else 0) := by
    intro d e
    by_cases hd : l ∣ d <;> by_cases he : l ∣ e <;> simp [hd, he] <;> ring
  calc (∑ d ∈ T, ∑ e ∈ T, (if (l ∣ d ∧ l ∣ e) then a d * a e * c else 0))
      = ∑ d ∈ T, ∑ e ∈ T, c * (if l ∣ d then a d else 0) * (if l ∣ e then a e else 0) := by
        apply Finset.sum_congr rfl; intro d _
        apply Finset.sum_congr rfl; intro e _
        rw [point]
    _ = (∑ d ∈ T, c * (if l ∣ d then a d else 0)) * (∑ e ∈ T, if l ∣ e then a e else 0) := by
        rw [sum_mul_sum]
    _ = c * (∑ d ∈ T, if l ∣ d then a d else 0) * (∑ e ∈ T, if l ∣ e then a e else 0) := by
        rw [← mul_sum]
    _ = c * (∑ d ∈ T.filter (fun d => l ∣ d), a d) * (∑ e ∈ T.filter (fun e => l ∣ e), a e) := by
        rw [← sum_filter]

/-- Rotation of a triple sum over the same finite set. -/
lemma triple_sum_swap (T : Finset ℕ) (G : ℕ → ℕ → ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, G d e l) = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, G d e l := by
  calc ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, G d e l
      = ∑ d ∈ T, ∑ l ∈ T, ∑ e ∈ T, G d e l := by
          apply Finset.sum_congr rfl; intro d _
          exact Finset.sum_comm
    _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, G d e l := by
          exact Finset.sum_comm

/-- Diagonalization of the quadratic form `∑_{d,e} a_d a_e gcd(d,e)` into the sum
`∑_l φ(l) (∑_{l ∣ d} a_d)^2`, for a finite set `T` closed under divisors consisting of
positive integers. -/
lemma sum_gcd_eq_sum_totient_sq (T : Finset ℕ) (hTpos : ∀ d ∈ T, 0 < d)
    (hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T) (a : ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, a d * a e * (Nat.gcd d e : ℝ))
      = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
  have step1 : (∑ d ∈ T, ∑ e ∈ T, a d * a e * (Nat.gcd d e : ℝ))
      = ∑ d ∈ T, ∑ e ∈ T, a d * a e *
          (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [totient_sum_eq_gcd hTpos hTclosed hd he]
  rw [step1]
  have step2 : (∑ d ∈ T, ∑ e ∈ T, a d * a e *
        (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0))
      = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
    calc (∑ d ∈ T, ∑ e ∈ T, a d * a e *
            (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0))
        = ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, a d * a e *
            (if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          rw [Finset.mul_sum]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, a d * a e *
            (if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
          rw [triple_sum_swap]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
            (if (l ∣ d ∧ l ∣ e) then a d * a e * (Nat.totient l : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          rw [mul_ite, mul_zero]
      _ = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
          apply Finset.sum_congr rfl; intro l _
          rw [sum_sum_ite, sq]
          ring
  rw [step2]

/-- Selberg double-sum diagonalization: the quadratic form `∑_{d,e ≤ D} λ_d λ_e / lcm(d,e)`
over the divisors of `M` diagonalizes into `∑_{l ≤ D} φ(l) (∑_{l ∣ d} λ_d / d)^2`. -/
theorem selberg_double_sum_diagonalization (M D : ℕ) (hM : 1 ≤ M) (lam : ℕ → ℝ) :
    (∑ d ∈ M.divisors.filter (fun d : ℕ => d ≤ D),
       ∑ e ∈ M.divisors.filter (fun e : ℕ => e ≤ D),
         lam d * lam e / ((Nat.lcm d e : ℕ) : ℝ))
    = ∑ l ∈ M.divisors.filter (fun l : ℕ => l ≤ D),
        (Nat.totient l : ℝ) *
          (∑ d ∈ (M.divisors.filter (fun d : ℕ => d ≤ D)).filter (fun d : ℕ => l ∣ d),
             lam d / (d : ℝ)) ^ 2 := by
  have hMpos : 0 < M := hM
  have hTpos : ∀ d ∈ M.divisors.filter (fun d : ℕ => d ≤ D), 0 < d := by
    intro d hd
    exact Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hMpos
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ M.divisors.filter (fun d : ℕ => d ≤ D) →
      l ∈ M.divisors.filter (fun d : ℕ => d ≤ D) := by
    intro l d hld hd
    have hdM : d ∣ M := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdD : d ≤ D := (Finset.mem_filter.mp hd).2
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hld.trans hdM, hMpos.ne'⟩,
      le_trans (Nat.le_of_dvd (hTpos d hd) hld) hdD⟩
  have key : (∑ d ∈ M.divisors.filter (fun d : ℕ => d ≤ D),
        ∑ e ∈ M.divisors.filter (fun e : ℕ => e ≤ D),
          lam d * lam e / ((Nat.lcm d e : ℕ) : ℝ))
      = ∑ d ∈ M.divisors.filter (fun d : ℕ => d ≤ D),
        ∑ e ∈ M.divisors.filter (fun e : ℕ => e ≤ D),
          lam d / (d : ℝ) * (lam e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    exact lcm_term lam (hTpos d hd).ne' (hTpos e he).ne'
  rw [key]
  exact sum_gcd_eq_sum_totient_sq _ hTpos hTclosed (fun d => lam d / (d : ℝ))

end Commons.NumberTheory.Sieve