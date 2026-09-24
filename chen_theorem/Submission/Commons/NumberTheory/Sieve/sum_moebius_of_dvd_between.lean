import Mathlib.Data.Real.Basic
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

namespace Commons.NumberTheory.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-- Reindexing: the divisors of `e` that are multiples of `l ∣ e` correspond to the
divisors of `e / l` via `k ↦ l * k`. -/
private lemma sum_divisors_filter_dvd_eq {M : Type*} [AddCommMonoid M]
    (l e : ℕ) (hle : l ∣ e) (hl : l ≠ 0) (f : ℕ → M) :
    (∑ d ∈ e.divisors.filter (fun d => l ∣ d), f d)
      = ∑ k ∈ (e / l).divisors, f (l * k) := by
  classical
  refine Finset.sum_bij (s := e.divisors.filter (fun d => l ∣ d)) (t := (e / l).divisors)
    (f := f) (g := fun k => f (l * k)) (fun d _ => d / l) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, he0⟩, hld⟩ := hd
    have hd_eq : d = l * (d / l) := (Nat.mul_div_cancel' hld).symm
    have he_eq : e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
    rw [Nat.mem_divisors]
    refine ⟨?_, ?_⟩
    · rw [hd_eq, he_eq] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hl)).mp hdvd
    · intro h
      exact he0 (by rw [he_eq, h, mul_zero])
  · intro d1 h1 d2 h2 heq
    rw [Finset.mem_filter] at h1 h2
    rw [← Nat.mul_div_cancel' h1.2, ← Nat.mul_div_cancel' h2.2, heq]
  · intro b hb
    rw [Nat.mem_divisors] at hb
    obtain ⟨hbvd, he0⟩ := hb
    refine ⟨l * b, ?_, ?_⟩
    · rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right l b⟩
      · rw [← Nat.mul_div_cancel' hle]
        exact Nat.mul_dvd_mul_left l hbvd
      · rw [← Nat.mul_div_cancel' hle]
        exact Nat.mul_ne_zero hl he0
    · rw [mul_comm l b]
      exact Nat.mul_div_left b (Nat.pos_of_ne_zero hl)
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact congrArg f (Nat.mul_div_cancel' hd.2).symm

/-- The Möbius divisor sum, as a real number. -/
private lemma sum_moebius_divisors_real (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))
      = if n = 1 then (1 : ℝ) else 0 := by
  have hZ := Commons.NumberTheory.Moebius.sum_moebius_divisors n
  have hcast : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    push_cast
    rfl
  rw [← hcast, hZ]
  by_cases h : n = 1 <;> simp [h]

theorem sum_moebius_of_dvd_between (l e : ℕ) (he : Squarefree e) (hle : l ∣ e) :
    (∑ d ∈ e.divisors.filter (fun d : ℕ => l ∣ d), (ArithmeticFunction.moebius d : ℝ))
      = if l = e then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  have hl : l ≠ 0 := by
    rintro rfl
    exact he.ne_zero (eq_zero_of_zero_dvd hle)
  have hiff : e / l = 1 ↔ l = e := by
    constructor
    · intro h
      have h' : e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
      rw [h, mul_one] at h'
      exact h'.symm
    · intro h
      subst h
      exact Nat.div_self (Nat.pos_of_ne_zero hl)
  rw [sum_divisors_filter_dvd_eq l e hle hl]
  have hterm : ∀ k ∈ (e / l).divisors,
      (ArithmeticFunction.moebius (l * k) : ℝ)
        = (ArithmeticFunction.moebius l : ℝ) * (ArithmeticFunction.moebius k : ℝ) := by
    intro k hk
    have hdvd : l * k ∣ e := by
      rw [← Nat.mul_div_cancel' hle]
      exact Nat.mul_dvd_mul_left l (Nat.mem_divisors.mp hk).1
    have hsq : Squarefree (l * k) := Squarefree.squarefree_of_dvd hdvd he
    have hcop : l.Coprime k := Nat.coprime_of_squarefree_mul hsq
    have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    rw [hμ, Int.cast_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_moebius_divisors_real,
    mul_ite, mul_one, mul_zero]
  by_cases h : e / l = 1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

end Commons.NumberTheory.Sieve