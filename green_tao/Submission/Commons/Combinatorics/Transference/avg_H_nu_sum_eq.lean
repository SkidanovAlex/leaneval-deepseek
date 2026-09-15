import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.BooleanRing

open Finset
open scoped BigOperators

namespace Commons.Combinatorics.Transference

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

lemma exists_true_of_ne_zero {d : ℕ} {ω : Fin d → Bool} (hω : ω ≠ 0) : ∃ i, ω i = true := by
  by_contra hc
  simp only [not_exists, Bool.not_eq_true] at hc
  apply hω
  ext i
  exact hc i

lemma zmod_sum_ite_add {p : ℕ} {d : ℕ} (ω : Fin d → Bool) (u v : Fin d → ZMod p) :
    (∑ i, (if ω i then (u + v) i else 0))
      = (∑ i, (if ω i then u i else 0)) + (∑ i, (if ω i then v i else 0)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by cases ω i <;> simp)

lemma zmod_sum_ite_surj {p : ℕ} {d : ℕ} {ω : Fin d → Bool} (hω : ω ≠ 0) (c : ZMod p) :
    ∃ v : Fin d → ZMod p, (∑ i, (if ω i then v i else 0)) = c := by
  obtain ⟨i0, hi0⟩ := exists_true_of_ne_zero hω
  refine ⟨fun i => if i = i0 then c else 0, ?_⟩
  rw [Finset.sum_eq_single i0]
  · simp [hi0]
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ i0) h

lemma sum_zmod_add_right {p : ℕ} [NeZero p] (F : ZMod p → ℝ) (a : ZMod p) :
    (∑ x : ZMod p, F (x + a)) = ∑ x : ZMod p, F x := by
  simpa using (Equiv.sum_comp (Equiv.addRight a) F)

lemma sum_shift_const {p : ℕ} [Fact p.Prime] {d : ℕ} {ω : Fin d → Bool} (hω : ω ≠ 0)
    (F : ZMod p → ℝ) (x : ZMod p) :
    (∑ v : Fin d → ZMod p, F (x + ∑ i, (if ω i then v i else 0)))
      = (Fintype.card (ZMod p) : ℝ) ^ (d - 1) * ∑ t : ZMod p, F t := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨i0, hi0⟩ := exists_true_of_ne_zero hω
  have hd : 1 ≤ d := by have := i0.isLt; omega
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hPpos : (0:ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    rw [hcard]; exact_mod_cast (Fact.out : p.Prime).pos
  have hPne : (Fintype.card (ZMod p) : ℝ) ≠ 0 := ne_of_gt hPpos
  have hconst : ∀ y : ZMod p,
      (∑ v : Fin d → ZMod p, F (y + ∑ i, (if ω i then v i else 0)))
        = (∑ v : Fin d → ZMod p, F (x + ∑ i, (if ω i then v i else 0))) := by
    intro y
    obtain ⟨v0, hv0⟩ := zmod_sum_ite_surj hω (y - x)
    have h1 : y = x + ∑ i, (if ω i then v0 i else 0) := by rw [hv0]; abel
    rw [h1]
    have h2 : (∑ v : Fin d → ZMod p,
          F (x + (∑ i, (if ω i then v0 i else 0)) + ∑ i, (if ω i then v i else 0)))
        = ∑ v : Fin d → ZMod p, F (x + ∑ i, (if ω i then (v0 + v) i else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [zmod_sum_ite_add ω v0 v, add_assoc]
    rw [h2]
    exact Equiv.sum_comp (Equiv.addLeft v0) (fun w => F (x + ∑ i, (if ω i then w i else 0)))
  have hsumG : (∑ y : ZMod p, ∑ v : Fin d → ZMod p, F (y + ∑ i, (if ω i then v i else 0)))
      = (Fintype.card (ZMod p) : ℝ) *
        (∑ v : Fin d → ZMod p, F (x + ∑ i, (if ω i then v i else 0))) := by
    rw [Finset.sum_congr rfl (fun y _ => hconst y)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hdouble : (∑ y : ZMod p, ∑ v : Fin d → ZMod p, F (y + ∑ i, (if ω i then v i else 0)))
      = (Fintype.card (ZMod p) : ℝ) ^ d * ∑ t : ZMod p, F t := by
    rw [Finset.sum_comm]
    have hinner : ∀ v : Fin d → ZMod p,
        (∑ y : ZMod p, F (y + ∑ i, (if ω i then v i else 0))) = ∑ t, F t :=
      fun v => sum_zmod_add_right F _
    rw [Finset.sum_congr rfl (fun v _ => hinner v)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow]
  refine mul_left_cancel₀ hPne ?_
  rw [← hsumG, hdouble]
  conv_rhs => rw [← mul_assoc, ← pow_succ']
  rw [show (↑(Fintype.card (ZMod p)) : ℝ) ^ ((d-1)+1) = (↑(Fintype.card (ZMod p)) : ℝ) ^ d from by
      congr 1; omega]

lemma inner_xH {p : ℕ} [Fact p.Prime] {d K : ℕ} {ν : ZMod p → ℝ} {ω : Fin d → Bool}
    (hω : ω ≠ 0) (h : Fin d → ZMod p) :
    (∑ x : ZMod p, ∑ H : Fin K → Fin d → ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = (Fintype.card (ZMod p) : ℝ) *
        ((Fintype.card (ZMod p) : ℝ) ^ (d - 1) *
          (∑ y : ZMod p, ∏ ω' : Fin d → Bool,
            ν (y + ∑ i, (if ω' i then h i else 0)))) ^ K := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have e1 : (∑ x : ZMod p, ∑ H : Fin K → Fin d → ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = (∑ x : ZMod p, ∑ H : Fin K → Fin d → ZMod p,
        ∏ j : Fin K, ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))) := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro H _
    rw [Finset.prod_comm]
  rw [e1]
  have e2 : ∀ x : ZMod p,
      (∑ H : Fin K → Fin d → ZMod p,
        ∏ j : Fin K, ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = ∏ j : Fin K, ∑ v : Fin d → ZMod p, ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then v i else 0))) := by
    intro x
    have key := Finset.prod_univ_sum
      (t := fun _ : Fin K => (Finset.univ : Finset (Fin d → ZMod p)))
      (f := fun (j : Fin K) (v : Fin d → ZMod p) => ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then v i else 0))))
    rw [Fintype.piFinset_univ] at key
    exact key.symm
  rw [Finset.sum_congr rfl (fun x _ => e2 x)]
  have e3 : ∀ x : ZMod p,
      (∏ j : Fin K, ∑ v : Fin d → ZMod p, ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then v i else 0))))
      = ((Fintype.card (ZMod p) : ℝ) ^ (d - 1) *
          (∑ y : ZMod p, ∏ ω' : Fin d → Bool,
            ν (y + ∑ i, (if ω' i then h i else 0)))) ^ K := by
    intro x
    have hfac : (∑ v : Fin d → ZMod p, ∏ ω' : Fin d → Bool,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then v i else 0))))
        = (Fintype.card (ZMod p) : ℝ) ^ (d - 1) *
          (∑ y : ZMod p, ∏ ω' : Fin d → Bool, ν (y + ∑ i, (if ω' i then h i else 0))) := by
      have hcongr : ∀ v : Fin d → ZMod p,
          (∏ ω' : Fin d → Bool,
            ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then v i else 0))))
          = (∏ ω' : Fin d → Bool,
            ν ((x + ∑ i, (if ω i then v i else 0)) + ∑ i, (if ω' i then h i else 0))) := by
        intro v
        apply Finset.prod_congr rfl
        intro ω' _
        congr 1
        abel
      rw [Finset.sum_congr rfl (fun v _ => hcongr v)]
      exact sum_shift_const hω
        (fun z => ∏ ω' : Fin d → Bool, ν (z + ∑ i, (if ω' i then h i else 0))) x
    rw [Finset.prod_congr rfl (fun j _ => hfac)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun x _ => e3 x)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma final_arith {P S : ℝ} {d K : ℕ} (hP : P ≠ 0) (hd : 1 ≤ d) :
    P * (P ^ (d - 1) * S) ^ K = P ^ (d * K + 1) * (P⁻¹ * S) ^ K := by
  rw [mul_pow, mul_pow, ← pow_mul, inv_pow]
  have hKd : K ≤ d * K + 1 := by
    have h1 : K ≤ d * K := Nat.le_mul_of_pos_left K (by omega : 0 < d)
    omega
  conv_rhs => rw [← mul_assoc]
  rw [← pow_sub₀ P hP hKd]
  have hexp : d * K + 1 - K = (d - 1) * K + 1 := by
    have hKd' : K ≤ d * K := Nat.le_mul_of_pos_left K (by omega : 0 < d)
    have h1 : (d - 1) * K = d * K - K := by rw [Nat.mul_sub_right_distrib, one_mul]
    rw [h1]
    omega
  rw [hexp]
  conv_lhs => rw [← mul_assoc, ← pow_succ']

theorem avg_H_nu_sum_eq {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (ω : Fin d → Bool) (hω : ω ≠ 0) :
    (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = (Fintype.card (ZMod p) : ℝ) ^ (d * K + 1) *
        ∑ h : Fin d → ZMod p,
          ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, ∏ ω' : Fin d → Bool,
            ν (y + ∑ i, (if ω' i then h i else 0))) ^ K := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcardpos : 0 < Fintype.card (ZMod p) := by
    rw [ZMod.card p]; exact (Fact.out : p.Prime).pos
  have hPne : (Fintype.card (ZMod p) : ℝ) ≠ 0 := by exact_mod_cast hcardpos.ne'
  have hperm : (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = ∑ h : Fin d → ZMod p, ∑ x : ZMod p, ∑ H : Fin K → Fin d → ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_comm]
  rw [hperm]
  rw [Finset.sum_congr rfl (fun h _ => inner_xH hω h)]
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun h _ => final_arith (P := (Fintype.card (ZMod p) : ℝ))
    (S := ∑ y : ZMod p, ∏ ω' : Fin d → Bool, ν (y + ∑ i, (if ω' i then h i else 0)))
    hPne hd)]

end Commons.Combinatorics.Transference