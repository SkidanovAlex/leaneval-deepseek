import Mathlib
import Submission.Commons.Data.Nat.card_divisors_le_const_mul_rpow
import Submission.Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_count_eq_fin_count
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.large_sieve_sq_neg_one
import Submission.Commons.Analysis.ExponentialSums.large_sieve
import Submission.Commons.Analysis.ExponentialSums.large_sieve_sq_neg_one_Icc
import Submission.Commons.Data.Nat.collapse_grid_coef_bound
import Submission.Commons.Analysis.Real.natLog_two_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

def rootSet (d : ℕ) : Finset ℕ := (Finset.range d).filter (fun ν : ℕ => d ∣ ν^2 + 1)

lemma mem_rootSet {d ν : ℕ} : ν ∈ rootSet d ↔ ν < d ∧ d ∣ ν^2 + 1 := by
  simp [rootSet]

lemma rootSet_eq_zmod (d : ℕ) :
    rootSet d = (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1) := by
  rw [rootSet]
  refine Finset.filter_congr (fun ν _ => ?_)
  constructor
  · intro h
    have h' : (((ν:ZMod d))^2 + 1) = 0 := by
      have h2 := (ZMod.natCast_eq_zero_iff (ν^2+1) d).mpr h
      push_cast at h2; exact h2
    rw [add_eq_zero_iff_eq_neg] at h'; exact h'
  · intro h
    have h' : (((ν^2+1 : ℕ)) : ZMod d) = 0 := by push_cast; rw [h]; ring
    exact (ZMod.natCast_eq_zero_iff (ν^2+1) d).mp h'

lemma card_rootSet_le (d : ℕ) (hd : 0 < d) : (rootSet d).card ≤ 2 ^ (d.primeFactors.card) := by
  rw [rootSet]
  haveI : NeZero d := ⟨hd.ne'⟩
  have h1 : ((Finset.range d).filter (fun μ : ℕ => d ∣ μ^2 + 1)).card
      = (Finset.univ.filter (fun x : Fin d => d ∣ (x:ℕ)^2 + 1)).card := by
    refine Finset.card_bij (fun μ hμ => (⟨μ, by simpa using (Finset.mem_filter.mp hμ).1⟩ : Fin d)) ?_ ?_ ?_
    · intro μ hμ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := (Finset.mem_filter.mp hμ).2
      simpa using this
    · intro μ hμ ν hν h
      simpa using h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨x.val, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨x.isLt, by simpa using hx⟩, by
        apply Fin.ext; simp⟩
  rw [h1]
  have h2 : (Finset.univ.filter (fun x : Fin d => d ∣ (x:ℕ)^2 + 1)).card
      = ({x : Fin d | d ∣ (x:ℕ)^2 + 1} : Set (Fin d)).ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [h2]
  rw [← Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_count_eq_fin_count hd]
  exact Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega hd

noncomputable def coef (K L e : ℕ) (ξ : ℕ → ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L),
    if (p.1 * p.2 = N ∧ e ∣ p.2) then ξ p.1 p.2 else 0

noncomputable def gfun (K L : ℕ) (ξ : ℕ → ℕ → ℂ) (d ν e : ℕ) : ℂ :=
  ∑ N ∈ Finset.Icc 1 (K*L), coef K L e ξ N * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ))

lemma coef_eq_zero_of_lt (K L e : ℕ) (ξ : ℕ → ℕ → ℂ) (h : L < e) (N : ℕ) :
    coef K L e ξ N = 0 := by
  rw [coef]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hp2b : p.2 ≤ L := (Finset.mem_Icc.mp hp2).2
  have hp2a : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
  have hnd : ¬ e ∣ p.2 := fun hdvd => by
    have := Nat.le_of_dvd (by omega) hdvd; omega
  simp [hnd]

lemma gfun_eq_zero_of_lt (K L e : ℕ) (ξ : ℕ → ℕ → ℂ) (d ν : ℕ) (h : L < e) :
    gfun K L ξ d ν e = 0 := by
  rw [gfun]
  refine Finset.sum_eq_zero (fun N _ => ?_)
  rw [coef_eq_zero_of_lt K L e ξ h N, zero_mul]

lemma sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M]
    (s1 : Finset α) (s2 : Finset β) (s3 : Finset γ) (s4 : Finset δ)
    (f : α → β → γ → δ → M) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, f a b c d)
      = ∑ d ∈ s4, ∑ c ∈ s3, ∑ a ∈ s1, ∑ b ∈ s2, f a b c d := by
  calc (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, f a b c d)
      = ∑ a ∈ s1, ∑ b ∈ s2, ∑ d ∈ s4, ∑ c ∈ s3, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
    _ = ∑ a ∈ s1, ∑ d ∈ s4, ∑ b ∈ s2, ∑ c ∈ s3, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, f a b c d := Finset.sum_comm
    _ = ∑ d ∈ s4, ∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, f a b c d :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ d ∈ s4, ∑ c ∈ s3, ∑ a ∈ s1, ∑ b ∈ s2, f a b c d :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)

lemma collapse_eq (K L e d ν : ℕ) (ξ : ℕ → ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0))
      = ∑ N ∈ Finset.Icc 1 (K*L),
          coef K L e ξ N * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ)) := by
  have hR : (∑ N ∈ Finset.Icc 1 (K*L), coef K L e ξ N * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ)))
      = ∑ N ∈ Finset.Icc 1 (K*L), (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          (if (k * l = N ∧ e ∣ l) then ξ k l else 0)) * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ)) := by
    refine Finset.sum_congr rfl (fun N _ => ?_)
    rw [coef, Finset.sum_product]
  rw [hR]
  simp only [Finset.sum_mul]
  rw [show (∑ N ∈ Finset.Icc 1 (K*L), ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        (if (k * l = N ∧ e ∣ l) then ξ k l else 0) * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ)))
      = ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ∑ N ∈ Finset.Icc 1 (K*L),
        (if (k * l = N ∧ e ∣ l) then ξ k l else 0) * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((N:ℝ)) / (d:ℝ)) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => ?_))
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hlL : l ≤ L := (Finset.mem_Icc.mp hl).2
  have hmem : k * l ∈ Finset.Icc 1 (K*L) := by
    rw [Finset.mem_Icc]; exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), Nat.mul_le_mul hkK hlL⟩
  rw [Finset.sum_eq_single (k*l)
      (fun b _ hne => by
        have h : ¬ (k * l = b ∧ e ∣ l) := fun hh => hne hh.1.symm
        rw [if_neg h, zero_mul])
      (fun hnot => absurd hmem hnot)]
  by_cases hc : e ∣ l <;> simp [hc]

lemma ite_gcd_eq_one_mul (l d : ℕ) (hd : 0 < d) (X : ℂ) :
    (if Nat.gcd l d = 1 then X else 0)
      = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * (if e ∣ l then X else 0) := by
  have hfil : d.divisors.filter (fun e => e ∣ l) = (Nat.gcd l d).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hed, _⟩, hel⟩
      exact ⟨Nat.dvd_gcd hel hed, (Nat.gcd_pos_of_pos_right l hd).ne'⟩
    · rintro ⟨hg, _⟩
      exact ⟨⟨hg.trans (Nat.gcd_dvd_right l d), hd.ne'⟩, hg.trans (Nat.gcd_dvd_left l d)⟩
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, hfil, ← Finset.sum_mul]
  have h1 : (∑ e ∈ (Nat.gcd l d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ))
      = if Nat.gcd l d = 1 then 1 else 0 := by
    have h2 : (∑ e ∈ (Nat.gcd l d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ))
        = ((∑ e ∈ (Nat.gcd l d).divisors, ArithmeticFunction.moebius e : ℤ) : ℂ) := by
      push_cast; rfl
    rw [h2, Commons.NumberTheory.Moebius.sum_moebius_divisors]
    by_cases h : Nat.gcd l d = 1 <;> simp [h]
  rw [h1]
  by_cases h : Nat.gcd l d = 1 <;> simp [h]

lemma inner_eq (K L d : ℕ) (hd : 0 < d) (ξ : ℕ → ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        (if Nat.gcd l d = 1 then ξ k l *
          (∑ ν ∈ rootSet d, Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ))) else 0))
      = ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e := by
  have hpull : ∀ k l, (if Nat.gcd l d = 1 then ξ k l *
        (∑ ν ∈ rootSet d, Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ))) else 0)
      = ∑ ν ∈ rootSet d,
          (if Nat.gcd l d = 1 then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0) := by
    intro k l
    by_cases h : Nat.gcd l d = 1
    · rw [if_pos h, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      rw [if_pos h]
    · rw [if_neg h, Finset.sum_eq_zero]
      intro ν _; rw [if_neg h]
  have hmoeb : ∀ k l (ν : ℕ), (if Nat.gcd l d = 1 then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0)
      = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0) := by
    intro k l ν
    exact ite_gcd_eq_one_mul l d hd _
  have hg : ∀ e (ν : ℕ), (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0))
        = ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e := by
    intro e ν
    have h1 : (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0))
        = ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
            (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
    rw [h1, collapse_eq K L e d ν ξ, gfun]
  calc (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          (if Nat.gcd l d = 1 then ξ k l * (∑ ν ∈ rootSet d, Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ))) else 0))
      = ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ∑ ν ∈ rootSet d,
          (if Nat.gcd l d = 1 then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => hpull k l))
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ∑ ν ∈ rootSet d, ∑ e ∈ d.divisors,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ =>
          Finset.sum_congr rfl (fun ν _ => hmoeb k l ν)))
    _ = ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (if e ∣ l then ξ k l * Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ)) else 0) :=
        sum_comm4 _ _ _ _ _
    _ = ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e :=
        Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun ν _ => hg e ν))

lemma sum_sqrt_le (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, Real.sqrt (f i) ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, f i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s (f := fun _ : ℕ => (1:ℝ)) (g := f) (fun _ => zero_le_one) hf
  simpa using h

lemma norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  have h : |ArithmeticFunction.moebius n| ≤ 1 := by
    rw [ArithmeticFunction.abs_moebius]; split <;> norm_num
  exact_mod_cast h

lemma divisors_filter_eq (d M : ℕ) (hd : 1 ≤ d) :
    d.divisors.filter (fun e => e ≤ M) = (Finset.Icc 1 M).filter (fun e => e ∣ d) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hed, _⟩, heM⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hed (by omega), heM⟩, hed⟩
  · rintro ⟨⟨he1, heM⟩, hed⟩
    exact ⟨⟨hed, by omega⟩, heM⟩


open Finset

lemma norm_sum_le_sqrt_card_mul (s : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ i ∈ s, f i‖ ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, ‖f i‖^2) := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ s, ‖f i‖)^2 ≤ (s.card : ℝ) * (∑ i ∈ s, ‖f i‖^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ : ℕ => (1:ℝ))
    have hc : (∑ _i ∈ s, ((1:ℝ))^2) = (s.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]; simp
    rw [hc, mul_comm] at h
    simpa using h
  have h3 : (∑ i ∈ s, ‖f i‖) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2) := by
    have hs : (0:ℝ) ≤ ∑ i ∈ s, ‖f i‖ := by positivity
    calc (∑ i ∈ s, ‖f i‖) = Real.sqrt ((∑ i ∈ s, ‖f i‖) ^ 2) := (Real.sqrt_sq hs).symm
      _ ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2) := Real.sqrt_le_sqrt h2
  refine h1.trans ?_
  rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (s.card : ℝ))]
  exact h3

lemma swap_divisors_le (D M : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ d e, 0 ≤ F d e)
    (hzero : ∀ d e, 1 ≤ d → e ∈ d.divisors → M < e → F d e = 0) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, F d e)
      ≤ ∑ e ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 D, F d e := by
  have step1 : ∀ d ∈ Finset.Icc 1 D, (∑ e ∈ d.divisors, F d e)
      = (∑ e ∈ Finset.Icc 1 M, if e ∣ d then F d e else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [← Finset.sum_subset (Finset.filter_subset (fun e => e ≤ M) d.divisors) ?_]
    · rw [divisors_filter_eq d M hd1, Finset.sum_filter]
    · intro e he hef
      simp only [Finset.mem_filter, not_and] at hef
      exact hzero d e hd1 he (by have := hef he; omega)
  calc (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, F d e)
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 M, (if e ∣ d then F d e else 0) :=
        Finset.sum_congr rfl step1
    _ = ∑ e ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 D, (if e ∣ d then F d e else 0) :=
        Finset.sum_comm
    _ ≤ ∑ e ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 D, F d e := by
        refine Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun d _ => ?_))
        by_cases h : e ∣ d
        · simp [h]
        · simp only [h, if_false]; exact hF d e

theorem reduced_linear_form_uniform (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D K L : ℕ), 1 ≤ D → 1 ≤ K → 1 ≤ L → ∀ ξ : ℕ → ℕ → ℂ,
      (∑ d ∈ Finset.Icc 1 D, ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          (if Nat.gcd l d = 1 then ξ k l *
            (∑ μ ∈ (Finset.range d).filter (fun μ : ℕ => d ∣ μ^2 + 1),
              Commons.Analysis.ExponentialSums.ch ((μ:ℝ) * ((k*l):ℝ) / (d:ℝ))) else 0)‖)
        ≤ C * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^eps
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
  set η : ℝ := eps/10 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηeps : 5*η/2 ≤ eps := by rw [hηdef]; linarith
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow η hη
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.Data.Nat.card_divisors_le_const_mul_rpow η hη
  obtain ⟨C3, hC3pos, hC3⟩ := Commons.Analysis.Real.natLog_two_bound η hη
  obtain ⟨C4, hC4pos, hC4⟩ := Commons.Data.Nat.collapse_grid_coef_bound η hη
  refine ⟨Real.sqrt (C1 * C2 * (8 * C3 * C4)) + 1, by positivity, ?_⟩
  intro D K L hD hK hL ξ
  set S : ℝ := ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖ ^ 2 with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  -- rewrite the LHS using Möbius
  have hstepA : (∑ d ∈ Finset.Icc 1 D, ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        (if Nat.gcd l d = 1 then ξ k l *
          (∑ ν ∈ rootSet d, Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * ((k*l:ℝ)) / (d:ℝ))) else 0)‖)
      = ∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖ := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd1 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
    congr 1
    exact inner_eq K L d hd1 ξ
  simp only [rootSet] at hstepA
  rw [hstepA]
  -- per-d Cauchy–Schwarz
  have hB1 : ∀ d ∈ Finset.Icc 1 D,
      ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖
        ≤ Real.sqrt (((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
            * Real.sqrt (∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) := by
    intro d hd
    have h1 : (∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e)
        = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (∑ ν ∈ rootSet d, gfun K L ξ d ν e) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum]
    rw [h1]
    calc ‖∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (∑ ν ∈ rootSet d, gfun K L ξ d ν e)‖
        ≤ ∑ e ∈ d.divisors, ‖((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            (∑ ν ∈ rootSet d, gfun K L ξ d ν e)‖ := norm_sum_le _ _
      _ ≤ ∑ e ∈ d.divisors, ‖∑ ν ∈ rootSet d, gfun K L ξ d ν e‖ := by
          refine Finset.sum_le_sum (fun e _ => ?_)
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le_one e)
      _ ≤ ∑ e ∈ d.divisors, Real.sqrt ((rootSet d).card : ℝ) *
            Real.sqrt (∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) := by
          refine Finset.sum_le_sum (fun e _ => ?_)
          exact norm_sum_le_sqrt_card_mul _ _
      _ = Real.sqrt ((rootSet d).card : ℝ) *
            ∑ e ∈ d.divisors, Real.sqrt (∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt ((rootSet d).card : ℝ) *
            (Real.sqrt ((d.divisors.card : ℝ)) *
              Real.sqrt (∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          exact sum_sqrt_le d.divisors (fun e => ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
            (fun e => by positivity)
      _ = Real.sqrt (((rootSet d).card : ℝ) * (d.divisors.card : ℝ)) *
            Real.sqrt (∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((rootSet d).card : ℝ))]
          ring
  have hB2 : (∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖)
      ≤ Real.sqrt (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
        * Real.sqrt (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
            ‖gfun K L ξ d ν e‖ ^ 2) := by
    calc (∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖)
        ≤ ∑ d ∈ Finset.Icc 1 D, Real.sqrt (((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
            * Real.sqrt (∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) :=
          Finset.sum_le_sum hB1
      _ ≤ Real.sqrt (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
            * Real.sqrt (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
                ‖gfun K L ξ d ν e‖ ^ 2) :=
          Real.sum_sqrt_mul_sqrt_le (Finset.Icc 1 D)
            (f := fun d => ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
            (g := fun d => ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
            (fun _ => by positivity) (fun _ => by positivity)
  -- bound the first factor
  have hDeta : ∀ d ∈ Finset.Icc 1 D, (d:ℝ)^η ≤ (D:ℝ)^η := by
    intro d hd
    exact Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast (Finset.mem_Icc.mp hd).2) (le_of_lt hη)
  have hroot_le : ∀ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) ≤ C1 * (D:ℝ)^η := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have h1 : ((rootSet d).card : ℝ) ≤ (2 : ℝ)^(d.primeFactors.card) := by
      exact_mod_cast card_rootSet_le d (by omega)
    have h2 : (2 : ℝ)^(d.primeFactors.card) ≤ C1 * (d:ℝ)^η := hC1 d hd1
    have h3 : (d:ℝ)^η ≤ (D:ℝ)^η := hDeta d hd
    calc ((rootSet d).card : ℝ) ≤ (2:ℝ)^(d.primeFactors.card) := h1
      _ ≤ C1 * (d:ℝ)^η := h2
      _ ≤ C1 * (D:ℝ)^η := mul_le_mul_of_nonneg_left h3 (le_of_lt hC1pos)
  have hdiv_le : ∀ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ≤ C2 * (D:ℝ)^η := by
    intro d hd
    have h2 : ((d.divisors.card : ℝ)) ≤ C2 * (d:ℝ)^η := hC2 d
    have h3 : (d:ℝ)^η ≤ (D:ℝ)^η := hDeta d hd
    calc ((d.divisors.card : ℝ)) ≤ C2 * (d:ℝ)^η := h2
      _ ≤ C2 * (D:ℝ)^η := mul_le_mul_of_nonneg_left h3 (le_of_lt hC2pos)
  have hF1 : (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
      ≤ C1 * C2 * ((D:ℝ)^(1+2*η)) := by
    calc (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (C1 * (D:ℝ)^η) * (C2 * (D:ℝ)^η) := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          exact mul_le_mul (hroot_le d hd) (hdiv_le d hd) (by positivity) (by positivity)
      _ = (D:ℝ) * ((C1 * (D:ℝ)^η) * (C2 * (D:ℝ)^η)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ = C1 * C2 * ((D:ℝ)^(1+2*η)) := by
          rw [Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ)) 1 (2*η), Real.rpow_one,
              show (2:ℝ)*η = η+η from by ring,
              Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ)) η η]
          ring
  -- the large sieve term
  have hLS : ∀ e : ℕ, (∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
      ≤ 8 * ((Nat.log 2 D : ℝ) + 1) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
          * (∑ N ∈ Finset.Icc 1 (K*L), ‖coef K L e ξ N‖ ^ 2) := by
    intro e
    have h := Commons.Analysis.ExponentialSums.large_sieve_sq_neg_one_Icc D (K*L) (coef K L e ξ)
    rw [show (∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
        = (∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
            ‖∑ n ∈ Finset.Icc 1 (K*L), coef K L e ξ n * Commons.Analysis.ExponentialSums.ch ((n:ℝ)*((ν:ℝ))/(d:ℝ))‖^2) from ?_]
    · simpa only [Nat.cast_mul] using h
    · refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [rootSet_eq_zmod d]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      congr 1
      congr 1
      rw [gfun]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show (ν:ℝ) * ((n:ℝ)) / (d:ℝ) = (n:ℝ) * (ν:ℝ) / (d:ℝ) from by ring]
  have hF2 : (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
      ≤ 8 * C3 * C4 * (D:ℝ)^η * (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S := by
    have hswap := swap_divisors_le D (K*L) (fun d e => ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
        (fun d e => by positivity)
        (fun d e hd1 he hlt => by
          have hLK : L ≤ K*L := by
            have h1 : 1*L ≤ K*L := Nat.mul_le_mul_right L hK
            simpa using h1
          have hgt : L < e := lt_of_le_of_lt hLK hlt
          refine Finset.sum_eq_zero (fun ν _ => ?_)
          rw [gfun_eq_zero_of_lt K L e ξ d ν hgt]
          simp)
    refine hswap.trans ?_
    calc (∑ e ∈ Finset.Icc 1 (K*L), ∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
        ≤ ∑ e ∈ Finset.Icc 1 (K*L), 8 * ((Nat.log 2 D : ℝ) + 1) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
            * (∑ N ∈ Finset.Icc 1 (K*L), ‖coef K L e ξ N‖ ^ 2) := by
          refine Finset.sum_le_sum (fun e _ => ?_)
          exact hLS e
      _ = 8 * ((Nat.log 2 D : ℝ) + 1) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
            * (∑ e ∈ Finset.Icc 1 (K*L), ∑ N ∈ Finset.Icc 1 (K*L), ‖coef K L e ξ N‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * ((Nat.log 2 D : ℝ) + 1) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
            * (C4 * (((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hSdef]
          simpa only [mul_assoc, coef, Finset.product_eq_sprod] using hC4 K L ξ hK hL
      _ ≤ 8 * C3 * C4 * (D:ℝ)^η * (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S := by
          have ha : (Nat.log 2 D : ℝ) + 1 ≤ C3 * (D:ℝ)^η := hC3 D hD
          calc 8 * ((Nat.log 2 D : ℝ) + 1) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
                * (C4 * (((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S))
              ≤ 8 * (C3 * (D:ℝ)^η) * (((K:ℝ)*(L:ℝ)) + (D:ℝ))
                * (C4 * (((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S)) := by gcongr
            _ = 8 * C3 * C4 * (D:ℝ)^η * (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S := by
                ring
  -- assemble
  have hsqrt1 : Real.sqrt (C1 * C2 * ((D:ℝ)^(1+2*η))) = Real.sqrt (C1*C2) * (D:ℝ)^(1/2 + η) := by
    rw [show C1 * C2 * ((D:ℝ)^(1+2*η)) = (C1*C2) * ((D:ℝ)^(1+2*η)) from by ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ C1*C2)]
    rw [show Real.sqrt ((D:ℝ)^(1+2*η)) = (D:ℝ)^(1/2+η) from by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg D)]; congr 1; ring]
  have e1 : Real.sqrt ((D:ℝ)^η) = (D:ℝ)^(η/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg D)]; congr 1; ring
  have e2 : Real.sqrt (((K:ℝ)*(L:ℝ))^η) = ((K:ℝ)*(L:ℝ))^(η/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (K:ℝ)*(L:ℝ))]; congr 1; ring
  have e3 : Real.sqrt ((L:ℝ)^η) = (L:ℝ)^(η/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg L)]; congr 1; ring
  have hregroup : (8 * C3 * C4 * (D:ℝ)^η * (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S)
      = (8*C3*C4) * ((D:ℝ)^η * ((((K:ℝ)*(L:ℝ)) + (D:ℝ)) * (((K:ℝ)*(L:ℝ))^η * ((L:ℝ)^η * S)))) := by ring
  have hsqrt2 : Real.sqrt (8 * C3 * C4 * (D:ℝ)^η * (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^η * (L:ℝ)^η * S)
      = Real.sqrt (8*C3*C4) * (D:ℝ)^(η/2) * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ))
          * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := by
    rw [hregroup]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 8*C3*C4)]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (D:ℝ)^η)]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((K:ℝ)*(L:ℝ)) + (D:ℝ))]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((K:ℝ)*(L:ℝ))^η)]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (L:ℝ)^η)]
    rw [e1, e2, e3]
    ring
  have hDKL : (1:ℝ) ≤ (D:ℝ) * (K:ℝ) * (L:ℝ) := by
    have h1 : (1:ℕ) ≤ D*K*L := by
      have h2 : 1*1*1 ≤ D*K*L := Nat.mul_le_mul (Nat.mul_le_mul hD hK) hL
      simpa using h2
    exact_mod_cast h1
  have hrpow_absorb : (D:ℝ)^(3*η/2) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2)
      ≤ (((D:ℝ)*(K:ℝ)*(L:ℝ)))^eps := by
    have hDpos : (0:ℝ) < D := by exact_mod_cast hD
    have hKLpos : (0:ℝ) < (K:ℝ)*(L:ℝ) := by
      have : (0:ℕ) < K*L := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    have hLpos : (0:ℝ) < L := by exact_mod_cast hL
    have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
    have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
    have hL1 : (1:ℝ) ≤ L := by exact_mod_cast hL
    have hKL1 : (1:ℝ) ≤ (K:ℝ)*(L:ℝ) := by nlinarith [hK1, hL1]
    have h1 : (D:ℝ)^(3*η/2) ≤ ((D:ℝ)*(K:ℝ)*(L:ℝ))^(3*η/2) := by
      apply Real.rpow_le_rpow (le_of_lt hDpos) _ (by positivity)
      nlinarith [hD1, hKL1]
    have h2 : ((K:ℝ)*(L:ℝ))^(η/2) ≤ ((D:ℝ)*(K:ℝ)*(L:ℝ))^(η/2) := by
      apply Real.rpow_le_rpow (le_of_lt hKLpos) _ (by positivity)
      nlinarith [hD1, hKL1]
    have h3 : (L:ℝ)^(η/2) ≤ ((D:ℝ)*(K:ℝ)*(L:ℝ))^(η/2) := by
      apply Real.rpow_le_rpow (le_of_lt hLpos) _ (by positivity)
      nlinarith [hD1, hK1, hL1]
    have h4 : (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(3*η/2) * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(η/2) * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(η/2)
        = (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(3*η/2 + η/2 + η/2) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ)*(K:ℝ)*(L:ℝ)),
          ← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ)*(K:ℝ)*(L:ℝ))]
    calc (D:ℝ)^(3*η/2) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2)
        ≤ (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(3*η/2) * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(η/2) * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(η/2) := by
          gcongr
      _ = (((D:ℝ)*(K:ℝ)*(L:ℝ)))^(3*η/2 + η/2 + η/2) := h4
      _ ≤ (((D:ℝ)*(K:ℝ)*(L:ℝ)))^eps := by
          rcases lt_or_eq_of_le hDKL with hlt | heq
          · exact le_of_lt ((Real.rpow_lt_rpow_left_iff hlt).mpr (by linarith [hηeps]))
          · rw [← heq, Real.one_rpow, Real.one_rpow]
  have hmain : (∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖)
      ≤ Real.sqrt (C1 * C2 * (8 * C3 * C4)) * (D:ℝ)^(1/2+3*η/2)
          * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := by
    refine hB2.trans ?_
    have hA : Real.sqrt (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
        ≤ Real.sqrt (C1*C2) * (D:ℝ)^(1/2+η) := by
      rw [← hsqrt1]; exact Real.sqrt_le_sqrt hF1
    have hBb : Real.sqrt (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
        ≤ Real.sqrt (8*C3*C4) * (D:ℝ)^(η/2) * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ))
              * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := by
      rw [← hsqrt2]; exact Real.sqrt_le_sqrt hF2
    have hDpow : (D:ℝ)^(1/2+η) * (D:ℝ)^(η/2) = (D:ℝ)^(1/2+3*η/2) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ))]; congr 1; ring
    have hsq12 : Real.sqrt (C1*C2) * Real.sqrt (8*C3*C4) = Real.sqrt (C1*C2*(8*C3*C4)) := by
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ C1*C2)]
    have hb2nn : (0:ℝ) ≤ Real.sqrt (C1*C2) * (D:ℝ)^(1/2+η) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg D) _)
    have hb1nn : (0:ℝ) ≤ Real.sqrt (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2) :=
      Real.sqrt_nonneg _
    calc Real.sqrt (∑ d ∈ Finset.Icc 1 D, ((rootSet d).card : ℝ) * (d.divisors.card : ℝ))
          * Real.sqrt (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ d.divisors, ∑ ν ∈ rootSet d, ‖gfun K L ξ d ν e‖ ^ 2)
        ≤ (Real.sqrt (C1*C2) * (D:ℝ)^(1/2+η))
          * (Real.sqrt (8*C3*C4) * (D:ℝ)^(η/2) * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ))
              * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S) :=
          mul_le_mul hA hBb hb1nn hb2nn
      _ = Real.sqrt (C1*C2) * Real.sqrt (8*C3*C4) * ((D:ℝ)^(1/2+η) * (D:ℝ)^(η/2))
            * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := by
          ring
      _ = Real.sqrt (C1 * C2 * (8 * C3 * C4)) * (D:ℝ)^(1/2+3*η/2)
            * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := by
          rw [hsq12, hDpow]
  calc (∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ d.divisors, ∑ ν ∈ rootSet d,
          ((ArithmeticFunction.moebius e : ℤ) : ℂ) * gfun K L ξ d ν e‖)
      ≤ Real.sqrt (C1 * C2 * (8 * C3 * C4)) * (D:ℝ)^(1/2+3*η/2)
          * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S := hmain
    _ ≤ (Real.sqrt (C1 * C2 * (8 * C3 * C4)) + 1) * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ)))^eps * Real.sqrt S := by
        have hDpos : (0:ℝ) < D := by exact_mod_cast hD
        have hsqrtD : (D:ℝ)^((1:ℝ)/2) * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ))
            = Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) := by
          rw [show ((K:ℝ)*(L:ℝ) + (D:ℝ)) = ((D:ℝ) + (K:ℝ)*(L:ℝ)) from by ring]
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.mul_rpow (le_of_lt hDpos) (by positivity)]
        have hsplit : (D:ℝ)^(1/2+3*η/2) = (D:ℝ)^((1:ℝ)/2) * (D:ℝ)^(3*η/2) := by
          rw [Real.rpow_add hDpos]
        rw [hsplit]
        calc Real.sqrt (C1*C2*(8*C3*C4)) * ((D:ℝ)^((1:ℝ)/2) * (D:ℝ)^(3*η/2))
              * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ)) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) * Real.sqrt S
            = Real.sqrt (C1*C2*(8*C3*C4)) * ((D:ℝ)^(3*η/2) * (((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2)))
              * ((D:ℝ)^((1:ℝ)/2) * Real.sqrt (((K:ℝ)*(L:ℝ)) + (D:ℝ))) * Real.sqrt S := by ring
          _ ≤ Real.sqrt (C1*C2*(8*C3*C4)) * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
              * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S := by
              rw [hsqrtD]
              have h1 : (D:ℝ)^(3*η/2) * (((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2))
                  ≤ (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps) := by
                have h2 : (D:ℝ)^(3*η/2) * (((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2))
                    = (D:ℝ)^(3*η/2) * ((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2) := by ring
                rw [h2]; exact hrpow_absorb
              have hS1 : (0:ℝ) ≤ Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) := Real.sqrt_nonneg _
              have hS2 : (0:ℝ) ≤ Real.sqrt S := Real.sqrt_nonneg _
              calc Real.sqrt (C1*C2*(8*C3*C4)) * ((D:ℝ)^(3*η/2) * (((K:ℝ)*(L:ℝ))^(η/2) * (L:ℝ)^(η/2)))
                    * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S
                  ≤ Real.sqrt (C1*C2*(8*C3*C4)) * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
                    * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S := by
                    gcongr
                _ = Real.sqrt (C1*C2*(8*C3*C4)) * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
                    * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S := rfl
          _ ≤ (Real.sqrt (C1*C2*(8*C3*C4)) + 1) * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ)))
              * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps) * Real.sqrt S := by
              have h2 : Real.sqrt (C1*C2*(8*C3*C4)) ≤ Real.sqrt (C1*C2*(8*C3*C4)) + 1 := by linarith
              calc Real.sqrt (C1*C2*(8*C3*C4)) * ((D:ℝ)*(K:ℝ)*(L:ℝ))^eps
                    * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S
                  ≤ (Real.sqrt (C1*C2*(8*C3*C4)) + 1) * ((D:ℝ)*(K:ℝ)*(L:ℝ))^eps
                    * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * Real.sqrt S := by
                    gcongr
                _ = (Real.sqrt (C1*C2*(8*C3*C4)) + 1) * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ)))
                    * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps) * Real.sqrt S := by ring




end Commons.NumberTheory.FriedlanderIwaniec
