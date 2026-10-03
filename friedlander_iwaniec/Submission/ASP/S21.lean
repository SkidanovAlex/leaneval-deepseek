/-
  **The `4 ∣ d` case of hypothesis `(R₃)` for X² + Y⁴.**

  The commons theorem `X2Y4_R3_hypothesis` proves the companion paper's `(R₃)` for the
  *cubefree moduli not divisible by `4`*; the remaining moduli are `d = 4m` with `m` odd
  cubefree.  They are handled here by the identity (exact up to `O(√x/m)`)

      `M_{4m}(x) = 2 · M_m(x/16)`      (`M_d` = the `√`-main term of §3 of the main paper)

  which reduces the `4 ∣ d` main term to the `¬ 4 ∣ d` one at the smaller scale `x/16`, together
  with the divisor-sum (3.3) `∑_{d ≤ D}|A_d − M_d| ≪ D^{1/4}x^{9/16+ε}` (valid for **all** `d`)
  and the standard comparison `M_d(x) − M_d^{√}(x) ≪ d^{-1}τ(d)x^{1/4}`.
-/
import Mathlib
import Submission.ASP.S20
import Submission.Commons.NumberTheory.Diophantine.sum_inv_sqrt_asymptotic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_R3_hypothesis
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_mul_four
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_sq_four_mul
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_rho_sq_div_le
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

/-! ## The `√`-main term of §3, as a function of a real point -/

/-- The `√`-main term of the main paper's §3, for a **real** point `X`:
`M_d(X) = d^{-1}∑_{|c| ≤ ⌊X^{1/4}⌋} ρ(c²;d)·2√(X − c⁴)`.
For integral `X` this is exactly the quantity appearing as the subtrahend in
`Submission.Md_sub_main_term_sum_le`. -/
def MdS (d : ℕ) (X : ℝ) : ℝ :=
  (1 / (d : ℝ)) * ∑ c ∈ Finset.Icc (-(⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ),
    (Submission.rho (c.natAbs ^ 2) d : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4))

/-- `MdS` in the `ℕ`-indexed form (symmetric in `c ↔ -c`). -/
lemma MdS_eq_nat (d : ℕ) (X : ℝ) :
    MdS d X = (1 / (d : ℝ)) * ((Submission.rho 0 d : ℝ) * (2 * Real.sqrt X)
      + 2 * ∑ c ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 4)⌋₊,
          (Submission.rho (c ^ 2) d : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4))) := by
  have hL : (∑ c ∈ Finset.Icc (-(⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ),
        (Submission.rho (c.natAbs ^ 2) d : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)))
      = ∑ c ∈ Finset.Icc (-(⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊X ^ ((1 : ℝ) / 4)⌋₊ : ℤ),
          (fun k : ℤ => (Submission.rho (k.natAbs ^ 2) d : ℝ)
            * (2 * Real.sqrt (X - (k : ℝ) ^ 4))) ((c.natAbs : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h4 : ((((c.natAbs : ℕ) : ℤ) : ℝ)) ^ 4 = (c : ℝ) ^ 4 := by
      have h1 : ((((c.natAbs : ℕ) : ℤ) : ℝ)) = |(c : ℝ)| := by
        rw [Int.natCast_natAbs c, Int.cast_abs]
      rw [h1, ← abs_pow]
      exact abs_of_nonneg (by positivity)
    beta_reduce
    rw [Int.natAbs_natCast, h4]
  rw [MdS, hL,
    sum_Icc_abs_eq (fun k : ℤ => (Submission.rho (k.natAbs ^ 2) d : ℝ)
      * (2 * Real.sqrt (X - (k : ℝ) ^ 4))) ⌊X ^ ((1 : ℝ) / 4)⌋₊]
  have h1 : ∀ k ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 4)⌋₊,
      (Submission.rho (((k : ℤ)).natAbs ^ 2) d : ℝ) * (2 * Real.sqrt (X - ((k : ℤ) : ℝ) ^ 4))
      = (Submission.rho (k ^ 2) d : ℝ) * (2 * Real.sqrt (X - (k : ℝ) ^ 4)) := by
    intro k _
    rw [Int.natAbs_natCast]
    push_cast
    ring
  congr 1
  rw [Finset.sum_congr rfl h1]
  norm_num

/-! ## The identity `M_{4m}(x) = 2 M_m(x/16)` -/

/-- `ρ(b²; 4) = 0` for odd `b`: modulo `4`, `α² + b⁴ ≡ α² + 1` has no root. -/
lemma rho_sq_four_eq_zero_of_odd (b : ℕ) (hb : Odd b) : Submission.rho (b ^ 2) 4 = 0 := by
  have hb4 : (((b ^ 2 : ℕ)) : ZMod 4) = 1 := by
    obtain ⟨k, rfl⟩ := hb
    push_cast
    exact (by decide : ∀ j : ZMod 4, (2 * j + 1) ^ 2 = 1) (k : ZMod 4)
  have hempty : {α : ZMod 4 | α ^ 2 + (((b ^ 2 : ℕ)) : ZMod 4) ^ 2 = 0} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro α hα
    simp only [Set.mem_ofPred_eq] at hα
    rw [hb4] at hα
    exact (by decide : ∀ j : ZMod 4, j ^ 2 + (1 : ZMod 4) ^ 2 ≠ 0) α hα
  rw [Submission.rho, hempty, Set.ncard_empty]

/-- `ρ(b²; 4m) = 0` for `m` odd and `b` odd. -/
lemma rho_sq_four_eq_zero_of_odd_mul (m b : ℕ) (hm : ¬ 2 ∣ m) (hb : Odd b) :
    Submission.rho (b ^ 2) (4 * m) = 0 := by
  have h2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  have hcop : Nat.Coprime 4 m := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.Coprime.pow_left 2 h2
  rw [Commons.NumberTheory.FriedlanderIwaniec.rho_mul_of_coprime (b ^ 2) 4 m hcop,
    rho_sq_four_eq_zero_of_odd b hb, zero_mul]

lemma sqrt_sixteen_mul (y : ℝ) : Real.sqrt (16 * y) = 4 * Real.sqrt y := by
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 16 by norm_num),
    show Real.sqrt (16 : ℝ) = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

lemma sqrt_sub_sq_four (X : ℝ) (u : ℝ) :
    Real.sqrt (X - (2 * u) ^ 4) = 4 * Real.sqrt (X / 16 - u ^ 4) := by
  have h : X - (2 * u) ^ 4 = 16 * (X / 16 - u ^ 4) := by ring
  rw [h, sqrt_sixteen_mul]

lemma sqrt_div_sixteen (X : ℝ) : Real.sqrt (X / 16) = Real.sqrt X / 4 := by
  rw [Real.sqrt_div' X (by norm_num : (0 : ℝ) ≤ 16),
    show Real.sqrt (16 : ℝ) = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

lemma floor_div_two_of_rpow (X : ℝ) (hX : 0 ≤ X) :
    ⌊(X / 16) ^ ((1 : ℝ) / 4)⌋₊ = ⌊X ^ ((1 : ℝ) / 4)⌋₊ / 2 := by
  have h1 : (X / 16) ^ ((1 : ℝ) / 4) = X ^ ((1 : ℝ) / 4) / 2 := by
    have h2 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [Real.div_rpow hX (by norm_num : (0 : ℝ) ≤ 16), h2]
  rw [h1]
  exact Nat.floor_div_natCast (X ^ ((1 : ℝ) / 4)) 2

/-- Reindexing a sum over the even numbers of `Icc 1 N` by `k ↦ 2k`. -/
lemma sum_even_reindex (N : ℕ) (F : ℕ → ℝ) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c => 2 ∣ c), F c)
      = ∑ k ∈ Finset.Icc 1 (N / 2), F (2 * k) := by
  refine Finset.sum_bij' (fun c _ => c / 2) (fun k _ => 2 * k) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨h1, h2⟩, k, hk⟩ := hc
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨k, by ring⟩⟩
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, k, hk⟩ := hc
    rw [hk, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  · intro k _
    exact Nat.mul_div_cancel_left k (by norm_num : 0 < 2)
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, k, hk⟩ := hc
    rw [hk, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

/-- **The `4 ∣ d` identity**: `M_{4m}(x) = 2 M_m(x/16) + O(√x/m)` for odd `m`. -/
lemma MdS_four_mul (m : ℕ) (hm : ¬ 2 ∣ m) (X : ℝ) (hX : 0 ≤ X) :
    MdS (4 * m) X = 2 * MdS m (X / 16)
      + (Real.sqrt X / (2 * (m : ℝ))) *
          ((Submission.rho 0 (4 * m) : ℝ) - 2 * (Submission.rho 0 m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact absurd (dvd_zero 2) hm
      · exact h
    exact_mod_cast hmpos
  set N : ℕ := ⌊X ^ ((1 : ℝ) / 4)⌋₊ with hN
  set T : ℝ := ∑ k ∈ Finset.Icc 1 (N / 2),
    (Submission.rho (k ^ 2) m : ℝ) * (2 * Real.sqrt (X / 16 - (k : ℝ) ^ 4)) with hT
  have hfloor : ⌊(X / 16) ^ ((1 : ℝ) / 4)⌋₊ = N / 2 := by
    rw [hN]; exact floor_div_two_of_rpow X hX
  have hinner : (∑ c ∈ Finset.Icc 1 N,
      (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)))
      = 8 * T := by
    have hodd : ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ 2 ∣ c),
        (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hc2⟩ := hc
      have hcodd : Odd c := Nat.not_even_iff_odd.mp (by
        rw [even_iff_two_dvd]; exact hc2)
      rw [rho_sq_four_eq_zero_of_odd_mul m c hm hcodd]; ring
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun c => 2 ∣ c)
      (fun c => (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)))
    have heveneq : ∑ c ∈ (Finset.Icc 1 N).filter (fun c => 2 ∣ c),
        (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4))
        = ∑ k ∈ Finset.Icc 1 (N / 2),
            (Submission.rho ((2 * k) ^ 2) (4 * m) : ℝ)
              * (2 * Real.sqrt (X - ((2 * k : ℕ) : ℝ) ^ 4)) :=
      sum_even_reindex N
        (fun c => (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)))
    have hterm : ∀ k : ℕ,
        (Submission.rho ((2 * k) ^ 2) (4 * m) : ℝ)
            * (2 * Real.sqrt (X - ((2 * k : ℕ) : ℝ) ^ 4))
          = 8 * ((Submission.rho (k ^ 2) m : ℝ)
              * (2 * Real.sqrt (X / 16 - (k : ℝ) ^ 4))) := by
      intro k
      rw [Commons.NumberTheory.FriedlanderIwaniec.rho_sq_four_mul k m hm]
      have h1 : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      rw [h1, sqrt_sub_sq_four X (k : ℝ)]
      push_cast
      ring
    calc (∑ c ∈ Finset.Icc 1 N,
        (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)))
        = ∑ c ∈ (Finset.Icc 1 N).filter (fun c => 2 ∣ c),
            (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4)) := by
          rw [← hsplit, hodd, add_zero]
      _ = ∑ k ∈ Finset.Icc 1 (N / 2),
            (Submission.rho ((2 * k) ^ 2) (4 * m) : ℝ)
              * (2 * Real.sqrt (X - ((2 * k : ℕ) : ℝ) ^ 4)) := heveneq
      _ = ∑ k ∈ Finset.Icc 1 (N / 2), 8 * ((Submission.rho (k ^ 2) m : ℝ)
            * (2 * Real.sqrt (X / 16 - (k : ℝ) ^ 4))) :=
            Finset.sum_congr rfl (fun k _ => hterm k)
      _ = 8 * T := by rw [← Finset.mul_sum, hT]
  have hL : MdS (4 * m) X = (1 / ((4 * m : ℕ) : ℝ)) * ((Submission.rho 0 (4 * m) : ℝ)
      * (2 * Real.sqrt X) + 2 * ∑ c ∈ Finset.Icc 1 N,
        (Submission.rho (c ^ 2) (4 * m) : ℝ) * (2 * Real.sqrt (X - (c : ℝ) ^ 4))) := by
    rw [MdS_eq_nat, ← hN]
  have hR : MdS m (X / 16) = (1 / (m : ℝ)) * ((Submission.rho 0 m : ℝ)
      * (2 * Real.sqrt (X / 16)) + 2 * T) := by
    rw [MdS_eq_nat, hfloor, ← hT]
  rw [hL, hR, hinner, sqrt_div_sixteen]
  field_simp
  push_cast
  ring



/-- The `c = 0` case of the `4m`-identity: `ρ(0; 4m) = 2ρ(0; m)` for odd `m`. -/
lemma rho_zero_four_mul (m : ℕ) (hm : ¬ 2 ∣ m) :
    Submission.rho 0 (4 * m) = 2 * Submission.rho 0 m := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.rho_sq_four_mul 0 m hm
  simpa using h

/-- **The exact `4 ∣ d` identity**: `M_{4m}(x) = 2 M_m(x/16)` for odd `m`. -/
lemma MdS_four_mul' (m : ℕ) (hm : ¬ 2 ∣ m) (X : ℝ) (hX : 0 ≤ X) :
    MdS (4 * m) X = 2 * MdS m (X / 16) := by
  rw [MdS_four_mul m hm X hX, rho_zero_four_mul m hm]
  push_cast
  ring

/-! ## Comparison with the `√`-main term of the commons development -/

lemma int_pow_four_eq_natAbs_pow (c : ℤ) : (c : ℤ) ^ 4 = ((c.natAbs ^ 4 : ℕ) : ℤ) := by
  have h1 : (c : ℤ) ^ 4 = |(c : ℤ)| ^ 4 := by
    rw [← abs_pow]
    exact (abs_of_nonneg (by positivity : (0 : ℤ) ≤ (c : ℤ) ^ 4)).symm
  rw [h1, ← Int.natCast_natAbs c]
  push_cast
  ring

/-- The number of `β ∈ range d` with `d ∣ β² + c⁴` is the root count `ρ(c²; d)`. -/
lemma card_filter_dvd_sq_add_pow_four_eq_rho (d : ℕ) [NeZero d] (c : ℤ) :
    ((Finset.range d).filter (fun β : ℕ => (d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)).card
      = Submission.rho (c.natAbs ^ 2) d := by
  have hfilter : (Finset.range d).filter (fun β : ℕ => (d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)
      = (Finset.range d).filter
          (fun β : ℕ => (d : ℤ) ∣ (β : ℤ) ^ 2 + (((c.natAbs ^ 2 : ℕ) : ℤ)) ^ 2) := by
    refine Finset.filter_congr fun β _ => ?_
    rw [int_pow_four_eq_natAbs_pow c]
    push_cast
    ring_nf
  rw [hfilter, Submission.card_range_filter_eq_card_zmod d (c.natAbs ^ 2),
    Submission.rho, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- For integral `X`, `MdS` is exactly the `√`-main term of `Submission.Md_sub_main_term_sum_le`. -/
lemma MdS_eq_commons (d : ℕ) [NeZero d] (x : ℕ) :
    MdS d (x : ℝ) = ∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
        ((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)),
      ∑ _β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
        2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ) := by
  rw [MdS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, card_filter_dvd_sq_add_pow_four_eq_rho, nsmul_eq_mul]
  ring


/-! ## The pointwise comparison `M_d^{√}(Y) ≈ M_d(⌊Y⌋)` -/


lemma MdS_sub_Md_le (m : ℕ) (hm : 1 ≤ m)
    (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ m) (Y : ℝ) (hY : 1 ≤ Y) :
    |MdS m Y - (Submission.Md m ⌊Y⌋₊ : ℝ)|
      ≤ (4 * (Submission.rho 0 m : ℝ)
          + 2 * ((m.divisors.card : ℝ)) ^ 2 * (⌊Y ^ ((1 : ℝ) / 4)⌋₊ + 1)) / m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hx0 : (0 : ℝ) ≤ Y := by linarith
  set x : ℕ := ⌊Y⌋₊ with hxdef
  set K : ℕ := ⌊Y ^ ((1 : ℝ) / 4)⌋₊ with hKdef
  set K' : ℕ := Nat.sqrt (Nat.sqrt x) with hKdef'
  have hxle : (x : ℝ) ≤ Y := by rw [hxdef]; exact Nat.floor_le hx0
  have hxlt : Y < (x : ℝ) + 1 := by rw [hxdef]; exact Nat.lt_floor_add_one Y
  have hK'eq : K' = ⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ := by
    rw [hKdef', hxdef]; exact Submission.Nat_sqrt_sqrt_eq x
  have hK'le : K' ≤ K := by
    rw [hK'eq, hKdef]
    refine Nat.floor_mono ?_
    exact Real.rpow_le_rpow (by positivity) hxle (by norm_num)
  have hS : (MdS m Y) * m = (Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y)
      + 2 * ∑ c ∈ Finset.Icc 1 K,
          (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4)) := by
    rw [MdS_eq_nat, hKdef]
    field_simp
  have hN : ((Submission.Md m x : ℚ) : ℝ) * m
      = 2 * (Nat.sqrt x : ℝ) * (Submission.rho 0 m : ℝ)
        + 2 * ∑ c ∈ Finset.Icc 1 K',
            (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) := by
    rw [Submission.Md, hKdef']
    push_cast
    rw [Submission.MdNum_reindex]
    push_cast
    field_simp
    ring
  -- the sum over `Icc 1 K` equals the sum over `Icc 1 K'`
  have hzf : ∀ c : ℕ, K' < c → c ≤ K →
      (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4)) = 0 := by
    intro c hc1 hc2
    have hcge : K' + 1 ≤ c := by omega
    have hpow4 : x < (K' + 1) ^ 4 := by
      have hb : Nat.sqrt x + 1 ≤ (K' + 1) ^ 2 := by
        have hb' : Nat.sqrt x < (K' + 1) ^ 2 := by
          have := Nat.lt_succ_sqrt' (Nat.sqrt x)
          rw [← hKdef'] at this
          simpa [Nat.succ_eq_add_one] using this
        omega
      calc x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' x
        _ ≤ ((K' + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hb 2
        _ = (K' + 1) ^ 4 := by ring
    have hxc : x < c ^ 4 := lt_of_lt_of_le hpow4 (Nat.pow_le_pow_left hcge 4)
    have hYc : Y < ((c : ℝ)) ^ 4 := by
      have hc1' : ((x + 1 : ℕ) : ℝ) ≤ (((c ^ 4 : ℕ)) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hxc)
      push_cast at hc1'
      linarith
    rw [Real.sqrt_eq_zero_of_nonpos (show Y - (c : ℝ) ^ 4 ≤ 0 by linarith)]
    ring
  have hsum_eq : ∑ c ∈ Finset.Icc 1 K,
        (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
      = ∑ c ∈ Finset.Icc 1 K',
        (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4)) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro c hc
      rw [Finset.mem_Icc] at hc ⊢
      exact ⟨hc.1, le_trans hc.2 hK'le⟩
    · intro c hcK hcn
      rw [Finset.mem_Icc] at hcK
      have hgt : K' < c := by
        by_contra hle
        exact hcn (by rw [Finset.mem_Icc]; exact ⟨by omega, not_lt.mp hle⟩)
      exact hzf c hgt hcK.2
  -- termwise comparison
  have hterm : ∀ c ∈ Finset.Icc 1 K',
      |(Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
        - (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ)|
      ≤ (Submission.rho (c ^ 2) m : ℝ) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have hc4 : c ^ 4 ≤ x := by
      have h1 : c ≤ Nat.sqrt (Nat.sqrt x) := by rw [← hKdef']; exact hc.2
      have h2 : (Nat.sqrt (Nat.sqrt x)) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
      have h3 : ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 ≤ (Nat.sqrt x) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      have h4 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
      calc c ^ 4 ≤ (Nat.sqrt (Nat.sqrt x)) ^ 4 := Nat.pow_le_pow_left h1 4
        _ = ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 := by ring
        _ ≤ (Nat.sqrt x) ^ 2 := h3
        _ ≤ x := h4
    have hu : ((x - c ^ 4 : ℕ) : ℝ) = (x : ℝ) - (c : ℝ) ^ 4 := by
      rw [Nat.cast_sub hc4]; push_cast; ring
    have hYc : Y - (c : ℝ) ^ 4 = ((x - c ^ 4 : ℕ) : ℝ) + (Y - (x : ℝ)) := by
      rw [hu]; ring
    set u : ℕ := x - c ^ 4 with hudef
    set s : ℕ := Nat.sqrt u with hsdef
    have hsle : ((s : ℕ) : ℝ) ≤ Real.sqrt (u : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc ((s : ℕ) : ℝ) ^ 2 = (((s : ℕ) ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (u : ℝ) := by
            rw [hsdef]; exact_mod_cast (Nat.sqrt_le' u)
    have htheta0 : (0 : ℝ) ≤ Y - (x : ℝ) := by linarith
    have htheta1 : Y - (x : ℝ) < 1 := by linarith
    have hsqrtle : Real.sqrt (Y - (c : ℝ) ^ 4) ≤ (s : ℝ) + 1 := by
      rw [hYc]
      have h1 : Real.sqrt (((u:ℕ):ℝ) + (Y - (x:ℝ))) ≤ Real.sqrt (((u:ℕ):ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt (((u:ℕ):ℝ) + 1) ≤ (s:ℝ) + 1 := by
        rw [Real.sqrt_le_left (by positivity)]
        have h3 : u + 1 ≤ (s + 1) ^ 2 := by
          rw [hsdef]; exact Nat.succ_le_succ_sqrt' u
        calc (u : ℝ) + 1 = ((u + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (((s + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h3
          _ = ((s : ℝ) + 1) ^ 2 := by push_cast; ring
      linarith
    have hsqrtge : (s : ℝ) ≤ Real.sqrt (Y - (c : ℝ) ^ 4) := by
      rw [hYc]
      exact le_trans hsle (Real.sqrt_le_sqrt (by linarith))
    have hkey : |2 * Real.sqrt (Y - (c : ℝ) ^ 4) - (2 * ((s:ℕ):ℝ) + 1)| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hcast : (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) = 2 * ((s:ℕ):ℝ) + 1 := by
      rw [hsdef, hudef]; push_cast; ring
    rw [hcast, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (Submission.rho (c^2) m : ℝ))]
    calc (Submission.rho (c ^ 2) m : ℝ)
            * |2 * Real.sqrt (Y - (c : ℝ) ^ 4) - (2 * ((s:ℕ):ℝ) + 1)|
        ≤ (Submission.rho (c ^ 2) m : ℝ) * 1 := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (Submission.rho (c ^ 2) m : ℝ) := by ring
  -- the `c = 0` part
  have hrho0 : |2 * Real.sqrt Y - 2 * (Nat.sqrt x : ℝ)| ≤ 4 := by
    have h1 : Real.sqrt (x:ℝ) ≤ Real.sqrt Y := Real.sqrt_le_sqrt hxle
    have h2 : Real.sqrt Y < Real.sqrt (x:ℝ) + 1 := by
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      have h3 : (x:ℝ) + 1 < (Real.sqrt (x:ℝ) + 1) ^ 2 := by
        nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (x:ℝ)), Real.sqrt_nonneg (x:ℝ)]
      linarith
    have h4 : Real.sqrt (x:ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := by
      have h4' : Real.sqrt (x:ℝ) < (Nat.sqrt x : ℝ) + 1 := by
        rw [Real.sqrt_lt (by positivity) (by positivity)]
        calc (x:ℝ) < (((Nat.sqrt x + 1)^2 : ℕ):ℝ) := by exact_mod_cast (Nat.lt_succ_sqrt' x)
          _ = ((Nat.sqrt x : ℝ) + 1) ^ 2 := by push_cast; ring
      linarith
    have h7 : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x:ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc ((Nat.sqrt x : ℝ)) ^ 2 = (((Nat.sqrt x)^2 : ℕ):ℝ) := by push_cast; ring
        _ ≤ (x:ℝ) := by exact_mod_cast (Nat.sqrt_le' x)
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- assemble
  have hmain : |(MdS m Y) * m - ((Submission.Md m x : ℚ) : ℝ) * m|
      ≤ (Submission.rho 0 m : ℝ) * 4
        + 2 * ∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ) := by
    rw [hS, hN, hsum_eq]
    have hFeq : (Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y)
          + 2 * ∑ c ∈ Finset.Icc 1 K',
              (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
        - (2 * (Nat.sqrt x : ℝ) * (Submission.rho 0 m : ℝ)
          + 2 * ∑ c ∈ Finset.Icc 1 K',
              (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ))
        = (Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y - 2 * (Nat.sqrt x : ℝ))
          + 2 * (∑ c ∈ Finset.Icc 1 K',
              (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
            - ∑ c ∈ Finset.Icc 1 K',
              (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ)) := by
      ring
    rw [hFeq]
    have h2 : |(Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y - 2 * (Nat.sqrt x : ℝ))|
        ≤ (Submission.rho 0 m : ℝ) * 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Submission.rho 0 m : ℝ))]
      exact mul_le_mul_of_nonneg_left hrho0 (by positivity)
    have h3 : |2 * (∑ c ∈ Finset.Icc 1 K',
            (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
          - ∑ c ∈ Finset.Icc 1 K',
            (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ))|
        ≤ 2 * ∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum hterm
    calc |(Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y - 2 * (Nat.sqrt x : ℝ))
            + 2 * (∑ c ∈ Finset.Icc 1 K',
                (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
              - ∑ c ∈ Finset.Icc 1 K',
                (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ))|
        ≤ |(Submission.rho 0 m : ℝ) * (2 * Real.sqrt Y - 2 * (Nat.sqrt x : ℝ))|
          + |2 * (∑ c ∈ Finset.Icc 1 K',
                (Submission.rho (c ^ 2) m : ℝ) * (2 * Real.sqrt (Y - (c : ℝ) ^ 4))
              - ∑ c ∈ Finset.Icc 1 K',
                (Submission.rho (c ^ 2) m : ℝ) * (((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ))| :=
          abs_add_le _ _
      _ ≤ (Submission.rho 0 m : ℝ) * 4
            + 2 * ∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ) := by linarith [h2, h3]
  -- the `ρ`-sum bound
  have hsumrho := Submission.ASP.sum_rho_le m K' hm hcb
  have htau : (2:ℕ) ^ m.primeFactors.card ≤ m.divisors.card :=
    Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
      (d := m) (by omega : 0 < m)
  have hsumrhoR : (∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ))
      ≤ ((m.divisors.card : ℝ)) ^ 2 * ((K : ℝ) + 1) := by
    have h1 : (∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ))
        ≤ ((2:ℕ) ^ m.primeFactors.card : ℝ) * ((K' : ℝ) * (m.divisors.card : ℝ)) := by
      exact_mod_cast hsumrho
    have hK'R : (K' : ℝ) ≤ (K : ℝ) + 1 := by
      exact_mod_cast (le_trans hK'le (Nat.le_succ K))
    have h2 : ((2:ℕ) ^ m.primeFactors.card : ℝ) ≤ (m.divisors.card : ℝ) := by exact_mod_cast htau
    have h3 : (0:ℝ) ≤ (m.divisors.card : ℝ) := by positivity
    calc (∑ c ∈ Finset.Icc 1 K', (Submission.rho (c ^ 2) m : ℝ))
        ≤ ((2:ℕ) ^ m.primeFactors.card : ℝ) * ((K' : ℝ) * (m.divisors.card : ℝ)) := h1
      _ ≤ (m.divisors.card : ℝ) * (((K : ℝ) + 1) * (m.divisors.card : ℝ)) := by
          refine mul_le_mul h2 ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hK'R h3
      _ = ((m.divisors.card : ℝ)) ^ 2 * ((K : ℝ) + 1) := by ring
  have hL : (MdS m Y) * m - ((Submission.Md m x : ℚ) : ℝ) * m
      = ((MdS m Y - ((Submission.Md m x : ℚ) : ℝ))) * m := by ring
  rw [hL, abs_mul, abs_of_pos hm0] at hmain
  rw [le_div_iff₀ hm0]
  rw [hxdef, hKdef]
  linarith [hmain, hsumrhoR]


/-! ## The `4 ∣ d` moduli of `(R₃)` -/

/-- The pair set encoding the moduli `4·(d₁·d₂²)`: squarefree coprime `d₁`, `d₂` with
`4·d₁·d₂² < N`. -/
def CO4 (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (Nat.sqrt N))).filter
    (fun p => Squarefree p.1 ∧ Squarefree p.2 ∧ Nat.Coprime p.1 p.2 ∧
      Odd (p.1 * p.2 ^ 2) ∧ 4 * (p.1 * p.2 ^ 2) < N)

/-- **The `4 ∣ d` moduli are exactly the `4·(d₁d₂²)`.** -/
lemma exists_cube_decomp_of_four_dvd (N d : ℕ) (hdN : d < N) (hd0 : d ≠ 0)
    (hcub : ∀ p ∈ d.primeFactors, d.factorization p ≤ 2) (h4 : 4 ∣ d) :
    ∃ q ∈ CO4 N, d = 4 * (q.1 * q.2 ^ 2) := by
  classical
  obtain ⟨m, hm⟩ := h4
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; omega
  have hcub4 : ∀ p ∈ (4 * m).primeFactors, (4 * m).factorization p ≤ 2 := by
    intro p hp
    have h1 : p ∈ d.primeFactors := by rw [hm]; exact hp
    have h2 := hcub p h1
    rwa [hm] at h2
  have hnot2 : ¬ 2 ∣ m := by
    rintro ⟨k, hk⟩
    have h8 : (2 : ℕ) ^ 3 ∣ 4 * m := ⟨k, by rw [hk]; ring⟩
    exact Submission.X2Y4R3.not_dvd_pow_three_of_cubefreeD (by omega : 4 * m ≠ 0) hcub4 2
      Nat.prime_two h8
  have hcubm : ∀ q ∈ m.primeFactors, m.factorization q ≤ 2 := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ m := (Nat.mem_primeFactors.mp hq).2.1
    have hq2 : q ≠ 2 := fun h => hnot2 (h ▸ hqdvd)
    have hqdfac : (4 : ℕ).factorization q = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      rintro ⟨c, hc⟩
      have hq2sq : q ∣ 2 ^ 2 := ⟨c, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hc⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp (hqprime.dvd_of_dvd_pow hq2sq) with h | h
      · exact hqprime.ne_one h
      · exact hq2 h
    have hmem : q ∈ (4 * m).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hqprime, dvd_trans hqdvd (dvd_mul_left m 4), by omega⟩
    have hfac : (4 * m).factorization q = (4 : ℕ).factorization q + m.factorization q := by
      rw [Nat.factorization_mul (by norm_num : (4:ℕ) ≠ 0) hm0]
      rfl
    have h := hcub4 q hmem
    rw [hfac, hqdfac, zero_add] at h
    exact h
  have hnot4 : ¬ 4 ∣ m := by
    rintro ⟨c, hc⟩
    exact hnot2 ⟨2 * c, by rw [hc]; ring⟩
  obtain ⟨a, b, hsa, hsb, hcop, hab⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.cubefree_decomp (by omega : 0 < m)
      (Submission.X2Y4R3.not_dvd_pow_three_of_cubefreeD hm0 hcubm) hnot4
  have ha1 : 1 ≤ a := hsa.ne_zero.bot_lt
  have hb1 : 1 ≤ b := hsb.ne_zero.bot_lt
  have hmN : m < N := by omega
  have haN : a ≤ N := by
    have h1 : a ≤ a * b ^ 2 := Nat.le_mul_of_pos_right a (pow_pos (by omega : 0 < b) 2)
    omega
  have hbN : b ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt']
    have h1 : b ^ 2 ≤ a * b ^ 2 := Nat.le_mul_of_pos_left _ (by omega : 0 < a)
    omega
  have hlt : 4 * (a * b ^ 2) < N := by omega
  have hnot4ab : ¬ 4 ∣ a * b ^ 2 := by rw [hab]; exact hnot4
  exact ⟨(a, b),
    (by
      rw [CO4, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, hsa, hsb, hcop,
        (Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd, hab]; exact hnot2)), hlt⟩),
    by rw [hm, hab]⟩


/-- The `4 ∣ d` part of `(R₃)` is bounded by `1` plus the pair sum over `CO4 N`. -/
lemma four_dvd_sum_le (N t : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ (Finset.range N).filter
        (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
      |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
    ≤ 1 + ∑ p ∈ CO4 N,
        |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
          - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)| := by
  classical
  set S : Finset ℕ := (Finset.range N).filter
        (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d) with hS
  have h0mem : (0 : ℕ) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (by intro p hp; simp at hp), by norm_num⟩
  have hAd0 : Submission.Ad 0 t = 1 := by
    rw [Submission.Ad]
    have hset : (Finset.range (t + 1)).filter (fun n => 0 ∣ n) = {0} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact Nat.eq_zero_of_zero_dvd h
      · rintro rfl; exact ⟨by omega, dvd_zero 0⟩
    rw [hset, Finset.sum_singleton]
    exact Submission.X2Y4R.an_zero
  have hg0 : (Submission.gdens 0 : ℝ) = 0 := by
    rw [Submission.gdens]; norm_num
  have hF0 : |(Submission.Ad 0 t : ℝ)
      - (Submission.gdens 0 : ℝ) * (Submission.Aseq t : ℝ)| = 1 := by
    rw [hAd0, hg0]; norm_num
  have hinj : ∀ d ∈ S.erase 0, ∃ q ∈ CO4 N, d = 4 * (q.1 * q.2 ^ 2) := by
    intro d hd
    rw [Finset.mem_erase] at hd
    obtain ⟨hdne, hdS⟩ := hd
    rw [hS, Finset.mem_filter, Finset.mem_range] at hdS
    exact exists_cube_decomp_of_four_dvd N d hdS.1 hdne hdS.2.1 hdS.2.2
  choose φ hφ1 hφ2 using hinj
  set ψ : ℕ → ℕ × ℕ := fun d => if h : d ∈ S.erase 0 then φ d h else (0, 0) with hψ
  have hψmem : ∀ d ∈ S.erase 0, ψ d ∈ CO4 N := by
    intro d hd; rw [hψ]; simp only [dif_pos hd]; exact hφ1 d hd
  have hψeq : ∀ d ∈ S.erase 0, d = 4 * ((ψ d).1 * (ψ d).2 ^ 2) := by
    intro d hd; rw [hψ]; simp only [dif_pos hd]; exact hφ2 d hd
  have hψinj : Set.InjOn ψ (↑(S.erase 0) : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hψeq a ha
    have h2 := hψeq b hb
    rw [h1, h2, hab]
  have hsum1 : ∑ d ∈ S.erase 0,
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
      = ∑ q ∈ (S.erase 0).image ψ,
        |(Submission.Ad (4 * (q.1 * q.2 ^ 2)) t : ℝ)
          - (Submission.gdens (4 * (q.1 * q.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)| := by
    rw [Finset.sum_image hψinj]
    refine Finset.sum_congr rfl fun d hd => ?_
    conv_lhs => rw [hψeq d hd]
  have hsum2 : ∑ q ∈ (S.erase 0).image ψ,
        |(Submission.Ad (4 * (q.1 * q.2 ^ 2)) t : ℝ)
          - (Submission.gdens (4 * (q.1 * q.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
      ≤ ∑ p ∈ CO4 N,
        |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
          - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _)
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    exact hψmem d hd
  have hsplit : ∑ d ∈ S,
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
      = |(Submission.Ad 0 t : ℝ) - (Submission.gdens 0 : ℝ) * (Submission.Aseq t : ℝ)|
        + ∑ d ∈ S.erase 0,
          |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)| := by
    exact (Finset.sum_erase_add S
      (fun d => |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      h0mem).symm.trans (add_comm _ _)
  rw [hsplit, hF0]
  linarith [hsum1, hsum2]


lemma CO4_injOn (N : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => 4 * (p.1 * p.2 ^ 2)) (↑(CO4 N) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  simp only [CO4, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
  have h1 : p.1 * p.2 ^ 2 = q.1 * q.2 ^ 2 :=
    Nat.mul_left_cancel (by norm_num : 0 < 4) heq
  exact Prod.ext_iff.mpr
    (Submission.X2Y4R3.mul_sq_inj_cube' hp.2.1 hp.2.2.1 hp.2.2.2.1 hq.2.1 hq.2.2.1
      hq.2.2.2.1 h1)

/-- `CO4 N` is contained in the `cubeCond` pair set of §3 (as a pair set). -/
lemma CO4_subset_cubeCond (N : ℕ) :
    CO4 N ⊆ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (Nat.sqrt N))).filter
      (fun p => Submission.X2Y4R.cubeCond N p.1 p.2) := by
  intro p hp
  rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hsa, hsb, hcop, hodd, hlt⟩ := hp
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨hp1, hp2⟩, hsa, hsb, hcop, ?_, ?_⟩
  · intro h4
    have h2 : ¬ (2:ℕ) ∣ p.1 * p.2 ^ 2 := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hodd
    exact absurd h4 (fun h => h2 ⟨p.2 ^ 2, by omega⟩)
  · omega

lemma sum_Ad_CO4_le (N t : ℕ) :
    (∑ p ∈ CO4 N, (Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 N, (Submission.Ad d t : ℝ) := by
  rw [← Finset.sum_image (f := fun d => (Submission.Ad d t : ℝ)) (CO4_injOn N)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, -, -, -, -, hlt⟩ := hp
  rw [Finset.mem_Icc]
  exact ⟨by
    have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    nlinarith [sq_nonneg (p.2 : ℤ), Nat.one_le_pow 2 p.2 (by omega : 1 ≤ p.2)], by omega⟩

lemma gdens_cast_nonneg (d : ℕ) : (0:ℝ) ≤ (Submission.gdens d : ℝ) :=
  Rat.cast_nonneg.mpr (Submission.X2Y4R.gdens_nonneg d)

lemma sum_gdens_CO4_le (N : ℕ) {Cg Ag : ℝ} (hCg : 0 ≤ Cg)
    (hGg : ∀ y : ℕ, 3 ≤ y →
      Submission.X2Y4R.cubeSum y (fun d₁ d₂ => |(Submission.gdens (d₁ * d₂ ^ 2) : ℝ)|)
        ≤ Cg * (Real.log y) ^ Ag) (hN : 3 ≤ N) :
    (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
      ≤ Cg * (Real.log N) ^ Ag := by
  have habs : ∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)
      = ∑ p ∈ CO4 N, (1/4 : ℝ) * |(Submission.gdens (p.1 * p.2 ^ 2) : ℝ)| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [CO4, Finset.mem_filter] at hp
    obtain ⟨-, -, -, -, hodd, -⟩ := hp
    have h2 : ¬ (2:ℕ) ∣ p.1 * p.2 ^ 2 := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hodd
    rw [Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_mul_four _ h2,
      abs_of_nonneg (gdens_cast_nonneg _)]
  have hsum : ∑ p ∈ CO4 N, |(Submission.gdens (p.1 * p.2 ^ 2) : ℝ)| ≤ Cg * (Real.log N) ^ Ag := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (CO4_subset_cubeCond N)
      (fun i _ _ => abs_nonneg _)) ?_
    rw [Finset.sum_filter, Finset.sum_product]
    simpa only [Submission.X2Y4R.cubeSum] using hGg N (by omega)
  rw [habs, ← Finset.mul_sum, one_div]
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have h0 : (0:ℝ) ≤ Cg * (Real.log N) ^ Ag := mul_nonneg hCg (Real.rpow_nonneg hlogN _)
  have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ (4:ℝ)⁻¹)
  calc (4:ℝ)⁻¹ * ∑ p ∈ CO4 N, |(Submission.gdens (p.1 * p.2 ^ 2) : ℝ)|
      ≤ (4:ℝ)⁻¹ * (Cg * (Real.log N) ^ Ag) := this
    _ ≤ 1 * (Cg * (Real.log N) ^ Ag) :=
        mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ)⁻¹ ≤ 1) h0
    _ = Cg * (Real.log N) ^ Ag := one_mul _

lemma sum_hdens_CO4_le (N : ℕ) {Ch Ah : ℝ}
    (hHh : ∀ y : ℕ, 3 ≤ y →
      Submission.X2Y4R.cubeSum y (fun d₁ d₂ => (Submission.hdens d₁ d₂ : ℝ))
        ≤ Ch * (Real.log y) ^ Ah) (hN : 3 ≤ N) :
    (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ)) ≤ Ch * (Real.log N) ^ Ah := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (CO4_subset_cubeCond N)
    (fun i _ _ => ?_)) ?_
  · have : (0:ℝ) ≤ (Submission.hdens i.1 i.2 : ℝ) := by
      simp only [Submission.hdens]; positivity
    exact this
  · rw [Finset.sum_filter, Finset.sum_product]
    simpa only [Submission.X2Y4R.cubeSum] using hHh N (by omega)

lemma not_prime_cube_dvd_mul_sq {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hcop : Nat.Coprime a b) :
    ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ a * b ^ 2 := by
  intro q hq hdiv
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have hp0 : a * b ^ 2 ≠ 0 := by positivity
  have hfac : (a * b ^ 2).factorization q
      = a.factorization q + 2 * b.factorization q := by
    rw [Nat.factorization_mul ha0 (pow_ne_zero 2 hb0), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have h3 : 3 ≤ (a * b ^ 2).factorization q := (hq.pow_dvd_iff_le_factorization hp0).mp hdiv
  have h1 : a.factorization q ≤ 1 := by
    have := (Nat.squarefree_iff_factorization_le_one ha0).mp ha q
    omega
  have h2 : b.factorization q ≤ 1 := by
    have := (Nat.squarefree_iff_factorization_le_one hb0).mp hb q
    omega
  have hnotboth : a.factorization q = 0 ∨ b.factorization q = 0 := by
    by_contra h
    push Not at h
    have hqa : q ∣ a := by
      by_contra hd
      exact h.1 (Nat.factorization_eq_zero_of_not_dvd hd)
    have hqb : q ∣ b := by
      by_contra hd
      exact h.2 (Nat.factorization_eq_zero_of_not_dvd hd)
    have : q ∣ Nat.gcd a b := Nat.dvd_gcd hqa hqb
    rw [hcop] at this
    exact hq.not_dvd_one this
  rw [hfac] at h3
  omega

lemma cubefree_mul_sq {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hcop : Nat.Coprime a b) :
    ∀ p ∈ (a * b ^ 2).primeFactors, (a * b ^ 2).factorization p ≤ 2 := by
  intro p hp
  have hp0 : a * b ^ 2 ≠ 0 := by
    rw [Nat.mem_primeFactors] at hp
    exact hp.2.2
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  by_contra hcon
  push Not at hcon
  exact not_prime_cube_dvd_mul_sq ha hb hcop p hpp (hpp.pow_dvd_iff_le_factorization hp0 |>.mpr (by omega))


/-- The pointwise decomposition of the `4∣d` summand. -/
lemma CO4_pointwise (p : ℕ × ℕ) (t : ℕ) (hodd : Odd (p.1 * p.2 ^ 2)) :
    |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
    ≤ |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
          - (Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)|
      + |(Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)
          - MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ)|
      + 2 * |MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16)
          - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)|
      + |2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)
          - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)| := by
  have hnot2 : ¬ 2 ∣ p.1 * p.2 ^ 2 := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  have h4 : MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ)
      = 2 * MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16) := MdS_four_mul' _ hnot2 _ (by positivity)
  have h1 := abs_sub_le ((Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ))
    ((Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ))
    ((Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ))
  have h2 := abs_sub_le ((Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ))
    (MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ))
    ((Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ))
  have h5 : |2 * MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16)
      - 2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)|
      = 2 * |MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16)
          - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)| := by
    rw [show 2 * MdS (p.1 * p.2 ^ 2) ((t:ℝ)/16) - 2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)
        = 2 * (MdS (p.1 * p.2 ^ 2) ((t:ℝ)/16) - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h6 := abs_sub_le (2 * MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16))
    (2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ))
    ((Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ))
  have hDB : |MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
      ≤ 2 * |MdS (p.1 * p.2 ^ 2) ((t : ℝ) / 16)
          - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)|
        + |2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t : ℝ) / 16⌋₊ : ℝ)
          - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)| := by
    rw [h4]
    linarith [h6, h5]
  linarith [h1, h2, hDB]


set_option maxHeartbeats 4000000 in
lemma hdens_cast_nonneg (d₁ d₂ : ℕ) : (0:ℝ) ≤ (Submission.hdens d₁ d₂ : ℝ) := by
  simp only [Submission.hdens]
  positivity

lemma CO4_injOn_snd (N : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2 ^ 2) (↑(CO4 N) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  exact CO4_injOn N hp hq (congrArg (fun z => 4 * z) heq)

lemma rho_zero_le_sqrt (m : ℕ) (hm : 1 ≤ m) : Submission.rho 0 m ≤ Nat.sqrt m := by
  rw [Submission.rho_zero_eq m (by omega)]
  exact Nat.le_sqrt'.mpr (Nat.le_of_dvd (by omega) Nat.floorRoot_pow_dvd)

lemma sum_rho_zero_div_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (Submission.rho 0 m : ℝ) / m
      ≤ ∑ m ∈ Finset.Icc 1 N, (Real.sqrt (m:ℝ))⁻¹ := by
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hsq : Real.sqrt (m:ℝ) ≠ 0 := by positivity
  have h1 : ((Submission.rho 0 m : ℕ) : ℝ) ≤ Real.sqrt (m:ℝ) := by
    have := rho_zero_le_sqrt m (by omega)
    calc ((Submission.rho 0 m : ℕ) : ℝ) ≤ ((Nat.sqrt m : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ Real.sqrt (m:ℝ) := by
          rw [Real.le_sqrt (by positivity) (by positivity)]
          exact_mod_cast (Nat.sqrt_le' m)
  have h2 : Real.sqrt (m:ℝ) / (m:ℝ) = (Real.sqrt (m:ℝ))⁻¹ := by
    field_simp
    rw [Real.sq_sqrt hm0.le]
  calc ((Submission.rho 0 m : ℕ) : ℝ) / (m:ℝ)
      = ((Submission.rho 0 m : ℕ) : ℝ) * (1/(m:ℝ)) := by ring
    _ ≤ Real.sqrt (m:ℝ) * (1/(m:ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (Real.sqrt (m:ℝ))⁻¹ := by rw [← div_eq_mul_one_div]; exact h2

lemma CO4_piece_W (N t : ℕ) {Ct Cinv : ℝ} (hCt : 0 < Ct) (hCinv : 0 < Cinv)
    (hTau : ∀ y : ℕ, 1 ≤ y → ∑ d ∈ Finset.Icc 1 y, (d.divisors.card : ℝ)^2 / d
        ≤ Ct * Real.log ((y:ℝ)+2)^4)
    (hInv : ∀ x : ℕ, 1 ≤ x → |(∑ n ∈ Finset.Icc 1 x, (Real.sqrt (n:ℝ))⁻¹) - 2*Real.sqrt x| ≤ Cinv)
    (hN : 2 ≤ N) (ht : 16 ≤ t) :
    (∑ p ∈ CO4 N, 2 * |MdS (p.1 * p.2 ^ 2) ((t:ℝ)/16)
        - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)|)
      ≤ 2 * (4 * (2 * Real.sqrt N + Cinv) + 2 * (((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
          * (Ct * Real.log ((N:ℝ)+2)^4)) := by
  set Y : ℝ := (t:ℝ)/16 with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    have : (16:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    linarith
  set K : ℕ := ⌊Y ^ ((1:ℝ)/4)⌋₊ with hKdef
  have hKY : K = ⌊((t:ℝ)/16) ^ ((1:ℝ)/4)⌋₊ := by rw [hKdef, hYdef]
  have hpt : ∀ p ∈ CO4 N, 2 * |MdS (p.1 * p.2 ^ 2) Y
      - (Submission.Md (p.1 * p.2 ^ 2) ⌊Y⌋₊ : ℝ)|
      ≤ 2 * ((4 * (Submission.rho 0 (p.1 * p.2 ^ 2) : ℝ)
          + 2 * ((p.1 * p.2 ^ 2).divisors.card : ℝ)^2 * ((K:ℝ)+1))
            / ((p.1 * p.2 ^ 2 : ℕ) : ℝ)) := by
    intro p hp
    rw [CO4, Finset.mem_filter] at hp
    obtain ⟨-, hsa, hsb, hcop, -, -⟩ := hp
    have hm1 : 1 ≤ p.1 * p.2 ^ 2 := by
      have h1 : 1 ≤ p.1 := hsa.ne_zero.bot_lt
      have h2 : 1 ≤ p.2 := hsb.ne_zero.bot_lt
      nlinarith [show (1:ℕ) ≤ p.2 ^ 2 by nlinarith]
    have h := MdS_sub_Md_le (p.1 * p.2 ^ 2) hm1
      (not_prime_cube_dvd_mul_sq hsa hsb hcop) Y hY1
    rw [← hKdef] at h
    linarith [h]
  have hext : (∑ p ∈ CO4 N, 2 * ((4 * (Submission.rho 0 (p.1 * p.2 ^ 2) : ℝ)
        + 2 * ((p.1 * p.2 ^ 2).divisors.card : ℝ)^2 * ((K:ℝ)+1))
          / ((p.1 * p.2 ^ 2 : ℕ) : ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 N, 2 * ((4 * (Submission.rho 0 m : ℝ)
        + 2 * (m.divisors.card : ℝ)^2 * ((K:ℝ)+1)) / ((m:ℕ) : ℝ)) := by
    rw [← Finset.sum_image (f := fun m => 2 * ((4 * (Submission.rho 0 m : ℝ)
      + 2 * (m.divisors.card : ℝ)^2 * ((K:ℝ)+1)) / ((m:ℕ) : ℝ))) (CO4_injOn_snd N)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, -, -, -, -, hlt⟩ := hp
    rw [Finset.mem_Icc]
    refine ⟨by
      have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
      have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
      nlinarith [show (1:ℕ) ≤ p.2 ^ 2 by nlinarith], by omega⟩
  have h1 : (∑ m ∈ Finset.Icc 1 N, (Submission.rho 0 m : ℝ) / m) ≤ 2 * Real.sqrt N + Cinv := by
    refine le_trans (sum_rho_zero_div_le N) ?_
    have := (abs_le.mp (hInv N (by omega))).2
    linarith
  have h2 : (∑ m ∈ Finset.Icc 1 N, (m.divisors.card : ℝ)^2 / m)
      ≤ Ct * Real.log ((N:ℝ)+2)^4 := hTau N (by omega)
  have h8 : (∑ m ∈ Finset.Icc 1 N, 2 * ((4 * (Submission.rho 0 m : ℝ)
        + 2 * (m.divisors.card : ℝ)^2 * ((K:ℝ)+1)) / ((m:ℕ) : ℝ)))
      ≤ 8 * (2 * Real.sqrt N + Cinv) + 4 * ((K:ℝ)+1) * (Ct * Real.log ((N:ℝ)+2)^4) := by
    have heq : (∑ m ∈ Finset.Icc 1 N, 2 * ((4 * (Submission.rho 0 m : ℝ)
        + 2 * (m.divisors.card : ℝ)^2 * ((K:ℝ)+1)) / ((m:ℕ) : ℝ)))
        = 8 * (∑ m ∈ Finset.Icc 1 N, (Submission.rho 0 m : ℝ) / m)
          + 4 * ((K:ℝ)+1) * (∑ m ∈ Finset.Icc 1 N, (m.divisors.card : ℝ)^2 / m) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [heq]
    have hK0 : (0:ℝ) ≤ (K:ℝ) + 1 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 4 * ((K:ℝ)+1))
    linarith [h1, h3]
  refine le_trans (le_trans (Finset.sum_le_sum hpt) hext) ?_
  rw [hKY]
  linarith [h8]


lemma rpow34_sub_le_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b < a + 1) :
    b ^ ((3:ℝ)/4) - a ^ ((3:ℝ)/4) ≤ 1 := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have h1 : a + 1 ≤ (a ^ ((3:ℝ)/4) + 1) ^ ((4:ℝ)/3) := by
    have h := Real.add_rpow_le_rpow_add (a := a ^ ((3:ℝ)/4)) (b := 1) (p := (4:ℝ)/3)
      (Real.rpow_nonneg ha0.le ((3:ℝ)/4)) (by norm_num) (by norm_num)
    rw [show (a ^ ((3:ℝ)/4)) ^ ((4:ℝ)/3) = a by rw [← Real.rpow_mul ha0.le]; norm_num,
      show (1:ℝ) ^ ((4:ℝ)/3) = 1 by simp] at h
    linarith
  have h4 : (a+1) ^ ((3:ℝ)/4) ≤ a ^ ((3:ℝ)/4) + 1 := by
    have h5 := Real.rpow_le_rpow (by linarith : (0:ℝ) ≤ a+1) h1
      (by norm_num : (0:ℝ) ≤ (3:ℝ)/4)
    have h6 : (((a ^ ((3:ℝ)/4) + 1) ^ ((4:ℝ)/3)) ^ ((3:ℝ)/4)) = a ^ ((3:ℝ)/4) + 1 := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ a ^ ((3:ℝ)/4) + 1)]
      norm_num
    linarith [h5, h6.le, h6.ge]
  have h3 : b ^ ((3:ℝ)/4) ≤ (a+1) ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow (by linarith) (le_of_lt hb) (by norm_num)
  linarith

/-- The `Md`-to-`gdens·A` part of the `4∣d` sum, bounded by the pair sums. -/
lemma CO4_piece_Z (N t : ℕ) {CM4 Ch Ah Cg Ag CAs κ : ℝ} (M : ℝ)
    (hCM4 : 0 ≤ CM4) (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg) (hCAs : 0 ≤ CAs) (hκ : 0 ≤ κ)
    (hAhM : Ah ≤ M) (hAgM : Ag ≤ M)
    (hM4 : ∀ d₁ d₂ : ℕ, Squarefree d₁ → Squarefree d₂ → Nat.Coprime d₁ d₂ →
      ¬ 4 ∣ d₁ * d₂ ^ 2 → ∀ x : ℕ, 1 ≤ x →
      |(Submission.Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (Submission.gdens (d₁ * d₂ ^ 2) : ℝ)
          * κ * (x : ℝ) ^ ((3:ℝ)/4)| ≤ CM4 * (Submission.hdens d₁ d₂ : ℝ) * Real.sqrt x)
    (hAs : ∀ x : ℕ, 1 ≤ x → |(Submission.Aseq x : ℝ) - 4 * κ * (x:ℝ)^((3:ℝ)/4)|
        ≤ CAs * Real.sqrt x)
    (hHh : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
        (fun a b => (Submission.hdens a b : ℝ)) ≤ Ch * (Real.log y) ^ Ah)
    (hGg : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
        (fun a b => |(Submission.gdens (a * b ^ 2) : ℝ)|) ≤ Cg * (Real.log y) ^ Ag)
    (hN : 3 ≤ N) (ht : 16 ≤ t) :
    (∑ p ∈ CO4 N, |2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (2 * CM4 * Ch + 32 * κ * Cg + CAs * Cg) * (Real.log N)^M * (Real.sqrt t + 1) := by
  set x' : ℕ := ⌊(t:ℝ)/16⌋₊ with hx'def
  have hx'1 : 1 ≤ x' := by
    rw [hx'def]
    refine Nat.le_floor ?_
    have : (16:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    linarith
  have hx'le : (x' : ℝ) ≤ (t:ℝ)/16 := by
    rw [hx'def]; exact Nat.floor_le (by positivity)
  have hx'lt : (t:ℝ)/16 < (x' : ℝ) + 1 := by
    rw [hx'def]; exact Nat.lt_floor_add_one _
  have hlogN1 : (1:ℝ) ≤ Real.log N := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
      rwa [Real.log_exp] at h
    have h4 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h5 := Real.log_le_log (by norm_num) h4
    linarith
  -- pointwise bound
  have hpt : ∀ p ∈ CO4 N, |2 * (Submission.Md (p.1 * p.2 ^ 2) x' : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
      ≤ 2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x'
        + 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)
        + CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t := by
    intro p hp
    rw [CO4, Finset.mem_filter] at hp
    obtain ⟨-, hsa, hsb, hcop, hodd, -⟩ := hp
    have hnot2 : ¬ 2 ∣ p.1 * p.2 ^ 2 := by
      rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd
    have hnot4 : ¬ 4 ∣ p.1 * p.2 ^ 2 := by
      intro h; exact hnot2 ⟨p.2 ^ 2, by omega⟩
    have hgm : (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)
        = (1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) :=
      Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_mul_four _ hnot2
    have hMd := hM4 p.1 p.2 hsa hsb hcop hnot4 x' hx'1
    have hA := hAs t (by omega)
    have hp8 : (8:ℝ) * ((t:ℝ)/16) ^ ((3:ℝ)/4) = (t:ℝ) ^ ((3:ℝ)/4) := by
      rw [show ((t:ℝ)/16) = (t:ℝ)/16 by rfl, Real.div_rpow (by positivity) (by norm_num)]
      rw [show ((16:ℝ)) ^ ((3:ℝ)/4) = 8 by
            rw [show (16:ℝ) = 2^(4:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 4,
              ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
            norm_num]
      ring
    have hdiff := rpow34_sub_le_one (by exact_mod_cast hx'1) hx'le hx'lt
    have hg0 : (0:ℝ) ≤ (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) := gdens_cast_nonneg _
    have hsqrt0 : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg _
    -- assemble
    have hMd2 : |2 * (Submission.Md (p.1 * p.2 ^ 2) x' : ℝ)
        - 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4)|
        ≤ 2 * (CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x') := by
      rw [show 2 * (Submission.Md (p.1 * p.2 ^ 2) x' : ℝ)
          - 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4)
          = 2 * ((Submission.Md (p.1 * p.2 ^ 2) x' : ℝ)
            - 4 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4)) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hMd (by norm_num)
    have hA2 : |8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
        ≤ 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
          + (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (CAs * Real.sqrt t) := by
      rw [hgm]
      have h1 : 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4)
          - (1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * (Submission.Aseq t : ℝ)
          = 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
              * ((x' : ℝ) ^ ((3:ℝ)/4) - ((t:ℝ)/16) ^ ((3:ℝ)/4))
            - (1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ)
              * ((Submission.Aseq t : ℝ) - 4 * κ * (t:ℝ)^((3:ℝ)/4)) := by
        linear_combination ((Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ) * hp8
      rw [h1]
      have habs : |((x' : ℝ) ^ ((3:ℝ)/4) - ((t:ℝ)/16) ^ ((3:ℝ)/4))| ≤ 1 := by
        rw [abs_sub_le_iff]
        constructor
        · have h1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (x':ℝ)) hx'le
            (by norm_num : (0:ℝ) ≤ (3:ℝ)/4)
          have ht0 : (0:ℝ) ≤ ((t:ℝ)/16) ^ ((3:ℝ)/4) := Real.rpow_nonneg (by positivity) _
          linarith
        · exact hdiff
      have hbd : |8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
            * ((x' : ℝ) ^ ((3:ℝ)/4) - ((t:ℝ)/16) ^ ((3:ℝ)/4))|
          ≤ 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ := by
        have h8 : |(8:ℝ)| = 8 := abs_of_nonneg (by norm_num)
        rw [abs_mul, abs_mul, abs_mul, h8, abs_of_nonneg hg0, abs_of_nonneg hκ]
        calc 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
              * |((x' : ℝ) ^ ((3:ℝ)/4) - ((t:ℝ)/16) ^ ((3:ℝ)/4))|
            ≤ 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * 1 :=
              mul_le_mul_of_nonneg_left habs (by positivity)
          _ = 8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ := by ring
      have hbd2 : |(1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ)
            * ((Submission.Aseq t : ℝ) - 4 * κ * (t:ℝ)^((3:ℝ)/4))|
          ≤ (1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * (CAs * Real.sqrt t) := by
        have h4 : |((1:ℝ)/4)| = 1/4 := abs_of_nonneg (by norm_num)
        rw [abs_mul, abs_mul, h4, abs_of_nonneg hg0]
        exact mul_le_mul_of_nonneg_left hA (by positivity)
      have htri := abs_add_le (8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
          * ((x' : ℝ) ^ ((3:ℝ)/4) - ((t:ℝ)/16) ^ ((3:ℝ)/4)))
        (-((1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ)
          * ((Submission.Aseq t : ℝ) - 4 * κ * (t:ℝ)^((3:ℝ)/4))))
      rw [abs_neg, ← sub_eq_add_neg] at htri
      linarith [htri, hbd, hbd2]
    have hAB := abs_sub_le (2 * (Submission.Md (p.1 * p.2 ^ 2) x' : ℝ))
      (8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ * (x' : ℝ) ^ ((3:ℝ)/4))
      ((Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ))
    have hfin : 2 * (CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x')
          + (8 * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ) * κ
            + (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (CAs * Real.sqrt t))
        ≤ 2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x'
          + 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)
          + CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t := by
      have hg4 : (1/4 : ℝ) * (Submission.gdens (p.1 * p.2 ^ 2) : ℝ)
          = (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) := by rw [hgm]
      have hg40 : (0:ℝ) ≤ (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) := gdens_cast_nonneg _
      have hk0 : (0:ℝ) ≤ κ := hκ
      have hs0 : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
      have hCA0 : (0:ℝ) ≤ CAs * Real.sqrt t := mul_nonneg hCAs hs0
      nlinarith [hg4, hg40, hk0, hs0, hCA0]
    linarith [hAB, hMd2, hA2, hfin]
  -- sums
  have hsumH : (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ)) ≤ Ch * (Real.log N) ^ Ah :=
    sum_hdens_CO4_le N hHh (by omega)
  have hsumG : (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
      ≤ Cg * (Real.log N) ^ Ag := sum_gdens_CO4_le N hCg hGg (by omega)
  have hH0 : (0:ℝ) ≤ (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ)) :=
    Finset.sum_nonneg fun i _ => hdens_cast_nonneg i.1 i.2
  have hG0 : (0:ℝ) ≤ (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) :=
    Finset.sum_nonneg fun i _ => gdens_cast_nonneg _
  set A : ℝ := 2 * CM4 * Ch + 32 * κ * Cg + CAs * Cg with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have hl : (0:ℝ) ≤ (Real.log N)^Ah := Real.rpow_nonneg (by linarith) _
    have hl2 : (0:ℝ) ≤ (Real.log N)^Ag := Real.rpow_nonneg (by linarith) _
    have h1 : (0:ℝ) ≤ 2 * CM4 * Ch := by positivity
    have h2 : (0:ℝ) ≤ 32 * κ * Cg := by positivity
    have h3 : (0:ℝ) ≤ CAs * Cg := by positivity
    linarith
  have hb1 : (∑ p ∈ CO4 N, 2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x')
      ≤ 2 * CM4 * (Ch * (Real.log N) ^ Ah) * Real.sqrt t := by
    have hfac : (∑ p ∈ CO4 N, 2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x')
        = (2 * CM4 * Real.sqrt x') * (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hfac]
    have hx't : Real.sqrt x' ≤ Real.sqrt t := Real.sqrt_le_sqrt (by
      have : (16:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
      show (x':ℝ) ≤ (t:ℝ)
      linarith [hx'le])
    have h1 : (2 * CM4 * Real.sqrt x') * (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ))
        ≤ (2 * CM4 * Real.sqrt x') * (Ch * (Real.log N) ^ Ah) :=
      mul_le_mul_of_nonneg_left hsumH (by positivity)
    have h2 : (2 * CM4 * Real.sqrt x') * (Ch * (Real.log N) ^ Ah)
        ≤ (2 * CM4 * Real.sqrt t) * (Ch * (Real.log N) ^ Ah) := by
      have h3 : 2 * CM4 * Real.sqrt x' ≤ 2 * CM4 * Real.sqrt t := by
        calc 2 * CM4 * Real.sqrt x' = (2 * CM4) * Real.sqrt x' := by ring
          _ ≤ (2 * CM4) * Real.sqrt t := mul_le_mul_of_nonneg_left hx't (by positivity)
          _ = 2 * CM4 * Real.sqrt t := by ring
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    calc (2 * CM4 * Real.sqrt x') * (∑ p ∈ CO4 N, (Submission.hdens p.1 p.2 : ℝ))
        ≤ (2 * CM4 * Real.sqrt x') * (Ch * (Real.log N) ^ Ah) := h1
      _ ≤ (2 * CM4 * Real.sqrt t) * (Ch * (Real.log N) ^ Ah) := h2
      _ = 2 * CM4 * (Ch * (Real.log N) ^ Ah) * Real.sqrt t := by ring
  have hb2 : (∑ p ∈ CO4 N, 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
      ≤ 32 * κ * (Cg * (Real.log N) ^ Ag) := by
    have hfac : (∑ p ∈ CO4 N, 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
        = (32 * κ) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) := by
      rw [Finset.mul_sum]
    calc (∑ p ∈ CO4 N, 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
        = (32 * κ) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) := hfac
      _ ≤ (32 * κ) * (Cg * (Real.log N) ^ Ag) :=
          mul_le_mul_of_nonneg_left hsumG (by linarith [hκ])
  have hb3 : (∑ p ∈ CO4 N, CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t)
      ≤ CAs * (Cg * (Real.log N) ^ Ag) * Real.sqrt t := by
    have hfac : (∑ p ∈ CO4 N, CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t)
        = (CAs * Real.sqrt t) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hfac]
    have h1 : (CAs * Real.sqrt t) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
        ≤ (CAs * Real.sqrt t) * (Cg * (Real.log N) ^ Ag) :=
      mul_le_mul_of_nonneg_left hsumG (by positivity)
    calc (CAs * Real.sqrt t) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
        ≤ (CAs * Real.sqrt t) * (Cg * (Real.log N) ^ Ag) := h1
      _ = CAs * (Cg * (Real.log N) ^ Ag) * Real.sqrt t := by ring
  have hlogAh : (Real.log N) ^ Ah ≤ (Real.log N) ^ M :=
    Real.rpow_le_rpow_of_exponent_le hlogN1 hAhM
  have hlogAg : (Real.log N) ^ Ag ≤ (Real.log N) ^ M :=
    Real.rpow_le_rpow_of_exponent_le hlogN1 hAgM
  have hlogM0 : (0:ℝ) ≤ (Real.log N) ^ M := Real.rpow_nonneg (by linarith) _
  have htarget : 2 * CM4 * (Ch * (Real.log N) ^ Ah) * Real.sqrt t
        + 32 * κ * (Cg * (Real.log N) ^ Ag)
        + CAs * (Cg * (Real.log N) ^ Ag) * Real.sqrt t
      ≤ A * (Real.log N)^M * (Real.sqrt t + 1) := by
    rw [hAdef]
    have hst0 : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hst1 : (1:ℝ) ≤ Real.sqrt t + 1 := by linarith
    have e1 : 2 * CM4 * (Ch * (Real.log N)^Ah) * Real.sqrt t
        ≤ (2 * CM4 * Ch) * (Real.log N)^M * (Real.sqrt t + 1) := by
      have h3 : Ch * (Real.log N)^Ah ≤ Ch * (Real.log N)^M := mul_le_mul_of_nonneg_left hlogAh hCh
      have h4 : 2 * CM4 * (Ch * (Real.log N)^Ah) ≤ 2 * CM4 * (Ch * (Real.log N)^M) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      calc 2 * CM4 * (Ch * (Real.log N)^Ah) * Real.sqrt t
          ≤ (2 * CM4 * (Ch * (Real.log N)^M)) * Real.sqrt t := mul_le_mul_of_nonneg_right h4 hst0
        _ ≤ (2 * CM4 * (Ch * (Real.log N)^M)) * (Real.sqrt t + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (2 * CM4 * Ch) * (Real.log N)^M * (Real.sqrt t + 1) := by ring
    have e2 : 32 * κ * (Cg * (Real.log N)^Ag)
        ≤ (32 * κ * Cg) * (Real.log N)^M * (Real.sqrt t + 1) := by
      have h3 : Cg * (Real.log N)^Ag ≤ Cg * (Real.log N)^M := mul_le_mul_of_nonneg_left hlogAg hCg
      have h4 : 32 * κ * (Cg * (Real.log N)^Ag) ≤ 32 * κ * (Cg * (Real.log N)^M) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : 32 * κ * (Cg * (Real.log N)^M) * 1
          ≤ 32 * κ * (Cg * (Real.log N)^M) * (Real.sqrt t + 1) :=
        mul_le_mul_of_nonneg_left hst1 (by positivity)
      calc 32 * κ * (Cg * (Real.log N)^Ag) ≤ 32 * κ * (Cg * (Real.log N)^M) := h4
        _ ≤ 32 * κ * (Cg * (Real.log N)^M) * (Real.sqrt t + 1) := by linarith [h5]
        _ = (32 * κ * Cg) * (Real.log N)^M * (Real.sqrt t + 1) := by ring
    have e3 : CAs * (Cg * (Real.log N)^Ag) * Real.sqrt t
        ≤ (CAs * Cg) * (Real.log N)^M * (Real.sqrt t + 1) := by
      have h3 : Cg * (Real.log N)^Ag ≤ Cg * (Real.log N)^M := mul_le_mul_of_nonneg_left hlogAg hCg
      have h4 : CAs * (Cg * (Real.log N)^Ag) ≤ CAs * (Cg * (Real.log N)^M) :=
        mul_le_mul_of_nonneg_left h3 hCAs
      calc CAs * (Cg * (Real.log N)^Ag) * Real.sqrt t
          ≤ (CAs * (Cg * (Real.log N)^M)) * Real.sqrt t := mul_le_mul_of_nonneg_right h4 hst0
        _ ≤ (CAs * (Cg * (Real.log N)^M)) * (Real.sqrt t + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (CAs * Cg) * (Real.log N)^M * (Real.sqrt t + 1) := by ring
    linarith [e1, e2, e3]
  calc (∑ p ∈ CO4 N, |2 * (Submission.Md (p.1 * p.2 ^ 2) x' : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ ∑ p ∈ CO4 N, (2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x'
          + 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)
          + CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t) :=
        Finset.sum_le_sum hpt
    _ = (∑ p ∈ CO4 N, 2 * CM4 * (Submission.hdens p.1 p.2 : ℝ) * Real.sqrt x')
        + (∑ p ∈ CO4 N, 32 * κ * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
        + (∑ p ∈ CO4 N, CAs * (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * Real.sqrt t) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 2 * CM4 * (Ch * (Real.log N) ^ Ah) * Real.sqrt t
        + 32 * κ * (Cg * (Real.log N) ^ Ag)
        + CAs * (Cg * (Real.log N) ^ Ag) * Real.sqrt t := add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ A * (Real.log N)^M * (Real.sqrt t + 1) := htarget


lemma CO4_subset_Icc_image (N t : ℕ) :
    (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)|)
      ≤ ∑ d ∈ Finset.Icc 1 N, |(Submission.Ad d t : ℝ) - (Submission.Md d t : ℝ)| := by
  rw [← Finset.sum_image (f := fun d => |(Submission.Ad d t : ℝ) - (Submission.Md d t : ℝ)|)
    (CO4_injOn N)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _)
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, -, -, -, -, hlt⟩ := hp
  rw [Finset.mem_Icc]
  exact ⟨by
    have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    nlinarith [show (1:ℕ) ≤ p.2 ^ 2 by nlinarith], by omega⟩

lemma CO4_bound_fine (N t : ℕ) (hN : 3 ≤ N) (ht : 16 ≤ t)
    (hNt : N ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊)
    {CAd CMd CM4 Ch Ah Cg Ag Cinv Ct CAs κ M : ℝ}
    (hCAd : 0 < CAd) (hCMd : 0 < CMd)
    (hAd : ∀ x D : ℕ, 1 ≤ x → 1 ≤ D → D ≤ ⌊(x : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      ∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d x : ℝ) - (Submission.Md d x : ℝ)|
        ≤ CAd * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
    (hMd : ∀ x D : ℕ, 1 ≤ x → 1 ≤ D →
      ∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
          - ∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
              (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ),
            ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
              2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ)|
        ≤ CMd * (x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (D : ℝ) + 2)) ^ 6)
    (hM4 : ∀ d₁ d₂ : ℕ, Squarefree d₁ → Squarefree d₂ → Nat.Coprime d₁ d₂ →
      ¬ 4 ∣ d₁ * d₂ ^ 2 → ∀ x : ℕ, 1 ≤ x →
      |(Submission.Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (Submission.gdens (d₁ * d₂ ^ 2) : ℝ)
          * κ * (x : ℝ) ^ ((3:ℝ)/4)| ≤ CM4 * (Submission.hdens d₁ d₂ : ℝ) * Real.sqrt x)
    (hAs : ∀ x : ℕ, 1 ≤ x → |(Submission.Aseq x : ℝ) - 4 * κ * (x:ℝ)^((3:ℝ)/4)|
        ≤ CAs * Real.sqrt x)
    (hHh : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
        (fun a b => (Submission.hdens a b : ℝ)) ≤ Ch * (Real.log y) ^ Ah)
    (hGg : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
        (fun a b => |(Submission.gdens (a * b ^ 2) : ℝ)|) ≤ Cg * (Real.log y) ^ Ag)
    (hInv : ∀ x : ℕ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 x, (Real.sqrt (n:ℝ))⁻¹) - 2*Real.sqrt x| ≤ Cinv)
    (hTau : ∀ y : ℕ, 1 ≤ y → ∑ d ∈ Finset.Icc 1 y, (d.divisors.card : ℝ)^2 / d
        ≤ Ct * Real.log ((y:ℝ)+2)^4)
    (hCM4 : 0 ≤ CM4) (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg) (hCAs : 0 ≤ CAs) (hκ : 0 ≤ κ)
    (hCt : 0 < Ct) (hCinv : 0 < Cinv)
    (hAhM : Ah ≤ M) (hAgM : Ag ≤ M) :
    (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ CAd * (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        + CMd * (t : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (N : ℝ) + 2)) ^ 6
        + 2 * (4 * (2 * Real.sqrt N + Cinv)
            + 2 * (((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
              * (Ct * Real.log ((N : ℝ) + 2) ^ 4))
        + (2 * CM4 * Ch + 32 * κ * Cg + CAs * Cg) * (Real.log (N : ℝ)) ^ M
            * (Real.sqrt t + 1) := by
  have hU : (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)|)
      ≤ CAd * (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
    le_trans (CO4_subset_Icc_image N t) (hAd t N (by omega) (by omega) hNt)
  have hV : (∑ p ∈ CO4 N, |(Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ)|)
      ≤ CMd * (t : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (N : ℝ) + 2)) ^ 6 := by
    refine le_trans ?_ (hMd t N (by omega) (by omega))
    rw [← Finset.sum_image (f := fun d => |(Submission.Md d t : ℝ) - MdS d (t : ℝ)|)
      (CO4_injOn N)]
    have hconv : (∑ d ∈ (CO4 N).image (fun p : ℕ × ℕ => 4 * (p.1 * p.2 ^ 2)),
            |(Submission.Md d t : ℝ) - MdS d (t : ℝ)|)
        = ∑ d ∈ (CO4 N).image (fun p : ℕ × ℕ => 4 * (p.1 * p.2 ^ 2)),
            |(Submission.Md d t : ℝ)
              - ∑ c ∈ Finset.Icc (-(⌊(t : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
                  (⌊(t : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ),
                ∑ β ∈ (Finset.range d).filter
                  (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                  2 * Real.sqrt ((t : ℝ) - (c : ℝ) ^ 4) / (d : ℝ)| := by
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
      rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, -, -, -, -, hlt⟩ := hp
      have hd1 : 1 ≤ 4 * (p.1 * p.2 ^ 2) := by
        have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
        have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
        nlinarith [show (1:ℕ) ≤ p.2 ^ 2 by nlinarith]
      haveI : NeZero (4 * (p.1 * p.2 ^ 2)) := ⟨by omega⟩
      rw [MdS_eq_commons _ t]
    rw [hconv]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _)
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    rw [CO4, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, -, -, -, -, hlt⟩ := hp
    rw [Finset.mem_Icc]
    exact ⟨by
      have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
      have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
      nlinarith [show (1:ℕ) ≤ p.2 ^ 2 by nlinarith], by omega⟩
  have hW := CO4_piece_W N t hCt hCinv hTau hInv (by omega) ht
  have hZ := CO4_piece_Z N t M hCM4 hCh hCg hCAs hκ hAhM hAgM hM4 hAs hHh hGg hN ht
  have hpt : (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
            - (Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)|)
        + (∑ p ∈ CO4 N, |(Submission.Md (4 * (p.1 * p.2 ^ 2)) t : ℝ)
            - MdS (4 * (p.1 * p.2 ^ 2)) (t : ℝ)|)
        + (∑ p ∈ CO4 N, 2 * |MdS (p.1 * p.2 ^ 2) ((t:ℝ)/16)
            - (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)|)
        + (∑ p ∈ CO4 N, |2 * (Submission.Md (p.1 * p.2 ^ 2) ⌊(t:ℝ)/16⌋₊ : ℝ)
            - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [CO4, Finset.mem_filter] at hp
    exact CO4_pointwise p t hp.2.2.2.2.1
  refine le_trans hpt ?_
  linarith [hU, hV, hW, hZ]


lemma CO4_bound_crude (N t : ℕ) (hN : 3 ≤ N)
    {CAd2 CAu Cg Ag : ℝ} (hCAd2 : 0 ≤ CAd2) (hCAu : 0 ≤ CAu) (hCg : 0 ≤ Cg)
    (hAd2 : ∀ D x : ℕ, (∑ d ∈ Finset.Icc 1 D, (Submission.Ad d x : ℝ))
        ≤ (D:ℝ) + CAd2 * (x:ℝ)^((1:ℝ)/100) * (Submission.Aseq x : ℝ))
    (hAu : ∀ x : ℕ, 1 ≤ x → (Submission.Aseq x : ℝ) ≤ CAu * (x:ℝ)^((3:ℝ)/4))
    (hGg : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
        (fun a b => |(Submission.gdens (a * b ^ 2) : ℝ)|) ≤ Cg * (Real.log y) ^ Ag)
    (ht2 : 2 ≤ t) (htN : (t:ℝ)^((3:ℝ)/4) ≤ 2 * (N:ℝ)) :
    (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (N:ℝ) + 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
        + 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag := by
  have hAu' : (Submission.Aseq t : ℝ) ≤ CAu * (2 * (N:ℝ)) := by
    refine le_trans (hAu t (by omega)) ?_
    exact mul_le_mul_of_nonneg_left (by linarith [htN]) hCAu
  have hpt : ∀ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|
      ≤ (Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        + (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ) := by
    intro p _
    have hA0 : (0:ℝ) ≤ (Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ) := by positivity
    have hB0 : (0:ℝ) ≤ (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ) :=
      mul_nonneg (gdens_cast_nonneg _) (by positivity)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h1 : (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (∑ d ∈ Finset.Icc 1 N, (Submission.Ad d t : ℝ))
        + (Submission.Aseq t : ℝ) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) := by
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    refine add_le_add (sum_Ad_CO4_le N t) ?_
    exact le_of_eq (Finset.sum_congr rfl fun p _ => by ring)
  have h2 := hAd2 N t
  have h3 : (Submission.Aseq t : ℝ) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ))
      ≤ CAu * (2 * (N:ℝ)) * (Cg * (Real.log N) ^ Ag) := by
    refine mul_le_mul hAu' (sum_gdens_CO4_le N hCg hGg (by omega)) ?_ ?_
    · exact Finset.sum_nonneg fun i _ => gdens_cast_nonneg _
    · exact mul_nonneg hCAu (by positivity)
  have h4 : (∑ d ∈ Finset.Icc 1 N, (Submission.Ad d t : ℝ))
      ≤ (N:ℝ) + CAd2 * (t:ℝ)^((1:ℝ)/100) * (CAu * (2 * (N:ℝ))) := by
    refine le_trans h2 ?_
    have hA0 := hAu'
    have hx0 : (0:ℝ) ≤ CAd2 * (t:ℝ)^((1:ℝ)/100) :=
      mul_nonneg hCAd2 (Real.rpow_nonneg (by positivity) _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hA0 hx0)
  calc (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (∑ d ∈ Finset.Icc 1 N, (Submission.Ad d t : ℝ))
        + (Submission.Aseq t : ℝ) * (∑ p ∈ CO4 N, (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ)) := h1
    _ ≤ ((N:ℝ) + CAd2 * (t:ℝ)^((1:ℝ)/100) * (CAu * (2 * (N:ℝ))))
        + CAu * (2 * (N:ℝ)) * (Cg * (Real.log N) ^ Ag) := add_le_add h4 h3
    _ = (N:ℝ) + 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
        + 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag := by ring



end

end Submission.ASP
