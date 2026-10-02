
/-
The sharp asymptotic for the coprime Mertens-type sum
`Θ(Q,r) = Σ_{(m,r)=1, m ≤ Q} μ(m) log(Q/m)/m` (Graham's Lemma 10, the input to the
Barban–Vehov estimate in the Density4 area of Linnik's theorem).

Organisation:
* `sHalf r = σ_{-1/2}(r) = Σ_{d | r} d^{-1/2}`,
  `Tsel r Q = r/φ(r) - Θ(Q,r)`,
  `Lpow Q = (log (2+Q))^{-3}`;
* the recursion `Tsel r Q = Σ_{d | r} (μ(d)²/d) Tsel d (Q/d)` (proved in `selTheta_recursion`),
  together with the divisor identity `Σ_{d | r} μ(d)²/φ(d) = r/φ(r)`;
* a strong induction on `⌈Q⌉₊`, uniformly in `r`, splitting the recursion sum at
  `X = Q^{1/100}`:
  - `d = 1`: the base case `|Tsel 1 Q| ≤ c₁ (log(2+Q))^{-3}` (`selU_sub_one_bound`);
  - `2 ≤ d ≤ X`: induction hypothesis, plus `log(2+Q/d) ≥ (99/100) log(2+Q)` (`log_ratio`),
    and the bookkeeping estimate `Σ_{2 ≤ d | r} μ(d)²σ_{-1/2}(d)/d ≤ (9/10)σ_{-1/2}(r)`
    (`diag_weighted_sum_le_alt`);
  - `d > X`: the trivial bound `|Tsel d y| ≤ d/φ(d) + log(2+y)(1+log(2+y))` together with
    `Σ_{d | r, d > X} μ(d)²/d ≤ σ_{-1/2}(r)/√X`, `Σ_{d | r, d > X} μ(d)²/φ(d) ≤ 1000σ_{-1/2}(r)/√X`
    (`divisorTail_bounds`) and the uniform boundedness of
    `Q^{-1/200}(1000+LY)(log(2+Q))^3` (`window_log_bound`).
-/
import Mathlib
import Submission.Commons.NumberTheory.Totient.sum_divisors_mu_sq_div_totient
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one
import Submission.Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds
import Submission.Work.LinnikAreas.Density4.selTheta_recursion
import Submission.Work.LinnikAreas.Density4.divisorTail_bounds
import Submission.Work.LinnikAreas.Density4.diag_weighted_sum_le_alt
import Submission.Work.LinnikAreas.Density4.sHalf_facts
import Submission.Work.LinnikAreas.Density4.selU_sub_one_bound
import Submission.Work.LinnikAreas.Density4.window_log_bound

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-- `σ_{-1/2}(r) = Σ_{d | r} d^{-1/2}`. -/
def sHalf (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)

/-- `T_r(Q) = r/φ(r) - Θ(Q,r)`. -/
def Tsel (r : ℕ) (Q : ℝ) : ℝ := (r:ℝ)/(Nat.totient r : ℝ) - selTheta Q r

/-- `L(Q) = (log (2+Q))^{-3}`, the decay factor of the error term. -/
def Lpow (Q : ℝ) : ℝ := (Real.log (2 + Q)) ^ (-3 : ℤ)

lemma Lpow_nonneg {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ Lpow Q := by
  rw [Lpow]
  exact zpow_nonneg (Real.log_nonneg (by linarith)) _

lemma sHalf_nonneg (r : ℕ) : 0 ≤ sHalf r := by
  rw [sHalf]
  apply Finset.sum_nonneg
  intro d _
  positivity

lemma sHalf_one : sHalf 1 = 1 := by simp [sHalf]

lemma sHalf_ge_one {r : ℕ} (hr : 1 ≤ r) : 1 ≤ sHalf r := by
  have h1 : (1:ℕ) ∈ r.divisors := Nat.one_mem_divisors.mpr (by omega)
  rw [sHalf]
  have h := Finset.single_le_sum (f := fun d : ℕ => (1:ℝ)/Real.sqrt (d:ℝ))
    (fun d hd => by
      have hpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      positivity) h1
  simpa using h

lemma selTheta_eq_zero_of_lt_one {y : ℝ} (hy : y < 1) (k : ℕ) : selTheta y k = 0 := by
  simp [selTheta, Nat.floor_eq_zero.mpr hy]

lemma Tsel_of_lt_one {y : ℝ} (hy : y < 1) (d : ℕ) :
    Tsel d y = (d:ℝ)/(Nat.totient d : ℝ) := by
  rw [Tsel, selTheta_eq_zero_of_lt_one hy d, sub_zero]

/-- Crude bound for `Θ`: with `⌊y⌋₊ = N`, every term is at most
`log(2+y)/m` and `Σ_{m ≤ N} 1/m ≤ 1 + log N ≤ 1 + log(2+y)`. -/
lemma selTheta_abs_le {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    |selTheta y k| ≤ Real.log (2+y) * (1 + Real.log (2+y)) := by
  have hlog : 0 ≤ Real.log (2+y) := Real.log_nonneg (by linarith)
  set N := ⌊y⌋₊ with hN
  have hterm : ∀ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m k),
      |((ArithmeticFunction.moebius m : ℝ)) * Real.log (y/(m:ℝ)) / (m:ℝ)|
        ≤ Real.log (2+y) * (1/(m:ℝ)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmN⟩, _⟩ := hm
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hmlog : |Real.log (y/(m:ℝ))| ≤ Real.log (2+y) := by
      have hmley : (m:ℝ) ≤ y := by
        calc (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hmN
          _ ≤ y := by rw [hN]; exact Nat.floor_le hy
      have hypos : 0 < y := lt_of_lt_of_le hmpos hmley
      have hnn : 0 ≤ Real.log (y/(m:ℝ)) :=
        Real.log_nonneg (by rw [le_div_iff₀ hmpos]; linarith)
      have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      rw [abs_of_nonneg hnn]
      apply Real.log_le_log (div_pos hypos hmpos)
      rw [div_le_iff₀ hmpos]
      nlinarith [hm1']
    have hmu : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 :=
      Commons.NumberTheory.Moebius.moebius_abs_le_one m
    rw [abs_div, abs_mul, abs_of_nonneg hmpos.le]
    have hstep : |(ArithmeticFunction.moebius m : ℝ)| * |Real.log (y/(m:ℝ))| / (m:ℝ)
        ≤ 1 * Real.log (2+y) / (m:ℝ) := by
      apply div_le_div_of_nonneg_right _ hmpos.le
      exact mul_le_mul hmu hmlog (abs_nonneg _) (by norm_num)
    calc |(ArithmeticFunction.moebius m : ℝ)| * |Real.log (y/(m:ℝ))| / (m:ℝ)
        ≤ 1 * Real.log (2+y) / (m:ℝ) := hstep
      _ = Real.log (2+y) * (1/(m:ℝ)) := by ring
  rw [selTheta, ← hN]
  calc |∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m k),
        (ArithmeticFunction.moebius m : ℝ) * Real.log (y/(m:ℝ)) / (m:ℝ)|
      ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m k),
          |(ArithmeticFunction.moebius m : ℝ) * Real.log (y/(m:ℝ)) / (m:ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m k),
          Real.log (2+y) * (1/(m:ℝ)) := Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (2+y) * (1/(m:ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro m hm _
        have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        positivity
    _ = Real.log (2+y) * ∑ m ∈ Finset.Icc 1 N, 1/(m:ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.log (2+y) * (1 + Real.log (2+y)) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · rw [hN0]
          have hemp : Finset.Icc 1 (0:ℕ) = ∅ := by simp
          rw [hemp, Finset.sum_empty]
          linarith [hlog]
        · have hb := (Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds).2.1 N hNpos
          have hlogN : Real.log (N:ℝ) ≤ Real.log (2+y) := by
            apply Real.log_le_log (by exact_mod_cast hNpos)
            have : (N:ℝ) ≤ y := by rw [hN]; exact Nat.floor_le hy
            linarith
          linarith

lemma Tsel_abs_le {y : ℝ} (hy : 0 ≤ y) {d : ℕ} (hd : 1 ≤ d) :
    |Tsel d y| ≤ (d:ℝ)/(Nat.totient d : ℝ) + Real.log (2+y) * (1 + Real.log (2+y)) := by
  have hφpos : (0:ℝ) ≤ (d:ℝ)/(Nat.totient d : ℝ) := by
    have : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    positivity
  rw [Tsel, sub_eq_add_neg]
  calc |(d:ℝ)/(Nat.totient d : ℝ) + -(selTheta y d)|
      ≤ |(d:ℝ)/(Nat.totient d : ℝ)| + |-(selTheta y d)| := abs_add_le _ _
    _ = (d:ℝ)/(Nat.totient d : ℝ) + |selTheta y d| := by rw [abs_of_nonneg hφpos, abs_neg]
    _ ≤ (d:ℝ)/(Nat.totient d : ℝ) + Real.log (2+y) * (1 + Real.log (2+y)) := by
        linarith [selTheta_abs_le hy d]

lemma selTheta_one_eq_selU (y : ℝ) : selTheta y 1 = selU y := by
  rw [selTheta, selU, Finset.filter_true_of_mem]
  intro m _
  exact Nat.coprime_one_right m

lemma Tsel_recursion (Q : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    Tsel r Q = ∑ d ∈ r.divisors,
      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ)) := by
  have hsum := Commons.NumberTheory.Totient.sum_divisors_mu_sq_div_totient r hr
  have hstep : ∀ d ∈ r.divisors,
      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
        ((d:ℝ)/(Nat.totient d : ℝ) - selTheta (Q/(d:ℝ)) d)
      = ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
        - ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * selTheta (Q/(d:ℝ)) d := by
    intro d hd
    have hd0 : (d:ℝ) ≠ 0 := by
      have : 0 < d := Nat.pos_of_mem_divisors hd
      exact_mod_cast this.ne'
    have hφ0 : (Nat.totient d : ℝ) ≠ 0 := by
      have : 0 < Nat.totient d := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd)
      exact_mod_cast this.ne'
    field_simp
  have hmain : (∑ d ∈ r.divisors,
      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ)))
      = (∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
        - (∑ d ∈ r.divisors,
            ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * selTheta (Q/(d:ℝ)) d) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Tsel]
    exact hstep d hd
  rw [hmain, hsum, Tsel, selTheta_recursion Q r hr]

lemma Tsel_one_bound : ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q →
    |Tsel 1 Q| ≤ c * Lpow Q := by
  obtain ⟨c, hc, hb⟩ := selU_sub_one_bound
  refine ⟨c, hc, ?_⟩
  intro Q hQ
  have heq : Tsel 1 Q = 1 - selU Q := by
    rw [Tsel, Nat.totient_one, Nat.cast_one, div_one, selTheta_one_eq_selU]
  rw [heq, abs_sub_comm]
  simpa [Lpow] using hb Q hQ

/-- For `d ≤ Q^{1/100}` one has `log(2+Q/d) ≥ (99/100) log(2+Q)`. -/
lemma log_ratio {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd : 1 ≤ d)
    (hdQ : (d:ℝ) ≤ Q ^ ((1:ℝ)/100)) :
    (99/100) * Real.log (2 + Q) ≤ Real.log (2 + Q/(d:ℝ)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hq99 : (0:ℝ) < Q ^ ((99:ℝ)/100) := Real.rpow_pos_of_pos hQ0 _
  have hdiv : Q ^ ((99:ℝ)/100) ≤ Q/(d:ℝ) := by
    rw [le_div_iff₀ hd0]
    calc Q ^ ((99:ℝ)/100) * (d:ℝ) ≤ Q ^ ((99:ℝ)/100) * Q ^ ((1:ℝ)/100) :=
          mul_le_mul_of_nonneg_left hdQ hq99.le
      _ = Q ^ ((99:ℝ)/100 + (1:ℝ)/100) := by rw [← Real.rpow_add hQ0]
      _ = Q ^ (1:ℝ) := by norm_num
      _ = Q := Real.rpow_one Q
  have hsub : (2 + Q) ^ ((99:ℝ)/100) ≤ 2 + Q ^ ((99:ℝ)/100) := by
    have h := Real.rpow_add_le_add_rpow (p := (99:ℝ)/100) (a := 2) (b := Q)
      (by norm_num) hQ0.le (by norm_num) (by norm_num)
    have h2 : (2:ℝ) ^ ((99:ℝ)/100) ≤ 2 := by
      calc (2:ℝ) ^ ((99:ℝ)/100) ≤ (2:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    linarith
  have hlogeq : (99/100) * Real.log (2+Q) = Real.log ((2+Q) ^ ((99:ℝ)/100)) := by
    rw [Real.log_rpow (by linarith)]
  rw [hlogeq]
  calc Real.log ((2+Q) ^ ((99:ℝ)/100)) ≤ Real.log (2 + Q ^ ((99:ℝ)/100)) :=
        Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hsub
    _ ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_le_log (by linarith) (by linarith)

lemma one_le_div_of_le_rpow {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd : 1 ≤ d)
    (hdQ : (d:ℝ) ≤ Q ^ ((1:ℝ)/100)) : 1 ≤ Q/(d:ℝ) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hd0]
  calc (1:ℝ) * (d:ℝ) = (d:ℝ) := one_mul _
    _ ≤ Q ^ ((1:ℝ)/100) := hdQ
    _ ≤ Q ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
    _ = Q := Real.rpow_one Q

/-- The `d > Q^{1/100}` part of the recursion, bounded with the trivial estimate for `T_d`. -/
lemma window_part_bound {Q : ℝ} (hQ : 1 ≤ Q) {r : ℕ} (hr : 1 ≤ r) {Kw LY : ℝ}
    (hLYnn : 0 ≤ LY)
    (hwin : Q ^ (-(1:ℝ)/200) * (1000 + LY) * (Real.log (2 + Q)) ^ 3 ≤ Kw) :
    (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/100) < (d:ℝ)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
      + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/100) < (d:ℝ)),
            ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
      ≤ sHalf r * Kw * Lpow Q := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hXpos : 0 < Q ^ ((1:ℝ)/100) := Real.rpow_pos_of_pos hQpos _
  obtain ⟨ht1, ht2⟩ := divisorTail_bounds r hr (Q ^ ((1:ℝ)/100)) hXpos
  have hsqX : Real.sqrt (Q ^ ((1:ℝ)/100)) = Q ^ ((1:ℝ)/200) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQpos.le]
    norm_num
  have hneg : Q ^ (-(1:ℝ)/200) = (Q ^ ((1:ℝ)/200))⁻¹ := by
    rw [show (-(1:ℝ)/200 : ℝ) = -((1:ℝ)/200) by ring]
    exact Real.rpow_neg hQpos.le ((1:ℝ)/200)
  have hB : sHalf r / Real.sqrt (Q ^ ((1:ℝ)/100)) = sHalf r * Q ^ (-(1:ℝ)/200) := by
    rw [hsqX, hneg, div_eq_mul_inv]
  have hB2 : 1000 * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/100)))
      = sHalf r * (1000 * Q ^ (-(1:ℝ)/200)) := by
    rw [hB]; ring
  have hsHalf : 0 ≤ sHalf r := sHalf_nonneg r
  have h3 : (0:ℝ) < (Real.log (2 + Q)) ^ 3 := by
    have : 0 < Real.log (2+Q) := Real.log_pos (by linarith)
    positivity
  have hkey : Q ^ (-(1:ℝ)/200) * (1000 + LY) ≤ Kw * Lpow Q := by
    have hLpow : Lpow Q = ((Real.log (2+Q)) ^ 3)⁻¹ := by
      rw [Lpow, zpow_neg, zpow_ofNat]
    rw [hLpow]
    calc Q ^ (-(1:ℝ)/200) * (1000 + LY)
        = (Q ^ (-(1:ℝ)/200) * (1000 + LY) * (Real.log (2 + Q)) ^ 3) *
            ((Real.log (2 + Q)) ^ 3)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), mul_one]
      _ ≤ Kw * ((Real.log (2 + Q)) ^ 3)⁻¹ := mul_le_mul_of_nonneg_right hwin (by positivity)
  calc (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/100) < (d:ℝ)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
      + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/100) < (d:ℝ)),
            ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
      ≤ 1000 * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/100)))
        + LY * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/100))) :=
        add_le_add ht2 (mul_le_mul_of_nonneg_left ht1 hLYnn)
    _ = sHalf r * (Q ^ (-(1:ℝ)/200) * (1000 + LY)) := by
        rw [hB2, hB]; ring
    _ ≤ sHalf r * (Kw * Lpow Q) := mul_le_mul_of_nonneg_left hkey hsHalf
    _ = sHalf r * Kw * Lpow Q := by ring

/-- Final bookkeeping: `c₁·L + K·λ·L·(9/10)σ + σ·K_w·L ≤ K·σ·L` under
`c₁ + (9/10)λK + K_w ≤ K` and `σ ≥ 1`, `L ≥ 0`. -/
lemma arith_assembly {K c1 Kw lam s L A B C : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hc1 : 0 < c1)
    (hKineq : c1 + (9/10)*lam*K + Kw ≤ K)
    (h1 : A ≤ c1*L) (h2 : B ≤ K*lam*L*((9/10)*s)) (h3 : C ≤ s*Kw*L) :
    A + B + C ≤ K * s * L := by
  have hstep : c1 * L ≤ c1 * L * s := by
    simpa using mul_le_mul_of_nonneg_left hs (mul_nonneg hc1.le hL)
  have hA : A ≤ c1 * s * L := by linarith
  have heqB : K * lam * L * ((9/10) * s) = K * lam * (9/10) * s * L := by ring
  have hB : B ≤ K * lam * (9/10) * s * L := by linarith
  have heqC : s * Kw * L = Kw * s * L := by ring
  have hC : C ≤ Kw * s * L := by linarith
  have h5 : (c1 + (9/10)*lam*K + Kw) * (s * L) ≤ K * (s * L) :=
    mul_le_mul_of_nonneg_right hKineq (mul_nonneg (by linarith : (0:ℝ) ≤ s) hL)
  have expand : (c1 + (9/10)*lam*K + Kw) * (s * L)
      = c1 * s * L + K * lam * (9/10) * s * L + Kw * s * L := by ring
  linarith [hA, hB, hC, h5, expand]

/-- Main estimate: `|T_r(Q)| ≤ K σ_{-1/2}(r) (log(2+Q))^{-3}` uniformly in `Q ≥ 1`, `r ≥ 1`. -/
theorem Tsel_bound : ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
    |Tsel r Q| ≤ K * sHalf r * Lpow Q := by
  obtain ⟨c1, hc1pos, hbase⟩ := Tsel_one_bound
  obtain ⟨Kw, hKwpos, hwin⟩ := window_log_bound
  set lam : ℝ := (100/99)^3 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; norm_num
  have hden : 0 < 1 - (9/10) * lam := by rw [hlamdef]; norm_num
  set K : ℝ := max 1 (max c1 ((c1 + Kw) / (1 - (9/10) * lam))) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKc1 : c1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbig : (c1 + Kw) / (1 - (9/10) * lam) ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKineq : c1 + (9/10) * lam * K + Kw ≤ K := by
    have h1 : (1 - (9/10) * lam) * ((c1 + Kw) / (1 - (9/10) * lam)) ≤ (1 - (9/10) * lam) * K :=
      mul_le_mul_of_nonneg_left hKbig hden.le
    rw [mul_div_cancel₀ _ (ne_of_gt hden)] at h1
    linarith
  refine ⟨K, hKpos, ?_⟩
  have key : ∀ N : ℕ, ∀ r : ℕ, ∀ Q : ℝ, 1 ≤ Q → Nat.ceil Q ≤ N → 1 ≤ r →
      |Tsel r Q| ≤ K * sHalf r * Lpow Q := by
    intro N
    induction N with
    | zero =>
      intro r Q hQ hN hr
      have hpos : 0 < Nat.ceil Q := Nat.ceil_pos.mpr (by linarith)
      omega
    | succ N ih =>
      intro r Q hQ hN hr
      rcases lt_or_ge (Nat.ceil Q) (N + 1) with hlt | hge
      · exact ih r Q hQ (by omega) hr
      · have hceil : Nat.ceil Q = N + 1 := le_antisymm hN hge
        have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
        have hLQnn : 0 ≤ Lpow Q := Lpow_nonneg hQ
        rcases eq_or_lt_of_le hr with h1 | h2
        · subst h1
          have hb := le_trans (hbase Q hQ) (mul_le_mul_of_nonneg_right hKc1 hLQnn)
          simpa [sHalf_one] using hb
        · set X : ℝ := Q ^ ((1:ℝ)/100) with hXeq
          have hXpos : 0 < X := by rw [hXeq]; exact Real.rpow_pos_of_pos hQpos _
          have hXleQ : X ≤ Q := by
            rw [hXeq]
            calc Q ^ ((1:ℝ)/100) ≤ Q ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
              _ = Q := Real.rpow_one Q
          set LY : ℝ := Real.log (2 + Q ^ ((99:ℝ)/100)) *
            (1 + Real.log (2 + Q ^ ((99:ℝ)/100))) with hLYeq
          have hLYnn : 0 ≤ LY := by
            rw [hLYeq]
            have h2' : (1:ℝ) ≤ 2 + Q ^ ((99:ℝ)/100) := by
              have hpp := Real.rpow_pos_of_pos hQpos ((99:ℝ)/100)
              linarith
            have hlog2 : 0 ≤ Real.log (2 + Q ^ ((99:ℝ)/100)) := Real.log_nonneg h2'
            exact mul_nonneg hlog2 (by linarith)
          rw [Tsel_recursion Q r hr]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hsplit : (∑ d ∈ r.divisors,
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              = (∑ d ∈ r.divisors.filter (fun d : ℕ => d = 1),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|) := by
            rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            by_cases hd1 : d = 1
            · subst hd1
              simp
            · by_cases hd2 : (d:ℝ) ≤ X
              · rw [if_neg (by simpa using hd1), if_pos ⟨hd1, hd2⟩,
                  if_neg (fun h => not_le_of_gt h.2 hd2)]
                ring
              · rw [if_neg (by simpa using hd1), if_neg (fun h => hd2 h.2),
                  if_pos ⟨hd1, not_le.mp hd2⟩]
                ring
          rw [hsplit]
          have hpiece1 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d = 1),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ c1 * Lpow Q := by
            have hfil : r.divisors.filter (fun d : ℕ => d = 1) = {(1:ℕ)} := by
              ext d
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · intro h; exact h.2
              · intro h
                subst h
                exact ⟨Nat.one_mem_divisors.mpr (by omega), rfl⟩
            rw [hfil, Finset.sum_singleton]
            simpa using hbase Q hQ
          have hpiece2 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ K * lam * Lpow Q * ((9/10) * sHalf r) := by
            have hKL : 0 ≤ K * lam * Lpow Q :=
              mul_nonneg (mul_nonneg hKpos.le hlampos.le) hLQnn
            have hpw : ∀ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  ≤ K * lam * Lpow Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by
              intro d hd
              simp only [Finset.mem_filter] at hd
              obtain ⟨hdvd, hd1', hdle⟩ := hd
              have hdpos : 0 < d := Nat.pos_of_mem_divisors hdvd
              have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
              have h2d : 2 ≤ d := by omega
              have hw : 0 ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) := by positivity
              have hdiv1 : 1 ≤ Q/(d:ℝ) := one_le_div_of_le_rpow hQ (by omega) hdle
              have hQge2 : (2:ℝ) ≤ Q :=
                le_trans (by exact_mod_cast h2d : (2:ℝ) ≤ (d:ℝ)) (le_trans hdle hXleQ)
              have h2le : (2:ℝ) ≤ (Nat.ceil Q : ℝ) := le_trans hQge2 (Nat.le_ceil Q)
              have hN1 : 1 ≤ N := by
                have h2N : (2:ℕ) ≤ Nat.ceil Q := by exact_mod_cast h2le
                omega
              have hceil' : Nat.ceil (Q/(d:ℝ)) ≤ N := by
                rw [Nat.ceil_le, div_le_iff₀ hdR]
                have h1 : Q ≤ ((N:ℝ)+1) := by
                  have h := Nat.le_ceil Q
                  rw [hceil] at h
                  push_cast at h
                  exact h
                have h2' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast h2d
                have hNd1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
                have hmul : (N:ℝ) * 2 ≤ (N:ℝ) * (d:ℝ) :=
                  mul_le_mul_of_nonneg_left h2' (by positivity)
                nlinarith [h1, hmul, hNd1]
              have hih := ih d (Q/(d:ℝ)) hdiv1 hceil' (by omega : 1 ≤ d)
              have hlam : (Real.log (2 + Q/(d:ℝ)))^(-3:ℤ) ≤ lam * Lpow Q := by
                have hlogr := log_ratio hQ (by omega : 1 ≤ d) hdle
                have ha : 0 < Real.log (2 + Q/(d:ℝ)) := by
                  apply Real.log_pos; linarith
                have hb : 0 < Real.log (2 + Q) := by
                  apply Real.log_pos; linarith
                have hcub : (Real.log (2+Q))^3
                    ≤ ((100/99:ℝ)^3) * (Real.log (2 + Q/(d:ℝ)))^3 := by
                  have h1' : Real.log (2+Q) ≤ (100/99:ℝ) * Real.log (2 + Q/(d:ℝ)) := by
                    linarith
                  calc (Real.log (2+Q))^3 ≤ ((100/99:ℝ) * Real.log (2 + Q/(d:ℝ)))^3 :=
                        pow_le_pow_left₀ hb.le h1' 3
                    _ = ((100/99:ℝ)^3) * (Real.log (2 + Q/(d:ℝ)))^3 := by ring
                rw [hlamdef, Lpow, zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
                rw [inv_eq_one_div, inv_eq_one_div, mul_one_div,
                  le_div_iff₀ (by positivity : (0:ℝ) < (Real.log (2+Q))^3),
                  div_mul_eq_mul_div,
                  div_le_iff₀ (by positivity : (0:ℝ) < (Real.log (2+Q/(d:ℝ)))^3)]
                linarith [hcub]
              calc |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * |Tsel d (Q/(d:ℝ))| := by
                    rw [abs_mul, abs_of_nonneg hw]
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      (K * sHalf d * Lpow (Q/(d:ℝ))) := mul_le_mul_of_nonneg_left hih hw
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      (K * sHalf d * (lam * Lpow Q)) := by
                    apply mul_le_mul_of_nonneg_left _ hw
                    exact mul_le_mul_of_nonneg_left hlam
                      (mul_nonneg hKpos.le (sHalf_nonneg d))
                _ = K * lam * Lpow Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by ring
            calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    K * lam * Lpow Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) :=
                  Finset.sum_le_sum hpw
              _ = K * lam * Lpow Q *
                    (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by
                  rw [Finset.mul_sum]
              _ ≤ K * lam * Lpow Q * ((9/10) * sHalf r) := by
                  apply mul_le_mul_of_nonneg_left _ hKL
                  calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                          ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d)
                      ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d),
                          ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d := by
                        apply Finset.sum_le_sum_of_subset_of_nonneg
                        · intro d hd
                          simp only [Finset.mem_filter] at hd ⊢
                          have h1d : 1 ≤ d := Nat.pos_of_mem_divisors hd.1
                          exact ⟨hd.1, by omega⟩
                        · intro d hd _
                          have hdpos : (0:ℝ) < (d:ℝ) := by
                            exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
                          have hsnn : 0 ≤ sHalf d := sHalf_nonneg d
                          positivity
                    _ ≤ (9/10) * sHalf r := diag_weighted_sum_le_alt hr
          have hpiece3 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ sHalf r * Kw * Lpow Q := by
            have hpw : ∀ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                    + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := by
              intro d hd
              simp only [Finset.mem_filter] at hd
              obtain ⟨hdvd, hd1', hdX⟩ := hd
              have hdpos : 0 < d := Nat.pos_of_mem_divisors hdvd
              have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
              have hw : 0 ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) := by positivity
              have hqnn : 0 ≤ Q/(d:ℝ) := by positivity
              have htriv := Tsel_abs_le hqnn (by omega : 1 ≤ d)
              have hXlt : Q ^ ((1:ℝ)/100) < (d:ℝ) := by rw [← hXeq]; exact hdX
              have hqle : Q/(d:ℝ) ≤ Q ^ ((99:ℝ)/100) := by
                rw [div_le_iff₀ hdR]
                have hprod : Q ^ ((99:ℝ)/100) * Q ^ ((1:ℝ)/100) = Q := by
                  rw [← Real.rpow_add hQpos]
                  norm_num
                calc Q = Q ^ ((99:ℝ)/100) * Q ^ ((1:ℝ)/100) := hprod.symm
                  _ ≤ Q ^ ((99:ℝ)/100) * (d:ℝ) :=
                      mul_le_mul_of_nonneg_left hXlt.le (Real.rpow_nonneg hQpos.le _)
              have hlogle : Real.log (2 + Q/(d:ℝ)) ≤ Real.log (2 + Q ^ ((99:ℝ)/100)) :=
                Real.log_le_log (by linarith) (by linarith)
              have hLYlog : Real.log (2 + Q/(d:ℝ)) * (1 + Real.log (2 + Q/(d:ℝ))) ≤ LY := by
                rw [hLYeq]
                have h0 : 0 ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_nonneg (by linarith)
                have h2' : 0 ≤ Real.log (2 + Q ^ ((99:ℝ)/100)) := by
                  apply Real.log_nonneg
                  have hpp := Real.rpow_pos_of_pos hQpos ((99:ℝ)/100)
                  linarith
                have h4 : (1:ℝ) + Real.log (2 + Q/(d:ℝ))
                    ≤ 1 + Real.log (2 + Q ^ ((99:ℝ)/100)) := by linarith
                exact mul_le_mul hlogle h4 (by linarith) h2'
              have htot : ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                    ((d:ℝ)/(Nat.totient d : ℝ) + LY)
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                    + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := by
                have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdR
                have hφd : (Nat.totient d : ℝ) ≠ 0 := by
                  have : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
                  exact_mod_cast this.ne'
                field_simp
              calc |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * |Tsel d (Q/(d:ℝ))| := by
                    rw [abs_mul, abs_of_nonneg hw]
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      ((d:ℝ)/(Nat.totient d : ℝ)
                        + Real.log (2 + Q/(d:ℝ)) * (1 + Real.log (2 + Q/(d:ℝ)))) :=
                    mul_le_mul_of_nonneg_left htriv hw
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      ((d:ℝ)/(Nat.totient d : ℝ) + LY) := by
                    apply mul_le_mul_of_nonneg_left _ hw
                    linarith
                _ = ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                      + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := htot
            have hsub : r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ))
                ⊆ r.divisors.filter (fun d : ℕ => X < (d:ℝ)) := by
              intro d hd
              simp only [Finset.mem_filter] at hd ⊢
              exact ⟨hd.1, hd.2.2⟩
            have hsum1' : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
            have hsum2' : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ))
                ≤ LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) := by
              rw [Finset.mul_sum]
              have hcong : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ))
                  = ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    LY * (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) :=
                Finset.sum_congr rfl (fun d _ => by ring)
              rw [hcong]
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro d _ _
              exact mul_nonneg hLYnn (by positivity)
            have hwin' : Q ^ (-(1:ℝ)/200) * (1000 + LY) * (Real.log (2 + Q)) ^ 3 ≤ Kw := by
              rw [hLYeq]
              exact hwin Q hQ
            calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    (((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                      + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ)) :=
                  Finset.sum_le_sum hpw
              _ = (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                  + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ)) :=
                  Finset.sum_add_distrib
              _ ≤ (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                  + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) :=
                  add_le_add hsum1' hsum2'
              _ ≤ sHalf r * Kw * Lpow Q := window_part_bound hQ hr hLYnn hwin'
          exact arith_assembly (sHalf_ge_one hr) hLQnn hc1pos hKineq hpiece1 hpiece2 hpiece3
  intro Q hQ r hr
  exact key (Nat.ceil Q) r Q hQ le_rfl hr

/-- Sharp asymptotic for the coprime Mertens-type sum `Θ(Q,r)`: Graham's Lemma 10.
`Θ(Q,r) = r/φ(r) + O(σ_{-1/2}(r) (log 2Q)^{-3})` with `σ_{-1/2}(r) = Σ_{d | r} d^{-1/2}`. -/
theorem selTheta_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
    |selTheta Q r - (r : ℝ) / (Nat.totient r : ℝ)| ≤
      C * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
        (Real.log (2 + Q)) ^ (-3 : ℤ) := by
  obtain ⟨K, hK, h⟩ := Tsel_bound
  exact ⟨K, hK, fun Q hQ r hr => by
    simpa [Tsel, Lpow, sHalf, abs_sub_comm] using h Q hQ r hr⟩

end

end Work.LinnikAreas.Density4
