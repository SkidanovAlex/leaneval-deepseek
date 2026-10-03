import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FIArea6.prime_recip_sum_le

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section

/-- **Elementary product bound over small primes.**

For every `k`, there is a constant `Cm > 0` such that whenever `Pz ≥ 2`, `log log x ≥ 2`,
`(log log x)^2 ≤ log Pz ≤ 2 (log log x)^2`, one has
`∏_{p ≤ Pz} (1 + 2^k · p^{1/(2 (log log x)^2)} / p) ≤ Cm · (log Pz)^{2^{k+3}}`.

The two-sided constraint on `log Pz` forces `p^{1/(2 (log log x)^2)} ≤ e` for every `p ≤ Pz`
(the exponent is at most `log p / (2 (log log x)^2) ≤ log Pz /(2 (log log x)^2) ≤ 1`).
Hence each factor is at most `1 + (2^k e)/p`, and the Mertens bound
`∑_{p ≤ Pz} 1/p ≤ log log Pz + (1 - log log 2)`
(`Work.FIArea6.primeRecips_upper`) turns the product into `(log Pz)^{2^k e}` up to a
constant; since `e ≤ 8 = 2^3` the exponent is dominated by `2^{k+3}`. -/
theorem prod_primes_one_add_le (k : ℕ) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ x Pz : ℕ, 2 ≤ Pz →
      2 ≤ Real.log (Real.log (x : ℝ)) →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Real.log (Pz : ℝ) ≤ 2 * (Real.log (Real.log (x : ℝ))) ^ 2 →
      (∏ p ∈ Nat.primesLE Pz,
          (1 + (2:ℝ)^k * ((p : ℝ) ^ ((1:ℝ) / (2 * (Real.log (Real.log (x:ℝ)))^2)) / (p:ℝ))))
        ≤ Cm * (Real.log (Pz : ℝ)) ^ ((2:ℝ)^(k+3)) := by
  refine ⟨Real.exp ((2:ℝ)^k * Real.exp 1 * (1 - Real.log (Real.log 2))), Real.exp_pos _, ?_⟩
  intro x Pz hPz hx hZlo hZhi
  set L : ℝ := Real.log (Real.log (x : ℝ)) with hLdef
  set Z : ℝ := Real.log (Pz : ℝ) with hZdef
  set c : ℝ := (2:ℝ)^k with hcdef
  set θ : ℝ := (1:ℝ) / (2 * L^2) with hθdef
  set B : ℝ := c * Real.exp 1 with hBdef
  have hL2 : 2 ≤ L := hx
  have hLpos : 0 < L := by linarith
  have hθnn : 0 ≤ θ := by rw [hθdef]; positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hZ4 : 4 ≤ Z := by
    have h4 : 4 ≤ L^2 := by nlinarith
    linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZpos : 0 < Z := by linarith
  -- pointwise bound: `p ^ θ ≤ e`, hence each factor is at most `1 + (2^k e)/p`
  have hpoint : ∀ p ∈ Nat.primesLE Pz,
      (1 + c * ((p:ℝ)^θ / (p:ℝ))) ≤ 1 + B / (p:ℝ) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hppos : (0:ℝ) < (p:ℝ) := by
      have h2 : 2 ≤ p := hp.2.two_le
      have : 0 < p := by omega
      exact_mod_cast this
    have hple : (p:ℝ) ≤ (Pz:ℝ) := by exact_mod_cast hp.1
    have hlogp : Real.log (p:ℝ) ≤ Z := by
      rw [hZdef]; exact Real.log_le_log hppos hple
    have hrpow_le : (p:ℝ)^θ ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hppos]
      apply Real.exp_le_exp.mpr
      have h1 : Real.log (p:ℝ) * θ ≤ Z * θ := mul_le_mul_of_nonneg_right hlogp hθnn
      have h2 : Z * θ ≤ 1 := by
        have h3 : Z * θ ≤ (2 * L^2) * θ := mul_le_mul_of_nonneg_right hZhi hθnn
        have h4 : (2 * L^2) * θ = 1 := by
          rw [hθdef]
          rw [mul_one_div, div_self (by positivity : (2 * L^2) ≠ 0)]
        linarith
      linarith
    have hquot : (p:ℝ)^θ / (p:ℝ) ≤ Real.exp 1 / (p:ℝ) :=
      div_le_div_of_nonneg_right hrpow_le hppos.le
    have h1 : c * ((p:ℝ)^θ / (p:ℝ)) ≤ c * (Real.exp 1 / (p:ℝ)) :=
      mul_le_mul_of_nonneg_left hquot hc0
    have h2 : c * (Real.exp 1 / (p:ℝ)) = B / (p:ℝ) := by
      rw [hBdef]; ring
    linarith
  have hfnneg : ∀ p ∈ Nat.primesLE Pz, 0 ≤ 1 + c * ((p:ℝ)^θ / (p:ℝ)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hppos : (0:ℝ) < (p:ℝ) := by
      have h2 : 2 ≤ p := hp.2.two_le
      have : 0 < p := by omega
      exact_mod_cast this
    have hqq : 0 ≤ (p:ℝ)^θ / (p:ℝ) :=
      div_nonneg (Real.rpow_nonneg hppos.le θ) hppos.le
    have : 0 ≤ c * ((p:ℝ)^θ / (p:ℝ)) := mul_nonneg hc0 hqq
    linarith
  have hstep1 : (∏ p ∈ Nat.primesLE Pz, (1 + c * ((p:ℝ)^θ / (p:ℝ))))
      ≤ ∏ p ∈ Nat.primesLE Pz, (1 + B / (p:ℝ)) :=
    Finset.prod_le_prod₀ hfnneg hpoint
  -- bound the majorant product via the Mertens reciprocal-prime sum
  set S : ℝ := ∏ p ∈ Nat.primesLE Pz, (1 + B / (p:ℝ)) with hSdef
  have hgpos : ∀ p ∈ Nat.primesLE Pz, 0 < 1 + B / (p:ℝ) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hppos : (0:ℝ) < (p:ℝ) := by
      have h2 : 2 ≤ p := hp.2.two_le
      have : 0 < p := by omega
      exact_mod_cast this
    have : 0 ≤ B / (p:ℝ) := div_nonneg hBnn hppos.le
    linarith
  have hSpos : 0 < S := Finset.prod_pos hgpos
  have hlogS : Real.log S = ∑ p ∈ Nat.primesLE Pz, Real.log (1 + B / (p:ℝ)) := by
    rw [hSdef]
    exact Real.log_prod (fun p hp => ne_of_gt (hgpos p hp))
  have hlog_le : Real.log S ≤ ∑ p ∈ Nat.primesLE Pz, B / (p:ℝ) := by
    rw [hlogS]
    apply Finset.sum_le_sum
    intro p hp
    have h1 : 0 < 1 + B / (p:ℝ) := hgpos p hp
    have h2 := Real.log_le_sub_one_of_pos h1
    have h3 : (1 + B / (p:ℝ)) - 1 = B / (p:ℝ) := by ring
    linarith
  have hsum_eq : ∑ p ∈ Nat.primesLE Pz, B / (p:ℝ)
      = B * ∑ p ∈ Nat.primesLE Pz, (1:ℝ)/(p:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hrec_eq : Commons.NumberTheory.Mertens.primeRecips ((Pz:ℕ):ℝ)
      = ∑ p ∈ Nat.primesLE Pz, (1:ℝ)/(p:ℝ) := by
    simp only [Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast]
  have hrec_le : ∑ p ∈ Nat.primesLE Pz, (1:ℝ)/(p:ℝ)
      ≤ Real.log Z + (1 - Real.log (Real.log 2)) := by
    have h := Work.FIArea6.primeRecips_upper (x := (Pz:ℝ)) (by exact_mod_cast hPz)
    rw [← hZdef] at h
    rw [hrec_eq] at h
    exact h
  have hlog_bound : Real.log S ≤ B * (Real.log Z + (1 - Real.log (Real.log 2))) := by
    calc Real.log S ≤ ∑ p ∈ Nat.primesLE Pz, B / (p:ℝ) := hlog_le
      _ = B * ∑ p ∈ Nat.primesLE Pz, (1:ℝ)/(p:ℝ) := hsum_eq
      _ ≤ B * (Real.log Z + (1 - Real.log (Real.log 2))) :=
          mul_le_mul_of_nonneg_left hrec_le hBnn
  have hexpZ : Real.exp (B * Real.log Z) = Z ^ B := by
    rw [Real.rpow_def_of_pos hZpos B]
    congr 1
    ring
  have hS_bound : S ≤ Z^B * Real.exp (B * (1 - Real.log (Real.log 2))) := by
    calc S = Real.exp (Real.log S) := (Real.exp_log hSpos).symm
      _ ≤ Real.exp (B * (Real.log Z + (1 - Real.log (Real.log 2)))) :=
            Real.exp_le_exp.mpr hlog_bound
      _ = Real.exp (B * Real.log Z) * Real.exp (B * (1 - Real.log (Real.log 2))) := by
            rw [← Real.exp_add]; congr 1; ring
      _ = Z^B * Real.exp (B * (1 - Real.log (Real.log 2))) := by rw [hexpZ]
  have hZpow_le : Z ^ B ≤ Z ^ ((2:ℝ)^(k+3)) := by
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    rw [hBdef, hcdef]
    have h8 : Real.exp 1 ≤ 8 := by have := Real.exp_one_lt_three; linarith
    calc (2:ℝ)^k * Real.exp 1 ≤ (2:ℝ)^k * 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = (2:ℝ)^(k+3) := by rw [pow_add]; norm_num
  have hStep2 : S ≤ Z ^ ((2:ℝ)^(k+3)) * Real.exp (B * (1 - Real.log (Real.log 2))) := by
    calc S ≤ Z^B * Real.exp (B * (1 - Real.log (Real.log 2))) := hS_bound
      _ ≤ Z^((2:ℝ)^(k+3)) * Real.exp (B * (1 - Real.log (Real.log 2))) :=
          mul_le_mul_of_nonneg_right hZpow_le (Real.exp_pos _).le
  have hCm_eq : Real.exp (B * (1 - Real.log (Real.log 2)))
      = Real.exp ((2:ℝ)^k * Real.exp 1 * (1 - Real.log (Real.log 2))) := by
    rw [hBdef, hcdef]
  calc (∏ p ∈ Nat.primesLE Pz, (1 + c * ((p:ℝ)^θ / (p:ℝ))))
      ≤ S := hstep1
    _ ≤ Z ^ ((2:ℝ)^(k+3)) * Real.exp (B * (1 - Real.log (Real.log 2))) := hStep2
    _ = Z ^ ((2:ℝ)^(k+3)) * Real.exp ((2:ℝ)^k * Real.exp 1 * (1 - Real.log (Real.log 2))) := by
          rw [hCm_eq]
    _ = Real.exp ((2:ℝ)^k * Real.exp 1 * (1 - Real.log (Real.log 2))) * Z ^ ((2:ℝ)^(k+3)) :=
          mul_comm _ _

end

end Work.FIChain
