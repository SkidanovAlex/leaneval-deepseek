import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod

/-!
# U-decomposition of `log σ(N_ε) − log N_ε`, inlined form

Self-contained (Mathlib + commons only) port of `caU_decomp` from
`Submission/Work/NumberTheory/Robin/caU.lean`.  For the colossally-abundant number

  `N_ε = ∏_{p < ⌈exp(2/ε)⌉+2, p prime} p ^ ⌊log((p^{1+ε}−1)/(p^{1+ε}−p))/log p⌋₊`

the per-prime identity `log(σ(p^a)/p^a) = log(p/(p−1)) + log(1 − p^{−(a+1)})` (for `a ≥ 1`,
and trivially `0 = 0` for `a = 0`) summed over the prime support
`supp(ε) = {p prime : 1 ≤ a_p}` gives

  `log σ(N_ε) − log N_ε = Σ_{p∈supp} log(p/(p−1)) + Σ_{p∈supp} log(1 − p^{−(a_p+1)})`.

All helper definitions are private so nothing leaks into the commons namespace.
-/

namespace Commons.NumberTheory.Robin

noncomputable section

open scoped BigOperators

/-- The range bound `⌈exp(2/ε)⌉ + 2` for the prime support. -/
private abbrev caBoundD (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- The primes below the range bound. -/
private abbrev caPrimesD (ε : ℝ) : Finset ℕ := (Finset.range (caBoundD ε)).filter Nat.Prime

/-- The exponent `⌊μ(p,ε)⌋₊` of the prime `p` in `N_ε`. -/
private abbrev caExpD (p : ℕ) (ε : ℝ) : ℕ :=
  ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊

/-- The colossally-abundant number `N_ε`. -/
private abbrev caND (ε : ℝ) : ℕ := Finset.prod (caPrimesD ε) (fun p => p ^ caExpD p ε)

/-- The prime support `{p prime : 1 ≤ a_p}`. -/
private abbrev caSuppD (ε : ℝ) : Finset ℕ := (caPrimesD ε).filter (fun p => 1 ≤ caExpD p ε)

/-- `log(p/(p−1))`, the Mertens main factor at `p`. -/
private abbrev caMertensLogD (p : ℕ) : ℝ := Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- `log(1 − p^{−(a+1)}) = log((p^{a+1}−1)/p^{a+1})`, the correction factor. -/
private abbrev caCorrLogD (p : ℕ) (a : ℕ) : ℝ :=
  Real.log ((((p : ℝ) ^ (a + 1 : ℕ)) - 1) / ((p : ℝ) ^ (a + 1 : ℕ)))

/-- `log(σ(p^a)/p^a) = log((p^{a+1}−1)/(p^a·(p−1)))`. -/
private abbrev caPowTermD (p : ℕ) (a : ℕ) : ℝ :=
  Real.log ((((p : ℝ) ^ (a + 1 : ℕ)) - 1) / (((p : ℝ) ^ a) * ((p : ℝ) - 1)))

/-- multiplicativity of `σ 1` over a product of prime powers with distinct primes. -/
private lemma sigma_prod_prime_pows {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p) (a : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
      have hp' : Nat.Prime p := hprime p (by simp)
      have hcop : (p ^ a p).Coprime (Finset.prod s (fun q => q ^ a q)) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq' : Nat.Prime q := hprime q (Finset.mem_insert_of_mem hq)
        have hpq_ne : q ≠ p := by
          intro hpq
          exact hpnot (by simpa [hpq] using hq)
        have hpq : p.Coprime q := (Nat.coprime_primes hp' hq').mpr (Ne.symm hpq_ne)
        have h1 : p.Coprime (q ^ a q) := Nat.Coprime.pow_right (a q) hpq
        exact Nat.Coprime.pow_left (a p) h1
      have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have ih' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpnot, hσ, ih', Finset.prod_insert hpnot]

/-- `log σ(N_ε)` splits over the range-product of `N_ε`. -/
private lemma log_sigma_ND {ε : ℝ} :
    Real.log (((ArithmeticFunction.sigma 1 (caND ε) : ℕ) : ℝ)) =
      Finset.sum (caPrimesD ε)
        (fun p => Real.log (((ArithmeticFunction.sigma 1 (p ^ caExpD p ε) : ℕ) : ℝ))) := by
  have hfac : ArithmeticFunction.sigma 1 (caND ε) =
      Finset.prod (caPrimesD ε)
        (fun p => ArithmeticFunction.sigma 1 (p ^ caExpD p ε)) := by
    unfold caND
    exact sigma_prod_prime_pows (s := caPrimesD ε)
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p => caExpD p ε)
  rw [hfac]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro p hp
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ caExpD p ε) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos (Nat.Prime.pos hp') (caExpD p ε))
  exact_mod_cast (ne_of_gt hσ)

/-- `log N_ε` splits over the range-product of `N_ε`. -/
private lemma log_ND {ε : ℝ} :
    Real.log ((caND ε : ℕ) : ℝ) =
      Finset.sum (caPrimesD ε) (fun p => (caExpD p ε : ℝ) * Real.log (p : ℝ)) := by
  unfold caND
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpow : 0 < p ^ caExpD p ε := pow_pos (Nat.Prime.pos hp') (caExpD p ε)
    exact_mod_cast (ne_of_gt hpow)

/-- per-prime: `log σ(p^a) − log(p^a) = caPowTermD p a` (prime `p`, any `a`). -/
private lemma log_sigma_pow_sub_log_pow {p a : ℕ} (hp : Nat.Prime p) :
    Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) - Real.log ((p ^ a : ℕ) : ℝ) =
      caPowTermD p a := by
  have hpa : 0 < p ^ a := pow_pos (Nat.Prime.pos hp) a
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ a) := (ArithmeticFunction.sigma_pos_iff).2 hpa
  have hσr : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) := by exact_mod_cast hσ
  have hpar : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) := by exact_mod_cast hpa
  have hclosed : ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) =
      (((p : ℝ) ^ (a + 1 : ℕ)) - 1) / (((p : ℝ) ^ a) * ((p : ℝ) - 1)) := by
    simpa using (Commons.NumberTheory.Robin.sigma_one_ratio_prime_pow (p := p) (k := a) hp)
  calc
    Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) - Real.log ((p ^ a : ℕ) : ℝ)
        = Real.log ((((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) / ((p ^ a : ℕ) : ℝ)) := by
            rw [← Real.log_div hσr.ne' hpar.ne']
    _ = caPowTermD p a := by
            unfold caPowTermD
            rw [hclosed]

/-- `caPowTermD p 0 = 0` (the empty prime power contributes nothing; prime `p ≥ 2`). -/
private lemma caPowTermD_zero {p : ℕ} (hp : 2 ≤ p) : caPowTermD p 0 = 0 := by
  unfold caPowTermD
  have hnum : ((p : ℝ) ^ 1) - 1 = (p : ℝ) - 1 := by simp
  have hden : ((p : ℝ) ^ 0) * ((p : ℝ) - 1) = (p : ℝ) - 1 := by simp
  rw [hnum, hden]
  have hpm : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  rw [div_self hpm]
  simp

/-- per-prime split: `caPowTermD p a = log(p/(p−1)) + log((p^{a+1}−1)/p^{a+1})` for `p ≥ 2`. -/
private lemma caPowTermD_split {p a : ℕ} (hp : 2 ≤ p) :
    caPowTermD p a = caMertensLogD p + caCorrLogD p a := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpminus : 0 < (p : ℝ) - 1 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpminus
  have hposA : 0 < ((p : ℝ) ^ (a + 1 : ℕ)) - 1 := by
    have hpowgt : 1 < (p : ℝ) ^ (a + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : a + 1 ≠ 0)
    linarith
  have hposC : 0 < (p : ℝ) ^ (a + 1 : ℕ) := pow_pos hp0 (a + 1)
  have hprod : (((p : ℝ) ^ (a + 1 : ℕ)) - 1) / (((p : ℝ) ^ a) * ((p : ℝ) - 1)) =
      ((p : ℝ) / ((p : ℝ) - 1)) *
        ((((p : ℝ) ^ (a + 1 : ℕ)) - 1) / ((p : ℝ) ^ (a + 1 : ℕ))) := by
    rw [pow_succ]
    field_simp [hp1, ne_of_gt hp0]
  calc
    caPowTermD p a = Real.log (((p : ℝ) / ((p : ℝ) - 1)) *
        ((((p : ℝ) ^ (a + 1 : ℕ)) - 1) / ((p : ℝ) ^ (a + 1 : ℕ)))) := by
          unfold caPowTermD
          rw [hprod]
    _ = caMertensLogD p + caCorrLogD p a := by
          unfold caMertensLogD caCorrLogD
          rw [Real.log_mul (ne_of_gt (div_pos hp0 hpminus)) (ne_of_gt (div_pos hposA hposC))]

/-- A sum over `caPrimesD ε` of `if 1 ≤ a_p then f p else 0` equals the sum of `f` over the
support `caSuppD ε`. -/
private lemma sum_if_eq_sum_supp {ε : ℝ} (f : ℕ → ℝ) :
    Finset.sum (caPrimesD ε) (fun p => if 1 ≤ caExpD p ε then f p else 0) =
      Finset.sum (caSuppD ε) f := by
  rw [show caSuppD ε = (caPrimesD ε).filter (fun p => 1 ≤ caExpD p ε) from rfl]
  exact (Finset.sum_filter (s := caPrimesD ε) (p := fun p => 1 ≤ caExpD p ε) (f := f)).symm

/-- **U-decomposition**, in terms of the private abbreviations. -/
private theorem caU_aux {ε : ℝ} (hε : 0 < ε) :
    Real.log (((ArithmeticFunction.sigma 1 (caND ε) : ℕ) : ℝ)) - Real.log ((caND ε : ℕ) : ℝ) =
      Finset.sum (caSuppD ε) (fun p => caMertensLogD p) +
      Finset.sum (caSuppD ε) (fun p => caCorrLogD p (caExpD p ε)) := by
  have hsplit : Real.log (((ArithmeticFunction.sigma 1 (caND ε) : ℕ) : ℝ)) -
        Real.log ((caND ε : ℕ) : ℝ) =
      Finset.sum (caPrimesD ε) (fun p => caPowTermD p (caExpD p ε)) := by
    calc
      Real.log (((ArithmeticFunction.sigma 1 (caND ε) : ℕ) : ℝ)) - Real.log ((caND ε : ℕ) : ℝ)
          = Finset.sum (caPrimesD ε)
              (fun p => Real.log (((ArithmeticFunction.sigma 1 (p ^ caExpD p ε) : ℕ) : ℝ))) -
            Finset.sum (caPrimesD ε) (fun p => (caExpD p ε : ℝ) * Real.log (p : ℝ)) := by
              rw [log_sigma_ND, log_ND]
      _ = Finset.sum (caPrimesD ε) (fun p =>
            Real.log (((ArithmeticFunction.sigma 1 (p ^ caExpD p ε) : ℕ) : ℝ)) -
              (caExpD p ε : ℝ) * Real.log (p : ℝ)) := by
            rw [← Finset.sum_sub_distrib]
      _ = Finset.sum (caPrimesD ε) (fun p => caPowTermD p (caExpD p ε)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have h1 := log_sigma_pow_sub_log_pow (p := p) (a := caExpD p ε) hp'
            have h2 : Real.log ((p ^ caExpD p ε : ℕ) : ℝ) =
                (caExpD p ε : ℝ) * Real.log (p : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]
            linarith
  have hguarded : Finset.sum (caPrimesD ε) (fun p => caPowTermD p (caExpD p ε)) =
      Finset.sum (caPrimesD ε) (fun p =>
        if 1 ≤ caExpD p ε then caMertensLogD p + caCorrLogD p (caExpD p ε) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    by_cases ha : 1 ≤ caExpD p ε
    · have hsp := caPowTermD_split (p := p) (a := caExpD p ε) hp'.two_le
      simp only [ha, if_true]
      exact hsp
    · have hz : caExpD p ε = 0 := by omega
      rw [hz, caPowTermD_zero hp'.two_le]
      simp
  calc
    Real.log (((ArithmeticFunction.sigma 1 (caND ε) : ℕ) : ℝ)) - Real.log ((caND ε : ℕ) : ℝ)
        = Finset.sum (caPrimesD ε) (fun p => caPowTermD p (caExpD p ε)) := hsplit
    _ = Finset.sum (caPrimesD ε) (fun p =>
          if 1 ≤ caExpD p ε then caMertensLogD p + caCorrLogD p (caExpD p ε) else 0) :=
        hguarded
    _ = Finset.sum (caSuppD ε) (fun p => caMertensLogD p + caCorrLogD p (caExpD p ε)) :=
        sum_if_eq_sum_supp (fun p => caMertensLogD p + caCorrLogD p (caExpD p ε))
    _ = Finset.sum (caSuppD ε) (fun p => caMertensLogD p) +
        Finset.sum (caSuppD ε) (fun p => caCorrLogD p (caExpD p ε)) := by
          rw [Finset.sum_add_distrib]

theorem caU_decomp {ε : ℝ} (hε : 0 < ε) :
    Real.log (((ArithmeticFunction.sigma 1 (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) : ℕ) : ℝ)) - Real.log (((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) : ℕ) : ℝ)
      = (Finset.sum (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) (fun p : ℕ => Real.log ((p : ℝ) / ((p : ℝ) - 1)))) + (Finset.sum (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) (fun p : ℕ => Real.log ((((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1)) - 1) / ((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1))))) := by
  simpa only [caBoundD, caPrimesD, caExpD, caND, caSuppD, caMertensLogD, caCorrLogD]
    using caU_aux hε

end

end Commons.NumberTheory.Robin