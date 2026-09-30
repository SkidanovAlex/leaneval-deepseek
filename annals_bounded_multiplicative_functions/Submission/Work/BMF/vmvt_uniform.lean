import Mathlib
import Submission.Work.BMF.Defs
import Submission.Vinogradov.ChallengeDeps
import Submission.Work.BMF.J_mono_X
import Submission.Work.BMF.vmvt_setup
import Submission.Work.BMF.linnik_bound
import Submission.Work.BMF.prime_interval_count
import Submission.Work.BMF.recursion_step
import Submission.Work.BMF.J_kk_le
import Submission.Work.BMF.vmvt_step_ineq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTE: ... (see DESIGN.md 'Addendum: vk_prime_sums detail').

## Plan of the proof (classical Vinogradov–Linnik iteration)

`J_{kr,k}(P) ≤ exp(C₀k²r²(1+log(kr)))·P^{2kr − k(k+1)/2 + (k²/2)(1−1/k)^r}`,
proved by induction on `r ≥ 1` for every `k ≥ 2` and every `P ≥ 1`:

* base `r = 1`: `J_{k,k}(P) ≤ k!·P^k` (`Work.BMF.J_kk_le`), and `k! ≤ exp(C₀k²(1+log k))`;
* step `r → r+1`: the classical recursion `Work.BMF.recursion_step` turns `J_{k(r+1),k}(Q)` into
  a constant multiple of `Q^k·J_{kr,k}(1+Q/M)` with `M = max k (⌈Q^{1/k}⌉+1)`, the primes coming
  from the quantitative short-interval count `Work.BMF.prime_interval_count`; the induction
  hypothesis and the pure arithmetic inequality `Work.BMF.vmvt_step_ineq` then give
  `Ac C₀ k (r+1)·Q^{th k (r+1)}`.

The definitions `pC`, `th`, `Ac`, `C0` live in `Submission/Work/BMF/vmvt_setup.lean`.
-/

namespace Work.BMF

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

noncomputable section

/-- A set of `⌈k³/2⌉` primes lying in `(M, max (2M) ⌈pC·k³·log k⌉]`. -/
theorem exists_prime_set (k M : ℕ) (hk : 2 ≤ k) (hM : 1 ≤ M) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ (∀ p ∈ P, M < p) ∧
      (∀ p ∈ P, p ≤ max (2*M) ⌈pC * (k:ℝ)^3 * Real.log k⌉₊) ∧
      P.card = ⌈(k:ℝ)^3/2⌉₊ := by
  set Y : ℕ := max (2*M) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ with hY
  set S : Finset ℕ := (Finset.Ioc M Y).filter Nat.Prime with hS
  have hspec' : k^3 ≤ 2 * S.card := by
    rw [hS]
    exact pC_spec k M hk hM
  have hcardS : ⌈(k:ℝ)^3/2⌉₊ ≤ S.card := by
    refine Nat.ceil_le.mpr ?_
    have h3 : ((k^3 : ℕ) : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hspec'
    push_cast at h3
    linarith
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hcardS
  refine ⟨P, ?_, ?_, ?_, hPcard⟩
  · intro p hp
    exact (Finset.mem_filter.mp (hPsub hp)).2
  · intro p hp
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hPsub hp)).1).1
  · intro p hp
    have hmem := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hPsub hp)).1).2
    rwa [hY] at hmem

lemma th_one (k : ℕ) (hk : 1 ≤ k) : th k 1 = (k:ℝ) := by
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  simp only [th, pow_one, Nat.cast_one, mul_one]
  field_simp
  ring

/-- `th k r ≥ k` for `k ≥ 1`, `r ≥ 1`. -/
lemma th_ge (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) : (k:ℝ) ≤ th k r := by
  have mono : ∀ n, th k n ≤ th k (n+1) := by
    intro n
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hle1 : (1 - 1/(k:ℝ)) ≤ 1 := by
      have : (0:ℝ) < (k:ℝ) := by linarith
      rw [sub_le_iff_le_add]; simp
    have hu1 : (1-1/(k:ℝ))^n ≤ 1 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 1 - 1/(k:ℝ) by
        have : (1:ℝ) ≤ k := by exact_mod_cast hk
        rw [sub_nonneg]; exact div_le_one_of_le₀ this (by positivity)) hle1 n
      simpa using h
    have hp : (1-1/(k:ℝ))^(n+1) = (1-1/(k:ℝ))^n*(1-1/(k:ℝ)) := pow_succ _ _
    have hdiff : th k (n+1) - th k n = 2*(k:ℝ) - (k:ℝ)/2*(1-1/(k:ℝ))^n := by
      simp only [th, hp]; push_cast; field_simp; ring
    have hb : (k:ℝ)/2*(1-1/(k:ℝ))^n ≤ (k:ℝ)/2 :=
      mul_le_of_le_one_right (by positivity) hu1
    linarith
  have hle : th k 1 ≤ th k r := (monotone_nat_of_le_succ mono) hr
  rw [th_one k hk] at hle
  exact hle

/-- `th k r` is nonnegative for `k ≥ 1`, `r ≥ 1`. -/
lemma th_nonneg (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) : 0 ≤ th k r :=
  le_trans (by positivity : (0:ℝ) ≤ k) (th_ge k r hk hr)

/-- The main induction. -/
theorem main_claim (k : ℕ) (hk : 2 ≤ k) :
    ∀ r ≥ 1, ∀ Q ≥ 1, J (k*r) k Q ≤ Ac C0 k r * (Q:ℝ)^(th k r) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
      intro Q hQ
      have hth : th k 1 = (k:ℝ) := th_one k (by omega)
      have hk1 : k*1 = k := Nat.mul_one k
      rw [hk1, hth, Real.rpow_natCast]
      have hfac : ((k.factorial:ℕ):ℝ) ≤ Ac C0 k 1 := by
        have hk1' : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        have hlogk : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg hk1'
        have hkk : (0:ℝ) < k := by linarith
        have hC0 : (1:ℝ) ≤ C0 := by
          have h : 0 < Real.log (pC+8) := Real.log_pos (by linarith [pC_pos])
          simp only [C0]; linarith
        have h1 : Real.log ((k.factorial:ℕ):ℝ) ≤ (k:ℝ)*Real.log k := by
          have h2 : ((k.factorial:ℕ):ℝ) ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
          calc Real.log ((k.factorial:ℕ):ℝ) ≤ Real.log ((k:ℝ)^k) :=
                Real.log_le_log (by positivity) h2
            _ = (k:ℝ)*Real.log k := Real.log_pow _ _
        have h3 : (k:ℝ)*Real.log k ≤ C0*(k:ℝ)^2*1*(1+Real.log k) := by
          nlinarith [hlogk, hk1', hC0, sq_nonneg (k:ℝ), mul_nonneg hlogk (le_of_lt hkk),
            mul_nonneg (sq_nonneg (k:ℝ)) hlogk]
        have h4 : ((k.factorial:ℕ):ℝ) ≤ Real.exp (C0*(k:ℝ)^2*1*(1+Real.log k)) := by
          calc ((k.factorial:ℕ):ℝ) = Real.exp (Real.log ((k.factorial:ℕ):ℝ)) :=
                (Real.exp_log (by positivity)).symm
            _ ≤ Real.exp (C0*(k:ℝ)^2*1*(1+Real.log k)) := Real.exp_le_exp.mpr (le_trans h1 h3)
        simpa only [Ac, Nat.cast_one, one_pow, mul_one] using h4
      calc J k k Q ≤ ((k.factorial:ℕ):ℝ) * (Q:ℝ)^k := J_kk_le k Q
        _ ≤ Ac C0 k 1 * (Q:ℝ)^k := by
            apply mul_le_mul_of_nonneg_right hfac (by positivity)
  | succ r hr ih =>
      intro Q hQ
      set M : ℕ := max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ + 1) with hMdef
      set Y : ℕ := max (2*M) ⌈pC * (k:ℝ)^3 * Real.log k⌉₊ with hYdef
      have hk1 : 1 ≤ k := by omega
      have hM1 : 1 ≤ M := le_trans (by omega : 1 ≤ k) (le_max_left _ _)
      obtain ⟨P, hPp, hPlb, hPub, hPcard⟩ := exists_prime_set k M hk hM1
      have hMk : k ≤ M := le_max_left _ _
      have hMgt : (Q:ℝ)^(1/(k:ℝ)) < (M:ℝ) := by
        have hceil : (Q:ℝ)^(1/(k:ℝ)) ≤ ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have hlt : ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) < (M:ℝ) := by
          have h2 : (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) + 1 ≤ M := by
            simp only [hMdef]
            exact le_max_right _ _
          have h3 : ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) + 1 ≤ (M:ℝ) := by exact_mod_cast h2
          linarith
        exact lt_of_le_of_lt hceil hlt
      have hMQ : (Q:ℝ) < (M:ℝ)^k := by
        have hq0 : (0:ℝ) ≤ Q := by positivity
        have hk0 : (0:ℝ) < k := by positivity
        have hrpow : ((Q:ℝ)^(1/(k:ℝ)))^k = (Q:ℝ) := by
          rw [← Real.rpow_natCast ((Q:ℝ)^(1/(k:ℝ))) k, ← Real.rpow_mul hq0]
          have hexp : (1/(k:ℝ)) * (k:ℝ) = 1 := by field_simp
          rw [hexp, Real.rpow_one]
        calc (Q:ℝ) = ((Q:ℝ)^(1/(k:ℝ)))^k := hrpow.symm
          _ < (M:ℝ)^k := pow_lt_pow_left₀ hMgt (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ Q) _) (by omega : k ≠ 0)
      have hSk : k ≤ k*(r+1) := by nlinarith [hr]
      have hrec := recursion_step k (k*(r+1)) Q M Y hk hSk hQ hMk hMQ P hPp hPlb hPub hPcard.ge
      have hsub : k*(r+1) - k = k*r := by rw [Nat.mul_succ]; omega
      rw [hsub] at hrec
      have hP6 : (P.card:ℝ)^2 ≤ (k:ℝ)^6 := by
        have h1 : P.card ≤ k^3 := by
          rw [hPcard]
          refine Nat.ceil_le.mpr ?_
          push_cast
          nlinarith [show (0:ℝ) ≤ (k:ℝ)^3 by positivity]
        have h2 : ((P.card:ℕ):ℝ) ≤ ((k^3:ℕ):ℝ) := by exact_mod_cast h1
        push_cast at h2
        have h3 : ((P.card:ℕ):ℝ)^2 ≤ ((k:ℝ)^3)^2 :=
          pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (P.card:ℝ)) h2 2
        calc ((P.card:ℕ):ℝ)^2 ≤ ((k:ℝ)^3)^2 := h3
          _ = (k:ℝ)^6 := by ring
      have hIH := ih (1 + Q / M) (Nat.le_add_right 1 (Q/M))
      have hcast : (((1 + Q / M : ℕ) : ℝ)) ≤ 1 + (Q:ℝ)/(M:ℝ) := by
        have h1 : ((Q / M : ℕ) : ℝ) * (M:ℝ) ≤ (Q:ℝ) := by
          have := Nat.div_mul_le_self Q M
          exact_mod_cast this
        have hMpos : (0:ℝ) < M := by positivity
        have h2 : ((Q / M : ℕ) : ℝ) ≤ (Q:ℝ)/(M:ℝ) := by
          rw [le_div_iff₀ hMpos]
          exact h1
        push_cast
        linarith
      have hAcpos : 0 < Ac C0 k r := Real.exp_pos _
      have hIH' : J (k*r) k (1 + Q / M) ≤ Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r) := by
        refine hIH.trans ?_
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hAcpos)
        exact Real.rpow_le_rpow (by positivity) hcast (th_nonneg k r hk1 hr)
      calc J (k*(r+1)) k Q
          ≤ (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*
              ((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M) := hrec
        _ ≤ (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*
              ((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*
              (Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by
            have hprod : (P.card:ℝ)^2 * J (k*r) k (1 + Q / M) ≤
                (k:ℝ)^6 * (Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) :=
              mul_le_mul hP6 hIH' (by
                unfold LeanEval.NumberTheory.VinogradovMeanValue.J; positivity) (by positivity)
            have h2 := mul_le_mul_of_nonneg_left hprod
              (show (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k by positivity)
            have hprod2 : 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M)
                ≤ 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*(Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by
              calc 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M)
                  = (4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k)*((P.card:ℝ)^2*J (k*r) k (1 + Q / M)) := by ring
                _ ≤ (4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k)*((k:ℝ)^6*(Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r))) := h2
                _ = 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*(Ac C0 k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by ring
            exact add_le_add (le_refl _) hprod2
        _ ≤ Ac C0 k (r+1) * (Q:ℝ)^(th k (r+1)) := by
            have hstep := vmvt_step_ineq k r Q hk hr hQ
            simp only [hMdef, hYdef]
            rw [show 2*(k*r)+k*(k-1)/2 = 2*k*r+k*(k-1)/2 from by ring]
            exact hstep

/-- **V0. Vinogradov's mean value estimate with an explicit constant** (classical
Vinogradov–Karatsuba iteration, *not* the BDG route). For `k ≥ 2`, `r ≥ 1`, `s = kr`:
`J_{s,k}(P) ≤ exp(C₀ k² r² (1 + log(kr))) · P^{2s − k(k+1)/2 + (k²/2)(1 − 1/k)^r}`.
The constant must be explicit in `k` and `r`, because the exponential-sum bound takes
`k ≍ log t / log N`, which is unbounded. -/
theorem vmvt_uniform :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k r P : ℕ), 2 ≤ k → 1 ≤ r → 1 ≤ P →
      J (k * r) k P ≤
        Real.exp (C₀ * (k : ℝ) ^ 2 * (r : ℝ) ^ 2 * (1 + Real.log ((k : ℝ) * r))) *
          (P : ℝ) ^ (2 * ((k : ℝ) * r) - (k : ℝ) * (k + 1) / 2 +
            (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ r) := by
  refine ⟨C0, C0_pos, ?_⟩
  intro k r P hk hr hP
  have hmain := main_claim k hk r hr P hP
  simpa only [Ac, th] using hmain

end
end Work.BMF
