/-
  Companion paper ("Asymptotic sieve for primes", Friedlander–Iwaniec, Ann. of Math. 148
  (1998) 1041–1065), §8 (`S₃`), the `λ⁺` part.

  `S3 = S3minus − S3plus` is split (in `S8.lean`) according to `Λ(c) = λ⁻(c) − λ⁺(c)`, where

      `λ⁺(c) = ∑_{m ∣ c, C < m} μ(m)·log(m/C)`,   `λ⁻(c) = ∑_{m ∣ c, m ≤ C} μ(m)·log(C/m)`.

  The estimate (8.1) for the `λ⁻` part — which rests on the integral representation
  `λ⁻(c) = ∫_1^C ρ(c;t)/t dt` — is proved in `S8b.lean` from the `(B′)`-type hypothesis
  `RhoWindow` (the companion's bilinear axiom, restricted to the *small* truncation levels
  `s ≤ C = x/D`; that is exactly (B3) of the companion).

  Here we prove the `λ⁺` part (8.3)–(8.4) of the paper by a *single* further application of the
  same axiom, using the companion identity

      `λ⁺(c) = − ∫_C^M ρ(c;t)/t dt`   for   `2 ≤ c ≤ M`   and   `0 < C ≤ M`,

  which is the `λ⁺`-analogue of the `λ⁻` integral representation (`S8.lamMinus_eq_integral`) and
  is *not* mentioned in the companion paper.  The paper instead rewrites `λ⁺` by summation by
  parts into an `A_d`-difference (its (8.2)) and estimates the two halves separately: the main
  term (8.3) by the Möbius-cancellation hypothesis (2.4) and the remainder (8.4) by the
  remainder hypothesis `(R′)` applied after integrating over the smoothing variables.

  Because `λ⁺` is an integral of the *same* kernel `ρ(n;t)` as `λ⁻`, the `(B′)`-axiom suffices
  for it as well — at the price of using the bilinear form at truncation levels `t ∈ [C, sz]`
  rather than `t ∈ [1, C]`.  The hypothesis `RhoWindow` below is therefore stated with the
  level range `s ∈ [1, R]` for some `R ≥ ⌊sz⌋₊`; the companion's (B3) prescribes the smaller
  level range `s ≤ x/D = C`.

  Main results:

  * `lamPlus_eq_neg_integral`  — the integral representation of `λ⁺`;
  * `S3plus_eq_reindex`        — `(b,e) ↦ ℓ = be` merged, as for `S₃⁻`;
  * `abs_S3plus_le`            — `|S₃⁺| ≤ J·E·log(⌊sz⌋₊/C)`  (the `λ⁺` half of §8);
  * `abs_S3_le` ★              — `|S₃| ≤ J·E·log ⌊sz⌋₊`, i.e. §8's (8.5) as far as the
                                 companion's own hypotheses are concerned.
-/
import Mathlib
import Submission.ASP.S8
import Submission.ASP.S8b

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### The interval integral of the step function `t ↦ 1_{m<t}/t` -/

/-- `∫_C^M 1_{m<t}/t dt = log(M/C)` if `m ≤ C`, `= log(M/m)` if `C < m < M`, `= 0` if `M ≤ m`
(for `1 ≤ m` and `0 < C ≤ M`). -/
lemma integral_stepInv_Ioc (m : ℕ) (hm : 1 ≤ m) {C M : ℝ} (hC : 0 < C) (hCM : C ≤ M) :
    (∫ t in C..M, stepInv m t)
      = if ((m : ℕ) : ℝ) ≤ C then Real.log (M / C)
        else if ((m : ℕ) : ℝ) < M then Real.log (M / (m : ℝ)) else 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le hC hCM
  by_cases hmC : ((m : ℕ) : ℝ) ≤ C
  · -- `m ≤ C`: the integrand is `1/t` throughout
    rw [if_pos hmC]
    have hcongr : (∫ t in C..M, stepInv m t) = ∫ t in C..M, 1 / t := by
      rw [intervalIntegral.integral_of_le hCM, intervalIntegral.integral_of_le hCM]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      rw [stepInv, if_pos (lt_of_le_of_lt hmC ht.1)]
    rw [hcongr, integral_one_div_of_pos hC hMpos]
  · rw [if_neg hmC]
    have hmC' : C < ((m : ℕ) : ℝ) := not_le.mp hmC
    by_cases hmM : ((m : ℕ) : ℝ) < M
    · -- `C < m < M`
      rw [if_pos hmM]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_stepInv m hm C ((m : ℕ) : ℝ))
        (intervalIntegrable_stepInv m hm ((m : ℕ) : ℝ) M)]
      have h0 : (∫ t in C..((m : ℕ) : ℝ), stepInv m t) = 0 := by
        refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall fun t ht => ?_)
        rw [Set.uIoc_of_le hmC'.le] at ht
        rw [stepInv, if_neg (not_lt.mpr ht.2)]
      have h1 : (∫ t in ((m : ℕ) : ℝ)..M, stepInv m t) = ∫ t in ((m : ℕ) : ℝ)..M, 1 / t := by
        rw [intervalIntegral.integral_of_le hmM.le, intervalIntegral.integral_of_le hmM.le]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        rw [stepInv, if_pos ht.1]
      rw [h0, zero_add, h1, integral_one_div_of_pos hmpos hMpos]
    · -- `M ≤ m`: the integrand vanishes
      rw [if_neg hmM]
      have hMm : M ≤ ((m : ℕ) : ℝ) := not_lt.mp hmM
      refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hCM] at ht
      rw [stepInv, if_neg (not_lt.mpr (le_trans ht.2 hMm))]

/-! ### The integral representation of `λ⁺` -/

/-- **§8, the integral representation of `λ⁺`**: for `2 ≤ c ≤ M` and `0 < C ≤ M`,
`λ⁺(c) = − ∫_C^M ρ(c;t)·t^{-1} dt`.  This is the `λ⁺`-analogue of `S8.lamMinus_eq_integral`
and is the device by which the `(B′)`-axiom (applied to the kernel `ρ(n;t)` with `t ≥ C`) also
controls the `λ⁺`-part of `S₃`. -/
theorem lamPlus_eq_neg_integral (c M : ℕ) {C : ℝ} (hc : 2 ≤ c) (hcM : c ≤ M)
    (hC : 0 < C) (hCM : C ≤ (M : ℝ)) :
    lamPlus c C = -∫ t in C..(M : ℝ), rhoTrunc c t / t := by
  classical
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have h1 : (1 : ℕ) ≤ M := le_trans (by norm_num : (1 : ℕ) ≤ 2) (le_trans hc hcM)
    exact_mod_cast h1
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  -- the a.e. identity `ρ(c;t)/t = ∑_{m ∣ c} μ(m)·1_{m<t}/t`
  set S : Set ℝ := (c.divisors : Set ℕ).image (fun m : ℕ => (m : ℝ)) with hS
  have hSfin : S.Finite := by
    rw [hS]
    exact (Finset.finite_toSet c.divisors).image (fun m : ℕ => (m : ℝ))
  have haeS : ∀ᵐ t ∂volume, t ∉ S :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hSfin.measure_zero volume)
  have hpt : ∀ t ∉ S, rhoTrunc c t / t
      = ∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ) * stepInv m t := by
    intro t htS
    have hne : ∀ m ∈ c.divisors, (m : ℝ) ≠ t := by
      intro m hm hmt
      exact htS (by rw [hS]; exact ⟨m, hm, hmt⟩)
    rw [rhoTrunc, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [stepInv]
    by_cases hle : ((m : ℕ) : ℝ) ≤ t
    · have hlt : ((m : ℕ) : ℝ) < t := lt_of_le_of_ne hle (hne m hm)
      rw [if_pos hle, if_pos hlt]
      ring
    · rw [if_neg hle, if_neg (not_lt.mpr (le_of_lt (not_le.mp hle)))]
      simp
  have hcongr : (∫ t in C..(M : ℝ), rhoTrunc c t / t)
      = ∫ t in C..(M : ℝ),
          ∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ) * stepInv m t := by
    rw [intervalIntegral.integral_of_le hCM, intervalIntegral.integral_of_le hCM]
    refine MeasureTheory.integral_congr_ae ?_
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc C (M : ℝ))),
      rhoTrunc c t / t = ∑ m ∈ c.divisors,
        (ArithmeticFunction.moebius m : ℝ) * stepInv m t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact haeS.mono (fun t htS _ => hpt t htS)
  rw [hcongr, intervalIntegral.integral_finsetSum (fun m hm =>
    (intervalIntegrable_stepInv m
      (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hm).1
        (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2)) C (M : ℝ)).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  -- the interval integrals
  have hkey : ∀ m ∈ c.divisors,
      -(∫ t in C..(M : ℝ), stepInv m t)
        - (if C < ((m : ℕ) : ℝ) then Real.log (((m : ℕ) : ℝ) / C) else 0)
        = -Real.log ((M : ℝ) / C) := by
    intro m hm
    have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hm).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2)
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmM : ((m : ℕ) : ℝ) ≤ (M : ℝ) := by
      have hle : m ≤ M := le_trans (Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hm).1) hcM
      exact_mod_cast hle
    rw [integral_stepInv_Ioc m hm1 hC hCM]
    by_cases h1 : ((m : ℕ) : ℝ) ≤ C
    · rw [if_pos h1, if_neg (not_lt.mpr h1)]
      ring
    · rw [if_neg h1, if_pos (not_le.mp h1)]
      by_cases h2 : ((m : ℕ) : ℝ) < M
      · rw [if_pos h2, Real.log_div (ne_of_gt hMpos) (ne_of_gt hmpos),
          Real.log_div (ne_of_gt hmpos) (ne_of_gt hC),
          Real.log_div (ne_of_gt hMpos) (ne_of_gt hC)]
        ring
      · rw [if_neg h2, ← le_antisymm hmM (not_lt.mp h2)]
        ring
  have hmu : (∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)) = 0 := by
    have h := sum_moebius_divisors_eq c
    rw [if_neg (by omega : ¬ (c = 1))] at h
    exact h
  have hterm : ∀ m ∈ c.divisors,
      -(∫ t in C..(M : ℝ), stepInv m t)
        = (if C < ((m : ℕ) : ℝ) then Real.log (((m : ℕ) : ℝ) / C) else 0)
            - Real.log ((M : ℝ) / C) := by
    intro m hm
    have := hkey m hm
    linarith
  have hsum : (∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
        * (-(∫ t in C..(M : ℝ), stepInv m t)))
      = (∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
          * (if C < ((m : ℕ) : ℝ) then Real.log (((m : ℕ) : ℝ) / C) else 0))
        - Real.log ((M : ℝ) / C) * (∑ m ∈ c.divisors,
            (ArithmeticFunction.moebius m : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hterm m hm]
    ring
  have hfin : (∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
        * (if C < ((m : ℕ) : ℝ) then Real.log (((m : ℕ) : ℝ) / C) else 0))
      = lamPlus c C := by
    rw [lamPlus, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases h : C < ((m : ℕ) : ℝ) <;> simp [h]
  symm
  calc -(∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
        * (∫ t in C..(M : ℝ), stepInv m t))
      = ∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
          * (-(∫ t in C..(M : ℝ), stepInv m t)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = (∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ)
          * (if C < ((m : ℕ) : ℝ) then Real.log (((m : ℕ) : ℝ) / C) else 0))
        - Real.log ((M : ℝ) / C) * (∑ m ∈ c.divisors,
            (ArithmeticFunction.moebius m : ℝ)) := hsum
    _ = lamPlus c C := by rw [hmu, mul_zero, sub_zero, hfin]

/-! ### The `λ⁺`-part of `S₃`: reindexing and the integral bound -/

/-- The inner `c`-sum of `S₃⁺` at a fixed `ℓ`: `∑_{z < c ≤ sz, ℓc ≤ N} λ⁺(c)·a(ℓc)`. -/
def S3plusInner (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
    lamPlus c C * a (ℓ * c)

/-- **§8**: the `(b,e)`-pair of `S₃⁺` is merged into `ℓ = b·e` (the `λ⁺`-analogue of
`S8b.S3minus_eq_reindex`). -/
theorem S3plus_eq_reindex (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) :
    S3plus a lam N z sy sz C
      = ∑ ℓ ∈ Finset.Icc 1 N,
          (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ))
            * rhoOf lam ℓ * S3plusInner a N ℓ z sz C := by
  classical
  set Cf : Finset ℕ := (Finset.Icc 1 N).filter
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz) with hCf
  have hA : S3plus a lam N z sy sz C
      = ∑ c ∈ Cf, lamPlus c C *
          ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ) *
              ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
                a (b * (c * e)) * rhoOf lam (b * e) := by
    unfold S3plus
    rw [hCf]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  rw [hA]
  rw [Finset.sum_congr rfl (fun c hc => by
    rw [sum_merge_be a lam N sy (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  set A : ℝ := (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
      (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ with hAdef
  have hset : Cf.filter (fun c => ℓ * c ≤ N)
      = (Finset.Icc 1 N).filter
          (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) := by
    rw [hCf, Finset.filter_filter]
    refine Finset.filter_congr (fun c _ => ?_)
    tauto
  have hsum : (∑ c ∈ Cf, lamPlus c C * (A * (if ℓ * c ≤ N then a (ℓ * c) else 0)))
      = ∑ c ∈ Cf.filter (fun c => ℓ * c ≤ N), lamPlus c C * (A * a (ℓ * c)) := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
  rw [hsum, hset, S3plusInner, hAdef]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => by ring)

/-- The inner `c`-sum of `S₃⁺` is bounded by the integral of the `(B′)`-integrand:
this is the `λ⁺`-analogue of `S8b.abs_Csum_le_integral`.  Here `M` is any natural number that
dominates every modulus in the sum (`c ≤ sz ≤ M` need not hold, only the integers `c ≤ sz` are
below `M`). -/
theorem abs_S3plusInner_le_integral (a : ℕ → ℝ) (N ℓ M : ℕ) (z sz C : ℝ)
    (hC : 0 < C) (hCM : C ≤ (M : ℝ)) (hz : 1 ≤ z)
    (hM : ∀ c : ℕ, ((c : ℕ) : ℝ) ≤ sz → c ≤ M)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    |S3plusInner a N ℓ z sz C| ≤ ∫ s in C..(M : ℝ), |Xrho a N ℓ s z sz| / s := by
  classical
  set Ch : Finset ℕ := (Finset.Icc 1 N).filter
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) with hCh
  have hmem : ∀ c ∈ Ch, 2 ≤ c ∧ c ≤ M := by
    intro c hc
    rw [hCh] at hc
    obtain ⟨-, hcz⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc2, hc3, -⟩ := hcz
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hcge : (1 : ℝ) < (c : ℝ) := lt_of_le_of_lt hz1 hc2
    have hc2' : 2 ≤ c := by exact_mod_cast hcge
    exact ⟨hc2', hM c hc3⟩
  -- Step 1: the sum is (minus) the integral of the `ρ`-weighted sum
  have hInt : (∑ c ∈ Ch, lamPlus c C * a (ℓ * c))
      = -∫ s in C..(M : ℝ), (∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c)) / s := by
    have hstep : (∑ c ∈ Ch, lamPlus c C * a (ℓ * c))
        = ∑ c ∈ Ch, -(∫ s in C..(M : ℝ), rhoTrunc c s / s) * a (ℓ * c) := by
      refine Finset.sum_congr rfl (fun c hc => ?_)
      obtain ⟨hc2, hcM⟩ := hmem c hc
      rw [lamPlus_eq_neg_integral c M hc2 hcM hC hCM]
    rw [hstep]
    have hfac : ∀ c ∈ Ch, -(∫ s in C..(M : ℝ), rhoTrunc c s / s) * a (ℓ * c)
        = -((∫ s in C..(M : ℝ), rhoTrunc c s / s) * a (ℓ * c)) :=
      fun c _ => by ring
    rw [Finset.sum_congr rfl hfac, Finset.sum_neg_distrib]
    congr 1
    have hcongr1 : (∫ s in C..(M : ℝ), (∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c)) / s)
        = ∫ s in C..(M : ℝ), ∑ c ∈ Ch, (rhoTrunc c s / s) * a (ℓ * c) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s _ => ?_))
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    rw [hcongr1]
    have hinter : ∀ c ∈ Ch, (∫ s in C..(M : ℝ), rhoTrunc c s / s) * a (ℓ * c)
        = ∫ s in C..(M : ℝ), rhoTrunc c s / s * a (ℓ * c) := by
      intro c _
      rw [show (fun s : ℝ => rhoTrunc c s / s * a (ℓ * c))
          = fun s : ℝ => a (ℓ * c) * (rhoTrunc c s / s) from by funext s; ring,
        intervalIntegral.integral_const_mul]
      ring
    rw [Finset.sum_congr rfl hinter]
    exact (intervalIntegral.integral_finsetSum (fun c _ =>
      (intervalIntegrable_div_Ioc (measurable_rhoTrunc c) hC hCM
        ((c.divisors.card : ℝ)) (fun s _ => abs_rhoTrunc_le c s)).mul_const _)).symm
  rw [S3plusInner, ← hCh, hInt, abs_neg]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hCM) ?_
  refine intervalIntegral.integral_mono_ae_restrict hCM ?_ ?_ ?_
  · -- integrability of the left-hand side
    refine (intervalIntegrable_div_Ioc (measurable_rhoCsum a Ch ℓ) hC hCM
      (∑ c ∈ Ch, (c.divisors.card : ℝ) * |a (ℓ * c)|) (fun s _ => ?_)).abs
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_rhoTrunc_le c s) (abs_nonneg _)
  · -- integrability of the right-hand side
    refine intervalIntegrable_div_Ioc (measurable_Xrho a N ℓ z sz).abs hC hCM
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|) (fun s _ => ?_)
    simpa using abs_Xrho_le a N ℓ s z sz
  · -- the pointwise bound
    change ∀ᵐ x ∂(volume.restrict (Set.Icc C (M : ℝ))),
        |(∑ c ∈ Ch, rhoTrunc c x * a (ℓ * c)) / x| ≤ |Xrho a N ℓ x z sz| / x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hC hs.1
    have hsum_eq : (∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c))
        = (ArithmeticFunction.moebius ℓ : ℝ) * Xrho a N ℓ s z sz := by
      have hterm : ∀ c : ℕ, rhoTrunc c s * a (ℓ * c)
          = (ArithmeticFunction.moebius ℓ : ℝ)
              * ((ArithmeticFunction.moebius c : ℝ) * rhoTrunc c s
                  * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c)) := by
        intro c
        conv_lhs => rw [a_eq_moebius_triple_mul_a ha ℓ c]
        ring
      have hsum2 : (∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * rhoTrunc c s
          * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c))
          = Xrho a N ℓ s z sz := by
        rw [Xrho_eq_sum_filter, hCh]
      rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum, hsum2]
    rw [hsum_eq, abs_div, abs_of_pos hs0, abs_mul]
    calc |(ArithmeticFunction.moebius ℓ : ℝ)| * |Xrho a N ℓ s z sz| / s
        ≤ 1 * |Xrho a N ℓ s z sz| / s := by
          gcongr
          exact abs_moebius_cast_le_one ℓ
      _ = |Xrho a N ℓ s z sz| / s := by ring

/-! ### §8 (8.3)–(8.4): the `λ⁺`-contribution to `S₃` -/

/-- The window hypothesis is monotone in the level bound. -/
lemma RhoWindow.mono_level {a : ℕ → ℝ} {N : ℕ} {w : ℕ → ℝ} {E C C' lo hi : ℝ}
    (h : RhoWindow a N w E C lo hi) (hC' : C' ≤ C) : RhoWindow a N w E C' lo hi :=
  fun s t hs1 hsC ht1 ht2 => h s t hs1 (le_trans hsC hC') ht1 ht2

/-- **§8 (8.3)–(8.4)**: the `λ⁺`-contribution to `S₃` is `≤ J·E·log(⌊sz⌋₊/C)` under the
`(B′)`-type hypothesis `RhoWindow` with levels up to `R ≥ ⌊sz⌋₊` (and `sz = 2^J z`). -/
theorem abs_S3plus_le (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) {w : ℕ → ℝ} {E R : ℝ} {J : ℕ}
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hz : 1 ≤ z) (hC : 1 ≤ C) (hCsz : C ≤ ((⌊sz⌋₊ : ℕ) : ℝ))
    (hsz : sz = (2 : ℝ) ^ J * z) (hR : ((⌊sz⌋₊ : ℕ) : ℝ) ≤ R) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      abs (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * abs (rhoOf lam ℓ) ≤ w ℓ)
    (hwin : RhoWindow a N w E R z sz) :
    abs (S3plus a lam N z sy sz C)
      ≤ (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ) / C) := by
  classical
  rw [S3plus_eq_reindex]
  -- Step 1: bound `(∑_{b∣ℓ} μ b)·ρ_ℓ` by `w ℓ`
  have h1 : abs (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * S3plusInner a N ℓ z sz C)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (S3plusInner a N ℓ z sz C) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ hℓ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hw ℓ (Finset.mem_Icc.mp hℓ).1) (abs_nonneg _)
  -- Step 2: each inner sum by its integral
  have h2 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (S3plusInner a N ℓ z sz C))
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ),
          abs (Xrho a N ℓ s z sz) / s) := by
    refine Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left ?_ (hw0 ℓ))
    exact abs_S3plusInner_le_integral a N ℓ ⌊sz⌋₊ z sz C (lt_of_lt_of_le zero_lt_one hC)
      hCsz hz (fun c hc => Nat.le_floor hc) ha
  -- Step 3: swap the `ℓ`-sum and the integral
  have hInt : ∀ ℓ : ℕ, IntervalIntegrable (fun s : ℝ => abs (Xrho a N ℓ s z sz) / s)
      volume C ((⌊sz⌋₊ : ℕ) : ℝ) := fun ℓ =>
    intervalIntegrable_div_Ioc (measurable_Xrho a N ℓ z sz).abs (lt_of_lt_of_le zero_lt_one hC)
      hCsz (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * abs (a (ℓ * n)))
      (fun s _ => by simpa using abs_Xrho_le a N ℓ s z sz)
  have h3 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ),
        abs (Xrho a N ℓ s z sz) / s))
      = ∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ),
          ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s) := by
    rw [Finset.sum_congr rfl (fun ℓ _ =>
      (intervalIntegral.integral_const_mul (w ℓ) (fun s => abs (Xrho a N ℓ s z sz) / s)).symm)]
    rw [intervalIntegral.integral_finsetSum (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))]
  -- Step 4: the pointwise bound (dyadic windows) at each level `s ∈ [C, ⌊sz⌋₊]`
  have hpt : ∀ s : ℝ, C ≤ s → s ≤ ((⌊sz⌋₊ : ℕ) : ℝ) →
      (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s)) ≤ ((J : ℝ) * E) / s := by
    intro s hsC hsM
    have hs0 : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hC) hsC
    have hs1 : 1 ≤ s := le_trans hC hsC
    have hsR : s ≤ R := le_trans hsM hR
    calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
        = (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (Xrho a N ℓ s z sz)) / s := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ ((J : ℝ) * E) / s :=
          div_le_div_of_nonneg_right
            (sum_w_Xrho_le a N z sz R (by linarith) hsz hw0 hwin s hs1 hsR) hs0.le
  -- Step 5: integrate
  have hIntSum : IntervalIntegrable (fun s : ℝ =>
      ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
      volume C ((⌊sz⌋₊ : ℕ) : ℝ) := by
    have hfun : (∑ ℓ ∈ Finset.Icc 1 N, fun x : ℝ => w ℓ * (abs (Xrho a N ℓ x z sz) / x))
        = fun s : ℝ => ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s) := by
      funext s
      rw [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))
  have hIntR : IntervalIntegrable (fun s : ℝ => ((J : ℝ) * E) / s) volume C
      ((⌊sz⌋₊ : ℕ) : ℝ) :=
    intervalIntegrable_div_Ioc measurable_const (lt_of_lt_of_le zero_lt_one hC) hCsz
      (abs ((J : ℝ) * E)) (fun s _ => by simp)
  have h4 : (∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ),
      ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
      ≤ (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ) / C) := by
    have hmono : (∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ),
        ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
        ≤ ∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ), ((J : ℝ) * E) / s := by
      refine intervalIntegral.integral_mono_ae_restrict hCsz hIntSum hIntR ?_
      change ∀ᵐ x ∂(volume.restrict (Set.Icc C ((⌊sz⌋₊ : ℕ) : ℝ))),
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ x z sz) / x)) ≤ ((J : ℝ) * E) / x
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun s hs => hpt s hs.1 hs.2)
    have hMpos : (0 : ℝ) < ((⌊sz⌋₊ : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans hC hCsz)
    have hval : (∫ s in C..((⌊sz⌋₊ : ℕ) : ℝ), ((J : ℝ) * E) / s)
        = (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ) / C) := by
      have hfun : (fun s : ℝ => ((J : ℝ) * E) / s)
          = fun s => ((J : ℝ) * E) * (1 / s) := by funext s; ring
      rw [hfun, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (lt_of_lt_of_le zero_lt_one hC) hMpos]
    rw [hval] at hmono
    exact hmono
  exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))

/-- **§8 (8.1) + (8.3)–(8.4) combined**: with a *single* `(B′)`-type hypothesis `RhoWindow` at
truncation levels up to `R ≥ ⌊sz⌋₊`, both halves of `S₃ = S₃⁻ − S₃⁺` satisfy their estimates, so
`|S₃⁻ − S₃⁺| ≤ J·E·log ⌊sz⌋₊`. -/
theorem abs_S3split_le (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) {w : ℕ → ℝ} {E R : ℝ} {J : ℕ}
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hz : 1 ≤ z) (hC : 1 ≤ C) (hCsz : C ≤ ((⌊sz⌋₊ : ℕ) : ℝ))
    (hsz : sz = (2 : ℝ) ^ J * z) (hR : ((⌊sz⌋₊ : ℕ) : ℝ) ≤ R) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      abs (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * abs (rhoOf lam ℓ) ≤ w ℓ)
    (hwin : RhoWindow a N w E R z sz) :
    abs (S3minus a lam N z sy sz C - S3plus a lam N z sy sz C)
      ≤ (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ)) := by
  have hminus := abs_S3minus_le a lam N z sy sz C ha (lt_of_lt_of_le zero_lt_one hz) hC hsz hw0 hw
    (hwin.mono_level (le_trans hCsz hR))
  have hplus := abs_S3plus_le a lam N z sy sz C ha hz hC hCsz hsz hR hw0 hw hwin
  have hCne : C ≠ 0 := (ne_of_gt (lt_of_lt_of_le zero_lt_one hC))
  have hMne : (((⌊sz⌋₊ : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans hC hCsz))
  calc abs (S3minus a lam N z sy sz C - S3plus a lam N z sy sz C)
      ≤ abs (S3minus a lam N z sy sz C) + abs (S3plus a lam N z sy sz C) := abs_sub _ _
    _ ≤ (J : ℝ) * E * Real.log C
          + (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ) / C) := add_le_add hminus hplus
    _ = (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ)) := by
        rw [Real.log_div hMne hCne]
        ring

/-- **§8 (8.5)**: `S₃(x;y,z) = O(J·E·log ⌊sz⌋₊)` under the `(B′)`-type hypothesis `RhoWindow`
at truncation levels up to `R ≥ ⌊sz⌋₊`. -/
theorem abs_S3_le (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) (Δ : ℕ)
    {w : ℕ → ℝ} {E R : ℝ} {J : ℕ}
    (ha : ∀ n, ¬ Squarefree n → a n = 0) (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hΔz : (Δ : ℝ) < z) (hz : 1 ≤ z) (hC : 1 ≤ C) (hCsz : C ≤ ((⌊sz⌋₊ : ℕ) : ℝ))
    (hsz : sz = (2 : ℝ) ^ J * z) (hR : ((⌊sz⌋₊ : ℕ) : ℝ) ≤ R) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      abs (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * abs (rhoOf lam ℓ) ≤ w ℓ)
    (hwin : RhoWindow a N w E R z sz) :
    abs (S3 a lam N z sy sz) ≤ (J : ℝ) * E * Real.log (((⌊sz⌋₊ : ℕ) : ℝ)) := by
  rw [S3_eq_S3minus_sub_S3plus a lam N z sy sz C Δ ha hlam_supp hΔz hz
    (lt_of_lt_of_le zero_lt_one hC)]
  exact abs_S3split_le a lam N z sy sz C ha hz hC hCsz hsz hR hw0 hw hwin

end

end Submission.ASP
