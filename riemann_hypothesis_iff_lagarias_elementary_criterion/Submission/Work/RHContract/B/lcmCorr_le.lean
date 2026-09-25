import Mathlib
import Submission.Work.RHContract.B.lcm_transfer_defs

/-!
# `Work.RHContract.B.lcmCorr_le`

The elementary bound on the correction term `B_L` of the `lcm`-transfer (ROUTE_LEAD §3.1):

  `lcmCorr x ≤ 5 / √x`  for `x ≥ 100`.

Writing `N = ⌊x⌋₊`, `M = Nat.sqrt N` and `e_p = Nat.log p N` (the exponent of `p` in
`lcm(1..N)`), the sum splits into primes `p` with `p² ≤ N` and primes with `p² > N`:

* `p² ≤ N` (at most `M` such primes, since `p ≤ M`): here `p^{e_p+1} > N`, so each term is
  `< 1/N`; the whole block is at most `M/N ≤ 1/M` (as `M² ≤ N`).
* `p² > N`: then `e_p = 1`, so the term is exactly `1/p²`, and
  `∑_{p²>N} 1/p² ≤ ∑_{n ∈ (M, N]} 1/n² ≤ 1/M` (Mathlib `sum_Ioc_inv_sq_le_sub`).

Together with the bound `-log (1 - t) ≤ 2t` for `0 ≤ t ≤ 1/2` this gives `lcmCorr x ≤ 4/M`,
and `4/M ≤ 5/√x` because `M ≥ √N - 1 ≥ (9/10)√N` while `x < N + 1 ≤ (101/100)N`.
-/

namespace Work.RHContract.B

/-- For `0 ≤ t ≤ 1/2` one has `-log (1 - t) ≤ 2t`. -/
lemma neg_log_one_sub_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ 2 * t := by
  have h1t : 0 < 1 - t := by linarith
  have hlog : -Real.log (1 - t) = Real.log (1 / (1 - t)) := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  have hmain : Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : 1 / (1 - t) - 1 = t / (1 - t) := by
    field_simp
    ring
  calc Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 := hmain
    _ = t / (1 - t) := h2
    _ = t * (1 / (1 - t)) := by ring
    _ ≤ t * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ ht0
        rw [div_le_iff₀ h1t]; linarith
    _ = 2 * t := by ring

theorem lcmCorr_le (x : ℝ) (hx : 100 ≤ x) : Work.RHContract.B.lcmCorr x ≤ 5 / Real.sqrt x := by
  have hN100 : 100 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hNpos : 0 < ⌊x⌋₊ := by omega
  have hNne : ⌊x⌋₊ ≠ 0 := by omega
  have hNposR : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hNpos
  have hNge : (100 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN100
  have hxpos : (0 : ℝ) < x := by linarith
  have hsqrtN : (10 : ℝ) ≤ Real.sqrt (⌊x⌋₊ : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hM10 : 10 ≤ Nat.sqrt ⌊x⌋₊ := by
    rw [Nat.le_sqrt]; simpa using hN100
  have hMposR : (0 : ℝ) < (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    have : 0 < Nat.sqrt ⌊x⌋₊ := by omega
    exact_mod_cast this
  -- per term bound: `-log (1 - p^{-(e_p+1)}) ≤ 2 p^{-(e_p+1)}`
  have hterm : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      -Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))
        ≤ 2 * (1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) := by
    intro p hp
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp
    have hp1 : 1 < p := by omega
    have hpN : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE hp
    have he1 : 1 ≤ Nat.log p ⌊x⌋₊ :=
      (Nat.le_log_iff_pow_le hp1 hNne).mpr (by simpa using hpN)
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpow4 : (4 : ℝ) ≤ (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by
      have h2 : 2 ≤ Nat.log p ⌊x⌋₊ + 1 := by omega
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (p : ℝ) ^ 2 := by nlinarith [sq_nonneg ((p : ℝ) - 2)]
        _ ≤ (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := pow_le_pow_right₀ hpR h2
    have ht0 : 0 ≤ 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by positivity
    have ht : 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) ≤ 1 / 2 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) hpow4
      linarith
    exact neg_log_one_sub_le_two_mul ht0 ht
  -- split the sum at `p * p ≤ ⌊x⌋₊`
  have hsum : ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)
      = (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊),
            1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))
        + (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊),
            1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE ⌊x⌋₊) (fun p => p * p ≤ ⌊x⌋₊)
      (fun p => 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))]
  -- small primes: at most `M` of them, each term `< 1/N`, hence the block is `≤ M/N ≤ 1/M`
  have hsmall : (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊),
      1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) ≤ 1 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    have hstep : ∀ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊),
        1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) ≤ 1 / (⌊x⌋₊ : ℝ) := by
      intro p hp
      have hpN : p ∈ Nat.primesLE ⌊x⌋₊ := (Finset.mem_filter.mp hp).1
      have hp1 : 1 < p := by have := Nat.two_le_of_mem_primesLE hpN; omega
      have hlt : ⌊x⌋₊ < p ^ (Nat.log p ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self hp1 ⌊x⌋₊
      have hle : (⌊x⌋₊ : ℝ) ≤ (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by exact_mod_cast hlt.le
      exact one_div_le_one_div_of_le hNposR hle
    have hcard : (((Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊)).card : ℝ)
        ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) := by
      have hc : ((Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊)).card ≤ Nat.sqrt ⌊x⌋₊ := by
        have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊)
            ⊆ Finset.Icc 1 (Nat.sqrt ⌊x⌋₊) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          refine Finset.mem_Icc.mpr ⟨?_, Nat.le_sqrt.mpr hp.2⟩
          have := Nat.two_le_of_mem_primesLE hp.1
          omega
        calc ((Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊)).card
            ≤ (Finset.Icc 1 (Nat.sqrt ⌊x⌋₊)).card := Finset.card_le_card hsub
          _ = Nat.sqrt ⌊x⌋₊ := by simp
      exact_mod_cast hc
    have hM2 : ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) * ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      simpa [pow_two] using (show ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) from by
        exact_mod_cast Nat.sqrt_le' ⌊x⌋₊)
    calc (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊),
            1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))
        ≤ ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊), (1 / (⌊x⌋₊ : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = (((Nat.primesLE ⌊x⌋₊).filter (fun p => p * p ≤ ⌊x⌋₊)).card : ℝ) * (1 / (⌊x⌋₊ : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) * (1 / (⌊x⌋₊ : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 1 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
          rw [mul_one_div, le_div_iff₀ hMposR, div_mul_eq_mul_div, div_le_iff₀ hNposR]
          simpa using hM2
  -- large primes: `e_p = 1`, the block is `∑ 1/n²` over `(M, N]`, at most `1/M`
  have hlarge : (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊),
      1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) ≤ 1 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    have hstep : ∀ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊),
        1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) = ((p : ℝ) ^ 2)⁻¹ := by
      intro p hp
      have hpN : p ∈ Nat.primesLE ⌊x⌋₊ := (Finset.mem_filter.mp hp).1
      have hpp : ¬ p * p ≤ ⌊x⌋₊ := (Finset.mem_filter.mp hp).2
      have hpNle : p ≤ ⌊x⌋₊ := Nat.le_of_mem_primesLE hpN
      have hp1 : 1 < p := by have := Nat.two_le_of_mem_primesLE hpN; omega
      have he : Nat.log p ⌊x⌋₊ = 1 := by
        have hle : 1 ≤ Nat.log p ⌊x⌋₊ :=
          (Nat.le_log_iff_pow_le hp1 hNne).mpr (by simpa using hpNle)
        have hlt : Nat.log p ⌊x⌋₊ < 2 :=
          (Nat.log_lt_iff_lt_pow hp1 hNne).mpr (by
            have : ⌊x⌋₊ < p * p := lt_of_not_ge hpp
            simpa [pow_two] using this)
        omega
      rw [he, one_div]
    have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊)
        ⊆ Finset.Ioc (Nat.sqrt ⌊x⌋₊) ⌊x⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine Finset.mem_Ioc.mpr ⟨?_, Nat.le_of_mem_primesLE hp.1⟩
      exact lt_of_not_ge (fun h => hp.2 (Nat.le_sqrt.mp h))
    have hMN : Nat.sqrt ⌊x⌋₊ ≤ ⌊x⌋₊ := by
      have h : Nat.sqrt ⌊x⌋₊ * Nat.sqrt ⌊x⌋₊ ≤ ⌊x⌋₊ := by
        simpa [pow_two] using Nat.sqrt_le' ⌊x⌋₊
      calc Nat.sqrt ⌊x⌋₊ = 1 * Nat.sqrt ⌊x⌋₊ := (one_mul _).symm
        _ ≤ Nat.sqrt ⌊x⌋₊ * Nat.sqrt ⌊x⌋₊ := Nat.mul_le_mul_right _ (by omega)
        _ ≤ ⌊x⌋₊ := h
    have hMne : Nat.sqrt ⌊x⌋₊ ≠ 0 := by omega
    calc (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊),
            1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))
        = ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬ p * p ≤ ⌊x⌋₊), ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_congr rfl hstep
      _ ≤ ∑ n ∈ Finset.Ioc (Nat.sqrt ⌊x⌋₊) ⌊x⌋₊, ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ ≤ 1 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
          have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := Nat.sqrt ⌊x⌋₊) (n := ⌊x⌋₊) hMne hMN
          have hfin : (((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ))⁻¹ - ((⌊x⌋₊ : ℝ))⁻¹
              ≤ 1 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
            have : (0 : ℝ) ≤ ((⌊x⌋₊ : ℝ))⁻¹ := by positivity
            rw [one_div]; linarith
          linarith
  -- `4 / M ≤ 5 / √x`
  have hfinal : 4 / (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ 5 / Real.sqrt x := by
    rw [div_le_div_iff₀ hMposR (Real.sqrt_pos_of_pos hxpos)]
    have h1 : Real.sqrt x ≤ (21 / 20) * Real.sqrt (⌊x⌋₊ : ℝ) := by
      have hxN : x ≤ (101 / 100) * (⌊x⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one x
        linarith
      calc Real.sqrt x ≤ Real.sqrt ((101 / 100) * (⌊x⌋₊ : ℝ)) := Real.sqrt_le_sqrt hxN
        _ = Real.sqrt (101 / 100) * Real.sqrt (⌊x⌋₊ : ℝ) := Real.sqrt_mul (by norm_num) _
        _ ≤ (21 / 20) * Real.sqrt (⌊x⌋₊ : ℝ) := by
            have h : Real.sqrt (101 / 100) ≤ 21 / 20 := by
              rw [Real.sqrt_le_iff]; norm_num
            exact mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (⌊x⌋₊ : ℝ) - 1 ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) := by
      have hnat : ⌊x⌋₊ < (Nat.sqrt ⌊x⌋₊ + 1) * (Nat.sqrt ⌊x⌋₊ + 1) := by
        simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt ⌊x⌋₊
      have hcast : (⌊x⌋₊ : ℝ) < ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) ^ 2 := by
        have h : (⌊x⌋₊ : ℝ)
            < ((Nat.sqrt ⌊x⌋₊ + 1 : ℕ) : ℝ) * ((Nat.sqrt ⌊x⌋₊ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h
        simpa [pow_two] using h
      have hsqrtlt : Real.sqrt (⌊x⌋₊ : ℝ) < (Nat.sqrt ⌊x⌋₊ : ℝ) + 1 :=
        (Real.sqrt_lt' (by positivity)).mpr hcast
      linarith
    linarith
  have hone : ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)
      ≤ 2 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    rw [hsum]
    have h2 : (1 : ℝ) / (Nat.sqrt ⌊x⌋₊ : ℝ) + 1 / (Nat.sqrt ⌊x⌋₊ : ℝ)
        = 2 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by ring
    linarith [hsmall, hlarge]
  calc Work.RHContract.B.lcmCorr x
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) := rfl
    _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, 2 * (1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) :=
        (Finset.mul_sum _ _ 2).symm
    _ ≤ 2 * (2 / (Nat.sqrt ⌊x⌋₊ : ℝ)) := by linarith
    _ = 4 / (Nat.sqrt ⌊x⌋₊ : ℝ) := by ring
    _ ≤ 5 / Real.sqrt x := hfinal

end Work.RHContract.B
