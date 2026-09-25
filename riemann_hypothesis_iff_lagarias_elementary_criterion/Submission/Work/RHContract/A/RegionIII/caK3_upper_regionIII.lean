import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.R3.caC_ge
import Submission.Work.RHContract.A.R3.prime_log_div_sub_one_sum_le
import Submission.Work.RHContract.A.RegionIII.caK3_numeric_end

namespace Work.RHContract.A.RegionIII

open scoped BigOperators

noncomputable section

/-- `V ξ = (1/2)·ξ^{−1/4} + 6·ξ^{−1/2}`: the slack `1 − c_lo ξ · ξ · log ξ` in the
per-summand estimate of the `K₃` bound. -/
def caV (ξ : ℝ) : ℝ := (1 / 2) * ξ ^ (-(1 / 4 : ℝ)) + 6 * ξ ^ (-(1 / 2 : ℝ))

/-- `c_lo ξ = (1 − V ξ)/(ξ log ξ)`, the explicit lower bound for `Margin.caC ε` obtained
from `Work.RHContract.A.R3.caC_ge_real`. -/
def caClo (ξ : ℝ) : ℝ := (1 - caV ξ) / (ξ * Real.log ξ)

/-! ## Elementary lemmas -/

/-- `((10:ℝ)^8)^{−1/2} = 1/10000`. -/
lemma ten_pow_eight_rpow_neg_half : ((10 : ℝ) ^ 8) ^ (-(1 / 2 : ℝ)) = 1 / 10000 := by
  rw [← Real.rpow_natCast (10 : ℝ) 8]
  rw [← Real.rpow_mul (x := (10 : ℝ)) (by norm_num) ((8 : ℕ) : ℝ) (-(1 / 2 : ℝ))]
  norm_num

/-- `ξ^{−1/2} ≤ 1/10000` for `ξ ≥ 10^8`. -/
lemma rpow_neg_half_le {ξ : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ) :
    ξ ^ (-(1 / 2 : ℝ)) ≤ 1 / 10000 :=
  calc ξ ^ (-(1 / 2 : ℝ)) ≤ ((10 : ℝ) ^ 8) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hξ (by norm_num)
    _ = 1 / 10000 := ten_pow_eight_rpow_neg_half

/-- `V ξ ≥ 0` for `ξ ≥ 0`. -/
lemma caV_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ caV ξ := by
  unfold caV
  have h1 : 0 ≤ ξ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hξ _
  have h2 : 0 ≤ ξ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hξ _
  linarith

/-- `V ξ ≤ 1` for `ξ ≥ 10^8`. -/
lemma caV_le_one {ξ : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ) : caV ξ ≤ 1 := by
  have hq : ξ ^ (-(1 / 4 : ℝ)) ≤ 1 / 100 :=
    le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hξ (by norm_num))
      (le_of_eq Work.RHContract.A.R3.ten_pow_eight_rpow_neg_quarter)
  have hh : ξ ^ (-(1 / 2 : ℝ)) ≤ 1 / 10000 := rpow_neg_half_le hξ
  unfold caV
  linarith

/-- `log 3 ≤ 11056/10000`, via `exp (11056/10000) ≥ 3` (seven terms of the exponential series). -/
lemma log_three_le_d : Real.log 3 ≤ (11056 : ℝ) / 10000 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (11056 : ℝ) / 10000) 7
  have hval : (3 : ℝ)
      ≤ ∑ i ∈ Finset.range 7, ((11056 : ℝ) / 10000) ^ i / ((Nat.factorial i : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- `caSum` is monotone in the level. -/
lemma caSum_mono_le (k : ℕ) {y : ℝ} (hy : 0 ≤ y) (hk : 3 ≤ k) :
    Work.RHContract.A.caSum 3 y ≤ Work.RHContract.A.caSum k y := by
  unfold Work.RHContract.A.caSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk) ?_
  intro i _ _
  exact pow_nonneg hy (i + 1)

/-- `caFf k p ≤ caFf 3 p` for primes `p ≥ 2` and `k ≥ 3`. -/
lemma caFf_le_three (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 3 ≤ k) :
    Work.RHContract.A.caFf k (p : ℝ) ≤ Work.RHContract.A.caFf 3 (p : ℝ) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hS3 : 0 < Work.RHContract.A.caSum 3 (p : ℝ) :=
    Work.RHContract.A.caSum_pos 3 (by norm_num) hp0
  have hSk : 0 < Work.RHContract.A.caSum k (p : ℝ) :=
    Work.RHContract.A.caSum_pos k (by omega) hp0
  have hmono := caSum_mono_le k (le_of_lt hp0) hk
  have h1 : 1 / Work.RHContract.A.caSum k (p : ℝ) ≤ 1 / Work.RHContract.A.caSum 3 (p : ℝ) :=
    one_div_le_one_div_of_le hS3 hmono
  unfold Work.RHContract.A.caFf
  refine div_le_div_of_nonneg_right ?_ (le_of_lt hlogp)
  have hx : (0 : ℝ) < 1 + 1 / Work.RHContract.A.caSum k (p : ℝ) := by positivity
  exact Real.log_le_log hx (by linarith)

/-- `caG (1.23·ξ) < ε` for `ξ = caXi ε ≥ 1530`. -/
lemma caG_mul_xi_lt (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHContract.A.caG (1.23 * (Work.RHPlan.caXi ε : ℝ)) < ε := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ1 : 1 < ξ := by linarith
  obtain ⟨q, hqprime, hξltq, hqle⟩ := Commons.NumberTheory.Primes.prime_gap_123 ξ hξ
  have hq2 : 2 ≤ q := hqprime.two_le
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqpos : 0 < (q : ℝ) := by linarith
  have hqG : Work.RHContract.A.caG (q : ℝ) < ε := by
    by_contra hcon
    push Not at hcon
    have hmu1 := (Work.RHContract.A.caMu_ge_iff_caFf q hq2 ε hε 1 le_rfl).mpr
      (by rwa [Work.RHContract.A.caFf_one])
    have hqfloor : 1 ≤ ⌊Work.RHPlan.caMu q ε⌋₊ := Nat.le_floor hmu1
    rcases lt_or_ge q (Work.RHContract.A.caK ε) with hqK | hqK
    · have hqmem : q ∈ Work.RHPlan.caSupport ε := by
        rw [Work.RHPlan.caSupport]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqK, hqprime⟩, hqfloor⟩
      have hle : q ≤ Work.RHPlan.caXi ε := Finset.le_sup (f := id) hqmem
      have hcast : (q : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by exact_mod_cast hle
      have hlt : (Work.RHPlan.caXi ε : ℝ) < (q : ℝ) := by rw [← hξdef]; exact hξltq
      exact absurd hcast (not_le.mpr hlt)
    · have hqexp : Real.exp (2 / ε) < (q : ℝ) := by
        have h2 : (Work.RHContract.A.caK ε : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqK
        rw [Work.RHContract.A.caK] at h2
        push_cast at h2
        have hc := Nat.le_ceil (Real.exp (2 / ε))
        linarith
      have hlogq : 2 / ε < Real.log (q : ℝ) := by
        have := Real.log_lt_log (Real.exp_pos (2 / ε)) hqexp
        rwa [Real.log_exp] at this
      have hbound : Work.RHContract.A.caG (q : ℝ)
          ≤ 1 / ((q : ℝ) * Real.log (q : ℝ)) := by
        unfold Work.RHContract.A.caG
        have hlog1 : Real.log (1 + 1 / (q : ℝ)) ≤ 1 / (q : ℝ) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (q : ℝ) by positivity)
          linarith
        have hlogqpos : 0 < Real.log (q : ℝ) := by
          have h2e : (0 : ℝ) < 2 / ε := by positivity
          linarith
        calc Real.log (1 + 1 / (q : ℝ)) / Real.log (q : ℝ)
            ≤ (1 / (q : ℝ)) / Real.log (q : ℝ) :=
              div_le_div_of_nonneg_right hlog1 (le_of_lt hlogqpos)
          _ = 1 / ((q : ℝ) * Real.log (q : ℝ)) := by field_simp
      have hlt : 1 / ((q : ℝ) * Real.log (q : ℝ)) < ε := by
        have hq2r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
        have hpos : 0 < (q : ℝ) * Real.log (q : ℝ) := by
          have hh : 0 < Real.log (q : ℝ) := by
            have h2e : (0 : ℝ) < 2 / ε := by positivity
            linarith
          exact mul_pos hqpos hh
        rw [div_lt_iff₀ hpos]
        have h2e : (2 : ℝ) < Real.log (q : ℝ) * ε := (div_lt_iff₀ hε).mp hlogq
        have h1 : (q : ℝ) * 2 < (q : ℝ) * (Real.log (q : ℝ) * ε) :=
          mul_lt_mul_of_pos_left h2e hqpos
        nlinarith [h1, hq2r]
      linarith [hcon, hbound, hlt]
  have hGbig : Work.RHContract.A.caG (1.23 * ξ) ≤ Work.RHContract.A.caG (q : ℝ) := by
    have h1 : (1.23 : ℝ) * ξ ∈ Set.Ioi (1 : ℝ) := by
      simp only [Set.mem_Ioi]; nlinarith [hξ1]
    have h2 : (q : ℝ) ∈ Set.Ioi (1 : ℝ) := by simp only [Set.mem_Ioi]; exact hq1
    have hqx1 : (q : ℝ) ≤ 1.23 * ξ := by
      have hd : (1.23 : ℝ) = 123 / 100 := by norm_num
      rw [hd]; exact hqle
    have hanti := Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
    have := (hanti.le_iff_ge h1 h2).mpr hqx1
    simpa [Work.RHContract.A.caG] using this
  exact lt_of_le_of_lt hGbig hqG

/-- `c_lo ξ ≤ Margin.caC ε` from the ψ-envelope at `ξ = caXi ε ≥ 10^8`. -/
lemma caClo_le_caC (ε : ℝ) {ξ : ℝ} (hξdef : ξ = (Work.RHPlan.caXi ε : ℝ))
    (hξ : (10 : ℝ) ^ 8 ≤ ξ)
    (hψ : |Chebyshev.psi ξ - ξ| ≤ 0.45 * ξ ^ (3 / 4 : ℝ) + 2) :
    caClo ξ ≤ Work.RHContract.Margin.caC ε := by
  rw [hξdef] at hξ hψ ⊢
  unfold Work.RHContract.Margin.caC
  have h := Work.RHContract.A.R3.caC_ge_real (Work.RHPlan.caXi ε : ℝ) hξ hψ
  have he : caClo (Work.RHPlan.caXi ε : ℝ)
      = (1 - (1 / 2) * (Work.RHPlan.caXi ε : ℝ) ^ (-(1 / 4 : ℝ))
          - 6 * (Work.RHPlan.caXi ε : ℝ) ^ (-(1 / 2 : ℝ)))
        / ((Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ)) := by
    unfold caClo caV
    ring
  rw [he]
  exact h

/-- Structural facts about a contributing prime `p` of `Margin.caK3 ε` at `ξ = caXi ε ≥ 10^8`:
`p ≥ 2`, `p ≤ (3.69ξ)^{1/3}` and `ξ < p^{e_p+1}`. -/
lemma caK3_index_bounds (ε : ℝ) (hε : 0 < ε) {ξ : ℝ} (hξdef : ξ = (Work.RHPlan.caXi ε : ℝ))
    (hξ : (10 : ℝ) ^ 8 ≤ ξ) {p : ℕ}
    (hp : p ∈ (Nat.primesLE ⌊Real.sqrt ξ⌋₊).filter
        (fun q : ℕ => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊)) :
    (2 ≤ p) ∧ (p ≤ ⌊(3.69 * ξ) ^ (1 / 3 : ℝ)⌋₊) ∧
      (ξ < (p : ℝ) ^ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) := by
  have hξ0 : 0 < ξ := by norm_num at hξ; linarith
  have hξ1 : 1 < ξ := by linarith
  have hp_mem1 : p ∈ Nat.primesLE ⌊Real.sqrt ξ⌋₊ := (Finset.mem_filter.mp hp).1
  have hp_cond : Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊ :=
    (Finset.mem_filter.mp hp).2
  have hp_prime : Nat.Prime p := (Nat.mem_primesLE.mp hp_mem1).2
  have hp_le : p ≤ ⌊Real.sqrt ξ⌋₊ := (Nat.mem_primesLE.mp hp_mem1).1
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp1r : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : 0 < (p : ℝ) := by linarith
  have hxi_pos_nat : 0 < Work.RHPlan.caXi ε := by
    have : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by rw [← hξdef]; linarith
    exact_mod_cast this
  have hp2le : p ^ 2 ≤ Work.RHPlan.caXi ε := by
    have h1 : (p : ℝ) ^ 2 ≤ ξ := by
      have hle1 : (p : ℝ) ≤ ((⌊Real.sqrt ξ⌋₊ : ℕ) : ℝ) := by exact_mod_cast hp_le
      have hle2 : ((⌊Real.sqrt ξ⌋₊ : ℕ) : ℝ) ≤ Real.sqrt ξ :=
        Nat.floor_le (Real.sqrt_nonneg ξ)
      have hnn : (0 : ℝ) ≤ ((⌊Real.sqrt ξ⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (p : ℝ) ^ 2 ≤ ((⌊Real.sqrt ξ⌋₊ : ℕ) : ℝ) ^ 2 := by nlinarith
        _ ≤ (Real.sqrt ξ) ^ 2 := by nlinarith [Real.sqrt_nonneg ξ]
        _ = ξ := Real.sq_sqrt (le_of_lt hξ0)
    have h2 : (((p ^ 2 : ℕ)) : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
      rw [← hξdef]; push_cast; exact h1
    exact_mod_cast h2
  have he2 : 2 ≤ Work.RHContract.Margin.caExpFloor ε p := by
    rw [Work.RHContract.Margin.caExpFloor, Nat.floor_natCast]
    exact (Nat.le_log_iff_pow_le (by omega : 1 < p) (ne_of_gt hxi_pos_nat)).mpr hp2le
  have hk3 : 3 ≤ Work.RHContract.Margin.caExpFloor ε p + 1 := by omega
  have hpow : ξ < (p : ℝ) ^ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) := by
    have h : Work.RHPlan.caXi ε < p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
      rw [Work.RHContract.Margin.caExpFloor, Nat.floor_natCast]
      exact Nat.lt_pow_succ_log_self (by omega : 1 < p) (Work.RHPlan.caXi ε)
    have h' : (Work.RHPlan.caXi ε : ℝ) < (((p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) : ℕ)) : ℝ) := by
      exact_mod_cast h
    have hcast : (((p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) : ℕ)) : ℝ)
        = (p : ℝ) ^ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (Work.RHContract.Margin.caExpFloor ε p + 1)]
      push_cast
      rfl
    rw [hcast, ← hξdef] at h'
    exact h'
  have hG : Work.RHContract.A.caG (1.23 * ξ) < ε := by
    rw [hξdef]
    exact caG_mul_xi_lt ε hε (by rw [← hξdef]; norm_num at hξ; linarith)
  have hμpos : 0 < Work.RHPlan.caMu p ε := Commons.NumberTheory.Robin.caMu_pos hp2 hε
  have hmu_ge : ((Work.RHContract.Margin.caExpFloor ε p + 1 : ℕ) : ℝ) ≤ Work.RHPlan.caMu p ε :=
    le_trans (by exact_mod_cast (by omega : Work.RHContract.Margin.caExpFloor ε p + 1
      ≤ ⌊Work.RHPlan.caMu p ε⌋₊)) (Nat.floor_le (le_of_lt hμpos))
  have hεFf : ε ≤ Work.RHContract.A.caFf (Work.RHContract.Margin.caExpFloor ε p + 1) (p : ℝ) :=
    (Work.RHContract.A.caMu_ge_iff_caFf p hp2 ε hε _ (by omega)).mp hmu_ge
  have hεFf3 : ε ≤ Work.RHContract.A.caFf 3 (p : ℝ) :=
    le_trans hεFf (caFf_le_three p hp2 _ hk3)
  have hp3le : (p : ℝ) ^ 3 ≤ 3.69 * ξ := by
    have h := Work.RHContract.A.caG_le_caFf_imp (1.23 * ξ) (p : ℝ) (by nlinarith [hξ1]) hp1r 3
      (by norm_num) (le_trans (le_of_lt hG) hεFf3)
    nlinarith [h, hξ0]
  have hcbrt : ((p : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (p : ℝ) := by
    rw [show ((p : ℝ) ^ 3) = (p : ℝ) ^ (((3 : ℕ)) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_mul (le_of_lt hp0r),
      show (((3 : ℕ)) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
  have hfloor_le : p ≤ ⌊(3.69 * ξ) ^ (1 / 3 : ℝ)⌋₊ := by
    have hple : (p : ℝ) ≤ (3.69 * ξ) ^ (1 / 3 : ℝ) := by
      rw [← hcbrt]
      exact Real.rpow_le_rpow (by positivity) hp3le (by norm_num)
    exact Nat.le_floor hple
  exact ⟨hp2, hfloor_le, hpow⟩

/-- **Per-summand bound.**  For a prime `p ≥ 2` with `ξ < p^{e_p+1}`, writing `k = e_p + 1`,

`max 0 (p^{−k}/(k(1−1/p)) − c(ε) log p) ≤ (1/(kξ))·(1/(p−1) + V ξ)`. -/
lemma caK3_summand_le (ε : ℝ) {ξ : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ)
    (hClo : caClo ξ ≤ Work.RHContract.Margin.caC ε)
    {p : ℕ} (hp2 : 2 ≤ p)
    (hpow : ξ < (p : ℝ) ^ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) :
    max 0 ((p : ℝ) ^ (-((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)) /
              (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
            - Work.RHContract.Margin.caC ε * Real.log (p : ℝ))
      ≤ (1 / (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * ξ))
          * (1 / ((p : ℝ) - 1) + caV ξ) := by
  set e : ℕ := Work.RHContract.Margin.caExpFloor ε p with he
  set K : ℝ := ((e : ℕ) : ℝ) + 1 with hK
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hξ0 : 0 < ξ := by norm_num at hξ; linarith
  have hξ1 : 1 < ξ := by linarith
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ1
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (le_of_lt hp1)
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKlogp : Real.log ξ ≤ K * Real.log (p : ℝ) := by
    have h1 : Real.log ξ < Real.log ((p : ℝ) ^ K) := Real.log_lt_log hξ0 hpow
    rw [Real.log_rpow hp0] at h1
    linarith
  have hpkpos : 0 < (p : ℝ) ^ K := Real.rpow_pos_of_pos hp0 K
  have hVin : 0 ≤ 1 - caV ξ := by have := caV_le_one hξ; linarith
  have hsub1 : 0 < 1 - 1 / (p : ℝ) := by
    have h : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
    linarith
  have hinv : (p : ℝ) ^ (-K) ≤ 1 / ξ := by
    rw [Real.rpow_neg (le_of_lt hp0) K, one_div]
    exact (inv_le_inv₀ hpkpos hξ0).mpr (le_of_lt hpow)
  have hcV : caClo ξ * Real.log (p : ℝ) = (1 - caV ξ) * Real.log (p : ℝ) / (ξ * Real.log ξ) := by
    unfold caClo; ring
  have hkey : (1 / (K * ξ)) * (1 - caV ξ)
      ≤ (1 - caV ξ) * Real.log (p : ℝ) / (ξ * Real.log ξ) := by
    have hcore : 1 / (K * ξ) ≤ Real.log (p : ℝ) / (ξ * Real.log ξ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hKlogp, le_of_lt hKpos, le_of_lt hξ0, le_of_lt hlogξ]
    calc (1 / (K * ξ)) * (1 - caV ξ) ≤ (Real.log (p : ℝ) / (ξ * Real.log ξ)) * (1 - caV ξ) :=
          mul_le_mul_of_nonneg_right hcore hVin
      _ = (1 - caV ξ) * Real.log (p : ℝ) / (ξ * Real.log ξ) := by ring
  have hpp : 0 < (p : ℝ) - 1 := by linarith
  have hYnn : 0 ≤ (1 / (K * ξ)) * (1 / ((p : ℝ) - 1) + caV ξ) := by
    have h1 : (0 : ℝ) ≤ 1 / (K * ξ) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
    have h3 : (0 : ℝ) ≤ caV ξ := caV_nonneg (le_of_lt hξ0)
    exact mul_nonneg h1 (by linarith)
  have hmain : (p : ℝ) ^ (-K) / (K * (1 - 1 / (p : ℝ)))
      - Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
      ≤ (1 / (K * ξ)) * (1 / ((p : ℝ) - 1) + caV ξ) := by
    have step1 : (p : ℝ) ^ (-K) / (K * (1 - 1 / (p : ℝ)))
        ≤ (1 / (K * ξ)) * (1 + 1 / ((p : ℝ) - 1)) := by
      have h2 : (p : ℝ) ^ (-K) / (K * (1 - 1 / (p : ℝ)))
          ≤ (1 / ξ) / (K * (1 - 1 / (p : ℝ))) :=
        div_le_div_of_nonneg_right hinv (le_of_lt (mul_pos hKpos hsub1))
      have h3 : (1 / ξ) / (K * (1 - 1 / (p : ℝ))) = (1 / (K * ξ)) * (1 / (1 - 1 / (p : ℝ))) := by
        field_simp
      have h4 : 1 / (1 - 1 / (p : ℝ)) = 1 + 1 / ((p : ℝ) - 1) := by
        field_simp
        ring
      rw [h3, h4] at h2
      exact h2
    have h2 : caClo ξ * Real.log (p : ℝ)
        ≤ Work.RHContract.Margin.caC ε * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hClo hlogp
    have step2 : (1 / (K * ξ)) * (1 - caV ξ)
        ≤ Work.RHContract.Margin.caC ε * Real.log (p : ℝ) := by
      rw [hcV] at h2
      linarith [hkey, h2]
    have h5 : (1 / (K * ξ)) * (1 + 1 / ((p : ℝ) - 1)) - (1 / (K * ξ)) * (1 - caV ξ)
        = (1 / (K * ξ)) * (1 / ((p : ℝ) - 1) + caV ξ) := by ring
    linarith [step1, step2, h5]
  exact max_le hYnn hmain

/-- **`Margin.caK3 ε ≤ (1/100)·u(ξ)` in the region `ξ = caXi ε ≥ 10^8`**,
`u ξ = 1/(√ξ log ξ)` (no `RiemannHypothesis` needed: the envelope hypothesis `hA2` suffices).

`Margin.caK3 ε = ∑_{p ≤ √ξ, e_p < a_p} max 0 (p^{−(e_p+1)}/((e_p+1)(1−1/p)) − caC ε·log p)`
with `e_p = Margin.caExpFloor ε p` and `a_p = ⌊Work.RHPlan.caMu p ε⌋₊`, the sum running over the
primes `p ∈ (Nat.primesLE ⌊√ξ⌋₊)`.

Every summand with `k := e_p + 1` obeys `ξ < p^k`, hence
`max 0 (p^{−k}/(k(1−1/p)) − caC ε log p) ≤ (1/(kξ))(1/(p−1) + V ξ)` with
`V ξ = ξ^{−1/4}/2 + 6ξ^{−1/2}` and `caClo ξ = (1 − V ξ)/(ξ log ξ) ≤ caC ε`; moreover `k ≥ 3`
and `caG(1.23ξ) < ε` force `p^3 ≤ 3.69 ξ`, so that `p ≤ (3.69ξ)^{1/3}` and hence
`log p ≤ log((3.69ξ)^{1/3})`.  Bounding `1/k ≤ log p/log ξ` and summing the resulting prime
sums with `∑_{p ≤ N} log p/(p−1) ≤ log 3 (log N + 2)` and `θ(N) ≤ log 3 · N` gives
`caK3 ε ≤ (1/(ξ log ξ))·(3 log((3.69ξ)^{1/3}) + 10 + 1.5 (3.69ξ)^{1/3} V ξ) ≤ (1/100)u(ξ)`. -/
theorem caK3_upper_regionIII (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hA2 : ∀ t : ℝ, Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2) :
    Work.RHContract.Margin.caK3 ε ≤ (1 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ8 : (10 : ℝ) ^ 8 ≤ ξ := hξ
  have hξ0 : 0 < ξ := by norm_num at hξ8; linarith
  have hξ1 : 1 < ξ := by linarith
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ1
  -- envelope at `t = ξ`
  have hψ : |Chebyshev.psi ξ - ξ| ≤ 0.45 * ξ ^ (3 / 4 : ℝ) + 2 := by
    refine hA2 ξ ?_
    rw [hξdef]
    have h1 : 1 ≤ Real.sqrt ξ := by
      have := Real.sqrt_le_sqrt (le_of_lt hξ1)
      rwa [Real.sqrt_one] at this
    calc Real.sqrt ξ = 1 * Real.sqrt ξ := (one_mul _).symm
      _ ≤ Real.sqrt ξ * Real.sqrt ξ :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg ξ)
      _ = ξ := Real.mul_self_sqrt (le_of_lt hξ0)
  have hClo : caClo ξ ≤ Work.RHContract.Margin.caC ε := caClo_le_caC ε hξdef hξ8 hψ
  -- the contributing primes and the cut-off `M = ⌊(3.69 ξ)^{1/3}⌋`
  set S : Finset ℕ := (Nat.primesLE ⌊Real.sqrt ξ⌋₊).filter
      (fun q : ℕ => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊) with hSdef
  set M : ℕ := ⌊(3.69 * ξ) ^ (1 / 3 : ℝ)⌋₊ with hMdef
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    have h2eq : (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← Real.rpow_natCast (2 : ℝ) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show (((3 : ℕ)) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hmain : (2 : ℝ) ≤ (3.69 * ξ) ^ (1 / 3 : ℝ) := by
      rw [h2eq]
      exact Real.rpow_le_rpow (by norm_num) (by linarith [hξ8]) (by norm_num)
    exact Nat.le_floor hmain
  have hMsub : ∀ p ∈ S, p ∈ Nat.primesLE M := by
    intro p hp
    obtain ⟨hp2, hpM, -⟩ := caK3_index_bounds ε hε hξdef hξ8 hp
    exact Nat.mem_primesLE.mpr ⟨hpM, (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2⟩
  have hcaK3 : Work.RHContract.Margin.caK3 ε = ∑ p ∈ S, max 0
      ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
              (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
            - Work.RHContract.Margin.caC ε * Real.log (p : ℝ)) := by
    rw [Work.RHContract.Margin.caK3, hSdef, hξdef]
  -- ### step 1: the per-summand bound
  have hstep1 : Work.RHContract.Margin.caK3 ε ≤
      ∑ p ∈ S, (1 / (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * ξ))
        * (1 / ((p : ℝ) - 1) + caV ξ) := by
    rw [hcaK3]
    refine Finset.sum_le_sum ?_
    intro p hp
    obtain ⟨hp2, hpM, hpow⟩ := caK3_index_bounds ε hε hξdef hξ8 hp
    exact caK3_summand_le ε hξ8 hClo hp2 hpow
  -- ### step 2: replace `1/k_p` by `log p / log ξ`
  have hstep2 : ∑ p ∈ S, (1 / (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * ξ))
        * (1 / ((p : ℝ) - 1) + caV ξ)
      ≤ ∑ p ∈ S, (Real.log (p : ℝ) / (Real.log ξ * ξ))
        * (1 / ((p : ℝ) - 1) + caV ξ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    obtain ⟨hp2, hpM, hpow⟩ := caK3_index_bounds ε hε hξdef hξ8 hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hXnn : 0 ≤ 1 / ((p : ℝ) - 1) + caV ξ := by
      have h1 : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
      have h2 := caV_nonneg (le_of_lt hξ0)
      linarith
    have hKpos : 0 < ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) := by positivity
    have hKlp : Real.log ξ
        < ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * Real.log (p : ℝ) := by
      have h := Real.log_lt_log hξ0 hpow
      rwa [Real.log_rpow hp0] at h
    have hker : 1 / (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * ξ)
        ≤ Real.log (p : ℝ) / (Real.log ξ * ξ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hKlp, hξ0, hlogξ, hKpos]
    exact mul_le_mul_of_nonneg_right hker hXnn
  -- ### step 3: factor out the constant `1/(log ξ · ξ)`
  have hstep3 : ∑ p ∈ S, (Real.log (p : ℝ) / (Real.log ξ * ξ))
        * (1 / ((p : ℝ) - 1) + caV ξ)
      = (1 / (Real.log ξ * ξ)) * ∑ p ∈ S, Real.log (p : ℝ)
        * (1 / ((p : ℝ) - 1) + caV ξ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  have hstep4 : ∑ p ∈ S, Real.log (p : ℝ) * (1 / ((p : ℝ) - 1) + caV ξ)
      = (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1))
        + caV ξ * ∑ p ∈ S, Real.log (p : ℝ) := by
    have hsplit : ∀ p ∈ S, Real.log (p : ℝ) * (1 / ((p : ℝ) - 1) + caV ξ)
        = Real.log (p : ℝ) / ((p : ℝ) - 1) + (caV ξ * Real.log (p : ℝ)) := by
      intro p _
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- ### step 4: the two prime sums
  have hA : ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)
      ≤ Real.log 3 * (Real.log (M : ℝ) + 2) := by
    have hle : ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ p ∈ Nat.primesLE M, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hMsub ?_
      intro i hi _
      have hi2 : 2 ≤ i := (Nat.mem_primesLE.mp hi).2.two_le
      have : (0 : ℝ) < (i : ℝ) - 1 := by
        have : (1 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 1 < i)
        linarith
      positivity
    exact le_trans hle (Work.RHContract.A.R3.prime_log_div_sub_one_sum_le M hM2)
  have hB : ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log 3 * (M : ℝ) := by
    have hle : ∑ p ∈ S, Real.log (p : ℝ) ≤ ∑ p ∈ Nat.primesLE M, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hMsub ?_
      intro i hi _
      exact Real.log_nonneg (by
        have h2 : 2 ≤ i := (Nat.mem_primesLE.mp hi).2.two_le
        exact_mod_cast (by omega : 1 ≤ i))
    refine le_trans hle ?_
    have htheta : ∑ p ∈ Nat.primesLE M, Real.log (p : ℝ) = Chebyshev.theta (M : ℝ) := by
      rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
    rw [htheta]
    exact Commons.NumberTheory.Chebyshev.theta_le_log3_mul M
  -- ### step 5: assemble the two sums into the numeric endpoint
  have hMle : (M : ℝ) ≤ (3.69 * ξ) ^ (1 / 3 : ℝ) := by
    rw [hMdef]
    exact Nat.floor_le (by positivity)
  have hlogM : Real.log (M : ℝ) ≤ Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) :=
    Real.log_le_log (by positivity) hMle
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hfnn : 0 ≤ Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) :=
    Real.log_nonneg (Real.one_le_rpow (by linarith [hξ8]) (by norm_num))
  have hAB : (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + caV ξ * ∑ p ∈ S, Real.log (p : ℝ)
      ≤ 3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
        + (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ := by
    have h1 : ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)
        ≤ (11056 / 10000) * (Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 2) := by
      have h2 : Real.log 3 * (Real.log (M : ℝ) + 2)
          ≤ (11056 / 10000) * (Real.log (M : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right log_three_le_d (by have := Real.log_nonneg hMone; linarith)
      have h3 : (11056 / 10000) * (Real.log (M : ℝ) + 2)
          ≤ (11056 / 10000) * (Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hlogM]) (by norm_num)
      linarith [hA, h2, h3]
    have h2 : caV ξ * ∑ p ∈ S, Real.log (p : ℝ)
        ≤ (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ := by
      have hV := caV_nonneg (le_of_lt hξ0)
      have hb : ∑ p ∈ S, Real.log (p : ℝ)
          ≤ (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) := by
        have h3 : Real.log 3 * (M : ℝ) ≤ (11056 / 10000) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right log_three_le_d (Nat.cast_nonneg M)
        have h4 : (11056 / 10000) * (M : ℝ)
            ≤ (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hMle (by norm_num)
        linarith [hB, h3, h4]
      calc caV ξ * ∑ p ∈ S, Real.log (p : ℝ)
          ≤ caV ξ * ((11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hb hV
        _ = (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ := by ring
    have hV := caV_nonneg (le_of_lt hξ0)
    linarith [h1, h2, hfnn, hV]
  -- ### step 6: close with the numeric endpoint
  have hnum := caK3_numeric_end ξ hξ8
  have hLpos : 0 < Real.log ξ * ξ := mul_pos hlogξ hξ0
  have hfinal : (1 / (Real.log ξ * ξ))
        * (3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
          + (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ)
      ≤ (1 / 100) * (1 / (Real.sqrt ξ * Real.log ξ)) := by
    simp only [caV] at *
    have hmul := mul_le_mul_of_nonneg_left hnum (le_of_lt (one_div_pos.mpr hLpos))
    have heq : (1 / (Real.log ξ * ξ)) * ((1 / 100) * Real.sqrt ξ)
        = (1 / 100) * (1 / (Real.sqrt ξ * Real.log ξ)) := by
      field_simp
      rw [Real.sq_sqrt (le_of_lt hξ0)]
    calc (1 / (Real.log ξ * ξ)) * (3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
          + (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ))
            * ((1 / 2) * ξ ^ (-(1 / 4 : ℝ)) + 6 * ξ ^ (-(1 / 2 : ℝ))))
        ≤ (1 / (Real.log ξ * ξ)) * ((1 / 100) * Real.sqrt ξ) := hmul
      _ = (1 / 100) * (1 / (Real.sqrt ξ * Real.log ξ)) := heq
  have hstep5 : Work.RHContract.Margin.caK3 ε
      ≤ (1 / (Real.log ξ * ξ))
          * (3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
            + (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ) := by
    refine le_trans hstep1 (le_trans hstep2 ?_)
    rw [hstep3, hstep4]
    exact mul_le_mul_of_nonneg_left hAB (by positivity)
  calc Work.RHContract.Margin.caK3 ε
      ≤ (1 / (Real.log ξ * ξ))
          * (3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
            + (11056 / 10000) * ((3.69 * ξ) ^ (1 / 3 : ℝ)) * caV ξ) := hstep5
    _ ≤ (1 / 100) * (1 / (Real.sqrt ξ * Real.log ξ)) := hfinal
    _ = (1 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
          * Real.log (Work.RHPlan.caXi ε : ℝ))) := by rw [hξdef]

end

end Work.RHContract.A.RegionIII
