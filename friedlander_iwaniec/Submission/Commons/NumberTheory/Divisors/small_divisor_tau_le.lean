import Mathlib
import Submission.Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le
import Submission.Commons.Data.Nat.card_divisors_mul_of_coprime

set_option maxHeartbeats 1000000

open Finset

namespace Commons.NumberTheory.Divisors

/-- Factorization of a product of prime powers over a finset of primes. -/
lemma factorization_finset_prod_pow {s : Finset ℕ} {e : ℕ → ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (p : ℕ) :
    (∏ q ∈ s, q ^ e q).factorization p = if p ∈ s then e p else 0 := by
  have hne : ∀ q ∈ s, q ^ e q ≠ 0 := fun q hq => pow_ne_zero _ (hs q hq).ne_zero
  have hfac : (∏ q ∈ s, q ^ e q).factorization = ∑ q ∈ s, Finsupp.single q (e q) := by
    rw [Nat.factorization_prod hne]
    refine Finset.sum_congr rfl ?_
    intro q hq
    rw [Nat.factorization_pow, (hs q hq).factorization, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hfac, Finsupp.finsetSum_apply]
  rw [show (∑ i ∈ s, (Finsupp.single i (e i)) p) = ∑ i ∈ s, (if i = p then e i else 0) from
    Finset.sum_congr rfl (fun i _ => Finsupp.single_apply)]
  rw [Finset.sum_ite_eq']

/-- Prime factors of a product of positive powers of primes. -/
lemma primeFactors_finset_prod_pow {s : Finset ℕ} {e : ℕ → ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (he : ∀ p ∈ s, 0 < e p) :
    (∏ p ∈ s, p ^ e p).primeFactors = s := by
  have hP0 : (∏ p ∈ s, p ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hpp, hdvd, _⟩
    have hfac : (∏ q ∈ s, q ^ e q).factorization p ≠ 0 := by
      rw [Ne, Nat.factorization_eq_zero_iff]
      rintro (h1 | h1 | h1)
      · exact h1 hpp
      · exact h1 hdvd
      · exact hP0 h1
    rw [factorization_finset_prod_pow hs] at hfac
    by_cases hp : p ∈ s
    · exact hp
    · rw [if_neg hp] at hfac; exact absurd rfl hfac
  · intro hp
    refine ⟨hs p hp, ?_, hP0⟩
    have h1 : p ^ e p ∣ ∏ q ∈ s, q ^ e q := dvd_prod_of_mem _ hp
    have h2 : p ∣ p ^ e p := by simpa using pow_dvd_pow p (Nat.one_le_iff_ne_zero.mpr (he p hp).ne')
    exact dvd_trans h2 h1

/-- Divisor count of a product of prime powers. -/
lemma card_divisors_finset_prod_pow {s : Finset ℕ} {e : ℕ → ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (he : ∀ p ∈ s, 0 < e p) :
    (∏ p ∈ s, p ^ e p).divisors.card = ∏ p ∈ s, (e p + 1) := by
  have hP0 : (∏ p ∈ s, p ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)
  rw [Nat.card_divisors hP0, primeFactors_finset_prod_pow hs he]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [factorization_finset_prod_pow hs, if_pos hp]

/-- `k * m ≤ m ^ k` for `m ≥ 2`, `k ≥ 1`. -/
lemma mul_le_pow_self {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) : k * m ≤ m ^ k := by
  have h2k : k ≤ 2 ^ (k - 1) := by have := Nat.lt_two_pow_self (n := k - 1); omega
  calc k * m ≤ m ^ (k - 1) * m := by
        apply Nat.mul_le_mul_right
        exact le_trans h2k (Nat.pow_le_pow_left hm _)
    _ = m ^ k := by
        conv_rhs => rw [show k = k - 1 + 1 by omega, pow_succ]

/-- Element-wise inequality `α + 1 ≤ (α / k + 1) ^ k` for `k ≤ α`. -/
lemma le_pow_div_add_one {k α : ℕ} (hk : 0 < k) (hα : k ≤ α) :
    α + 1 ≤ (α / k + 1) ^ k := by
  have hmod : α % k < k := Nat.mod_lt α hk
  have hq : 1 ≤ α / k := (Nat.one_le_div_iff hk).mpr hα
  have hαeq : α = k * (α / k) + α % k := (Nat.div_add_mod α k).symm
  have hstep : α + 1 ≤ k * (α / k + 1) := by
    have h1 : α + 1 = k * (α / k) + α % k + 1 := by nth_rewrite 1 [hαeq]; ring
    rw [h1]
    have : α % k + 1 ≤ k := by omega
    nlinarith
  exact le_trans hstep (mul_le_pow_self (by omega) (by omega))

/-- Real-power comparison: if `2 ^ r ≤ c ^ k` with `k ≥ 2` and `c ≥ 1`
then `k ^ r ≤ c ^ (k * logb 2 k)`. -/
lemma pow_nat_le_rpow_of_le {r k : ℕ} {c : ℝ} (hk : 2 ≤ k) (hc : 1 ≤ c)
    (h : (2:ℝ) ^ r ≤ c ^ k) : (k:ℝ) ^ r ≤ c ^ ((k:ℝ) * Real.logb 2 k) := by
  have hlogb : 0 ≤ Real.logb 2 k :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h2 : (2:ℝ) ^ Real.logb 2 k = (k:ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hk0
  calc (k:ℝ) ^ r = ((2:ℝ) ^ Real.logb 2 k) ^ r := by rw [h2]
    _ = ((2:ℝ) ^ Real.logb 2 k) ^ (r:ℝ) := by rw [Real.rpow_natCast]
    _ = (2:ℝ) ^ (Real.logb 2 k * r) := by rw [Real.rpow_mul (by norm_num)]
    _ = (2:ℝ) ^ (r * Real.logb 2 k) := by rw [mul_comm]
    _ = ((2:ℝ) ^ (r:ℝ)) ^ Real.logb 2 k := by rw [Real.rpow_mul (by norm_num)]
    _ = ((2:ℝ) ^ r) ^ Real.logb 2 k := by rw [Real.rpow_natCast]
    _ ≤ (c ^ (k:ℝ)) ^ Real.logb 2 k := by
        refine Real.rpow_le_rpow (by positivity) ?_ hlogb
        rw [Real.rpow_natCast]; exact h
    _ = c ^ ((k:ℝ) * Real.logb 2 k) := by rw [Real.rpow_mul hc0]

theorem small_divisor_tau_le {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧
      (n.divisors.card : ℝ)
        ≤ (2 * (d.divisors.card : ℝ)) ^ ((k : ℝ) * Real.log (k : ℝ) / Real.log 2) := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : 0 < k := by omega
  set Sp : Finset ℕ := n.primeFactors.filter (fun p => k ≤ n.factorization p) with hSp
  set Tp : Finset ℕ := n.primeFactors.filter (fun p => ¬ k ≤ n.factorization p) with hTp
  have hSp_mem : ∀ p, p ∈ Sp ↔ p ∈ n.primeFactors ∧ k ≤ n.factorization p := by
    intro p; rw [hSp, Finset.mem_filter]
  have hTp_mem : ∀ p, p ∈ Tp ↔ p ∈ n.primeFactors ∧ ¬ k ≤ n.factorization p := by
    intro p; rw [hTp, Finset.mem_filter]
  have hprim : ∀ p ∈ Sp, Nat.Prime p := fun p hp => by
    have h := (hSp_mem p).mp hp
    exact (Nat.mem_primeFactors.mp h.1).1
  have hprimT : ∀ p ∈ Tp, Nat.Prime p := fun p hp => by
    have h := (hTp_mem p).mp hp
    exact (Nat.mem_primeFactors.mp h.1).1
  have hSge : ∀ p ∈ Sp, k ≤ n.factorization p := fun p hp => ((hSp_mem p).mp hp).2
  have hSpos : ∀ p ∈ Sp, 0 < n.factorization p := fun p hp => by have := hSge p hp; omega
  have hTlt : ∀ p ∈ Tp, n.factorization p < k := fun p hp => by
    have := ((hTp_mem p).mp hp).2; omega
  have hTpos : ∀ p ∈ Tp, 0 < n.factorization p := fun p hp => by
    have h1 := (hTp_mem p).mp hp
    have hpp := (Nat.mem_primeFactors.mp h1.1).1
    have hdvd := (Nat.mem_primeFactors.mp h1.1).2.1
    exact Nat.pos_of_ne_zero (by
      intro h0
      rw [Nat.factorization_eq_zero_iff] at h0
      rcases h0 with h | h | h
      · exact h hpp
      · exact h hdvd
      · exact hn0 h)
  set L : ℕ := ∏ p ∈ Sp, p ^ n.factorization p with hL
  set M : ℕ := ∏ p ∈ Tp, p ^ n.factorization p with hM
  set DL : ℕ := ∏ p ∈ Sp, p ^ (n.factorization p / k) with hDL
  set RD : ℕ := ∏ p ∈ Tp, p ^ 1 with hRD
  have hL0 : L ≠ 0 := by
    rw [hL]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprim p hp).ne_zero)
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprimT p hp).ne_zero)
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hRD0 : RD ≠ 0 := by
    rw [hRD]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprimT p hp).ne_zero)
  have hRD1 : 1 ≤ RD := Nat.one_le_iff_ne_zero.mpr hRD0
  have hRDsq : Squarefree RD := by
    rw [Nat.squarefree_iff_factorization_le_one hRD0]
    intro p
    rw [hRD, factorization_finset_prod_pow hprimT]
    split <;> omega
  obtain ⟨DM, hdmdvd, hdmpow, hdmcard⟩ :=
    Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le RD k hk hRDsq hRD1
  -- n splits as L * M
  have hLM : L * M = n := by
    rw [hL, hM, hSp, hTp]
    rw [Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => k ≤ n.factorization p) (fun p => p ^ n.factorization p)]
    rw [← Nat.prod_primeFactors_pow_factorization hn0]
  -- divisor count identities
  have htl : L.divisors.card = ∏ p ∈ Sp, (n.factorization p + 1) := by
    rw [hL]; exact card_divisors_finset_prod_pow hprim hSpos
  have htm : M.divisors.card = ∏ p ∈ Tp, (n.factorization p + 1) := by
    rw [hM]; exact card_divisors_finset_prod_pow hprimT hTpos
  have htdl : DL.divisors.card = ∏ p ∈ Sp, (n.factorization p / k + 1) := by
    rw [hDL]
    exact card_divisors_finset_prod_pow hprim
      (fun p hp => Nat.div_pos (hSge p hp) hk0)
  have htR : RD.divisors.card = 2 ^ Tp.card := by
    rw [hRD, card_divisors_finset_prod_pow hprimT (fun p _ => Nat.one_pos),
      Finset.prod_const]
  have htn : n.divisors.card = L.divisors.card * M.divisors.card := by
    rw [Nat.card_divisors hn0, htl, htm, hSp, hTp]
    exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => k ≤ n.factorization p) (fun p => n.factorization p + 1)).symm
  -- arithmetic inequalities (ℕ)
  have hl_le : L.divisors.card ≤ DL.divisors.card ^ k := by
    rw [htl, htdl, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) ?_
    intro p hp
    exact le_pow_div_add_one hk0 (hSge p hp)
  have hm_le : M.divisors.card ≤ k ^ Tp.card := by
    rw [htm]
    calc ∏ p ∈ Tp, (n.factorization p + 1) ≤ ∏ p ∈ Tp, k := by
          refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) ?_
          intro p hp; have := hTlt p hp; omega
      _ = k ^ Tp.card := Finset.prod_const k
  have hRle : 2 ^ Tp.card ≤ (2 * DM.divisors.card) ^ k := by rw [← htR]; exact hdmcard
  -- divisibility / power facts for d = DL * DM
  have hDLdvd : DL ∣ L := by
    rw [hDL, hL]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p hp
    exact pow_dvd_pow p (Nat.div_le_self _ _)
  have hRDdvd : RD ∣ M := by
    rw [hRD, hM]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p hp
    exact pow_dvd_pow p (Nat.one_le_iff_ne_zero.mpr (hTpos p hp).ne')
  have hRDle : RD ≤ M := Nat.le_of_dvd hMpos hRDdvd
  have hdvd : (DL * DM) ∣ n := by
    rw [← hLM]
    exact mul_dvd_mul hDLdvd (dvd_trans hdmdvd hRDdvd)
  have hDLpow : DL ^ k ≤ L := by
    rw [hDL, hL, ← Finset.prod_pow]
    refine Nat.le_of_dvd hLpos (Finset.prod_dvd_prod_of_dvd _ _ ?_)
    intro p hp
    rw [← pow_mul]
    exact pow_dvd_pow p (Nat.div_mul_le_self _ _)
  have hdpow : (DL * DM) ^ k ≤ n := by
    rw [mul_pow, ← hLM]
    exact mul_le_mul hDLpow (le_trans hdmpow hRDle) (Nat.zero_le _) (Nat.zero_le _)
  refine ⟨DL * DM, hdvd, hdpow, ?_⟩
  -- coprimality
  have hdlR : Nat.Coprime DL RD := by
    rw [hDL, hRD]
    refine Nat.Coprime.prod_left ?_
    intro p hp
    refine Nat.Coprime.prod_right ?_
    intro q hq
    have hpne : p ≠ q := by
      intro hpq
      have h1 := hSge q (hpq ▸ hp)
      have h2 := ((hTp_mem q).mp hq).2
      omega
    rw [pow_one]
    exact ((Nat.coprime_primes (hprim p hp) (hprimT q hq)).mpr hpne).pow_left _
  have hdlm : Nat.Coprime DL DM := hdlR.coprime_dvd_right hdmdvd
  have hdd : (DL * DM).divisors.card = DL.divisors.card * DM.divisors.card :=
    Commons.Data.Nat.card_divisors_mul_of_coprime DL DM hdlm
  -- real arithmetic
  set K : ℝ := (k : ℝ) * Real.log (k : ℝ) / Real.log 2 with hK
  have hKlogb : K = (k:ℝ) * Real.logb 2 k := by
    rw [hK]; simp only [Real.logb]; ring
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 1 ≤ Real.log (k:ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have : Real.log 2 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    linarith
  have hKge : (k:ℝ) ≤ K := by
    rw [hK]
    calc (k:ℝ) = (k:ℝ) * 1 := by ring
      _ ≤ (k:ℝ) * (Real.log (k:ℝ) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (k:ℝ) * Real.log (k:ℝ) / Real.log 2 := by ring
  have hDL0 : DL ≠ 0 := by
    rw [hDL]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprim p hp).ne_zero)
  have hDM0 : DM ≠ 0 := by
    intro h'
    rw [h'] at hdmdvd
    exact hRD0 (zero_dvd_iff.mp hdmdvd)
  have hA1 : (1:ℝ) ≤ (DL.divisors.card : ℝ) := by
    have h1 : 1 ≤ DL.divisors.card := by
      have := (card_pos).mpr ⟨1, Nat.one_mem_divisors.mpr hDL0⟩
      omega
    exact_mod_cast h1
  have hB1 : (1:ℝ) ≤ (DM.divisors.card : ℝ) := by
    have h1 : 1 ≤ DM.divisors.card := by
      have := (card_pos).mpr ⟨1, Nat.one_mem_divisors.mpr hDM0⟩
      omega
    exact_mod_cast h1
  have hlR : (L.divisors.card : ℝ) ≤ (DL.divisors.card : ℝ) ^ k := by
    exact_mod_cast hl_le
  have hmR : (M.divisors.card : ℝ) ≤ (2 * (DM.divisors.card : ℝ)) ^ K := by
    have h1 : (2:ℝ) ^ Tp.card ≤ (2 * (DM.divisors.card : ℝ)) ^ k := by
      exact_mod_cast hRle
    have h2 : (M.divisors.card : ℝ) ≤ (k:ℝ) ^ Tp.card := by
      exact_mod_cast hm_le
    have h3 : (k:ℝ) ^ Tp.card ≤ (2 * (DM.divisors.card : ℝ)) ^ K := by
      have := pow_nat_le_rpow_of_le hk (by linarith [hB1]) h1
      rwa [hKlogb]
    linarith
  have hAK : (DL.divisors.card : ℝ) ^ k ≤ (DL.divisors.card : ℝ) ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hKge
  calc (n.divisors.card : ℝ)
      = (L.divisors.card : ℝ) * (M.divisors.card : ℝ) := by rw [htn]; push_cast; ring
    _ ≤ (DL.divisors.card : ℝ) ^ k * (2 * (DM.divisors.card : ℝ)) ^ K :=
        mul_le_mul hlR hmR (by positivity) (by positivity)
    _ ≤ (DL.divisors.card : ℝ) ^ K * (2 * (DM.divisors.card : ℝ)) ^ K :=
        mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (by positivity) K)
    _ = (2 * ((DL * DM).divisors.card : ℝ)) ^ K := by
        rw [hdd]; push_cast
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        ring

end Commons.NumberTheory.Divisors
