import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.caC1_cert_defs
import Submission.Work.RHContract.A.regionII.caC1_cert_CU_facts
import Submission.Work.RHContract.A.regionII.tailsFrom_mem
import Submission.Work.RHContract.A.regionII.caC1_tail_arith
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.Corpus

/-!
# `Margin.caC1 ε ≥ (43/100) · u(ξ)` in region II, part B

For `ξ = caXi ε ∈ [10^5, 10^8)` and `n = ⌊√(2.5 ξ)⌋₊ + 1`, `ξ₂(ε) ≤ n` and `10^5 ≤ ξ`, so

`caC1 ε = ∑_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³)) ≥ ∑_{n < q ≤ 10^5, q prime} (1/(2q²) − 1/(3q³))`.

The right-hand side is a decreasing step function of the cut-off `n` and the requirement
`(43/100)·u(ξ) ≤ (right-hand side)`, `u(ξ) = 1/(√ξ log ξ)`, is hardest exactly at the cut-offs
`j ∈ {501, 503, 509, …, 15809}`.  The finite integer certificate of `caC1_cert_defs`
(the `decide` check `cert_check`) verifies the arithmetic inequality at each of those cut-offs;
this file extracts it and assembles the result.
-/

set_option maxRecDepth 100000

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket
open scoped BigOperators

noncomputable section

/-! ## 1. The scaled excess is a lower bound for the excess -/

/-- `⌊10^40 c1 q⌋` never exceeds `10^40 c1 q`, where `c1 q = 1/(2q²) − 1/(3q³)`. -/
lemma c1num_le_scaled (q : ℕ) (hq : 0 < q) :
    (c1num q : ℝ) ≤ certScale * (1 / (2 * (q : ℝ) ^ 2) - 1 / (3 * (q : ℝ) ^ 3)) := by
  have hq2 : 2 ≤ 3 * q := by omega
  have hqr : (q : ℝ) ≠ 0 := by positivity
  have hcast : ((3 * q - 2 : ℕ) : ℝ) = 3 * (q : ℝ) - 2 := by
    rw [Nat.cast_sub (R := ℝ) hq2]
    push_cast
    ring
  have hden : ((6 * q ^ 3 : ℕ) : ℝ) = 6 * (q : ℝ) ^ 3 := by push_cast; ring
  have hmain : (c1num q : ℝ)
      ≤ ((3 * q - 2 : ℕ) : ℝ) * (certScale : ℝ) / ((6 * q ^ 3 : ℕ) : ℝ) := by
    rw [c1num]
    have h := Nat.cast_div_le (α := ℝ) (m := (3 * q - 2) * certScale) (n := 6 * q ^ 3)
    have h2 : (((3 * q - 2) * certScale : ℕ) : ℝ) = ((3 * q - 2 : ℕ) : ℝ) * (certScale : ℝ) := by
      push_cast
      ring
    rwa [h2] at h
  rw [hcast, hden] at hmain
  have h2 : (3 * (q : ℝ) - 2) / (6 * (q : ℝ) ^ 3)
      = 1 / (2 * (q : ℝ) ^ 2) - 1 / (3 * (q : ℝ) ^ 3) := by
    field_simp
    ring
  calc (c1num q : ℝ) ≤ (3 * (q : ℝ) - 2) * (certScale : ℝ) / (6 * (q : ℝ) ^ 3) := hmain
    _ = certScale * (1 / (2 * (q : ℝ) ^ 2) - 1 / (3 * (q : ℝ) ^ 3)) := by
        rw [← h2]; ring

/-! ## 2. `caC1` dominates the tail sum over the primes in `(n, 10^5]` -/

/-- `ξ₂(ε) ≤ ⌊√(2.5 ξ)⌋₊ + 1` as a statement about natural numbers. -/
lemma caXi2_le_floor_sqrt (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHContract.Margin.caXi2 ε ≤ ⌊Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ))⌋₊ + 1 := by
  have h := Work.RHContract.A.caXi2_le_sqrt ε hε hξ
  have hle : ((Work.RHContract.Margin.caXi2 ε : ℕ) : ℝ)
      ≤ Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ)) + 1 := h
  have hfloor : ⌊Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ)) + 1⌋₊
      = ⌊Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ))⌋₊ + 1 :=
    Nat.floor_add_one (Real.sqrt_nonneg _)
  have h' := Nat.le_floor hle
  rwa [hfloor] at h'

/-- **The finset reduction.**  For `ξ = caXi ε ≥ 10^5`, `caC1 ε` dominates the scaled excesses
of all primes in `(n, 10^5]`, `n = ⌊√(2.5ξ)⌋₊ + 1`. -/
lemma caC1_ge_tail (ε : ℝ) (hε : 0 < ε) (ξ : ℝ) (hξ : ξ = (Work.RHPlan.caXi ε : ℝ))
    (hlo : 100000 ≤ ξ) :
    (∑ q ∈ (Nat.primesLE 100000).filter (fun q => ⌊Real.sqrt (2.5 * ξ)⌋₊ + 1 < q),
        ((c1num q : ℝ) / certScale))
      ≤ Work.RHContract.Margin.caC1 ε := by
  set n : ℕ := ⌊Real.sqrt (2.5 * ξ)⌋₊ + 1 with hndef
  set m : ℕ := ⌊ξ⌋₊ with hmdef
  have hξ1530 : 1530 ≤ (Work.RHPlan.caXi ε : ℝ) := by rw [← hξ]; linarith
  have hcaXi2 : Work.RHContract.Margin.caXi2 ε ≤ n := by
    rw [hndef, hξ]
    exact caXi2_le_floor_sqrt ε hε hξ1530
  have hmge : 100000 ≤ m := by
    rw [hmdef]
    exact Nat.le_floor hlo
  have hC1 : Work.RHContract.Margin.caC1 ε
      = ∑ p ∈ (Nat.primesLE m).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) := by
    unfold Work.RHContract.Margin.caC1
    rw [← hξ, ← hmdef]
  have hsub : (Nat.primesLE 100000).filter (fun q => n < q)
      ⊆ (Nat.primesLE m).filter (fun q => Work.RHContract.Margin.caXi2 ε < q) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨?_, lt_of_le_of_lt hcaXi2 hp.2⟩
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1.1 hmge, hp.1.2⟩
  calc (∑ q ∈ (Nat.primesLE 100000).filter (fun q => n < q), ((c1num q : ℝ) / certScale))
      ≤ (∑ q ∈ (Nat.primesLE m).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          ((c1num q : ℝ) / certScale)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro p _ _; positivity)
    _ ≤ (∑ q ∈ (Nat.primesLE m).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          (1 / (2 * (q : ℝ) ^ 2) - 1 / (3 * (q : ℝ) ^ 3))) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hpprime : Nat.Prime p :=
          (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
        have hb := c1num_le_scaled p hpprime.pos
        have hS : (0 : ℝ) < certScale := by norm_num [certScale]
        rw [div_le_iff₀ hS, mul_comm]
        exact hb
    _ = Work.RHContract.Margin.caC1 ε := hC1.symm

/-! ## 3. The cut-off list -/

/-- Membership in the ascending cut-off list. -/
lemma mem_certAsc {q : ℕ} :
    q ∈ certAsc ↔ q = 501 ∨ (501 < q ∧ q ≤ 100000 ∧ Nat.Prime q) := by
  rw [certAsc, List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · have hh := (List.mem_filter.mp h).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
        exact hh.1
      · have hh := (List.mem_filter.mp h).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
        exact hh.2
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_filter.mp h).1
        exact CU_prim e he
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact Or.inl rfl
    · refine Or.inr (List.mem_filter.mpr ⟨?_, ?_⟩)
      · exact caC1_cert_CU_facts.2 q h3.two_le h2 h3
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h1, h2⟩

/-- Membership in the descending cut-off list. -/
lemma mem_certDesc {q : ℕ} :
    q ∈ certDesc ↔ q = 501 ∨ (501 < q ∧ q ≤ 100000 ∧ Nat.Prime q) := by
  rw [certDesc, List.mem_reverse]
  exact mem_certAsc

/-- The ascending cut-off list is strictly increasing. -/
lemma certAsc_pairwise : certAsc.Pairwise (· < ·) := by
  rw [certAsc, List.pairwise_cons]
  refine ⟨?_, List.Pairwise.filter _ caC1_cert_CU_facts.1⟩
  intro q hq
  have hh := (List.mem_filter.mp hq).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1

/-- The ascending cut-off list has no repetitions. -/
lemma certAsc_nodup : certAsc.Nodup := by
  rw [certAsc, List.nodup_cons]
  refine ⟨?_, List.Nodup.filter _ CU_nodup⟩
  intro h
  have hh := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact absurd hh.1 (lt_irrefl 501)

/-- The descending cut-off list is strictly decreasing. -/
lemma certDesc_pairwise : certDesc.Pairwise (· > ·) := by
  rw [certDesc]
  exact List.Pairwise.reverse certAsc_pairwise

/-- The descending cut-off list has no repetitions. -/
lemma certDesc_nodup : certDesc.Nodup := by
  rw [certDesc]
  exact List.nodup_reverse.mpr certAsc_nodup

/-- Every element of a list occurs as the first component of some pair of `tailsFrom`. -/
lemma exists_pair_tailsFrom : ∀ (l : List ℕ) (acc p : ℕ), p ∈ l →
    ∃ t : ℕ, (p, t) ∈ tailsFrom l acc := by
  intro l
  induction l with
  | nil => intro acc p hp; simp at hp
  | cons a as ih =>
    intro acc p hp
    rw [tailsFrom]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨acc, List.mem_cons_self ..⟩
    · obtain ⟨t, ht⟩ := ih (acc + c1num a) p hp'
      exact ⟨t, List.mem_cons_of_mem _ ht⟩

/-- **Certificate extraction.**  For every cut-off `p` of the descending cut-off list with
`p ≤ 15812` the paired tail sum satisfies the integer inequality. -/
lemma cert_spec {p : ℕ} (hp : p ∈ certDesc) (hp15812 : p ≤ 15812) :
    ∃ t : ℕ, (p, t) ∈ tailsFrom certDesc 0 ∧
      t = ((certDesc.filter (fun q => p < q)).map c1num).sum ∧
      688 * 10 ^ 46 ≤ t * (p - 1) * (2 * ltOf (p - 1) - certA) := by
  obtain ⟨t, htmem⟩ := exists_pair_tailsFrom certDesc 0 p hp
  refine ⟨t, htmem, ?_, ?_⟩
  · simpa using tailsFrom_mem certDesc certDesc_pairwise 0 htmem
  · have hall := List.all_eq_true.mp cert_check (p, t) htmem
    rw [certOk, Bool.or_eq_true] at hall
    rcases hall with h | h
    · simp only [decide_eq_true_eq] at h; omega
    · simpa using h

/-- The descending cut-off list above `p` is, for `p ≥ 501`, exactly the set of primes in
`(p, 10^5]`. -/
lemma certDesc_filter_toFinset {p : ℕ} (hp : 501 ≤ p) :
    (certDesc.filter (fun q => p < q)).toFinset
      = (Nat.primesLE 100000).filter (fun q => p < q) := by
  ext q
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Nat.mem_primesLE,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hq, hpq⟩
    rw [mem_certDesc] at hq
    rcases hq with rfl | ⟨h501, hle, hprime⟩
    · omega
    · exact ⟨⟨hle, hprime⟩, hpq⟩
  · rintro ⟨⟨hle, hprime⟩, hpq⟩
    refine ⟨?_, hpq⟩
    rw [mem_certDesc]
    exact Or.inr ⟨by omega, hle, hprime⟩

/-- `c1num` summed over the cut-offs above `p` equals the sum over the primes in `(p, 10^5]`. -/
lemma tail_eq_prime_sum {p : ℕ} (hp : 501 ≤ p) :
    ((certDesc.filter (fun q => p < q)).map c1num).sum
      = ((Nat.primesLE 100000).filter (fun q => p < q)).sum c1num := by
  rw [← List.sum_toFinset c1num (List.Nodup.filter _ certDesc_nodup),
    certDesc_filter_toFinset hp]

/-! ## 4. The certificate index -/

/-- For `ξ ∈ [10^5, 10^8)` and `n = ⌊√(2.5ξ)⌋₊ + 1` there is a cut-off `p` of the certificate
list with `501 ≤ p ≤ 15812`, whose prime-tail sum is the same as the sum over `(n, 10^5]`, and
with `ξ ≥ (p−1)²/2.5`. -/
lemma cert_index (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    ∃ p : ℕ, 501 ≤ p ∧ p ≤ 15812 ∧ p ∈ certDesc ∧
      ((Nat.primesLE 100000).filter (fun q => ⌊Real.sqrt (2.5 * ξ)⌋₊ + 1 < q)
        = (Nat.primesLE 100000).filter (fun q => p < q)) ∧
      ((p : ℝ) - 1) ^ 2 / 2.5 ≤ ξ := by
  have h500 : (500 : ℝ) ≤ Real.sqrt (2.5 * ξ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 500)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h15812 : Real.sqrt (2.5 * ξ) < 15812 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 15812)]
    nlinarith
  set n : ℕ := ⌊Real.sqrt (2.5 * ξ)⌋₊ + 1 with hndef
  have hn501 : 501 ≤ n := by
    have h : 500 ≤ ⌊Real.sqrt (2.5 * ξ)⌋₊ := Nat.le_floor h500
    rw [hndef]
    omega
  have hn15812 : n ≤ 15812 := by
    have h : ⌊Real.sqrt (2.5 * ξ)⌋₊ < 15812 := (Nat.floor_lt (Real.sqrt_nonneg _)).mpr h15812
    rw [hndef]
    omega
  rcases le_or_gt n 502 with hn502 | hn503
  · refine ⟨501, le_rfl, by omega, mem_certDesc.mpr (Or.inl rfl), ?_, ?_⟩
    · refine Finset.filter_congr (fun q hq => ?_)
      rw [Nat.mem_primesLE] at hq
      constructor
      · intro h; omega
      · intro h
        rcases lt_or_ge n q with h' | h'
        · exact h'
        · exfalso
          have hq2 : q = 502 := by omega
          subst hq2
          norm_num at hq
    · have h1 : (((501 : ℕ) : ℝ) - 1) ^ 2 / 2.5 = 100000 := by norm_num
      rw [h1]
      exact hlo
  · have h503mem : 503 ∈ Nat.primesLE n := by
      rw [Nat.mem_primesLE]
      exact ⟨by omega, by norm_num⟩
    have hne : (Nat.primesLE n).Nonempty := ⟨503, h503mem⟩
    obtain ⟨p, hpmem, hp_ge, hpmax⟩ :
        ∃ p : ℕ, p ∈ Nat.primesLE n ∧ 503 ≤ p ∧ ∀ q ∈ Nat.primesLE n, q ≤ p := by
      refine ⟨(Nat.primesLE n).max' hne, Finset.max'_mem _ _, ?_, ?_⟩
      · exact Finset.le_max' (Nat.primesLE n) 503 h503mem
      · intro q hq
        exact Finset.le_max' (Nat.primesLE n) q hq
    have hp_le_n : p ≤ n := (Nat.mem_primesLE.mp hpmem).1
    have hp_prime : Nat.Prime p := (Nat.mem_primesLE.mp hpmem).2
    refine ⟨p, by omega, by omega, ?_, ?_, ?_⟩
    · rw [mem_certDesc]
      exact Or.inr ⟨by omega, by omega, hp_prime⟩
    · refine Finset.filter_congr (fun q hq => ?_)
      rw [Nat.mem_primesLE] at hq
      constructor
      · intro h; omega
      · intro h
        by_contra hcon
        have hqmem : q ∈ Nat.primesLE n := by
          rw [Nat.mem_primesLE]
          exact ⟨by omega, hq.2⟩
        have hqp : q ≤ p := hpmax q hqmem
        omega
    · have hp_geR : (503 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge
      have hp_le_floor : (p : ℝ) ≤ (⌊Real.sqrt (2.5 * ξ)⌋₊ : ℝ) + 1 := by
        have h : p ≤ ⌊Real.sqrt (2.5 * ξ)⌋₊ + 1 := by
          have h2 := hp_le_n
          rw [hndef] at h2
          exact h2
        exact_mod_cast h
      have hk := Nat.floor_le (Real.sqrt_nonneg (2.5 * ξ))
      have hple : ((p : ℝ) - 1) ≤ Real.sqrt (2.5 * ξ) := by linarith
      have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have hsq : ((p : ℝ) - 1) ^ 2 ≤ (Real.sqrt (2.5 * ξ)) ^ 2 :=
        pow_le_pow_left₀ hp1 hple 2
      rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2.5 * ξ)] at hsq
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2.5)]
      linarith

/-! ## 5. The main theorem -/

theorem caC1_lower_B (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    (43/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.Margin.caC1 ε := by
  obtain ⟨p, hp501, hp15812, hpmem, hfilter, hξp⟩ :=
    cert_index (Work.RHPlan.caXi ε : ℝ) hlo hhi
  obtain ⟨t, htmem, htval, htcheck⟩ := cert_spec hpmem hp15812
  -- step 1: `caC1 ε` dominates the scaled tail sum over `(n, 10^5]`
  have hstep1 : (∑ q ∈ (Nat.primesLE 100000).filter
        (fun q => ⌊Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ))⌋₊ + 1 < q),
        ((c1num q : ℝ) / certScale)) ≤ Work.RHContract.Margin.caC1 ε :=
    caC1_ge_tail ε hε _ rfl hlo
  -- step 2: that sum is `t / 10^40`
  have hsum : (∑ q ∈ (Nat.primesLE 100000).filter (fun q => p < q), c1num q) = t := by
    rw [← tail_eq_prime_sum hp501, ← htval]
  have hstep2 : (t : ℝ) / certScale ≤ Work.RHContract.Margin.caC1 ε := by
    have hcast : (∑ q ∈ (Nat.primesLE 100000).filter (fun q => p < q), (c1num q : ℝ))
        = (t : ℝ) := by
      rw [← hsum]; push_cast; rfl
    calc (t : ℝ) / certScale
        = (∑ q ∈ (Nat.primesLE 100000).filter (fun q => p < q),
            (c1num q : ℝ)) / certScale := by rw [hcast]
      _ = ∑ q ∈ (Nat.primesLE 100000).filter (fun q => p < q),
            ((c1num q : ℝ) / certScale) := Finset.sum_div _ _ _
      _ = ∑ q ∈ (Nat.primesLE 100000).filter
            (fun q => ⌊Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ))⌋₊ + 1 < q),
            ((c1num q : ℝ) / certScale) := by rw [hfilter]
      _ ≤ Work.RHContract.Margin.caC1 ε := hstep1
  -- step 3: the certificate inequality
  have hstep3 : (43 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) ≤ (t : ℝ) / certScale := by
    have hcs : (certScale : ℝ) = 10 ^ 40 := by norm_num [certScale]
    rw [hcs]
    exact caC1_tail_arith (p := p) (t := t) (ξ := (Work.RHPlan.caXi ε : ℝ)) hp501 hξp htcheck
  have hcaU : Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      = 1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ)) := rfl
  rw [hcaU]
  exact le_trans hstep3 hstep2

end

end Work.RHContract.A.regionII
