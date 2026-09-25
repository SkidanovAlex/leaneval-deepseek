import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.caK3B_defs
import Submission.Work.RHContract.A.regionII.caK3B_term_bound
import Submission.Work.RHContract.A.regionII.caK3B_structure
import Submission.Work.RHContract.A.regionII.card_le_one_prime_short
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.Corpus

/-!
# `caK3_upper_B`

`K₃` (the deep-level losses of the colossally abundant number) is bounded by
`(24/1000)·u(ξ)` for `10^5 ≤ ξ(ε) < 10^8`, given the `A2` bound on `ψ(ξ)`.

Strategy.  By `caK3B_term_bound` every summand is at most
`(1/ξ)·(1/k_p)·(1 − kB ξ + 1/(p−1))` with `k_p = e_p + 1`.  Primes with `k_p ≤ 6` are
handled by the *window* shape `caK3B_structure`: the window
`(ξ^{1/k}, 1 + (ξ/kB ξ)^{1/k})` has length `< 2`, so it contains at most one prime
(`card_le_one_prime_short`), and the weight `(1/k)(1/25 + 1/(ξ^{1/k}−1))` is at most `9/250`
for `3 ≤ k ≤ 6`.  Primes with `k_p ≥ 7` satisfy `p ≤ 13`, and the corresponding weights give
a constant `671235/3141600`.  Summing: `caK3 ε ≤ (36/250 + 671235/3141600)/ξ`, and this is
at most `(24/1000)·caU ξ` because `√ξ/log ξ ≥ 316.22/18.636`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Real
open scoped BigOperators

namespace Work.RHContract.A.regionII

lemma rpow_one_div_le_one_add_div (y : ℝ) (hy : 0 ≤ y) (k : ℕ) (hk : 1 ≤ k) :
    (1 + y)^(1/(k:ℝ)) ≤ 1 + y/(k:ℝ) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hyk : 0 ≤ y/(k:ℝ) := div_nonneg hy hk0.le
  have hbase : 0 ≤ 1+y := by linarith
  have hbase2 : 0 ≤ 1+y/(k:ℝ) := by linarith
  rw [← Real.rpow_le_rpow_iff (x := (1+y)^(1/(k:ℝ))) (y := 1+y/(k:ℝ)) (z := (k:ℝ))
    (by positivity) hbase2 hk0]
  rw [show ((1+y)^(1/(k:ℝ)))^(k:ℝ) = (1+y)^((1/(k:ℝ))*(k:ℝ)) by
        rw [Real.rpow_mul hbase], one_div, inv_mul_cancel₀ (ne_of_gt hk0), Real.rpow_one]
  have hb := one_add_mul_le_pow (a := y/(k:ℝ)) (by linarith) k
  have hsimp : (1:ℝ) + (k:ℝ)*(y/(k:ℝ)) = 1+y := by field_simp
  rw [hsimp] at hb
  rw [Real.rpow_natCast (1+y/(k:ℝ)) k]
  exact hb

lemma inv_kB_rpow_le (ξ : ℝ) (hlo : 100000 ≤ ξ) (k : ℕ) (hk : 1 ≤ k) :
    (1/kB ξ)^(1/(k:ℝ)) ≤ 1 + (1 - kB ξ)/((k:ℝ) * kB ξ) := by
  have hBle := kB_le_one ξ hlo
  have hBge := kB_ge ξ hlo
  have hB0 : 0 < kB ξ := by linarith
  have h1 : (1:ℝ)/kB ξ = 1 + (1 - kB ξ)/kB ξ := by
    field_simp
    ring
  rw [h1]
  have hy : 0 ≤ (1 - kB ξ)/kB ξ := div_nonneg (by linarith) hB0.le
  have h2 : (1 + (1 - kB ξ)/kB ξ)^(1/(k:ℝ)) ≤ 1 + ((1 - kB ξ)/kB ξ)/(k:ℝ) :=
    rpow_one_div_le_one_add_div _ hy k hk
  have h3 : ((1 - kB ξ)/kB ξ)/(k:ℝ) = (1 - kB ξ)/((k:ℝ) * kB ξ) := by field_simp
  rw [h3] at h2
  exact h2

lemma kB_win_general (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) {k : ℕ} (hk3 : 3 ≤ k)
    (hk6 : k ≤ 6) : ξ^(1/(k:ℝ)) * (1 - kB ξ) < (96/100) * k := by
  have hd0 : 0 ≤ 1 - kB ξ := by
    have := kB_le_one ξ hlo; linarith
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcases with h | h | h | h <;> subst h
  · have h2 := kB_win3 ξ hlo hhi
    norm_num at h2 ⊢
    exact h2
  · have h2 := kB_win4 ξ hlo hhi
    norm_num at h2 ⊢
    exact h2
  · have hle : ξ^(1/(5:ℝ)) ≤ ξ^(1/4:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ ξ)
      norm_num
    have h1 := mul_le_mul_of_nonneg_right hle hd0
    have h2 := kB_win4 ξ hlo hhi
    norm_num at h1 h2 ⊢
    linarith
  · have hle : ξ^(1/(6:ℝ)) ≤ ξ^(1/4:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ ξ)
      norm_num
    have h1 := mul_le_mul_of_nonneg_right hle hd0
    have h2 := kB_win4 ξ hlo hhi
    norm_num at h1 h2 ⊢
    linarith

lemma kB_window (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) {k : ℕ} (hk3 : 3 ≤ k)
    (hk6 : k ≤ 6) : 1 + (ξ/kB ξ)^(1/(k:ℝ)) - ξ^(1/(k:ℝ)) < 2 := by
  have hξ0 : 0 < ξ := by linarith
  have hB0 : 0 < kB ξ := by have := kB_ge ξ hlo; linarith
  have hxpos : 0 < ξ^(1/(k:ℝ)) := Real.rpow_pos_of_pos hξ0 _
  have hdiv : (ξ/kB ξ)^(1/(k:ℝ)) = ξ^(1/(k:ℝ)) * (1/kB ξ)^(1/(k:ℝ)) := by
    rw [show ξ/kB ξ = ξ * (1/kB ξ) by ring, Real.mul_rpow hξ0.le (by positivity)]
  rw [hdiv]
  have h1 := inv_kB_rpow_le ξ hlo k (by omega)
  have hwin := kB_win_general ξ hlo hhi hk3 hk6
  have hBge := kB_ge ξ hlo
  have h3 : ξ^(1/(k:ℝ)) * (1-kB ξ)/((k:ℝ)*kB ξ) < 1 := by
    rw [div_lt_one (by positivity)]
    have hk : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    nlinarith [hwin, hBge, hk]
  have h4 : ξ^(1/(k:ℝ)) * (1/kB ξ)^(1/(k:ℝ))
      ≤ ξ^(1/(k:ℝ)) * (1 + (1-kB ξ)/((k:ℝ)*kB ξ)) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hxpos)
  have h5 : ξ^(1/(k:ℝ)) * (1 + (1-kB ξ)/((k:ℝ)*kB ξ)) - ξ^(1/(k:ℝ))
      = ξ^(1/(k:ℝ)) * (1-kB ξ)/((k:ℝ)*kB ξ) := by ring
  linarith

lemma k_weight_le (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) {k : ℕ} (hk3 : 3 ≤ k)
    (hk6 : k ≤ 6) : (1/(k:ℝ)) * (1/25 + 1/(ξ^(1/(k:ℝ)) - 1)) ≤ 9/250 := by
  obtain ⟨h4, h5, h6, h3, -, -, -, h17, -, -, -, -⟩ := rpow_facts ξ hlo hhi
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcases with h | h | h | h <;> subst h
  · have hp : (44:ℝ) ≤ ξ^(1/3:ℝ) - 1 := by norm_num at h3 ⊢; linarith
    have hle : (ξ^(1/3:ℝ) - 1)⁻¹ ≤ (44:ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr hp
    norm_num at hle ⊢
    linarith
  · have hp : (15:ℝ) ≤ ξ^(1/4:ℝ) - 1 := by norm_num at h4 ⊢; linarith
    have hle : (ξ^(1/4:ℝ) - 1)⁻¹ ≤ (15:ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr hp
    norm_num at hle ⊢
    linarith
  · have hp : (8:ℝ) ≤ ξ^(1/5:ℝ) - 1 := by norm_num at h5 ⊢; linarith
    have hle : (ξ^(1/5:ℝ) - 1)⁻¹ ≤ (8:ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr hp
    norm_num at hle ⊢
    linarith
  · have hp : (58/10:ℝ) ≤ ξ^(1/6:ℝ) - 1 := by norm_num at h6 ⊢; linarith
    have hle : (ξ^(1/6:ℝ) - 1)⁻¹ ≤ (58/10:ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr hp
    norm_num at hle ⊢
    linarith


/-- `Nat.log b x = n` when `b^n ≤ x < b^(n+1)`. -/
lemma natlog_eq_of {b x n : ℕ} (hb : 1 < b) (h1 : b^n ≤ x) (h2 : x < b^(n+1)) :
    Nat.log b x = n := by
  have hb1 : 1 ≤ b := le_of_lt hb
  have hx0 : x ≠ 0 := by
    have hb0 : 0 < b := by omega
    have := pow_pos hb0 n
    omega
  have hle : n ≤ Nat.log b x := (Nat.le_log_iff_pow_le hb hx0).mpr h1
  have hlt : Nat.log b x < n+1 := by
    by_contra h
    push_neg at h
    exact absurd ((Nat.le_log_iff_pow_le hb hx0).mp h) (not_le.mpr h2)
  omega

theorem caK3_upper_B (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8)
    (hA2 : |Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)|
        ≤ 0.45 * (Work.RHPlan.caXi ε : ℝ) ^ (3/4:ℝ) + 2) :
    Work.RHContract.Margin.caK3 ε
      ≤ (24/1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have h1e5 : (100000:ℝ) ≤ ξ := hlo
  have h1e8 : ξ < (10:ℝ)^8 := hhi
  have hξ0 : 0 < ξ := by linarith
  have hLpos : 0 < Real.log ξ :=
    lt_of_lt_of_le (by norm_num) (le_trans log1e5_ge (Real.log_le_log (by norm_num) h1e5))
  have hcaC : kcc ξ ≤ Work.RHContract.Margin.caC ε := kcc_le_caC ε hε hlo hA2
  have hBge : (24/25:ℝ) ≤ kB ξ := kB_ge ξ h1e5
  have hBle : kB ξ ≤ 1 := kB_le_one ξ h1e5
  have hB0 : 0 < kB ξ := by linarith
  -- the index sets
  set S : Finset ℕ := (Nat.primesLE ⌊Real.sqrt ξ⌋₊).filter
      (fun q => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊) with hS
  have hK3eq : Work.RHContract.Margin.caK3 ε = ∑ p ∈ S, Work.RHContract.A.caK3term ε p := by
    rw [hS]; exact caK3_eq ε
  set P : Finset ℕ := S.filter (fun p => 0 < Work.RHContract.A.caK3term ε p) with hP
  have hPS : ∀ p ∈ P, p ∈ S := by
    intro p hp
    rw [hP] at hp
    exact (Finset.mem_filter.mp hp).1
  have hPpos : ∀ p ∈ P, 0 < Work.RHContract.A.caK3term ε p := by
    intro p hp
    rw [hP] at hp
    exact (Finset.mem_filter.mp hp).2
  have hSP : ∑ p ∈ S, Work.RHContract.A.caK3term ε p
      = ∑ p ∈ P, Work.RHContract.A.caK3term ε p := by
    symm
    refine Finset.sum_subset (fun p hp => hPS p hp) ?_
    intro p hpS hpP
    by_contra hne
    have hpos : 0 < Work.RHContract.A.caK3term ε p :=
      lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hne)
    exact hpP (by rw [hP]; exact Finset.mem_filter.mpr ⟨hpS, hpos⟩)
  rw [hK3eq, hSP]
  -- the split
  set P1 : Finset ℕ := P.filter (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ 6) with hP1
  set P2 : Finset ℕ := P.filter (fun p => ¬ (Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ 6)) with hP2
  have hsplit : ∑ p ∈ P, Work.RHContract.A.caK3term ε p
      = ∑ p ∈ P1, Work.RHContract.A.caK3term ε p + ∑ p ∈ P2, Work.RHContract.A.caK3term ε p := by
    rw [hP1, hP2]
    exact (Finset.sum_filter_add_sum_filter_not P
      (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ 6)
      (fun p => Work.RHContract.A.caK3term ε p)).symm
  have hmem1 : ∀ p ∈ P1, p ∈ P ∧ Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ 6 := by
    intro p hp; rw [hP1] at hp; exact Finset.mem_filter.mp hp
  have hmem2 : ∀ p ∈ P2, p ∈ P ∧ ¬ (Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ 6) := by
    intro p hp; rw [hP2] at hp; exact Finset.mem_filter.mp hp
  -- bound for P1
  have hP1term : ∀ p ∈ P1, Work.RHContract.A.caK3term ε p ≤ (9/250) * (1/ξ) := by
    intro p hp
    obtain ⟨hpP, hple6⟩ := hmem1 p hp
    obtain ⟨hk3, hgt, hle, hlt⟩ := caK3B_structure ε hε hlo hcaC (hPS p hpP) (hPpos p hpP)
    have ht := caK3B_term_bound ε hε hlo hcaC (hPS p hpP)
    set k : ℕ := Nat.log p (Work.RHPlan.caXi ε) + 1 with hk
    have hk3' : 3 ≤ k := hk ▸ hk3
    have hk6' : k ≤ 6 := hk ▸ hple6
    have hpprime : Nat.Prime p := by
      have h1 := (Finset.mem_filter.mp (hPS p hpP)).1
      exact (Nat.mem_primesLE.mp h1).2
    have hp2 : 2 ≤ p := hpprime.two_le
    have hpr : 0 < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      linarith
    have hx1 : 1 < ξ^(1/(k:ℝ)) := by
      have h : (6.8:ℝ) ≤ ξ^(1/(k:ℝ)) := by
        have h67 := (rpow_facts ξ h1e5 h1e8).2.2.1
        have hle' : ξ^(1/6:ℝ) ≤ ξ^(1/(k:ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          have : ((k:ℕ):ℝ) ≤ 6 := by exact_mod_cast hk6'
          linarith
        linarith
      linarith
    have hgt' : ξ^(1/(k:ℝ)) - 1 < (p:ℝ) - 1 := by linarith
    have hinv : (1/((p:ℝ)-1)) ≤ 1/(ξ^(1/(k:ℝ)) - 1) :=
      one_div_le_one_div_of_le (by linarith) (le_of_lt hgt')
    have hw := k_weight_le ξ h1e5 h1e8 hk3' hk6'
    have hfin : (1/(k:ℝ)) * (1 - kB ξ + 1/((p:ℝ)-1)) ≤ 9/250 := by
      have h1 : 1 - kB ξ ≤ (1:ℝ)/25 := by linarith
      have h2 : (1/(k:ℝ)) * (1 - kB ξ + 1/((p:ℝ)-1))
          ≤ (1/(k:ℝ)) * (1/25 + 1/(ξ^(1/(k:ℝ)) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
    have hterm : (1/(k:ℝ)) = 1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ)) := by
      rw [hk]
    rw [hterm] at hfin
    calc Work.RHContract.A.caK3term ε p
        ≤ (1/ξ) * (1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
            (1 - kB ξ + 1/((p:ℝ)-1)) := ht
      _ = (1/ξ) * ((1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
            (1 - kB ξ + 1/((p:ℝ)-1))) := by ring
      _ ≤ (1/ξ) * (9/250) := by
            apply mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = (9/250) * (1/ξ) := by ring
  -- cardinality of P1
  have hP1card : (P1.card : ℝ) ≤ 4 := by
    have hmaps : Set.MapsTo (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1) ↑P1 ↑(Finset.Icc 3 6) := by
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨(caK3B_structure ε hε hlo hcaC (hPS p (hmem1 p hp).1) (hPpos p (hmem1 p hp).1)).1,
        (hmem1 p hp).2⟩
    have hcardle : (∑ k ∈ Finset.Icc 3 6,
        (P1.filter (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1 = k)).card) ≤ 4 := by
      have h1 : ∀ k ∈ Finset.Icc 3 6,
          (P1.filter (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1 = k)).card ≤ 1 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        apply card_le_one_prime_short (a := ξ^(1/(k:ℝ))) (b := 1 + (ξ/kB ξ)^(1/(k:ℝ)))
        · intro p hp
          obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
          have h1 := (Finset.mem_filter.mp (hPS p (hmem1 p hp1).1)).1
          exact (Nat.mem_primesLE.mp h1).2
        · intro p hp
          obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
          have hstr := caK3B_structure ε hε hlo hcaC (hPS p (hmem1 p hp1).1) (hPpos p (hmem1 p hp1).1)
          have hk1 : 3 ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 := hstr.1
          have hk6'' : ((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) ≤ 6 := by
            have := (hmem1 p hp1).2
            exact_mod_cast this
          have hgeom : (1:ℝ)/6 ≤ 1/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) :=
            one_div_le_one_div_of_le (by positivity) hk6''
          have hmono := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ ξ) hgeom
          have h68 := (rpow_facts ξ h1e5 h1e8).2.2.1
          have hgt := hstr.2.1
          have hreal : (3:ℝ) ≤ (p:ℝ) := by linarith
          exact_mod_cast hreal
        · intro p hp
          obtain ⟨hp1, hpk⟩ := Finset.mem_filter.mp hp
          have hstr := caK3B_structure ε hε hlo hcaC (hPS p (hmem1 p hp1).1) (hPpos p (hmem1 p hp1).1)
          have hpk' : ((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) = (k:ℝ) := by rw [hpk]
          have he : ξ^(1/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ):ℝ)) = ξ^(1/(k:ℝ)) := by rw [hpk']
          rw [← he]
          exact hstr.2.1
        · intro p hp
          obtain ⟨hp1, hpk⟩ := Finset.mem_filter.mp hp
          have hstr := caK3B_structure ε hε hlo hcaC (hPS p (hmem1 p hp1).1) (hPpos p (hmem1 p hp1).1)
          have hpk' : ((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) = (k:ℝ) := by rw [hpk]
          have he : (ξ/kB ξ)^(1/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ):ℝ)) = (ξ/kB ξ)^(1/(k:ℝ)) := by rw [hpk']
          rw [← he]
          exact hstr.2.2.2
        · have hwin := kB_window ξ h1e5 h1e8 (k := k) hk.1 hk.2
          linarith
      calc ∑ k ∈ Finset.Icc 3 6,
            (P1.filter (fun p => Nat.log p (Work.RHPlan.caXi ε) + 1 = k)).card
          ≤ ∑ _k ∈ Finset.Icc 3 6, (1:ℕ) := Finset.sum_le_sum h1
        _ = 4 := by decide
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact_mod_cast hcardle
  have hP1sum : ∑ p ∈ P1, Work.RHContract.A.caK3term ε p ≤ 4 * (9/250) * (1/ξ) := by
    have h1 : ∑ p ∈ P1, Work.RHContract.A.caK3term ε p ≤ ∑ _p ∈ P1, (9/250) * (1/ξ) :=
      Finset.sum_le_sum hP1term
    have h2 : ∑ _p ∈ P1, (9/250) * (1/ξ) = (P1.card : ℝ) * ((9/250) * (1/ξ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h2] at h1
    have h3 : ((P1.card : ℝ)) * ((9/250) * (1/ξ)) ≤ 4 * ((9/250) * (1/ξ)) :=
      mul_le_mul_of_nonneg_right hP1card (by positivity)
    linarith
  -- bound for P2
  have hP2le13 : ∀ p ∈ P2, p ≤ 13 := by
    intro p hp
    obtain ⟨hpP, hp7⟩ := hmem2 p hp
    have hstr := caK3B_structure ε hε hlo hcaC (hPS p hpP) (hPpos p hpP)
    have hk7 : 7 ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 := by omega
    have hk7' : (7:ℝ) ≤ ((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) := by exact_mod_cast hk7
    have hbase : 1 ≤ ξ/kB ξ := by
      rw [le_div_iff₀ hB0]
      linarith [hBle, h1e5]
    have hquot : ξ/kB ξ ≤ 14^7 := by
      rw [div_le_iff₀ hB0]
      nlinarith [hBge, h1e8]
    have hle7 : (1:ℝ)/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ) ≤ 1/7 :=
      one_div_le_one_div_of_le (by norm_num) hk7'
    have hmono := Real.rpow_le_rpow_of_exponent_le hbase hle7
    have h14' : ((ξ/kB ξ)^(1/7:ℝ)) ≤ 14 := by
      by_contra hcon
      push_neg at hcon
      have hb7 : (14:ℝ)^7 < ((ξ/kB ξ)^(1/7:ℝ))^7 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      have he : ((ξ/kB ξ)^(1/7:ℝ))^7 = ξ/kB ξ := by
        rw [← Real.rpow_natCast ((ξ/kB ξ)^(1/7:ℝ)) 7, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [he] at hb7
      linarith
    have h15 : (p:ℝ) < 15 := by linarith [hstr.2.2.2, hmono, h14']
    have hp15 : p < 15 := by exact_mod_cast h15
    have hp14 : p ≤ 14 := by omega
    have hprime : Nat.Prime p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (hPS p hpP)).1).2
    have hne : p ≠ 14 := by
      intro h
      rw [h] at hprime
      exact absurd hprime (by decide : ¬ Nat.Prime 14)
    omega
  have hP2term : ∀ p ∈ P2, Work.RHContract.A.caK3term ε p
      ≤ (1/ξ) * ((1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := by
    intro p hp
    obtain ⟨hpP, hp7⟩ := hmem2 p hp
    have ht := caK3B_term_bound ε hε hlo hcaC (hPS p hpP)
    have hk7 : 7 ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 := by omega
    have hklog : Nat.log p 100000 + 1 ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 := by
      have hX : 100000 ≤ Work.RHPlan.caXi ε := by
        have : (100000:ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by rw [← hξdef]; exact h1e5
        exact_mod_cast this
      exact Nat.add_le_add_right (Nat.log_mono_right hX) 1
    have hmax : ((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ) ≤ (((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ)) : ℝ) := by
      have : max 7 (Nat.log p 100000 + 1) ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 := max_le hk7 hklog
      exact_mod_cast this
    have hposmax : 0 < ((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ) := by positivity
    have h1inv : 1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))
        ≤ 1/(((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hposmax hmax
    have hB : 1 - kB ξ ≤ (1:ℝ)/25 := by linarith
    have hpprime : Nat.Prime p := by
      have h1 := (Finset.mem_filter.mp (hPS p hpP)).1
      exact (Nat.mem_primesLE.mp h1).2
    have hpr : 0 < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
      linarith
    have h1nn : 0 ≤ 1/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ) := by positivity
    have h2nn : 0 ≤ 1/25 + 1/((p:ℝ)-1) := by positivity
    have hstep : (1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
        (1 - kB ξ + 1/((p:ℝ)-1))
        ≤ (1/(((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ))) * (1/25 + 1/((p:ℝ)-1)) := by
      apply mul_le_mul h1inv _ _ h1nn
      · linarith [hB]
      · have : 0 ≤ 1/((p:ℝ)-1) := div_nonneg (by norm_num) hpr.le
        linarith
    calc Work.RHContract.A.caK3term ε p
        ≤ (1/ξ) * (1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
            (1 - kB ξ + 1/((p:ℝ)-1)) := ht
      _ = (1/ξ) * ((1/(((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ))) *
            (1 - kB ξ + 1/((p:ℝ)-1))) := by ring
      _ ≤ (1/ξ) * ((1/(((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ))) * (1/25 + 1/((p:ℝ)-1))) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (1/ξ) * ((1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := by ring
  -- the sum over P2
  have hP2subset : P2 ⊆ Nat.primesLE 13 := by
    intro p hp
    rw [Nat.mem_primesLE]
    exact ⟨hP2le13 p hp, (Nat.mem_primesLE.mp (Finset.mem_filter.mp (hPS p (hmem2 p hp).1)).1).2⟩
  have hP2sum : ∑ p ∈ P2, Work.RHContract.A.caK3term ε p
      ≤ (1/ξ) * (∑ p ∈ Nat.primesLE 13,
          (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := by
    have h1 : ∑ p ∈ P2, Work.RHContract.A.caK3term ε p
        ≤ ∑ p ∈ P2, (1/ξ) * ((1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) :=
      Finset.sum_le_sum hP2term
    have h2 : ∑ p ∈ P2, (1/ξ) * ((1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ))
        = (1/ξ) * (∑ p ∈ P2, (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    have h3 : ∑ p ∈ P2, (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)
        ≤ ∑ p ∈ Nat.primesLE 13,
            (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hP2subset
      intro p hp hnp
      have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
      have hpr : (0:ℝ) < (p:ℝ) - 1 := by
        have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        linarith
      apply div_nonneg _ (by positivity)
      have : 0 ≤ 1/((p:ℝ)-1) := div_nonneg (by norm_num) hpr.le
      linarith
    rw [h2] at h1
    calc ∑ p ∈ P2, Work.RHContract.A.caK3term ε p
        ≤ (1/ξ) * (∑ p ∈ P2, (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := h1
      _ ≤ (1/ξ) * (∑ p ∈ Nat.primesLE 13,
            (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
  -- evaluate the constant sum
  have hconstsum : (∑ p ∈ Nat.primesLE 13,
      (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ)) ≤ 671235/3141600 := by
    have hpe : Nat.primesLE 13 = {2, 3, 5, 7, 11, 13} := by decide
    rw [hpe]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]

  -- final numeric comparison
  have hsq : (31622/100 : ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]
    linarith
  have hlog : Real.log ξ ≤ (18636:ℝ)/1000 := log1e8_le ξ (by linarith) h1e8
  have hrat : (31622/100)/((18636:ℝ)/1000) ≤ Real.sqrt ξ / Real.log ξ := by
    rw [div_le_div_iff₀ (by norm_num) hLpos]
    nlinarith [hsq, hlog, Real.sqrt_nonneg ξ]
  have hnum : 4 * (9/250) + 671235/3141600
      ≤ (24/1000) * ((31622/100)/((18636:ℝ)/1000)) := by
    have h : (0:ℝ) < (18636:ℝ)/1000 := by norm_num
    have h2 : (24/1000) * ((31622/100)/((18636:ℝ)/1000))
        = (24/1000) * (31622/100) / ((18636:ℝ)/1000) := (mul_div_assoc _ _ _).symm
    rw [h2, le_div_iff₀ h]
    norm_num
  have hfinstep : 4 * (9/250) + 671235/3141600 ≤ (24/1000) * (Real.sqrt ξ / Real.log ξ) := by
    have := mul_le_mul_of_nonneg_left hrat (by norm_num : (0:ℝ) ≤ 24/1000)
    linarith
  -- conclude
  have htotal : Work.RHContract.Margin.caK3 ε
      ≤ (4 * (9/250) + 671235/3141600) * (1/ξ) := by
    rw [hK3eq, hSP, hsplit]
    have hc : (1/ξ) * (∑ p ∈ Nat.primesLE 13,
        (1/25 + 1/((p:ℝ)-1))/((max 7 (Nat.log p 100000 + 1) : ℕ) : ℝ))
        ≤ (1/ξ) * (671235/3141600) :=
      mul_le_mul_of_nonneg_left hconstsum (by positivity)
    linarith [hP1sum, hP2sum, hc]
  have hU : (24/1000) * Work.RHContract.A.RegionII.caU ξ
      = (24/1000) * (Real.sqrt ξ / Real.log ξ) * (1/ξ) := by
    rw [Work.RHContract.A.RegionII.caU]
    have hsq2 : Real.sqrt ξ * Real.sqrt ξ = ξ := Real.mul_self_sqrt hξ0.le
    have hs : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ0
    field_simp
    rw [pow_two, hsq2]
  rw [hU]
  have := mul_le_mul_of_nonneg_right hfinstep (by positivity : (0:ℝ) ≤ 1/ξ)
  linarith [htotal, this]

end Work.RHContract.A.regionII
