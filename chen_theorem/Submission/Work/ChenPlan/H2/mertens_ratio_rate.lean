import Mathlib
import Submission.Commons.NumberTheory.Chen.rough_theta_lower_of_bv
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp

open Finset
open scoped BigOperators

namespace Work.ChenPlan.H2

open Commons.NumberTheory.Chen (Vsieve oddPrimesLt Vsieve_bounds Vsieve_le_one Vsieve_pos Vsieve_mono)

/-- The product of `(p-1)/(p-2)` over the odd primes `< Y` is `(Vsieve Y)⁻¹`. -/
private lemma prod_ratio_oddPrimesLt (Y : ℕ) :
    (∏ p ∈ oddPrimesLt Y, (((p:ℝ)-1) / ((p:ℝ)-2))) = (Vsieve Y)⁻¹ := by
  rw [Vsieve, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  obtain ⟨-, hpp, hp2⟩ := Finset.mem_filter.mp hp
  have hq3 : 3 ≤ p := by have := hpp.two_le; omega
  have h1 : ((p:ℝ)-1) ≠ 0 := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hq3
    linarith
  have hfac : (1 - 1/((p:ℝ)-1)) = ((p:ℝ)-2)/((p:ℝ)-1) := by
    field_simp
    ring
  rw [hfac, inv_div]

/-- For `2 < w` and `w < z`, the product of `(p-1)/(p-2)` over the primes `p` with
`w ≤ p < z` equals the `Vsieve` ratio `Vsieve ⌈w⌉ / Vsieve z`. -/
private lemma prod_ratio_eq_vsieve {z : ℕ} {w : ℝ} (hw : 2 < w) (hwz : w < z) :
    (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ)),
        (((p:ℝ)-1) / ((p:ℝ)-2))) = Vsieve (Nat.ceil w) / Vsieve z := by
  set s := Nat.ceil w with hs
  have hsle : s ≤ z := Nat.ceil_le.mpr (le_of_lt hwz)
  have hset : (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ))
      = oddPrimesLt z \ oddPrimesLt s := by
    ext p
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    constructor
    · rintro ⟨hpz, hpp, hwp⟩
      refine ⟨⟨hpz, hpp, ?_⟩, ?_⟩
      · intro hp2; subst hp2; norm_num at hwp; linarith
      · rintro ⟨hps, -, -⟩
        have hpw : (p:ℝ) < w := Nat.lt_ceil.mp hps
        linarith
    · rintro ⟨⟨hpz, hpp, hp2⟩, hnot⟩
      refine ⟨hpz, hpp, ?_⟩
      have hge : s ≤ p := by
        by_contra hc
        exact hnot ⟨by omega, hpp, hp2⟩
      have h1 : ((s : ℕ) : ℝ) ≤ (p:ℝ) := by exact_mod_cast hge
      have h2 : w ≤ ((s : ℕ) : ℝ) := Nat.le_ceil w
      linarith
  rw [hset]
  have hsub : oddPrimesLt s ⊆ oddPrimesLt z := by
    intro p hp
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsd := Finset.prod_sdiff (s₁ := oddPrimesLt s)
    (s₂ := oddPrimesLt z) (f := fun p : ℕ => (((p:ℝ)-1) / ((p:ℝ)-2))) hsub
  rw [prod_ratio_oddPrimesLt z, prod_ratio_oddPrimesLt s] at hsd
  have hVs : Vsieve s ≠ 0 := ne_of_gt (Vsieve_pos s)
  have hfin : (∏ p ∈ oddPrimesLt z \ oddPrimesLt s, (((p:ℝ)-1) / ((p:ℝ)-2)))
      = (Vsieve z)⁻¹ * Vsieve s := by
    rw [← hsd, mul_assoc, inv_mul_cancel₀ hVs, mul_one]
  rw [hfin, div_eq_inv_mul]

theorem mertens_ratio_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℕ) (w : ℝ), 2 ≤ w → w < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log w) * (1 + K / Real.log w) := by
  obtain ⟨Ksharp, hKsharp, N₀, hN₀⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.Vsieve_mul_log_diff_le 1 (by norm_num)
  obtain ⟨cV, CV, hcV, hCV, hVb⟩ := Vsieve_bounds
  refine ⟨max (Ksharp / cV) ((Real.log (N₀:ℝ))^2 / cV), ?_, ?_⟩
  · exact le_trans (div_nonneg (sq_nonneg _) hcV.le) (le_max_right _ _)
  · intro z w h2 hwz
    set K : ℝ := max (Ksharp / cV) ((Real.log (N₀:ℝ))^2 / cV) with hKdef
    have hKnn : 0 ≤ K := by
      rw [hKdef]; exact le_trans (div_nonneg (sq_nonneg _) hcV.le) (le_max_right _ _)
    have hKs : Ksharp / cV ≤ K := by rw [hKdef]; exact le_max_left _ _
    have hKN : (Real.log (N₀:ℝ))^2 / cV ≤ K := by rw [hKdef]; exact le_max_right _ _
    have hlogw_ge1 : (1:ℝ) ≤ 1 + K / Real.log w := by
      have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
      have : 0 ≤ K / Real.log w := div_nonneg hKnn hlogw.le
      linarith
    have hlogw_pos_fac : 0 < 1 + K / Real.log w := lt_of_lt_of_le one_pos hlogw_ge1
    by_cases hw2 : w = 2
    · -- w = 2 : the factor at p = 2 vanishes
      have hz2 : (2:ℝ) < (z:ℝ) := by simpa [hw2] using hwz
      have hmem : 2 ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ)) := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by exact_mod_cast hz2, Nat.prime_two, by rw [hw2]; norm_num⟩
      have hprod : (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ)),
          (((p:ℝ)-1) / ((p:ℝ)-2))) = 0 := Finset.prod_eq_zero hmem (by norm_num)
      rw [hprod]
      apply mul_nonneg
      · exact div_nonneg (Real.log_pos (by linarith)).le (Real.log_pos (by rw [hw2]; norm_num)).le
      · exact hlogw_pos_fac.le
    · have hw2' : 2 < w := lt_of_le_of_ne h2 (Ne.symm hw2)
      set s : ℕ := Nat.ceil w with hsdef
      have hsz : s ≤ z := by rw [hsdef]; exact Nat.ceil_le.mpr (le_of_lt hwz)
      have hs3 : 3 ≤ s := by
        rw [hsdef]
        have h2' : (2:ℝ) < ((Nat.ceil w : ℕ) : ℝ) := lt_of_lt_of_le hw2' (Nat.le_ceil w)
        have h3 : 2 < Nat.ceil w := by exact_mod_cast h2'
        omega
      have hP : (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ)),
          (((p:ℝ)-1) / ((p:ℝ)-2))) = Vsieve s / Vsieve z := by
        rw [hsdef]; exact prod_ratio_eq_vsieve hw2' hwz
      have hlogs_pos : 0 < Real.log (s:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
      have hlogz_pos : 0 < Real.log (z:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hlogw_pos : 0 < Real.log w := Real.log_pos (by linarith)
      have hlogs_ge : Real.log w ≤ Real.log (s:ℝ) := by
        apply Real.log_le_log (by linarith)
        rw [hsdef]; exact Nat.le_ceil w
      have hVz_pos : 0 < Vsieve z := Vsieve_pos z
      rw [hP]
      by_cases hz4 : 4 ≤ z
      · by_cases hsh : N₀ ≤ s
        · -- sharp regime
          have hKn : 0 ≤ Ksharp / cV := div_nonneg hKsharp.le hcV.le
          have hdiff := hN₀ s z hsh hsz
          have h1 : Vsieve s * Real.log (s:ℝ) ≤ Vsieve z * Real.log (z:ℝ) + Ksharp / Real.log (s:ℝ) := by
            have h := (abs_le.mp hdiff).2
            rw [Real.rpow_one] at h
            linarith
          have hVzlog : cV ≤ Vsieve z * Real.log (z:ℝ) := by
            have h := (hVb z hz4).1
            rw [div_le_iff₀ hlogz_pos] at h
            linarith
          have h2 : Ksharp / Real.log (s:ℝ) ≤ Vsieve z * Real.log (z:ℝ) * (Ksharp / cV) / Real.log (s:ℝ) := by
            rw [div_le_div_iff_of_pos_right hlogs_pos]
            have hge : 1 ≤ Vsieve z * Real.log (z:ℝ) / cV := by
              rw [le_div_iff₀ hcV]; linarith
            calc Ksharp = 1 * Ksharp := by ring
              _ ≤ (Vsieve z * Real.log (z:ℝ) / cV) * Ksharp := mul_le_mul_of_nonneg_right hge hKsharp.le
              _ = Vsieve z * Real.log (z:ℝ) * (Ksharp / cV) := by ring
          have h3 : Vsieve s * Real.log (s:ℝ)
              ≤ Vsieve z * Real.log (z:ℝ) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) := by
            calc Vsieve s * Real.log (s:ℝ)
                ≤ Vsieve z * Real.log (z:ℝ) + Ksharp / Real.log (s:ℝ) := h1
              _ ≤ Vsieve z * Real.log (z:ℝ) + Vsieve z * Real.log (z:ℝ) * (Ksharp/cV)/Real.log (s:ℝ) := by
                  linarith [h2]
              _ = Vsieve z * Real.log (z:ℝ) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) := by ring
          have h4 : Vsieve s / Vsieve z
              ≤ (Real.log (z:ℝ)/Real.log (s:ℝ)) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) := by
            have hb : Vsieve s ≤ Vsieve z * Real.log (z:ℝ) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) / Real.log (s:ℝ) :=
              (le_div_iff₀ hlogs_pos).mpr h3
            rw [div_le_iff₀ hVz_pos]
            calc Vsieve s ≤ Vsieve z * Real.log (z:ℝ) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) / Real.log (s:ℝ) := hb
              _ = (Real.log (z:ℝ)/Real.log (s:ℝ)) * (1 + (Ksharp/cV)/Real.log (s:ℝ)) * Vsieve z := by ring
          have h5 : (Real.log (z:ℝ)/Real.log (s:ℝ)) * (1 + (Ksharp/cV)/Real.log (s:ℝ))
              ≤ (Real.log (z:ℝ)/Real.log w) * (1 + K/Real.log w) := by
            have hA : Real.log (z:ℝ)/Real.log (s:ℝ) ≤ Real.log (z:ℝ)/Real.log w :=
              div_le_div_of_nonneg_left hlogz_pos.le hlogw_pos hlogs_ge
            have hB : (1 + (Ksharp/cV)/Real.log (s:ℝ)) ≤ (1 + K/Real.log w) := by
              have hinv : 1/Real.log (s:ℝ) ≤ 1/Real.log w :=
                one_div_le_one_div_of_le hlogw_pos hlogs_ge
              have hstep : (Ksharp/cV)/Real.log (s:ℝ) ≤ K/Real.log w := by
                calc (Ksharp/cV)/Real.log (s:ℝ) = (Ksharp/cV)*(1/Real.log (s:ℝ)) := by ring
                  _ ≤ K * (1/Real.log w) :=
                      mul_le_mul hKs hinv (div_nonneg zero_le_one hlogs_pos.le) hKnn
                  _ = K/Real.log w := by ring
              linarith
            exact mul_le_mul hA hB (by have h := div_nonneg hKn hlogs_pos.le; linarith)
              (div_nonneg hlogz_pos.le hlogw_pos.le)
          exact le_trans h4 h5
        · -- crude regime
          have hsN : s < N₀ := lt_of_not_ge hsh
          have hVz_ge : cV / Real.log (z:ℝ) ≤ Vsieve z := (hVb z hz4).1
          have hVzlog : cV ≤ Vsieve z * Real.log (z:ℝ) := by
            have h := hVz_ge
            rw [div_le_iff₀ hlogz_pos] at h
            linarith
          have h2 : 1 / Vsieve z ≤ Real.log (z:ℝ) / cV := by
            rw [le_div_iff₀ hcV]
            rw [show (1:ℝ)/Vsieve z * cV = cV / Vsieve z from by ring]
            rw [div_le_iff₀ hVz_pos]
            linarith [hVzlog]
          have hPle : Vsieve s / Vsieve z ≤ Real.log (z:ℝ) / cV := by
            have h1 : Vsieve s ≤ 1 := Vsieve_le_one s
            have h1' : Vsieve s * (1/Vsieve z) ≤ 1 * (Real.log (z:ℝ)/cV) :=
              mul_le_mul h1 h2 (by positivity) (by norm_num)
            calc Vsieve s / Vsieve z = Vsieve s * (1/Vsieve z) := by rw [div_eq_mul_one_div]
              _ ≤ 1 * (Real.log (z:ℝ)/cV) := h1'
              _ = Real.log (z:ℝ)/cV := by ring
          have hwN : w < (N₀:ℝ) := by
            have h1 : w ≤ (s:ℝ) := by rw [hsdef]; exact Nat.le_ceil w
            have h2' : (s:ℝ) < (N₀:ℝ) := by exact_mod_cast hsN
            linarith
          have hlogN_pos : 0 < Real.log (N₀:ℝ) := by
            apply Real.log_pos
            have h3s : (3:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs3
            have hsN' : (s:ℝ) < (N₀:ℝ) := by exact_mod_cast hsN
            linarith
          have hlogwN : Real.log w ≤ Real.log (N₀:ℝ) := Real.log_le_log (by linarith) (le_of_lt hwN)
          have hsq : Real.log w * Real.log w ≤ (Real.log (N₀:ℝ))^2 := by
            have h := mul_le_mul hlogwN hlogwN hlogw_pos.le hlogN_pos.le
            simpa [pow_two] using h
          have hKN' : (Real.log (N₀:ℝ))^2 ≤ cV * K := by
            have h := hKN
            rw [div_le_iff₀ hcV] at h
            linarith
          have hmain : Real.log w * Real.log w ≤ cV * Real.log w + cV * K := by
            have : 0 ≤ cV * Real.log w := mul_nonneg hcV.le hlogw_pos.le
            linarith
          have hkey : Real.log w / cV ≤ 1 + K / Real.log w := by
            have h1 : Real.log w * Real.log w ≤ (1 + K / Real.log w) * cV * Real.log w := by
              have heq : (1 + K/Real.log w)*cV*Real.log w = cV*Real.log w + cV*K := by
                field_simp
              rw [heq]; exact hmain
            have h2' := (mul_le_mul_iff_of_pos_right hlogw_pos).mp h1
            rwa [div_le_iff₀ hcV]
          have hcle : Real.log (z:ℝ) / cV ≤ (Real.log (z:ℝ)/Real.log w) * (1 + K/Real.log w) := by
            have heq : Real.log (z:ℝ)/cV = (Real.log (z:ℝ)/Real.log w)*(Real.log w/cV) := by
              field_simp
            rw [heq]
            exact mul_le_mul_of_nonneg_left hkey (div_nonneg hlogz_pos.le hlogw_pos.le)
          exact le_trans hPle hcle
      · -- z = 3
        have hz3' : z = 3 := by
          have hz3 : 3 ≤ z := by
            have : (2:ℝ) < (z:ℝ) := lt_of_le_of_lt h2 hwz
            have : 2 < z := by exact_mod_cast this
            omega
          omega
        have hs3' : s = 3 := by omega
        rw [hs3', hz3']
        rw [div_self (ne_of_gt (Vsieve_pos 3))]
        have h1 : 1 ≤ Real.log (3:ℝ)/Real.log w := by
          rw [le_div_iff₀ hlogw_pos]
          have hw3 : w ≤ 3 := by
            have : (z:ℝ) = 3 := by exact_mod_cast hz3'
            linarith [hwz]
          simpa using Real.log_le_log (by linarith) hw3
        have hA : (0:ℝ) ≤ Real.log (3:ℝ)/Real.log w :=
          div_nonneg (Real.log_nonneg (by norm_num)) hlogw_pos.le
        simpa using mul_le_mul h1 hlogw_ge1 (by norm_num : (0:ℝ) ≤ 1) hA

end Work.ChenPlan.H2
