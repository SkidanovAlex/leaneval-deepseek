import Mathlib
import Submission.Work.LinnikAreas2.SbcDefs
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaSum
import Submission.Commons.Analysis.PSeries.tsum_nat_rpow_neg_le
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex

namespace Work.LinnikAreas2

open Finset

noncomputable section

/-- `aWf` is multiplicative on coprime (nonzero) arguments. -/
lemma aWf_mul {r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t) (h : r.Coprime t) :
    aWf (r * t) = aWf r * aWf t := by
  have hr0 : r ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  unfold aWf
  rw [Nat.primeFactors_mul hr0 ht0, Finset.prod_union h.disjoint_primeFactors]

/-- `nu = μ·aWf` is multiplicative on coprime arguments. -/
lemma nu_mul {r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t) (h : r.Coprime t) :
    nu (r * t) = nu r * nu t := by
  unfold nu
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, aWf_mul hr ht h]
  push_cast
  ring

/-- `aWf n * invAWf n = 1`. -/
lemma aWf_mul_invAWf (n : ℕ) : aWf n * invAWf n = 1 := by
  unfold aWf invAWf
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The target summand rewritten with `nu`. -/
lemma bcTerm_eq (z r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    bcTerm z r t
      = (if r.Coprime t then (Real.pi ^ 2 / 6)⁻¹ * nu r * nu t * Wt z r t else 0) := by
  by_cases h : r.Coprime t
  · rw [if_pos h]
    simp only [bcTerm, Wt, nu]
    rw [if_pos h, show (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1)) = aWf (r * t)
      from rfl, aWf_mul hr ht h]
    ring
  · rw [if_neg h]
    simp only [bcTerm, if_neg h, zero_mul]

/-- For `1 ≤ r` and `r ≤ t`, `max ⌊z/t⌋ ⌊z/r⌋ = ⌊z/r⌋`. -/
lemma max_div_eq_right {z r t : ℕ} (hr : 1 ≤ r) (h : r ≤ t) : max (z / t) (z / r) = z / r :=
  max_eq_right (Nat.div_le_div_left h hr)

/-- The `r = t` summand vanishes for `r ≥ 2`. -/
lemma bcTerm_self_eq_zero (z r : ℕ) (hr : 2 ≤ r) : bcTerm z r r = 0 := by
  have h : ¬ r.Coprime r := by rw [Nat.coprime_self]; omega
  simp only [bcTerm]
  rw [if_neg h, zero_mul]

/-- `bcTerm z` is symmetric in `r`,`t`. -/
lemma bcTerm_symm (z r t : ℕ) : bcTerm z r t = bcTerm z t r := by
  unfold bcTerm
  by_cases h : r.Coprime t
  · rw [if_pos h, if_pos h.symm, max_comm (z / t) (z / r), Nat.mul_comm r t]
    ring
  · have h2 : ¬ t.Coprime r := fun hh => h hh.symm
    simp only [if_neg h, if_neg h2]
    ring

/-- The reindexing and the split into `r < t`, `r = t`, `r > t`. -/
lemma sum_split_reindex (z N : ℕ) (hz : 1 ≤ z) :
    (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)), bcTerm z r t)
      = bcTerm z 1 1 * ((N / z : ℕ) : ℝ)
        + 2 * ∑ t ∈ Finset.Icc 1 (N / z),
            ((N / (z * t) : ℕ) : ℝ) * ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t := by
  have hsym : ∀ r t : ℕ, bcTerm z r t = bcTerm z t r := bcTerm_symm z
  have hdiag : ∀ r : ℕ, 2 ≤ r → bcTerm z r r = 0 := bcTerm_self_eq_zero z
  -- Step A: the per-`q` split
  have hstep1 : ∀ M : ℕ, 1 ≤ M →
      (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, bcTerm z r t)
        = bcTerm z 1 1 + 2 * ∑ t ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t := by
    intro M hM
    have hfilter : ∀ t : ℕ, t ≤ M →
        (Finset.Icc 1 M).filter (fun r => r < t) = Finset.Icc 1 (t - 1) := by
      intro t htM
      apply Finset.ext
      intro r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hr1, _⟩, hrt⟩
        exact ⟨hr1, by omega⟩
      · rintro ⟨hr1, hr2⟩
        exact ⟨⟨hr1, by omega⟩, by omega⟩
    have hsplit : (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, bcTerm z r t)
        = (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if r < t then bcTerm z r t else 0))
          + (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if r = t then bcTerm z r t else 0))
          + (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if t < r then bcTerm z r t else 0)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hrt : r < t
      · rw [if_pos hrt, if_neg (ne_of_lt hrt), if_neg (not_lt.mpr (le_of_lt hrt))]
        ring
      · by_cases heq : r = t
        · rw [if_neg hrt, if_pos heq, if_neg (by rw [heq]; exact lt_irrefl t)]
          ring
        · have htr : t < r := lt_of_le_of_ne (le_of_not_gt hrt) (Ne.symm heq)
          rw [if_neg hrt, if_neg heq, if_pos htr]
          ring
    have hthird : (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if t < r then bcTerm z r t else 0))
        = ∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if r < t then bcTerm z r t else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : a < b
      · rw [if_pos h, if_pos h, hsym b a]
      · rw [if_neg h, if_neg h]
    have hdiagsum : (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if r = t then bcTerm z r t else 0))
        = bcTerm z 1 1 := by
      have h1 : ∀ r ∈ Finset.Icc 1 M,
          (∑ t ∈ Finset.Icc 1 M, (if r = t then bcTerm z r t else 0)) = bcTerm z r r := by
        intro r hr
        have hstep : (∑ t ∈ Finset.Icc 1 M, (if r = t then bcTerm z r t else 0))
            = (if r = r then bcTerm z r r else 0) :=
          Finset.sum_eq_single r (fun t _ htne => by rw [if_neg (Ne.symm htne)])
            (fun h => absurd hr h)
        rw [hstep, if_pos rfl]
      rw [Finset.sum_congr rfl h1]
      refine Finset.sum_eq_single 1 ?_ ?_
      · intro r hr hrne
        have hr2 : 2 ≤ r := by
          have := (Finset.mem_Icc.mp hr).1; omega
        exact hdiag r hr2
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩) h
    have hfirst : (∑ r ∈ Finset.Icc 1 M, ∑ t ∈ Finset.Icc 1 M, (if r < t then bcTerm z r t else 0))
        = ∑ t ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter, hfilter t (Finset.mem_Icc.mp ht).2]
    rw [hsplit, hthird, hdiagsum, hfirst]
    ring
  -- Step B: the `q`-reindexing
  have hstep2 : ∀ F : ℕ → ℝ,
      (∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / (q * z)), F t)
        = ∑ t ∈ Finset.Icc 1 (N / z), ((N / (z * t) : ℕ) : ℝ) * F t := by
    intro F
    have hQ : ∀ q ∈ Finset.Icc 1 (N / z), N / (q * z) ≤ N / z := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqz : z ≤ q * z := by nlinarith
      exact Nat.div_le_div_left hqz (by omega : 0 < z)
    have h1 : (∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / (q * z)), F t)
        = ∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / z),
            (if t ≤ N / (q * z) then F t else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hfil : (Finset.Icc 1 (N / z)).filter (fun t => t ≤ N / (q * z))
          = Finset.Icc 1 (N / (q * z)) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans h.2 (hQ q hq)⟩, h.2⟩⟩
      rw [← hfil, Finset.sum_filter]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ t ∈ Finset.Icc 1 (N / z),
        (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then F t else 0))
          = ((N / (z * t) : ℕ) : ℝ) * F t := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have hcard : (Finset.Icc 1 (N / z)).filter (fun q => t ≤ N / (q * z))
          = Finset.Icc 1 (N / (z * t)) := by
        have hzpos : 0 < z := by omega
        have hztpos : 0 < z * t := Nat.mul_pos hzpos (by omega : 0 < t)
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hq1, _⟩, hq3⟩
          have hqzpos : 0 < q * z := Nat.mul_pos (by omega : 0 < q) hzpos
          exact ⟨hq1, (Nat.le_div_iff_mul_le hztpos).mpr (by
            rw [show q * (z * t) = t * (q * z) by ring]
            exact (Nat.le_div_iff_mul_le hqzpos).mp hq3)⟩
        · rintro ⟨hq1, hq2⟩
          have hqzpos : 0 < q * z := Nat.mul_pos (by omega : 0 < q) hzpos
          refine ⟨⟨hq1, ?_⟩, ?_⟩
          · exact le_trans hq2 (Nat.div_le_div_left (Nat.le_mul_of_pos_right z (by omega : 0 < t)) hzpos)
          · exact (Nat.le_div_iff_mul_le hqzpos).mpr (by
              rw [show t * (q * z) = q * (z * t) by ring]
              exact (Nat.le_div_iff_mul_le hztpos).mp hq2)
      have hsplit : (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then F t else 0))
          = (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then (1 : ℝ) else 0)) * F t := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        by_cases hc : t ≤ N / (q * z)
        · rw [if_pos hc, if_pos hc, one_mul]
        · rw [if_neg hc, if_neg hc, zero_mul]
      have hcard2 : ((Finset.Icc 1 (N / z)).filter (fun q => t ≤ N / (q * z))).card
          = N / (z * t) := by
        rw [hcard, Nat.card_Icc]
        exact Nat.add_sub_cancel _ _
      have hb1 : (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then F t else 0))
          = (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then (1 : ℝ) else 0)) * F t := hsplit
      have hb2 : (∑ q ∈ Finset.Icc 1 (N / z), (if t ≤ N / (q * z) then (1 : ℝ) else 0))
          = ((Finset.Icc 1 (N / z)).filter (fun q => t ≤ N / (q * z))).card :=
        Finset.sum_boole (fun q => t ≤ N / (q * z)) (Finset.Icc 1 (N / z))
      rw [hb1, hb2, hcard2]
    apply Finset.sum_congr rfl
    intro t ht
    exact h2 t ht
  calc (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)), bcTerm z r t)
      = ∑ q ∈ Finset.Icc 1 (N / z), (bcTerm z 1 1
          + 2 * ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        refine hstep1 (N / (q * z)) ?_
        rw [Nat.le_div_iff_mul_le (Nat.mul_pos (by omega : 0 < q) (by omega : 0 < z))]
        calc 1 * (q * z) = q * z := one_mul _
          _ ≤ (N / z) * z := Nat.mul_le_mul_right z (Finset.mem_Icc.mp hq).2
          _ ≤ N := Nat.div_mul_le_self N z
    _ = bcTerm z 1 1 * ((N / z : ℕ) : ℝ)
        + 2 * ∑ t ∈ Finset.Icc 1 (N / z),
            ((N / (z * t) : ℕ) : ℝ) * ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
          ← Finset.mul_sum]
        rw [show ((((N / z) + 1 - 1 : ℕ)) : ℝ) * bcTerm z 1 1
            = bcTerm z 1 1 * ((N / z : ℕ) : ℝ) by
          rw [show (N / z) + 1 - 1 = N / z from Nat.add_sub_cancel _ _]; ring]
        rw [hstep2 (fun t => ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t)]

/-- `Wt z 1 1 = 2z`. -/
lemma Wt_one_one (z : ℕ) (hz : 1 ≤ z) : Wt z 1 1 = 2 * (z : ℝ) := by
  have hz0 : (z : ℝ) ≠ 0 := by positivity
  have hmax : max (z / 1) (z / 1) = z := by simp
  unfold Wt
  rw [hmax]
  have hl : (z : ℝ) * ((1 : ℕ) : ℝ) / (z : ℝ) = 1 := by
    rw [Nat.cast_one, mul_one, div_self hz0]
  rw [hl, Real.log_one]
  ring

/-- The `r = t = 1` summand. -/
lemma bcTerm_one_one (z : ℕ) (hz : 1 ≤ z) :
    bcTerm z 1 1 = (Real.pi ^ 2 / 6)⁻¹ * (2 * (z : ℝ)) := by
  rw [bcTerm_eq z 1 1 le_rfl le_rfl, if_pos (by decide : (1:ℕ).Coprime 1),
    Wt_one_one z hz]
  unfold nu aWf
  simp [Nat.primeFactors_one]

/-- The pointwise bound on `Fterm`. -/
lemma Fterm_abs_le (z r t : ℕ) (hz : 1 ≤ z) (hr : 1 ≤ r) (hrt : r < t) (htz : t ≤ z) :
    |Fterm z r t| ≤ ((r : ℝ) / (z : ℝ)) * Real.log ((t : ℝ) / (r : ℝ)) + 5 := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hrtR : (r : ℝ) < (t : ℝ) := by exact_mod_cast hrt
  have hmax : max (z / t) (z / r) = z / r := max_div_eq_right hr (le_of_lt hrt)
  set Y : ℕ := z / r with hY
  have hrY : Y * r ≤ z := by rw [hY]; exact Nat.div_mul_le_self z r
  have hYr : (Y : ℝ) * (r : ℝ) ≤ (z : ℝ) := by exact_mod_cast hrY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    have : 0 < Y := by rw [hY]; exact Nat.div_pos (by omega : r ≤ z) (by omega : 0 < r)
    exact_mod_cast this
  set u : ℝ := Real.log ((t : ℝ) / (r : ℝ)) with hu
  have hu_ge : 0 ≤ u := by
    rw [hu]
    apply Real.log_nonneg
    exact (le_div_iff₀ hrR).mpr (by linarith)
  set s : ℝ := (Y : ℝ) * (r : ℝ) / (z : ℝ) with hs
  have hs_pos : 0 < s := by rw [hs]; positivity
  have hs_le : s ≤ 1 := by rw [hs, div_le_one hzR]; exact hYr
  set w : ℝ := Real.log s with hw
  have hw_le : w ≤ 0 := Real.log_nonpos hs_pos.le hs_le
  set d : ℝ := (z : ℝ) / (r : ℝ) - (Y : ℝ) with hdd
  have hd_ge : 0 ≤ d := by
    rw [hdd]
    have : (Y : ℝ) ≤ (z : ℝ) / (r : ℝ) := (le_div_iff₀ hrR).mpr hYr
    linarith
  have hd_lt : d < 1 := by
    have heq : (z : ℝ) / (r : ℝ) - (Y : ℝ) = ((z % r : ℕ) : ℝ) / (r : ℝ) := by
      have h3 : ((z % r : ℕ) : ℝ) = (z : ℝ) - (Y : ℝ) * (r : ℝ) := by
        have h4 : z % r = z - Y * r := by
          have hh : Y * r + z % r = z := by
            have h2 := Nat.div_add_mod z r
            rw [← hY] at h2
            rw [Nat.mul_comm r Y] at h2
            exact h2
          omega
        rw [h4, Nat.cast_sub hrY]
        push_cast
        ring
      rw [h3]
      field_simp
    rw [hdd, heq, div_lt_one hrR]
    exact_mod_cast Nat.mod_lt z (by omega : 0 < r)
  have h1ms : (1 : ℝ) - s = d * ((r : ℝ) / (z : ℝ)) := by
    rw [hdd, hs]; field_simp
  have hYs : (Y : ℝ) * ((1 - s) / s) = d := by
    rw [h1ms, hs]; field_simp
  have hlog_le : -Real.log s ≤ (1 - s) / s := by
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / s by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hs_pos), Real.log_one] at h3
    rw [show (1 : ℝ) / s - 1 = (1 - s) / s by field_simp] at h3
    rw [show (0 : ℝ) - Real.log s = -Real.log s by ring] at h3
    linarith
  have hlogYt : Real.log ((Y : ℝ) * (t : ℝ) / (z : ℝ)) = w + u := by
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hmul : (Y : ℝ) * (t : ℝ) / (z : ℝ) = s * ((t : ℝ) / (r : ℝ)) := by
      rw [hs]; field_simp
    rw [hmul, hw, hu, Real.log_mul (ne_of_gt hs_pos) (ne_of_gt (div_pos htR hrR))]
  have hlogYr : Real.log ((Y : ℝ) * (r : ℝ) / (z : ℝ)) = w := by
    rw [← hs, hw]
  have hid : (Y : ℝ) * ((Real.log ((Y : ℝ) * (t : ℝ) / (z : ℝ)) - 1)
        * (Real.log ((Y : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1)
      - -(((z : ℝ) / (r : ℝ)) * (Real.log ((t : ℝ) / (r : ℝ)) - 2))
      = u * (d + (Y : ℝ) * w) + ((Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d) := by
    rw [hlogYt, hlogYr, ← hu, hdd]; ring
  have hub1 : |d + (Y : ℝ) * w| ≤ (r : ℝ) / (z : ℝ) := by
    have hψ0 : 0 ≤ 1 - s + s * w := by
      have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / s by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt hs_pos), Real.log_one] at h3
      have h4 : -Real.log s ≤ 1 / s - 1 := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt hs_pos)
      rw [show s * (1 / s - 1) = 1 - s by field_simp] at h5
      rw [hw]; linarith
    have hψle : 1 - s + s * w ≤ (1 - s) ^ 2 := by
      have h3 := Real.log_le_sub_one_of_pos hs_pos
      rw [hw]; nlinarith [h3]
    have hid1 : d + (Y : ℝ) * w = ((z : ℝ) / (r : ℝ)) * (1 - s + s * w) := by
      rw [hdd, hs, hw]; field_simp
    rw [hid1, abs_of_nonneg (mul_nonneg (by positivity) hψ0)]
    calc ((z : ℝ) / (r : ℝ)) * (1 - s + s * w)
        ≤ ((z : ℝ) / (r : ℝ)) * (1 - s) ^ 2 := mul_le_mul_of_nonneg_left hψle (by positivity)
      _ = d ^ 2 * ((r : ℝ) / (z : ℝ)) := by rw [h1ms]; field_simp
      _ ≤ (r : ℝ) / (z : ℝ) := by
          have hd1 : d ≤ 1 := le_of_lt hd_lt
          have hd2 : d ^ 2 ≤ 1 := by nlinarith [hd_ge, hd1]
          calc d ^ 2 * ((r : ℝ) / (z : ℝ)) ≤ 1 * ((r : ℝ) / (z : ℝ)) :=
                mul_le_mul_of_nonneg_right hd2 (by positivity)
            _ = (r : ℝ) / (z : ℝ) := one_mul _
  have hub2 : |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d| ≤ 5 := by
    have hYwabs : |(Y : ℝ) * w| ≤ 1 := by
      rw [hw, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hYpos) hw_le),
        show -((Y : ℝ) * Real.log s) = (Y : ℝ) * (-Real.log s) by ring]
      have := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hYpos)
      linarith [hYs, hd_lt]
    have hwabs : |w| ≤ 1 := by
      rw [hw, abs_of_nonpos hw_le]
      have h2 : (Y : ℝ) * (-Real.log s) ≤ d := by
        have := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hYpos)
        rwa [hYs] at this
      have h3 : -Real.log s ≤ d / (Y : ℝ) := by
        rw [le_div_iff₀ (by linarith)]
        linarith [h2]
      have h4 : d / (Y : ℝ) ≤ 1 := by
        have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by
          have : 1 ≤ Y := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr (by omega)
          rw [hY]; exact_mod_cast this
        rw [div_le_one (by linarith)]
        linarith [hd_lt]
      linarith
    obtain ⟨hwlo, hwhi⟩ := abs_le.mp hwabs
    have habs : |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w)| + |2 * d|
        = |(Y : ℝ) * w| * |w - 2| + 2 * |d| := by
      rw [show (Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) = ((Y : ℝ) * w) * (w - 2) by ring]
      rw [abs_mul]
      rw [show |2 * d| = 2 * |d| by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
    calc |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d|
        ≤ |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w)| + |2 * d| := by
          rw [show (Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d
            = ((Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w)) - 2 * d by ring]
          exact abs_sub _ _
      _ = |(Y : ℝ) * w| * |w - 2| + 2 * |d| := habs
      _ ≤ 1 * 3 + 2 * 1 := by
          apply add_le_add
          · apply mul_le_mul hYwabs _ (abs_nonneg _) (by norm_num)
            rw [abs_le]; constructor <;> linarith
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            rw [abs_le]; constructor <;> linarith [hd_ge, le_of_lt hd_lt]
      _ = 5 := by norm_num
  rw [Fterm, Wt, hmax, Mterm, hid]
  calc |u * (d + (Y : ℝ) * w) + ((Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d)|
      ≤ |u * (d + (Y : ℝ) * w)| + |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d| := abs_add_le _ _
    _ = u * |d + (Y : ℝ) * w| + |(Y : ℝ) * w ^ 2 - 2 * ((Y : ℝ) * w) - 2 * d| := by
        rw [abs_mul, abs_of_nonneg hu_ge]
    _ ≤ u * ((r : ℝ) / (z : ℝ)) + 5 := by
        have := mul_le_mul_of_nonneg_left hub1 hu_ge
        linarith [hub2]
    _ = ((r : ℝ) / (z : ℝ)) * u + 5 := by ring

/-- `|nu n| ≤ 1`. -/
lemma nu_abs_le_one (n : ℕ) : |nu n| ≤ 1 := by
  unfold nu
  rw [abs_mul]
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have h2 : |aWf n| ≤ 1 := by
    unfold aWf
    rw [abs_of_nonneg (Finset.prod_nonneg (fun p _ => by positivity))]
    apply Finset.prod_le_one₀ (fun p _ => by positivity)
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast (by omega : 1 ≤ p)
    rw [div_le_one (by linarith)]
    linarith
  calc |(ArithmeticFunction.moebius n : ℝ)| * |aWf n| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The error term is `O(t)`. -/
lemma errTerm_abs_le (z t : ℕ) (hz : 1 ≤ z) (ht : t ≤ z) :
    |errTerm z t| ≤ 7 * (t : ℝ) := by
  unfold errTerm
  have hnu : ∀ r : ℕ, |nu r| ≤ 1 := by
    intro r
    unfold nu
    rw [abs_mul]
    have h1 : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
    have h2 : |aWf r| ≤ 1 := by
      unfold aWf
      rw [abs_of_nonneg (Finset.prod_nonneg (fun p _ => by positivity))]
      apply Finset.prod_le_one₀ (fun p _ => by positivity)
      intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        exact_mod_cast (by omega : 1 ≤ p)
      rw [div_le_one (by linarith)]
      linarith
    calc |(ArithmeticFunction.moebius r : ℝ)| * |aWf r| ≤ 1 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hterm : ∀ r : ℕ, 1 ≤ r → r < t →
      |(if r.Coprime t then nu r * Fterm z r t else (0 : ℝ))|
        ≤ ((t : ℝ) - (r : ℝ)) / (z : ℝ) + 5 := by
    intro r hr1 hrt
    by_cases hc : r.Coprime t
    · rw [if_pos hc, abs_mul]
      have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hF := Fterm_abs_le z r t hz hr1 hrt ht
      have hstep : |nu r| * |Fterm z r t|
          ≤ 1 * (((r : ℝ) / (z : ℝ)) * Real.log ((t : ℝ) / (r : ℝ)) + 5) :=
        mul_le_mul (hnu r) hF (abs_nonneg _) (by norm_num)
      have hlog : (r : ℝ) * Real.log ((t : ℝ) / (r : ℝ)) ≤ (t : ℝ) - (r : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (t : ℝ) / (r : ℝ) by positivity)
        rw [Real.log_div (ne_of_gt htR) (ne_of_gt hrR)] at h
        have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hrR)
        have h3 : (r : ℝ) * ((t : ℝ) / (r : ℝ) - 1) = (t : ℝ) - (r : ℝ) := by field_simp
        rw [Real.log_div (ne_of_gt htR) (ne_of_gt hrR)]
        linarith [h2, h3]
      have hfin : ((r : ℝ) / (z : ℝ)) * Real.log ((t : ℝ) / (r : ℝ))
          ≤ ((t : ℝ) - (r : ℝ)) / (z : ℝ) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hlog (le_of_lt hzR)
      linarith [hstep, hfin]
    · rw [if_neg hc, abs_zero]
      have hrle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast (le_of_lt hrt)
      have h0 : 0 ≤ ((t : ℝ) - (r : ℝ)) / (z : ℝ) :=
        div_nonneg (by linarith) (le_of_lt hzR)
      linarith
  calc |∑ r ∈ Finset.Icc 1 (t - 1), (if r.Coprime t then nu r * Fterm z r t else (0 : ℝ))|
      ≤ ∑ r ∈ Finset.Icc 1 (t - 1),
          |(if r.Coprime t then nu r * Fterm z r t else (0 : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (t - 1), (6 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr2 : r ≤ t - 1 := (Finset.mem_Icc.mp hr).2
        have hrt : r < t := by omega
        refine le_trans (hterm r hr1 hrt) ?_
        have hrle : (r : ℝ) ≤ (t : ℝ) := by
          have := (Finset.mem_Icc.mp hr).2
          exact_mod_cast (by omega : r ≤ t)
        have h1 : ((t : ℝ) - (r : ℝ)) / (z : ℝ) ≤ 1 := by
          rw [div_le_one hzR]
          have htzR : (t : ℝ) ≤ (z : ℝ) := by exact_mod_cast ht
          linarith
        linarith
    _ = 6 * ((t - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring
    _ ≤ 7 * (t : ℝ) := by
        have h : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
          have h2 : t - 1 ≤ t := by omega
          exact_mod_cast h2
        nlinarith

/-- Telescoping of `Σ_{1 ≤ m ≤ M} (g m − g (m+1))`. -/
lemma sum_Icc_sub_tele (g : ℕ → ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (g m - g (m + 1))) = g 1 - g (M + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    ring

/-- `Σ_{m ≥ 1} 1/(m·log²(2+m))` converges. -/
lemma sum_inv_mul_logsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) ≤ C := by
  refine ⟨12, by norm_num, ?_⟩
  have hpt : ∀ m : ℕ, 1 ≤ m →
      1 / ((m : ℝ) * (Real.log ((m : ℝ) + 2)) ^ 2)
        ≤ 3 * (1 / Real.log ((m : ℝ) + 1) - 1 / Real.log ((m : ℝ) + 2)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : (0 : ℝ) < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
    have h2 : (0 : ℝ) < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith)
    have h1' : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have h2' : (0 : ℝ) < (m : ℝ) + 2 := by linarith
    have hle : Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 2) :=
      Real.log_le_log h1' (by linarith)
    have hkey : (1 : ℝ) ≤ (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) * ((m : ℝ) + 2) := by
      have hyi : (0 : ℝ) < (((m : ℝ) + 2) / ((m : ℝ) + 1))⁻¹ := by positivity
      have h := Real.log_le_sub_one_of_pos hyi
      rw [Real.log_inv] at h
      have hlogy : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
          = Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) :=
        Real.log_div (ne_of_gt h2') (ne_of_gt h1')
      rw [hlogy] at h
      have heq : (((m : ℝ) + 2) / ((m : ℝ) + 1))⁻¹ - 1 = -(1 / ((m : ℝ) + 2)) := by
        rw [inv_div]; field_simp; ring
      rw [heq] at h
      have hge : (1 : ℝ) / ((m : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by
        linarith
      have := mul_le_mul_of_nonneg_right hge (le_of_lt h2')
      rw [one_div_mul_cancel (ne_of_gt h2')] at this
      linarith
    have hexp2 : 1 / Real.log ((m : ℝ) + 1) - 1 / Real.log ((m : ℝ) + 2)
        = (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1))
            / (Real.log ((m : ℝ) + 1) * Real.log ((m : ℝ) + 2)) := by
      rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
      ring
    rw [hexp2, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hLd : (0 : ℝ) ≤ Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by linarith
    have h3m : (m : ℝ) + 2 ≤ 3 * (m : ℝ) := by linarith
    have hstep : (1 : ℝ) ≤ 3 * (m : ℝ) * (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) := by
      calc (1 : ℝ) ≤ (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) * ((m : ℝ) + 2) := hkey
        _ ≤ (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) * (3 * (m : ℝ)) :=
              mul_le_mul_of_nonneg_left h3m hLd
        _ = 3 * (m : ℝ) * (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) := by ring
    have hmul := mul_le_mul_of_nonneg_right hstep
      (show (0 : ℝ) ≤ (Real.log ((m : ℝ) + 2)) ^ 2 by positivity)
    nlinarith [hmul, hle, h1, h2, hLd]
  intro M
  calc (∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2))
      ≤ ∑ m ∈ Finset.Icc 1 M,
          3 * (1 / Real.log ((m : ℝ) + 1) - 1 / Real.log ((m : ℝ) + 2)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hh := hpt m (Finset.mem_Icc.mp hm).1
        rw [show (2 : ℝ) + (m : ℝ) = (m : ℝ) + 2 by ring]
        exact hh
    _ = 3 * (∑ m ∈ Finset.Icc 1 M,
          (1 / Real.log ((m : ℝ) + 1) - 1 / Real.log ((m : ℝ) + 2))) := by
        rw [Finset.mul_sum]
    _ = 3 * (∑ m ∈ Finset.Icc 1 M,
          (1 / Real.log ((m : ℝ) + 1) - 1 / Real.log ((((m + 1 : ℕ)) : ℝ) + 1))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro m _
        have harg : Real.log ((((m + 1 : ℕ)) : ℝ) + 1) = Real.log ((m : ℝ) + 2) := by
          congr 1
          push_cast
          ring
        rw [harg]
    _ = 3 * (1 / Real.log 2 - 1 / Real.log ((M : ℝ) + 2)) := by
        congr 1
        rw [sum_Icc_sub_tele (fun k : ℕ => 1 / Real.log ((k : ℝ) + 1)) M]
        have harg : Real.log ((((M + 1 : ℕ)) : ℝ) + 1) = Real.log ((M : ℝ) + 2) := by
          congr 1
          push_cast
          ring
        rw [harg]
        norm_num
    _ ≤ 3 * (1 / Real.log 2) := by
        have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        have : 0 ≤ 1 / Real.log ((M : ℝ) + 2) := by
          apply div_nonneg (by norm_num)
          exact le_of_lt (Real.log_pos (by linarith))
        linarith
    _ ≤ 12 := by
        have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
          have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
          rw [Real.log_div (by norm_num) (by norm_num)] at h
          simp at h
          linarith
        have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        rw [show (3 : ℝ) * (1 / Real.log 2) = 3 / Real.log 2 by ring, div_le_iff₀ hpos]
        linarith

/-- `(d : ℝ) ^ (-(3/2)) = 1/(d·√d)`. -/
lemma rpow_neg_three_halves (d : ℕ) :
    (d : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    push_cast
    rw [Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)]
    norm_num
  · have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast h
    have h1 : (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) ^ ((3 : ℝ) / 2) := by
      calc (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (1 / 2) := by
            rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = (d : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hd 1 (1 / 2)).symm
        _ = (d : ℝ) ^ ((3 : ℝ) / 2) := by norm_num
    rw [h1, one_div, ← Real.rpow_neg (le_of_lt hd)]

/-- `Σ_{d ≤ Q} d^{-3/2}` converges. -/
lemma inv_rpow_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ d ∈ Finset.Icc 1 Q, (d : ℝ) ^ (-(3 / 2 : ℝ))) ≤ C := by
  refine ⟨3, by norm_num, ?_⟩
  intro Q
  have hsum : Summable (fun d : ℕ => (d : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  calc (∑ d ∈ Finset.Icc 1 Q, (d : ℝ) ^ (-(3 / 2 : ℝ)))
      ≤ ∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
        hsum.sum_le_tsum _ (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ ≤ 1 + ((3 / 2 : ℝ) - 1)⁻¹ := Commons.Analysis.PSeries.tsum_nat_rpow_neg_le (by norm_num)
    _ = 3 := by norm_num

/-- `Σ_{n} σ_{-1/2}(n)/(n·log²(2+n))` converges. -/
lemma sigma_recip_logsq_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ t ∈ Finset.Icc 1 Q,
          (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2)) ≤ C := by
  obtain ⟨C1, hC1, hsum⟩ := sum_inv_mul_logsq_le
  obtain ⟨C2, hC2, hcube⟩ := inv_rpow_sum_le
  refine ⟨C1 * C2, by positivity, ?_⟩
  intro Q
  have hswap : (∑ t ∈ Finset.Icc 1 Q,
        (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
          / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2))
      = ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / d),
          (1 / Real.sqrt (d : ℝ))
            / (((d * m : ℕ) : ℝ) * (Real.log (2 + ((d * m : ℕ) : ℝ))) ^ 2) := by
    have h0 := Work.LinnikAreas.Density4.sum_Icc_div_reindex Q (fun _ => True)
      (fun d m => (1 / Real.sqrt (d : ℝ))
        / (((d * m : ℕ) : ℝ) * (Real.log (2 + ((d * m : ℕ) : ℝ))) ^ 2))
    simp only [Finset.filter_true] at h0
    rw [h0]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [hswap]
  have hpt : ∀ d m : ℕ, 1 ≤ d → 1 ≤ m →
      (1 / Real.sqrt (d : ℝ))
            / (((d * m : ℕ) : ℝ) * (Real.log (2 + ((d * m : ℕ) : ℝ))) ^ 2)
        ≤ (d : ℝ) ^ (-(3 / 2 : ℝ))
            * (1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) := by
    intro d m hd hm
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hdm : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hdm]
    have hpos1 : (0 : ℝ) < 2 + (m : ℝ) := by linarith
    have hpos2 : (0 : ℝ) < 2 + ((d : ℝ) * (m : ℝ)) := by linarith
    have hlogle : Real.log (2 + (m : ℝ)) ≤ Real.log (2 + ((d : ℝ) * (m : ℝ))) := by
      apply Real.log_le_log hpos1
      nlinarith
    have hlog2m : (0 : ℝ) < Real.log (2 + (m : ℝ)) := Real.log_pos (by linarith)
    have hlogdm : (0 : ℝ) < Real.log (2 + ((d : ℝ) * (m : ℝ))) := Real.log_pos (by linarith)
    have hsq : (Real.log (2 + (m : ℝ))) ^ 2 ≤ (Real.log (2 + ((d : ℝ) * (m : ℝ)))) ^ 2 := by
      nlinarith [hlogle, hlog2m, hlogdm]
    have hb : (1 : ℝ) / ((m : ℝ) * (Real.log (2 + ((d : ℝ) * (m : ℝ)))) ^ 2)
        ≤ 1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2) :=
      one_div_le_one_div_of_le (by positivity)
        (by nlinarith [hsq, hm0, sq_nonneg (Real.log (2 + (m : ℝ)))])
    calc (1 / Real.sqrt (d : ℝ)) / ((d : ℝ) * (m : ℝ) * (Real.log (2 + ((d : ℝ) * (m : ℝ)))) ^ 2)
        = (1 / ((d : ℝ) * Real.sqrt (d : ℝ)))
            * (1 / ((m : ℝ) * (Real.log (2 + ((d : ℝ) * (m : ℝ)))) ^ 2)) := by
          field_simp
      _ ≤ (1 / ((d : ℝ) * Real.sqrt (d : ℝ)))
            * (1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (d : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) := by
          rw [rpow_neg_three_halves d]

  calc (∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / d),
          (1 / Real.sqrt (d : ℝ))
            / (((d * m : ℕ) : ℝ) * (Real.log (2 + ((d * m : ℕ) : ℝ))) ^ 2))
      ≤ ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / d),
          (d : ℝ) ^ (-(3 / 2 : ℝ))
            * (1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro m hm
        exact hpt d m (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hm).1
    _ = ∑ d ∈ Finset.Icc 1 Q, (d : ℝ) ^ (-(3 / 2 : ℝ))
          * (∑ m ∈ Finset.Icc 1 (Q / d),
              1 / ((m : ℝ) * (Real.log (2 + (m : ℝ))) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q, (d : ℝ) ^ (-(3 / 2 : ℝ)) * C1 := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left (hsum (Q / d)) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = C1 * ∑ d ∈ Finset.Icc 1 Q, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ C1 * C2 := mul_le_mul_of_nonneg_left (hcube Q) (le_of_lt hC1)

/-- `aWf n = (∏_{p | n} (1 + 1/p))⁻¹`. -/
lemma aWf_eq_inv_prod (n : ℕ) :
    aWf n = (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))⁻¹ := by
  have h1 : aWf n
      = (∏ p ∈ n.primeFactors, (p : ℝ)) / (∏ p ∈ n.primeFactors, ((p : ℝ) + 1)) := by
    rw [aWf, Finset.prod_div_distrib]
  have h2 : (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
      = (∏ p ∈ n.primeFactors, ((p : ℝ) + 1)) / (∏ p ∈ n.primeFactors, (p : ℝ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by
      have := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast this.ne_zero
    field_simp
  rw [h1, h2, inv_div]

/-- The coprime reciprocal `ν`-sum decays (Graham (12) / An Lemma 12), from
`Work.LinnikAreas.JutilaPieces.MobiusKappaSum`. -/
lemma coprime_recip_nu_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      |∑ r ∈ Finset.Icc 1 t, (if r.Coprime t then nu r / (r : ℝ) else 0)|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * (Real.log (2 + (t : ℝ))) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := Work.LinnikAreas.JutilaPieces.MobiusKappaSum 2
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h2 := h (t : ℝ) t h1 ht
  rw [Nat.floor_natCast] at h2
  have heq : (∑ r ∈ Finset.Icc 1 t, (if r.Coprime t then nu r / (r : ℝ) else 0))
      = (∑ n ∈ (Finset.Icc 1 t).filter (fun n => Nat.Coprime n t),
          (ArithmeticFunction.moebius n : ℝ)
            / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime t
    · rw [if_pos hc, if_pos hc]
      unfold nu
      rw [aWf_eq_inv_prod n]
      have hn0 : (n : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hn).1; positivity
      have hppos : (0 : ℝ) < ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) :=
        Finset.prod_pos (fun p _ => by positivity)
      field_simp
    · simp only [if_neg hc]
  rw [heq]
  exact h2

/-- `wtTerm z t = -z·S2Term z t + errTerm z t`. -/
lemma wtTerm_eq (z t : ℕ) : wtTerm z t = -((z : ℝ) * S2Term z t) + errTerm z t := by
  unfold wtTerm S2Term errTerm Fterm Mterm
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 : (r : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hr).1; positivity
  by_cases h : r.Coprime t
  · rw [if_pos h, if_pos h, if_pos h]
    ring_nf
  · rw [if_neg h, if_neg h, if_neg h]
    ring

/-- `S2Term z t = ATerm z t - 2·B11Term z t` for `t ≥ 2`. -/
lemma S2Term_eq (z t : ℕ) (ht : 2 ≤ t) :
    S2Term z t = ATerm z t - 2 * B11Term z t := by
  have htop : 1 ≤ (t - 1) + 1 := by omega
  have hte : (t - 1) + 1 = t := by omega
  have hnt : ¬ t.Coprime t := by rw [Nat.coprime_self]; omega
  have hAI : Finset.Icc 1 t = Finset.Icc 1 ((t - 1) + 1) := congrArg (Finset.Icc 1) hte.symm
  have hA : ATerm z t
      = (∑ r ∈ Finset.Icc 1 (t - 1),
            (if r.Coprime t then nu r * Real.log ((t : ℝ) / (r : ℝ)) / (r : ℝ) else 0))
        + (if ((t - 1) + 1).Coprime t then
              nu ((t - 1) + 1) * Real.log ((t : ℝ) / (((t - 1) + 1 : ℕ) : ℝ))
                / (((t - 1) + 1 : ℕ) : ℝ) else 0) := by
    unfold ATerm
    rw [hAI, Finset.sum_Icc_succ_top htop]
  have hB : B11Term z t
      = (∑ r ∈ Finset.Icc 1 (t - 1), (if r.Coprime t then nu r / (r : ℝ) else 0))
        + (if ((t - 1) + 1).Coprime t then nu ((t - 1) + 1) / (((t - 1) + 1 : ℕ) : ℝ)
            else 0) := by
    unfold B11Term
    rw [hAI, Finset.sum_Icc_succ_top htop]
  rw [hA, hB, hte]
  simp only [hnt, if_false, add_zero]
  unfold S2Term
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 : (r : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hr).1; positivity
  by_cases h : r.Coprime t
  · rw [if_pos h, if_pos h, if_pos h]
    ring_nf
  · rw [if_neg h, if_neg h, if_neg h]
    ring

/-- The reciprocal Möbius sum is bounded. -/
lemma mu_recip_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      |∑ t ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius t : ℝ) / (t : ℝ)| ≤ C := by
  obtain ⟨c, C0, hc, hC0, hdec⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  refine ⟨max C0 1, lt_max_of_lt_right one_pos, ?_⟩
  intro Q
  rcases Nat.lt_or_ge Q 2 with hQ | hQ
  · interval_cases Q
    · rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)
    · have h1 : (∑ t ∈ Finset.Icc 1 (1:ℕ), (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))
          = 1 := by
        rw [Finset.Icc_self, Finset.sum_singleton]
        norm_num [ArithmeticFunction.moebius_apply_one]
      rw [h1, abs_one]
      exact le_max_right _ _
  · have h2 : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    have h := hdec (Q:ℝ) h2
    rw [Nat.floor_natCast] at h
    refine le_trans h ?_
    have hexp : Real.exp (-(c * Real.sqrt (Real.log (Q:ℝ)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ Real.sqrt (Real.log (Q:ℝ)) := Real.sqrt_nonneg _
        nlinarith [hc])
    have hC0le : C0 ≤ max C0 1 := le_max_left _ _
    have hpos : 0 < Real.exp (-(c * Real.sqrt (Real.log (Q:ℝ)))) := Real.exp_pos _
    nlinarith

/-- The floor-perturbation of the reciprocal Möbius sum. -/
lemma mu_floor_bounded (z N Q : ℕ) (hz : 1 ≤ z) :
    |∑ t ∈ Finset.Icc 1 Q,
        (ArithmeticFunction.moebius t : ℝ)
          * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)))|
      ≤ (Q : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ t : ℕ,
      |(ArithmeticFunction.moebius t : ℝ)
          * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)))| ≤ 1 := by
    intro t
    set θ : ℝ := ((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)) with hθ
    have hle : ((N / (z * t) : ℕ) : ℝ) ≤ (N : ℝ) / ((z : ℝ) * (t : ℝ)) := by
      have h2 := Nat.cast_div_le (α := ℝ) (m := N) (n := z * t)
      push_cast at h2
      exact h2
    have hfl : ⌊(N : ℝ) / ((z : ℝ) * (t : ℝ))⌋₊ = N / (z * t) := by
      rw [show (N : ℝ) / ((z : ℝ) * (t : ℝ)) = (N : ℝ) / ((z * t : ℕ) : ℝ) by push_cast; ring]
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    have hlt : (N : ℝ) / ((z : ℝ) * (t : ℝ)) < ((N / (z * t) : ℕ) : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((N : ℝ) / ((z : ℝ) * (t : ℝ)))
      rwa [hfl] at h
    have hθ1 : θ ≤ 0 := by rw [hθ]; linarith
    have hθ2 : -1 < θ := by rw [hθ]; linarith
    have hθabs : |θ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul]
    have hmu : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t)
    calc |(ArithmeticFunction.moebius t : ℝ)| * |θ| ≤ 1 * 1 :=
          mul_le_mul hmu hθabs (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc ∑ t ∈ Finset.Icc 1 Q,
        |(ArithmeticFunction.moebius t : ℝ)
          * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)))|
      ≤ ∑ _t ∈ Finset.Icc 1 Q, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hterm t)
    _ = (Q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

/-- `S2Term` is close to `ζ(2)·∏_{p|t}(p+1)/p` (for all `t ≥ 1`). -/
lemma S2Term_close :
    ∃ C : ℝ, 0 < C ∧ ∀ (z t : ℕ), 1 ≤ t →
      |S2Term z t - (Real.pi ^ 2 / 6) * invAWf t|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            / (Real.log (2 + (t : ℝ))) ^ 2 := by
  obtain ⟨CA, hCA, hA⟩ := Work.LinnikAreas.Density4.mu_kappa_log_sum
  obtain ⟨CB, hCB, hB⟩ := coprime_recip_nu_decay
  refine ⟨max ((Real.pi^2/6) * (Real.log 3)^2) (4*CA + 2*CB), ?_, ?_⟩
  · exact lt_max_of_lt_left (by positivity)
  · intro z t ht
    rcases eq_or_lt_of_le ht with h1 | h2
    · subst h1
      have hS : S2Term z 1 = 0 := by
        unfold S2Term
        rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty]
      have hi : invAWf 1 = 1 := by unfold invAWf; simp [Nat.primeFactors_one]
      have hσ : (∑ d ∈ (1:ℕ).divisors, 1 / Real.sqrt (d : ℝ)) = 1 := by
        rw [Nat.divisors_one, Finset.sum_singleton]; norm_num
      have h1' : |S2Term z 1 - (Real.pi^2/6) * invAWf 1| = Real.pi^2/6 := by
        rw [hS, hi, mul_one, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      rw [h1', hσ, mul_one, show Real.log (2 + ((1:ℕ):ℝ)) = Real.log 3 by norm_num,
        le_div_iff₀ (by positivity : (0:ℝ) < (Real.log 3)^2)]
      exact le_max_left _ _
    · have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hσ0 : 0 ≤ (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) :=
        Finset.sum_nonneg (fun d _ => by positivity)
      have hp1 : (0:ℝ) < (Real.log (t:ℝ))^2 := by
        have : (1:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 1 < t)
        have := Real.log_pos this; positivity
      have hp2 : (0:ℝ) < (Real.log (2 + (t:ℝ)))^2 := by
        have : (1:ℝ) < 2 + (t:ℝ) := by
          have : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast h2
          linarith
        have := Real.log_pos this; positivity
      have hlog4 : (Real.log (2 + (t:ℝ)))^2 ≤ 4 * (Real.log (t:ℝ))^2 := by
        have ht2 : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast h2
        have hlogt : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg (by linarith)
        have hmul : Real.log ((t:ℝ)*(t:ℝ)) = 2 * Real.log (t:ℝ) := by
          rw [Real.log_mul (by linarith) (by linarith)]; ring
        have hle' : Real.log (2 + (t:ℝ)) ≤ Real.log ((t:ℝ)*(t:ℝ)) :=
          Real.log_le_log (by linarith) (by nlinarith)
        have h2t : Real.log (2 + (t:ℝ)) ≤ 2 * Real.log (t:ℝ) := by rw [← hmul]; exact hle'
        have hnn : 0 ≤ Real.log (2 + (t:ℝ)) := Real.log_nonneg (by linarith)
        nlinarith
      have hAt : |ATerm z t - (Real.pi^2/6) * invAWf t|
          ≤ CA * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / (Real.log (t:ℝ))^2 := by
        have h := hA t t (by omega) (by omega)
        have hform1 : (∑ n ∈ (Finset.Icc 1 t).filter (fun n => Nat.Coprime n t),
              (ArithmeticFunction.moebius n : ℝ)
                * (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
                * (Real.log (t : ℝ) - Real.log (n : ℝ)) / (n : ℝ)) = ATerm z t := by
          simp only [ATerm, Finset.sum_filter, nu, aWf]
          refine Finset.sum_congr rfl (fun n hn => ?_)
          by_cases hc : n.Coprime t
          · have hn0 : (n:ℝ) ≠ 0 := by
              have := (Finset.mem_Icc.mp hn).1; positivity
            have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
            simp only [if_pos hc, Real.log_div (ne_of_gt htR) hn0]
          · simp only [if_neg hc]
        have hinv : (Real.pi^2/6) * (∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ))
            = (Real.pi^2/6) * invAWf t := by simp only [invAWf]
        rw [hform1, hinv] at h
        exact h
      have hBt : |B11Term z t| ≤ CB * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            / (Real.log (2 + (t:ℝ)))^2 := by
        have h := hB t (by omega)
        have hlogpos : 0 < Real.log (2 + (t:ℝ)) :=
          Real.log_pos (by linarith : (1:ℝ) < 2 + (t:ℝ))
        have hrp : (Real.log (2 + (t:ℝ))) ^ (-(2:ℝ)) = 1 / (Real.log (2 + (t:ℝ)))^2 := by
          rw [Real.rpow_neg (le_of_lt hlogpos)]
          simp
        rw [hrp, mul_one_div] at h
        unfold B11Term
        exact h
      have hA5 : |ATerm z t - (Real.pi^2/6) * invAWf t|
          ≤ 4 * CA * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / (Real.log (2 + (t:ℝ)))^2 := by
        have hCAσ : 0 ≤ CA * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) :=
          mul_nonneg (le_of_lt hCA) hσ0
        refine le_trans hAt ?_
        rw [div_le_div_iff₀ hp1 hp2]
        nlinarith [hlog4, hCAσ]
      have hkey : |S2Term z t - (Real.pi^2/6) * invAWf t|
          ≤ |ATerm z t - (Real.pi^2/6) * invAWf t| + 2 * |B11Term z t| := by
        have := S2Term_eq z t h2
        calc |S2Term z t - (Real.pi^2/6) * invAWf t|
            = |(ATerm z t - (Real.pi^2/6) * invAWf t) - 2 * B11Term z t| := by
              rw [this]; ring_nf
          _ ≤ |ATerm z t - (Real.pi^2/6) * invAWf t| + |2 * B11Term z t| := abs_sub _ _
          _ = |ATerm z t - (Real.pi^2/6) * invAWf t| + 2 * |B11Term z t| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have hCmax : 4*CA + 2*CB ≤
          max ((Real.pi^2/6) * (Real.log 3)^2) (4*CA + 2*CB) := le_max_right _ _
      have hfin : |S2Term z t - (Real.pi^2/6) * invAWf t|
          ≤ (4*CA + 2*CB) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t:ℝ)))^2 := by
        have h2B : 2 * |B11Term z t| ≤ 2 * (CB * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t:ℝ)))^2) := by linarith [hBt]
        have hcomb : 4 * CA * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t:ℝ)))^2
            + 2 * (CB * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t:ℝ)))^2)
            = (4*CA + 2*CB) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t:ℝ)))^2 := by ring
        linarith [hkey, hA5, h2B, hcomb]
      rw [le_div_iff₀ hp2]
      rw [le_div_iff₀ hp2] at hfin
      nlinarith [hfin, hCmax, hσ0]

/-- Main theorem. -/
theorem s3_hard_error_BC : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    |(∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        (if r.Coprime t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
        ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
          * ((max (z / t) (z / r) : ℕ) : ℝ)
          * ((Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ)) - 1)
              * (Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ)) - 1) + 1)))| ≤ C * (N : ℝ) := by
  obtain ⟨C1, hC1, hSig⟩ := sigma_recip_logsq_sum
  obtain ⟨C3, hC3, hS2c⟩ := S2Term_close
  obtain ⟨C4, hC4, hMu⟩ := mu_recip_bounded
  have hζ1 : (1 : ℝ) ≤ Real.pi ^ 2 / 6 := by nlinarith [Real.pi_gt_three]
  have hζ0 : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  refine ⟨20 * (C4 + C3 * C1 + 1), by positivity, ?_⟩
  intro z N hz2 hzN hNz
  have hz1 : 1 ≤ z := by omega
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hQz : N / z ≤ z := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega : 0 < z)]
    nlinarith
  change |(∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)), bcTerm z r t)| ≤ 20 * (C4 + C3 * C1 + 1) * (N : ℝ)
  rw [sum_split_reindex z N hz1]
  set Q : ℕ := N / z with hQdef
  set R : ℝ := ∑ t ∈ Finset.Icc 1 Q,
      ((N / (z * t) : ℕ) : ℝ) * ∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t with hRdef
  have hbc : ∀ t : ℕ, (∑ r ∈ Finset.Icc 1 (t - 1), bcTerm z r t)
      = (Real.pi ^ 2 / 6)⁻¹ * nu t * wtTerm z t := by
    intro t
    rcases Nat.eq_zero_or_pos t with h0 | ht1
    · subst h0
      have h1 : (Finset.Icc 1 (0 - 1) : Finset ℕ) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]; norm_num
      rw [h1, Finset.sum_empty]
      unfold wtTerm
      rw [h1, Finset.sum_empty]
      ring
    · unfold wtTerm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      rw [bcTerm_eq z r t hr1 ht1]
      by_cases hc : r.Coprime t
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc, mul_zero]
  have hR1 : R = (Real.pi ^ 2 / 6)⁻¹ *
      (∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * wtTerm z t)) := by
    rw [hRdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hbc t]; ring
  have hR2 : (∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * wtTerm z t))
      = -((z : ℝ) * (∑ t ∈ Finset.Icc 1 Q,
            ((N / (z * t) : ℕ) : ℝ) * (nu t * S2Term z t)))
        + ∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [wtTerm_eq z t]; ring
  have hR3 : (∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * S2Term z t))
      = (Real.pi ^ 2 / 6) * (∑ t ∈ Finset.Icc 1 Q,
            ((N / (z * t) : ℕ) : ℝ) * (ArithmeticFunction.moebius t : ℝ))
        + ∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) *
            (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    have hnu : nu t * invAWf t = (ArithmeticFunction.moebius t : ℝ) := by
      unfold nu; rw [mul_assoc, aWf_mul_invAWf, mul_one]
    have hexp : nu t * S2Term z t = (Real.pi ^ 2 / 6) * (nu t * invAWf t)
        + nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t) := by ring
    rw [hexp, hnu]; ring
  -- bounds on the three pieces
  have hSigMu : |∑ t ∈ Finset.Icc 1 Q,
        ((N / (z * t) : ℕ) : ℝ) * (ArithmeticFunction.moebius t : ℝ)|
      ≤ (N : ℝ) / (z : ℝ) * C4 + (Q : ℝ) := by
    have hsplit : (∑ t ∈ Finset.Icc 1 Q,
          ((N / (z * t) : ℕ) : ℝ) * (ArithmeticFunction.moebius t : ℝ))
        = ((N : ℝ) / (z : ℝ)) * (∑ t ∈ Finset.Icc 1 Q,
              (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))
          + ∑ t ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius t : ℝ)
              * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have ht0 : (t : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hsplit]
    have h2 := hMu Q
    have h3 := mu_floor_bounded z N Q hz1
    have h4 : |((N : ℝ) / (z : ℝ)) * (∑ t ∈ Finset.Icc 1 Q,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))| ≤ (N : ℝ) / (z : ℝ) * C4 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc |((N : ℝ) / (z : ℝ)) * (∑ t ∈ Finset.Icc 1 Q,
            (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))
          + ∑ t ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius t : ℝ)
              * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)))|
        ≤ |((N : ℝ) / (z : ℝ)) * (∑ t ∈ Finset.Icc 1 Q,
              (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))|
          + |∑ t ∈ Finset.Icc 1 Q, (ArithmeticFunction.moebius t : ℝ)
              * (((N / (z * t) : ℕ) : ℝ) - (N : ℝ) / ((z : ℝ) * (t : ℝ)))| := abs_add_le _ _
      _ ≤ (N : ℝ) / (z : ℝ) * C4 + (Q : ℝ) := add_le_add h4 h3
  have hSigE : |∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) *
        (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t))|
      ≤ (N : ℝ) / (z : ℝ) * (C3 * C1) := by
    have hnu : ∀ t : ℕ, |nu t| ≤ 1 := nu_abs_le_one
    have hkey : ∀ t ∈ Finset.Icc 1 Q,
        |((N / (z * t) : ℕ) : ℝ) * (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t))|
          ≤ (N : ℝ) / (z : ℝ) * (C3 *
              ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2))) := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have hS2 := hS2c z t ht1
      have hW : ((N / (z * t) : ℕ) : ℝ) ≤ (N : ℝ) / ((z : ℝ) * (t : ℝ)) := by
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := z * t)
        push_cast at this
        exact this
      have htR : (0 : ℝ) < (t : ℝ) := by positivity
      have hlogpos : (0 : ℝ) < Real.log (2 + (t : ℝ)) := Real.log_pos (by linarith [ht1])
      have hσ0 : 0 ≤ (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) :=
        Finset.sum_nonneg (fun d _ => by positivity)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
      have h2 : |nu t| * |S2Term z t - (Real.pi ^ 2 / 6) * invAWf t|
          ≤ 1 * (C3 * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              / (Real.log (2 + (t : ℝ))) ^ 2) :=
        mul_le_mul (hnu t) hS2 (abs_nonneg _) (by norm_num)
      calc ((N / (z * t) : ℕ) : ℝ)
            * (|nu t| * |S2Term z t - (Real.pi ^ 2 / 6) * invAWf t|)
          ≤ ((N : ℝ) / ((z : ℝ) * (t : ℝ)))
              * (1 * (C3 * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                  / (Real.log (2 + (t : ℝ))) ^ 2)) := by
            apply mul_le_mul hW h2 (by positivity) (by positivity)
        _ = (N : ℝ) / (z : ℝ) * (C3 *
              ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2))) := by
            field_simp
    calc |∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) *
          (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t))|
        ≤ ∑ t ∈ Finset.Icc 1 Q, |((N / (z * t) : ℕ) : ℝ) *
            (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.Icc 1 Q, (N : ℝ) / (z : ℝ) * (C3 *
              ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2))) :=
          Finset.sum_le_sum hkey
      _ = (N : ℝ) / (z : ℝ) * (C3 * ∑ t ∈ Finset.Icc 1 Q,
              (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                / ((t : ℝ) * (Real.log (2 + (t : ℝ))) ^ 2)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (N : ℝ) / (z : ℝ) * (C3 * C1) := by
          have hsum := hSig Q
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (le_of_lt hC3)) (by positivity)
  have hSigErr : |∑ t ∈ Finset.Icc 1 Q,
        ((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t)| ≤ 7 * (N : ℝ) := by
    have hkey : ∀ t ∈ Finset.Icc 1 Q,
        |((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t)| ≤ 7 * (N : ℝ) / (z : ℝ) := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htz : t ≤ z := le_trans (Finset.mem_Icc.mp ht).2 hQz
      have herr := errTerm_abs_le z t hz1 htz
      have hW : ((N / (z * t) : ℕ) : ℝ) ≤ (N : ℝ) / ((z : ℝ) * (t : ℝ)) := by
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := z * t)
        push_cast at this
        exact this
      have htR : (0 : ℝ) < (t : ℝ) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
      have h2 : |nu t| * |errTerm z t| ≤ 1 * (7 * (t : ℝ)) :=
        mul_le_mul (nu_abs_le_one t) herr (abs_nonneg _) (by norm_num)
      calc ((N / (z * t) : ℕ) : ℝ) * (|nu t| * |errTerm z t|)
          ≤ ((N : ℝ) / ((z : ℝ) * (t : ℝ))) * (1 * (7 * (t : ℝ))) :=
            mul_le_mul hW h2 (by positivity) (by positivity)
        _ = 7 * (N : ℝ) / (z : ℝ) := by field_simp
    calc |∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t)|
        ≤ ∑ t ∈ Finset.Icc 1 Q,
            |((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.Icc 1 Q, 7 * (N : ℝ) / (z : ℝ) := Finset.sum_le_sum hkey
      _ = (Q : ℝ) * (7 * (N : ℝ) / (z : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; push_cast; ring
      _ ≤ 7 * (N : ℝ) := by
          have hQzR : (Q : ℝ) ≤ (z : ℝ) := by exact_mod_cast hQz
          rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hzR]
          nlinarith [hQzR, hNR]
  have hR : |R| ≤ (N : ℝ) * (C4 + C3 * C1 + 8) := by
    set S1 : ℝ := ∑ t ∈ Finset.Icc 1 Q,
      ((N / (z * t) : ℕ) : ℝ) * (ArithmeticFunction.moebius t : ℝ) with hS1
    set S2 : ℝ := ∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) *
      (nu t * (S2Term z t - (Real.pi ^ 2 / 6) * invAWf t)) with hS2
    set S3 : ℝ := ∑ t ∈ Finset.Icc 1 Q,
      ((N / (z * t) : ℕ) : ℝ) * (nu t * errTerm z t) with hS3
    have hsum : (∑ t ∈ Finset.Icc 1 Q, ((N / (z * t) : ℕ) : ℝ) * (nu t * wtTerm z t))
        = -((z : ℝ) * ((Real.pi ^ 2 / 6) * S1 + S2)) + S3 := by
      rw [hS1, hS2, hS3, hR2, hR3]
    rw [hR1, hsum]
    have hA : |S1| ≤ (N : ℝ) / (z : ℝ) * C4 + (Q : ℝ) := hSigMu
    have hB : |S2| ≤ (N : ℝ) / (z : ℝ) * (C3 * C1) := hSigE
    have hC : |S3| ≤ 7 * (N : ℝ) := hSigErr
    have hzS1 : |(z : ℝ) * ((Real.pi ^ 2 / 6) * S1)|
        ≤ (z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ))) := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hzR), abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA (by positivity)) (le_of_lt hzR)
    have hzS2 : |(z : ℝ) * S2| ≤ (z : ℝ) * ((N : ℝ) / (z : ℝ) * (C3 * C1)) := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hzR)]
      exact mul_le_mul_of_nonneg_left hB (le_of_lt hzR)
    have hstep : |(Real.pi ^ 2 / 6)⁻¹ * (-((z : ℝ) * ((Real.pi ^ 2 / 6) * S1 + S2)) + S3)|
        ≤ (Real.pi ^ 2 / 6)⁻¹ * ((z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ))
            + (N : ℝ) / (z : ℝ) * (C3 * C1)) + 7 * (N : ℝ)) := by
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hζ0))]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hζ0))
      have h2 := abs_add_le (-((z : ℝ) * ((Real.pi ^ 2 / 6) * S1) + (z : ℝ) * S2)) S3
      rw [abs_neg] at h2
      have h3 : |(z : ℝ) * ((Real.pi ^ 2 / 6) * S1) + (z : ℝ) * S2|
          ≤ (z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ)))
            + (z : ℝ) * ((N : ℝ) / (z : ℝ) * (C3 * C1)) :=
        (abs_add_le _ _).trans (add_le_add hzS1 hzS2)
      have hU : -((z : ℝ) * ((Real.pi ^ 2 / 6) * S1 + S2)) + S3
          = -((z : ℝ) * ((Real.pi ^ 2 / 6) * S1) + (z : ℝ) * S2) + S3 := by ring
      have hBig : (z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ))
            + (N : ℝ) / (z : ℝ) * (C3 * C1)) + 7 * (N : ℝ)
          = (z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ)))
            + (z : ℝ) * ((N : ℝ) / (z : ℝ) * (C3 * C1)) + 7 * (N : ℝ) := by ring
      rw [hU, hBig]
      linarith [h2, h3, hC]
    refine hstep.trans ?_
    have hzQ : (z : ℝ) * (Q : ℝ) ≤ (N : ℝ) := by
      rw [hQdef]; exact_mod_cast Nat.mul_div_le N z
    have hinv : (Real.pi ^ 2 / 6)⁻¹ ≤ 1 := by rw [inv_le_one₀ hζ0]; exact hζ1
    rw [show (Real.pi ^ 2 / 6)⁻¹ * ((z : ℝ) * ((Real.pi ^ 2 / 6) * ((N : ℝ) / (z : ℝ) * C4 + (Q : ℝ))
          + (N : ℝ) / (z : ℝ) * (C3 * C1)) + 7 * (N : ℝ))
        = (N : ℝ) * C4 + (z : ℝ) * (Q : ℝ) + (N : ℝ) * (C3 * C1) * (Real.pi ^ 2 / 6)⁻¹
          + 7 * (N : ℝ) * (Real.pi ^ 2 / 6)⁻¹ by
      field_simp]
    have h1 := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ (N : ℝ) * (C3 * C1))
    have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 7 * (N : ℝ))
    nlinarith [hzQ, h1, h2, hC3, hC1, hC4, hNR]
  have hRabs : |R| ≤ (N : ℝ) * (C4 + C3 * C1 + 8) := hR
  have hdiag : |bcTerm z 1 1 * (Q : ℝ)| ≤ 2 * (N : ℝ) := by
    rw [bcTerm_one_one z hz1]
    have hnn : 0 ≤ (Real.pi ^ 2 / 6)⁻¹ * (2 * (z : ℝ)) * (Q : ℝ) := by positivity
    rw [abs_of_nonneg hnn]
    have hzQ : (z : ℝ) * (Q : ℝ) ≤ (N : ℝ) := by
      rw [hQdef]; exact_mod_cast Nat.mul_div_le N z
    have hζinv : (Real.pi ^ 2 / 6)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hζ0]; exact hζ1
    calc (Real.pi ^ 2 / 6)⁻¹ * (2 * (z : ℝ)) * (Q : ℝ)
        = (Real.pi ^ 2 / 6)⁻¹ * (2 * ((z : ℝ) * (Q : ℝ))) := by ring
      _ ≤ 1 * (2 * (N : ℝ)) := by
          apply mul_le_mul hζinv _ (by positivity) (by norm_num)
          linarith
      _ = 2 * (N : ℝ) := by ring
  have hNfac : (0:ℝ) ≤ (N : ℝ) := hNR
  calc |bcTerm z 1 1 * (Q : ℝ) + 2 * R|
      ≤ |bcTerm z 1 1 * (Q : ℝ)| + |2 * R| := abs_add_le _ _
    _ ≤ 2 * (N : ℝ) + 2 * ((N : ℝ) * (C4 + C3 * C1 + 8)) := by
        apply add_le_add hdiag
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hRabs (by norm_num)
    _ ≤ 20 * (C4 + C3 * C1 + 1) * (N : ℝ) := by
        have hC3C1 : 0 < C3 * C1 := mul_pos hC3 hC1
        rw [show 2 * (N : ℝ) + 2 * ((N : ℝ) * (C4 + C3 * C1 + 8))
              = (N : ℝ) * (2 + 2 * (C4 + C3 * C1 + 8)) by ring]
        rw [show 20 * (C4 + C3 * C1 + 1) * (N : ℝ)
              = (N : ℝ) * (20 * (C4 + C3 * C1 + 1)) by ring]
        apply mul_le_mul_of_nonneg_left _ hNR
        linarith [hC1, hC3, hC4, hC3C1]

end

end Work.LinnikAreas2
