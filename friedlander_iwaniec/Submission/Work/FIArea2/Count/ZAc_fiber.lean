import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Count.class_delta_sum_le

set_option maxHeartbeats 2000000

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `gcd (gcd m b) c ≤ gcd m c` for `m ≠ 0`. -/
private lemma gcd_gcd_le_gcd_left {m b c : ℕ} (hm : m ≠ 0) :
    Nat.gcd (Nat.gcd m b) c ≤ Nat.gcd m c :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left hm))
    (Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _))

/-- `Σ_{d | m} φ(d) τ(d)³/d ≤ τ(m)⁴`. -/
lemma sum_totient_mul_tau_cube_div_le (m : ℕ) :
    (∑ d ∈ m.divisors, (Nat.totient d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)))
      ≤ (((m.divisors.card : ℝ))) ^ 4 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hterm : ∀ d ∈ m.divisors,
        (Nat.totient d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))
          ≤ (((m.divisors.card : ℝ))) ^ 3 := by
      intro d hd
      obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
      have hdne : d ≠ 0 := by
        intro h
        rw [h] at hdm
        exact hm (Nat.eq_zero_of_zero_dvd hdm)
      have hsub : d.divisors ⊆ m.divisors := Nat.divisors_subset_of_dvd hm hdm
      have hcard : ((d.divisors.card : ℝ)) ≤ ((m.divisors.card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hsub
      have hphi : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hdne
      have h3 : ((d.divisors.card : ℝ)) ^ 3 ≤ ((m.divisors.card : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hcard 3
      calc (Nat.totient d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))
          ≤ (d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hphi (by positivity)
        _ = ((d.divisors.card : ℝ)) ^ 3 := by field_simp
        _ ≤ ((m.divisors.card : ℝ)) ^ 3 := h3
    calc (∑ d ∈ m.divisors, (Nat.totient d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)))
        ≤ ∑ d ∈ m.divisors, (((m.divisors.card : ℝ))) ^ 3 := Finset.sum_le_sum hterm
      _ = ((m.divisors.card : ℝ)) * (((m.divisors.card : ℝ))) ^ 3 := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((m.divisors.card : ℝ))) ^ 4 := by ring

/-- Swapping a sum against the `gcd` expansion `gcd m Δ = Σ_{d | m, d | Δ} φ(d)`. -/
lemma sum_mul_gcd_eq_totient {α : Type*} [DecidableEq α] (P : Finset α) (Δ : α → ℕ) (w : α → ℝ)
    (m : ℕ) (hm : m ≠ 0) (hw : ∀ p ∈ P, Δ p = 0 → w p = 0) :
    (∑ p ∈ P, w p * (Nat.gcd m (Δ p) : ℝ))
      = ∑ d ∈ m.divisors, (Nat.totient d : ℝ) * ∑ p ∈ P.filter (fun p => d ∣ Δ p ∧ Δ p ≠ 0), w p := by
  have hpt : ∀ p ∈ P, w p * (Nat.gcd m (Δ p) : ℝ)
      = ∑ d ∈ m.divisors, if (d ∣ Δ p ∧ Δ p ≠ 0) then w p * (Nat.totient d : ℝ) else 0 := by
    intro p hp
    by_cases hΔ : Δ p = 0
    · have hw0 : w p = 0 := hw p hp hΔ
      rw [hw0, hΔ, Nat.gcd_zero_right, zero_mul]
      exact (Finset.sum_eq_zero (fun d _ => by simp)).symm
    · have hset : (Nat.gcd m (Δ p)).divisors = m.divisors.filter (fun d => d ∣ Δ p) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨⟨hdm, hdΔ⟩, _⟩
          exact ⟨⟨hdm, hm⟩, hdΔ⟩
        · rintro ⟨⟨hdm, _⟩, hdΔ⟩
          exact ⟨⟨hdm, hdΔ⟩, Nat.gcd_ne_zero_left hm⟩
      have h1 : (Nat.gcd m (Δ p) : ℝ)
          = ∑ d ∈ (Nat.gcd m (Δ p)).divisors, (Nat.totient d : ℝ) := by
        rw [← Nat.cast_sum, Nat.sum_totient]
      rw [h1, hset, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdvd : d ∣ Δ p
      · rw [if_pos hdvd, if_pos ⟨hdvd, hΔ⟩]
      · rw [if_neg hdvd, if_neg (fun h => hdvd h.1), mul_zero]
  calc ∑ p ∈ P, w p * (Nat.gcd m (Δ p) : ℝ)
      = ∑ p ∈ P, ∑ d ∈ m.divisors,
          if (d ∣ Δ p ∧ Δ p ≠ 0) then w p * (Nat.totient d : ℝ) else 0 :=
        Finset.sum_congr rfl hpt
    _ = ∑ d ∈ m.divisors, ∑ p ∈ P,
          if (d ∣ Δ p ∧ Δ p ≠ 0) then w p * (Nat.totient d : ℝ) else 0 :=
        Finset.sum_comm
    _ = ∑ d ∈ m.divisors, ∑ p ∈ P.filter (fun p => d ∣ Δ p ∧ Δ p ≠ 0),
          w p * (Nat.totient d : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_filter]
    _ = ∑ d ∈ m.divisors, (Nat.totient d : ℝ) *
          ∑ p ∈ P.filter (fun p => d ∣ Δ p ∧ Δ p ≠ 0), w p := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_mul]
        ring

theorem ZAc_fiber :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (h1 h2 r1 r2 : ℤ) (thr : ℝ) (Dm : ℕ),
      0 ≤ R → 1 ≤ Dm → r1 ∈ Finset.Icc (-R) R → r2 ∈ Finset.Icc (-R) R →
      r1 ≠ 0 → tA h1 h2 r1 r2 ≠ 0 →
      (∀ s1 ∈ Finset.Icc (-R) R, ∀ s2 ∈ Finset.Icc (-R) R,
          cdg h1 h2 r1 s1 r2 s2 ≤ Dm) →
      (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
          (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
        ≤ C * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8
            * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4) := by
  obtain ⟨C1, hC1pos, hC1⟩ := class_delta_sum_le
  refine ⟨C1, hC1pos, ?_⟩
  intro R h1 h2 r1 r2 thr Dm hR hDm hr1mem hr2mem hr1ne htAne hcdg
  set m : ℕ := (tA h1 h2 r1 r2).natAbs with hmdef
  set Dn : ℕ := 2 * R.natAbs ^ 2 + 1 with hDndef
  set TL : ℝ := C1 * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
      * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8 with hTLdef
  have hmne : m ≠ 0 := by rw [hmdef]; exact Int.natAbs_ne_zero.mpr htAne
  have hDn1 : 1 ≤ Dn := by rw [hDndef]; omega
  have hDnZ : (Dn : ℤ) = 2 * R * R + 1 := by
    rw [hDndef]; push_cast; rw [abs_of_nonneg hR]; ring
  have hDnR : (Dn : ℝ) = 2 * (R : ℝ) ^ 2 + 1 := by
    have h : (Dn : ℝ) = ((2 * R * R + 1 : ℤ) : ℝ) := by exact_mod_cast hDnZ
    rw [h]; push_cast; ring
  have hRnn : (0 : ℤ) ≤ R := hR
  have hr1Ic : -R ≤ r1 ∧ r1 ≤ R := Finset.mem_Icc.mp hr1mem
  have hr2Ic : -R ≤ r2 ∧ r2 ≤ R := Finset.mem_Icc.mp hr2mem
  have hr1abs : |r1| ≤ R := abs_le.mpr hr1Ic
  have hr2abs : |r2| ≤ R := abs_le.mpr hr2Ic
  -- a bound for `Δ` over the box
  have hDbound : ∀ p : ℤ × ℤ, p.1 ∈ Finset.Icc (-R) R → p.2 ∈ Finset.Icc (-R) R →
      (r1 * p.2 - r2 * p.1).natAbs ≤ Dn := by
    intro p hp1 hp2
    have hp1Ic : -R ≤ p.1 ∧ p.1 ≤ R := Finset.mem_Icc.mp hp1
    have hp2Ic : -R ≤ p.2 ∧ p.2 ≤ R := Finset.mem_Icc.mp hp2
    have hp1abs : |p.1| ≤ R := abs_le.mpr hp1Ic
    have hp2abs : |p.2| ≤ R := abs_le.mpr hp2Ic
    have h1 : |r1 * p.2| ≤ R * R := by
      rw [abs_mul]
      exact mul_le_mul hr1abs hp2abs (abs_nonneg _) hRnn
    have h2 : |r2 * p.1| ≤ R * R := by
      rw [abs_mul]
      exact mul_le_mul hr2abs hp1abs (abs_nonneg _) hRnn
    have h3 : |r1 * p.2 - r2 * p.1| ≤ 2 * (R * R) := by
      calc |r1 * p.2 - r2 * p.1| ≤ |r1 * p.2| + |r2 * p.1| := abs_sub _ _
        _ ≤ R * R + R * R := add_le_add h1 h2
        _ = 2 * (R * R) := by ring
    have h4 : ((r1 * p.2 - r2 * p.1).natAbs : ℤ) ≤ (Dn : ℤ) := by
      rw [Int.natCast_natAbs, hDnZ]
      linarith
    exact_mod_cast h4
  -- the termwise bound
  have hterm : ∀ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R),
      ZW h1 h2 r1 p.1 r2 p.2
        ≤ (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
            / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ)
          * (Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) : ℝ) := by
    intro p hp
    have hcdgle : cdg h1 h2 r1 p.1 r2 p.2 ≤ Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) := by
      have hcdgform : cdg h1 h2 r1 p.1 r2 p.2
          = Nat.gcd (Nat.gcd (tA h1 h2 r1 r2).natAbs (tB h1 h2 p.1 p.2).natAbs)
              ((r1 * p.2 - r2 * p.1).natAbs) := rfl
      rw [hcdgform, hmdef]
      exact gcd_gcd_le_gcd_left (Int.natAbs_ne_zero.mpr htAne)
    rw [ZW]
    simp only [dlt]
    have hcast : ((cdg h1 h2 r1 p.1 r2 p.2 : ℕ) : ℝ)
        ≤ ((Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) : ℕ) : ℝ) := by exact_mod_cast hcdgle
    exact mul_le_mul_of_nonneg_left hcast (by positivity)
  have hterm_nn : ∀ p : ℤ × ℤ, (0 : ℝ) ≤ ZW h1 h2 r1 p.1 r2 p.2 := by
    intro p
    rw [ZW]
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (by positivity)
  -- the logarithm comparison
  have hL : (Real.log ((Dn : ℕ) : ℝ) + 2) ^ 8
      ≤ (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8 := by
    have hpos : (0 : ℝ) < (Dn : ℝ) := by rw [hDnR]; positivity
    have hle : (Dn : ℝ) ≤ 2 * (R : ℝ) ^ 2 + 2 := by rw [hDnR]; linarith
    have hlog : Real.log ((Dn : ℝ)) ≤ Real.log (2 * (R : ℝ) ^ 2 + 2) := Real.log_le_log hpos hle
    have hbase : (0 : ℝ) ≤ Real.log ((Dn : ℝ)) + 2 := by
      have : (0 : ℝ) ≤ Real.log ((Dn : ℝ)) :=
        Real.log_nonneg (by rw [hDnR]; nlinarith [sq_nonneg (R : ℝ)])
      linarith
    exact pow_le_pow_left₀ hbase (by linarith) 8
  have hTLnn : (0 : ℝ) ≤ TL := by
    rw [hTLdef]
    apply mul_nonneg (mul_nonneg hC1pos.le _) (pow_nonneg _ 8)
    · have h1 : (0 : ℝ) ≤ 2 * (R : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        linarith
      positivity
    · have : (1 : ℝ) ≤ 2 * (R : ℝ) ^ 2 + 2 := by nlinarith [sq_nonneg (R : ℝ)]
      have := Real.log_nonneg this
      linarith
  -- step 1: drop the threshold indicator
  have hstep1 : (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
        (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
      ≤ ∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R), ZW h1 h2 r1 p.1 r2 p.2 := by
    have hprod : (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
        (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
        = ∑ p ∈ (Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R),
            (if thr < |(p.1 : ℝ)| ∧ thr < |(p.2 : ℝ)| then ZW h1 h2 r1 p.1 r2 p.2 else 0) :=
      (Finset.sum_product _ _ (fun p : ℤ × ℤ =>
        (if thr < |(p.1 : ℝ)| ∧ thr < |(p.2 : ℝ)| then ZW h1 h2 r1 p.1 r2 p.2 else 0))).symm
    rw [hprod, Finset.product_eq_sprod]
    apply Finset.sum_le_sum
    intro p hp
    by_cases h : thr < |(p.1 : ℝ)| ∧ thr < |(p.2 : ℝ)|
    · rw [if_pos h]
    · rw [if_neg h]
      exact hterm_nn p
  -- step 2: termwise bound
  have hstep2 : (∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R), ZW h1 h2 r1 p.1 r2 p.2)
      ≤ ∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R),
          (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
            / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ)
          * (Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) : ℝ) :=
    Finset.sum_le_sum hterm
  -- step 3: the gcd swap
  have hswap : (∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R),
          (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
            / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ)
          * (Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) : ℝ))
      = ∑ d ∈ m.divisors, (Nat.totient d : ℝ) *
          ∑ p ∈ ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
              (fun p => d ∣ (r1 * p.2 - r2 * p.1).natAbs
                ∧ (r1 * p.2 - r2 * p.1).natAbs ≠ 0),
            (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
              / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ) :=
    sum_mul_gcd_eq_totient _ _ _ m hmne (by
      intro p hp hΔ
      simp [hΔ])
  -- step 4: the per-divisor bound
  have hdbound : ∀ d ∈ m.divisors,
      (∑ p ∈ ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
          (fun p => d ∣ (r1 * p.2 - r2 * p.1).natAbs
            ∧ (r1 * p.2 - r2 * p.1).natAbs ≠ 0),
        (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
          / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ))
      ≤ TL * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) := by
    intro d hd
    obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
    have hdne : d ≠ 0 := by
      intro h
      rw [h] at hdm
      exact hmne (Nat.eq_zero_of_zero_dvd hdm)
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdne
    have hfe : ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
          (fun p => d ∣ (r1 * p.2 - r2 * p.1).natAbs
            ∧ (r1 * p.2 - r2 * p.1).natAbs ≠ 0)
        = ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
          (fun p => (d : ℤ) ∣ r1 * p.2 - r2 * p.1 ∧ r1 * p.2 - r2 * p.1 ≠ 0) := by
      refine Finset.filter_congr (fun p hp => ?_)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1), Int.natAbs_ne_zero.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h1), Int.natAbs_ne_zero.mpr h2⟩
    have hC1inst := hC1 r1 r2 hr1ne d hd1 Dn hDn1 (-R) R (-R) R hDbound
    have hTnat : (((R - (-R) + 1)).natAbs : ℝ) = 2 * (R : ℝ) + 1 := by
      have hnn : (0 : ℤ) ≤ R - (-R) + 1 := by omega
      rw [Nat.cast_natAbs, Int.cast_abs]
      rw [abs_of_nonneg (by exact_mod_cast hnn : (0 : ℝ) ≤ ((R - (-R) + 1 : ℤ) : ℝ))]
      push_cast
      ring
    have hrn : ((r1.natAbs : ℕ) : ℝ) = |(r1 : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hTeq : 1 + ((r1.gcd r2 : ℕ) : ℝ) * (((R - (-R) + 1)).natAbs : ℝ) / ((r1.natAbs : ℕ) : ℝ)
        = 1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)| := by
      rw [hTnat, hrn]
    rw [hfe]
    have hXnn : (0 : ℝ) ≤ (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) := by positivity
    have hTnn : (0 : ℝ) ≤ 1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)| := by
      have h1 : (0 : ℝ) ≤ 2 * (R : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        linarith
      positivity
    have hnn : (0 : ℝ)
        ≤ C1 * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) :=
      mul_nonneg (mul_nonneg hC1pos.le hTnn) hXnn
    refine hC1inst.trans ?_
    calc C1 * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (((R - (-R) + 1)).natAbs : ℝ) / ((r1.natAbs : ℕ) : ℝ))
            * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) * (Real.log ((Dn : ℕ) : ℝ) + 2) ^ 8
        ≤ C1 * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8 := by
          rw [hTeq]
          exact mul_le_mul_of_nonneg_left hL hnn
      _ = TL * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) := by
          rw [hTLdef]; ring
  calc (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
        (if thr < |(s1 : ℝ)| ∧ thr < |(s2 : ℝ)| then ZW h1 h2 r1 s1 r2 s2 else 0))
      ≤ ∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R), ZW h1 h2 r1 p.1 r2 p.2 := hstep1
    _ ≤ ∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-R) R),
          (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
            / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ)
          * (Nat.gcd m ((r1 * p.2 - r2 * p.1).natAbs) : ℝ) := hstep2
    _ = ∑ d ∈ m.divisors, (Nat.totient d : ℝ) *
          ∑ p ∈ ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
              (fun p => d ∣ (r1 * p.2 - r2 * p.1).natAbs
                ∧ (r1 * p.2 - r2 * p.1).natAbs ≠ 0),
            (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ)) ^ 3
              / (((r1 * p.2 - r2 * p.1).natAbs : ℕ) : ℝ) := hswap
    _ ≤ ∑ d ∈ m.divisors, (Nat.totient d : ℝ) * (TL * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) :=
        Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hdbound d hd) (by positivity))
    _ = TL * ∑ d ∈ m.divisors, (Nat.totient d : ℝ) * (((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
    _ ≤ TL * (((m.divisors.card : ℝ))) ^ 4 :=
        mul_le_mul_of_nonneg_left (sum_totient_mul_tau_cube_div_le m) hTLnn
    _ = C1 * (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
          * (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8
          * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4) := by
        rw [hTLdef, hmdef]

end

end Work.FIArea2.Count
