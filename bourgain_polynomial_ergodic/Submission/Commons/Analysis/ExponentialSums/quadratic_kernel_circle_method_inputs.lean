import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic
import Submission.Commons.Analysis.ExponentialSums.quadratic_minor_arc_decay

namespace Commons.Analysis.ExponentialSums

open Finset

set_option maxHeartbeats 1000000

/-- Two fractions `a/q`, `a'/q'` in lowest terms with `0 ≤ a < q`, `0 ≤ a' < q'` coincide
iff they are the same fraction. -/
lemma reduced_fraction_eq_iff {q q' a a' : ℕ} (hq : 0 < q) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hq' : 0 < q') (ha' : a' < q') (hg' : Nat.gcd a' q' = 1) :
    (a : ℝ) / (q : ℝ) = (a' : ℝ) / (q' : ℝ) ↔ a = a' ∧ q = q' := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  constructor
  · intro h
    have hcrossR : (a : ℝ) * (q' : ℝ) = (a' : ℝ) * (q : ℝ) := by
      field_simp [ne_of_gt hq0, ne_of_gt hq0'] at h
      ring_nf at h ⊢
      exact h
    have hcross : a * q' = a' * q := by exact_mod_cast hcrossR
    have hcopq : q.Coprime a := Nat.coprime_comm.mp (Nat.coprime_iff_gcd_eq_one.mpr hg)
    have hcopq' : q'.Coprime a' := Nat.coprime_comm.mp (Nat.coprime_iff_gcd_eq_one.mpr hg')
    have h1 : q ∣ q' := hcopq.dvd_of_dvd_mul_left (by rw [hcross]; exact dvd_mul_left q a')
    have h2 : q' ∣ q := hcopq'.dvd_of_dvd_mul_left (by rw [← hcross]; exact dvd_mul_left q' a)
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    exact ⟨by nlinarith, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The basic separation of two distinct reduced fractions. -/
lemma reduced_fraction_dist_ge {q q' a a' : ℕ} (hq : 0 < q) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hq' : 0 < q') (ha' : a' < q') (hg' : Nat.gcd a' q' = 1)
    (hne : ¬ (a = a' ∧ q = q')) :
    ((q : ℝ) * (q' : ℝ))⁻¹ ≤ |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hcross_ne : (a : ℤ) * (q' : ℤ) ≠ (a' : ℤ) * (q : ℤ) := by
    intro h
    have hnat : a * q' = a' * q := by exact_mod_cast h
    have hcopq : q.Coprime a := Nat.coprime_comm.mp (Nat.coprime_iff_gcd_eq_one.mpr hg)
    have hcopq' : q'.Coprime a' := Nat.coprime_comm.mp (Nat.coprime_iff_gcd_eq_one.mpr hg')
    have h1 : q ∣ q' := hcopq.dvd_of_dvd_mul_left (by rw [hnat]; exact dvd_mul_left q a')
    have h2 : q' ∣ q := hcopq'.dvd_of_dvd_mul_left (by rw [← hnat]; exact dvd_mul_left q' a)
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    exact hne ⟨by nlinarith, rfl⟩
  have hnum_int : (1 : ℤ) ≤ |(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)| := by
    have h0 : 0 < |(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)| :=
      abs_pos.mpr (sub_ne_zero.mpr hcross_ne)
    omega
  have hnum : (1 : ℝ) ≤ |(a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ)| := by
    have h1 : ((1 : ℤ) : ℝ) ≤ ((|(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast hnum_int
    have h2 : ((|(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)| : ℤ) : ℝ)
        = |(a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ)| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    rw [h2] at h1
    simpa using h1
  have hden : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := by positivity
  have heq : |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)|
      = |(a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    rw [div_sub_div _ _ (ne_of_gt hq0) (ne_of_gt hq0'), abs_div, abs_of_pos hden]
    ring_nf
  rw [heq, inv_eq_one_div]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)


/-- `N^{-δ} ≤ 2 N^{-(1+δ)}` is impossible for `N ≥ 3` and `δ > 0`. -/
lemma rpow_impossible {N : ℕ} (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (h : (N : ℝ) ^ (-δ) ≤ 2 * (N : ℝ) ^ (-(1 + δ))) : False := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpow : (0 : ℝ) < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hNpos δ
  have hm : (N : ℝ) ^ (-δ) * (N : ℝ) ^ δ ≤ (2 * (N : ℝ) ^ (-(1 + δ))) * (N : ℝ) ^ δ :=
    mul_le_mul_of_nonneg_right h (le_of_lt hpow)
  have e1 : (N : ℝ) ^ (-δ) * (N : ℝ) ^ δ = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have e2 : (2 * (N : ℝ) ^ (-(1 + δ))) * (N : ℝ) ^ δ = 2 * (N : ℝ) ^ (-1 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hNpos]
    norm_num
  rw [e1, e2] at hm
  have hinv : (N : ℝ) ^ (-1 : ℝ) = ((N : ℝ))⁻¹ := by
    have := Real.rpow_neg hNpos.le (1 : ℝ)
    simpa using this
  rw [hinv] at hm
  have h2 : (N : ℝ) ≤ 2 := by
    have h3 := mul_le_mul_of_nonneg_right hm (le_of_lt hNpos)
    rw [show (1 : ℝ) * (N : ℝ) = (N : ℝ) by ring,
      show (2 * ((N : ℝ))⁻¹) * (N : ℝ) = 2 by field_simp] at h3
    exact h3
  have h4 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

/-- **Uniqueness of the major-arc representation.**  For `N ≥ 3` and `δ ≤ 1/4`, a point
`α ∈ [0,1]` can lie in at most one major arc `|α - a/q - l| ≤ N^{-1-δ}` with `1 ≤ q ≤ N^δ`,
`0 ≤ a < q`, `gcd(a,q) = 1` and `l ∈ {-2,-1,0,1,2}`. -/
theorem major_arc_representation_unique
    {N : ℕ} (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}
    (hq : 1 ≤ q) (hqδ : q ≤ Nat.floor ((N : ℝ) ^ δ)) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hq' : 1 ≤ q') (hqδ' : q' ≤ Nat.floor ((N : ℝ) ^ δ)) (ha' : a' < q') (hg' : Nat.gcd a' q' = 1)
    (hl : l ∈ Finset.Icc (-2 : ℤ) 2) (hl' : l' ∈ Finset.Icc (-2 : ℤ) 2)
    (h₁ : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹)
    (h₂ : |α - (a' : ℝ) / (q' : ℝ) - (l' : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹) :
    q = q' ∧ a = a' ∧ l = l' := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNrpow : (0 : ℝ) < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hNr δ
  have hrad : ((N : ℝ) ^ (1 + δ))⁻¹ < 1 / 2 := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]
    have h1 : (2 : ℝ) < (N : ℝ) ^ (1 + δ) := by
      calc (2 : ℝ) < (N : ℝ) := by linarith
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    linarith
  have hqR : (q : ℝ) ≤ (N : ℝ) ^ δ := by
    have h1 : (q : ℝ) ≤ (Nat.floor ((N : ℝ) ^ δ) : ℝ) := by exact_mod_cast hqδ
    have h2 := Nat.floor_le (le_of_lt hNrpow)
    linarith
  have hqR' : (q' : ℝ) ≤ (N : ℝ) ^ δ := by
    have h1 : (q' : ℝ) ≤ (Nat.floor ((N : ℝ) ^ δ) : ℝ) := by exact_mod_cast hqδ'
    have h2 := Nat.floor_le (le_of_lt hNrpow)
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqpos' : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast (by omega : 0 < q')
  -- (A) the two shifted arguments are within 2r
  have hdiff2 : |((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))|
      ≤ 2 * ((N : ℝ) ^ (1 + δ))⁻¹ := by
    have h := abs_sub_le ((a : ℝ) / (q : ℝ) + (l : ℝ)) α ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))
    have e1 : |((a : ℝ) / (q : ℝ) + (l : ℝ)) - α|
        = |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| := by rw [← abs_sub_comm]; congr 1; ring
    have e2 : |α - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))|
        = |α - (a' : ℝ) / (q' : ℝ) - (l' : ℝ)| := by congr 1; ring
    rw [e1, e2] at h
    linarith
  -- (B) if l ≠ l' then the two shifted arguments are separated by at least N^{-δ}
  have hl_eq : l = l' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- l < l'
      have hD : ((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))
          ≤ -(((q : ℝ))⁻¹) := by
        have haq : (a : ℝ) / (q : ℝ) ≤ 1 - ((q : ℝ))⁻¹ := by
          have h2 : (a : ℝ) ≤ (q : ℝ) - 1 := by
            have : a + 1 ≤ q := by omega
            have : ((a : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast this
            linarith
          rw [div_le_iff₀ hqpos]
          calc (a : ℝ) ≤ (q : ℝ) - 1 := h2
            _ = (1 - ((q : ℝ))⁻¹) * (q : ℝ) := by field_simp
        have h3 : (1 : ℝ) ≤ (l' : ℝ) - (l : ℝ) := by
          have h4 : l + 1 ≤ l' := by omega
          have h5 : ((l : ℝ) + 1) ≤ (l' : ℝ) := by exact_mod_cast h4
          linarith
        have h6 : 0 ≤ (a' : ℝ) / (q' : ℝ) := by positivity
        linarith
      have hneg : ((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ)) < 0 := by
        have : (0 : ℝ) < ((q : ℝ))⁻¹ := inv_pos.mpr hqpos
        linarith
      have hlow : ((N : ℝ) ^ δ)⁻¹ ≤
          |((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))| := by
        rw [abs_of_neg hneg]
        have h7 : ((N : ℝ) ^ δ)⁻¹ ≤ ((q : ℝ))⁻¹ :=
          (inv_le_inv₀ hNrpow hqpos).2 hqR
        linarith
      have hfin := le_trans hlow hdiff2
      rw [(Real.rpow_neg hNr.le δ).symm, (Real.rpow_neg hNr.le (1 + δ)).symm] at hfin
      exact rpow_impossible hN hδ hfin
    · -- l' < l
      have hD : ((q' : ℝ))⁻¹ ≤ ((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ)) := by
        have h6 : 0 ≤ (a : ℝ) / (q : ℝ) := by positivity
        have haq' : (a' : ℝ) / (q' : ℝ) ≤ 1 - ((q' : ℝ))⁻¹ := by
          have h2 : (a' : ℝ) ≤ (q' : ℝ) - 1 := by
            have : a' + 1 ≤ q' := by omega
            have : ((a' : ℝ) + 1) ≤ (q' : ℝ) := by exact_mod_cast this
            linarith
          rw [div_le_iff₀ hqpos']
          calc (a' : ℝ) ≤ (q' : ℝ) - 1 := h2
            _ = (1 - ((q' : ℝ))⁻¹) * (q' : ℝ) := by field_simp
        have h3 : (1 : ℝ) ≤ (l : ℝ) - (l' : ℝ) := by
          have h4 : l' + 1 ≤ l := by omega
          have h5 : ((l' : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast h4
          linarith
        linarith
      have hpos : 0 < ((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ)) := by
        have : (0 : ℝ) < ((q' : ℝ))⁻¹ := inv_pos.mpr hqpos'
        linarith
      have hlow : ((N : ℝ) ^ δ)⁻¹ ≤
          |((a : ℝ) / (q : ℝ) + (l : ℝ)) - ((a' : ℝ) / (q' : ℝ) + (l' : ℝ))| := by
        rw [abs_of_nonneg (le_of_lt hpos)]
        have h7 : ((N : ℝ) ^ δ)⁻¹ ≤ ((q' : ℝ))⁻¹ :=
          (inv_le_inv₀ hNrpow hqpos').2 hqR'
        linarith
      have hfin := le_trans hlow hdiff2
      rw [(Real.rpow_neg hNr.le δ).symm, (Real.rpow_neg hNr.le (1 + δ)).symm] at hfin
      exact rpow_impossible hN hδ hfin
  subst hl_eq
  -- (C) now show (a,q) = (a',q')
  have hcross2 : |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| ≤ 2 * ((N : ℝ) ^ (1 + δ))⁻¹ := by
    have hzz : |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)|
        = |(α - (a' : ℝ) / (q' : ℝ) - (l : ℝ)) - (α - (a : ℝ) / (q : ℝ) - (l : ℝ))| := by
      rw [show (α - (a' : ℝ) / (q' : ℝ) - (l : ℝ)) - (α - (a : ℝ) / (q : ℝ) - (l : ℝ))
          = (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) by ring]
    rw [hzz]
    have h := abs_sub_le (α - (a' : ℝ) / (q' : ℝ) - (l : ℝ)) 0
      (α - (a : ℝ) / (q : ℝ) - (l : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  by_cases heq : a = a' ∧ q = q'
  · exact ⟨heq.2, heq.1, rfl⟩
  · exfalso
    have hlow := reduced_fraction_dist_ge (by omega : 0 < q) ha hg (by omega : 0 < q') ha' hg' heq
    have hqq : ((q : ℝ) * (q' : ℝ)) ≤ (N : ℝ) ^ δ * (N : ℝ) ^ δ :=
      mul_le_mul hqR hqR' (by positivity) (by positivity)
    have hden : (0 : ℝ) < (N : ℝ) ^ δ * (N : ℝ) ^ δ := by positivity
    have hqden : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := by positivity
    have hinv : ((N : ℝ) ^ δ * (N : ℝ) ^ δ)⁻¹ ≤ ((q : ℝ) * (q' : ℝ))⁻¹ :=
      (inv_le_inv₀ hden hqden).2 hqq
    have hpow : ((N : ℝ) ^ δ * (N : ℝ) ^ δ)⁻¹ = (N : ℝ) ^ (-(2 * δ)) := by
      rw [← Real.rpow_add (x := (N : ℝ)) hNr, Real.rpow_neg hNr.le]
      congr 1; ring
    -- combine: `N^{-2δ} ≤ 2 N^{-(1+δ)}`
    have hmono : (N : ℝ) ^ (-(2 * δ)) ≤ 2 * ((N : ℝ) ^ (1 + δ))⁻¹ := by
      rw [← hpow]
      linarith
    -- multiply by `N^{1+δ}`: get `N^{1-δ} ≤ 2`
    have hmain : (N : ℝ) ^ (-(2 * δ)) = (N : ℝ) ^ (-(1 + δ)) * (N : ℝ) ^ (1 - δ) := by
      rw [← Real.rpow_add (x := (N : ℝ)) hNr]
      congr 1; ring
    have hp : (0 : ℝ) < (N : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hNr _
    have hfin : (N : ℝ) ^ (1 - δ) ≤ 2 := by
      have h2 := mul_le_mul_of_nonneg_right (hmain ▸ hmono) (le_of_lt hp)
      have e1 : ((N : ℝ) ^ (-(1 + δ)) * (N : ℝ) ^ (1 - δ)) * (N : ℝ) ^ (1 + δ)
          = (N : ℝ) ^ (1 - δ) := by
        rw [show ((N : ℝ) ^ (-(1 + δ)) * (N : ℝ) ^ (1 - δ)) * (N : ℝ) ^ (1 + δ)
            = ((N : ℝ) ^ (-(1 + δ)) * (N : ℝ) ^ (1 + δ)) * (N : ℝ) ^ (1 - δ) by ring,
          ← Real.rpow_add (x := (N : ℝ)) hNr,
          show (-(1 + δ) + (1 + δ) : ℝ) = 0 by ring, Real.rpow_zero, one_mul]
      have e2 : (2 * ((N : ℝ) ^ (1 + δ))⁻¹) * (N : ℝ) ^ (1 + δ) = 2 := by
        rw [mul_assoc, ← Real.rpow_neg hNr.le (1 + δ), ← Real.rpow_add (x := (N : ℝ)) hNr,
          show (-(1 + δ) + (1 + δ) : ℝ) = 0 by ring, Real.rpow_zero, mul_one]
      rwa [e1, e2] at h2
    -- and `2 < N^{1-δ}` since `δ ≤ 1/4` and `N ≥ 3`
    have h2lt : (2 : ℝ) < (N : ℝ) ^ (1 - δ) := by
      have h27 : (2 : ℝ) < (27 : ℝ) ^ (1 / 4 : ℝ) := by
        have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
            ← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [← h16]
        exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      have h3 : (27 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hN3 3
        norm_num at h
        exact h
      have hstep : (27 : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
        have h1 : ((N : ℝ) ^ (3 : ℕ)) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_mul (le_of_lt hNr)]
          norm_num
        rw [← h1]
        exact Real.rpow_le_rpow (by positivity) h3 (by norm_num)
      have h4 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (1 - δ) :=
        Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
      linarith
    linarith


/-- If `α ∈ [0,1]` is not within `N^{-(1+σ)}` of any reduced fraction `a/q` (`1 ≤ q ≤ N^ℓ`)
shifted by an integer, then `α` is at distance more than `N^{-2+ℓ}` from *every* fraction with
denominator at most `N^ℓ`.  This is the elementary complement relation between Bourgain's major
arcs and his minor arcs. -/
theorem major_arc_complement_minor_arc :
    ∀ (ℓ σ : ℝ), 0 < ℓ → ℓ ≤ 1 / 4 → 0 < σ → ℓ + σ ≤ 1 →
      ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ℓ) → a < q →
            Nat.gcd a q = 1 →
            ((N : ℝ) ^ (1 + σ))⁻¹ < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
        ∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ℓ →
          (N : ℝ) ^ (-(2 : ℝ) + ℓ) < |α - (a : ℝ) / (q : ℝ)| := by
  intro ℓ σ hℓ hℓ4 hσ hℓσ N hN α hα0 hα1 hnoarc q a hq hqℓ
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  -- integer division a = q * m + r
  set r : ℤ := a % (q : ℤ) with hr
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg a (ne_of_gt hqpos)
  have hrltZ : r < (q : ℤ) := hr ▸ Int.emod_lt_of_pos a hqpos
  set m : ℤ := a / (q : ℤ) with hm
  have hdecZ : a = (q : ℤ) * m + r := by
    have h := Int.mul_ediv_add_emod a (q : ℤ)
    rw [← hm, ← hr] at h
    exact h.symm
  set rn : ℕ := r.toNat with hrn
  have hrcast : (rn : ℤ) = r := hrn ▸ Int.toNat_of_nonneg hr0
  have hrn_lt : rn < q := by
    have h : (rn : ℤ) < (q : ℤ) := by rw [hrcast]; exact hrltZ
    exact_mod_cast h
  set d : ℕ := Nat.gcd rn q with hd
  have hddvdq : d ∣ q := hd ▸ Nat.gcd_dvd_right rn q
  have hddvdr : d ∣ rn := hd ▸ Nat.gcd_dvd_left rn q
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvdq (by omega)
  set q₁ : ℕ := q / d with hq1
  set r₁ : ℕ := rn / d with hr1
  have hq1d : q₁ * d = q := hq1 ▸ Nat.div_mul_cancel hddvdq
  have hr1d : r₁ * d = rn := hr1 ▸ Nat.div_mul_cancel hddvdr
  have hcop : Nat.gcd r₁ q₁ = 1 := by
    have hpos : 0 < rn.gcd q := by rw [← hd]; exact hdpos
    have h := Nat.coprime_div_gcd_div_gcd (m := rn) (n := q) hpos
    rw [hq1, hr1]
    exact Nat.coprime_iff_gcd_eq_one.mp h
  have hr1lt : r₁ < q₁ := by
    have h3 : rn / d < q / d := Nat.div_lt_div_of_lt_of_dvd hddvdq hrn_lt
    rw [hq1, hr1]; exact h3
  have hq1le : q₁ ≤ q := hq1 ▸ Nat.div_le_self q d
  have hq1pos : 0 < q₁ := by
    rcases Nat.eq_zero_or_pos q₁ with h0 | hp
    · rw [h0, zero_mul] at hq1d; omega
    · exact hp
  have hq1Rpos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq1pos
  have hrq : (rn : ℝ) / (q : ℝ) = (r₁ : ℝ) / (q₁ : ℝ) := by
    have h1 : (rn : ℝ) = (r₁ : ℝ) * (d : ℝ) := by
      have : r₁ * d = rn := hr1d
      rw [← this]; push_cast; ring
    have h2 : (q : ℝ) = (q₁ : ℝ) * (d : ℝ) := by
      have : q₁ * d = q := hq1d
      rw [← this]; push_cast; ring
    rw [h1, h2]
    field_simp
  have haq : (a : ℝ) / (q : ℝ) = (m : ℝ) + (r₁ : ℝ) / (q₁ : ℝ) := by
    have h1 : (a : ℝ) = (q : ℝ) * (m : ℝ) + (rn : ℝ) := by
      have hZ : a = (q : ℤ) * m + (rn : ℤ) := by rw [hrcast]; exact hdecZ
      exact_mod_cast hZ
    rw [h1, add_div, mul_div_cancel_left₀ _ (ne_of_gt hqposR), hrq]
  rw [haq]
  set v : ℝ := (r₁ : ℝ) / (q₁ : ℝ) with hv
  have hv0 : 0 ≤ v := hv ▸ by positivity
  have hv1 : v < 1 := by
    rw [hv, div_lt_one hq1Rpos]
    exact_mod_cast hr1lt
  have hq1floor : q₁ ≤ Nat.floor ((N : ℝ) ^ ℓ) := by
    rw [Nat.le_floor_iff (Real.rpow_nonneg (le_of_lt hNr) ℓ)]
    have h1 : (q₁ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1le
    linarith
  -- the two candidate comparisons
  by_cases hmle : |((m : ℝ))| ≤ 2
  · have hkey := hnoarc q₁ r₁ m (by omega) hq1floor hr1lt hcop
    rw [← hv] at hkey
    have hgoal1 : ((N : ℝ) ^ (1 + σ))⁻¹ = (N : ℝ) ^ (-(1 + σ)) := by
      rw [← Real.rpow_neg (le_of_lt hNr) (1 + σ)]
    have hmono2 : (N : ℝ) ^ (-(2 : ℝ) + ℓ) ≤ (N : ℝ) ^ (-(1 + σ)) :=
      Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    calc (N : ℝ) ^ (-(2 : ℝ) + ℓ) ≤ (N : ℝ) ^ (-(1 + σ)) := hmono2
      _ = ((N : ℝ) ^ (1 + σ))⁻¹ := hgoal1.symm
      _ < |α - ((m : ℝ) + v)| := by
          rw [show |α - ((m : ℝ) + v)| = |α - v - (m : ℝ)| by congr 1; ring]
          exact hkey
  · have hmgt : (2 : ℝ) < |((m : ℝ))| := lt_of_not_ge hmle
    have hm3 : (3 : ℝ) ≤ |((m : ℝ))| := by
      have hZ : (2 : ℤ) < |m| := by exact_mod_cast hmgt
      have hZ3 : (3 : ℤ) ≤ |m| := by omega
      exact_mod_cast hZ3
    have hsmall : (N : ℝ) ^ (-(2 : ℝ) + ℓ) < 1 := by
      have hexp : (0 : ℝ) < 2 - ℓ := by linarith
      have h1 : (N : ℝ) ^ (-(2 : ℝ) + ℓ) = ((N : ℝ) ^ (2 - ℓ))⁻¹ := by
        rw [show -(2:ℝ) + ℓ = -(2 - ℓ) by ring]
        exact Real.rpow_neg (le_of_lt hNr) _
      rw [h1, inv_lt_one_iff₀]
      right
      have h3 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      calc (1 : ℝ) = (1 : ℝ) ^ (2 - ℓ) := (Real.one_rpow _).symm
        _ < (N : ℝ) ^ (2 - ℓ) := Real.rpow_lt_rpow (by norm_num) h3 hexp
    have hbig : (1 : ℝ) < |α - ((m : ℝ) + v)| := by
      have h2 : |α - v| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h3 : |(m : ℝ)| ≤ |α - v - (m : ℝ)| + |α - v| := by
        have h := abs_sub_le ((m : ℝ)) (α - v) 0
        simp only [sub_zero] at h
        have heq : (m : ℝ) - (α - v) = -((α - v - (m : ℝ))) := by ring
        rw [heq, abs_neg] at h
        exact h
      rw [show |α - ((m : ℝ) + v)| = |α - v - (m : ℝ)| by congr 1; ring]
      linarith
    linarith


lemma exp_phase_shift_int (x : ℝ) (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (((x - (m : ℝ)) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) : ℂ)) := by
  rw [show (2 * Real.pi * Complex.I * (((x - (m : ℝ)) : ℝ) : ℂ))
      = 2 * Real.pi * Complex.I * ((x : ℝ) : ℂ) + (-m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I)
      by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem quadratic_kernel_major_arc_bound :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (a : ℤ) (q : ℕ) (l : ℤ) (α : ℝ), 1 ≤ q →
        (q : ℝ) ≤ (N : ℝ) ^ δ → Int.gcd a (q : ℤ) = 1 →
        |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹ →
        ‖((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
            (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ)))
          - ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
              Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)) : ℂ))))
            * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
                ((((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ 2 * s ^ 2 : ℝ)) : ℂ)))‖
        ≤ C * ((N : ℝ) ^ c)⁻¹ := by
  obtain ⟨δa, hδa0, θ, hθ0, Ca, hCa0, hasym⟩ :=
    Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic
  refine ⟨δa, θ, Ca, hδa0, hθ0, hCa0, ?_⟩
  intro N hN a q l α hq hqδ hgcd hb
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hkey := hasym N a q (α - (a : ℝ) / (q : ℝ) - (l : ℝ)) (by omega) (by omega) hqδ hgcd hb
  have hphase : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
            ((((a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ))) * (n : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro n
    rw [show (a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ)) = α - (l : ℝ) by ring]
    have harg : (α * (n : ℝ) ^ 2 : ℝ)
        = ((α - (l : ℝ)) * (n : ℝ) ^ 2) - (-(l * ((n : ℤ)) ^ 2) : ℤ) := by push_cast; ring
    rw [harg]
    exact exp_phase_shift_int ((α - (l : ℝ)) * (n : ℝ) ^ 2) (-(l * ((n : ℤ)) ^ 2))
  have hsum : Finset.sum (Finset.range N) (fun n =>
        Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ)))
      = Finset.sum (Finset.range N) (fun n => Complex.exp (2 * Real.pi * Complex.I *
          ((((a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ))) * (n : ℝ) ^ 2 : ℝ) : ℂ))) :=
    Finset.sum_congr rfl (fun n _ => hphase n)
  rw [hsum]
  have hcast : (((N : ℝ)) : ℂ)⁻¹ = ((((N : ℝ)⁻¹ : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_inv]
  rw [hcast]
  exact hkey


/-- **The minor-arc bound for the square kernel.**  Off the major arcs at level `σ`
(no reduced fraction `a/q` with `q ≤ N^ℓ` is within `N^{-(1+σ)}` of `α` up to an integer) the
square kernel decays like a power of `N`.  This is Bourgain's minor-arc estimate in the
"complement of the major arcs" form produced by `major_arc_complement_minor_arc` together with
`quadratic_minor_arc_decay`. -/
theorem quadratic_kernel_minor_arc_bound :
    ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 / 4 →
      ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧
        ∀ (σ : ℝ), 0 < σ → ℓ + σ ≤ 1 →
          ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
            (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ℓ) → a < q →
                Nat.gcd a q = 1 →
                ((N : ℝ) ^ (1 + σ))⁻¹ < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
            ‖((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
                (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ)))‖
            ≤ C * ((N : ℝ) ^ ν)⁻¹ := by
  intro ℓ hℓ0 hℓ4
  obtain ⟨Cm, ν, hCm0, hν0, hdecay⟩ :=
    Commons.Analysis.ExponentialSums.quadratic_minor_arc_decay ℓ hℓ0 hℓ4
  refine ⟨ν, Cm, hν0, hCm0, ?_⟩
  intro σ hσ0 hℓσ N hN α hα0 hα1 hnoarc
  have hminor : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ℓ →
      (N : ℝ) ^ (-(2 : ℝ) + ℓ) < |α - (a : ℝ) / (q : ℝ)| :=
    major_arc_complement_minor_arc ℓ σ hℓ0 hℓ4 hσ0 hℓσ N hN α hα0 hα1 hnoarc
  have hkey := hdecay N α (by omega) hminor
  rw [Real.rpow_neg (le_of_lt (by exact_mod_cast (by omega : 0 < N) : (0:ℝ) < (N:ℝ))) ν] at hkey
  exact hkey


theorem quadratic_kernel_circle_method_inputs :
    (∀ (ℓ σ : ℝ), 0 < ℓ → ℓ ≤ 1 / 4 → 0 < σ → ℓ + σ ≤ 1 →
      ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ℓ) → a < q →
            Nat.gcd a q = 1 →
            ((N : ℝ) ^ (1 + σ))⁻¹ < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
        ∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ℓ →
          (N : ℝ) ^ (-(2 : ℝ) + ℓ) < |α - (a : ℝ) / (q : ℝ)|)
    ∧ (∀ {N : ℕ} {δ : ℝ} {α : ℝ} {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}, 3 ≤ N → 0 < δ → δ ≤ 1 / 4 →
        0 ≤ α → α ≤ 1 → 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ δ) → a < q → Nat.gcd a q = 1 →
        1 ≤ q' → q' ≤ Nat.floor ((N : ℝ) ^ δ) → a' < q' → Nat.gcd a' q' = 1 →
        l ∈ Finset.Icc (-2 : ℤ) 2 → l' ∈ Finset.Icc (-2 : ℤ) 2 →
        |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹ →
        |α - (a' : ℝ) / (q' : ℝ) - (l' : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹ →
        q = q' ∧ a = a' ∧ l = l')
    ∧ (∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
        ∀ (N : ℕ), 3 ≤ N → ∀ (a : ℤ) (q : ℕ) (l : ℤ) (α : ℝ), 1 ≤ q →
          (q : ℝ) ≤ (N : ℝ) ^ δ → Int.gcd a (q : ℤ) = 1 →
          |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹ →
          ‖((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
              (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ)))
            - ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
                Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)) : ℂ))))
              * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
                  ((((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ 2 * s ^ 2 : ℝ)) : ℂ)))‖
          ≤ C * ((N : ℝ) ^ c)⁻¹)
    ∧ (∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 / 4 →
        ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧
          ∀ (σ : ℝ), 0 < σ → ℓ + σ ≤ 1 →
            ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
              (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ℓ) → a < q →
                  Nat.gcd a q = 1 →
                  ((N : ℝ) ^ (1 + σ))⁻¹ < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
              ‖((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
                  (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ)))‖
              ≤ C * ((N : ℝ) ^ ν)⁻¹)
:= by
  refine ⟨major_arc_complement_minor_arc, ?_, quadratic_kernel_major_arc_bound,
    quadratic_kernel_minor_arc_bound⟩
  intro N δ α q q' a a' l l' hN hδ hδ4 hα0 hα1 hq hqδ ha hg hq' hqδ' ha' hg' hl hl' h1 h2
  exact major_arc_representation_unique hN hδ hδ4 hα0 hα1 hq hqδ ha hg hq' hqδ' ha' hg' hl hl' h1 h2

end Commons.Analysis.ExponentialSums
