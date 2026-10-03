import Mathlib
import Submission.Work.FIArea7.sum_divisors_eq_sum_prod_le

namespace Work.FIArea7.smallCInnerAux

/-!
# The weighted divisor sum `Σ_{d ≤ D} τ(d) d^{-11/12}`

We prove `Σ_{d ≤ D} τ(d) d^{-11/12} ≤ 24 D^{1/12} log(D+2)`.

The strategy is the classical one: write `τ(d) = Σ_{e ∣ d} 1`, reindex the double sum over
pairs `(e, f)` with `e f ≤ D`, use the integral comparison `Σ_{f ≤ F} f^{-11/12} ≤ 12 F^{1/12}`
and `Σ_{e ≤ D} e^{-1} = harmonic D ≤ 1 + log D ≤ 2 log(D+2)`.
-/

/-- Pointwise integral comparison: for `m ≥ 2`,
`m ^ (-(11/12)) ≤ 12 * (m ^ (1/12) - (m - 1) ^ (1/12))`.

This is the mean-value/integral-comparison step: since `x ↦ x ^ (-(11/12))` is antitone on
`[m-1, m] ⊂ (0, ∞)`, `m ^ (-(11/12))` is at most the integral of the function over `[m-1, m]`,
which is `12 (m ^ (1/12) - (m-1) ^ (1/12))`. -/
lemma rpow_neg_shift_le (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℕ) : ℝ) ^ (-(11 : ℝ) / 12)
      ≤ 12 * ((m : ℝ) ^ ((1 : ℝ) / 12) - ((m - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
  have hle : m - 1 ≤ m := by omega
  have h1m : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    have h : 1 ≤ m - 1 := by omega
    exact_mod_cast h
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(11 : ℝ) / 12))
      (Set.Icc ((m - 1 : ℕ) : ℝ) (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hsum := hanti.sum_le_integral_Ico hle
  have hIco : Finset.Ico (m - 1) m = {m - 1} := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hIco, Finset.sum_singleton] at hsum
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at hsum
  have hsum2 : ((m : ℕ) : ℝ) ^ (-(11 : ℝ) / 12)
      ≤ ∫ x in ((m - 1 : ℕ) : ℝ)..((m : ℕ) : ℝ), x ^ (-(11 : ℝ) / 12) := by
    simpa using hsum
  have hint : (∫ x in ((m - 1 : ℕ) : ℝ)..((m : ℕ) : ℝ), x ^ (-(11 : ℝ) / 12))
      = 12 * ((m : ℝ) ^ ((1 : ℝ) / 12) - ((m - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(11 : ℝ) / 12))]
    have hexp : (-(11 : ℝ) / 12) + 1 = (1 : ℝ) / 12 := by norm_num
    rw [hexp, div_eq_mul_inv]
    have h12 : (((1 : ℝ) / 12))⁻¹ = 12 := by norm_num
    rw [h12]
    ring
  linarith [hsum2, hint]

/-- The integral-comparison bound `Σ_{m = 1}^{F} m ^ (-(11/12)) ≤ 12 F ^ (1/12)`. -/
lemma sum_rpow_neg_Icc_le (F : ℕ) :
    (∑ m ∈ Finset.Icc 1 F, ((m : ℕ) : ℝ) ^ (-(11 : ℝ) / 12))
      ≤ 12 * (F : ℝ) ^ ((1 : ℝ) / 12) := by
  induction F with
  | zero =>
    have he : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_iff.mpr (by norm_num)
    have h0 : (0 : ℝ) ^ ((1 : ℝ) / 12) = 0 := Real.zero_rpow (by norm_num)
    rw [he, Finset.sum_empty, Nat.cast_zero, h0]
    simp
  | succ F ih =>
    rcases Nat.eq_zero_or_pos F with hF | hF
    · subst hF
      rw [Finset.Icc_self, Finset.sum_singleton]
      simp only [Nat.cast_one, Real.one_rpow]
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ F + 1)]
      have hpt := rpow_neg_shift_le (F + 1) (by omega)
      rw [Nat.add_sub_cancel] at hpt
      have h := add_le_add ih hpt
      calc (∑ k ∈ Finset.Icc 1 F, ((k : ℕ) : ℝ) ^ (-(11 : ℝ) / 12))
            + (((F + 1 : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12)
          ≤ 12 * (F : ℝ) ^ ((1 : ℝ) / 12)
              + 12 * ((((F + 1 : ℕ)) : ℝ) ^ ((1 : ℝ) / 12) - (F : ℝ) ^ ((1 : ℝ) / 12)) := h
        _ = 12 * ((((F + 1 : ℕ)) : ℝ)) ^ ((1 : ℝ) / 12) := by ring

/-- `12 D^{1/12} · harmonic D ≤ 24 D^{1/12} · log (D+2)`. -/
lemma harmonic_rpow_log_le (D : ℕ) :
    12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (harmonic D : ℝ)
      ≤ 24 * (D : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((D : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have h0 : (0 : ℝ) ^ ((1 : ℝ) / 12) = 0 := Real.zero_rpow (by norm_num)
    have hh0 : (harmonic 0 : ℝ) = 0 := by simp [harmonic]
    rw [Nat.cast_zero, h0, hh0]
    simp
  · have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hkey : 1 + Real.log (D : ℝ) ≤ 2 * Real.log ((D : ℝ) + 2) := by
      rcases Nat.lt_or_ge D 2 with h2 | h2
      · interval_cases D
        have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
        simp only [Nat.cast_one, Real.log_one, add_zero]
        rw [show (1 : ℝ) + 2 = 3 by norm_num]
        linarith
      · have hD2 : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast h2
        have hlogD : Real.log (D : ℝ) ≤ Real.log ((D : ℝ) + 2) :=
          Real.log_le_log (by linarith) (by linarith)
        have h1le : (1 : ℝ) ≤ Real.log ((D : ℝ) + 2) := by
          have hlog4 : Real.log 4 ≤ Real.log ((D : ℝ) + 2) :=
            Real.log_le_log (by norm_num) (by linarith)
          have h4 : (1 : ℝ) ≤ Real.log 4 := by
            have h42 : (4 : ℝ) = 2 * 2 := by norm_num
            rw [h42, Real.log_mul (by norm_num) (by norm_num)]
            linarith
          linarith
        linarith
    have hH := harmonic_le_one_add_log D
    have hmain : (harmonic D : ℝ) ≤ 2 * Real.log ((D : ℝ) + 2) := le_trans hH hkey
    calc 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (harmonic D : ℝ)
        ≤ 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (2 * Real.log ((D : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 24 * (D : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((D : ℝ) + 2) := by ring

/-- The weighted two-variable divisor bound
`Σ_{b ≤ D} Σ_{m ≤ D, bm ≤ D} (bm)^{-11/12} ≤ 12 D^{1/12} · harmonic D`. -/
lemma sum_prod_rpow_le (D : ℕ) :
    (∑ b ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 D,
        (if b * m ≤ D then (((b * m : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12) else 0))
      ≤ 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (harmonic D : ℝ) := by
  have hH : (harmonic D : ℝ) = ∑ b ∈ Finset.Icc 1 D, ((b : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Rat.cast_inv, Rat.cast_natCast])
  have hinner : ∀ b ∈ Finset.Icc 1 D,
      (∑ m ∈ Finset.Icc 1 D,
          (if b * m ≤ D then (((b * m : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12) else 0))
        ≤ 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ)⁻¹ := by
    intro b hb
    obtain ⟨hb1, hbD⟩ := Finset.mem_Icc.mp hb
    have hbpos : 0 < b := by omega
    have hbposR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
    have hbnonneg : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hset : (Finset.Icc 1 D).filter (fun m => b * m ≤ D) = Finset.Icc 1 (D / b) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hm1, _⟩, hbm⟩
        refine ⟨hm1, (Nat.le_div_iff_mul_le hbpos).mpr ?_⟩
        rw [Nat.mul_comm]
        exact hbm
      · rintro ⟨hm1, hm2⟩
        have h1 : m * b ≤ D := (Nat.le_div_iff_mul_le hbpos).mp hm2
        exact ⟨⟨hm1, le_trans hm2 (Nat.div_le_self D b)⟩, by rwa [Nat.mul_comm]⟩
    rw [← Finset.sum_filter (fun m => b * m ≤ D)
          (fun m => (((b * m : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12)), hset]
    have h2 : ∀ m ∈ Finset.Icc 1 (D / b), (((b * m : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12)
        = (b : ℝ) ^ (-(11 : ℝ) / 12) * (m : ℝ) ^ (-(11 : ℝ) / 12) := by
      intro m _
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg b) (Nat.cast_nonneg m)]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    have hstep1 : (b : ℝ) ^ (-(11 : ℝ) / 12)
          * (∑ m ∈ Finset.Icc 1 (D / b), (m : ℝ) ^ (-(11 : ℝ) / 12))
        ≤ (b : ℝ) ^ (-(11 : ℝ) / 12) * (12 * (((D / b : ℕ)) : ℝ) ^ ((1 : ℝ) / 12)) :=
      mul_le_mul_of_nonneg_left (sum_rpow_neg_Icc_le (D / b)) (Real.rpow_nonneg hbnonneg _)
    have hstep2 : (((D / b : ℕ)) : ℝ) ^ ((1 : ℝ) / 12)
        ≤ (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12)) := by
      calc (((D / b : ℕ)) : ℝ) ^ ((1 : ℝ) / 12)
          ≤ (((D : ℝ) / (b : ℝ))) ^ ((1 : ℝ) / 12) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (by norm_num)
        _ = (D : ℝ) ^ ((1 : ℝ) / 12) / (b : ℝ) ^ ((1 : ℝ) / 12) :=
            Real.div_rpow (Nat.cast_nonneg D) hbnonneg _
        _ = (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hbnonneg]
    have hstep3 : (b : ℝ) ^ (-(11 : ℝ) / 12) * (12 * (((D / b : ℕ)) : ℝ) ^ ((1 : ℝ) / 12))
        ≤ (b : ℝ) ^ (-(11 : ℝ) / 12)
            * (12 * ((D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep2 (by norm_num))
        (Real.rpow_nonneg hbnonneg _)
    have hfinal : (b : ℝ) ^ (-(11 : ℝ) / 12)
          * (12 * ((D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12))))
        = 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ)⁻¹ := by
      have hcc : (b : ℝ) ^ (-(11 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12)) = (b : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one (b : ℝ), ← Real.rpow_add hbposR]
        congr 1
        norm_num
      rw [show (b : ℝ) ^ (-(11 : ℝ) / 12)
            * (12 * ((D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12))))
          = 12 * (D : ℝ) ^ ((1 : ℝ) / 12)
              * ((b : ℝ) ^ (-(11 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12))) by ring,
        hcc]
    calc (b : ℝ) ^ (-(11 : ℝ) / 12)
          * (∑ m ∈ Finset.Icc 1 (D / b), (m : ℝ) ^ (-(11 : ℝ) / 12))
        ≤ (b : ℝ) ^ (-(11 : ℝ) / 12) * (12 * (((D / b : ℕ)) : ℝ) ^ ((1 : ℝ) / 12)) := hstep1
      _ ≤ (b : ℝ) ^ (-(11 : ℝ) / 12)
            * (12 * ((D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ) ^ (-((1 : ℝ) / 12)))) := hstep3
      _ = 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ)⁻¹ := hfinal
  calc (∑ b ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 D,
          (if b * m ≤ D then (((b * m : ℕ)) : ℝ) ^ (-(11 : ℝ) / 12) else 0))
      ≤ ∑ b ∈ Finset.Icc 1 D, 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (b : ℝ)⁻¹ :=
        Finset.sum_le_sum hinner
    _ = 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * ∑ b ∈ Finset.Icc 1 D, (b : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
    _ = 12 * (D : ℝ) ^ ((1 : ℝ) / 12) * (harmonic D : ℝ) := by rw [← hH]

/-- **The weighted divisor sum** `Σ_{d ≤ D} τ(d)·d^{-11/12} ≤ 24·D^{1/12}·log(D+2)`.

Proof: `τ(d) = #{e : e ∣ d}`, so the sum is `Σ_{e ≤ D} Σ_{f ≤ D/e} (ef)^{-11/12}`, and
`Σ_{f ≤ F} f^{-11/12} ≤ 12 F^{1/12}` (compare with `∫_1^{F+1} x^{-11/12} dx`), giving
`12 D^{1/12} Σ_{e ≤ D} e^{-1} ≤ 12 D^{1/12}(1 + log D)` using `Nat.harmonic_le_one_add_log`. -/
theorem sumTauRpow (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11:ℝ)/12))
      ≤ 24 * (D : ℝ) ^ ((1:ℝ)/12) * Real.log ((D : ℝ) + 2) := by
  have hreindex :
      (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11:ℝ)/12))
        = ∑ b ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 D,
            (if b * m ≤ D then (((b * m : ℕ)) : ℝ) ^ (-(11:ℝ)/12) else 0) := by
    rw [← Work.FIArea7.sum_divisors_eq_sum_prod_le D
          (fun b m => (((b * m : ℕ)) : ℝ) ^ (-(11:ℝ)/12))]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hsum : (∑ b ∈ d.divisors, (((b * (d / b) : ℕ)) : ℝ) ^ (-(11:ℝ)/12))
        = ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11:ℝ)/12) := by
      rw [Finset.sum_congr rfl (fun b hb => by
        rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1])]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
  calc (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11:ℝ)/12))
      = ∑ b ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 D,
          (if b * m ≤ D then (((b * m : ℕ)) : ℝ) ^ (-(11:ℝ)/12) else 0) := hreindex
    _ ≤ 12 * (D : ℝ) ^ ((1:ℝ)/12) * (harmonic D : ℝ) := sum_prod_rpow_le D
    _ ≤ 24 * (D : ℝ) ^ ((1:ℝ)/12) * Real.log ((D : ℝ) + 2) := harmonic_rpow_log_le D

end Work.FIArea7.smallCInnerAux
