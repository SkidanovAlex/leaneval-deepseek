import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTPlan.A6

/-- **Uniform bound on the second factor of the crude composite constant.**  With
`uScale ρ L = ⌊2^{2ρL}⌋` and `l ≤ L`, writing `s = 2^{ρL} ≥ 1`:

`2^{-uScale ρ L} · ⌈2^{Qc·2^{ρl}}⌉² ≤ 8·2^{2Qc·s − s²} ≤ 8·2^{Qc²}`

(since `2Qc·s − s² = Qc² − (s − Qc)² ≤ Qc²`).  This is what makes the factor
`2(1 + 2·2^{-u}Q²)` of `mdlVanishingCase` uniform in `(l₁,l₂,k₁,k₂)` (take `l := l₁`,
`L := max (max l₁ l₂) (max k₁ k₂)`). -/
theorem two_pow_neg_scale_mul_Q_bound (ρ : ℝ) (hρ : 0 < ρ) (Qc : ℝ) (hQc : 0 < Qc) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l L : ℕ), l ≤ L →
      (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ L : ℤ)) *
        ((Nat.ceil ((2 : ℝ) ^ (Qc * 2 ^ (ρ * (l : ℝ))))) : ℝ) ^ 2 ≤ C := by
  -- `s = 2^{ρL} ≥ 1`; the first factor is `2^{-⌊s²⌋} ≤ 2^{1-s²}` and the second is
  -- `≤ 4·2^{2Qc·s}` (`2^{ρl} ≤ s`, and the ceiling costs a factor `2`).
  refine ⟨8 * (2:ℝ) ^ (Qc^2), by positivity, ?_⟩
  intro l L hl
  set s : ℝ := (2:ℝ) ^ (ρ * (L:ℝ)) with hs
  have hs1 : 1 ≤ s := by
    rw [hs]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hspow : s ^ 2 = (2:ℝ) ^ (2*ρ*(L:ℝ)) := by
    rw [hs, sq, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  -- `uScale ρ L = ⌊s²⌋ ≥ s² - 1`, so the first factor is at most `2^{1-s²}`.
  have hfloor : s ^ 2 - 1 ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
    have hux : (Work.KMTAreas.A7.uScale ρ L : ℝ) = ⌊(2:ℝ) ^ (2*ρ*(L:ℝ))⌋₊ := by
      simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
        Nat.cast_one, one_mul]
    rw [hux, ← hspow]
    have h := Nat.lt_floor_add_one (s ^ 2)
    linarith
  have hz : (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ L : ℤ))
      = (2:ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ L : ℝ))) := by
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  have hf1 : (2:ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ L : ℝ))) ≤ (2:ℝ) ^ (1 - s ^ 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    linarith
  -- The ceiling factor: `⌈2^{Qc·2^{ρl}}⌉ ≤ 2·2^{Qc·2^{ρl}}` and `2^{ρl} ≤ s`.
  have hQy : (2:ℝ) ^ (Qc * 2 ^ (ρ * (l:ℝ))) ≤ (2:ℝ) ^ (Qc*s) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    have h2 : (2:ℝ) ^ (ρ*(l:ℝ)) ≤ s := by
      rw [hs]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      have : (l:ℝ) ≤ (L:ℝ) := by exact_mod_cast hl
      nlinarith [hρ]
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt hQc)
  have hQbound : ((Nat.ceil ((2 : ℝ) ^ (Qc * 2 ^ (ρ * (l : ℝ))))) : ℝ) ^ 2
      ≤ 4 * (2:ℝ) ^ (2*Qc*s) := by
    have hceil : ((Nat.ceil ((2:ℝ) ^ (Qc * 2 ^ (ρ * (l:ℝ))))) : ℝ)
        ≤ 2 * (2:ℝ) ^ (Qc * 2 ^ (ρ*(l:ℝ))) := by
      have h := Nat.ceil_lt_add_one
        (show (0:ℝ) ≤ (2:ℝ) ^ (Qc * 2 ^ (ρ * (l:ℝ))) by positivity)
      have hone : (1:ℝ) ≤ (2:ℝ) ^ (Qc * 2 ^ (ρ * (l:ℝ))) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      linarith
    have hstep : ((Nat.ceil ((2:ℝ) ^ (Qc*2^(ρ*(l:ℝ))))) : ℝ) ^ 2
        ≤ (2 * (2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hceil
    have hmul : (2 * (2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2
        = 4 * ((2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2 := by rw [mul_pow]; norm_num
    have hsq2 : ((2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2 ≤ ((2:ℝ) ^ (Qc*s)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hQy 2
    have hsqeq : ((2:ℝ) ^ (Qc*s)) ^ 2 = (2:ℝ) ^ (2*Qc*s) := by
      rw [sq, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    calc ((Nat.ceil ((2:ℝ) ^ (Qc*2^(ρ*(l:ℝ))))) : ℝ) ^ 2
        ≤ (2 * (2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2 := hstep
      _ = 4 * ((2:ℝ) ^ (Qc * 2^(ρ*(l:ℝ)))) ^ 2 := hmul
      _ ≤ 4 * ((2:ℝ) ^ (Qc*s)) ^ 2 := by linarith
      _ = 4 * (2:ℝ) ^ (2*Qc*s) := by rw [hsqeq]
  have hexp : (1 - s ^ 2) + 2*Qc*s ≤ 1 + Qc ^ 2 := by
    nlinarith [sq_nonneg (s - Qc)]
  calc (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ L : ℤ)) *
        ((Nat.ceil ((2 : ℝ) ^ (Qc * 2 ^ (ρ * (l : ℝ))))) : ℝ) ^ 2
      = (2:ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ L : ℝ))) *
        ((Nat.ceil ((2:ℝ) ^ (Qc*2^(ρ*(l:ℝ))))) : ℝ) ^ 2 := by rw [hz]
    _ ≤ (2:ℝ) ^ (1 - s ^ 2) * ((Nat.ceil ((2:ℝ) ^ (Qc*2^(ρ*(l:ℝ))))) : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right hf1 (by positivity)
    _ ≤ (2:ℝ) ^ (1 - s ^ 2) * (4 * (2:ℝ) ^ (2*Qc*s)) := by
        apply mul_le_mul_of_nonneg_left hQbound (by positivity)
    _ = 4 * (2:ℝ) ^ ((1 - s ^ 2) + 2*Qc*s) := by
        have h : (2:ℝ) ^ (1-s^2) * (4 * (2:ℝ) ^ (2*Qc*s))
            = 4 * ((2:ℝ) ^ (1-s^2) * (2:ℝ) ^ (2*Qc*s)) := by ring
        rw [h, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ ≤ 4 * (2:ℝ) ^ (1 + Qc ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 8 * (2:ℝ) ^ (Qc ^ 2) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
        ring

end Work.KMTPlan.A6
