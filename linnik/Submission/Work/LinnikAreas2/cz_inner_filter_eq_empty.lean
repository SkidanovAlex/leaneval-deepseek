import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs

namespace Work.LinnikAreas2

/-- The inner `m`-filter of the reindexed cross sum is empty once `q > ⌊N/y⌋`, or `r > ⌊N/(qw)⌋`,
or `t > ⌊N/(qy)⌋`: any `m` in the filter satisfies `m·q·r·t ≤ N` (from `m ≤ N/(q*r*t)`), and
`w < m·t`, `y < m·r` then force `q·r·w < N` (whence `r ≤ ⌊N/(qw)⌋`) and `q·y·t < N`
(whence `q ≤ ⌊N/y⌋` and `t ≤ ⌊N/(qy)⌋`, using `t ≥ 1`). -/
theorem cz_inner_filter_eq_empty (w y : ℝ) (N q r t : ℕ)
    (hw : 1 ≤ w) (hy : 1 ≤ y) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (h : Work.ZeroDensity.Jutila.czQ y N < q ∨ Work.ZeroDensity.Jutila.czR w N q < r
      ∨ Work.ZeroDensity.Jutila.czT y N q < t) :
    (Finset.Icc 1 (N / (q * r * t))).filter
        (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
          ∧ y < ((m * r : ℕ) : ℝ)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro m hm hmem
  obtain ⟨hcop, hwt, hyr⟩ := hmem
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm1, hmle⟩ := hm
  have hypos : (0 : ℝ) < y := by linarith
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hden : 0 < q * r * t := by positivity
  have hmul : m * (q * r * t) ≤ N := (Nat.le_div_iff_mul_le hden).mp hmle
  have hmulR : (m : ℝ) * (q : ℝ) * (r : ℝ) * (t : ℝ) ≤ (N : ℝ) := by
    have h' : ((m * (q * r * t) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmul
    have he : ((m * (q * r * t) : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) * (r : ℝ) * (t : ℝ) := by
      push_cast; ring
    rw [he] at h'
    exact h'
  have hyreal : y < (m : ℝ) * (r : ℝ) := by
    have he : ((m * r : ℕ) : ℝ) = (m : ℝ) * (r : ℝ) := by push_cast; ring
    rw [he] at hyr
    exact hyr
  have hwtreal : w < (m : ℝ) * (t : ℝ) := by
    have he : ((m * t : ℕ) : ℝ) = (m : ℝ) * (t : ℝ) := by push_cast; ring
    rw [he] at hwt
    exact hwt
  -- `q·y·t < N`, obtained by multiplying `y < m·r` by the positive `q·t`
  have hB : (q : ℝ) * y ≤ (q : ℝ) * y * (t : ℝ) := by
    have h0 : (0 : ℝ) ≤ (q : ℝ) * y := by positivity
    nlinarith [h0, ht1]
  have hA : (q : ℝ) * y * (t : ℝ) < (N : ℝ) := by
    have h1 : y * ((q : ℝ) * (t : ℝ)) < (m : ℝ) * (r : ℝ) * ((q : ℝ) * (t : ℝ)) :=
      mul_lt_mul_of_pos_right hyreal (by positivity)
    have h2 : (m : ℝ) * (r : ℝ) * ((q : ℝ) * (t : ℝ)) = (m : ℝ) * (q : ℝ) * (r : ℝ) * (t : ℝ) := by
      ring
    rw [h2] at h1
    have h3 : (q : ℝ) * y * (t : ℝ) = y * ((q : ℝ) * (t : ℝ)) := by ring
    rw [h3]
    exact lt_of_lt_of_le h1 hmulR
  -- `q·r·w < N`, obtained by multiplying `w < m·t` by the positive `q·r`
  have hC : (q : ℝ) * (r : ℝ) * w < (N : ℝ) := by
    have h1 : w * ((q : ℝ) * (r : ℝ)) < (m : ℝ) * (t : ℝ) * ((q : ℝ) * (r : ℝ)) :=
      mul_lt_mul_of_pos_right hwtreal (by positivity)
    have h2 : (m : ℝ) * (t : ℝ) * ((q : ℝ) * (r : ℝ)) = (m : ℝ) * (q : ℝ) * (r : ℝ) * (t : ℝ) := by
      ring
    rw [h2] at h1
    have h3 : (q : ℝ) * (r : ℝ) * w = w * ((q : ℝ) * (r : ℝ)) := by ring
    rw [h3]
    exact lt_of_lt_of_le h1 hmulR
  have hqle : q ≤ Work.ZeroDensity.Jutila.czQ y N := by
    show q ≤ ⌊(N : ℝ) / y⌋₊
    apply Nat.le_floor
    rw [le_div_iff₀ hypos]
    exact le_of_lt (lt_of_le_of_lt hB hA)
  have hrle : r ≤ Work.ZeroDensity.Jutila.czR w N q := by
    show r ≤ ⌊(N : ℝ) / ((q : ℝ) * w)⌋₊
    apply Nat.le_floor
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * w)]
    have he : (r : ℝ) * ((q : ℝ) * w) = (q : ℝ) * (r : ℝ) * w := by ring
    rw [he]
    linarith [hC]
  have htle : t ≤ Work.ZeroDensity.Jutila.czT y N q := by
    show t ≤ ⌊(N : ℝ) / ((q : ℝ) * y)⌋₊
    apply Nat.le_floor
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * y)]
    have he : (t : ℝ) * ((q : ℝ) * y) = (q : ℝ) * y * (t : ℝ) := by ring
    rw [he]
    linarith [hA]
  rcases h with h | h | h
  · exact absurd h (not_lt.mpr hqle)
  · exact absurd h (not_lt.mpr hrle)
  · exact absurd h (not_lt.mpr htle)

end Work.LinnikAreas2
