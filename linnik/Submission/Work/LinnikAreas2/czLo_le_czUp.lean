import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs

namespace Work.LinnikAreas2

/-- In the restricted ranges the lower cut-off is at most the upper cut-off: for `q ≥ 1`,
`r ≤ ⌊N/(qw)⌋` and `t ≤ ⌊N/(qy)⌋` one has `czLo w y r t ≤ czUp N q r t`.
Indeed `r ≤ N/(qw)` gives `w ≤ N/(qr)` hence `⌊w/t⌋ ≤ w/t ≤ N/(qrt)`, and `t ≤ N/(qy)` gives
`y ≤ N/(qt)` hence `⌊y/r⌋ ≤ y/r ≤ N/(qrt)`. -/
theorem czLo_le_czUp (w y : ℝ) (N q r t : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) (hq : 1 ≤ q)
    (hr : r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q))
    (ht : t ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czT y N q)) :
    Work.ZeroDensity.Jutila.czLo w y r t ≤ Work.ZeroDensity.Jutila.czUp N q r t := by
  rw [Finset.mem_Icc] at hr ht
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  have Hpos : 0 < q * r * t := by positivity
  -- `r ≤ ⌊N/(qw)⌋` gives the real bound `r ≤ N/(qw)`
  have hrle : (r : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
    have h1 : r ≤ ⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ := by
      simpa only [Work.ZeroDensity.Jutila.czR] using hr2
    calc (r : ℝ) ≤ (⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ (N : ℝ) / ((q : ℝ) * w) := Nat.floor_le (by positivity)
  -- `t ≤ ⌊N/(qy)⌋` gives the real bound `t ≤ N/(qy)`
  have htle : (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
    have h1 : t ≤ ⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ := by
      simpa only [Work.ZeroDensity.Jutila.czT] using ht2
    calc (t : ℝ) ≤ (⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ (N : ℝ) / ((q : ℝ) * y) := Nat.floor_le (by positivity)
  -- consequently `w·q·r ≤ N` and `y·q·t ≤ N`
  have hwqr : w * (q : ℝ) * (r : ℝ) ≤ (N : ℝ) := by
    have h2 : (r : ℝ) * ((q : ℝ) * w) ≤ (N : ℝ) := (le_div_iff₀ (by positivity)).mp hrle
    nlinarith [h2]
  have hyqt : y * (q : ℝ) * (t : ℝ) ≤ (N : ℝ) := by
    have h2 : (t : ℝ) * ((q : ℝ) * y) ≤ (N : ℝ) := (le_div_iff₀ (by positivity)).mp htle
    nlinarith [h2]
  rw [Work.ZeroDensity.Jutila.czLo, Work.ZeroDensity.Jutila.czUp]
  apply max_le
  · -- `⌊w/t⌋₊ ≤ N/(qrt)`
    rw [Nat.le_div_iff_mul_le Hpos, ← Nat.cast_le (α := ℝ)]
    push_cast
    have hA : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ w / (t : ℝ) := Nat.floor_le (by positivity)
    have hAt : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) * (t : ℝ) ≤ w := by
      have h := mul_le_mul_of_nonneg_right hA (le_of_lt (by positivity : (0 : ℝ) < t))
      rwa [div_mul_cancel₀ w (by positivity : (t : ℝ) ≠ 0)] at h
    have h1 : (((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) * (t : ℝ)) * ((q : ℝ) * (r : ℝ))
        ≤ w * ((q : ℝ) * (r : ℝ)) :=
      mul_le_mul_of_nonneg_right hAt (by positivity)
    nlinarith [h1, hwqr]
  · -- `⌊y/r⌋₊ ≤ N/(qrt)`
    rw [Nat.le_div_iff_mul_le Hpos, ← Nat.cast_le (α := ℝ)]
    push_cast
    have hB : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ y / (r : ℝ) := Nat.floor_le (by positivity)
    have hBr : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) ≤ y := by
      have h := mul_le_mul_of_nonneg_right hB (le_of_lt (by positivity : (0 : ℝ) < r))
      rwa [div_mul_cancel₀ y (by positivity : (r : ℝ) ≠ 0)] at h
    have h1 : (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) * ((q : ℝ) * (t : ℝ))
        ≤ y * ((q : ℝ) * (t : ℝ)) :=
      mul_le_mul_of_nonneg_right hBr (by positivity)
    nlinarith [h1, hyqt]

end Work.LinnikAreas2
