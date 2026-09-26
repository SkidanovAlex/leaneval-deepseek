import Mathlib

namespace Work.BoxShrink.Core.Counting

/-- If a `ℕ∞`-valued `e` has `ENNReal`-image bounded above by `ENNReal.ofReal C`,
and `C < n` for a positive natural `n`, then `e < n`. -/
theorem encard_lt_natCast_of_coe_le_ofReal {e : ℕ∞} {C : ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : ((e : ENNReal) ≤ ENNReal.ofReal C)) (hC : C < (n : ℝ)) : e < (n : ℕ∞) := by
  have hCn : ENNReal.ofReal C < (n : ENNReal) := (ENNReal.ofReal_lt_natCast hn).mpr hC
  have h1 : (e : ENNReal) < (n : ENNReal) := lt_of_le_of_lt h hCn
  exact (StrictMono.lt_iff_lt ENat.toENNReal_strictMono).mp h1

end Work.BoxShrink.Core.Counting
