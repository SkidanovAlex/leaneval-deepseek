import Mathlib

namespace Work.LinnikBurgess

lemma cftValAddLt {p : ℕ} [Fact p.Prime] {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : padicValInt p x < padicValInt p y) :
    padicValInt p (x + y) = padicValInt p x := by
  have hxy : x + y ≠ 0 := by
    intro h0
    have hyx : y = -x := by omega
    rw [hyx] at h
    simp [padicValInt, Int.natAbs_neg] at h
  have hrat : padicValRat p ((x : ℚ) + (y : ℚ)) = padicValRat p (x : ℚ) :=
    padicValRat.add_eq_of_lt (by exact_mod_cast hxy) (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by simpa using h)
  have hZ : (padicValInt p (x + y) : ℤ) = (padicValInt p x : ℤ) := by
    rw [← padicValRat.of_int (p := p) (z := x + y), ← padicValRat.of_int (p := p) (z := x)]
    simpa [Int.cast_add] using hrat
  exact_mod_cast hZ

end Work.LinnikBurgess
