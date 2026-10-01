import Mathlib

namespace Work.LinnikAreas

/-- Arithmetic core of the `szSimple` estimate: for every constant `C` there is a
threshold `M` such that, whenever `L ≥ M`, `N ≤ L` and `0 < lam ≤ 1/100`, the
product `(L/√lam + C + N + log 2/2 + 3/2) * ((√lam + lam)/L)` is `< 2`.

Writing `s = √lam` the product equals `1 + s + (C + N + log 2/2 + 3/2) * (s+s²)/L`;
the `L/√lam` term contributes the harmless `1 + s`, the `N`-term is controlled by
`N ≤ L`, and the constant term is killed by taking `M` larger than `11 C' / 79`
with `C' = C + log 2/2 + 3/2`. -/
theorem szSimple_arith_core (C : ℝ) : ∃ M : ℝ, ∀ L N lam : ℝ,
    0 < L → M ≤ L → N ≤ L → 0 < lam → lam ≤ 1 / 100 →
    (L / Real.sqrt lam + C + N + Real.log 2 / 2 + 3 / 2) * ((Real.sqrt lam + lam) / L) < 2 := by
  refine ⟨max 1 (11 * (C + Real.log 2 / 2 + 3 / 2) / 79 + 1), ?_⟩
  intro L N lam hL hML hNL hlam0 hlam1
  set s := Real.sqrt lam with hs
  have hs_pos : 0 < s := by rw [hs]; exact Real.sqrt_pos_of_pos hlam0
  have hs2 : s ^ 2 = lam := by rw [hs]; exact Real.sq_sqrt hlam0.le
  have hs_le : s ≤ 1 / 10 := by
    rw [hs]
    have h1 : Real.sqrt lam ≤ Real.sqrt (1 / 100) := Real.sqrt_le_sqrt hlam1
    have h2 : Real.sqrt ((1:ℝ) / 100) = 1 / 10 := by
      rw [show (1:ℝ) / 100 = (1 / 10) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    linarith
  have h79 : (79:ℝ) / 100 ≤ 1 - 2 * s - s ^ 2 := by nlinarith [hs_le, hs_pos.le]
  have hs_bd : s * (1 + s) ≤ 11 / 100 := by nlinarith [hs_le, hs_pos.le]
  have hspos : 0 < s * (1 + s) := by nlinarith [hs_pos]
  have hML2 : 11 * (C + Real.log 2 / 2 + 3 / 2) / 79 < L := by
    have : 11 * (C + Real.log 2 / 2 + 3 / 2) / 79 + 1 ≤ L := le_trans (le_max_right _ _) hML
    linarith
  have hkey : (C + Real.log 2 / 2 + 3 / 2) * (s * (1 + s)) < L * (1 - 2 * s - s ^ 2) := by
    by_cases hK : 0 ≤ C + Real.log 2 / 2 + 3 / 2
    · have h1 : (C + Real.log 2 / 2 + 3 / 2) * (s * (1 + s)) ≤ (C + Real.log 2 / 2 + 3 / 2) * (11 / 100) :=
        mul_le_mul_of_nonneg_left hs_bd hK
      have h2 : (C + Real.log 2 / 2 + 3 / 2) * (11 / 100) < L * (79 / 100) := by nlinarith [hML2]
      have h3 : L * (79 / 100) ≤ L * (1 - 2 * s - s ^ 2) := mul_le_mul_of_nonneg_left h79 hL.le
      linarith
    · have hKn : C + Real.log 2 / 2 + 3 / 2 < 0 := not_le.mp hK
      have h1 : (C + Real.log 2 / 2 + 3 / 2) * (s * (1 + s)) < 0 := mul_neg_of_neg_of_pos hKn hspos
      have h2 : 0 < L * (1 - 2 * s - s ^ 2) := by
        apply mul_pos hL; linarith
      linarith
  have haux : (C + N + Real.log 2 / 2 + 3 / 2) * (s * (1 + s)) < L * (1 - s) := by
    have hle : C + N + Real.log 2 / 2 + 3 / 2 ≤ L + (C + Real.log 2 / 2 + 3 / 2) := by linarith
    have h1 : (C + N + Real.log 2 / 2 + 3 / 2) * (s * (1 + s)) ≤ (L + (C + Real.log 2 / 2 + 3 / 2)) * (s * (1 + s)) :=
      mul_le_mul_of_nonneg_right hle hspos.le
    have h2 : (L + (C + Real.log 2 / 2 + 3 / 2)) * (s * (1 + s)) < L * (1 - s) := by nlinarith [hkey]
    linarith
  have hmain : (L + (C + N + Real.log 2 / 2 + 3 / 2) * s) * (s + s ^ 2) < 2 * (s * L) := by
    have hmul := mul_lt_mul_of_pos_right haux hs_pos
    nlinarith [hmul]
  have hEeq : (L / s + C + N + Real.log 2 / 2 + 3 / 2) * ((s + s ^ 2) / L)
      = (L + (C + N + Real.log 2 / 2 + 3 / 2) * s) * (s + s ^ 2) / (s * L) := by
    field_simp
    ring
  have hlam : lam = s ^ 2 := hs2.symm
  rw [hlam, hEeq]
  rw [div_lt_iff₀ (mul_pos hs_pos hL)]
  exact hmain

end Work.LinnikAreas
