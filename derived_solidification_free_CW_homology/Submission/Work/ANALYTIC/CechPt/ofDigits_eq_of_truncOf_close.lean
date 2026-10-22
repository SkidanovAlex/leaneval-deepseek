import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels

/-!
# Closeness of the level truncations forces equality of the two reals

Suppose two digit sequences `d`, `e` have level-`m` truncations `truncOf m d`, `truncOf m e` that
differ by at most one for every `m`, and suppose `D`, `E` are reals whose level-`m` dyadic
approximations `2^(m+1) * D`, `2^(m+1) * E` lie in the intervals
`[truncOf m d, truncOf m d + 1]`, `[truncOf m e, truncOf m e + 1]` respectively.  Then `D = E`.

The mathematics is the Archimedean property of `ℝ`: the hypotheses give
`2^(m+1) * |D - E| ≤ 2` for every `m`, i.e. `|D - E| ≤ (1/2)^m → 0`.
-/

namespace Work.ANALYTIC.CechPt

theorem ofDigits_eq_of_truncOf_close (d e : ℕ → Fin 2) (D E : ℝ)
    (h : ∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m d ≤ Work.ANALYTIC.CechPt.truncOf m e + 1)
    (h' : ∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m e ≤ Work.ANALYTIC.CechPt.truncOf m d + 1)
    (hd : ∀ m : ℕ, ((Work.ANALYTIC.CechPt.truncOf m d : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) * D ∧
        (2 : ℝ) ^ (m + 1) * D ≤ ((Work.ANALYTIC.CechPt.truncOf m d : ℕ) : ℝ) + 1)
    (he : ∀ m : ℕ, ((Work.ANALYTIC.CechPt.truncOf m e : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) * E ∧
        (2 : ℝ) ^ (m + 1) * E ≤ ((Work.ANALYTIC.CechPt.truncOf m e : ℕ) : ℝ) + 1) :
    D = E := by
  -- Step 1: the hypotheses give `2^(m+1) * (D - E) ≤ 2`, and likewise with `D` and `E` swapped.
  have key : ∀ m : ℕ, (2 : ℝ) ^ (m + 1) * (D - E) ≤ 2 := by
    intro m
    have h1 : ((truncOf m d : ℕ) : ℝ) ≤ ((truncOf m e : ℕ) : ℝ) + 1 := by
      have := h m
      exact_mod_cast this
    have h2 := (hd m).2
    have h3 := (he m).1
    linarith
  have key' : ∀ m : ℕ, (2 : ℝ) ^ (m + 1) * (E - D) ≤ 2 := by
    intro m
    have h1 : ((truncOf m e : ℕ) : ℝ) ≤ ((truncOf m d : ℕ) : ℝ) + 1 := by
      have := h' m
      exact_mod_cast this
    have h2 := (he m).2
    have h3 := (hd m).1
    linarith
  -- Step 2: the Archimedean property upgrades `|D - E| ≤ (1/2)^m` for all `m` to `D = E`.
  have hDE : D ≤ E := by
    by_contra hlt
    have hlt' : E < D := not_le.mp hlt
    have hpos : 0 < D - E := sub_pos.mpr hlt'
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((D - E)⁻¹) (by norm_num : (1 : ℝ) < 2)
    have h2 : 1 < (2 : ℝ) ^ m * (D - E) := by
      have := mul_lt_mul_of_pos_right hm hpos
      rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at this
    have h3 : 2 < (2 : ℝ) ^ (m + 1) * (D - E) := by
      rw [pow_succ]
      linarith
    linarith [key m]
  have hED : E ≤ D := by
    by_contra hlt
    have hlt' : D < E := not_le.mp hlt
    have hpos : 0 < E - D := sub_pos.mpr hlt'
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((E - D)⁻¹) (by norm_num : (1 : ℝ) < 2)
    have h2 : 1 < (2 : ℝ) ^ m * (E - D) := by
      have := mul_lt_mul_of_pos_right hm hpos
      rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at this
    have h3 : 2 < (2 : ℝ) ^ (m + 1) * (E - D) := by
      rw [pow_succ]
      linarith
    linarith [key' m]
  exact le_antisymm hDE hED

end Work.ANALYTIC.CechPt
