import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.basinEnters.petal_capture

/-!
# The good-basin lemma: every basin orbit enters the petal or hits `0`

`basin_good_exists` is the pointwise statement needed by PARAB0 (`basin_enter`): a point `z` of
the uniform parabolic basin of `f` has an iterate in the petal `Petal r M` — with the one
exception that its orbit may instead hit `0` (the degenerate case in which `f` collapses a whole
neighbourhood of `z` to `0`; then `z` is in the uniform basin but never enters any petal, see
`Submission/Work/Parab/basinEnters/counterexample.lean`).  The disjunction `∨ f^[n] z = 0` in the
statement is exactly what makes the statement true in general.

The proof is a two-case argument:

* if some iterate of `z` is `0`, take that iterate (right disjunct);
* otherwise the orbit of `z` converges to `0` (uniform convergence on a neighbourhood of `z`)
  and never vanishes, so the petal-capture argument `exists_iterate_mem_petal` — the chart
  increment along the orbit is `h zₙ / (1 + zₙ h zₙ) → 1`, whence `Re (-1/zₙ) → +∞` — puts some
  iterate into the petal `Petal r' M` for `r'` small enough that the quantitative estimates of
  `ParabolicBounds f h a r A A'` apply; enlarging the radius back to `r` with `Petal_mono`
  concludes (left disjunct).
-/

open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false

namespace Work.Parab.basinGood

noncomputable section

/-- **Restriction of the quantitative hypotheses to a small radius.**  Given `ParabolicBounds` at
*any* radius `r > 0`, there is a radius `r' ≤ min r (1/16)` at which the smallness condition
`A * r' ^ 2 + ‖a‖ * r' ≤ 1/8` used by the petal-capture estimates holds, and `ParabolicBounds`
still holds with the same constants. -/
lemma exists_small_bounds {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ r' ≤ 1 / 16 ∧
      A * r' ^ 2 + ‖a‖ * r' ≤ 1 / 8 ∧
      Work.FatouCoord.ParabolicBounds f h a r' A A' := by
  have hA0 : 0 ≤ A := hb.hA
  have hden : 0 < 16 * (‖a‖ + A + 1) := by
    have : 0 ≤ ‖a‖ + A := by linarith [norm_nonneg a, hA0]
    linarith
  have hρ : 0 < 1 / (16 * (‖a‖ + A + 1)) := one_div_pos.mpr hden
  set R : ℝ := min r (min (1 / 16) (1 / (16 * (‖a‖ + A + 1)))) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact lt_min hb.hr (lt_min (by norm_num) hρ)
  have hRr : R ≤ r := by rw [hR]; exact min_le_left _ _
  have hR16 : R ≤ 1 / 16 := by
    rw [hR]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRbig : R ≤ 1 / (16 * (‖a‖ + A + 1)) := by
    rw [hR]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hA1 : A ≤ ‖a‖ + A + 1 := by linarith [norm_nonneg a]
  have hidentity : (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) = 1 / 16 := by
    field_simp
  have hAr : A * R ≤ 1 / 16 := by
    have h1 : A * R ≤ A * (1 / (16 * (‖a‖ + A + 1))) :=
      mul_le_mul_of_nonneg_left hRbig hA0
    have h2 : A * (1 / (16 * (‖a‖ + A + 1))) ≤
        (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
      mul_le_mul_of_nonneg_right hA1 hρ.le
    linarith [h1, h2, hidentity]
  have hair : ‖a‖ * R ≤ 1 / 16 := by
    have h1 : ‖a‖ * R ≤ ‖a‖ * (1 / (16 * (‖a‖ + A + 1))) :=
      mul_le_mul_of_nonneg_left hRbig (norm_nonneg a)
    have h2 : ‖a‖ * (1 / (16 * (‖a‖ + A + 1))) ≤
        (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith [hA0]) hρ.le
    linarith [h1, h2, hidentity]
  have hsq : A * R ^ 2 ≤ 1 / 16 := by
    have h : R ^ 2 ≤ R * (1 / 16) := by nlinarith [hRpos, hR16]
    calc A * R ^ 2 ≤ A * (R * (1 / 16)) := mul_le_mul_of_nonneg_left h hA0
      _ = (A * R) * (1 / 16) := by ring
      _ ≤ (1 / 16) * (1 / 16) := mul_le_mul_of_nonneg_right hAr (by norm_num)
      _ ≤ 1 / 16 := by norm_num
  refine ⟨R, hRpos, hRr, hR16, by linarith, ?_⟩
  exact Work.Parab.basinEnters.parabolicBounds_mono hb hRpos hRr

/-- **The good-basin lemma.**  Every point of the uniform parabolic basin of `f` either has an
iterate in the petal `Petal r M`, or an iterate equal to `0`. -/
theorem basin_good_exists {f h : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ} {D : Set ℂ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hM : 0 < M) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ,
      f^[n] z ∈ Work.FatouCoord.Petal r M ∨ f^[n] z = 0 := by
  intro z hz
  by_cases hhit : ∃ n : ℕ, f^[n] z = 0
  · obtain ⟨n, hn⟩ := hhit
    exact ⟨n, Or.inr hn⟩
  · push Not at hhit
    obtain ⟨r', _hr'pos, hr'r, hr'16, hsmall, hb'⟩ := exists_small_bounds hb
    obtain ⟨n, hn⟩ := Work.Parab.basinEnters.exists_iterate_mem_petal hb' hr'16 hsmall hM
      (Work.Parab.basinEnters.tendsto_iterate_of_mem_basin hz) hhit
    have hmono : Work.FatouCoord.Petal r' M ⊆ Work.FatouCoord.Petal r M :=
      Work.FatouCoord.Petal_mono (M := M) (M' := M) hr'r le_rfl
    exact ⟨n, Or.inl (hmono hn)⟩

end

end Work.Parab.basinGood
