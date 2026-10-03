import Mathlib
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall

namespace Commons.NumberTheory.Zeta

set_option linter.unusedVariables false

/-- The zeros of the entire function `riemannZeta₁` inside an arbitrary closed ball form a
finite set.  This is `zetaZeroBall` (finiteness of the zeros in a ball centered at the origin)
transported to an arbitrary center. -/
lemma zeta1_zero_ball_finite (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ S : Finset ℂ, ∀ ρ : ℂ, ρ ∈ S ↔ riemannZeta₁ ρ = 0 ∧ ‖ρ - c‖ ≤ R := by
  obtain ⟨S₀, hS₀⟩ := zetaZeroBall (‖c‖ + R) (by positivity)
  refine ⟨S₀.filter (fun ρ => ‖ρ - c‖ ≤ R), ?_⟩
  intro ρ
  rw [Finset.mem_filter, hS₀]
  constructor
  · rintro ⟨⟨-, hζ⟩, hd⟩
    exact ⟨hζ, hd⟩
  · rintro ⟨hζ, hd⟩
    refine ⟨⟨?_, hζ⟩, hd⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : (ρ - c) + c = ρ := by ring
    calc ‖ρ‖ = ‖(ρ - c) + c‖ := by rw [h1]
      _ ≤ ‖ρ - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ R + ‖c‖ := by linarith [hd]
      _ = ‖c‖ + R := by ring

/-- For every real ordinate `t` with `|t| ≥ 5` there is a radius `R ∈ [7/2, 4]` such that
both the circle of radius `R` and the circle of radius `R/2` around `2 + i t` are free of
zeros of the completed zeta function `ζ₁`.  The only input is the finiteness of the zeros of
the entire function `ζ₁` in the disk of radius `4`; the two forbidden families of radii
`‖ρ - (2 + i t)‖` and `2 ‖ρ - (2 + i t)‖` are then finite, while `[7/2, 4]` is not. -/
theorem zeta1_exists_good_radius (t : ℝ) (ht : 5 ≤ |t|) :
    ∃ R : ℝ, 7 / 2 ≤ R ∧ R ≤ 4 ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ = R → riemannZeta₁ w ≠ 0) ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ = R / 2 → riemannZeta₁ w ≠ 0) := by
  classical
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  obtain ⟨Z, hZ⟩ := zeta1_zero_ball_finite c 4 (by norm_num)
  set B : Finset ℝ := Z.biUnion (fun ρ => ({‖ρ - c‖, 2 * ‖ρ - c‖} : Finset ℝ)) with hB
  have hBmem : ∀ r : ℝ, r ∈ B ↔ ∃ ρ ∈ Z, r = ‖ρ - c‖ ∨ r = 2 * ‖ρ - c‖ := by
    intro r
    rw [hB, Finset.mem_biUnion]
    constructor
    · rintro ⟨ρ, hρ, hr⟩
      refine ⟨ρ, hρ, ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton] at hr
      exact hr
    · rintro ⟨ρ, hρ, h | h⟩
      · exact ⟨ρ, hρ, by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl h⟩
      · exact ⟨ρ, hρ, by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr h⟩
  obtain ⟨R, hRIcc, hRB⟩ :=
    (Set.Icc_infinite (show (7 / 2 : ℝ) < 4 by norm_num)).exists_notMem_finite B.finite_toSet
  rw [Set.mem_Icc] at hRIcc
  have hRnotB : R ∉ B := fun h => hRB (by simpa using h)
  refine ⟨R, hRIcc.1, hRIcc.2, ?_, ?_⟩
  · intro w hw hζ
    have hwZ : w ∈ Z := (hZ w).mpr ⟨hζ, le_of_eq hw |>.trans hRIcc.2⟩
    exact hRnotB ((hBmem R).mpr ⟨w, hwZ, Or.inl hw.symm⟩)
  · intro w hw hζ
    have hle : ‖w - c‖ ≤ 4 := by
      rw [hw]; linarith [hRIcc.2]
    have hwZ : w ∈ Z := (hZ w).mpr ⟨hζ, hle⟩
    have h2 : R = 2 * ‖w - c‖ := by rw [hw]; ring
    exact hRnotB ((hBmem R).mpr ⟨w, hwZ, Or.inr h2⟩)

end Commons.NumberTheory.Zeta
