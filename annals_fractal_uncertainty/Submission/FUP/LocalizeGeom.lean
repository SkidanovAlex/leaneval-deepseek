import Submission.FUP.HSSets

open MeasureTheory Metric Set
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The geometry of the localisation set

This module contains the elementary geometry of the localisation step of Han–Schlag's
Corollary 4.2 (see `Submission/FUP/ROADMAP.md`, Session 53 §§1, 5.2):

* `locCubes c₁ a` — the localisation set `S = ⋃_n box (a n) (a n + 2c₁)`, one box of side `2c₁`
  per cell of the `2ℤ^d`-grid (`a n` is constrained by the caller to lie in the cell);
* `locCubesSmall c₁ a` — the concentric sub-boxes `I'_n` of side `c₁/2`;
* `separation_locCubes` — for `x ∈ S'` and `y ∉ S` there is a coordinate with
  `|x i - y i| > c₁/2`.  This is the hypothesis of the commons lemma
  `Commons.MeasureTheory.localised_conv_bound` with `r := c₁/2` (the radius of the compactly
  supported damping kernel), and it is why the sub-boxes are taken of side `c₁/2` rather than
  `c₁`: the inequality is *strict*.
-/

/-- The localisation set: one box of side `2c₁` in every cell. -/
noncomputable def locCubes (c₁ : ℝ) (a : (Fin d → ℤ) → Fin d → ℝ) : Set ℝᵈ :=
  ⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + 2 * c₁)

/-- The concentric sub-boxes of side `c₁/2`. -/
noncomputable def locCubesSmall (c₁ : ℝ) (a : (Fin d → ℤ) → Fin d → ℝ) : Set ℝᵈ :=
  ⋃ n : Fin d → ℤ, box (fun i => a n i + 3 * c₁ / 4) (fun i => a n i + 5 * c₁ / 4)

lemma measurableSet_locCubes (c₁ : ℝ) (a : (Fin d → ℤ) → Fin d → ℝ) :
    MeasurableSet (locCubes c₁ a) :=
  MeasurableSet.iUnion fun n => measurableSet_box _ _

lemma measurableSet_locCubesSmall (c₁ : ℝ) (a : (Fin d → ℤ) → Fin d → ℝ) :
    MeasurableSet (locCubesSmall c₁ a) :=
  MeasurableSet.iUnion fun n => measurableSet_box _ _

lemma mem_locCubes {c₁ : ℝ} {a : (Fin d → ℤ) → Fin d → ℝ} {y : ℝᵈ} :
    y ∈ locCubes c₁ a ↔ ∃ n : Fin d → ℤ, ∀ i : Fin d, a n i ≤ y i ∧ y i ≤ a n i + 2 * c₁ := by
  simp only [locCubes, Set.mem_iUnion, mem_box]

lemma mem_locCubesSmall {c₁ : ℝ} {a : (Fin d → ℤ) → Fin d → ℝ} {x : ℝᵈ} :
    x ∈ locCubesSmall c₁ a ↔
      ∃ n : Fin d → ℤ, ∀ i : Fin d, a n i + 3 * c₁ / 4 ≤ x i ∧ x i ≤ a n i + 5 * c₁ / 4 := by
  simp only [locCubesSmall, Set.mem_iUnion, mem_box]

/-- **The separation property of the localisation step.**  For `x` in a concentric sub-box of
side `c₁/2` and `y` outside the localisation set there is a coordinate `i` with
`|x i - y i| > c₁/2`. -/
theorem separation_locCubes {c₁ : ℝ} (hc₁ : 0 < c₁) (a : (Fin d → ℤ) → Fin d → ℝ) :
    ∀ x ∈ locCubesSmall c₁ a, ∀ y, y ∉ locCubes c₁ a → ∃ i : Fin d, c₁ / 2 < |x i - y i| := by
  intro x hx y hy
  obtain ⟨n, hn⟩ := mem_locCubesSmall.mp hx
  have hy' := hy
  rw [mem_locCubes] at hy'
  push_neg at hy'
  obtain ⟨i, hi⟩ := hy' n
  refine ⟨i, ?_⟩
  have hx1 := (hn i).1
  have hx2 := (hn i).2
  rcases lt_or_ge (y i) (a n i) with h | h
  · -- `y i < a n i`
    have hlt : 3 * c₁ / 4 < x i - y i := by linarith
    rw [abs_of_pos (by linarith)]
    linarith
  · -- `a n i ≤ y i`, hence `y i > a n i + 2 c₁`
    have h2 : a n i + 2 * c₁ < y i := hi h
    have hlt : 3 * c₁ / 4 < y i - x i := by linarith
    rw [abs_of_neg (by linarith)]
    linarith

end Submission.FUP
