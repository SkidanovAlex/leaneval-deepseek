import Submission.Work.Stems.Cubical.Kop4

/-!
# The boundary parametrisation `bd : I → ∂I²`: its values, and surjectivity onto `∂I²`

`Work.Stems.Cubical.bd` traverses `∂I²` counterclockwise from `(0,0)`, its four edges being
parametrised linearly.  Here we compute `bd` at the points of `I` corresponding to the four edges,
and deduce that every point of `∂I²` is of the form `bd t`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- The point of `I` with coordinate `(a+1)/4` (right edge). -/
def rightPt (a : unitInterval) : unitInterval :=
  ⟨(a : ℝ) / 4 + 1 / 4, by constructor <;> linarith [a.2.1, a.2.2]⟩

/-- The point of `I` with coordinate `(3-a)/4` (top edge). -/
def topPt (a : unitInterval) : unitInterval :=
  ⟨(3 - (a : ℝ)) / 4, by constructor <;> linarith [a.2.1, a.2.2]⟩

/-- The point of `I` with coordinate `1-a/4` (left edge). -/
def leftPt (a : unitInterval) : unitInterval :=
  ⟨1 - (a : ℝ) / 4, by constructor <;> linarith [a.2.1, a.2.2]⟩

@[simp] theorem rightPt_val (a : unitInterval) : (rightPt a : ℝ) = (a : ℝ) / 4 + 1 / 4 := rfl

@[simp] theorem topPt_val (a : unitInterval) : (topPt a : ℝ) = (3 - (a : ℝ)) / 4 := rfl

@[simp] theorem leftPt_val (a : unitInterval) : (leftPt a : ℝ) = 1 - (a : ℝ) / 4 := rfl

theorem bd_apply_zero (t : unitInterval) : (bd t : IC 2) 0 = ⟨bd0 t, bd0_mem t⟩ := rfl

theorem bd_apply_one (t : unitInterval) : (bd t : IC 2) 1 = ⟨bd1 t, bd1_mem t⟩ := rfl

@[simp] theorem bd0_right (a : unitInterval) : bd0 (rightPt a) = 1 := by
  have h4 : 4 * (rightPt a : ℝ) = (a : ℝ) + 1 := by rw [rightPt_val]; ring
  unfold bd0
  rw [h4, show (3 : ℝ) - ((a : ℝ) + 1) = 2 - (a : ℝ) by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

@[simp] theorem bd1_right (a : unitInterval) : bd1 (rightPt a) = a := by
  have h4 : 4 * (rightPt a : ℝ) = (a : ℝ) + 1 := by rw [rightPt_val]; ring
  unfold bd1
  rw [h4, show (4 : ℝ) - ((a : ℝ) + 1) = 3 - (a : ℝ) by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

@[simp] theorem bd0_top (a : unitInterval) : bd0 (topPt a) = a := by
  have h4 : 4 * (topPt a : ℝ) = 3 - (a : ℝ) := by rw [topPt_val]; ring
  unfold bd0
  rw [h4, show (3 : ℝ) - (3 - (a : ℝ)) = (a : ℝ) by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

@[simp] theorem bd1_top (a : unitInterval) : bd1 (topPt a) = 1 := by
  have h4 : 4 * (topPt a : ℝ) = 3 - (a : ℝ) := by rw [topPt_val]; ring
  unfold bd1
  rw [h4, show (4 : ℝ) - (3 - (a : ℝ)) = (a : ℝ) + 1 by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

@[simp] theorem bd0_left (a : unitInterval) : bd0 (leftPt a) = 0 := by
  have h4 : 4 * (leftPt a : ℝ) = 4 - (a : ℝ) := by rw [leftPt_val]; ring
  unfold bd0
  rw [h4, show (3 : ℝ) - (4 - (a : ℝ)) = (a : ℝ) - 1 by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

@[simp] theorem bd1_left (a : unitInterval) : bd1 (leftPt a) = a := by
  have h4 : 4 * (leftPt a : ℝ) = 4 - (a : ℝ) := by rw [leftPt_val]; ring
  unfold bd1
  rw [h4, show (4 : ℝ) - (4 - (a : ℝ)) = (a : ℝ) by ring]
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [a.2.1, a.2.2]

/-- `bd` at the parametrisation of the bottom edge. -/
@[simp] theorem bd_quarter_bot (a : unitInterval) :
    bd (quarter a) = fun j : Fin 2 => if j = 0 then a else 0 := by
  funext j
  fin_cases j <;> simp [bd_apply_zero, bd_apply_one, bd0_quarter, bd1_quarter]

/-- `bd` at the parametrisation of the right edge. -/
@[simp] theorem bd_right (a : unitInterval) :
    bd (rightPt a) = fun j : Fin 2 => if j = 0 then 1 else a := by
  funext j
  fin_cases j <;> simp [bd_apply_zero, bd_apply_one]

/-- `bd` at the parametrisation of the top edge. -/
@[simp] theorem bd_top (a : unitInterval) :
    bd (topPt a) = fun j : Fin 2 => if j = 0 then a else 1 := by
  funext j
  fin_cases j <;> simp [bd_apply_zero, bd_apply_one]

/-- `bd` at the parametrisation of the left edge. -/
@[simp] theorem bd_left (a : unitInterval) :
    bd (leftPt a) = fun j : Fin 2 => if j = 0 then 0 else a := by
  funext j
  fin_cases j <;> simp [bd_apply_zero, bd_apply_one]

/-- **Every point of `∂I²` is `bd t` for some `t`.** -/
theorem bd_eq_of_mem_boundary (x : IC 2) (hx : x ∈ Cube.boundary (Fin 2)) :
    ∃ t : unitInterval, bd t = x := by
  rw [Cube.boundary] at hx
  obtain ⟨i, hi | hi⟩ := hx
  · fin_cases i
    · refine ⟨leftPt (x 1), ?_⟩
      rw [bd_left]
      funext j
      fin_cases j <;> simp_all
    · refine ⟨quarter (x 0), ?_⟩
      rw [bd_quarter_bot]
      funext j
      fin_cases j <;> simp_all
  · fin_cases i
    · refine ⟨rightPt (x 1), ?_⟩
      rw [bd_right]
      funext j
      fin_cases j <;> simp_all
    · refine ⟨topPt (x 0), ?_⟩
      rw [bd_top]
      funext j
      fin_cases j <;> simp_all

end

end Work.Stems.Hur2
