import Submission.Work.BoxShrink.PinchOff.PerpBox
import Submission.Work.BoxShrink.PinchOff.TangentConfig
import Submission.Work.BoxShrink.Pinch.Plane

/-!
# A configuration of the standard torus whose cutting trace realises its own class in the box

The delivered chapter reduces Pardon's Lemma 3 to the residual `TracePerpSliceBox` (the honest form
of the residual, with `TameSlice` replaced by `TameClosedSlice`), whose content is: *a winding class
of the box region parallel to a period of the trace of the cutting plane is realised in the two
half-regions*.  This module fixes one configuration of the standard torus at which that statement
is **false**, while all the other hypotheses of the residual (`TransverseSlice`, `TameClosedSlice`,
`hZ`) are in force.  The configuration is

* `ψ = id`: the standard torus of revolution,
  `torusMap θ φ = ((2+cos φ) cos θ, (2+cos φ) sin θ, sin φ)`;
* `σ = (0 1 2)` (`ncCyc3`, the same cycle as `tangentCyc3`: `σ 0 = 1`, `σ 1 = 2`, `σ 2 = 0`), so
  that the box is `{|y 1 - 19/10| < 1, |y 2| < 2^{1/3}, |y 0 - 1| < 2^{2/3}}`, i.e.
  `y ∈ (9/10, 29/10)`, `|z| < 2^{1/3}`, `x ∈ (1 - 2^{2/3}, 1 + 2^{2/3})`;
* `s = 1` (`ncRad`) and the cutting plane `{x = 1/2}` (`c = ncCtr = (1, 19/10, 0)`, `u = -1/2`, so
  `planeG (θ,φ) = (2 + cos φ) cos θ - 1/2`).

The three facts which make it work, proved in the modules beside this one:

* the **meridian** `{θ = arccos (1/3)}` lies in the box region (`ncMer_mem_Omega`): its `y` ranges
  over `[2√2/3, 2√2] ⊂ (9/10, 29/10)`, its `x` over `[1/3, 1] ⊂ (1 - 2^{2/3}, 1 + 2^{2/3})` and its
  `z` over `[-1,1]`.  Its winding vector is `(0,1)`, so `(0,1) ∈ W(Ω)`;
* `Ω` lies in the open band `{9/10 < y < 29/10}`; the two halves `Ω⁺ = Ω ∩ {x > 1/2}`,
  `Ω⁻ = Ω ∩ {x < 1/2}` are each confined to a **window** of the parameter plane, so neither carries
  an essential loop (and neither does their union);
* the trace of the cutting plane is transverse to the surface, its periods all lie on the line
  `ℚ·(0,1)`, and the slice `Σ = Ω ∩ {x = 1/2}` is a union of two open arcs (so it carries no
  essential loop).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The configuration -/

/-- The cyclic permutation `(0 1 2)`, the same permutation as `tangentCyc3`. -/
def ncCyc3 : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- The box centre `(1, 19/10, 0)`. -/
def ncCtr : R3 := WithLp.toLp 2 (![1, (19 : ℝ) / 10, 0] : Fin 3 → ℝ)

/-- The box radius `s = 1`. -/
def ncRad : ℝ := 1

/-- The offset of the cutting plane: `u = -1/2`, so the plane is `{x = 1/2}`. -/
def ncU : ℝ := -1 / 2

/-- The meridian parameter of the loop lying in the box region: `arccos (1/3)`. -/
def ncTheta : ℝ := Real.arccos (1 / 3)

theorem ncCyc3_eq : ncCyc3 = tangentCyc3 := rfl

@[simp] theorem ncCyc3_zero : ncCyc3 0 = 1 := by decide
@[simp] theorem ncCyc3_one : ncCyc3 1 = 2 := by decide
@[simp] theorem ncCyc3_two : ncCyc3 2 = 0 := by decide

@[simp] theorem ncCtr_zero : ncCtr 0 = 1 := by simp [ncCtr]
@[simp] theorem ncCtr_one : ncCtr 1 = 19 / 10 := by simp [ncCtr]
@[simp] theorem ncCtr_two : ncCtr 2 = 0 := by simp [ncCtr]

theorem ncRad_eq : ncRad = 1 := rfl
theorem ncU_eq : ncU = -1 / 2 := rfl

/-- The parametrisation of the configuration is `torusMap`. -/
theorem par_nc (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par idDiffeo p = Work.Core.torusMap p.1 p.2 := by
  rw [Work.BoxShrink.Pinch.par_apply]; rfl

/-! ## The box in coordinates -/

/-- **The box of the configuration in coordinates.** -/
theorem mem_PBox_nc (y : R3) :
    y ∈ Submission.PBox ncRad ncCtr ncCyc3 ↔
      |y 1 - 19 / 10| < 1 ∧ |y 2| < (2 : ℝ) ^ (1 / 3 : ℝ) ∧
        |y 0 - 1| < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  rw [Submission.mem_PBox, ncRad_eq]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-- **The box norm of the configuration in coordinates.** -/
theorem boxNorm_nc (y : R3) :
    Submission.boxNorm ncCtr ncCyc3 y =
      max (max |y 1 - 19 / 10| (|y 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
        (|y 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Submission.boxNorm, ncCyc3_zero, ncCyc3_one, ncCyc3_two,
    ncCtr_one, ncCtr_two, ncCtr_zero, Submission.boxSide_zero,
    Submission.boxSide_one, Submission.boxSide_two]
  simp

/-- **The pull-back of the box norm**, in the coordinates `(θ, φ)` of `torusMap`. -/
theorem boxB_nc (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.boxB idDiffeo ncCtr ncCyc3 p =
      max (max |(2 + Real.cos p.2) * Real.sin p.1 - 19 / 10|
          (|Real.sin p.2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
        (|(2 + Real.cos p.2) * Real.cos p.1 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Work.BoxShrink.Pinch.boxB_apply, par_nc, boxNorm_nc]
  have h1 : (Work.Core.torusMap p.1 p.2) 1 = (2 + Real.cos p.2) * Real.sin p.1 := rfl
  have h2 : (Work.Core.torusMap p.1 p.2) 2 = Real.sin p.2 := rfl
  have h0 : (Work.Core.torusMap p.1 p.2) 0 = (2 + Real.cos p.2) * Real.cos p.1 := rfl
  rw [h1, h2, h0]

/-- **The box-region criterion in the parameter plane.** -/
theorem boxB_lt_one_iff (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.boxB idDiffeo ncCtr ncCyc3 p < 1 ↔
      |(2 + Real.cos p.2) * Real.sin p.1 - 19 / 10| < 1 ∧
        |Real.sin p.2| < (2 : ℝ) ^ (1 / 3 : ℝ) ∧
          |(2 + Real.cos p.2) * Real.cos p.1 - 1| < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  rw [boxB_nc, max_lt_iff, max_lt_iff,
    div_lt_one (by positivity : (0:ℝ) < 2 ^ (1/3:ℝ)),
    div_lt_one (by positivity : (0:ℝ) < 2 ^ (2/3:ℝ))]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **The pull-back of the plane coordinate**: `G (θ,φ) = (2 + cos φ) cos θ - 1/2`. -/
theorem planeG_nc (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.planeG idDiffeo ncCtr ncCyc3 ncU p =
      (2 + Real.cos p.2) * Real.cos p.1 - 1 / 2 := by
  rw [Work.BoxShrink.Pinch.planeG_apply, par_nc, Work.BoxShrink.Bubble.planeCoord_apply]
  have h0 : (Work.Core.torusMap p.1 p.2) 0 = (2 + Real.cos p.2) * Real.cos p.1 := rfl
  rw [ncCyc3_two, h0, ncCtr_zero, ncU_eq]
  ring

end

end Work.BoxShrink.PinchOff
