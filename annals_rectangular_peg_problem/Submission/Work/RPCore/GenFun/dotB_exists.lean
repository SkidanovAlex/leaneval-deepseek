import Mathlib
import Submission.Work.RPCore.GenFun.Basic

/-!
# The dot product as a continuous bilinear form on `PS`

`Work.RPCore.GenFun.dot` is the Euclidean pairing of `PS = ℝ⁴` written out in coordinates.
Here we exhibit it as a genuine continuous bilinear form
`dotB : PS →L[ℝ] PS →L[ℝ] ℝ`, sending `(u, v)` to `dot u v`, and record that it is symmetric.

The construction writes `dot` as the sum of the four rank-one pairings `uᵢ · vᵢ`; each of these
is `cᵢ.smulRight cᵢ` for the coordinate functional `cᵢ`, so continuity in both variables is
automatic and no norm estimate is needed.
-/

set_option autoImplicit false

noncomputable section

open Work.RPV

namespace Work.RPCore.GenFun

/-! ## The four coordinate functionals on `PS` -/

/-- First coordinate `u ↦ u.1.1`. -/
def co11 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- Second coordinate `u ↦ u.1.2`. -/
def co12 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- Third coordinate `u ↦ u.2.1`. -/
def co21 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- Fourth coordinate `u ↦ u.2.2`. -/
def co22 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

@[simp] theorem co11_apply (u : PS) : co11 u = u.1.1 := rfl
@[simp] theorem co12_apply (u : PS) : co12 u = u.1.2 := rfl
@[simp] theorem co21_apply (u : PS) : co21 u = u.2.1 := rfl
@[simp] theorem co22_apply (u : PS) : co22 u = u.2.2 := rfl

/-! ## The bilinear form -/

/-- The dot product of `PS = ℝ⁴` as a continuous bilinear form. -/
def dotB : PS →L[ℝ] PS →L[ℝ] ℝ :=
  co11.smulRight co11 + co12.smulRight co12 + co21.smulRight co21 + co22.smulRight co22

@[simp] theorem dotB_apply (u v : PS) : dotB u v = dot u v := by
  simp [dotB, dot_apply, ContinuousLinearMap.smulRight_apply]

theorem dotB_comm (u v : PS) : dotB u v = dotB v u := by
  rw [dotB_apply, dotB_apply, dot_comm]

theorem dotB_exists :
    ∃ B : Work.RPV.PS →L[ℝ] Work.RPV.PS →L[ℝ] ℝ,
      (∀ u v, B u v = Work.RPCore.GenFun.dot u v) ∧ (∀ u v, B u v = B v u) :=
  ⟨dotB, fun u v => dotB_apply u v, fun u v => dotB_comm u v⟩

end Work.RPCore.GenFun
