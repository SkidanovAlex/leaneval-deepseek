import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IsOdd` from reflection antisymmetry for axisymmetric no-swirl fields

This module proves `Work.Cyl.isOdd_of_reflZ_invariant`: for an axisymmetric field without swirl
`u = u_r(r,x₃) e_r + u_z(r,x₃) e_z`, the single reflection identity

  `u (reflZ x) = flipZ (u x)`  (i.e. `u(x₀,x₁,-x₃) = (u₀,u₁,-u₂)(x₀,x₁,x₃)`)

already forces the full oddness `FiniteTimeSingularity.IsOdd u`, i.e. that each component `uᵢ` is
odd in the coordinate `i` and even in the two others.

The mechanism is exactly the parity asymmetry of `cylField` (compare
`Work.Cyl.isOdd_cylField`): reflection in the axial coordinate only touches the profiles through
`x₃ ↦ -x₃`, so the third component of the reflection identity reads

  `u_z(r,-x₃) = -u_z(r,x₃)`   (all `r ≥ 0`, including the axis),

while the first component, evaluated at `(r,0,x₃)` with `r > 0`, reads

  `u_r(r,-x₃) = u_r(r,x₃)`   (all `r > 0`).

Reflections in the two *transverse* coordinates `x₀`, `x₁` are free: they leave both `r²` and `x₃`
unchanged and only flip the prefactor `x₀` (resp. `x₁`), which is exactly the parity required of
the first (resp. second) component.

Self-contained: only `Coords`, `Frame`, `Basic` (and Mathlib) are used, so this lemma is available
independently of the `IsOdd`-characterization lemmas proved elsewhere in `Work.Cyl`.
-/

namespace Work.Cyl

/-! ### Coordinate computations for the vectors `!₂[a,b,c]` -/

private lemma cons_zero (a b c : ℝ) : (!₂[a, b, c] : R3) 0 = a := by simp

private lemma radial_cons (a b c : ℝ) : radial (!₂[a, b, c] : R3) = Real.sqrt (a ^ 2 + b ^ 2) := by
  simp [radial, radSq]

private lemma axial_cons (a b c : ℝ) : axial (!₂[a, b, c] : R3) = c := by simp [axial]

private lemma reflZ_cons (a b c : ℝ) : reflZ (!₂[a, b, c] : R3) = !₂[a, b, -c] := by
  refine ext_coord ?_ ?_ ?_ <;> simp [reflZ]

/-- On the ray `r ≥ 0` the radial coordinate of `(r, 0, z)` is `r` itself. -/
private lemma radial_axis {r : ℝ} (hr : 0 ≤ r) (z : ℝ) : radial (!₂[r, 0, z] : R3) = r := by
  rw [radial_cons, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hr]

/-! ### The two nontrivial components of `flipZ` -/

private lemma flipZ_zero (v : R3) : (flipZ v) 0 = v 0 := by simp [flipZ]

private lemma flipZ_two (v : R3) : (flipZ v) 2 = - v 2 := by simp [flipZ]

theorem isOdd_of_reflZ_invariant (u : Work.Cyl.R3 → Work.Cyl.R3) (hax : Work.Cyl.IsAxiNoSwirl u)
    (hrefl : ∀ x, u (Work.Cyl.reflZ x) = Work.Cyl.flipZ (u x)) :
    FiniteTimeSingularity.IsOdd u := by
  obtain ⟨ur, uz, rfl⟩ := hax
  -- The axial reflection identity, read on the ray `(r,0,z)`: `u_z` is odd in `x₃`, `r ≥ 0`.
  have hodd : OddZnn uz := by
    intro r hr z
    have h := congrArg (fun v : R3 => v 2) (hrefl (!₂[r, 0, z] : R3))
    rw [reflZ_cons, cylField_two, flipZ_two] at h
    rw [cylField_two, radial_axis hr (-z), radial_axis hr z, axial_cons, axial_cons] at h
    exact h
  -- Its first component, read on `(r,0,z)` with `r > 0`: `u_r` is even in `x₃`, `r > 0`.
  have heven : ∀ r, 0 < r → ∀ z, ur r (-z) = ur r z := by
    intro r hr z
    have h := congrArg (fun v : R3 => v 0) (hrefl (!₂[r, 0, z] : R3))
    rw [reflZ_cons, cylField_zero, flipZ_zero] at h
    rw [cylField_zero, radial_axis hr.le (-z), radial_axis hr.le z, axial_cons, axial_cons] at h
    rw [cons_zero, cons_zero, mul_div_cancel_right₀ _ hr.ne', mul_div_cancel_right₀ _ hr.ne'] at h
    exact h
  -- Now assemble `IsOdd`: the transverse reflections are parity-free, the axial one uses the two
  -- profile parities just established (note the asymmetry `r > 0` for `u_r`, `r ≥ 0` for `u_z`).
  refine ⟨?_, ?_, ?_⟩
  · -- reflection in the first coordinate
    intro x₁ x₂
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero, neg_sq]
      ring
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero,
        neg_sq]
    · intro t
      simp only [cylField_two, radial_cons, axial_cons, neg_sq]
  · -- reflection in the second coordinate
    intro x₀ x₂
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero, neg_sq]
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero,
        neg_sq]
      ring
    · intro t
      simp only [cylField_two, radial_cons, axial_cons, neg_sq]
  · -- reflection in the axial coordinate
    intro x₀ x₁
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero]
      by_cases hx : x₀ = 0
      · simp [hx]
      · have hρ : 0 < Real.sqrt (x₀ ^ 2 + x₁ ^ 2) :=
          Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hx, sq_nonneg x₁])
        rw [heven _ hρ t]
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
      by_cases hx : x₁ = 0
      · simp [hx]
      · have hρ : 0 < Real.sqrt (x₀ ^ 2 + x₁ ^ 2) :=
          Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hx, sq_nonneg x₀])
        rw [heven _ hρ t]
    · intro t
      simp only [cylField_two, radial_cons, axial_cons]
      exact hodd _ (Real.sqrt_nonneg _) t

end Work.Cyl
