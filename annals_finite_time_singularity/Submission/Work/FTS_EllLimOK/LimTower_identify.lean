import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS_EllLimOK

/-! ## The definitional towers for `mixed`

`mixed (c+1) d X` is `Dz (mixed c d X)` definitionally, so its value at `(z,θ)` is
`z` times the `z`-derivative of the `θ`-slice of `mixed c d X`.  Likewise
`mixed 0 (d+1) X = Dth (mixed 0 d X)`, whose value is `sin(2θ)` times the
`θ`-derivative of the `z`-slice.  These two identities are pure unfolding, and they
are what turns the recurrence hypotheses on `F` into the identification with
`mixed c d (F 0 0)`. -/

theorem mixed_z_succ (X : ℝ → ℝ → ℝ) (c d : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (c + 1) d X z θ
      = z * deriv (fun z' => Work.Spaces.mixed c d X z' θ) z := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]

theorem mixed_th_succ (X : ℝ → ℝ → ℝ) (d : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 (d + 1) X z θ
      = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.mixed 0 d X z θ') θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dth, Work.Spaces.pth]

theorem LimTower_identify {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ := by
  -- The first-order identifications, from the two recurrence hypotheses at `(0,0)`.
  have one_z : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 1 0 z' θ' = Work.Spaces.mixed 1 0 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hd := (hdz 0 0 (by norm_num) z' θ' hz').deriv
    rw [Work.Spaces.mixed]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz]
    rw [hd, mul_comm z' (F 1 0 z' θ' / z'), div_mul_cancel₀ (F 1 0 z' θ') (ne_of_gt hzp)]
  have one_th : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 0 1 z' θ' = Work.Spaces.mixed 0 1 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hsin' : Real.sin (2 * θ') ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hd := (hdth 0 0 (by norm_num) z' θ' hz').deriv
    rw [Work.Spaces.mixed]
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero,
      Work.Spaces.Dth, Work.Spaces.pth]
    rw [hd, mul_comm (Real.sin (2 * θ')) (F 0 1 z' θ' / Real.sin (2 * θ')),
      div_mul_cancel₀ (F 0 1 z' θ') hsin']
  -- The second-order identifications, by transferring the slice derivative from `F` to
  -- `mixed` along the first-order identification (valid on the open quadrant, hence on a
  -- neighbourhood of the point).
  have two_z : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 2 0 z' θ' = Work.Spaces.mixed 2 0 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hev : (fun z'' => F 1 0 z'' θ') =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.mixed 1 0 (F 0 0) z'' θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hzp] with z'' hz''
      exact one_z z'' θ' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz'', hθ'0, hθ'1⟩)
    have hd : HasDerivAt (fun z'' => Work.Spaces.mixed 1 0 (F 0 0) z'' θ')
        (F 2 0 z' θ' / z') z' :=
      (hdz 1 0 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_z_succ (F 0 0) 1 0 z' θ', hd.deriv,
      mul_comm z' (F 2 0 z' θ' / z'), div_mul_cancel₀ (F 2 0 z' θ') (ne_of_gt hzp)]
  have one_one : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 1 1 z' θ' = Work.Spaces.mixed 1 1 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hev : (fun z'' => F 0 1 z'' θ') =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.mixed 0 1 (F 0 0) z'' θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hzp] with z'' hz''
      exact one_th z'' θ' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz'', hθ'0, hθ'1⟩)
    have hd : HasDerivAt (fun z'' => Work.Spaces.mixed 0 1 (F 0 0) z'' θ')
        (F 1 1 z' θ' / z') z' :=
      (hdz 0 1 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_z_succ (F 0 0) 0 1 z' θ', hd.deriv,
      mul_comm z' (F 1 1 z' θ' / z'), div_mul_cancel₀ (F 1 1 z' θ') (ne_of_gt hzp)]
  have two_th : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 0 2 z' θ' = Work.Spaces.mixed 0 2 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hsin' : Real.sin (2 * θ') ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hev : (fun θ'' => F 0 1 z' θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Work.Spaces.mixed 0 1 (F 0 0) z' θ'') := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ'0, hθ'1⟩] with θ'' hθ''
      exact one_th z' θ'' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzp, hθ''.1, hθ''.2⟩)
    have hd : HasDerivAt (fun θ'' => Work.Spaces.mixed 0 1 (F 0 0) z' θ'')
        (F 0 2 z' θ' / Real.sin (2 * θ')) θ' :=
      (hdth 0 1 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_th_succ (F 0 0) 1 z' θ', hd.deriv,
      mul_comm (Real.sin (2 * θ')) (F 0 2 z' θ' / Real.sin (2 * θ')),
      div_mul_cancel₀ (F 0 2 z' θ') hsin']
  -- Since `c + d ≤ 2`, both `c,d ≤ 2`; dispatch on the (at most six) possibilities.
  intro c d hcd z θ hzθ
  have hc2 : c ≤ 2 := by omega
  have hd2 : d ≤ 2 := by omega
  interval_cases c <;> interval_cases d <;> first
    | exact one_z z θ hzθ
    | exact one_th z θ hzθ
    | exact one_one z θ hzθ
    | exact two_z z θ hzθ
    | exact two_th z θ hzθ
    | rfl
    | omega

end Work.FTS_EllLimOK
