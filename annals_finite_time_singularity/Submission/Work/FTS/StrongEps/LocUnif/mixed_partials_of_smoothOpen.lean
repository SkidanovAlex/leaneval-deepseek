import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Blocks.DivSinHalfCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {F : ℝ → ℝ → ℝ}

/-! ## Elementary angular facts -/

theorem sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_ne_zero_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_Q0 hθ)

/-! ## (1) `∂_z (D_z^j D_θ^i F) = D_z^{j+1}D_θ^i F / z`

This is nothing but the defining recursion `D_z^{j+1} = z ∂_z ∘ D_z^j`, divided by `z`
(which is non-zero on the open quadrant). -/

theorem pz_mixed_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed (j + 1) i F z θ / z := by
  intro z θ h
  obtain ⟨hz, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hdef : Work.Spaces.mixed (j + 1) i F z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ := rfl
  rw [hdef, mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-! ## (2) `∂_θ (D_z^j D_θ^i F) = D_z^j D_θ^{i+1} F / sin 2θ`

`D_θ^{i+1} = sin 2θ · ∂_θ ∘ D_θ^i`, so this is `∂_θ` commuted with the iterates of `D_z`
(`Dth_DzIter_comm_eqOn`), divided by `sin 2θ` (non-zero on `(0, π/2)`). -/

theorem pth_mixed_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hs : Real.sin (2 * θ) ≠ 0 := sin_two_ne_zero_Q0 ⟨hθ0, hθ1⟩
  have hcomm := Work.Blocks.DivSinHalf.Dth_DzIter_comm_eqOn
    Work.FTS.EllipticEst.isOpen_Q0 (hF.DthIter i) j h
  have h23 : Work.Spaces.mixed j (i + 1) F z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i F) z θ := by
    have h3 : Work.Spaces.mixed j (i + 1) F z θ
        = Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i F)) z θ := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Function.uncurry] using hcomm.symm
    rw [h3]
    rfl
  rw [h23, mul_div_cancel_left₀ _ hs]

/-! ## (3) `∂_z (D_z^{j+1}D_θ^i F / z) = (D_z^{j+2}D_θ^i F - D_z^{j+1}D_θ^i F) / z²`

The quotient rule in `z`, with `∂_z` of the numerator evaluated by (1). -/

theorem pz_mixed_div_div (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = (Work.Spaces.mixed (j + 2) i F z θ - Work.Spaces.mixed (j + 1) i F z θ) / z ^ 2 := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hz' : z ≠ 0 := ne_of_gt hz
  have hd : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed (j + 1) i F) z θ) z :=
    (hF.mixed (j + 1) i).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz
  have hkey : deriv (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ / z') z
      = (Work.Spaces.pz (Work.Spaces.mixed (j + 1) i F) z θ * z
          - Work.Spaces.mixed (j + 1) i F z θ * 1) / z ^ 2 :=
    (hd.div (hasDerivAt_id' z) hz').deriv
  show deriv (fun z' : ℝ => Work.Spaces.mixed (j + 1) i F z' θ / z') z = _
  rw [hkey, pz_mixed_div (j + 1) i hF z θ h,
    show (j + 1) + 1 = j + 2 from by omega, div_mul_cancel₀ _ hz', mul_one]

/-! ## (4) `∂_z (D_z^j D_θ^{i+1} F / sin 2θ) = D_z^{j+1}D_θ^{i+1} F / (z sin 2θ)`

Here the angular factor `sin 2θ` is a constant as far as `∂_z` is concerned. -/

theorem pz_mixed_angdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ)) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hkey : deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ / Real.sin (2 * θ)) z
      = deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ) z / Real.sin (2 * θ) :=
    deriv_div_const _
  show deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ / Real.sin (2 * θ)) z = _
  rw [hkey, show deriv (fun z' : ℝ => Work.Spaces.mixed j (i + 1) F z' θ) z
      = Work.Spaces.pz (Work.Spaces.mixed j (i + 1) F) z θ from rfl,
    pz_mixed_div j (i + 1) hF z θ h, div_div]

/-! ## (5) `∂_θ (D_z^{j+1}D_θ^i F / z) = D_z^{j+1}D_θ^{i+1} F / (z sin 2θ)`

The radial factor `z` is a constant as far as `∂_θ` is concerned; (2) evaluates the
numerator. -/

theorem pth_mixed_zdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ)) := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hkey : deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ' / z) θ
      = deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ') θ / z :=
    deriv_div_const z
  show deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ' / z) θ = _
  rw [hkey, show deriv (fun θ' : ℝ => Work.Spaces.mixed (j + 1) i F z θ') θ
      = Work.Spaces.pth (Work.Spaces.mixed (j + 1) i F) z θ from rfl,
    pth_mixed_div (j + 1) i hF z θ h, div_div, mul_comm (Real.sin (2 * θ)) z]

/-! ## (6) `∂_θ (D_z^j D_θ^{i+1} F / sin 2θ) = D_z^j D_θ^{i+2} F / sin²2θ
  - 2cos 2θ · D_z^j D_θ^{i+1} F / sin²2θ`

The quotient rule in `θ`, with `(sin 2θ)' = 2 cos 2θ` and (2) evaluating the numerator. -/

theorem pth_mixed_angdiv (j i : ℕ) (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ
              / (Real.sin (2 * θ)) ^ 2 := by
  intro z θ h
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have hs : Real.sin (2 * θ) ≠ 0 := sin_two_ne_zero_Q0 ⟨hθ0, hθ1⟩
  have hds : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have h3 : HasDerivAt (Real.sin ∘ (fun y : ℝ => 2 * y)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    have h4 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
      simpa only [Function.comp_def] using h3
    exact h4.congr_deriv (by ring)
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ :=
    (((hF.mixed j (i + 1)).curry_θ hz).differentiableOn
        (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)
  have hkey : deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ' / Real.sin (2 * θ')) θ
      = (deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ * Real.sin (2 * θ)
          - Work.Spaces.mixed j (i + 1) F z θ
              * deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) / (Real.sin (2 * θ)) ^ 2 :=
    deriv_div hdθ hds.differentiableAt hs
  show deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ' / Real.sin (2 * θ')) θ = _
  rw [hkey, show deriv (fun θ' : ℝ => Work.Spaces.mixed j (i + 1) F z θ') θ
      = Work.Spaces.pth (Work.Spaces.mixed j (i + 1) F) z θ from rfl,
    hds.deriv, pth_mixed_div j (i + 1) hF z θ h,
    show (i + 1) + 1 = i + 2 from by omega]
  rw [div_mul_cancel₀ _ hs, ← sub_div]
  congr 1
  ring

/-! ## The six identities, assembled. -/

theorem mixed_partials_of_smoothOpen (j i : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.mixed j i F) z θ = Work.Spaces.mixed (j + 1) i F z θ / z) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.mixed j i F) z θ
        = Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ)) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = (Work.Spaces.mixed (j + 2) i F z θ - Work.Spaces.mixed (j + 1) i F z θ) / z ^ 2) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ
        = Work.Spaces.mixed (j + 1) (i + 1) F z θ / (z * Real.sin (2 * θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ
        = Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ / (Real.sin (2 * θ)) ^ 2) := by
  exact ⟨pz_mixed_div j i hF, pth_mixed_div j i hF, pz_mixed_div_div j i hF,
    pz_mixed_angdiv j i hF, pth_mixed_zdiv j i hF, pth_mixed_angdiv j i hF⟩

end Work.FTS.StrongEps.LocUnif
