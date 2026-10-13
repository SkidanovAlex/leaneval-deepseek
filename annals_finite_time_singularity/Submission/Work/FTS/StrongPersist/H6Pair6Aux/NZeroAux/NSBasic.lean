import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.UopHk.EllResid_slice_data

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts -/

/-- `sin 2θ ≠ 0` on the open angular interval. -/
theorem nzs_s2_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have h : Work.Construction.s2 θ = Real.sin (2 * θ) := rfl
  rw [h]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- `∂_θ f = D_θf / sin 2θ` on the open angular interval. -/
theorem nzs_pth_eq_Dth_div {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth f z θ = Work.Spaces.Dth f z θ / Work.Construction.s2 θ := by
  have hs : Work.Construction.s2 θ ≠ 0 := nzs_s2_ne_zero hθ
  have hD : Work.Spaces.Dth f z θ
      = Work.Construction.s2 θ * Work.Spaces.pth f z θ := rfl
  rw [hD, eq_div_iff hs]
  ring

/-- **The exact shape of `N` used below.**  On the open quadrant, with
`Ξ = PhiTil α F Ψ`, `A₁ = ℛ(Ξ)`, `A₂ = U(Ξ)/sin 2θ`, `A₃ = V(Ξ)`, the nonlinear term reads

`N α F Ψ = 2 A₁ F − 2 A₂ D_θF − 2α A₃ D_zF − (1/2) (F,K) D_θF − sin²θ (F,K) F`. -/
theorem nzs_N_form (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Construction.N α F Ψ z θ
        = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ) z θ * F z θ
          - 2 * (Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ
              / Work.Construction.s2 θ) * Work.Spaces.Dth F z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
              * Work.Spaces.Dz F z θ
          - (1 / 2) * Work.Construction.FK F z * Work.Spaces.Dth F z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK F z * F z θ := by
  intro z θ hzθ
  obtain ⟨_hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hs : Work.Construction.s2 θ ≠ 0 := nzs_s2_ne_zero hθ
  have h1 : Work.Construction.N α F Ψ z θ
      = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ) z θ * F z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ
            * Work.Spaces.pth F z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
            * Work.Spaces.Dz F z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
            * Work.Spaces.pth F z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK F z * F z θ := rfl
  rw [h1, nzs_pth_eq_Dth_div (f := F) hθ]
  field_simp

/-! ## The straightened stream function and its first partials -/

/-- `∂_z(Φ̃)` in terms of `∂_zΨ` and `(L₁₂ F)'`. -/
theorem nzs_pz_PhiTil (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hg : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Work.Construction.s2 θ
            * deriv (fun z' => Work.Construction.L12 F z') z := by
  have hfun : Work.Construction.PhiTil α F Ψ
      = fun z' θ' => Ψ z' θ'
          - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z' := rfl
  rw [hfun, Work.Spaces.pz]
  rw [show (fun z' => Ψ z' θ - (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 F z')
      = (fun z' => Ψ z' θ)
        - (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z')
      from rfl,
    deriv_sub hΨ (hg.const_mul ((1 / (4 * α)) * Work.Construction.s2 θ))]
  rw [Work.Spaces.pz]
  have h2 : deriv (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 F z') z
      = ((1 / (4 * α)) * Work.Construction.s2 θ)
        * deriv (fun z' => Work.Construction.L12 F z') z := by
    rw [show (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z')
        = fun z' => (((1 / (4 * α)) * Work.Construction.s2 θ))
            * Work.Construction.L12 F z' from rfl]
    exact deriv_const_mul (((1 / (4 * α)) * Work.Construction.s2 θ)) hg
  rw [h2]

/-- `∂_θ(Φ̃)` in terms of `∂_θΨ` and `L₁₂ F`. -/
theorem nzs_pth_PhiTil (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pth Ψ z θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
  have hfun : Work.Construction.PhiTil α F Ψ
      = fun z' θ' => Ψ z' θ'
          - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z' := rfl
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hderiv : deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ
      = 2 * Real.cos (2 * θ) := by
    have h := Work.FTS.EllipticEst.UopHk.deriv_sin_two θ
    rw [show Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') from rfl]
    exact h
  have hd : DifferentiableAt ℝ (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
      * Work.Construction.L12 F z) θ :=
    (hs2.const_mul (1 / (4 * α))).mul_const (Work.Construction.L12 F z)
  rw [hfun, Work.Spaces.pth]
  rw [show (fun θ' => Ψ z θ'
        - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z)
      = (fun θ' => Ψ z θ')
        - (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z)
      from rfl,
    deriv_sub hΨ hd]
  rw [Work.Spaces.pth]
  have h2 : deriv (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
        * Work.Construction.L12 F z) θ
      = (1 / (4 * α)) * (deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ)
        * Work.Construction.L12 F z := by
    rw [show (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 F z)
        = fun θ' => (((1 / (4 * α)) * Work.Construction.s2 θ')
            * Work.Construction.L12 F z) from rfl]
    have h := deriv_mul_const (x := θ)
      (c := fun θ' : ℝ => (1 / (4 * α)) * Work.Construction.s2 θ')
      ((hs2.const_mul (1 / (4 * α)))) (Work.Construction.L12 F z)
    rw [h]
    have h3 : deriv (fun θ' : ℝ => (1 / (4 * α)) * Work.Construction.s2 θ') θ
        = (1 / (4 * α)) * deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ :=
      deriv_const_mul (1 / (4 * α)) hs2
    rw [h3]
  rw [h2, hderiv]



end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
