import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.H2W

open scoped Real Topology
open Set Filter

/-- One step of the commutation of `∂_θ` with `D_z = z ∂_z`: at a point where `g` is `C²`,
`∂_θ (D_z g) = D_z (∂_θ g)`. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz g z θ') θ
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    (Work.Spaces.pz_pth_comm hg).symm
  rw [h1, h3]
  rfl

/-- `∂_θ` commutes with the iterates of `D_z` on the open quadrant: for `f` of class `C^∞`
on `(0,∞) × (0,π/2)` one has `∂_θ (D_z^j f) = D_z^j (∂_θ f)` there. -/
theorem pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) (z, θ) :=
        ((hf.DzIter j).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩))).of_le
          (by simp [Work.Stability.smoothOrder])
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ :=
        pth_Dz_apply hcd
      have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := by
        have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z' θ)
            =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, hθ'⟩)
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j + 1) f)) (z, θ)
          = Function.uncurry (Work.Spaces.DzIter (j + 1) (Work.Spaces.pth f)) (z, θ)
      simp only [Function.uncurry]
      rw [show Work.Spaces.DzIter (j + 1) f
            = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl, hstep, hcongr]
      rfl

/-- The second angular derivative `∂_θ²` commutes with the iterates of `D_z = z ∂_z` on the
open quadrant: for `f` of class `C^∞` on `(0,∞) × (0,π/2)`,
`∂_θ² (D_z^i f) = D_z^i (∂_θ² f)` there. -/
theorem pthIter2_DzIter_comm {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i f)))
      (Function.uncurry (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 f)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ'⟩
  have hL : Work.Spaces.pthIter 2 (Work.Spaces.DzIter i f)
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter i f)) := by
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  have hR : Work.Spaces.pthIter 2 f
      = Work.Spaces.pth (Work.Spaces.pth f) := by
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  have hstep1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter i f)) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter i (Work.Spaces.pth f)) z θ := by
    have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i f) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth f) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
      exact pth_DzIter_eqOn_Q0 hf i
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth f) z θ') θ
    rw [hev.deriv_eq]
  have hstep2 : Work.Spaces.pth (Work.Spaces.DzIter i (Work.Spaces.pth f)) z θ
      = Work.Spaces.DzIter i (Work.Spaces.pth (Work.Spaces.pth f)) z θ :=
    pth_DzIter_eqOn_Q0 hf.pth i (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)
  simp only [Function.uncurry]
  rw [hL, hR, hstep1, hstep2]

end Work.EllipticEst.H2W
