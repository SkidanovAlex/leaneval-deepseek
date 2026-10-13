import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.PhiStar.ZeroOffWitness
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Real

namespace Work.FTS_FinalLeaves.SolFire

/-! ## The two pointwise facts about the firing stream function

`psiFire Φs E g` is the odd extension in `θ` of the cut `PsiCan Φs E g`; on the branch
`θ > 0` it *is* the canonical stream function, and at `θ = 0` it vanishes (the cut). -/

/-- `psiFire` agrees with the canonical stream function on the branch `θ > 0`
(restated here so that it can be used without re-importing the `FinalV2` development). -/
theorem slice_psiFire_of_pos {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.FTS.FinalV2.psiFire Φs E g z θ τ = Work.FTS.Nonlin.PsiCan Φs E g z θ τ :=
  Work.FTS.FinalV2.psiFire_of_pos hθ

/-- `psiFire` vanishes on the axis `θ = 0`, for every `z` and every `τ`. -/
theorem slice_psiFire_zero {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (z τ : ℝ) :
    Work.FTS.FinalV2.psiFire Φs E g z 0 τ = 0 := by
  simp only [Work.FTS.FinalV2.psiFire, Work.FTS.BSIdent.PhiOdd, Work.FTS.FinalV2.psiCut,
    le_refl, ite_true]
  simp

/-- `extG` agrees with `g` at every `z > 0` and `τ ≥ 0`, whence the same for `Ftau`. -/
theorem Ftau_extG_of_pos {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Ftau α (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.Construction.Ftau α g τ z θ := by
  simp only [Work.Construction.Ftau, Work.FTS.RegPkgGal.extG_of_pos hz hτ]

theorem isBslSolPos_psiFire_extG {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hτ : 0 ≤ τ)
    (h : Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) :
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α (Work.FTS.RegPkgGal.extG g) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ) := by
  obtain ⟨heq, h0, h1, hdec⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the equation on the open quadrant: `psiFire = PsiCan` there and `extG = g` at `z > 0`
    intro z hz θ hθ hθ2
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
    rw [Work.FTS.PhiStar.bslOp_congr α
      (Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) hmem
      (fun z' θ' h' => by
        obtain ⟨-, hθ', -⟩ := (Work.FTS.EllipticEst.mem_Q0).mp h'
        exact slice_psiFire_of_pos hθ')]
    rw [heq z hz θ hθ hθ2]
    exact (Ftau_extG_of_pos hτ hz).symm
  · -- the Dirichlet condition at `θ = 0`: the cut kills the value
    intro z _
    exact slice_psiFire_zero z τ
  · -- the Dirichlet condition at `θ = π/2`
    intro z hz
    have hpos : (0 : ℝ) < π / 2 := by positivity
    change Work.FTS.FinalV2.psiFire Φs E g z (π / 2) τ = 0
    rw [slice_psiFire_of_pos hpos]
    exact h1 z hz
  · -- decay in `z` at fixed `θ ∈ Iθ`
    intro θ hθ
    rw [Work.Spaces.Iθ] at hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0]
      have hconst : (fun z : ℝ => Work.FTS.Galerkin.slice
          (Work.FTS.FinalV2.psiFire Φs E g) τ z 0) = fun _ : ℝ => (0 : ℝ) := by
        funext z
        exact slice_psiFire_zero z τ
      rw [hconst]
      exact tendsto_const_nhds
    · have hev : (fun z : ℝ => Work.FTS.Galerkin.slice
            (Work.FTS.FinalV2.psiFire Φs E g) τ z θ)
          =ᶠ[atTop] (fun z : ℝ => Work.FTS.Galerkin.slice
            (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ) := by
        filter_upwards with z
        exact slice_psiFire_of_pos hθ0
      exact Filter.Tendsto.congr' hev.symm (hdec θ ⟨hθ.1, hθ.2⟩)

end Work.FTS_FinalLeaves.SolFire
