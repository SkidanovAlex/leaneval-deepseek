import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

theorem sb0_psiFieldAdd {f g : ℝ → ℝ → ℝ} {x : Work.Cyl.R3}
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hg : DifferentiableAt ℝ (fun p : ℝ × ℝ => g p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    Work.Cyl.psiField (fun r z => f r z + g r z) x = Work.Cyl.psiField f x + Work.Cyl.psiField g x := by
  -- the two slices of `f` and `g` at `(r, z) = (radial x, axial x)`
  have hfz : DifferentiableAt ℝ (fun z' : ℝ => f (Work.Cyl.radial x) z') (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_slice_snd f _ _ hf
  have hgz : DifferentiableAt ℝ (fun z' : ℝ => g (Work.Cyl.radial x) z') (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_slice_snd g _ _ hg
  have hfr : DifferentiableAt ℝ (fun r' : ℝ => f r' (Work.Cyl.axial x)) (Work.Cyl.radial x) :=
    Work.Cyl.differentiableAt_slice_fst f _ _ hf
  have hgr : DifferentiableAt ℝ (fun r' : ℝ => g r' (Work.Cyl.axial x)) (Work.Cyl.radial x) :=
    Work.Cyl.differentiableAt_slice_fst g _ _ hg
  -- additivity of the two partial derivatives at that point
  have hpz : Work.Cyl.pdZ (fun r z => f r z + g r z) (Work.Cyl.radial x) (Work.Cyl.axial x)
      = Work.Cyl.pdZ f (Work.Cyl.radial x) (Work.Cyl.axial x)
        + Work.Cyl.pdZ g (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    unfold Work.Cyl.pdZ
    exact deriv_add hfz hgz
  have hpr : Work.Cyl.pdR (fun r z => f r z + g r z) (Work.Cyl.radial x) (Work.Cyl.axial x)
      = Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x)
        + Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    unfold Work.Cyl.pdR
    exact deriv_add hfr hgr
  -- `psiField = cylField (∂_zψ) (-ψ/r - ∂_rψ)`, and `cylField` acts pointwise
  simp only [Work.Cyl.psiField, Work.Cyl.cylField, hpz, hpr]
  rw [add_div, add_smul,
    show -((f (Work.Cyl.radial x) (Work.Cyl.axial x)
            + g (Work.Cyl.radial x) (Work.Cyl.axial x)) / Work.Cyl.radial x)
        - (Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x)
           + Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x))
      = (-(f (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          - Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x))
        + (-(g (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          - Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x)) from by
      rw [add_div]; ring]
  rw [add_smul]
  abel

end Work.FTS_StreamBdry.SB0
