import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.OpenPkg.C4Factors

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

theorem smoothOpen_FK_radial {α : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) := by
  -- `L₁₂(g)` is `C^∞` on the open quadrant, by the delivered `smoothOpen_L12_radial`
  -- (read off from the hypothesis that `Vop (PhiTg α g Φg)` is smooth).
  have hL12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hΦg hV
  -- hence its radial slice `z ↦ L₁₂(g)(z)` is `C^∞` on `(0,∞)`
  have hθ₀ : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := hL12.curry_z hθ₀
  have hsliceN : ∀ m : ℕ, ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := fun m =>
    (contDiffOn_infty.mp (by simpa only [Work.Stability.smoothOrder] using hslice)) m
  -- and so is its derivative, at every finite order
  have hdN : ∀ n : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun z => deriv (fun z' => Work.Construction.L12 g z') z) (Set.Ioi 0) := by
    intro n
    have h1 : ContDiffOn ℝ (((n : ℕ) : WithTop ℕ∞) + 1)
        (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := by
      have := hsliceN (n + 1)
      simpa using this
    exact ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (n := ((n : ℕ) : WithTop ℕ∞)) (f := fun z => Work.Construction.L12 g z)
      (s := Set.Ioi 0) isOpen_Ioi).mp h1).2.2
  have hRn : ∀ n : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun z => -(z * deriv (fun z' => Work.Construction.L12 g z') z)) (Set.Ioi 0) := by
    intro n
    have hid : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => z) (Set.Ioi 0) :=
      contDiff_id.contDiffOn
    exact (hid.mul (hdN n)).neg
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => -(z * deriv (fun z' => Work.Construction.L12 g z') z)) :=
    Work.FTS.NonlinRows.smoothOpen_radial hRn
  -- on the quadrant, `FK g z = -z·∂_z L₁₂(g)(z)`
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  simp only [Function.uncurry]
  rw [Work.FTS.OpenPkg.deriv_L12_eq hα hα1 hsm hmem h0 hz]
  field_simp

end Work.FTS.Nonlinear.Open
