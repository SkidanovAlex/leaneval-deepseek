import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FM.Core2
import Submission.Work.FTS.OpenPkg.C4Factors

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxFK

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## `FK g` is `C^∞` on the open quadrant

The angular moment `FK g z = ∫_θ K(θ)·g z θ dθ` is, on `z > 0`, the derivative of the radial
function `L₁₂(g)`:

  `∂_z L₁₂(g)(z) = - FK g z / z`   (`Work.FTS.OpenPkg.deriv_L12_eq`),

i.e. `FK g z = - z · ∂_z L₁₂(g)(z)`.  The hypothesis that `Vop (PhiTg α g Φg)` is `SmoothOpen`
gives (`Work.FTS.NonlinRows.smoothOpen_L12_radial`, via the identity
`Vop (PhiTil α g Φg) = Vop Φg - (1/(2α)) c₂(θ) L₁₂(g)(z)` and the non-degeneracy
`c₂(π/4) = -1/2`) that `z ↦ L₁₂(g)(z)` is `C^∞` on `(0,∞)`.  Being `C^∞` on `(0,∞)`, that
function is `C^{n+1}` for every `n`, hence its `deriv` is `C^n`, so `z ↦ -z·∂_z L₁₂(g)(z)` is
`C^∞` on `(0,∞)`, and `smoothOpen_radial` promotes it to the open quadrant. -/

/-- **The radial function `FK g` is `C^∞` on the open quadrant.**

*Step 1.* `Work.FTS.NonlinRows.smoothOpen_L12_radial` gives `SmoothOpen (fun z _ => L₁₂(g) z)`,
so the radial slice `z ↦ L₁₂(g)(z)` is `C^∞` on `(0,∞)`, hence `C^n` there for every `n`.

*Step 2.* `contDiffOn_succ_iff_deriv_of_isOpen` extracts, at every finite order `n`, that
`deriv (fun z => L₁₂(g) z)` is `C^n` on `(0,∞)`.

*Step 3.* `z ↦ -(z · deriv (L₁₂ g) z)` is therefore `C^n` for every `n`, so `SmoothOpen` by
`Work.FTS.NonlinRows.smoothOpen_radial`.

*Step 4.* Off the null set `z = 0`, `deriv_L12_eq` identifies this with `FK g`, and the two
functions agree on the open quadrant `Q0` (where `z > 0`). -/
theorem smoothOpen_FK_radial {α : ℝ} {g Φg : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) := by
  -- Step 1: `L₁₂(g)` is `C^∞` on the open quadrant, read off from `Vop (PhiTg α g Φg)`.
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
  -- Step 2: and so is its derivative, at every finite order
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
  -- Step 3: `z ↦ -z·∂_z L₁₂(g)(z)` is `C^∞` on the quadrant
  have hRn : ∀ n : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun z => -(z * deriv (fun z' => Work.Construction.L12 g z') z)) (Set.Ioi 0) := by
    intro n
    have hid : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => z) (Set.Ioi 0) :=
      contDiff_id.contDiffOn
    exact (hid.mul (hdN n)).neg
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => -(z * deriv (fun z' => Work.Construction.L12 g z') z)) :=
    Work.FTS.NonlinRows.smoothOpen_radial hRn
  -- Step 4: on the quadrant, `FK g z = -z·∂_z L₁₂(g)(z)`
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  simp only [Function.uncurry]
  rw [Work.FTS.OpenPkg.deriv_L12_eq hα hα1 hsm hmem h0 hz]
  field_simp

end Work.FTS.NonlinRows.AuxFK
