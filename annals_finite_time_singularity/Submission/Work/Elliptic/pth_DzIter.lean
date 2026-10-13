import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pth` commutes with the iterates of `D_z`

For a function `Φ` that is smooth on an open neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd Φ`) the plain angular derivative `pth = ∂_θ` commutes with
every iterate of `D_z = z ∂_z` on that neighbourhood:

  `∂_θ (D_z^j Φ) = D_z^j (∂_θ Φ)`  on `Iz × Iθ`.

The point is that `∂_θ` commutes with multiplication by the radial variable `z` (the
factor `z` does not depend on `θ`) and with `∂_z` (Clairaut/Schwarz, available because
`Φ` is `C^∞` on an open neighbourhood of the quadrant).  The iteration is organized as
an equality on the open set `nbhU`, where both sides are honest derivatives, because the
inductive step needs to differentiate the two sides with respect to `z` (`pz_congr`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

/-- One step of the commutation: at a point of the neighbourhood where `g` is smooth,
`∂_θ (D_z g) = D_z (∂_θ g)`. -/
lemma pth_Dz_apply {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ} (hy : y ∈ Work.Spaces.nbhU)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry g) y :=
    (ContDiffOn.contDiffAt hg (Work.Spaces.isOpen_nbhU.mem_nhds hy)).of_le (by norm_num)
  -- `∂_θ (z · ∂_z g) = z · ∂_θ ∂_z g`
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  -- Clairaut: `∂_θ ∂_z g = ∂_z ∂_θ g`
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) h2).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

/-- On `nbhU` the angular derivative of the `j`-th `D_z`-iterate of `Φ` is the
`j`-th `D_z`-iterate of its angular derivative. -/
lemma pth_DzIter_eqOn (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) Work.Spaces.nbhU := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j Φ) :=
      Work.Spaces.SmoothNbhd.DzIter hΦ j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y :=
      pth_Dz_apply hy hs
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) y :=
      Work.Spaces.Dz_congr ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) Φ)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)) y
    rw [show Work.Spaces.DzIter (j+1) Φ = Work.Spaces.Dz (Work.Spaces.DzIter j Φ) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) from rfl]
    exact hstep.trans hcongr

theorem pth_DzIter (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ) (j : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ :=
  pth_DzIter_eqOn Φ hΦ j (Work.Spaces.mem_nbhU hz hθ)

end Work.Elliptic
