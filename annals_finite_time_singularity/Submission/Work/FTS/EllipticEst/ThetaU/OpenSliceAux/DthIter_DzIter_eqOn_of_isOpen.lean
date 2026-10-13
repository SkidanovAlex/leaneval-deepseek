/-
# `D_θ^i` commutes with `D_z^j` on an arbitrary open set

For any *open* set `V ⊆ ℝ × ℝ` on which the (uncurried) profile `g` is `C^n` for every `n`
(equivalently, smooth in the genuine sense `Work.Stability.smoothOrder = ∞`), the iterated
curvilinear derivatives `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` commute on `V`:

`D_θ^i (D_z^j g) = D_z^j (D_θ^i g) = mixed j i g` on `V`.

This is the *general open set* form of
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` (stated for the open quadrant
`(0,∞) × (0,π/2)` and pointwise) and of `Work.Spaces.DthIter_DzIter_comm_eqOn` (stated for
the fixed corner set `nbhU`): the argument only ever uses that `V` is open (so that `deriv`
agrees with the honest derivative and derivatives may be compared locally) together with the
genuine `C^∞`-regularity of `g` on `V`, which here is supplied in the *finite-order* form
`∀ n : ℕ, ContDiffOn ℝ n (uncurry g) V` and converted by `contDiffOn_infty`.

The proof is the same as in `DthIter_DzIter_eq_mixed_open`: one `D_θ` may be moved across one
`D_z` by Clairaut (`Work.Spaces.Dz_Dth_comm`), and the two sides of the identity may be
compared at a point because they agree on the open set `V` containing it.

All of this rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.ThetaU.OpenSliceAux

/-- On an open set `V` on which `f` is `C^∞`, a single `D_θ` moves across any number of
iterates of `D_z`: `D_θ (D_z^j f) = D_z^j (D_θ f)` on `V`. -/
theorem Dth_DzIter_eqOn_of_smooth {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.Dth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      -- `D_z^j f` is still `C^∞` on `V`, hence `C²` at `y`: Clairaut applies there.
      have hfj : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j f)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV hf j
      intro y hy
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) y :=
        (hfj.contDiffAt (hV.mem_nhds hy)).of_le (by simp)
      have hstep : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter j f)) y.1 y.2 :=
        (Work.Spaces.Dz_Dth_comm hcd).symm
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dth f)) y.1 y.2
      rw [hstep]
      -- the two functions agree on the open set `V`, so their `z`-derivatives agree at `y`.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter j f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.Dth f)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

/-- **Commutation of the mixed curvilinear derivatives on an arbitrary open set.**  If the
uncurried profile `g` is `C^n` on the open set `V` for every `n` — i.e. genuinely smooth on
`V` — then `D_θ^i` and `D_z^j` commute on `V`, so that `D_θ^i (D_z^j g) = mixed j i g` there. -/
theorem DthIter_DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V :=
    contDiffOn_infty.mpr hg
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i g))) V := by
    induction i with
    | zero => intro y hy; rfl
    | succ i ih =>
        have hgi : ContDiffOn ℝ Work.Stability.smoothOrder
            (Function.uncurry (Work.Spaces.DthIter i g)) V :=
          Work.FTS.LocData.contDiffOn_DthIter hV hsm i
        intro y hy
        show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
            = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
        -- replace `D_θ^i (D_z^j g)` by `D_z^j (D_θ^i g)` inside the outer `D_θ`.
        have hcon : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
            = Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) y.1 y.2 := by
          show Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.DzIter j g)) y.1 y.2
              = Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) y.1 y.2
          rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]
        rw [hcon]
        exact Dth_DzIter_eqOn_of_smooth hV hgi j hy
  intro y hy
  exact hcomm hy

end Work.FTS.EllipticEst.ThetaU.OpenSliceAux
