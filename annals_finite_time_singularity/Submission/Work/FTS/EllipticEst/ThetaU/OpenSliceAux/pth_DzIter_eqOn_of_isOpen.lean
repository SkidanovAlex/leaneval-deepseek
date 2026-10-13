/-
# `∂_θ` commutes with `D_z^j` on an arbitrary open set

For any *open* set `V ⊆ ℝ × ℝ` on which the (uncurried) profile `g` is `C^n` for every `n`
(equivalently, smooth in the genuine sense `Work.Stability.smoothOrder = ∞`), the plain
angular derivative `∂_θ` commutes with every iterate of the curvilinear radial derivative
`D_z = z∂_z`:

`∂_θ (D_z^j g) = D_z^j (∂_θ g)` on `V`.

This is the *general open set* form (in the `C^∞` rather than the analytic class) of the
Clairaut identity used throughout the localisation chapter; the sibling module
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceAux/DthIter_DzIter_eqOn_of_isOpen.lean`
proves the corresponding statement for `D_θ = sin(2θ)∂_θ`, from which this one cannot be
derived directly (the factor `sin 2θ` vanishes at the angular boundary).

The proof is a plain induction on `j`.  At a point `y ∈ V` the function `D_z^j g` is `C²`
(by `C^∞`-regularity, `contDiffOn_DzIter`), so Clairaut
(`Work.Spaces.pz_pth_comm`, packaged as `pth_Dz_eq_of_contDiffAt_two` for the operator
`D_z = z ∂_z`) moves the `∂_θ` across one `D_z`.  What remains is a comparison of two
functions agreeing on the open set `V` by the induction hypothesis, which is legitimate
because `deriv` is local: `Work.Spaces.pz_congr_of_isOpen`.

All of this rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
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

/-- Pointwise Clairaut for `∂_θ` and `D_z = z ∂_z`: at a point where the uncurried `f` is `C²`,
`∂_θ (z ∂_z f) = z ∂_z (∂_θ f)`.  (Both sides are `z · ∂_θ∂_z f`; the `θ`-derivative of the
`z`-partial is the `z`-partial of the `θ`-derivative by `Work.Spaces.pz_pth_comm`, and the
factor `z` may be pulled out of the `θ`-derivative by `deriv_const_mul_field`.) -/
private lemma pth_Dz_eq_of_contDiffAt_two {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := rfl
  rw [h1, h2, (Work.Spaces.pz_pth_comm h).symm]

theorem pth_DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j g)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth g))) V := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V :=
    contDiffOn_infty.mpr hg
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      -- `D_z^j g` is still `C^∞` on `V`, hence `C²` at `y`: Clairaut applies there.
      have hgj : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j g)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV hsm j
      intro y hy
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j g)) y :=
        (hgj.contDiffAt (hV.mem_nhds hy)).of_le (by simp)
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j g)) y.1 y.2 :=
        pth_Dz_eq_of_contDiffAt_two hcd
      show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth g)) y.1 y.2
      rw [hstep]
      -- the two functions agree on the open set `V`, so their `z`-partials agree at `y`.
      show y.1 * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter j g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

end Work.FTS.EllipticEst.ThetaU.OpenSliceAux
