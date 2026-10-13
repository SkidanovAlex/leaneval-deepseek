import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Regularity of the slice operator `Lzero1`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` on the open interval `(0, π/2)`
(`Work.FTS.EllipticEst.Lzero1`).  Since `θ ↦ tan θ` is smooth on `(0, π/2)` (the cosine
never vanishes there) and `deriv` loses exactly one order of differentiability on an open
set, `Lzero1` loses two orders:

`ContDiffOn ℝ (m + 2) u s → ContDiffOn ℝ m (Lzero1 u) s`,  `s = (0, π/2)`.

The only Mathlib ingredient that is not available off the shelf is smoothness of `Real.tan`
on `(0, π/2)` (Mathlib has it only pointwise, `Real.contDiffAt_tan`); we record it first,
since it is useful in its own right for every slicewise computation in this chapter.
-/

namespace Work.FTS.EllipticEst.remov.SliceTopAux

/-- `Real.tan` is `C^n` on the open interval `(0, π/2)`: the cosine does not vanish there. -/
theorem contDiffOn_tan_Ioo (n : WithTop ℕ∞) :
    ContDiffOn ℝ n Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  exact (Real.contDiffAt_tan.mpr (ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))).contDiffWithinAt

theorem contDiffOnLzero1 (m : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (m + 2) u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ m (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hs : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  -- `tan · u` is `C^{m+2}`
  have htu : ContDiffOn ℝ (m + 2) (fun θ => Real.tan θ * u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_tan_Ioo (m + 2)).mul hu
  -- one `deriv` on `deriv u` and one on `tan · u`
  have hdu : ContDiffOn ℝ (m + 1) (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen hs (le_of_eq rfl)
  have hd2 : ContDiffOn ℝ m (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdu.deriv_of_isOpen hs le_rfl
  have hd1 : ContDiffOn ℝ (m + 1) (deriv (fun θ => Real.tan θ * u θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    htu.deriv_of_isOpen hs (le_of_eq rfl)
  have hA : ContDiffOn ℝ m (fun θ => -(deriv (fun t => deriv u t) θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    hd2.neg
  have hB : ContDiffOn ℝ m (fun θ => deriv (fun t => Real.tan t * u t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.of_le le_self_add
  have hC : ContDiffOn ℝ m (fun θ => (6 : ℝ) * u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.mul (hu.of_le le_self_add)
  show ContDiffOn ℝ m (fun θ => -(deriv (fun t => deriv u t) θ)
      + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) (Set.Ioo 0 (Real.pi / 2))
  exact (hA.add hB).sub hC

end Work.FTS.EllipticEst.remov.SliceTopAux
