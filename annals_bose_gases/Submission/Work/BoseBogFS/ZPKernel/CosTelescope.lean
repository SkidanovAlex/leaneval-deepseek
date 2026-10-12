import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsL.LatticeCoulomb.latToolbox
import Submission.Work.BoseRowsL.LatticeCoulomb.latticeInvFourSum
import Submission.Work.BoseRowsL.LatticeCoulomb.telescopeCos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPKernel.CosTelescope`

The telescoping cosine bound for the truncated lattice sum `Σ_{0<‖n‖≤R} cos(2π⟪n,z⟫)/‖n‖²`:
the prefactor `1 − cos(2π z_j)` controls the sum, uniformly in the truncation radius `R`.

The mathematics is the *telescoping* (second-difference) cancellation exploited by the
sibling development `Submission/Work/BoseRowsL/LatticeCoulomb/`:

  `cos θ · (1 − cos φ) = cos θ − cos(θ+φ)/2 − cos(θ−φ)/2`,  `φ = 2π z_j`,  `θ = 2π⟪nvec n,z⟫`,

which turns the sum into `Σ_m telG T j m · cos(2π⟪nvec m,z⟫)` over the carrier
`telW T j = T ∪ (T+e_j) ∪ (T−e_j)`, where `telG T j` is the second difference of
`m ↦ 1_{m∈T}/‖nvec m‖²` along `e_j`.  That second difference is *absolutely* summable
(interior: `O(‖m‖⁻⁴)`; boundary: an `O(‖m‖⁻²)` shell of width one), whence
`Σ_{m∈telW T j} |telG T j m| ≤ 100`, and the conclusion follows since `|cos| ≤ 1`.

The stronger constant `100` is proved in the sibling module
`Work.BoseRowsL.LatticeCoulomb.telescopeCos` (with the *same* hypotheses `h1`, `h2`, `h4`);
the present statement with the very generous constant `100000000` is its immediate
consequence.  Note that the hypothesis `hz : ‖z‖ ≤ 1/2` is not needed: the bound is uniform
in `z` as well.
-/

namespace Work.BoseBogFS.ZPKernel

theorem CosTelescope (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3)
    (z : EuclideanSpace ℝ (Fin 3))
    (h1 : ∀ n ∈ T, n ≠ 0)
    (h2 : ∀ n ∈ T, ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R → n ∈ T)
    (hz : ‖z‖ ≤ 1 / 2) :
    (1 - Real.cos (2 * Real.pi * z.ofLp j))
      * |∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
          / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2| ≤ 100000000 := by
  have h := Work.BoseRowsL.LatticeCoulomb.telescopeCos R T j z h1 h2 h4
  linarith

end Work.BoseBogFS.ZPKernel
