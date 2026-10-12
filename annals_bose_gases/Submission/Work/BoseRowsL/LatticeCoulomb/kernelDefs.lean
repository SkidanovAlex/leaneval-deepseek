import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.kernelDefs`

Auxiliary vocabulary for the proof of `Work.BoseRowsL.LatticeCoulomb.latticeKernel_bound`.

The proof compares the lattice sum `Σ_{0<‖n‖≤R} cos(2π⟪n,z⟫)/‖n‖²` with the ball integral
`∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖²` by the *cell* method: the unit cube `ucell n` centred at the
lattice point `n` has

  `∫_{q ∈ ucell n} cos (2π⟪q,z⟫) dq = sigma z * cos (2π⟪nvec n,z⟫)`,
  `sigma z := ∫_{q ∈ ucell 0} cos (2π⟪q,z⟫) dq`,

because the "odd" part `∫_{ucell 0} sin (2π⟪q,z⟫) dq` vanishes (the cube is symmetric).  The
first moment `sigBullet z := ∫_{ucell 0} sin (2π⟪q,z⟫) • q dq` and the vector `sinVec z` collect
the linear correction.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The cell average of the cosine: `sigma z = ∫_{q ∈ ucell 0} cos (2π⟪q,z⟫) dq`. -/
noncomputable def sigma (z : E3) : ℝ := ∫ q in ucell 0, Real.cos (2 * Real.pi * inner ℝ q z)

/-- The sine-weighted first moment of the unit cube:
`sigBullet z = ∫_{q ∈ ucell 0} sin (2π⟪q,z⟫) • q dq`. -/
noncomputable def sigBullet (z : E3) : E3 :=
  ∫ q in ucell 0, (Real.sin (2 * Real.pi * inner ℝ q z)) • q

/-- The vector `(sin (2π z_i))_i`. -/
noncomputable def sinVec (z : E3) : E3 :=
  WithLp.toLp 2 (fun i : Fin 3 => Real.sin (2 * Real.pi * z.ofLp i))

/-- `gam z = ⟪sigBullet z, sinVec z⟫`. -/
noncomputable def gam (z : E3) : ℝ := inner ℝ (sigBullet z) (sinVec z)

@[simp] lemma sinVec_apply (z : E3) (i : Fin 3) :
    (sinVec z).ofLp i = Real.sin (2 * Real.pi * z.ofLp i) := rfl

end Work.BoseRowsL.LatticeCoulomb
