import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsFS.RowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kernel vocabulary for the honest lattice row

The box modes of the honest model are `k_j = (2π/ℓ)·j` (`Work.BoseRowsFS.kvec`), and the
heat-kernel/Poisson identity identifies the Gaussian mode sum
`thetaK ℓ s z = Σ_j e^{-s‖k_j‖²}cos⟨k_j,z⟩` with `ℓ³` times the image sum of the corpus heat
kernel `Kt s w = (4πs)^{-3/2}e^{-‖w‖²/4s}` over the lattice `ℓℤ³`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-- The box mode `k_j = (2π/ℓ)·vecZ j` (`= ℓ⁻¹ • Work.BoseB4.vec j`). -/
def kvec (ℓ : ℝ) (j : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  (2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ j

lemma kvec_eq (ℓ : ℝ) (j : Fin 3 → ℤ) :
    kvec ℓ j = ℓ⁻¹ • Work.BoseB4.vec j := by
  rw [kvec, vec_eq_smul_vecZ, smul_smul]
  congr 1
  ring

lemma norm_kvec {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (j : Fin 3 → ℤ) :
    ‖kvec ℓ j‖ = (2 * Real.pi / ℓ) * ‖vecZ j‖ := by
  rw [kvec, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- The Gaussian mode sum (mode form of the theta kernel) at the box lattice. -/
def thetaK (ℓ s : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑' j : Fin 3 → ℤ, Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) * Real.cos (inner ℝ (kvec ℓ j) z)

/-- The image tail `Σ_{m ≠ 0} Kt s (z + ℓ·m)`. -/
def imageTail (ℓ s : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Kt s (z + ℓ • vecZ m.1)

end Work.BoseRowsFS
