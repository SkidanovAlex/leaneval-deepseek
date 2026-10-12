import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.SubaddVol
import Submission.Superadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — easy consequences of superadditivity/subadditivity.

- The box energy is non-decreasing in the particle number at fixed box size
  (superadditivity plus nonnegativity of the single-particle energy).
- Densities (at the same box size) are accordingly ordered.
- A subadditivity bound in which the two subsystems may occupy the same
  large box as long as their *own* boxes are small and far apart.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The box energy is non-decreasing in the particle number: `N ≤ M` implies
`E(N, L) ≤ E(M, L)`. -/
lemma boxEnergy_mono_N {N M : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hNM : N ≤ M) :
    boxEnergy N L v ≤ boxEnergy M L v := by
  let d := M - N
  have hsum : N + d = M := by
    dsimp [d]
    exact Nat.add_sub_of_le hNM
  have hs := boxEnergy_superadd (N1 := N) (N2 := d) hL hv hv1
  have hE2 : 0 ≤ boxEnergy d L v := boxEnergy_nonneg hL hv
  have hle : boxEnergy N L v ≤ boxEnergy N L v + boxEnergy d L v := by linarith
  calc
    boxEnergy N L v ≤ boxEnergy N L v + boxEnergy d L v := hle
    _ ≤ boxEnergy (N + d) L v := hs
    _ = boxEnergy M L v := by rw [hsum]

/-- Energy density at fixed box size is non-decreasing in the density. -/
lemma density_mono_N {N M : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hNM : N ≤ M) :
    boxEnergy N L v / L ^ 3 ≤ boxEnergy M L v / L ^ 3 := by
  exact div_le_div_of_nonneg_right (boxEnergy_mono_N hL hv hv1 hNM) (pow_nonneg (le_of_lt hL) 3)

end BoseGases

end Submission
