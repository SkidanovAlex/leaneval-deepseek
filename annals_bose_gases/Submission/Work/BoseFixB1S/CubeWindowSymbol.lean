import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.CubeWindowKinetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.CubeWindowSymbol` — the cube cutoff's symbol vocabulary

Holder of `Submission/Work/BoseFixB1S/LowCountWindowB1copy.lean`; third module of the cube route
(after `CubeWindowKinetic` and `CubeWindowKernel`).  See `FINDING_LowCountWindowB1copy_session2.md`
§5.

FS's `lem:LocKinEn` (`con:BSlidingassp` and the two-cut symbol comparison) is stated in the corpus
`Submission/Work/OneBodyKin/Defs.lean` through the **ball** bump's Fourier profile
`profHat p = ∫ z, chi z · cos⟪p,z⟫` (`symA ℓ F q = (2π)⁻³∫_p F‖q + ℓ⁻¹•p‖·profHat(p)²`), and the
two-cut criterion `Work.OneBodyTwoCut.TwoCutCriterionSharp ℓ d c_sb c_big` is
`√winGradOne ≤ (c_sb − c_big)(dℓ)` with `winGradOne = ∫|∇χ|²`.  Because the square of the profile is
the Fourier transform of the window *autocorrelation* `conv3 χ χ`, running the chapter at the cube
cutoff replaces exactly this profile: the cube's overlap kernel is `convScaleCube M a`
(`CubeWindowKernel`, with the proved identity `integral_cubeWin_mul_cubeWin`) and its Fourier profile
is `profHatCube M` below.  The definitions here are the *only* new vocabulary the cube symbol
comparison needs; they are the literal cube analogues of `profHat`, `winGradOne`, `symA`.

**Consumers (to be stated against these definitions).**

* `symACube_fsKinCoeff_mix_scaled_cube` — the cube two-cut comparison, the analogue of the proved
  `Work.BoseFixB1.Core.symA_fsKinCoeff_mix_scaled` (its inputs `hM1`, `hM2` become the moment bounds
  on `profHatCube M`, supplied by `profHatCube_moments` + Cauchy–Schwarz, and its `htail` input is
  the cube instance at `0`);
* `cruxUnprojCube` — the cube unprojection inequality (`bsFamilyFormUnprojCube ≤ (2π)⁻³∫ symACube …
  ‖kinFT ψ‖²`), the analogue of the proved `Work.BoseFixB1S.cruxUnprojB1`, consuming
  `familyFormUnprojCube_eq_kernelForm` + `symACube_fsKinCoeff_mix_scaled_cube`;
* the cube two-cut *criterion* (regime condition) `√(winGradCube M) ≤ (c_sb − c_big)·a`, the
  analogue of `TwoCutCriterionSharp`, whose constant bookkeeping against FS's parameters
  (`a = ℓd`, `M = mValue = 48`) is a bounded arithmetic task.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The cube cutoff's Fourier profile**: `profHatCube M p = ∫ z, χ_M(z)·cos⟪p,z⟫` — the cube
analogue of `Work.OneBodyKin.profHat` (which uses the corpus's ball bump `χ`).  It is the real
Fourier transform of `chiSmall M` (the sine part vanishes by `chiSmall_even`). -/
noncomputable def profHatCube (M : ℕ) (p : E3) : ℝ :=
  ∫ z : E3, Submission.BoseGases.chiSmall M z * Real.cos (inner ℝ p z)

/-- **The cube gradient energy**: the cube analogue of `Work.hlocWire2.winGradOne`
(`= Σ_k ∫(∂_k χ)²`); for an orthonormal basis this is `∫‖∇χ_M‖²`. -/
noncomputable def winGradCube (M : ℕ) : ℝ :=
  ∫ z : E3, ‖gradient (Submission.BoseGases.chiSmall M) z‖ ^ 2

/-- **The cube first symbol** `symACube M a F q = (2π)⁻³∫_p F‖q + a⁻¹•p‖·(profHatCube M p)²` — the
cube analogue of `Work.OneBodyKin.symA`.  Its kernel form is
`(2π)⁻³∫_z convScaleCube M a z · kinKernel F z · e^{-i⟪q,z⟫}dz`. -/
noncomputable def symACube (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (q : E3) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2

end Work.BoseFixB1S
