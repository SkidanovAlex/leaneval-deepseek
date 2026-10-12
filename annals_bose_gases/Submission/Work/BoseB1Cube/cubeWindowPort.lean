import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.KH.chiB_kinFT_decay
import Submission.Work.BoseFixB1S.mfSpecGeSharpDivDirichletB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeWindowPort` — the window-parametric spectral relation at the
# cube cutoff

The hole half of the cube flat band residual (`Work.BoseB1Cube.CubeBandHole`, the regime
`flatPairSum ≤ 0`) is paid, as in the frozen chapter, by the **windowed Dirichlet energy** of the
fluctuation: the fleet's `Work.Analysis.HoleVoidCost.holeVoidCostCountQuadGood` states

    c·R·S(S+Q)/V ≤ N·( tBdiagFormInd ℓ B V χ_B (·)² Φ + C·μ(a v)(Q+N) )     [pairSum ≤ 0],

and the passage from the *kinetic slot of the word* (`cubeSpectral`) to that Dirichlet slot is the
PROVED window-parametric inequality `Work.BoseFixB1S.sbKin_ge_sharp_of_chi` instantiated at the
cube cutoff.  The frozen chapter instantiates it at the ball cutoff
(`Work.BoseFixB1S.mfSpecGeSharpDivDirichletB1`); this module supplies the **cube** instance, i.e.
the exact statement a prover of `CubeBandHole` needs:

    cubeSpectral(χ) ≥ (1−ε)·tBdiagFormInd ℓ B V χ (·)² Φ − (1+1/ε)c²·tBdiagFormInd ℓ B V χ 1 Φ ,
    χ = chiSmallB M ℓ d u ,  B = dlBox ℓ d u ,  V = boxMass ℓ d u ,  c = sbCut μ (a v) ,

for every `0 < ε ≤ 1`.  This is *window-parametric* (only `χ` continuous with
`tsupport χ ⊆ acube ℓ` enters), so the cube instance is a pure instantiation; the only new
window fact it needs is `tsupport (chiSmallB M ℓ d u) ⊆ acube ℓ`, proved here from the corpus's
`chiSmallB_support_big_box` and the closedness of `acube ℓ`.

**What this does *not* supply** (recorded for the hole-half prover): the *identification* of the
Dirichlet slot `tBdiagFormInd χ (·)²` with the honest Dirichlet energy
`Σ_i ∫ Σ_k (∂_k(χ(x_i)·Q_{B,i}Φ))²` is the PROVED `Work.BoseFixB1S.mfKinEqDirichletB1` at the
**ball** cutoff `chiB`, and its proof needs `ContDiff ℝ ⊤ χ` (a Schwartz-type Fourier argument)
which the corpus cutoff `chiSmallB` does **not** satisfy (it is `C^{M−1}`, `M = 48`).  So the
capacity half of the hole route is on disk at `chiB` and at the `C^∞` cube bump `chiCubeB`
(`BoseFixB1B/chiCubeBump.lean`, `chiCubeB_contDiff`), but *not* at `chiSmallB`; a prover of
`CubeBandHole` must either (i) redo the peel for `C^{47}` windows, or (ii) prove a cube-vs-cube
window comparison `bSpectralCubeB ≤ cubeSpectral(chiSmallB) + (mass terms)` (which is *not* the
refuted ball-vs-cube comparison: both bumps are cube-supported, but they are *not* pointwise
comparable, since the `ℓ`-scale factor of `chiSmallB` is the ball bump `chiScale ℓ`).
See `FINDING_cubeFlatWordKinDiluteBand.md` §3.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The topological support of the cube cutoff lies in the big box.**  From the corpus's
`chiSmallB_support_big_box` (`chiSmallB ≠ 0` forces `|x_j| ≤ ℓ/2`) and the closedness of
`acube ℓ`. -/
theorem tsupport_chiSmallB_subset_acube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    tsupport (Submission.BoseGases.chiSmallB M ℓ d u) ⊆ Submission.BoseGases.acube ℓ := by
  refine closure_minimal ?_ (Work.BoseFixB1.KH.isClosed_acube ℓ)
  intro x hx
  rw [Submission.BoseGases.mem_acube_iff]
  intro j
  have h := Submission.BoseGases.chiSmallB_support_big_box hM hℓ
    (Function.mem_support.mp hx) j
  rw [abs_le] at h
  exact Set.mem_Icc.mpr ⟨by linarith [h.1], h.2⟩

/-- **The spectral relation at the cube cutoff** — `Work.BoseFixB1S.sbKin_ge_sharp_of_chi`
instantiated at `χ = chiSmallB M ℓ d u`: the cube window's `[‖p‖−c]₊²`-slot dominates
`(1−ε)` times the cube window's `‖p‖²`-slot (the *windowed Dirichlet energy*) minus
`(1+1/ε)c²` times its mass slot.  This is the passage used by the hole half of the cube flat band
residual to turn the capacity input `(VC_B)` (stated for `tBdiagFormInd`) into a bound at the
kinetic slot of the word. -/
theorem cubeSpectral_ge_sharp_divDirichlet {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (c : ℝ) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 - ε) * (Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
          (fun r : ℝ => r ^ 2) Φ)
      - ((1 + 1 / ε) * c ^ 2) * (Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
          (fun _ : ℝ => (1 : ℝ)) Φ)
      ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ :=
  Work.BoseFixB1S.sbKin_ge_sharp_of_chi hℓ (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hV
    (Submission.BoseGases.chiSmallB_continuous hM hℓ hd u)
    (tsupport_chiSmallB_subset_acube hM hℓ u) hΦc c hc hε hε1

end Work.BoseB1Cube
