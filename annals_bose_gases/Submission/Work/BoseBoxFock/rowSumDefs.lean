import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.latFinset_parseval_box
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowSumDefs` — the vocabulary of the lattice row sum

The target `Work.BoseBoxFock.latRowSum_tendsto_L2` compares, in `L²` of the centred corpus box
`Work.BoseK15.corpusBox.boxL ℓ = [-ℓ/2,ℓ/2]³`, the finite lattice row sum

    `rowSum ℓ fu N W z = Σ_{k : Lab N} uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) · Ŵ(kmomLab ℓ N k)
                          · e^{i⟪kmomLab ℓ N k, z⟫}`

with `ℓ³` times the periodisation `latPer ℓ W z = Σ'_m W(z + ℓ·latVec m)`.

The proof compares `rowSum` with the *momentum-ball* partial sum

    `ballSum ℓ N W z = Σ_{‖latVec n‖ ≤ N/4} Ŵ(kmomInt ℓ n) · e^{i⟪kmomInt ℓ n, z⟫}`,

which is exactly the partial sum of `Work.BoseBoxFock.latFourier_tendsto_periodisation` at the
cut-off `Λ = uvRad ℓ N`; their difference is the `cube N`-indexed character sum with coefficients
`rhoCoef` (supported in the annulus `N/4 < ‖latVec n‖ < N/2`), whose `L²` norm is computed by
Parseval (`Work.BoseBoxFock.latFinset_parseval_box`) and bounded by the lattice tail
(`Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`).

This module only fixes the vocabulary, so that the pieces of the proof can be stated and proved
independently.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open LatFourier

/-- The lattice character `z ↦ e^{i⟪kmomInt ℓ n, z⟫}`. -/
def latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))

/-- **The finite lattice row sum of the target**: the `Lab N`-indexed partial sum of the lattice
Fourier series of `W`, with the ultraviolet cut-off `uvCut fu (uvRad ℓ N)`. -/
def rowSum (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) (z : E3) : ℂ :=
  ∑ k : Lab N, ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
      * Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)
      * latChr ℓ (labVec N k) z

/-- The momentum-ball partial sum at the lattice radius `N/4`, in the `Fin 3 → ℤ` indexing of
`Work.BoseBoxFock.latFourier_tendsto_periodisation` (with `Λ = uvRad ℓ N`). -/
def ballSum (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) (z : E3) : ℂ :=
  ∑ n ∈ latBall ((N : ℝ) / 4), latFt ℓ W n * latChr ℓ n z

/-- The coefficient of `rowSum - ballSum` in the `cube N`-indexing.  Its support is the annulus
`N/4 < ‖latVec n‖ < N/2`: on the momentum ball the cut-off equals `1` (so the coefficient
vanishes), and off the ball `2·uvRad` it vanishes. -/
def rhoCoef (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) :
    (Fin 3 → ℤ) → ℂ :=
  fun n => ((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ) * latFt ℓ W n
      - (if n ∈ latBall ((N : ℝ) / 4) then latFt ℓ W n else 0)

end Work.BoseBoxFock
