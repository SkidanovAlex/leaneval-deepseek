import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseBoxFock.chat_eq_kinFT_of_even
import Submission.Work.BoseBoxFock.pinQ_kernel_expansion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQLimDefs` — the limit kernels of the FS `Q₂` row

The four lattice sums `pinQA/pinQB/pinQC/pinQD` of `pinQ_kernel_expansion` are the truncated
(`Lab N`, UV-cut) versions of four **infinite** sums, and the reduction of the `Q₂` row
(`FINDING_PotPairRows_exists.md` §5.3, step (S2)) compares each of them with its limit as the
cut-off grows:

* `pinQA` (the `χχ`-term) — the truncated lattice Fourier series of `W`, whose `L²` limit is the
  **periodisation** `ℓ³Σ_m W(·+ℓ•latVec m)`; the convergence is *not* absolute and is the content of
  `Work.BoseBoxFock.latFourier_tendsto_periodisation`
  (`Work.BoseBoxFock.latRowSum_tendsto_L2` is the consumer-shaped form);
* `pinQB`, `pinQC`, `pinQD` (the three `χ̂`-terms) — **absolutely** convergent lattice sums
  (χ is `C∞` with compact support, `chat W` is bounded), whose limits are the honest functions
  `pinQBl`, `pinQCl`, `pinQDl` below; the tails are uniform in the position variable
  (`Work.BoseBoxFock.hatChi_lattice_tail_le`).

`K1lim` is the limit of the expanded pair kernel `K1exp` (`pinQ_kernel_expansion.lean`): it is the
function-by-function limit of `K1exp v μ N c` as `N → ∞` when `c k = uvCut·chat W(kmomLab ℓ N k)`.

Everything here is definitional (`sorry`-free); the *proofs* of the convergence statements are the
content of the reduction and live in the consumer files.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **periodisation** `ℓ³Σ_m W(z + ℓ•latVec m)`: the pointwise (L²-)limit of `pinQA`, and the
`χχ`-part of the limit kernel. -/
noncomputable def latPer3 (ℓ : ℝ) (W : E3 → ℝ) (z : E3) : ℂ :=
  ((ℓ ^ 3 : ℝ) : ℂ) * LatFourier.latPer ℓ W z

/-- The periodisation is `ℓℤ³`-periodic. -/
theorem latPer3_add_latVec (ℓ : ℝ) (W : E3 → ℝ) (v : Fin 3 → ℤ) (z : E3) :
    latPer3 ℓ W (z + ℓ • latVec v) = latPer3 ℓ W z := by
  have hmain : LatFourier.latPer ℓ W (z + ℓ • latVec v) = LatFourier.latPer ℓ W z := by
    rw [LatFourier.latPer, LatFourier.latPer]
    have hf : (fun m : Fin 3 → ℤ => ((W (z + ℓ • latVec v + ℓ • latVec m) : ℝ) : ℂ))
        = fun m : Fin 3 → ℤ => ((W (z + ℓ • latVec (v + m)) : ℝ) : ℂ) := by
      funext m
      congr 1
      congr 1
      rw [add_assoc, ← smul_add, ← LatFourier.latVec_add]
    rw [hf]
    let e : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) :=
      { toFun := fun m => v + m
        invFun := fun m => -v + m
        left_inv := fun m => by simp [add_assoc]
        right_inv := fun m => by simp [add_assoc] }
    have h2 := Equiv.tsum_eq e (fun m : Fin 3 → ℤ => ((W (z + ℓ • latVec m) : ℝ) : ℂ))
    simpa [e] using h2
  unfold latPer3
  rw [hmain]

/-- The limit of the first `χ̂`-lattice sum `pinQB`. -/
noncomputable def pinQBl (ℓ : ℝ) (W : E3 → ℝ) (w : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
    * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
    * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))

/-- The limit of the second `χ̂`-lattice sum `pinQC`. -/
noncomputable def pinQCl (ℓ : ℝ) (W : E3 → ℝ) (y : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
    * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
    * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))

/-- The limit of the `θθ`-lattice sum `pinQD` (a constant). -/
noncomputable def pinQDl (ℓ : ℝ) (W : E3 → ℝ) : ℂ :=
  ∑' n : Fin 3 → ℤ, ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
    * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2

/-- **The limit pair kernel**: the four-term limit form of `K1exp` at the honest box side `ℓ`. -/
noncomputable def K1lim (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) : ℂ :=
  ((ℓ ^ 3)⁻¹ : ℝ) *
    ( (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
      - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
      - Work.BoseK15.corpusBox.thetaFun ℓ w
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y
      + Work.BoseK15.corpusBox.thetaFun ℓ w
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W)

end Work.BoseBoxFock
