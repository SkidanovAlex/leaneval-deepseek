import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.AeS1.unwAux
import Submission.Work.FTS.EllipticEst.AeS1.unwMain
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyMine
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.aeEnergyOfCutEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

/-!
**The unweighted (radial weight `w²` only) first-order energy inequality** — Step 1 of
`prop:H2` of Elgindi, Annals **194** (2021) in the almost-everywhere class `H2W.Ae.AeData`.

Route (all ingredients sorry-free and axiom-clean, `#print axioms` verified):

* `Cores.Pieces.AeGradRho.AeCutEnergyMine` — the *truncated* `w²`-energy inequality at a general
  compactly supported cut-off `φ` (from the truncated energy identity, the slice self-form and the
  weight algebra);
* `Cores.Pieces.AeGradRho.aeEnergyOfCutEnergy` — removal of the cut-off (monotone convergence
  along `Work.FTS.EllipticEst.cut n` plus the vanishing truncation error), giving the `∫⁻`-form
  energy inequality with the constant `13/2 + 3α² + (3/2)α(5+α) < 9`;
* `AeS1.unwEnergyD_of` — the final bookkeeping: the a.e. constrained slice gap
  `9∫u² ≤ ∫(∂_θu)²` (`AeS1.gap9_lintegral`, from `H2W.AeProof.AeGapSlices`) absorbs the `u²`-mass
  since the constant is `< 9`, and the `L²`-dictionary `AeS1.l2Dictionary` turns the
  `∫⁻`-inequality into the honest Bochner statement, with `L2Mem` for the two first-order
  quantities.
-/
theorem unwEnergyD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
      α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      ≤ C * Work.Spaces.HkSq α 0 G :=
  unwEnergyD_of (Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.aeEnergyOfCutEnergy
    Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyMine)

end Work.FTS.EllipticEst.AeS1
