import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseB1Cube.PortSmallB.DiffSmallB
import Submission.Work.BoseB1Cube.PortSmallB.fibreDirConvW
import Submission.Work.BoseFixB1B.B1Bfix2.diffFibre_factsB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube.PortSmallB

theorem fibreDirDiffSmallB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    Work.BoseB1Cube.PortSmallB.DiffFibreFactsS L d M u ψ K Cb γ ∧
      Work.BoseB1Cube.PortSmallB.FibreDirDiffConvS L d M u ψ K Cb γ :=
  ⟨Work.BoseB1Cube.PortSmallB.diffFibre_factsSmallB hL hd hM u hcut hψ hCb hψb,
   Work.BoseB1Cube.PortSmallB.fibreDirConvW hL hd hM u hcut hψ hCb hψb⟩

end Work.BoseB1Cube.PortSmallB
