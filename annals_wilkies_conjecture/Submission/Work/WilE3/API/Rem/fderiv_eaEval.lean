import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE2.ev_hasFDerivAt

namespace Work.WilE3.API.Rem

/-- The Fréchet derivative of `eaEval c Q` is the gradient `∑ᵢ (eaEval c (eaD c i Q) x) • projᵢ`.

This is the E3-vocabulary restatement of area E2's `Work.WilE2.ev_hasFDerivAt`, which proves
the same statement for the general chain structure `Work.WilE2.ESys`: the chain `c` is
`ESys.ofChain c`, and `ESys.ofChain_ev` / `ESys.ofChain_d` identify `ESys.ev` with `eaEval`
and `ESys.d` with `eaD` definitionally, while `ESys.grad` is by definition the displayed sum. -/
theorem fderiv_eaEval {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) :
    HasFDerivAt (WilkiesDesign.E.eaEval c Q)
      ((∑ i : Fin k, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x := by
  exact Work.WilE2.ev_hasFDerivAt (Work.WilE2.ESys.ofChain c) Q x

end Work.WilE3.API.Rem
