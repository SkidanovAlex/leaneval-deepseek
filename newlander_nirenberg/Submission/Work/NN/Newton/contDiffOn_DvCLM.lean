import Mathlib
import Submission.Work.NN.Newton.pushforward_setup

/-!
# `z ↦ DvCLM v z` is `C¹` on a polydisc when the components `v l` are `C²`

`Work.NN.Newton.DvCLM v z = ContinuousLinearMap.pi (fun l => fderiv ℝ (v l) z)` is the
componentwise derivative of the correction `v`.  If every component `v l` is `C²` on the
polydisc `Pd n R`, then each `z ↦ fderiv ℝ (v l) z` is `C¹` there (`Pd` is open, so the
derivative is the honest `fderiv`, and `ContDiffOn.fderiv_of_isOpen` lowers the order by one).
The family is then reassembled into a single continuous linear map through the continuous
linear equivalence `ContinuousLinearMap.piEquivL`, which preserves `C¹`.
-/

noncomputable section

open scoped ContDiff

namespace Work.NN.Newton

lemma contDiffOn_DvCLM {n : ℕ} {R : ℝ} {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ContDiffOn ℝ 2 (v l) (Work.NN.Newton.Pd n R)) :
    ContDiffOn ℝ 1 (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n R) := by
  -- each component has a `C¹` derivative on the (open) polydisc
  have h1 : ∀ l, ContDiffOn ℝ 1 (fun z => fderiv ℝ (v l) z) (Pd n R) := fun l =>
    (hv l).fderiv_of_isOpen (isOpen_Pd n R) (by norm_num)
  -- hence the whole family, as a map into the product of the endomorphism spaces
  have h2 : ContDiffOn ℝ 1 (fun z : Work.NN.Core.Cn n => fun l => fderiv ℝ (v l) z)
      (Pd n R) :=
    contDiffOn_pi.2 h1
  -- and the product of endomorphism spaces is identified with the endomorphism space of `ℂⁿ`
  have h3 : ContDiffOn ℝ 1
      (fun z => ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ)
        (fun l => fderiv ℝ (v l) z)) (Pd n R) :=
    (ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ)).contDiff.comp_contDiffOn
      h2
  refine h3.congr ?_
  intro z _
  rw [DvCLM]
  rfl

end Work.NN.Newton
