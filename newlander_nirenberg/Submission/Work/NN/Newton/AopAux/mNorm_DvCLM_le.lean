import Mathlib
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Newton.DvCLM_data_le
import Submission.Work.NN.Newton.AopAux.mNorm_le_ofReal_of_component_le

namespace Work.NN.Newton.AopAux

open scoped NNReal ENNReal ContDiff
open Set

-- `hr4` and `hδ` belong to the interface of the statement but are not needed by the argument.
set_option linter.unusedVariables false

/-- The four families of scalar functions attached to `DvCLM v` -- the two real-basis families
`z ↦ (DvCLM v z e_j)_l`, `z ↦ (DvCLM v z (i e_j))_l`, and the components of the `ℂ`-linear and
`ℂ`-antilinear coefficient families of `DvCLM v z` -- all have `C^{1,α}`-norm at most `8 b` on
the polydisc `Pd n (r (1 - δ))`.

Indeed `(DvCLM v z h)_l = fderiv ℝ (v l) z h`, `linCoef (DvCLM v z) p` is the vector
`z ↦ ∂_p v_l z` and `antiCoef (DvCLM v z) p` is the vector `z ↦ ∂̄_p v_l z`, so every one of
these families is one of the first order coefficient families of one of the components `v l`,
and the `C^{2,α}`-estimate `holderNorm_one_fderiv_coeff_le` bounds each of those by `8 b`. -/
theorem DvCLM_component_holderNorm_le {n : ℕ} {α r δ b : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 1 ≤ r) (hδ8 : δ ≤ 1 / 8)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n (r * (1 - δ))))
    (hb0 : 0 ≤ b)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b) :
    (∀ j l : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => (Work.NN.Newton.DvCLM v z (Pi.single j 1)) l)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ j l : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => (Work.NN.Newton.DvCLM v z (Pi.single j (Complex.I : ℂ))) l)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ p l : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => (Work.NN.Newton.linCoef (Work.NN.Newton.DvCLM v z) p) l)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
    (∀ p l : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => (Work.NN.Newton.antiCoef (Work.NN.Newton.DvCLM v z) p) l)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) := by
  have hR : 0 < r * (1 - δ) := by nlinarith
  have hcoeff : ∀ l : Fin n,
      (∀ p, Work.CR.Flat.holderNorm 1 α (fun z => fderiv ℝ (v l) z (Pi.single p 1))
          (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
      (∀ p, Work.CR.Flat.holderNorm 1 α
          (fun z => fderiv ℝ (v l) z (Pi.single p (Complex.I : ℂ)))
          (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
      (∀ p, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dCoord p (v l) z)
          (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) ∧
      (∀ p, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord p (v l) z)
          (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (8 * b)) :=
    fun l => Work.NN.Newton.holderNorm_one_fderiv_coeff_le (R := r * (1 - δ))
      hα0 hα1 hR (hv l) hb0 (hb l)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l
    rw [show (fun z => (Work.NN.Newton.DvCLM v z (Pi.single j 1)) l)
        = (fun z => fderiv ℝ (v l) z (Pi.single j 1)) from rfl]
    exact (hcoeff l).1 j
  · intro j l
    rw [show (fun z => (Work.NN.Newton.DvCLM v z (Pi.single j (Complex.I : ℂ))) l)
        = (fun z => fderiv ℝ (v l) z (Pi.single j (Complex.I : ℂ))) from rfl]
    exact (hcoeff l).2.1 j
  · intro p l
    rw [show (fun z => (Work.NN.Newton.linCoef (Work.NN.Newton.DvCLM v z) p) l)
        = (fun z => Work.CR.Flat.dCoord p (v l) z) from by
      funext z
      rw [Work.NN.Newton.linCoef_apply, Work.CR.Flat.dCoord, Work.NN.Newton.DvCLM_apply,
        Work.NN.Newton.DvCLM_apply]]
    exact (hcoeff l).2.2.1 p
  · intro p l
    rw [show (fun z => (Work.NN.Newton.antiCoef (Work.NN.Newton.DvCLM v z) p) l)
        = (fun z => Work.CR.Flat.dbarCoord p (v l) z) from by
      funext z
      rw [Work.NN.Newton.antiCoef_apply, Work.CR.Flat.dbarCoord, Work.NN.Newton.DvCLM_apply,
        Work.NN.Newton.DvCLM_apply]]
    exact (hcoeff l).2.2.2 p

theorem mNorm_DvCLM_le {n : ℕ} {α r δ b : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 1 ≤ r) (hr4 : r ≤ 4) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n (r * (1 - δ))))
    (hb0 : 0 ≤ b)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b) :
    Work.NN.Newton.mNorm 1 α (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal (32 * (n : ℝ) ^ 2 * b) := by
  have hb8 : 0 ≤ 8 * b := by linarith
  obtain ⟨h1, h2, h3, h4⟩ :=
    DvCLM_component_holderNorm_le hα0 hα1 hr hδ8 (v := v) hv hb0 hb
  refine (mNorm_le_ofReal_of_component_le hb8 h1 h2 h3 h4).trans (le_of_eq ?_)
  congr 1
  ring

end Work.NN.Newton.AopAux
