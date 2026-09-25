/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary estimates for the Newton correction

Sharp (constant `1/2`) bound on the `C^{1,α}`-norm of the coordinate datum of the perturbation,
`coordDatum A p q = Lcoef A (fun y => y p) q = (i/2)·(A z e_q)_p`.  This is the form needed by
`Work.NN.Newton.newtonCorrectionArith`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Newton.newtonCorrDefs

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

variable {n : ℕ}

/-- The unit vector `Pi.single q 1` of `ℂⁿ` has norm at most `1`. -/
lemma norm_single_one_le (q : Fin n) : ‖(Pi.single q (1 : ℂ) : Work.NN.Core.Cn n)‖ ≤ 1 := by
  rw [Pi.norm_def, NNReal.coe_le_one]
  refine Finset.sup_le fun b _ => ?_
  by_cases h : b = q
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/-- The coordinate datum is bounded by `a/2` in `C^{1,α}`. -/
lemma coordDatum_holderNorm_le_half {α r a : ℝ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hAsm : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)))
    (hA : ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) ≤ ENNReal.ofReal a)
    (p q : Fin n) :
    Work.CR.Flat.holderNorm 1 α (coordDatum A p q)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (a / 2) := by
  rw [coordDatum_eq_fun]
  have huniq : UniqueDiffOn ℝ (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    (Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)).uniqueDiffOn
  have hsm : ContDiffOn ℝ (1 : ℕ) (fun z => (A z (Pi.single q (1 : ℂ))) p)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
    have h1 : ContDiffOn ℝ (1 : ℕ) (fun z => A z (Pi.single q (1 : ℂ)))
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
      simpa using (hAsm 1).clm_apply contDiffOn_const
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      ContDiff.comp_contDiffOn ((ContinuousLinearMap.proj p).contDiff) h1
  have hs := Work.CR.Flat.Holder.holderNorm_smul (k := 1) (α := α) (Complex.I / 2) hsm huniq
  rw [show (fun z : Work.NN.Core.Cn n => Complex.I / 2 * (A z (Pi.single q (1 : ℂ))) p)
        = (Complex.I / 2) • (fun z => (A z (Pi.single q (1 : ℂ))) p) from rfl, hs]
  have hnorm : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hnorm]
  have hb := hA (Pi.single q (1 : ℂ)) (norm_single_one_le q) p
  calc ENNReal.ofReal (1 / 2) * Work.CR.Flat.holderNorm 1 α
        (fun z => A z (Pi.single q (1 : ℂ)) p)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal a :=
        mul_le_mul_of_nonneg_left hb (by simp)
    _ = ENNReal.ofReal (a / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          show (1 : ℝ) / 2 * a = a / 2 from by ring]

end Work.NN.Newton
