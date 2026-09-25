/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Congruence of `holderNorm` on a set

`Work.CR.Flat.holderNorm k α f Ω` only sees the values of `f` on `Ω` (it is built from
`iteratedFDerivWithin ℝ i f Ω` and the value seminorm, all of them restricted to `Ω`).  This file
records that, which is what the cut-off step of `Work.NN.Final.aPrioriEstimate_of_vecHolder` needs:
`χ ≡ 1` on `pd n ρ (3/2)` makes `χ * u` and `u` agree there, so their `holderNorm`s on that polydisc
coincide and monotonicity can carry the estimate from `(3/2)` down to `1`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Final

open Work.CR.Flat

/-- `iterDerivNorm` only sees the values of the function on the set. -/
lemma iterDerivNorm_congr_of_eqOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℂ} {Ω : Set X} (h : Set.EqOn f g Ω) (i : ℕ) :
    Work.CR.Flat.iterDerivNorm i f Ω = Work.CR.Flat.iterDerivNorm i g Ω := by
  unfold Work.CR.Flat.iterDerivNorm
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  rw [iteratedFDerivWithin_congr h hx i]

/-- `holderSeminorm` only sees the values of the function on the set. -/
lemma holderSeminorm_congr_of_eqOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℂ} {Ω : Set X} (h : Set.EqOn f g Ω) (i : ℕ) (α : ℝ) :
    Work.CR.Flat.holderSeminorm i α f Ω = Work.CR.Flat.holderSeminorm i α g Ω := by
  unfold Work.CR.Flat.holderSeminorm
  refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
    iSup_congr fun _ => ?_
  rw [iteratedFDerivWithin_congr h hx i, iteratedFDerivWithin_congr h hy i]

/-- **Congruence of `holderNorm` on a set**: pointwise equality on `Ω` gives equality of the
`C^{k,α}` norms on `Ω`. -/
theorem holderNorm_congr_of_eqOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℂ} {Ω : Set X} (h : Set.EqOn f g Ω) (k : ℕ) (α : ℝ) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterDerivNorm_congr_of_eqOn h i, holderSeminorm_congr_of_eqOn h i α]

end Work.NN.Final
