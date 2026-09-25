/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Congruence of the `C^{k,α}` norms on an open set

If two functions agree on an open set `Ω` then their within-derivatives on `Ω` (which are the
ambient iterated derivatives, since `Ω` is open) agree pointwise, hence so do
`iterDerivNorm`, `holderSeminorm` and `holderNorm`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set Filter

namespace Work.NN.Final

open Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Agreement on an open set forces equality of the within-derivatives of every order. -/
lemma iteratedFDerivWithin_eq_of_eqOn_isOpen {Ω : Set X} (_hΩ : IsOpen Ω) {f g : X → ℂ}
    (h : ∀ x ∈ Ω, f x = g x) (i : ℕ) {x : X} (hx : x ∈ Ω) :
    iteratedFDerivWithin ℝ i f Ω x = iteratedFDerivWithin ℝ i g Ω x :=
  Filter.EventuallyEq.iteratedFDerivWithin_eq (s := Ω)
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h) (h x hx) i

lemma iterDerivNorm_congr_of_isOpen {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℂ}
    (h : ∀ x ∈ Ω, f x = g x) (i : ℕ) :
    iterDerivNorm i f Ω = iterDerivNorm i g Ω := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hx]
    exact le_iSup₂_of_le x hx le_rfl
  · rw [← iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hx]
    exact le_iSup₂_of_le x hx le_rfl

lemma holderSeminorm_congr_of_isOpen {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℂ}
    (h : ∀ x ∈ Ω, f x = g x) (i : ℕ) (α : ℝ) :
    holderSeminorm i α f Ω = holderSeminorm i α g Ω := by
  refine le_antisymm
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
  · rw [iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hx,
      iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · rw [← iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hx,
      ← iteratedFDerivWithin_eq_of_eqOn_isOpen hΩ h i hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma holderNorm_congr_of_isOpen {Ω : Set X} (hΩ : IsOpen Ω) {f g : X → ℂ}
    (h : ∀ x ∈ Ω, f x = g x) (k : ℕ) (α : ℝ) :
    holderNorm k α f Ω = holderNorm k α g Ω := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterDerivNorm_congr_of_isOpen hΩ h i, holderSeminorm_congr_of_isOpen hΩ h i α]

end Work.NN.Final
