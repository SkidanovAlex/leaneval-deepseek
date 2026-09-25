import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Final

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- At a point of `Ω'` contained in the interior of `Ω`, the iterated within-derivative relative
to `Ω'` agrees with the one relative to `Ω` (both equal the global iterated derivative). -/
lemma iteratedFDerivWithin_eq_of_subset_interior {Ω Ω' : Set X} (hΩ' : IsOpen Ω')
    (hint : Ω' ⊆ interior Ω) (i : ℕ) (f : X → ℂ) {x : X} (hx : x ∈ Ω') :
    iteratedFDerivWithin ℝ i f Ω' x = iteratedFDerivWithin ℝ i f Ω x := by
  have hx_int : x ∈ interior Ω := hint hx
  have h1 : iteratedFDerivWithin ℝ i f Ω' x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω') (f := f) i hΩ' hx
  have h2 : iteratedFDerivWithin ℝ i f (interior Ω) x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := interior Ω) (f := f) i isOpen_interior hx_int
  have h3 : iteratedFDerivWithin ℝ i f (Ω ∩ interior Ω) x
      = iteratedFDerivWithin ℝ i f Ω x :=
    iteratedFDerivWithin_inter_open (𝕜 := ℝ) (s := Ω) (u := interior Ω) (f := f)
      isOpen_interior hx_int
  rw [h1, ← h3, Set.inter_eq_right.mpr interior_subset, h2]

lemma iterDerivNorm_le_of_subset_interior {Ω Ω' : Set X} (hΩ' : IsOpen Ω')
    (hint : Ω' ⊆ interior Ω) (i : ℕ) (f : X → ℂ) :
    Work.CR.Flat.iterDerivNorm i f Ω' ≤ Work.CR.Flat.iterDerivNorm i f Ω := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDerivWithin_eq_of_subset_interior hΩ' hint i f hx]
  exact le_iSup₂_of_le x (interior_subset (hint hx)) le_rfl

lemma holderSeminorm_le_of_subset_interior {Ω Ω' : Set X} (hΩ' : IsOpen Ω')
    (hint : Ω' ⊆ interior Ω) (i : ℕ) (α : ℝ) (f : X → ℂ) :
    Work.CR.Flat.holderSeminorm i α f Ω' ≤ Work.CR.Flat.holderSeminorm i α f Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [iteratedFDerivWithin_eq_of_subset_interior hΩ' hint i f hx,
      iteratedFDerivWithin_eq_of_subset_interior hΩ' hint i f hy]
  exact le_iSup₂_of_le x (interior_subset (hint hx))
    (le_iSup₂_of_le y (interior_subset (hint hy)) (le_iSup_of_le hxy le_rfl))

theorem holderNorm_le_of_subset_interior {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω Ω' : Set X} (hΩ' : IsOpen Ω') (hint : Ω' ⊆ interior Ω) (k : ℕ) (α : ℝ) (f : X → ℂ) :
    Work.CR.Flat.holderNorm k α f Ω' ≤ Work.CR.Flat.holderNorm k α f Ω :=
  Finset.sum_le_sum fun i _ =>
    add_le_add (iterDerivNorm_le_of_subset_interior hΩ' hint i f)
      (holderSeminorm_le_of_subset_interior hΩ' hint i α f)

end Work.NN.Final
