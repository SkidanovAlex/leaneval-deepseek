import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_boxSlotOf_symm`

The sum over the slots of the first-quantised rank-one operators
`Σ_j boxSlotOf e w v j Θ` is again a **symmetric** operator: if `Θ = X` is invariant
under permutations of the particle labels, then so is `Σ_j boxSlotOf e w v j X`.

This is the symmetry input needed to identify `boxCreOf ∘ boxAnnOf` with the slot sum:
the composite is symmetric (it is an operator built from the symmetric Fock space) and
`boxCreOf_boxAnnOf_slot` writes it as `Σ_j boxSlotOf e w v j Θ`, whence `Σ_j boxSlotOf`
preserves the symmetric subspace.

The proof is the obvious reindexing.  Unfolding the definition,

`(boxSlotOf e w v j X)(x) = η_w(x_j) ∫_z conj(η_v z) · X (x[j ↦ z])`,

and the *only* point is that putting the hole in slot `j` of the permuted configuration
`x ∘ σ` is the same as putting the hole in slot `σ j` of `x` and then permuting:
`(x ∘ σ)[j ↦ z] = (x[σ j ↦ z]) ∘ σ`.  Symmetry of `X` therefore identifies the
integrands at `j`, and `Equiv.sum_comp` turns `∑_j f (σ j)` into `∑_j f j`.
-/

namespace Work.BoseBoxFock

open scoped BigOperators
open MeasureTheory

theorem sum_boxSlotOf_symm {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (w v : Fin m → ℝ) (X : Work.BoseDict.Xn d → ℂ)
    (hX : ∀ (σ : Equiv.Perm (Fin d)) (x : Work.BoseDict.Xn d), X (x ∘ σ) = X x) :
    ∀ (σ : Equiv.Perm (Fin d)) (x : Work.BoseDict.Xn d),
      (∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j X) (x ∘ σ)
        = (∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j X) x := by
  intro σ x
  simp only [Finset.sum_apply, Work.BoseDict.boxSlotOf]
  -- `(x ∘ σ)[j ↦ z] = (x[σ j ↦ z]) ∘ σ`
  have hupdate : ∀ (j : Fin d) (z : Work.BoseDict.Sp),
      Function.update (x ∘ σ) j z = (Function.update x (σ j) z) ∘ σ := by
    intro j z
    funext i
    by_cases hi : i = j
    · subst hi; simp [Function.update]
    · have hne : σ i ≠ σ j := fun h => hi (σ.injective h)
      simp [Function.update, hi, hne]
  trans ∑ j : Fin d, Work.BoseDict.etaOf e w (x (σ j)) *
      ∫ z : Work.BoseDict.Sp,
        (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * X (Function.update x (σ j) z)
  · -- the `j`-th summands agree, using `hX` at the permuted configuration
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : Work.BoseDict.etaOf e w ((x ∘ σ) j) = Work.BoseDict.etaOf e w (x (σ j)) := by
      simp
    have h2 : (∫ z : Work.BoseDict.Sp,
          (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * X (Function.update (x ∘ σ) j z))
        = ∫ z : Work.BoseDict.Sp,
          (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * X (Function.update x (σ j) z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [hupdate j z, hX σ]
    rw [h1, h2]
  · -- reindex the sum along the permutation
    exact Equiv.sum_comp σ (fun j => Work.BoseDict.etaOf e w (x j) *
      ∫ z : Work.BoseDict.Sp,
        (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * X (Function.update x j z))

end Work.BoseBoxFock
