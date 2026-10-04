import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `sum_integral_pdVec_const_le_ENormSq`

The energy `ENormSq k u = Σ_{l : Fin k → ι} ∫_{unitCube} ‖∂^l u‖²` is a sum over *all* iterated
partial derivatives of order `k`.  The "pure" derivatives `∂ᵢ^k` correspond to the constant
multi-indices `l = (fun _ => i)`, so their energy is a sub-sum of `ENormSq k u` and hence bounded
by it:

  `Σ_{i : ι} ∫_{unitCube} ‖∂ᵢ^k u‖² ≤ ENormSq k u`.

Nothing about `u` is used beyond the fact that the integral of a nonnegative function is
nonnegative; the only requirement is `k ≥ 1`, which makes the map `i ↦ (fun _ : Fin k => i)`
injective (for `k = 0` the map is constant and the claim fails).
-/

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

theorem sum_integral_pdVec_const_le_ENormSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (c : (ι → ℤ) → ℂ) :
    ∑ i : ι, ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pdVec k (fun _ : Fin k => i) (Work.Diff.STE.seriesFun c) x‖ ^ 2
      ≤ Work.Diff.STE.ENormSq k (Work.Diff.STE.seriesFun c) := by
  classical
  rw [ENormSq]
  -- the individual energies
  set G : (Fin k → ι) → ℝ := fun l => ∫ x in unitCube, ‖pdVec k l (seriesFun c) x‖ ^ 2 with hG
  have hGnn : ∀ l, 0 ≤ G l := by
    intro l
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by positivity)
  -- the constant multi-index map is injective because `Fin k` is nonempty
  have hinj : Set.InjOn (fun i : ι => (fun _ : Fin k => i)) ((Finset.univ : Finset ι) : Set ι) := by
    intro a _ b _ hab
    have h0 : (0 : ℕ) < k := lt_of_lt_of_le Nat.zero_lt_one hk
    have h := congrFun hab ⟨0, h0⟩
    simpa using h
  -- rewrite the left-hand sum as a sum over the image
  have h1 : ∑ i : ι, G (fun _ : Fin k => i)
      = ∑ l ∈ Finset.univ.image (fun i : ι => (fun _ : Fin k => i)), G l := by
    rw [Finset.sum_image]
    exact hinj
  rw [h1]
  -- and a sub-sum of nonnegative terms is at most the whole sum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hGnn x)

end Work.Diff.STE
