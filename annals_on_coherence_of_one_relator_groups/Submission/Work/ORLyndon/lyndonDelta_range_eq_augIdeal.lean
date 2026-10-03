import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.augIdeal_eq_span

/-!
# The range of `δ` is the augmentation ideal

The second map `δ : K[G]^X → K[G]` of the Lyndon resolution of a one-relator group `G = ⟨X | r⟩`
sends `(a_x) ↦ Σ_x a_x (x - 1)`, where `x` also denotes the image of the generator `x ∈ X` in `G`.
Its range is therefore the `K[G]`-submodule spanned by the elements `x - 1`.  Since `X` generates
`G`, this span is exactly the augmentation ideal `I_{K[G]} = ker ε`.

This file proves that `LinearMap.range (lyndonDelta K r) = augIdeal K (OneRelatorGroup r)`.

## Main results

* `Work.ORLyndon.augIdeal_eq_span_of_closure_range`: for any `f : X → G` whose range generates `G`,
  the `K[G]`-span of `{f x - 1}` is the augmentation ideal of `G`.
* `Work.ORLyndon.lyndonDelta_range_eq_augIdeal`: the range of `δ` is the augmentation ideal.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- If `f : X → G` is a family whose range generates the group `G`, then the `K[G]`-submodule of
`K[G]` spanned by the elements `f x - 1` is the augmentation ideal of `K[G]`.

Indeed `augIdeal K G` is spanned by all `g - 1` (`augIdeal_eq_span`), and every `g - 1` lies in the
span of the `f x - 1`: this follows by closure induction, using the identities
`hk - 1 = h(k - 1) + (h - 1)` and `h⁻¹ - 1 = -(h⁻¹ (h - 1))`. -/
theorem augIdeal_eq_span_of_closure_range {K : Type*} [CommRing K] {G : Type*} [Group G]
    {X : Type*} (f : X → G) (hf : Subgroup.closure (Set.range f) = ⊤) :
    Submodule.span (MonoidAlgebra K G) (Set.range (fun x => MonoidAlgebra.of K G (f x) - 1)) =
      augIdeal K G := by
  rw [augIdeal_eq_span]
  let S : Submodule (MonoidAlgebra K G) (MonoidAlgebra K G) :=
    Submodule.span (MonoidAlgebra K G) (Set.range (fun x => MonoidAlgebra.of K G (f x) - 1))
  -- the set of `g` with `of g - 1 ∈ S` is a subgroup of `G`
  let H : Subgroup G :=
    { carrier := {g : G | MonoidAlgebra.of K G g - 1 ∈ S}
      mul_mem' := by
        intro a b ha hb
        change MonoidAlgebra.of K G (a * b) - 1 ∈ S
        have h1 : MonoidAlgebra.of K G (a * b) - 1 =
            MonoidAlgebra.of K G a * (MonoidAlgebra.of K G b - 1) +
              (MonoidAlgebra.of K G a - 1) := by
          rw [map_mul, mul_sub, mul_one]; abel
        rw [h1]
        exact Submodule.add_mem _
          (by simpa only [smul_eq_mul] using
            Submodule.smul_mem S (MonoidAlgebra.of K G a) hb) ha
      one_mem' := by
        change MonoidAlgebra.of K G (1 : G) - 1 ∈ S
        rw [map_one, sub_self]
        exact Submodule.zero_mem _
      inv_mem' := by
        intro a ha
        change MonoidAlgebra.of K G a⁻¹ - 1 ∈ S
        have h1 : MonoidAlgebra.of K G a⁻¹ - 1 =
            -(MonoidAlgebra.of K G a⁻¹ * (MonoidAlgebra.of K G a - 1)) := by
          rw [mul_sub, mul_one, ← map_mul, inv_mul_cancel, map_one]; abel
        rw [h1]
        exact Submodule.neg_mem _
          (by simpa only [smul_eq_mul] using
            Submodule.smul_mem S (MonoidAlgebra.of K G a⁻¹) ha) }
  have key : ∀ g : G, MonoidAlgebra.of K G g - 1 ∈ S := by
    intro g
    have hle : Subgroup.closure (Set.range f) ≤ H := by
      rw [Subgroup.closure_le]
      rintro g ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, rfl⟩
    exact hle (by rw [hf]; exact Subgroup.mem_top g)
  refine le_antisymm ?_ ?_
  · -- `span {f x - 1} ≤ span {g - 1}`
    rw [Submodule.span_le]
    rintro y ⟨x, rfl⟩
    exact Submodule.subset_span ⟨f x, rfl⟩
  · -- `span {g - 1} ≤ span {f x - 1}`
    rw [Submodule.span_le]
    rintro y ⟨g, rfl⟩
    exact key g

theorem lyndonDelta_range_eq_augIdeal {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) :
    LinearMap.range (Work.ORLyndon.lyndonDelta (K := K) r) =
      Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r) := by
  -- `δ` is the linear combination of the vectors `x - 1`
  have hdelta : lyndonDelta (K := K) r =
      Finsupp.linearCombination (MonoidAlgebra K (OneRelatorGroup r))
        (fun x : X => MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r (FreeGroup.of x)) - 1) := by
    refine LinearMap.ext fun a => ?_
    rw [lyndonDelta_apply, Finsupp.linearCombination_apply]
    have hfun : (fun (x : X) (c : MonoidAlgebra K (OneRelatorGroup r)) =>
          c * ((presentAlg K r) ((of K (FreeGroup X)) (FreeGroup.of x)) - 1)) =
        (fun (i : X) (a : MonoidAlgebra K (OneRelatorGroup r)) =>
          a * ((of K (OneRelatorGroup r)) ((presentRho r) (FreeGroup.of i)) - 1)) := by
      funext x c
      rw [presentAlg_of]
    rw [hfun]
    simp only [smul_eq_mul]
  rw [hdelta, Finsupp.range_linearCombination]
  -- the images of the generators generate `G`, so the span is the augmentation ideal
  exact augIdeal_eq_span_of_closure_range (K := K)
    (fun x : X => presentRho r (FreeGroup.of x))
    (PresentedGroup.closure_range_of ({r} : Set (FreeGroup X)))

end Work.ORLyndon
