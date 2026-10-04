import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem norm_iteratedFDerivWithin_le_pi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} [Fintype ι] {s : Set E} {F : E → (ι → G)} {x : E} {i : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hF : ContDiffWithinAt ℝ (⊤ : ℕ∞) F s x)
    (h : ∀ j : ι, ‖iteratedFDerivWithin ℝ i (fun y => F y j) s x‖ ≤ A) :
    ‖iteratedFDerivWithin ℝ i F s x‖ ≤ A := by
  -- Each component of the iterated derivative is the iterated derivative of the component:
  -- the `j`-th coordinate of `D^iF` is `proj j ∘ D^iF`, which is `D^i(F · j)`.
  have hcomp : ∀ j : ι,
      iteratedFDerivWithin ℝ i (fun y => F y j) s x
        = (ContinuousLinearMap.proj j : (ι → G) →L[ℝ] G).compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ i F s x) := by
    intro j
    have hle : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hfun : (fun y => F y j) = ⇑(ContinuousLinearMap.proj j : (ι → G) →L[ℝ] G) ∘ F := rfl
    rw [hfun]
    exact ContinuousLinearMap.iteratedFDerivWithin_comp_left
      (𝕜 := ℝ) (f := F) (s := s) (x := x) (i := i)
      (ContinuousLinearMap.proj j : (ι → G) →L[ℝ] G) hF hs hx hle
  -- `D^iF` is the product of its components, so its norm is the sup of the component norms.
  have hpi : iteratedFDerivWithin ℝ i F s x
      = ContinuousMultilinearMap.pi (fun j : ι =>
          (ContinuousLinearMap.proj j : (ι → G) →L[ℝ] G).compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ i F s x)) := by
    ext v j
    rw [ContinuousMultilinearMap.pi_apply]
    rfl
  rw [hpi, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg hA).mpr (fun j => by rw [← hcomp j]; exact h j)

end Work.Diff.STE.B3
