import Mathlib
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.PTGeometric.ProjOfPlane.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.ThomBordism

open Work.PTGeometric

/-- **The orthogonal projection onto the span of an orthonormal family, as a sum.**  For a finite
orthonormal family `f` in a finite-dimensional real inner product space,
`(span ℝ (range f)).starProjection x = ∑ i, ⟪f i, x⟫ • f i`. -/
private lemma starProjection_span_eq_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E} (hf : Orthonormal ℝ f) (x : E) :
    (Submodule.span ℝ (Set.range f)).starProjection x = ∑ i, inner ℝ (f i) x • f i := by
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction
    (p := fun u _ => inner ℝ u (x - ∑ i, inner ℝ (f i) x • f i) = 0) ?_ ?_ ?_ ?_ hu
  · rintro - ⟨j, rfl⟩
    rw [inner_sub_right]
    have h := hf.inner_right_fintype (fun i => inner ℝ (f i) x) j
    rw [h, sub_self]
  · simp
  · intro a b _ _ ha hb; rw [inner_add_left, ha, hb, add_zero]
  · intro c a _ ha; rw [inner_smul_left, ha, mul_zero]

/-- The orthogonal projection onto the `padEuc`-image of the span of an orthonormal frame is the
`padEndEuc`-conjugate of the projection onto the span. -/
theorem gtdFrameProj_padEuc {k m : ℕ} (hm : 8 ≤ m) {F : Fin k → EuclideanSpace ℝ (Fin (8 + k))}
    (hF : Orthonormal ℝ F) :
    Work.PTGeometric.frameProj (fun j => Work.PTGeometric.padEuc k m hm (F j))
      = Work.PTGeometric.padEndEuc k m hm
          ((Submodule.span ℝ (Set.range F)).subtypeL.comp
            (Submodule.span ℝ (Set.range F)).orthogonalProjectionOnto) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [frameProj_apply, padEndEuc_apply]
  have hstar : (Submodule.span ℝ (Set.range F)).starProjection (projEuc k m hm w)
      = ∑ j, inner ℝ (F j) (projEuc k m hm w) • F j :=
    starProjection_span_eq_sum hF (projEuc k m hm w)
  rw [show (Submodule.span ℝ (Set.range F)).subtypeL.comp
        (Submodule.span ℝ (Set.range F)).orthogonalProjectionOnto
        = (Submodule.span ℝ (Set.range F)).starProjection from rfl, hstar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  have h : inner ℝ (F j) (projEuc k m hm w) = inner ℝ (padEuc k m hm (F j)) w := by
    rw [← padEuc_adjoint k m hm]
    exact ContinuousLinearMap.adjoint_inner_right (padEuc k m hm) (F j) w
  exact h.symm

end Work.ThomBordism
