import Mathlib
import Submission.Work.Bordism.Middle
import Submission.Work.ThomBordism.sigmaInterForm

/-!
# Non-degeneracy of a finite orthogonal sum of quadratic forms

For a finite family of quadratic forms `Q i` on `ℚ`-vector spaces `V i`, the orthogonal sum
`x ↦ ∑ i, Q i (x i)` on the product `∀ i, V i` is non-degenerate as soon as each `Q i` is:

`Work.ThomBordism.nondegenerate_sum_prod`.

The auxiliary computation is `Work.ThomBordism.associated_sum_comp_proj`: the associated bilinear
form of the orthogonal sum evaluates coordinatewise,

`associated (∑ i, (Q i).comp (proj i)) x y = ∑ i, associated (Q i) (x i) (y i)`.

This is the non-degeneracy companion of `Work.ThomBordism.signature_sum_prod` (additivity of the
signature over a finite orthogonal sum); it is the second algebraic input (after
`Work.ThomBordism.nondegenerate_comp_linearEquiv`) of the transportation of the middle intersection
form of a boundary to the disjoint union of its pieces.
-/


namespace Work.ThomBordism

open Work.SignatureBordism

/-- **The associated bilinear form of a finite orthogonal sum**, evaluated coordinatewise. -/
theorem associated_sum_comp_proj {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] (Q : ∀ i, QuadraticForm ℚ (V i))
    (x y : ∀ i, V i) :
    QuadraticMap.associated
        (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i)) x y
      = ∑ i, QuadraticMap.associated (Q i) (x i) (y i) := by
  have hmain : QuadraticMap.associated
        (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i))
      = ∑ i, LinearMap.compl₁₂ (QuadraticMap.associated (Q i))
          (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i)
          (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i) := by
    rw [show QuadraticMap.associated
          (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i))
        = QuadraticMap.associatedHom ℚ
            (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i)) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show QuadraticMap.associated (Q i)
        = QuadraticMap.associatedHom ℚ (Q i) from rfl]
    exact QuadraticMap.associated_comp ℚ (Q i) (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i)
  rw [hmain, sum_apply₂]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [LinearMap.compl₁₂_apply, LinearMap.proj_apply]

/-- **The orthogonal sum of finitely many non-degenerate forms is non-degenerate.** -/
theorem nondegenerate_sum_prod {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] (Q : ∀ i, QuadraticForm ℚ (V i))
    (h : ∀ i, Work.Bordism.Nondegenerate (Q i)) :
    Work.Bordism.Nondegenerate
      (∑ i, (Q i).comp (LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] V i)) := by
  classical
  intro x hx
  funext j
  refine h j (x j) (fun yj => ?_)
  have hupd := hx (Function.update (0 : ∀ i, V i) j yj)
  rw [associated_sum_comp_proj Q x (Function.update (0 : ∀ i, V i) j yj),
    Finset.sum_eq_single j] at hupd
  · rw [Function.update_self j yj (0 : ∀ i, V i)] at hupd
    exact hupd
  · intro i _ hij
    rw [Function.update_of_ne (a := i) (a' := j) hij yj (0 : ∀ i, V i)]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Work.ThomBordism
