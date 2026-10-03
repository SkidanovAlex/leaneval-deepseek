import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right

/-!
# The dimension of a finitely generated submodule of `R^n` over a von Neumann regular ring

For a von Neumann regular ring `R` carrying a Sylvester rank function `rk`, and a finitely
generated left submodule `W = span (range v) ≤ R^n` (with `v : Fin k → (Fin n → R)`), we define
`dimOf R rk v` to be the rank of the (matrix of the) idempotent endomorphism of `R^n` whose
range is `W`; such an idempotent exists by `exists_idempotent_range_span_aux`.

The main point is that this is well defined (independent of the chosen idempotent).
-/

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

variable {R : Type u} [Ring R] [VonNeumannRegularRing R]

/-- Two idempotent endomorphisms of the free module `R^n` with the same range have associated
matrices of the same rank. -/
theorem rank_idem_eq_of_range_eq (rk : SylvesterRank R) {n : ℕ}
    (e f : Module.End R (Fin n → R)) (he : e * e = e) (hf : f * f = f)
    (h : LinearMap.range e = LinearMap.range f) :
    rk.rk n n (Matrix.toLinearMapRight'.symm e) = rk.rk n n (Matrix.toLinearMapRight'.symm f) := by
  have hec : e ∘ₗ e = e := by rwa [Module.End.mul_eq_comp] at he
  have hfc : f ∘ₗ f = f := by rwa [Module.End.mul_eq_comp] at hf
  have he' : e ∘ₗ f = f := by
    apply DFunLike.ext; intro y
    obtain ⟨z, hz⟩ := (h.symm ▸ LinearMap.mem_range_self f y : f y ∈ LinearMap.range e)
    rw [LinearMap.comp_apply, ← hz]
    exact congrArg (fun g => g z) hec
  have hf' : f ∘ₗ e = e := by
    apply DFunLike.ext; intro y
    obtain ⟨z, hz⟩ := (h ▸ LinearMap.mem_range_self e y : e y ∈ LinearMap.range f)
    rw [LinearMap.comp_apply, ← hz]
    exact congrArg (fun g => g z) hfc
  have hmat : Matrix.toLinearMapRight'.symm e * Matrix.toLinearMapRight'.symm f =
      Matrix.toLinearMapRight'.symm e := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hf'
  have hmat' : Matrix.toLinearMapRight'.symm f * Matrix.toLinearMapRight'.symm e =
      Matrix.toLinearMapRight'.symm f := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact he'
  have h1 : rk.rk n n (Matrix.toLinearMapRight'.symm e) ≤ rk.rk n n (Matrix.toLinearMapRight'.symm f) := by
    calc rk.rk n n (Matrix.toLinearMapRight'.symm e)
        = rk.rk n n (Matrix.toLinearMapRight'.symm e * Matrix.toLinearMapRight'.symm f) := by
          rw [hmat]
      _ ≤ rk.rk n n (Matrix.toLinearMapRight'.symm f) :=
          rk.rk_mul_le_right (Matrix.toLinearMapRight'.symm e) (Matrix.toLinearMapRight'.symm f)
  have h2 : rk.rk n n (Matrix.toLinearMapRight'.symm f) ≤ rk.rk n n (Matrix.toLinearMapRight'.symm e) := by
    calc rk.rk n n (Matrix.toLinearMapRight'.symm f)
        = rk.rk n n (Matrix.toLinearMapRight'.symm f * Matrix.toLinearMapRight'.symm e) := by
          rw [hmat']
      _ ≤ rk.rk n n (Matrix.toLinearMapRight'.symm e) :=
          rk.rk_mul_le_right (Matrix.toLinearMapRight'.symm f) (Matrix.toLinearMapRight'.symm e)
  linarith

/-- The rank of the matrix of a fixed endomorphism. -/
noncomputable def dimOfEnd (rk : SylvesterRank R) {n : ℕ} (e : Module.End R (Fin n → R)) : ℝ :=
  rk.rk n n (Matrix.toLinearMapRight'.symm e)

/-- The dimension of the submodule `span (range v) ≤ R^n`. -/
noncomputable def dimOf (rk : SylvesterRank R) {n k : ℕ} (v : Fin k → (Fin n → R)) : ℝ :=
  dimOfEnd rk (Classical.choose (Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v))

/-- `dimOf` is computed by any idempotent endomorphism with range `span (range v)`. -/
theorem dimOf_eq (rk : SylvesterRank R) {n k : ℕ} (v : Fin k → (Fin n → R))
    (e : Module.End R (Fin n → R)) (he : e * e = e)
    (hrange : LinearMap.range e = Submodule.span R (Set.range v)) :
    dimOfEnd rk e = dimOf rk v := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v)
  exact rank_idem_eq_of_range_eq rk e _ he h1 (by rw [hrange, h2])

end Work.ORHughesFree.NaturalExtension
