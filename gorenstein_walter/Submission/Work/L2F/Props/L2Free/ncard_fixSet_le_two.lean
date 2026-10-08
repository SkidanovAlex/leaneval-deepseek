import Mathlib
import Submission.Work.L2F.Props.L2Free.Defs
import Submission.Work.L2F.Props.L2Free.three_lines_smul_id
import Submission.Work.L2F.Props.L2Free.smul_rep_mem_span

open scoped LinearAlgebra.Projectivization MatrixGroups
open Matrix

namespace Work.L2F.Props.L2Free

/-! ## Fixed points of `SL(2,F)` on `ℙ¹(F)` and eigenvectors

The proof of `ncard_fixSet_le_two` rests on two independent inputs proved next door:

* `smul_rep_mem_span`: if `A ∈ SL(2,F)` fixes a point `p` of `ℙ¹(F)`, then `p.rep` is an
  eigenvector of `A`;
* `three_lines_smul_id`: a linear endomorphism of `F²` preserving three pairwise distinct lines is
  a scalar multiple of the identity.

The short bridges between them, and the translation of the linear-algebra conclusion back into
`A ∈ Z(SL(2,F))`, are proved here. -/

/-- The action of `A ∈ SL(2,F)` on a vector of `F²` agrees with the linear map `A.toLin'`. -/
theorem smul_eq_toLin'_apply {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) :
    A • v = (A.toLin' : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) v := by
  rw [show (A.toLin' : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) v = A.toLin' v from rfl]
  simp [Matrix.SpecialLinearGroup.smul_def, Matrix.toLin'_apply, Matrix.smul_eq_mulVec,
    Matrix.SpecialLinearGroup.toLin'_apply]

/-- A point fixed by `A ∈ SL(2,F)` spans a line invariant under the linear map `A.toLin'`. -/
theorem toLin'_rep_mem_span {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (p : P1 F) (h : A • p = p) :
    (A.toLin' : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) p.rep ∈ Submodule.span F {p.rep} := by
  rw [← smul_eq_toLin'_apply]
  exact smul_rep_mem_span A p h

/-- Distinct points of `ℙ¹(F)` have linearly independent representatives. -/
theorem linearIndependent_reps_of_ne {F : Type*} [Field F] (a b : P1 F) (h : a ≠ b) :
    LinearIndependent F ![a.rep, b.rep] := by
  have h1 : Projectivization.Independent ![(a : P1 F), b] :=
    Projectivization.independent_pair_iff_ne a b |>.mpr h
  rw [← Projectivization.mk_rep a, ← Projectivization.mk_rep b] at h1
  exact (Projectivization.independent_mk_iff_LinearIndependent (Projectivization.rep_nonzero a)
    (Projectivization.rep_nonzero b)).mp h1

/-- The representative of a point `c` distinct from `a` does not lie in the line spanned by the
representative of `a`. -/
theorem rep_not_mem_span_of_ne {F : Type*} [Field F] (a c : P1 F) (h : a ≠ c) :
    c.rep ∉ Submodule.span F {a.rep} := by
  intro hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  apply h
  rw [← Projectivization.mk_rep a, ← Projectivization.mk_rep c]
  exact ((Projectivization.mk_eq_mk_iff' F c.rep a.rep (Projectivization.rep_nonzero c)
    (Projectivization.rep_nonzero a)).mpr ⟨t, ht⟩).symm

/-- A non-identity element of `PSL(2,F)` fixes at most two points of `ℙ¹(F) = ℙ F (Fin 2 → F)`.
Lift `g` to `A : SL(2,F)` (`g ≠ 1` forces `A ∉ center`); the fixed points are the eigenlines of
`A`, and three fixed lines would force `A` to be scalar. -/
theorem ncard_fixSet_le_two (F : Type*) [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hg : g ≠ 1) :
    (Work.L2F.Props.L2Free.fixSet F g).ncard ≤ 2 := by
  classical
  obtain ⟨A, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
  refine ncard_le_two_of_not_three _ ?_
  intro a ha b hb c hc hab hac hbc
  rw [mem_fixSet_iff] at ha hb hc
  have ha' : A • a = a := by
    rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] at ha
    exact ha
  have hb' : A • b = b := by
    rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] at hb
    exact hb
  have hc' : A • c = c := by
    rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] at hc
    exact hc
  obtain ⟨cc, hcc⟩ := three_lines_smul_id (A.toLin' : (Fin 2 → F) →ₗ[F] (Fin 2 → F))
    a.rep b.rep c.rep (linearIndependent_reps_of_ne a b hab) (rep_not_mem_span_of_ne a c hac)
    (rep_not_mem_span_of_ne b c hbc) (toLin'_rep_mem_span A a ha') (toLin'_rep_mem_span A b hb')
    (toLin'_rep_mem_span A c hc')
  have hscalar : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) cc := calc
    (A : Matrix (Fin 2) (Fin 2) F)
        = LinearMap.toMatrix' (A.toLin' : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) := by
          rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.toMatrix'_toLin']
    _ = Matrix.scalar (Fin 2) cc := by
          rw [hcc]
          rw [show (cc • 1 : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) =
            algebraMap F (Module.End F (Fin 2 → F)) cc from
            (Algebra.algebraMap_eq_smul_one cc).symm]
          exact LinearMap.toMatrix'_algebraMap cc
  have hcenter : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨cc, ?_, hscalar.symm⟩
    have h1 : (Matrix.scalar (Fin 2) cc).det = cc ^ Fintype.card (Fin 2) := by simp
    have hdet : (Matrix.scalar (Fin 2) cc).det = 1 := by rw [← hscalar]; exact A.2
    rw [h1] at hdet
    exact hdet
  have hone : (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcenter
  exact hg hone

end Work.L2F.Props.L2Free
