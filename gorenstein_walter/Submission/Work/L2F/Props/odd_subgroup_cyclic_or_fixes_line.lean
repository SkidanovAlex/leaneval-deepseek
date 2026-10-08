import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Props.oddsub.range_toPGL_of_odd_card
import Submission.Work.L2F.Props.oddsub.finite_comap_toPGL
import Submission.Work.L2F.Props.oddsub.isCyclic_inf_centralizer
import Submission.Work.L2F.Props.oddsub.eq_or_trace_sub_of_commute
import Submission.Work.L2F.Props.oddsub.conj_eq_self_of_mem_zpowers
import Submission.Work.L2F.Props.oddsub.fixes_line_of_unipotent
import Submission.Work.L2F.Props.oddsub.isCyclic_of_no_unipotent

/-!
# `odd_subgroup_cyclic_or_fixes_line` — helpers

Auxiliary lemmas for `Work.L2F.Props.odd_subgroup_cyclic_or_fixes_line`:

* `toPGL_negOne_eq_one`: the central involution `-1` of `SL(2,F)` is trivial in `PGL(2,F)`;
* `eq_one_or_negOne_of_eq_smul_one`: a scalar element of `SL(2,F)` is `±1`;
* `SemisimpleSL_of_lift`: a lift of a nontrivial element of `PGL(2,F)` which is not unipotent is
  semisimple.

The main theorem is stated at the bottom.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

variable {F : Type*} [Field F]

/-- The image of the central element `-1` of `SL(2,F)` in `PGL(2,F)` is trivial. -/
theorem toPGL_negOne_eq_one (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup.toPGL (Work.L2F.negOne F) = 1 := by
  rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker, Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have h : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 := rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h, neg_mul, mul_neg,
    mul_one, one_mul]

/-- An element of `SL(2,F)` which is a scalar matrix is `1` or `-1`. -/
theorem eq_one_or_negOne_of_eq_smul_one (g : Matrix.SpecialLinearGroup (Fin 2) F) (c : F)
    (hc : ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    g = 1 ∨ g = Work.L2F.negOne F := by
  have hdet : c ^ 2 = 1 := by
    have h := congrArg Matrix.det hc
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.SpecialLinearGroup.det_coe,
      mul_one] at h
    exact h.symm
  rcases sq_eq_one_iff.mp hdet with h1 | h1
  · left
    apply Subtype.ext
    rw [hc, h1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [hc, h1, neg_smul, one_smul]
    rfl

/-- Expansion of a square: `(M - a • 1) * (M - a • 1) = M * M - (2 * a) • M + (a * a) • 1`. -/
theorem sub_smul_one_mul_self (M : Matrix (Fin 2) (Fin 2) F) (a : F) :
    (M - a • (1 : Matrix (Fin 2) (Fin 2) F)) * (M - a • (1 : Matrix (Fin 2) (Fin 2) F)) =
      M * M - (2 * a) • M + (a * a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h2M : (2 * a) • (M : Matrix (Fin 2) (Fin 2) F) = a • M + a • M := by
    rw [two_mul, add_smul]
  rw [h2M]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;> ring

/-- **A lift of a nontrivial, non-unipotent element is semisimple.**  Let `g ∈ SL(2,F)` with
`toPGL g ≠ 1`, and suppose `g` is not `λ·1 + N` with `N` nonzero nilpotent.  Then the
characteristic polynomial of `g` has two distinct roots (`SemisimpleSL g`). -/
theorem SemisimpleSL_of_lift (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hne : Matrix.SpecialLinearGroup.toPGL g ≠ 1)
    (hu : ¬ UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) :
    SemisimpleSL ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  set G : Matrix (Fin 2) (Fin 2) F := ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) with hG
  have hdet : G.det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hg1 : g ≠ 1 := fun h => hne (by rw [h, map_one])
  have hgm1 : g ≠ Work.L2F.negOne F := fun h => hne (by rw [h, toPGL_negOne_eq_one F])
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F G
  rw [hdet, one_smul] at hCH
  constructor
  · intro c hc
    rcases eq_one_or_negOne_of_eq_smul_one g c hc with h | h
    · exact hg1 h
    · exact hgm1 h
  · rcases eq_or_ne (2 : F) 0 with h2 | h2
    · -- characteristic two: `tr ≠ 0`
      right
      refine ⟨h2, ?_⟩
      intro htr
      apply hu
      refine ⟨1, ?_, ?_⟩
      · intro hzero
        apply hg1
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_one, ← hG]
        simpa using sub_eq_zero.mp hzero
      · rw [sub_smul_one_mul_self, hCH, htr, zero_smul, zero_sub]
        rw [show (2 * (1 : F)) = 0 from by rw [mul_one]; exact h2, zero_smul]
        rw [one_mul, one_smul]
        abel
    · -- odd characteristic: `tr^2 - 4 ≠ 0`
      left
      refine ⟨h2, ?_⟩
      rw [hdet, mul_one]
      intro hsq
      have hfac : (G.trace - 2) * (G.trace + 2) = 0 := by
        rw [show (G.trace - 2) * (G.trace + 2) = G.trace ^ 2 - 4 from by ring]
        exact hsq
      rcases mul_eq_zero.mp hfac with htr | htr
      · have ht : G.trace = 2 := sub_eq_zero.mp htr
        apply hu
        refine ⟨1, ?_, ?_⟩
        · intro hzero
          apply hg1
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_one, ← hG]
          simpa using sub_eq_zero.mp hzero
        · rw [sub_smul_one_mul_self, hCH, ht]
          rw [show (2 * (1 : F)) = 2 from by rw [mul_one]]
          rw [one_mul, one_smul]
          abel
      · have ht : G.trace = -2 := by simpa using eq_neg_of_add_eq_zero_left htr
        apply hu
        refine ⟨-1, ?_, ?_⟩
        · intro hzero
          apply hgm1
          apply Subtype.ext
          have hval : G = (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := sub_eq_zero.mp hzero
          rw [← hG, hval, neg_smul, one_smul]
          rfl
        · rw [sub_smul_one_mul_self, hCH, ht]
          rw [show (2 * (-1 : F)) = -2 from by ring]
          rw [show ((-1 : F) * (-1 : F)) = 1 from by ring, one_smul]
          rw [show ((-2 : F) • G) = -((2 : F) • G) from by rw [neg_smul]]
          abel

theorem odd_subgroup_cyclic_or_fixes_line (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K)) :
    IsCyclic K ∨
      ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL g ∈ K →
          ∃ c : F, Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F) v = c • v := by
  have hK : K ≤ Matrix.SpecialLinearGroup.toPGL.range :=
    Work.L2F.Props.oddsub.range_toPGL_of_odd_card F K hodd
  by_cases hu : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toPGL g ∈ K ∧
        UnipotentMatrix (g : Matrix (Fin 2) (Fin 2) F)
  · refine Or.inr ?_
    simpa only [HasCommonEigenvectorSL, Subgroup.mem_comap] using
      Work.L2F.Props.oddsub.fixes_line_of_unipotent F K hodd hK hu
  · refine Or.inl (Work.L2F.Props.oddsub.isCyclic_of_no_unipotent F K hodd hK ?_)
    rintro g hg hgu
    exact hu ⟨g, hg, hgu⟩

end Work.L2F.Props
