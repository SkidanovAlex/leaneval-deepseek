import Mathlib
import Submission.Work.L2F.Props.L2Free.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

namespace Work.L2F.Props.L2Free

variable (F : Type*) [Field F]

/-! ## The stabilizer of the base point `[1:0]`

These two lemmas are the local, `AUTL2`-free versions of
`Work.L2F.Props.TwoSylow.pslStab_infty_eq_normalizer`, expressed in the Mathlib model
`P1 F = ℙ F (Fin 2 → F)`. -/

/-- The vector `M • ![1,0]` is the first column of the matrix `M`. -/
lemma sl_smul_of_vecOne (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    M • (![1, 0] : Fin 2 → F) = ![((M : Matrix (Fin 2) (Fin 2) F)) 0 0,
      ((M : Matrix (Fin 2) (Fin 2) F)) 1 0] := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead]

/-- A matrix `M ∈ SL(2,F)` maps into the stabilizer of the base point `inf F = [1:0]` exactly
when it is upper triangular: `(M : PSL(2,F)) • [1:0] = [1:0]` iff the first column of `M` is a
multiple of `![1,0]` iff `M 1 0 = 0`. -/
lemma pslMap_mem_pslStab_inf_iff (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F M ∈ pslStab F (inf F) ↔
      (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [mem_pslStab_iff]
  rw [show Work.PSL2.pslMap F M = (M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) from rfl]
  simp only [inf, Work.PSL2.ptInf]
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrArg (fun v : Fin 2 → F => v 1) ha
    rw [sl_smul_of_vecOne F M] at h1
    simpa using h1.symm
  · intro h
    refine ⟨((M : Matrix (Fin 2) (Fin 2) F)) 0 0, ?_⟩
    rw [sl_smul_of_vecOne F M]
    ext i
    fin_cases i <;> simp [h]

/-- The stabilizer of `inf F = [1:0]` in `PSL(2,F)` is the normalizer of the unipotent subgroup:
both are the image of the upper triangular matrices under the quotient map. -/
lemma pslStab_inf_eq_normalizer (h2 : (2 : F) ≠ 0) :
    pslStab F (inf F) =
      Subgroup.normalizer (Work.L2F.pslUnipotent F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
  have hcomap : Subgroup.comap (Work.PSL2.pslMap F) (pslStab F (inf F)) =
      Subgroup.comap (Work.PSL2.pslMap F)
        (Subgroup.normalizer (Work.L2F.pslUnipotent F :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) := by
    ext M
    rw [Subgroup.mem_comap, Subgroup.mem_comap, pslMap_mem_pslStab_inf_iff F M,
      (Work.L2F.PSL.pslMap_mem_normalizer_iff_mem_borel F h2 M).trans
        (Work.L2F.Conic.mem_borel F M)]
  have hrange : (Work.PSL2.pslMap F).range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  calc pslStab F (inf F)
      = Subgroup.map (Work.PSL2.pslMap F) (Subgroup.comap (Work.PSL2.pslMap F)
          (pslStab F (inf F))) := by
        rw [Subgroup.map_comap_eq, hrange, top_inf_eq]
    _ = Subgroup.map (Work.PSL2.pslMap F) (Subgroup.comap (Work.PSL2.pslMap F)
          (Subgroup.normalizer (Work.L2F.pslUnipotent F :
            Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))) := by rw [hcomap]
    _ = Subgroup.normalizer (Work.L2F.pslUnipotent F :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
        rw [Subgroup.map_comap_eq, hrange, top_inf_eq]

/-- Every point stabilizer in `PSL(2,F)` (`F` finite of odd characteristic) has `q(q-1)/2`
elements, `q = Nat.card F`; stated fraction-free.  Reduce by transitivity plus
`Work.L2F.Props.L2Free.pslStab_smul_conj` to the base point `inf F = Work.PSL2.ptInf F`, whose
stabilizer is the normalizer of `Work.L2F.pslUnipotent F` (which you may reprove locally); then use
`Work.L2F.PSL.normalizer_pslUnipotent_card`. -/
theorem pslStab_card (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (x : Work.L2F.Props.L2Free.P1 F) :
    2 * Nat.card (Work.L2F.Props.L2Free.pslStab F x) = Nat.card F * (Nat.card F - 1) := by
  obtain ⟨g, hg⟩ : ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      g • inf F = x := MulAction.exists_smul_eq _ _ _
  have hcard : Nat.card (pslStab F x) = Nat.card (pslStab F (inf F)) := by
    rw [← hg, pslStab_smul_conj F g (inf F)]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hcard, pslStab_inf_eq_normalizer F h2]
  exact Work.L2F.PSL.normalizer_pslUnipotent_card F h2

end Work.L2F.Props.L2Free
