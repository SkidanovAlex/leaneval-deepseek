/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the action morphism and its chart descriptions.

The action is obtained by gluing the two chart morphisms `srcChartHom k 0` and `srcChartHom k 1`
along the cover of `srcScheme k = ℙ¹ × Spec k[T;T⁻¹]` by the two charts `D₊(X₀) × 𝔾_m` and
`D₊(X₁) × 𝔾_m`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.SourceChart
import Submission.Work.AbVar.P1Action.srcChart_range
import Submission.Work.AbVar.P1Action.srcChart_cover
import Submission.Work.AbVar.P1Action.srcCover_overlap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- The two charts cover the source `ℙ¹ ⊗ 𝔾_m`. -/
theorem srcChartι_iSup_opensRange :
    (⨆ i, (srcChartι k i).opensRange) = ⊤ :=
  srcChart_cover k

/-- The cover of the source by the two charts `D₊(Xᵢ) × 𝔾_m`. -/
noncomputable abbrev srcCover : (srcScheme k).OpenCover where
  I₀ := Fin 2
  X i := Spec (CommRingCat.of (srcChartRing k i))
  f i := srcChartι k i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : x ∈ (⨆ i, (srcChartι k i).opensRange) := by
      rw [srcChartι_iSup_opensRange k]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, hi⟩

/-- The chart morphisms agree on the overlap of the two charts. -/
theorem srcCover_compat :
    pullback.fst (srcChartι k 0) (srcChartι k 1) ≫ srcChartHom k 0
      = pullback.snd (srcChartι k 0) (srcChartι k 1) ≫ srcChartHom k 1 :=
  srcCover_overlap k

/-- The overlap compatibility in the opposite order. -/
theorem srcCover_compat_swap :
    pullback.fst (srcChartι k 1) (srcChartι k 0) ≫ srcChartHom k 1
      = pullback.snd (srcChartι k 1) (srcChartι k 0) ≫ srcChartHom k 0 := by
  have h := congrArg (fun t => (pullbackSymmetry (srcChartι k 0) (srcChartι k 1)).inv ≫ t)
    (srcCover_compat k)
  simp only [← Category.assoc] at h
  rw [pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd] at h
  exact h.symm

/-- The compatibility of the chart morphism with itself on the double chart. -/
theorem srcChartι_diag_compat (i : Fin 2) :
    pullback.fst (srcChartι k i) (srcChartι k i) ≫ srcChartHom k i
      = pullback.snd (srcChartι k i) (srcChartι k i) ≫ srcChartHom k i := by
  haveI : Mono (srcChartι k i) := inferInstance
  rw [fst_eq_snd_of_mono_eq (srcChartι k i)]

/-- The scaling action on the source `ℙ¹ ⊗ 𝔾_m`. -/
noncomputable def scalingActLeft : srcScheme k ⟶ (Work.AbVar.P1 k).left :=
  (srcCover k).glueMorphisms (fun i => srcChartHom k i) (by
    intro i j
    fin_cases i <;> fin_cases j
    · exact srcChartι_diag_compat k 0
    · exact srcCover_compat k
    · exact srcCover_compat_swap k
    · exact srcChartι_diag_compat k 1)

/-- The chart description of `scalingActLeft`. -/
theorem srcChartι_scalingActLeft (i : Fin 2) :
    srcChartι k i ≫ scalingActLeft k = srcChartHom k i :=
  Scheme.Cover.ι_glueMorphisms _ _ _ _

/-- The structure morphism of `scalingActLeft`. -/
theorem scalingActLeft_hom :
    scalingActLeft k ≫ (Work.AbVar.P1 k).hom
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ≫ (Work.AbVar.P1 k).hom := by
  apply (srcCover k).hom_ext
  intro i
  rw [← Category.assoc, srcChartι_scalingActLeft, srcChartHom_hom, ← Category.assoc,
    srcChartι_fst, Category.assoc, chartObjHom_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The scaling action `ℙ¹ ⊗ 𝔾_m ⟶ ℙ¹`. -/
noncomputable def scalingAct : Work.AbVar.P1 k ⊗ Work.AbVar.Gm k ⟶ Work.AbVar.P1 k :=
  Over.homMk (scalingActLeft k : (Work.AbVar.P1 k ⊗ Work.AbVar.Gm k).left ⟶ (Work.AbVar.P1 k).left)
    (by
      show (scalingActLeft k : (Work.AbVar.P1 k ⊗ Work.AbVar.Gm k).left ⟶ (Work.AbVar.P1 k).left)
          ≫ (Work.AbVar.P1 k).hom = pullback.fst (Work.AbVar.P1 k).hom (Work.AbVar.Gm k).hom
            ≫ (Work.AbVar.P1 k).hom
      rw [scalingActLeft_hom]
      rfl)

/-- The chart description of the scaling action. -/
theorem srcChartι_scalingAct (i : Fin 2) :
    srcChartι k i ≫ (scalingAct k).left = srcChartHom k i := by
  show srcChartι k i ≫ scalingActLeft k = srcChartHom k i
  exact srcChartι_scalingActLeft k i

end

end Work.AbVar.P1Action
