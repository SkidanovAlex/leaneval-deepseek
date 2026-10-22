import Mathlib
import Submission.Work.ATOM.Main

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

/-- **The null-sequence scheme in the derived category.**  Given the maps `g, F, s, G, F_P, s_P, m`
of REFS/03 §1 (here written with `CategoryTheory.CategoryStruct.comp`) for a null sequence
`g : P ⟶ W`, together with the seven identities `h₁`–`h₇` at the level of `LightCondAb`,
precomposition with `Q ((singleC n).map g)` is bijective on `Hom_D(Q (singleC n W), Q (ιC N))`
for every complex `N` of solid objects.  This is the D-half of
`Work.ATOM.solidCofibrant_zred_of_schemeData` with `ℤ̃[S]` replaced by an arbitrary `W`, isolated
so that it can be used without the `SolidCofibrant` wrapper. -/
theorem bijective_schemeD (S : LightProfinite.{0}) (n : ℤ)
    [CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft LightCondensed.P)]
    {W : LightCondAb}
    (g : LightCondensed.P ⟶ W)
    (F : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ W)
    (s : W ⟶ Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S))
    (G : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ LightCondensed.P)
    (FP : Work.ATOM.tmul LightCondensed.P LightCondensed.P ⟶ LightCondensed.P)
    (sP : LightCondensed.P ⟶ Work.ATOM.tmul LightCondensed.P LightCondensed.P)
    (m : Work.ATOM.tmul LightCondensed.P LightCondensed.P ⟶ Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S))
    (h₁ : CategoryTheory.CategoryStruct.comp (Work.ATOM.preShift (Work.ATOM.zfree S)) F = CategoryTheory.CategoryStruct.comp G g)
    (h₂ : CategoryTheory.CategoryStruct.comp s F = CategoryTheory.CategoryStruct.id W)
    (h₃ : CategoryTheory.CategoryStruct.comp m F = CategoryTheory.CategoryStruct.comp FP g)
    (h₄ : CategoryTheory.CategoryStruct.comp m G = CategoryTheory.CategoryStruct.comp Work.ATOM.preShiftP FP)
    (h₅ : CategoryTheory.CategoryStruct.comp g s = CategoryTheory.CategoryStruct.comp sP m)
    (h₆ : CategoryTheory.CategoryStruct.comp m (Work.ATOM.preShift (Work.ATOM.zfree S)) = CategoryTheory.CategoryStruct.comp Work.ATOM.preShiftP m)
    (h₇ : CategoryTheory.CategoryStruct.comp sP FP = CategoryTheory.CategoryStruct.id LightCondensed.P) :
    ∀ N : CochainComplex LightCondensed.Solid ℤ,
      Function.Bijective (fun ψ : DerivedCategory.Q.obj ((Work.ATOM.singleC n).obj W) ⟶
          DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
        CategoryTheory.CategoryStruct.comp (DerivedCategory.Q.map ((Work.ATOM.singleC n).map g)) ψ) := by
  -- Transport the seven identities of the scheme along `Q ∘ (singleC n).map`.
  have k₁D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map (Work.ATOM.preShift (Work.ATOM.zfree S))) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map F) =
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map G) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map g) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (Work.ATOM.singleC n).map_comp, ← (Work.ATOM.singleC n).map_comp, h₁]
  have k₂D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map s) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map F) =
      𝟙 (DerivedCategory.Q.obj ((Work.ATOM.singleC n).obj W)) := by
    rw [← DerivedCategory.Q.map_comp, ← (Work.ATOM.singleC n).map_comp, h₂,
      (Work.ATOM.singleC n).map_id, DerivedCategory.Q.map_id]
  have k₃D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map m) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map F) =
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map FP) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map g) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (Work.ATOM.singleC n).map_comp, ← (Work.ATOM.singleC n).map_comp, h₃]
  have k₄D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map m) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map G) =
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map Work.ATOM.preShiftP) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map FP) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (Work.ATOM.singleC n).map_comp, ← (Work.ATOM.singleC n).map_comp, h₄]
  have k₅D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map g) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map s) =
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map sP) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map m) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (Work.ATOM.singleC n).map_comp, ← (Work.ATOM.singleC n).map_comp, h₅]
  have k₆D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map m) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map (Work.ATOM.preShift (Work.ATOM.zfree S))) =
      DerivedCategory.Q.map ((Work.ATOM.singleC n).map Work.ATOM.preShiftP) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map m) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (Work.ATOM.singleC n).map_comp, ← (Work.ATOM.singleC n).map_comp, h₆]
  have k₇D : DerivedCategory.Q.map ((Work.ATOM.singleC n).map sP) ≫
        DerivedCategory.Q.map ((Work.ATOM.singleC n).map FP) =
      𝟙 (DerivedCategory.Q.obj ((Work.ATOM.singleC n).obj LightCondensed.P)) := by
    rw [← DerivedCategory.Q.map_comp, ← (Work.ATOM.singleC n).map_comp, h₇,
      (Work.ATOM.singleC n).map_id, DerivedCategory.Q.map_id]
  intro N
  exact Work.ANALYTIC.scheme_bijective (C := DerivedCategory LightCondAb)
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map g))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map F))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map s))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map G))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map (Work.ATOM.preShift (Work.ATOM.zfree S))))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map FP))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map sP))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map Work.ATOM.preShiftP))
    (DerivedCategory.Q.map ((Work.ATOM.singleC n).map m))
    k₁D k₂D k₃D k₄D k₅D k₆D k₇D
    (Work.ATOM.homD_pre_oneMinusShift_bijective N n (Work.ATOM.zfree S))
    (Work.ATOM.homD_pre_oneMinusShift_bijective N n LightCondensed.P)

end Work.ANALYTIC
