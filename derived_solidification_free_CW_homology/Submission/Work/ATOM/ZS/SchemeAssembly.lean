import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Assembly
import Submission.Work.ATOM.homK_pre_oneMinusShift_bijective
import Submission.Work.ATOM.homD_pre_oneMinusShift_bijective
import Submission.Work.ATOM.ZS.Data
import Submission.Work.ANALYTIC.scheme_bijective

/-!
# AREA ATOM: the null-sequence scheme in `K` and `D`

This file contains the *assembly* of the null-sequence trick of REFS/03 §1 for the reduced free
object `ℤ̃[S] = zred S s₀`.  The explicit maps `g̃, F, s, G, F_P, s_P, m` and the seven identities
are supplied as hypotheses (they are constructed in `Submission/Work/ATOM/ZS/NullSeqMaps.lean`);
what is proved here is that *any* such data makes `ℤ̃[S]` solid-cofibrant:

* apply `Work.ANALYTIC.scheme_bijective` in the homotopy category `K(LightCondAb)` with
  `D = hq (ιC N)`, where the hypothesis `hT` is F7 in `K`
  (`Work.ATOM.homK_pre_oneMinusShift_bijective`);
* apply it in `D(LightCondAb)` with `D = Q (ιC N)`, where `hT` is F7 in `D`
  (`Work.ATOM.homD_pre_oneMinusShift_bijective`);
* conclude with `Work.ATOM.solidCofibrant_of_bijective_pre`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- **The null-sequence scheme for `ℤ̃[S]`.**  Given the maps of REFS/03 §1 and the seven
identities (at the level of `LightCondAb`), the atom on the reduced free object `ℤ̃[S]` is
solid-cofibrant. -/
theorem solidCofibrant_zred_of_schemeData (S : LightProfinite.{0}) [Infinite S] (n : ℤ)
    [CategoryTheory.Limits.PreservesFiniteLimits (MonoidalCategory.tensorLeft P)]
    (g : P ⟶ zred S (levelData S).s₀)
    (F : tmul P (zfree S) ⟶ zred S (levelData S).s₀)
    (s : zred S (levelData S).s₀ ⟶ tmul P (zfree S))
    (G : tmul P (zfree S) ⟶ P)
    (FP : tmul P P ⟶ P)
    (sP : P ⟶ tmul P P)
    (m : tmul P P ⟶ tmul P (zfree S))
    (h₁ : preShift (zfree S) ≫ F = G ≫ g)
    (h₂ : s ≫ F = 𝟙 (zred S (levelData S).s₀))
    (h₃ : m ≫ F = FP ≫ g)
    (h₄ : m ≫ G = preShiftP ≫ FP)
    (h₅ : g ≫ s = sP ≫ m)
    (h₆ : m ≫ preShift (zfree S) = preShiftP ≫ m)
    (h₇ : sP ≫ FP = 𝟙 P) :
    Submission.Blueprint.SolidCofibrant ((singleC n).obj (zred S (levelData S).s₀)) := by
  -- the seven identities, transported along `(singleC n).map` and a functor `Φ` out of complexes
  have m₁ : (singleC n).map (preShift (zfree S)) ≫ (singleC n).map F =
      (singleC n).map G ≫ (singleC n).map g := by
    rw [← (singleC n).map_comp, ← (singleC n).map_comp, h₁]
  have m₂ : (singleC n).map s ≫ (singleC n).map F = (singleC n).map (𝟙 (zred S (levelData S).s₀)) := by
    rw [← (singleC n).map_comp, h₂]
  have m₃ : (singleC n).map m ≫ (singleC n).map F = (singleC n).map FP ≫ (singleC n).map g := by
    rw [← (singleC n).map_comp, ← (singleC n).map_comp, h₃]
  have m₄ : (singleC n).map m ≫ (singleC n).map G = (singleC n).map preShiftP ≫ (singleC n).map FP := by
    rw [← (singleC n).map_comp, ← (singleC n).map_comp, h₄]
  have m₅ : (singleC n).map g ≫ (singleC n).map s = (singleC n).map sP ≫ (singleC n).map m := by
    rw [← (singleC n).map_comp, ← (singleC n).map_comp, h₅]
  have m₆ : (singleC n).map m ≫ (singleC n).map (preShift (zfree S)) =
      (singleC n).map preShiftP ≫ (singleC n).map m := by
    rw [← (singleC n).map_comp, ← (singleC n).map_comp, h₆]
  have m₇ : (singleC n).map sP ≫ (singleC n).map FP = (singleC n).map (𝟙 P) := by
    rw [← (singleC n).map_comp, h₇]
  -- the same, in an arbitrary target category
  have k₁K : hq.map ((singleC n).map (preShift (zfree S))) ≫ hq.map ((singleC n).map F) =
      hq.map ((singleC n).map G) ≫ hq.map ((singleC n).map g) := by
    rw [← hq.map_comp, ← hq.map_comp, ← (singleC n).map_comp, ← (singleC n).map_comp, h₁]
  have k₂K : hq.map ((singleC n).map s) ≫ hq.map ((singleC n).map F) =
      𝟙 (hq.obj ((singleC n).obj (zred S (levelData S).s₀))) := by
    rw [← hq.map_comp, ← (singleC n).map_comp, h₂, (singleC n).map_id, hq.map_id]
  have k₃K : hq.map ((singleC n).map m) ≫ hq.map ((singleC n).map F) =
      hq.map ((singleC n).map FP) ≫ hq.map ((singleC n).map g) := by
    rw [← hq.map_comp, ← hq.map_comp, ← (singleC n).map_comp, ← (singleC n).map_comp, h₃]
  have k₄K : hq.map ((singleC n).map m) ≫ hq.map ((singleC n).map G) =
      hq.map ((singleC n).map preShiftP) ≫ hq.map ((singleC n).map FP) := by
    rw [← hq.map_comp, ← hq.map_comp, ← (singleC n).map_comp, ← (singleC n).map_comp, h₄]
  have k₅K : hq.map ((singleC n).map g) ≫ hq.map ((singleC n).map s) =
      hq.map ((singleC n).map sP) ≫ hq.map ((singleC n).map m) := by
    rw [← hq.map_comp, ← hq.map_comp, ← (singleC n).map_comp, ← (singleC n).map_comp, h₅]
  have k₆K : hq.map ((singleC n).map m) ≫ hq.map ((singleC n).map (preShift (zfree S))) =
      hq.map ((singleC n).map preShiftP) ≫ hq.map ((singleC n).map m) := by
    rw [← hq.map_comp, ← hq.map_comp, ← (singleC n).map_comp, ← (singleC n).map_comp, h₆]
  have k₇K : hq.map ((singleC n).map sP) ≫ hq.map ((singleC n).map FP) =
      𝟙 (hq.obj ((singleC n).obj P)) := by
    rw [← hq.map_comp, ← (singleC n).map_comp, h₇, (singleC n).map_id, hq.map_id]
  have k₁D : DerivedCategory.Q.map ((singleC n).map (preShift (zfree S))) ≫
        DerivedCategory.Q.map ((singleC n).map F) =
      DerivedCategory.Q.map ((singleC n).map G) ≫ DerivedCategory.Q.map ((singleC n).map g) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (singleC n).map_comp, ← (singleC n).map_comp, h₁]
  have k₂D : DerivedCategory.Q.map ((singleC n).map s) ≫
        DerivedCategory.Q.map ((singleC n).map F) =
      𝟙 (DerivedCategory.Q.obj ((singleC n).obj (zred S (levelData S).s₀))) := by
    rw [← DerivedCategory.Q.map_comp, ← (singleC n).map_comp, h₂, (singleC n).map_id,
      DerivedCategory.Q.map_id]
  have k₃D : DerivedCategory.Q.map ((singleC n).map m) ≫
        DerivedCategory.Q.map ((singleC n).map F) =
      DerivedCategory.Q.map ((singleC n).map FP) ≫
        DerivedCategory.Q.map ((singleC n).map g) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (singleC n).map_comp, ← (singleC n).map_comp, h₃]
  have k₄D : DerivedCategory.Q.map ((singleC n).map m) ≫
        DerivedCategory.Q.map ((singleC n).map G) =
      DerivedCategory.Q.map ((singleC n).map preShiftP) ≫
        DerivedCategory.Q.map ((singleC n).map FP) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (singleC n).map_comp, ← (singleC n).map_comp, h₄]
  have k₅D : DerivedCategory.Q.map ((singleC n).map g) ≫
        DerivedCategory.Q.map ((singleC n).map s) =
      DerivedCategory.Q.map ((singleC n).map sP) ≫ DerivedCategory.Q.map ((singleC n).map m) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (singleC n).map_comp, ← (singleC n).map_comp, h₅]
  have k₆D : DerivedCategory.Q.map ((singleC n).map m) ≫
        DerivedCategory.Q.map ((singleC n).map (preShift (zfree S))) =
      DerivedCategory.Q.map ((singleC n).map preShiftP) ≫
        DerivedCategory.Q.map ((singleC n).map m) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← (singleC n).map_comp, ← (singleC n).map_comp, h₆]
  have k₇D : DerivedCategory.Q.map ((singleC n).map sP) ≫
        DerivedCategory.Q.map ((singleC n).map FP) =
      𝟙 (DerivedCategory.Q.obj ((singleC n).obj P)) := by
    rw [← DerivedCategory.Q.map_comp, ← (singleC n).map_comp, h₇, (singleC n).map_id,
      DerivedCategory.Q.map_id]
  have hK : ∀ N : CochainComplex Solid ℤ,
      Function.Bijective (fun φ : hq.obj ((singleC n).obj (zred S (levelData S).s₀)) ⟶
          hq.obj (Submission.Blueprint.ιC.obj N) =>
        hq.map ((singleC n).map g) ≫ φ) := by
    intro N
    exact Work.ANALYTIC.scheme_bijective (C := HomotopyCategory LightCondAb (ComplexShape.up ℤ))
      (hq.map ((singleC n).map g)) (hq.map ((singleC n).map F)) (hq.map ((singleC n).map s))
      (hq.map ((singleC n).map G)) (hq.map ((singleC n).map (preShift (zfree S))))
      (hq.map ((singleC n).map FP)) (hq.map ((singleC n).map sP))
      (hq.map ((singleC n).map preShiftP)) (hq.map ((singleC n).map m))
      k₁K k₂K k₃K k₄K k₅K k₆K k₇K
      (homK_pre_oneMinusShift_bijective N n (zfree S))
      (homK_pre_oneMinusShift_bijective N n P)
  have hD : ∀ N : CochainComplex Solid ℤ,
      Function.Bijective (fun ψ : DerivedCategory.Q.obj
          ((singleC n).obj (zred S (levelData S).s₀)) ⟶
          DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
        DerivedCategory.Q.map ((singleC n).map g) ≫ ψ) := by
    intro N
    exact Work.ANALYTIC.scheme_bijective (C := DerivedCategory LightCondAb)
      (DerivedCategory.Q.map ((singleC n).map g))
      (DerivedCategory.Q.map ((singleC n).map F))
      (DerivedCategory.Q.map ((singleC n).map s))
      (DerivedCategory.Q.map ((singleC n).map G))
      (DerivedCategory.Q.map ((singleC n).map (preShift (zfree S))))
      (DerivedCategory.Q.map ((singleC n).map FP))
      (DerivedCategory.Q.map ((singleC n).map sP))
      (DerivedCategory.Q.map ((singleC n).map preShiftP))
      (DerivedCategory.Q.map ((singleC n).map m))
      k₁D k₂D k₃D k₄D k₅D k₆D k₇D
      (homD_pre_oneMinusShift_bijective N n (zfree S))
      (homD_pre_oneMinusShift_bijective N n P)
  exact solidCofibrant_of_bijective_pre (zred S (levelData S).s₀) g n hK hD

end Work.ATOM
