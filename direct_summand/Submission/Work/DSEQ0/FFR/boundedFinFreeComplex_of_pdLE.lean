import Mathlib
import Submission.Work.DSEQ0.bounded_free_model_of_triangle
import Submission.Work.DSEQ0.exists_bounded_free_model
import Submission.Work.DSEQ0.FFR.oneStep_model_of_shortExact
import Submission.Work.DSEQ0.FFR.free_of_hasProjectiveDimensionLE_zero

namespace Work.DSEQ0.FFR

universe u

open CategoryTheory Limits Pretriangulated

set_option linter.style.haveILetI false

section Helpers

variable {R : Type u} [CommRing R]

/-- A zero object of `ModuleCat R` is a finite module. -/
lemma moduleFinite_of_isZero {X : ModuleCat.{u} R} (hX : IsZero X) : Module.Finite R X := by
  haveI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  infer_instance

/-- A zero object of `ModuleCat R` is a free module. -/
lemma moduleFree_of_isZero {X : ModuleCat.{u} R} (hX : IsZero X) : Module.Free R X := by
  haveI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  infer_instance

/-- Shifting preserves "finite free terms, supported in a window". -/
lemma shiftFunctor_bdd_finFree (G : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (G.X j)) (hfree : ∀ j, Module.Free R (G.X j))
    (hbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (G.X j)) (n : ℤ) :
    (∀ j, Module.Finite R (((CochainComplex.shiftFunctor (ModuleCat.{u} R) n).obj G).X j)) ∧
      (∀ j, Module.Free R (((CochainComplex.shiftFunctor (ModuleCat.{u} R) n).obj G).X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j →
        IsZero (((CochainComplex.shiftFunctor (ModuleCat.{u} R) n).obj G).X j)) := by
  obtain ⟨a, b, hb⟩ := hbdd
  refine ⟨fun j => ?_, fun j => ?_, ⟨a - n, b - n, fun j hj => ?_⟩⟩
  · simpa only [CochainComplex.shiftFunctor_obj_X, add_comm] using hfin (j + n)
  · simpa only [CochainComplex.shiftFunctor_obj_X, add_comm] using hfree (j + n)
  · rcases hj with hj | hj
    · exact hb (j + n) (Or.inl (by omega))
    · exact hb (j + n) (Or.inr (by omega))

end Helpers


section Main

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Auxiliary form of the main theorem, proved by induction on the bound `n` on the projective
dimension. -/
theorem exists_model_aux :
    ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M → ∀ (i : ℤ),
      CategoryTheory.HasProjectiveDimensionLE M n →
      ∃ (G : CochainComplex (ModuleCat.{u} R) ℤ),
        (∀ j, Module.Finite R (G.X j)) ∧ (∀ j, Module.Free R (G.X j)) ∧
        (∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (G.X j)) ∧
        ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M,
          QuasiIso g := by
  intro n
  induction n with
  | zero =>
    intro M hM i h
    haveI : Module.Finite R M := hM
    have hfree : Module.Free R M :=
      free_of_hasProjectiveDimensionLE_zero R M h
    refine ⟨(HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M,
      ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj; rw [HomologicalComplex.single_obj_X_self]; exact hM
      · exact moduleFinite_of_isZero (HomologicalComplex.isZero_single_obj_X _ i M j hj)
    · intro j
      by_cases hj : j = i
      · subst hj; rw [HomologicalComplex.single_obj_X_self]; exact hfree
      · exact moduleFree_of_isZero (HomologicalComplex.isZero_single_obj_X _ i M j hj)
    · exact ⟨i, i, fun j hj => by
        rcases hj with hj | hj
        · exact HomologicalComplex.isZero_single_obj_X _ i M j (by omega)
        · exact HomologicalComplex.isZero_single_obj_X _ i M j (by omega)⟩
    · exact ⟨𝟙 _, inferInstance⟩
  | succ n ih =>
    intro M hM i h
    haveI : Module.Finite R M := hM
    -- A finite free cover of `M`, and its kernel.
    obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := ↥M)
    let f : (Fin m → R) →ₗ[R] ↥M := Fintype.linearCombination R s
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
      exact hs
    have hS : (f.shortComplexKer).ShortExact := LinearMap.shortExact_shortComplexKer hf
    -- The kernel is finite, its projective dimension drops by one.
    have hKfin : Module.Finite R (f.shortComplexKer).X₁ := by
      change Module.Finite R ↥(LinearMap.ker f)
      rw [Module.Finite.iff_fg]
      exact (isNoetherian_def.mp
        (isNoetherian_of_isNoetherianRing_of_finite R (Fin m → R))) (LinearMap.ker f)
    haveI : Projective (f.shortComplexKer).X₂ := by
      change Projective (ModuleCat.of R (Fin m → R))
      exact ModuleCat.projective_of_free (Pi.basisFun R (Fin m))
    have h2 : CategoryTheory.HasProjectiveDimensionLT (f.shortComplexKer).X₂ (n + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
    have h3 : CategoryTheory.HasProjectiveDimensionLT (f.shortComplexKer).X₃ (n + 2) := h
    have hKpd : CategoryTheory.HasProjectiveDimensionLT (f.shortComplexKer).X₁ (n + 1) :=
      hS.hasProjectiveDimensionLT_X₁ (n + 1) h2 h3
    obtain ⟨G, hGfin, hGfree, hGbdd, q, hq⟩ := ih _ hKfin i hKpd
    -- Splice the model of the kernel with the free cover.
    have hX2fin : Module.Finite R (f.shortComplexKer).X₂ := by
      change Module.Finite R (Fin m → R)
      infer_instance
    have hX2free : Module.Free R (f.shortComplexKer).X₂ := by
      change Module.Free R (Fin m → R)
      infer_instance
    have hres := oneStep_model_of_shortExact R (f.shortComplexKer) hS hX2fin hX2free i
      G hGfin hGfree hGbdd q hq
    simpa only [ModuleCat.of_coe] using hres

end Main

theorem boundedFinFreeComplex_of_pdLE (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℤ) (h : CategoryTheory.HasProjectiveDimensionLE M n) : ∃ (G : CochainComplex (ModuleCat.{u} R) ℤ), (∀ j, Module.Finite R (G.X j)) ∧ (∀ j, Module.Free R (G.X j)) ∧ (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧ ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M, QuasiIso g := by
  exact exists_model_aux n M ‹Module.Finite R M› i h

end Work.DSEQ0.FFR
