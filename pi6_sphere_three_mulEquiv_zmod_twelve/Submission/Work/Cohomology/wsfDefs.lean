import Mathlib
import Submission.Work.Cohomology.pd_glue_defs

/-!
# The relative cochain complex `C^*(U, U∩A)` and restrictions

Vocabulary for `Work.Cohomology.subsingleton_pdCohSub_union_of_wellFounded`.

For `X` a topological space, `A ⊆ X` and `U ⊆ X`:

* `rcSet A U = C^*(U, U∩A)` is the relative cochain complex of the pair `(U, U∩A)`;
* `rcKern A U n` is its degree-`n` part (relative `n`-cochains, a submodule of the singular
  `n`-cochains of `U`), with differential `rcDiff A U n`;
* for `S ⊆ T`, `rcRes A h : rcSet A T ⟶ rcSet A S` is the restriction of relative cochains, whose
  degree-`n` component is `ModuleCat.ofHom (rcResLM A h n)`.

The file records the value formula of `rcResLM`, its commutation with the differential
(`rcResLM_comm`), its functoriality (`rcResLM_comp`) and the induced functoriality of `rcRes`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {X : Type} [TopologicalSpace X] (A : Set X)

/-- The relative cochain complex `C^*(U, U ∩ A)` of the pair `(U, U∩A)`, for `U ⊆ X`. -/
abbrev rcSet (U : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  relComplex ℤ (TopCat.of U) {y : U | (y : X) ∈ A}

/-- The relative `n`-cochains of `U`: cochains on `U` vanishing on chains lying in `A`. -/
abbrev rcKern (U : Set X) (n : ℕ) : Submodule ℤ
    ↥((singularCochainComplex ℤ (TopCat.of U)).X n) :=
  relKern ℤ (TopCat.of U) {y : U | (y : X) ∈ A} n

/-- The differential of the relative cochain complex on relative cochains. -/
abbrev rcDiff (U : Set X) (n : ℕ) : ↥(rcKern A U n) →ₗ[ℤ] ↥(rcKern A U (n+1)) :=
  relDiffLM ℤ (TopCat.of U) {y : U | (y : X) ∈ A} n

/-- The `n`-th differential of `rcSet`. -/
theorem rcSet_d (U : Set X) (n : ℕ) :
    (rcSet A U).d n (n+1) = ModuleCat.ofHom (rcDiff A U n) :=
  relComplex_d ℤ (TopCat.of U) {y : U | (y : X) ∈ A} n

/-- The value of the relative differential. -/
theorem rcDiff_coe (U : Set X) (n : ℕ) (x : ↥(rcKern A U n)) :
    ((rcDiff A U n x : ↥(rcKern A U (n+1))) :
      ↥((singularCochainComplex ℤ (TopCat.of U)).X (n+1))) =
      ((singularCochainComplex ℤ (TopCat.of U)).d n (n+1)).hom
        (x : ↥((singularCochainComplex ℤ (TopCat.of U)).X n)) :=
  relDiffLM_coe ℤ (TopCat.of U) {y : U | (y : X) ∈ A} n x

/-- The underlying linear map of the restriction of relative cochains along `S ⊆ T`. -/
abbrev rcResLM {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    ↥(rcKern A T n) →ₗ[ℤ] ↥(rcKern A S n) :=
  relMapLM (R := ℤ) (X₁ := TopCat.of S) (X₂ := TopCat.of T)
    (A₁ := {y : S | (y : X) ∈ A}) (A₂ := {y : T | (y : X) ∈ A})
    (f := pdIncl (M := TopCat.of X) T S h) (fun y hy => hy) n

/-- The value of the restriction map. -/
theorem rcResLM_coe {S T : Set X} (h : S ⊆ T) (n : ℕ) (x : ↥(rcKern A T n)) :
    ((rcResLM A h n x : ↥(rcKern A S n)) :
      ↥((singularCochainComplex ℤ (TopCat.of S)).X n)) =
      (ModuleCat.Hom.hom
        ((dualChainMap ℤ (TopCat.of S) (TopCat.of T)
          (pdIncl (M := TopCat.of X) T S h)).f n))
        (x : ↥((singularCochainComplex ℤ (TopCat.of T)).X n)) :=
  relMapLM_coe ℤ _ _ (pdIncl (M := TopCat.of X) T S h) (fun y hy => hy) n x

/-- The inclusion `pdIncl` is the identity when the sets coincide. -/
theorem pdIncl_self (M : TopCat) (S : Set M) (h : S ⊆ S) :
    pdIncl S S h = 𝟙 (TopCat.of S) := by
  apply TopCat.ext
  intro y
  rfl

/-- The inclusion `pdIncl` is compatible with composition. -/
theorem pdIncl_comp {M : TopCat} {S S' T : Set M} (h : S ⊆ S') (h' : S' ⊆ T) :
    pdIncl S' S h ≫ pdIncl T S' h' = pdIncl T S (h.trans h') := by
  apply TopCat.ext
  intro y
  rfl

/-- **Naturality of the restriction**: for `S ⊆ T` the restriction commutes with the differentials,
`rcResLM A h (n+1) (rcDiff A T n x) = rcDiff A S n (rcResLM A h n x)`. -/
theorem rcResLM_comm {S T : Set X} (h : S ⊆ T) (n : ℕ) (x : ↥(rcKern A T n)) :
    rcResLM A h (n+1) (rcDiff A T n x) = rcDiff A S n (rcResLM A h n x) := by
  apply Subtype.ext
  rw [rcResLM_coe, rcDiff_coe, rcDiff_coe, rcResLM_coe]
  have h2 := congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm
    (dualChainMap ℤ (TopCat.of S) (TopCat.of T)
      (pdIncl (M := TopCat.of X) T S h)) n (n+1))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h2
  exact (LinearMap.congr_fun h2 (x : ↥((singularCochainComplex ℤ (TopCat.of T)).X n))).symm

/-- The restriction is compatible with composition of inclusions, at the level of cochains. -/
theorem rcResLM_comp {S S' T : Set X} (h : S ⊆ S') (h' : S' ⊆ T) (n : ℕ) :
    (rcResLM A h n).comp (rcResLM A h' n) = rcResLM A (h.trans h') n := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [LinearMap.comp_apply, rcResLM_coe, rcResLM_coe, rcResLM_coe]
  have hcomp : (dualChainMap ℤ (TopCat.of S) (TopCat.of T)
        (pdIncl (M := TopCat.of X) T S (h.trans h'))).f n
      = (dualChainMap ℤ (TopCat.of S') (TopCat.of T)
          (pdIncl (M := TopCat.of X) T S' h')).f n
        ≫ (dualChainMap ℤ (TopCat.of S) (TopCat.of S')
            (pdIncl (M := TopCat.of X) S' S h)).f n := by
    rw [← pdIncl_comp h h']
    rw [dualChainMap_comp ℤ (pdIncl (M := TopCat.of X) S' S h)
      (pdIncl (M := TopCat.of X) T S' h'), HomologicalComplex.comp_f]
  rw [hcomp, ModuleCat.hom_comp]
  rfl

/-- The restriction of relative cochains along `S ⊆ T`, as a cochain map. -/
def rcRes {S T : Set X} (h : S ⊆ T) : rcSet A T ⟶ rcSet A S :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (rcResLM A h n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [rcSet_d, rcSet_d]
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply]
    exact (rcResLM_comm A h n x).symm)

/-- The degreewise description of `rcRes`. -/
theorem rcRes_f {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (rcRes A h).f n = ModuleCat.ofHom (rcResLM A h n) := rfl

/-- The restriction is compatible with composition of inclusions. -/
theorem rcRes_comp {S S' T : Set X} (h : S ⊆ S') (h' : S' ⊆ T) :
    rcRes A (h.trans h') = rcRes A h' ≫ rcRes A h := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, rcRes_f, rcRes_f, rcRes_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact congrArg (fun f => f x) (rcResLM_comp A h h' n).symm

/-- The homology of `rcSet` is `pdCohSub`. -/
theorem rcSet_homology_eq (U : Set X) (k : ℕ) :
    (rcSet A U).homology k = pdCohSub (TopCat.of X) A U k := rfl

end

end Work.Cohomology
