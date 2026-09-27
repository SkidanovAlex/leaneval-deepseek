import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.chartedSpaceChangeModel
import Submission.Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt

/-!
# Smoothness into `(0,∞) × ℝP³` is smoothness of the two components

`Work.Drive.halfLineProjectiveCharted` is the transparent smooth structure on
`(0,∞) × ℝP³` modelled on `ℝ⁴` which is used in the capping construction: it is the
`ChartedSpace` obtained from

* the structure on `(0,∞)` transported from `ℝ¹` along `expHomeo : ℝ¹ ≃ₜ (0,∞)`,
* the transparent projective structure `Work.Drive.projCharted 3` on `ℝP³`,

taken as a product and then re-modelled on `ℝ⁴` along the canonical linear homeomorphism
`Work.Drive.psiEquiv : ℝ¹ × ℝ³ ≃ₜ ℝ⁴`.

The main result of this file, `Work.Drive.contMDiffAt_halfLineProjective_iff`, unwinds all of this
and says that a map `g : ℝ^k → (0,∞) × ℝP³` is `C^∞` at `z` for that structure exactly when

* the first component, read through the exponential chart (`expHomeo.symm ∘ ·`), is `C^∞` at `z`
  as a map into `ℝ¹`, and
* the second component is `C^∞` at `z` as a map into `ℝP³` for `projCharted 3`.

The proof is the three-step reduction: the re-modelling along `psiEquiv` does not change
`ContMDiffAt` (`Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel'`, a version of
`Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel` in which the source manifold is arbitrary);
smoothness into a product is componentwise (`contMDiffAt_prod_iff` with
`modelWithCornersSelf_prod`); and smoothness into `(0,∞)` for the structure pushed forward along
`expHomeo` is smoothness of `expHomeo.symm ∘ ·` for the standard structure on `ℝ¹`
(`Work.Drive.chartedStructure_contMDiffWithinAt`).
-/

namespace Work.Drive

open Manifold Function Set Topology Filter
open scoped Manifold ContDiff

noncomputable section

/-- Composing on the left with a global `C^n` homeomorphism `φ` (with `C^n` inverse) does not
change `C^n`-regularity within a set at a point.  This is
`Work.Drive.contDiffWithinAt_comp_homeomorph_iff` with an arbitrary normed source, which is what
is needed for the model change `chartedSpaceChangeModel` when the source of the maps considered is
not the new model space. -/
theorem contDiffWithinAt_comp_homeomorph_iff'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (φ : E ≃ₜ E') {n : WithTop ℕ∞}
    (hφ : ContDiff 𝕜 n (φ : E → E')) (hφ' : ContDiff 𝕜 n (φ.symm : E' → E))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] {g : W → E} {T : Set W} {p : W} :
    ContDiffWithinAt 𝕜 n (⇑φ ∘ g) T p ↔ ContDiffWithinAt 𝕜 n g T p := by
  constructor
  · intro h
    have h1 : ContDiffWithinAt 𝕜 n (φ.symm : E' → E) univ (φ (g p)) :=
      hφ'.contDiffAt.contDiffWithinAt
    have h2 := h1.comp p h (Set.mapsTo_univ _ _)
    refine h2.congr (fun y _ => ?_) ?_
    · simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    · simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  · intro h
    have h1 : ContDiffWithinAt 𝕜 n (φ : E → E') univ (g p) := hφ.contDiffAt.contDiffWithinAt
    exact h1.comp p h (Set.mapsTo_univ _ _)

section

set_option linter.style.haveILetI false

/-- **Smoothness is invariant under the model change `chartedSpaceChangeModel`**, with an arbitrary
source manifold.  This is `Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel` with the model
space `F` of the source decoupled from the new model space `E'`: if `M` is a charted space over `E`,
`φ : E ≃ₜ E'` is a `C^n` homeomorphism with `C^n` inverse, and `M` is re-charted over `E'` by
`chartedSpaceChangeModel φ`, then `f : Z → M` is `C^n` within `s` at `z` for the new structure if
and only if it is for the old one. -/
theorem contMDiffWithinAt_chartedSpaceChangeModel'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 F H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (φ : E ≃ₜ E') {n : WithTop ℕ∞}
    (hφ : ContDiff 𝕜 n (φ : E → E')) (hφ' : ContDiff 𝕜 n (φ.symm : E' → E))
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
    (f : Z → M) (s : Set Z) (z : Z) :
    letI := Work.Drive.chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ
    (ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E') n f s z ↔
      ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) n f s z) := by
  letI : ChartedSpace E' M := Work.Drive.chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ
  change ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E') n f s z ↔
      ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) n f s z
  have hchart : ∀ y : M, (⇑(chartAt E' y) : M → E') = ⇑φ ∘ ⇑(chartAt E y) :=
    Work.Drive.chartAt_chartedSpaceChangeModel φ
  constructor
  · intro h
    refine ⟨h.continuousWithinAt, ?_⟩
    have hh := h.prop
    rw [contDiffWithinAtProp_self_target] at hh
    rw [contDiffWithinAtProp_self_target]
    have key : (↑(chartAt E' (f z)) ∘ f ∘ ↑(chartAt H z).symm) ∘ I.symm
        = ⇑φ ∘ ((↑(chartAt E (f z)) ∘ f ∘ ↑(chartAt H z).symm) ∘ I.symm) := by
      rw [hchart (f z)]
      simp only [Function.comp_assoc]
    rw [key] at hh
    exact (contDiffWithinAt_comp_homeomorph_iff' φ hφ hφ').mp hh
  · intro h
    refine ⟨h.continuousWithinAt, ?_⟩
    have hh := h.prop
    rw [contDiffWithinAtProp_self_target] at hh
    rw [contDiffWithinAtProp_self_target]
    have key : (↑(chartAt E' (f z)) ∘ f ∘ ↑(chartAt H z).symm) ∘ I.symm
        = ⇑φ ∘ ((↑(chartAt E (f z)) ∘ f ∘ ↑(chartAt H z).symm) ∘ I.symm) := by
      rw [hchart (f z)]
      simp only [Function.comp_assoc]
    rw [key]
    exact (contDiffWithinAt_comp_homeomorph_iff' φ hφ hφ').mpr hh

theorem contMDiffAt_halfLineProjective_iff {k : ℕ}
    (g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (z : EuclideanSpace ℝ (Fin k)) :
    letI := Work.Drive.projCharted 3
    letI := Work.Drive.halfLineProjectiveCharted
    (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z ∧
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => (g w).2) z) := by
  -- The three transparent structures entering the definition of `halfLineProjectiveCharted`,
  -- plus the transported structure on `(0,∞)`.
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace Work.Drive.expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ))
      (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  change (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z ∧
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => (g w).2) z)
  -- Step 1: undoing the model change along `psiEquiv : ℝ¹ × ℝ³ ≃ₜ ℝ⁴`.
  have hA : (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g z) :=
    contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (E' := EuclideanSpace ℝ (Fin 4))
      (F := EuclideanSpace ℝ (Fin k)) (H := EuclideanSpace ℝ (Fin k))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) Work.Drive.psiEquiv.toHomeomorph
      Work.Drive.psiEquiv.contDiff Work.Drive.psiEquiv.symm.contDiff g univ z
  -- Step 2: smoothness into a product is componentwise.
  have hB : (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.fst ∘ g) z ∧
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.snd ∘ g) z) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffAt_prod_iff g
  -- Step 3: on `(0,∞)` the chart of the transported structure is `expHomeo.symm`.
  have hC : (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.fst ∘ g) z ↔
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z) :=
    Work.Drive.chartedStructure_contMDiffWithinAt
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      Work.Drive.expHomeo (Prod.fst ∘ g) univ z
  rw [hA, hB, hC]
  exact Iff.rfl

end

end

end Work.Drive
