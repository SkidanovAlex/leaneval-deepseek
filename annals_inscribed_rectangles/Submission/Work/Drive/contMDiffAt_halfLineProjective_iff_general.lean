import Mathlib
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff

/-!
# The componentwise criterion for `C^∞` maps into `(0,∞) × ℝP³`, over an arbitrary source

`Work.Drive.contMDiffAt_halfLineProjective_iff` proves the componentwise criterion for maps
`EuclideanSpace ℝ (Fin k) → (0,∞) × ℝP³`, where both source and target carry the "self" model.
This file records the same criterion for a map `g : Z → (0,∞) × ℝP³` whose source is an arbitrary
charted space `(Z, H, I)`:

`g` is `C^∞` at `z` for the transparent structure `Work.Drive.halfLineProjectiveCharted` on
`(0,∞) × ℝP³` exactly when

* the first component, read through the exponential chart (`expHomeo.symm ∘ ·`), is `C^∞` at `z`
  as a map into `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, and
* the second component is `C^∞` at `z` as a map into `ℝP³` for `projCharted 3`.

Nothing new is needed: each of the three ingredients of the proof of
`Work.Drive.contMDiffAt_halfLineProjective_iff` is already stated for an arbitrary source manifold,

* `Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel'` (undoing the model change along
  `Work.Drive.psiEquiv`),
* `contMDiffAt_prod_iff` (smoothness into a product is componentwise), and
* `Work.Drive.chartedStructure_contMDiffWithinAt` (smoothness for a structure transported along
  `Work.Drive.expHomeo`),
-/

namespace Work.Drive

open Manifold Function Set Topology Filter
open scoped Manifold ContDiff

noncomputable section

set_option linter.style.haveILetI false in
theorem contMDiffAt_halfLineProjective_iff_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
    (g : Z → Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) (z : Z) :
    @ContMDiffAt ℝ _ E _ _ H _ I Z _ _ (EuclideanSpace ℝ (Fin 4)) _ _
      (EuclideanSpace ℝ (Fin 4)) _ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.halfLineProjectiveCharted)
      ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
    ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z ∧
      @ContMDiffAt ℝ _ E _ _ H _ I Z _ _ (EuclideanSpace ℝ (Fin 3)) _ _
        (EuclideanSpace ℝ (Fin 3)) _ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (g w).2) z := by
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
  change (ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
    ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z ∧
      ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => (g w).2) z)
  -- Step 1: undoing the model change along `psiEquiv : ℝ¹ × ℝ³ ≃ₜ ℝ⁴`.
  have hA : (ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g z) :=
    Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (E' := EuclideanSpace ℝ (Fin 4))
      (F := E) (H := H) I Work.Drive.psiEquiv.toHomeomorph
      Work.Drive.psiEquiv.contDiff Work.Drive.psiEquiv.symm.contDiff g univ z
  -- Step 2: smoothness into a product is componentwise.
  have hB : (ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g z ↔
      ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.fst ∘ g) z ∧
      ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.snd ∘ g) z) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffAt_prod_iff g
  -- Step 3: on `(0,∞)` the chart of the transported structure is `expHomeo.symm`.
  have hC : (ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.fst ∘ g) z ↔
      ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.expHomeo.symm (g w).1) z) :=
    Work.Drive.chartedStructure_contMDiffWithinAt
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (I' := I)
      Work.Drive.expHomeo (Prod.fst ∘ g) univ z
  rw [hA, hB, hC]
  exact Iff.rfl

end

end Work.Drive
