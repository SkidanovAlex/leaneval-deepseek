import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt
import Submission.Work.Drive.contMDiffAt_projRot

/-!
# The rotation of the capping space is `C^∞` in the rotation parameter

The counting engine (`Work.Drive.clampedSweep`, `Work.Drive.Meet3Generic`, …) is fed by *chains*
`□ → CappingSpace` on boxes, and the openness clause of `Work.Drive.StripRel` — the local constancy of
the parity function `u ↦ b u` — needs the rotated chains `x ↦ rotCapping u (P x)` to form a `C^∞`
family in `(u, x)`.  This file supplies exactly that:

* `Work.Drive.contMDiffAt_rotCapping` — the rotation
  `(t, p) ↦ rotCapping t p` is `C^∞` on `ℝ × CappingSpace` for the transparent structure
  `Work.Drive.cappingCharted` (pointwise form);
* `Work.Drive.contMDiff_rotCapping` — the same, globally, for `ContMDiff`.

The ingredients are all proved elsewhere:

* `Work.Drive.cappingSpaceHomeoProj_rotCapping` — in the model `(0,∞) × ℝP³` the rotation fixes the
  radial coordinate and acts on the `ℝP³` factor by `Work.Drive.projRot`;
* `Work.Drive.contMDiffAt_projRot` — the two-variable smoothness `(t, x) ↦ projRot t x` on the
  product manifold `ℝ × ℝP³`;
* `Work.Drive.contMDiffAt_halfLineProjective_iff_general` — smoothness into the model factorises
  into the `(0,∞)`-component (through `expHomeo`) and the `ℝP³`-component;
* `Work.Drive.chartedStructure_contMDiffWithinAt` — smoothness into `CappingSpace` is smoothness of
  the composite with `cappingSpaceHomeoProj`, for the transported structure.

With this, for *any* `C^∞` chain `P : Z → CappingSpace` (any charted source `Z`) the family
`(t, z) ↦ rotCapping t (P z)` is `C^∞` by composing with `contMDiff_rotCapping` — no hypothesis on how
`P` is presented.
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology
open Set Filter

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- `cappingSpaceHomeoProj` is `C^∞` from the transparent structure on `CappingSpace`. -/
lemma contMDiffAt_cappingSpaceHomeoProj_charted (p₀ : CappingSpace) :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3)) := projCharted 3
     letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) :=
       halfLineProjectiveCharted
     ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      cappingSpaceHomeoProj p₀) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) :=
    halfLineProjectiveCharted
  have h := (chartedStructure_contMDiffWithinAt
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (M := Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) (M' := CappingSpace)
    (e := cappingSpaceHomeoProj.symm) (Z := CappingSpace) (f := id) univ p₀).mp
    (contMDiffWithinAt_id (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  simpa only [contMDiffWithinAt_univ, Function.comp_def, id_eq, Homeomorph.symm_symm] using h

/-- **The rotation action on the capping space is `C^∞` in the rotation parameter.** -/
theorem contMDiffAt_rotCapping (t₀ : ℝ) (p₀ : CappingSpace) :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
       prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
     ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
       (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (fun q : ℝ × CappingSpace => rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2) (t₀, p₀)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) :=
    halfLineProjectiveCharted
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) (ℝ × ℙ ℝ (Eucl 3)) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3))
  set x₀ : ℙ ℝ (Eucl 3) := (cappingSpaceHomeoProj p₀).2 with hx₀
  -- the unrotated family and its two components
  have hG₀ : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × CappingSpace => cappingSpaceHomeoProj q.2) (t₀, p₀) :=
    (contMDiffAt_cappingSpaceHomeoProj_charted p₀).comp (t₀, p₀)
      (contMDiffAt_snd (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  obtain ⟨hrad₀, hproj₀⟩ := (contMDiffAt_halfLineProjective_iff_general
    (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
    (fun q : ℝ × CappingSpace => cappingSpaceHomeoProj q.2) (t₀, p₀)).mp hG₀
  -- the rotated family, via the component criterion
  have hG : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × CappingSpace =>
        cappingSpaceHomeoProj (rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2)) (t₀, p₀) := by
    refine (contMDiffAt_halfLineProjective_iff_general
      (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
      (fun q : ℝ × CappingSpace =>
        cappingSpaceHomeoProj (rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2)) (t₀, p₀)).mpr ⟨?_, ?_⟩
    · have hfun : (fun q : ℝ × CappingSpace =>
            expHomeo.symm ((cappingSpaceHomeoProj (rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2)).1))
          = fun q : ℝ × CappingSpace => expHomeo.symm ((cappingSpaceHomeoProj q.2).1) := by
        funext q
        rw [cappingSpaceHomeoProj_rotCapping]
      rw [hfun]
      exact hrad₀
    · have hfun : (fun q : ℝ × CappingSpace =>
            (cappingSpaceHomeoProj (rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2)).2)
          = fun q : ℝ × CappingSpace => projRot q.1 ((cappingSpaceHomeoProj q.2).2) := by
        funext q
        rw [cappingSpaceHomeoProj_rotCapping]
      rw [hfun]
      -- the inner map into `ℝ × ℝP³`
      have hInner : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
          ((modelWithCornersSelf ℝ ℝ).prod
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × CappingSpace => (q.1, (cappingSpaceHomeoProj q.2).2)) (t₀, p₀) :=
        (contMDiffAt_prod_iff _).mpr ⟨contMDiffAt_fst, hproj₀⟩
      -- the outer map, kept as a local definition so that `projRot` is not unfolded
      let F : ℝ × ℙ ℝ (Eucl 3) → ℙ ℝ (Eucl 3) := fun q => projRot q.1 q.2
      have hF : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
          (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F (t₀, x₀) := by
        have h := contMDiffAt_projRot t₀ x₀
        rw [modelWithCornersSelf_prod] at h
        exact h
      have hcomp := hF.comp (I := ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
        (I' := (modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (t₀, p₀) hInner
      simpa only [F, Function.comp_def] using hcomp
  -- transport back to `CappingSpace`
  exact (chartedStructure_contMDiffWithinAt
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (I' := ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))))
    (M := Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) (M' := CappingSpace)
    (e := cappingSpaceHomeoProj.symm) (Z := ℝ × CappingSpace)
    (f := fun q : ℝ × CappingSpace => rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2) univ (t₀, p₀)).mpr
    (by simpa only [contMDiffWithinAt_univ, Homeomorph.symm_symm] using hG)

/-- **The rotation of the capping space is `C^∞` in the rotation parameter.** -/
theorem contMDiff_rotCapping :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
       prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
     ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
       (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (fun q : ℝ × CappingSpace => rotCapping ((q.1 : ℝ) : UnitAddCircle) q.2)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Set.Ioi (0:ℝ) × ℙ ℝ (Eucl 3)) :=
    halfLineProjectiveCharted
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) (ℝ × ℙ ℝ (Eucl 3)) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3))
  intro q
  exact contMDiffAt_rotCapping q.1 q.2


/-- **The rotated chain.**  For a `C^∞` chain `P : Z → CappingSpace` on an arbitrary charted source
and a `C^∞` rotation parameter `τ : Z → ℝ`, the rotated chain `z ↦ rotCapping (τ z) (P z)` is `C^∞`.
This is the form in which the openness clause of `Work.Drive.StripRel` (local constancy of
`u ↦ b u` along the rotated chains) consumes the smoothness of the rotation. -/
theorem contMDiffAt_rotCapping_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
    (P : Z → CappingSpace) (τ : Z → ℝ) (z₀ : Z)
    (hP : @ContMDiffAt ℝ _ E _ _ H _ I Z _ _ (EuclideanSpace ℝ (Fin 4)) _ _
      (EuclideanSpace ℝ (Fin 4)) _ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      CappingSpace _ cappingCharted ((⊤ : ℕ∞) : WithTop ℕ∞) P z₀)
    (hτ : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) τ z₀) :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
       prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
     ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (fun z => rotCapping ((τ z : ℝ) : UnitAddCircle) (P z)) z₀) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 4))) (ℝ × CappingSpace) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 4)) CappingSpace
  have hpair : ContMDiffAt I ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (τ z, P z)) z₀ := (contMDiffAt_prod_iff _).mpr ⟨hτ, hP⟩
  exact (contMDiffAt_rotCapping (τ z₀) (P z₀)).comp (I := I) z₀ hpair

end

end Work.Drive
