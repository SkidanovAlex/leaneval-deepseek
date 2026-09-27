import Mathlib
import Submission.Work.Drive.rowsOpen
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.blockPlaneInvariant
import Submission.Work.Drive.contMDiff_rotPresentation
import Submission.Work.Drive.contMDiffAt_classMap_prod
import Submission.Work.Drive.classRowRebasing
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.refTripleClause

/-!
# The **end-triple** rows of the design are open in the design parameter

`CLASSROWS_DENSITY_MECHANISM.md` §3.1 names the *openness* of the design's class rows as the piece
that turns the row producers of the class-row lane into the open-dense family `R` of
`Work.Drive.exists_classRowFamily`.  The **pair** row is `Drive/isOpen_pairReg_designPert.lean`
(and `Drive/pairRowOpenPert.lean`); this file supplies the **end-triple** rows, i.e. the rows

* `EndTripleReg P̂₀P̂₁P̂₂` (the design's own perturbed triple),
* the two mixed rows in which one or two slots are the *transported* linear models
  `Work.Drive.linTransClass`,

and, for completeness, the all-linear row of `Work.Drive.DesignRowsLinAt`.

## The route

* `Drive/rowsOpen.lean` supplies the generic brick: for a jointly smooth family of plane *class maps*
  the box-restricted end-triple regularity `Work.Drive.BoxEndTripleRegG` is **open** in the family
  parameter (`Work.Drive.isOpen_boxEndTripleRegG`), through the charted triple-difference system, the
  open set of injective continuous linear maps and the compactness of the unit box;
* the passage from the box form to the unrestricted `Work.Drive.EndTripleReg` is
  `Work.Drive.endTripleReg_of_boxEndTripleReg_affRep` (the design's presentations factor through
  `foldBox`, hence are invariant under the affine representatives of the unit square);
* the joint smoothness of the design's two families of class maps is `classMap`-smoothness
  (**`Work.Drive.contMDiff_designPertClass_fam_er`**, **`Work.Drive.contMDiff_linTransClass_fam_er`**),
  built on `Work.Drive.contMDiffAt_classMap_prod` and the two identifying equalities
  `planeClassMap_chartPert_comp_rb` and `planeClassMap_chartPert_diskPlane_linPlaneChart`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartER :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Work.Drive.Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The class map of a smooth presentation is smooth -/

/-- The class map of a smooth plane presentation is smooth. -/
theorem contMDiff_planeClassMap_of_contMDiff_er
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (planeClassMap P) :=
  fun y => contMDiffAt_cls_of_contMDiff_gen (k := 2) hP y

/-- **Joint smoothness of the class perturbation**: for a smooth parameter map `τ` into `𝔼³` and a
smooth class map `A`, the map `(p, y) ↦ classMap (τ p) (A y)` is `C^∞`. -/
theorem contMDiff_classMap_fam_er {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (τ : P → Eucl 3) (hτ : ContMDiff (𝓘(ℝ, P)) (𝓡 4) Work.Drive.Ctop τ)
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓡 2) (𝓡 3) Work.Drive.Ctop A) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) Work.Drive.Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => Work.Drive.classMap (τ q.1) (A q.2)) := by
  intro q
  have h1 : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Work.Drive.Ctop
      (fun z : P × EuclideanSpace ℝ (Fin 2) => τ z.1) q :=
    (hτ q.1).comp q
      (ContinuousLinearMap.fst ℝ P (EuclideanSpace ℝ (Fin 2))).contMDiff.contMDiffAt
  have h2 : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) Work.Drive.Ctop
      (fun z : P × EuclideanSpace ℝ (Fin 2) => A z.2) q :=
    (hA q.2).comp q
      (ContinuousLinearMap.snd ℝ P (EuclideanSpace ℝ (Fin 2))).contMDiff.contMDiffAt
  exact (Work.Drive.contMDiffAt_classMap_prod (τ q.1) (A q.2)).comp q (h1.prodMk h2)

/-- **The design's perturbed class map is jointly smooth in the design parameter and the plane
parameter.** -/
theorem contMDiff_designPertClass_fam_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q)) (u : UnitAddCircle) (k : Fin 3) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        designPertClass Q u q.1 k q.2) := by
  have h1 := contMDiff_classMap_fam_er (P := EuclideanSpace ℝ (Fin 12))
    (fun t => (blk k) t) ((blk k).contMDiff)
    (planeClassMap (rotPresentation Q u))
    (contMDiff_planeClassMap_of_contMDiff_er (contMDiff_rotPresentation Q u hQ))
  have hfun : (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.classMap ((blk k) q.1)
          (planeClassMap (rotPresentation Q u) q.2))
      = fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        designPertClass Q u q.1 k q.2 := by
    funext q
    show Work.Drive.classMap ((blk k) q.1) (planeClassMap (rotPresentation Q u) q.2)
      = planeClassMap (fun y => chartPert ((blk k) q.1) (rotPresentation Q u y)) q.2
    rw [planeClassMap_chartPert_comp_rb]
    rfl
  rwa [hfun] at h1

/-- **The design's transported linear class model is jointly smooth in the design parameter.** -/
theorem contMDiff_linTransClass_fam_er (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (k : Fin 3) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        linTransClass Φ ((blk k) q.1) cl hcl q.2) := by
  have h1 := contMDiff_classMap_fam_er (P := EuclideanSpace ℝ (Fin 12))
    (fun t => (blk k) t) ((blk k).contMDiff)
    (planeClassMap (diskPlane (linPlaneChart Φ cl hcl)))
    (contMDiff_planeClassMap_of_contMDiff_er
      (contMDiff_diskPlane (linPlaneChart_contMDiff Φ cl hcl)))
  have hfun : (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.classMap ((blk k) q.1)
          (planeClassMap (diskPlane (linPlaneChart Φ cl hcl)) q.2))
      = fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        linTransClass Φ ((blk k) q.1) cl hcl q.2 := by
    funext q
    show Work.Drive.classMap ((blk k) q.1)
        (planeClassMap (diskPlane (linPlaneChart Φ cl hcl)) q.2)
      = linTransClass Φ ((blk k) q.1) cl hcl q.2
    have e1 : Work.Drive.classMap ((blk k) q.1)
        (planeClassMap (diskPlane (linPlaneChart Φ cl hcl)) q.2)
        = planeClassMap (fun z => chartPert ((blk k) q.1)
            (diskPlane (linPlaneChart Φ cl hcl) z)) q.2 :=
      (congrFun (planeClassMap_chartPert_comp_rb ((blk k) q.1)
        (diskPlane (linPlaneChart Φ cl hcl))) q.2).symm
    have e2 : planeClassMap (fun z => chartPert ((blk k) q.1)
          (diskPlane (linPlaneChart Φ cl hcl) z)) q.2
        = planeClassMap (diskPlane (linPlaneChart
            (Φ.trans (classEquiv ((blk k) q.1))) cl hcl)) q.2 :=
      congrFun (planeClassMap_chartPert_diskPlane_linPlaneChart Φ cl hcl ((blk k) q.1)) q.2
    rw [linTransClass, e1, e2]
  rwa [hfun] at h1


/-! ## 2. The design's presentations: smoothness and invariance -/

/-- **Each perturbed design presentation is smooth.** -/
theorem contMDiff_designPertPlane_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (designPertPlane Q u t k) := by
  intro y
  have h1 : ContMDiffAt (𝓡 2) ((𝓡 4).prod (𝓡 4)) Work.Drive.Ctop
      (fun y' : EuclideanSpace ℝ (Fin 2) =>
        ((blk k) t, rotPresentation Q u y')) y :=
    contMDiffAt_const.prodMk ((contMDiff_rotPresentation Q u hQ) y)
  refine ContMDiffAt.comp
    (f := fun y' : EuclideanSpace ℝ (Fin 2) => ((blk k) t, rotPresentation Q u y')) y
    (contMDiffAt_chartPert ((blk k) t) (rotPresentation Q u y)) h1

/-- **Each perturbed design presentation is invariant under the affine symmetries of the parameter
square.** -/
theorem designPertPlane_affRep_er (Q : ℂ → CappingSpace) (u : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        designPertPlane Q u t k (affRep e mm y) = designPertPlane Q u t k y := by
  intro e mm he y
  show chartPert ((blk k) t) (rotPresentation Q u (affRep e mm y))
    = chartPert ((blk k) t) (rotPresentation Q u y)
  rw [rotPresentation_affRep he mm Q u y]

/-- **Each transported linear disk presentation is invariant under the affine symmetries.** -/
theorem linDiskPlane_affRep_er (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (τ : Eucl 3) :
    ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl) (affRep e mm y)
          = diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl) y :=
  fun e mm he y => diskPlane_affRep he mm
    (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl) y

/-! ## 3. The box form of the end-triple rows -/

/-- **For three affinely invariant smooth presentations, the box-restricted end-triple regularity is
the unrestricted one.** -/
theorem boxEndTripleReg_iff_endTripleReg_pres_er
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P k (affRep e mm y) = P k y) :
    BoxEndTripleReg (planeClassMap (P 0)) (planeClassMap (P 1)) (planeClassMap (P 2)) ↔
      EndTripleReg (planeClassMap (P 0)) (planeClassMap (P 1)) (planeClassMap (P 2)) :=
  ⟨endTripleReg_of_boxEndTripleReg_affRep P hP hinv,
    fun h y₀ y₁ y₂ _ h1 h2 => h y₀ y₁ y₂ h1 h2⟩

/-! ## 4. The openness of the end-triple rows -/

/-- **The end-triple row of three locally smooth class families is open in the parameter.** -/
theorem isOpen_endTripleReg_of_fam_er
    (A₀ A₁ A₂ : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA₀ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => A₀ q.1 q.2))
    (hA₁ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => A₁ q.1 q.2))
    (hA₂ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => A₂ q.1 q.2))
    (hboxiff : ∀ t : EuclideanSpace ℝ (Fin 12),
      BoxEndTripleReg (A₀ t) (A₁ t) (A₂ t) ↔ EndTripleReg (A₀ t) (A₁ t) (A₂ t)) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg (A₀ t) (A₁ t) (A₂ t)} := by
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  have hbase : BoxEndTripleRegG (A₀ t₀) (A₁ t₀) (A₂ t₀) :=
    (boxEndTripleRegG_iff (A₀ t₀) (A₁ t₀) (A₂ t₀)).mpr ((hboxiff t₀).mpr ht₀)
  refine (eventually_boxEndTripleRegG A₀ A₁ A₂ hA₀ hA₁ hA₂ t₀ hbase).mono fun t ht => ?_
  exact (hboxiff t).mp ((boxEndTripleRegG_iff (A₀ t) (A₁ t) (A₂ t)).mp ht)


/-! ## 5. The design's presentations: the three-slot box passage -/

/-- **The box passage for three concrete presentations.** -/
theorem boxEndTripleReg_iff_endTripleReg_three_er
    (P₀ P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h₀ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P₀)
    (h₁ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P₁)
    (h₂ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P₂)
    (i₀ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₀ (affRep e mm y) = P₀ y)
    (i₁ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₁ (affRep e mm y) = P₁ y)
    (i₂ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₂ (affRep e mm y) = P₂ y) :
    BoxEndTripleReg (planeClassMap P₀) (planeClassMap P₁) (planeClassMap P₂) ↔
      EndTripleReg (planeClassMap P₀) (planeClassMap P₁) (planeClassMap P₂) := by
  have h := boxEndTripleReg_iff_endTripleReg_pres_er ![P₀, P₁, P₂]
    (by intro k; fin_cases k
        · exact h₀
        · exact h₁
        · exact h₂)
    (by
      intro e mm he k y
      fin_cases k
      · exact i₀ e mm he y
      · exact i₁ e mm he y
      · exact i₂ e mm he y)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
    Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons] using h

/-! ## 6. The end-triple rows of the design -/

/-- The smoothness of a linear disk presentation. -/
theorem contMDiff_linDiskPlane_er (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (τ : Eucl 3) :
    ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop
      (diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl)) :=
  contMDiff_diskPlane (linPlaneChart_contMDiff _ cl hcl)

/-- **The design's own perturbed end-triple row is open in the design parameter.** -/
theorem isOpen_endTripleReg_designPert_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u₀ u₁ u₂ : UnitAddCircle) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (designPertClass Q u₀ t 0) (designPertClass Q u₁ t 1)
        (designPertClass Q u₂ t 2)} := by
  refine isOpen_endTripleReg_of_fam_er (fun t => designPertClass Q u₀ t 0)
    (fun t => designPertClass Q u₁ t 1) (fun t => designPertClass Q u₂ t 2)
    (contMDiff_designPertClass_fam_er Q hQ u₀ 0)
    (contMDiff_designPertClass_fam_er Q hQ u₁ 1)
    (contMDiff_designPertClass_fam_er Q hQ u₂ 2) ?_
  intro t
  exact boxEndTripleReg_iff_endTripleReg_three_er (designPertPlane Q u₀ t 0)
    (designPertPlane Q u₁ t 1) (designPertPlane Q u₂ t 2)
    (contMDiff_designPertPlane_er Q hQ u₀ t 0) (contMDiff_designPertPlane_er Q hQ u₁ t 1)
    (contMDiff_designPertPlane_er Q hQ u₂ t 2)
    (designPertPlane_affRep_er Q u₀ t 0) (designPertPlane_affRep_er Q u₁ t 1)
    (designPertPlane_affRep_er Q u₂ t 2)

/-- **The design's first mixed end-triple row is open**: one transported linear model in the first
slot, the design's perturbed planes in the other two. -/
theorem isOpen_endTripleReg_designMixed1_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u₁ u₂ : UnitAddCircle) (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (linTransClass Φ ((blk 0) t) cl hcl) (designPertClass Q u₁ t 1)
        (designPertClass Q u₂ t 2)} := by
  refine isOpen_endTripleReg_of_fam_er (fun t => linTransClass Φ ((blk 0) t) cl hcl)
    (fun t => designPertClass Q u₁ t 1) (fun t => designPertClass Q u₂ t 2)
    (contMDiff_linTransClass_fam_er Φ cl hcl 0)
    (contMDiff_designPertClass_fam_er Q hQ u₁ 1)
    (contMDiff_designPertClass_fam_er Q hQ u₂ 2) ?_
  intro t
  exact boxEndTripleReg_iff_endTripleReg_three_er
    (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl))
    (designPertPlane Q u₁ t 1) (designPertPlane Q u₂ t 2)
    (contMDiff_linDiskPlane_er Φ cl hcl ((blk 0) t))
    (contMDiff_designPertPlane_er Q hQ u₁ t 1) (contMDiff_designPertPlane_er Q hQ u₂ t 2)
    (linDiskPlane_affRep_er Φ cl hcl ((blk 0) t))
    (designPertPlane_affRep_er Q u₁ t 1) (designPertPlane_affRep_er Q u₂ t 2)

/-- **The design's second mixed end-triple row is open**: two transported linear models first, the
design's perturbed plane last. -/
theorem isOpen_endTripleReg_designMixed2_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u₂ : UnitAddCircle) (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (linTransClass Φ₁ ((blk 1) t) cl hcl) (linTransClass Φ₀ ((blk 0) t) cl hcl)
        (designPertClass Q u₂ t 2)} := by
  refine isOpen_endTripleReg_of_fam_er (fun t => linTransClass Φ₁ ((blk 1) t) cl hcl)
    (fun t => linTransClass Φ₀ ((blk 0) t) cl hcl) (fun t => designPertClass Q u₂ t 2)
    (contMDiff_linTransClass_fam_er Φ₁ cl hcl 1)
    (contMDiff_linTransClass_fam_er Φ₀ cl hcl 0)
    (contMDiff_designPertClass_fam_er Q hQ u₂ 2) ?_
  intro t
  exact boxEndTripleReg_iff_endTripleReg_three_er
    (diskPlane (linPlaneChart (Φ₁.trans (classEquiv ((blk 1) t))) cl hcl))
    (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl))
    (designPertPlane Q u₂ t 2)
    (contMDiff_linDiskPlane_er Φ₁ cl hcl ((blk 1) t))
    (contMDiff_linDiskPlane_er Φ₀ cl hcl ((blk 0) t))
    (contMDiff_designPertPlane_er Q hQ u₂ t 2)
    (linDiskPlane_affRep_er Φ₁ cl hcl ((blk 1) t))
    (linDiskPlane_affRep_er Φ₀ cl hcl ((blk 0) t))
    (designPertPlane_affRep_er Q u₂ t 2)

/-- **The all-linear end-triple row is open in the design parameter.** -/
theorem isOpen_endTripleReg_designLin_er (Φ₀ Φ₁ Φ₂ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ)
    (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (linTransClass Φ₂ ((blk 2) t) cl hcl) (linTransClass Φ₀ ((blk 0) t) cl hcl)
        (linTransClass Φ₁ ((blk 1) t) cl hcl)} := by
  refine isOpen_endTripleReg_of_fam_er (fun t => linTransClass Φ₂ ((blk 2) t) cl hcl)
    (fun t => linTransClass Φ₀ ((blk 0) t) cl hcl)
    (fun t => linTransClass Φ₁ ((blk 1) t) cl hcl)
    (contMDiff_linTransClass_fam_er Φ₂ cl hcl 2)
    (contMDiff_linTransClass_fam_er Φ₀ cl hcl 0)
    (contMDiff_linTransClass_fam_er Φ₁ cl hcl 1) ?_
  intro t
  exact boxEndTripleReg_iff_endTripleReg_three_er
    (diskPlane (linPlaneChart (Φ₂.trans (classEquiv ((blk 2) t))) cl hcl))
    (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl))
    (diskPlane (linPlaneChart (Φ₁.trans (classEquiv ((blk 1) t))) cl hcl))
    (contMDiff_linDiskPlane_er Φ₂ cl hcl ((blk 2) t))
    (contMDiff_linDiskPlane_er Φ₀ cl hcl ((blk 0) t))
    (contMDiff_linDiskPlane_er Φ₁ cl hcl ((blk 1) t))
    (linDiskPlane_affRep_er Φ₂ cl hcl ((blk 2) t))
    (linDiskPlane_affRep_er Φ₀ cl hcl ((blk 0) t))
    (linDiskPlane_affRep_er Φ₁ cl hcl ((blk 1) t))


/-! ## 7. The bundled triple rows of the two design bundles -/

/-- **The three end-triple rows of `Work.Drive.DesignRowsSweepAt` are open.** -/
theorem isOpen_designRowsSweepTriples_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (designPertClass Q (designAngles a c' 0) t 0)
          (designPertClass Q (designAngles a c' 1) t 1)
          (designPertClass Q (designAngles a c' 2) t 2) ∧
      EndTripleReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
          (designPertClass Q (designAngles a c' 1) t 1)
          (designPertClass Q (designAngles a c' 2) t 2) ∧
      EndTripleReg (linTransClass (Φ 1) ((blk 1) t) cl hcl)
          (linTransClass (Φ 0) ((blk 0) t) cl hcl)
          (designPertClass Q (designAngles a c' 2) t 2)} := by
  have h1 := isOpen_endTripleReg_designPert_er Q hQ (designAngles a c' 0)
    (designAngles a c' 1) (designAngles a c' 2)
  have h2 := isOpen_endTripleReg_designMixed1_er Q hQ (designAngles a c' 1)
    (designAngles a c' 2) (Φ 0) cl hcl
  have h3 := isOpen_endTripleReg_designMixed2_er Q hQ (designAngles a c' 2)
    (Φ 0) (Φ 1) cl hcl
  have hset : {t : EuclideanSpace ℝ (Fin 12) |
        EndTripleReg (designPertClass Q (designAngles a c' 0) t 0)
            (designPertClass Q (designAngles a c' 1) t 1)
            (designPertClass Q (designAngles a c' 2) t 2) ∧
        EndTripleReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 1) t 1)
            (designPertClass Q (designAngles a c' 2) t 2) ∧
        EndTripleReg (linTransClass (Φ 1) ((blk 1) t) cl hcl)
            (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 2) t 2)}
      = ({t : EuclideanSpace ℝ (Fin 12) |
          EndTripleReg (designPertClass Q (designAngles a c' 0) t 0)
            (designPertClass Q (designAngles a c' 1) t 1)
            (designPertClass Q (designAngles a c' 2) t 2)} ∩
        {t : EuclideanSpace ℝ (Fin 12) |
          EndTripleReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 1) t 1)
            (designPertClass Q (designAngles a c' 2) t 2)}) ∩
        {t : EuclideanSpace ℝ (Fin 12) |
          EndTripleReg (linTransClass (Φ 1) ((blk 1) t) cl hcl)
            (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 2) t 2)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact (h1.inter h2).inter h3

/-- **The all-linear end-triple row of `Work.Drive.DesignRowsLinAt` is open.** -/
theorem isOpen_designRowsLinTriple_er (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ)
    (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      EndTripleReg (linTransClass (Φ 2) ((blk 2) t) cl hcl)
        (linTransClass (Φ 0) ((blk 0) t) cl hcl)
        (linTransClass (Φ 1) ((blk 1) t) cl hcl)} :=
  isOpen_endTripleReg_designLin_er (Φ 0) (Φ 1) (Φ 2) cl hcl


/-! ## 8. The design's pair row and the full `DesignRowsSweepAt` openness -/

/-- **The box passage for two concrete presentations.** -/
theorem boxPairReg_iff_pairReg_three_er
    (P₀ P₁ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h₀ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P₀)
    (h₁ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P₁)
    (i₀ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₀ (affRep e mm y) = P₀ y)
    (i₁ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₁ (affRep e mm y) = P₁ y) :
    BoxPairReg (planeClassMap P₀) (planeClassMap P₁) ↔
      PairReg (planeClassMap P₀) (planeClassMap P₁) :=
  ⟨pairReg_of_boxPairReg_affRep P₀ P₁ h₀ h₁ i₀ i₁, fun h _ _ _ _ hm => h _ _ hm⟩

/-- **The design's pair row is open in the design parameter.** -/
theorem isOpen_pairReg_designPert_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u₁ u₂ : UnitAddCircle) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      PairReg (designPertClass Q u₁ t 1) (designPertClass Q u₂ t 2)} := by
  have hbox : IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      BoxPairRegG (fun y => designPertClass Q u₁ t 1 y)
        (fun y => designPertClass Q u₂ t 2 y)} :=
    isOpen_boxPairRegG (A := fun t => designPertClass Q u₁ t 1)
      (B := fun t => designPertClass Q u₂ t 2)
      (contMDiff_designPertClass_fam_er Q hQ u₁ 1)
      (contMDiff_designPertClass_fam_er Q hQ u₂ 2)
  have hset : {t : EuclideanSpace ℝ (Fin 12) |
        PairReg (designPertClass Q u₁ t 1) (designPertClass Q u₂ t 2)}
      = {t : EuclideanSpace ℝ (Fin 12) |
        BoxPairRegG (fun y => designPertClass Q u₁ t 1 y)
          (fun y => designPertClass Q u₂ t 2 y)} := by
    ext t
    exact ((boxPairReg_iff_pairReg_three_er (designPertPlane Q u₁ t 1)
      (designPertPlane Q u₂ t 2) (contMDiff_designPertPlane_er Q hQ u₁ t 1)
      (contMDiff_designPertPlane_er Q hQ u₂ t 2) (designPertPlane_affRep_er Q u₁ t 1)
      (designPertPlane_affRep_er Q u₂ t 2)).symm).trans
      ((boxPairRegG_iff (designPertClass Q u₁ t 1) (designPertClass Q u₂ t 2)).symm)
  rw [hset]
  exact hbox

/-- **The whole `Work.Drive.DesignRowsSweepAt` bundle is open in the design parameter.** -/
theorem isOpen_designRowsSweepAt_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) | DesignRowsSweepAt Q a c' Φ cl hcl t} := by
  have h1 := isOpen_pairReg_designPert_er Q hQ (designAngles a c' 1) (designAngles a c' 2)
  have h2 := isOpen_designRowsSweepTriples_er Q hQ a c' Φ cl hcl
  have hset : {t : EuclideanSpace ℝ (Fin 12) | DesignRowsSweepAt Q a c' Φ cl hcl t}
      = {t : EuclideanSpace ℝ (Fin 12) |
          PairReg (designPertClass Q (designAngles a c' 1) t 1)
            (designPertClass Q (designAngles a c' 2) t 2)} ∩
        {t : EuclideanSpace ℝ (Fin 12) |
          EndTripleReg (designPertClass Q (designAngles a c' 0) t 0)
              (designPertClass Q (designAngles a c' 1) t 1)
              (designPertClass Q (designAngles a c' 2) t 2) ∧
          EndTripleReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
              (designPertClass Q (designAngles a c' 1) t 1)
              (designPertClass Q (designAngles a c' 2) t 2) ∧
          EndTripleReg (linTransClass (Φ 1) ((blk 1) t) cl hcl)
              (linTransClass (Φ 0) ((blk 0) t) cl hcl)
              (designPertClass Q (designAngles a c' 2) t 2)} := by
    ext t
    simp only [DesignRowsSweepAt, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact h1.inter h2


/-! ## 9. The linear pair rows and the first three rows of `DesignRowsLinAt` -/

/-- **The pair row of two locally smooth class families is open in the parameter.** -/
theorem isOpen_pairReg_of_fam_er
    (A B : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 3)
      Work.Drive.Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (hboxiff : ∀ t : EuclideanSpace ℝ (Fin 12),
      BoxPairReg (A t) (B t) ↔ PairReg (A t) (B t)) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) | PairReg (A t) (B t)} := by
  have hbox : IsOpen {t : EuclideanSpace ℝ (Fin 12) | BoxPairRegG (A t) (B t)} :=
    isOpen_boxPairRegG hA hB
  have hset : {t : EuclideanSpace ℝ (Fin 12) | PairReg (A t) (B t)}
      = {t : EuclideanSpace ℝ (Fin 12) | BoxPairRegG (A t) (B t)} := by
    ext t
    exact (hboxiff t).symm.trans ((boxPairRegG_iff (A t) (B t)).symm)
  rw [hset]
  exact hbox

/-- **The pair row `lin₀ P̂₂` of `DesignRowsLinAt` is open.** -/
theorem isOpen_pairReg_linPert_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (u₂ : UnitAddCircle) (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      PairReg (linTransClass Φ ((blk 0) t) cl hcl) (designPertClass Q u₂ t 2)} :=
  isOpen_pairReg_of_fam_er _ _
    (contMDiff_linTransClass_fam_er Φ cl hcl 0)
    (contMDiff_designPertClass_fam_er Q hQ u₂ 2)
    (fun t => boxPairReg_iff_pairReg_three_er
      (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl))
      (designPertPlane Q u₂ t 2)
      (contMDiff_linDiskPlane_er Φ cl hcl ((blk 0) t))
      (contMDiff_designPertPlane_er Q hQ u₂ t 2)
      (linDiskPlane_affRep_er Φ cl hcl ((blk 0) t))
      (designPertPlane_affRep_er Q u₂ t 2))

/-- **The pair row `lin₀ lin₁` of `DesignRowsLinAt` is open.** -/
theorem isOpen_pairReg_linLin_er (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      PairReg (linTransClass Φ₀ ((blk 0) t) cl hcl)
        (linTransClass Φ₁ ((blk 1) t) cl hcl)} :=
  isOpen_pairReg_of_fam_er _ _
    (contMDiff_linTransClass_fam_er Φ₀ cl hcl 0)
    (contMDiff_linTransClass_fam_er Φ₁ cl hcl 1)
    (fun t => boxPairReg_iff_pairReg_three_er
      (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl))
      (diskPlane (linPlaneChart (Φ₁.trans (classEquiv ((blk 1) t))) cl hcl))
      (contMDiff_linDiskPlane_er Φ₀ cl hcl ((blk 0) t))
      (contMDiff_linDiskPlane_er Φ₁ cl hcl ((blk 1) t))
      (linDiskPlane_affRep_er Φ₀ cl hcl ((blk 0) t))
      (linDiskPlane_affRep_er Φ₁ cl hcl ((blk 1) t)))

/-- **The first three rows of `Work.Drive.DesignRowsLinAt` are open in the design parameter** (the
remaining conjunct is the algebraic general-position clause `hrank`/`hgen`). -/
theorem isOpen_designRowsLin123_er (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (diskPlane Q))
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
          (designPertClass Q (designAngles a c' 2) t 2) ∧
      PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
          (linTransClass (Φ 1) ((blk 1) t) cl hcl) ∧
      EndTripleReg (linTransClass (Φ 2) ((blk 2) t) cl hcl)
          (linTransClass (Φ 0) ((blk 0) t) cl hcl)
          (linTransClass (Φ 1) ((blk 1) t) cl hcl)} := by
  have h1 := isOpen_pairReg_linPert_er Q hQ (designAngles a c' 2) (Φ 0) cl hcl
  have h2 := isOpen_pairReg_linLin_er (Φ 0) (Φ 1) cl hcl
  have h3 := isOpen_designRowsLinTriple_er Φ cl hcl
  have hset : {t : EuclideanSpace ℝ (Fin 12) |
        PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 2) t 2) ∧
        PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (linTransClass (Φ 1) ((blk 1) t) cl hcl) ∧
        EndTripleReg (linTransClass (Φ 2) ((blk 2) t) cl hcl)
            (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (linTransClass (Φ 1) ((blk 1) t) cl hcl)}
      = ({t : EuclideanSpace ℝ (Fin 12) |
          PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (designPertClass Q (designAngles a c' 2) t 2)} ∩
        {t : EuclideanSpace ℝ (Fin 12) |
          PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (linTransClass (Φ 1) ((blk 1) t) cl hcl)}) ∩
        {t : EuclideanSpace ℝ (Fin 12) |
          EndTripleReg (linTransClass (Φ 2) ((blk 2) t) cl hcl)
            (linTransClass (Φ 0) ((blk 0) t) cl hcl)
            (linTransClass (Φ 1) ((blk 1) t) cl hcl)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact (h1.inter h2).inter h3

end

end Work.Drive
