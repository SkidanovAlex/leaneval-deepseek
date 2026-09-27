import Mathlib
import Submission.Work.Drive.exists_classLift_of_isPlaneChart
import Submission.Work.Drive.exists_neg_parallelism_of_planeChart_of_isPlaneChart
import Submission.Work.Drive.classRowAvoidParallel
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.endsHomotopyClauses
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.foldFlatProducers
import Submission.Work.Drive.foldFlatDesign
import Submission.Work.Drive.mfderiv_planeClassMap_chartPert_diskPlane_single

/-!
# The `t`-independent design data of the class-row assembly

This module packages, for the hypotheses of `Work.Drive.exists_classRowFamily` (an **injective** curve
`γ` with a plane chart `Q`), the *t-independent* data of the linearisation of the design's triple:

* a linear family `A : Eucl 3 ≃L[ℝ] Eucl 3` and the sheared/repaired charts
  `Φ k = Work.Drive.linBase A k` (`Drive/linShearCharts.lean`), chosen so that the chart's lifted class
  curve avoids the anti-parallel cone of the *linear* planes on the real diameter — the non-collision
  condition `hgood` of `Work.Drive.exists_homotopyClauses_rotPresentation`;
* three homotopies `H0 k` from the *unperturbed* design plane `rotPresentation Q (u k)` to the linear
  disk model of `Φ k` at the level `cl`, with the seam invariance and the chain smoothness;

together with the *transported* homotopies

> `Ht Φ H0 t k (s, y) = classMap (blk k t) (H0 k (σ s, y))`

(`σ` a smooth retraction of `ℝ` onto `[0,1]`), which run from the **perturbed** design plane
`Work.Drive.designPertClass Q (u k) t k` to the transported linear model
`Work.Drive.linTransClass (Φ k) (blk k t) cl hcl` — exactly the two ends that the three `Meet3Hyp`
clauses of the class linearisation need — and which are constant in `s` outside `[0,1]`.

Everything here is `t`-independent (the transport is applied pointwise per `t`); the rows that depend on
`t` are the subject of the separate producer `Work.Drive.DesignRowsAt`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. The linear family and the untransported homotopies -/

/-- **The design's linear family and its three (unperturbed) homotopies.**  For an injective curve with
a plane chart and any real angles `u` and level `cl > 0`, there is a linear family `A` (with the sheared
charts `linBase A k`) and homotopies `H0 k` from `planeClassMap (rotPresentation Q (u k))` to
`planeClassMap (diskPlane (linPlaneChart (linBase A k) cl hcl))`, seam-invariant, continuous, with `C^∞`
chains. -/
theorem exists_linBase_homotopies {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (u : Fin 3 → ℝ) (cl : ℝ) (hcl : 0 < cl) :
    ∃ (A : Eucl 3 ≃L[ℝ] Eucl 3)
      (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)),
      (∀ k, (fun y => H0 k (0, y))
          = planeClassMap (rotPresentation Q ((u k : ℝ) : UnitAddCircle))) ∧
      (∀ k, (fun y => H0 k (1, y))
          = planeClassMap (diskPlane (linPlaneChart (linBase A k) cl hcl))) ∧
      (∀ (k : Fin 3) (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        onSeam2 y → H0 k (t, seamInv2 y) = H0 k (t, y)) ∧
      (∀ k, Continuous (H0 k)) ∧
      (∀ k, ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, mk2 (x 0) (x 1)))) := by
  -- the lift of the chart's class map, and the essentiality of its boundary curve
  obtain ⟨V, hVne, hVsm, hQcls⟩ := exists_classLift_of_isPlaneChart hγne hQ
  have hVneC : ∀ z : ℂ, ‖z‖ = 1 → V z ≠ 0 := fun z _ => hVne z
  have hVcont : ContinuousOn V {z : ℂ | ‖z‖ = 1} := hVsm.continuous.continuousOn
  have hVcls : ∀ z : ℂ, ∀ hz : ‖z‖ = 1,
      Projectivization.mk ℝ (V z) (hVneC z hz) = (cappingSpaceHomeoProj (Q z)).2 :=
    fun z _ => (hQcls z).symm
  obtain ⟨hpar, hneg⟩ :=
    exists_neg_parallelism_of_planeChart_of_isPlaneChart hγinj hγne hQ V hVneC hVcont hVcls
  -- the three curves on the real diameter
  have hWne : ∀ (k : Fin 3) (t : ℝ), diagRotL (u k) (V ((t : ℝ) : ℂ)) ≠ 0 := by
    intro k t
    rw [diagRotL_apply]
    exact diagRot_ne_zero _ (hVne _)
  have hWsm : ∀ k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => diagRotL (u k) (V ((t : ℝ) : ℂ))) := by
    intro k
    exact ((diagRotL (u k) : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp
      (hVsm.comp Complex.ofRealCLM.contDiff)
  -- the linear automorphism avoiding the anti-parallel cone, and the repaired linear family
  obtain ⟨A, -, hAavoid⟩ := exists_trans_avoid_negParallel_cr
    (fun k t => diagRotL (u k) (V ((t : ℝ) : ℂ))) hWne hWsm 1 one_pos
  -- the non-collision condition `hgood` at the zero locus of the weight `χ z = z.im`
  have hgood : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → z.im = 0 →
      ¬ ∃ lam : ℝ, (linBase A k (linVecC z)) = lam • (diagRotL (u k) (V z)) ∧ lam < 0 := by
    intro k z hz hzim hbad
    obtain ⟨lam, hlam, hlt⟩ := hbad
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using hzim)
    have hmem : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
      have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hzim] at h1
      have h2 : z.re ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hz]
      constructor <;> nlinarith [sq_nonneg z.re]
    refine hAavoid k z.re hmem ⟨lam, hlt, ?_⟩
    have hb : linBase A k (linVecC z)
        = ((coordPermCLM (coordPerms k)).trans A) (linVecC ((z.re : ℝ) : ℂ)) := by
      conv_lhs => rw [hzre]
      rw [linBase_apply, linShear_linVecC_ofReal, ContinuousLinearEquiv.trans_apply]
    have hv : (diagRotL (u k)) (V z) = (diagRotL (u k)) (V ((z.re : ℝ) : ℂ)) := by
      conv_lhs => rw [hzre]
    rw [hb] at hlam
    rw [hv] at hlam
    exact hlam
  -- the homotopies
  obtain ⟨H, h0, h1, h2, h3, h4⟩ := exists_homotopyClauses_rotPresentation Q V hVne hVsm hQcls hpar
    (z₀ := 1) (by norm_num) hneg u (fun k => linBase A k) cl hcl
    (fun k z => z.im) (fun k => Complex.imCLM.contDiff) (fun k z _ => by simp) hgood
  exact ⟨A, H, h0, h1, h2, h3, h4⟩


/-! ## 2. The class map of a chart-perturbed presentation -/

/-- **The class map of a chart-perturbed plane presentation** is the class map of the plane
post-composed with the class action `classMap τ`. -/
theorem planeClassMap_chartPert_comp_cr (τ : Eucl 3) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    planeClassMap (fun y => chartPert τ (P y)) = classMap τ ∘ planeClassMap P := by
  funext y
  simp only [Function.comp_apply, planeClassMap, cappingSpaceHomeoProj_chartPert, coordFam_snd]

/-- The class action is `C^∞` at a fixed parameter. -/
theorem contMDiff_classMap_fixed_cr (τ : Eucl 3) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (classMap τ) :=
  fun p => contMDiffAt_classMap_point τ p

/-! ## 3. The time retraction and the transported homotopies -/

/-- The smooth retraction of the time line onto the interval `[0,1]` (`0` on `(-∞,0]`, `1` on `[1,∞)`). -/
def timeSat (s : ℝ) : ℝ := Real.smoothTransition s

@[simp] lemma timeSat_zero : timeSat 0 = 0 := Real.smoothTransition.zero_of_nonpos (le_refl 0)

lemma timeSat_of_nonpos {s : ℝ} (hs : s ≤ 0) : timeSat s = 0 :=
  Real.smoothTransition.zero_of_nonpos hs

lemma timeSat_of_one_le {s : ℝ} (hs : 1 ≤ s) : timeSat s = 1 :=
  Real.smoothTransition.one_of_one_le hs

lemma contDiff_timeSat : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) timeSat :=
  Real.smoothTransition.contDiff

/-- The reparametrisation of `𝔼³` replacing the third coordinate by its retraction: the shape in which
a time reparametrisation of a chain can be pushed to the level of `𝔼³`. -/
def satMap (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  x + (timeSat (x 2) - x 2) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

@[simp] lemma satMap_apply_zero (x : EuclideanSpace ℝ (Fin 3)) : satMap x 0 = x 0 := by
  simp [satMap]
@[simp] lemma satMap_apply_one (x : EuclideanSpace ℝ (Fin 3)) : satMap x 1 = x 1 := by
  simp [satMap]
@[simp] lemma satMap_apply_two (x : EuclideanSpace ℝ (Fin 3)) : satMap x 2 = timeSat (x 2) := by
  simp [satMap]

lemma contMDiff_satMap : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) satMap := by
  rw [contMDiff_iff_contDiff]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => timeSat (x 2) - x 2) :=
    (contDiff_timeSat.comp (by fun_prop)).sub (by fun_prop)
  exact contDiff_id.add (h1.smul contDiff_const)

/-- **The transported homotopy** of the design's `k`-th block at the parameter `t`: the `(B)`-lane
homotopy `H0 k`, class-perturbed by `classMap (blk k t)` and with its time retracted into `[0,1]`. -/
def transportHom (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  fun q => classMap ((blk k) t) (H0 k (timeSat q.1, q.2))

lemma transportHom_left (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    {s : ℝ} (hs : s ≤ 0) (y : EuclideanSpace ℝ (Fin 2)) :
    transportHom H0 t k (s, y) = transportHom H0 t k (0, y) := by
  simp only [transportHom, timeSat_of_nonpos hs, timeSat_zero]

lemma transportHom_right (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    {s : ℝ} (hs : 1 ≤ s) (y : EuclideanSpace ℝ (Fin 2)) :
    transportHom H0 t k (s, y) = transportHom H0 t k (1, y) := by
  simp only [transportHom, timeSat_of_one_le hs, timeSat_of_one_le (le_refl 1)]

lemma transportHom_seam (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (hH : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H0 k (s, seamInv2 y) = H0 k (s, y))
    (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (hy : onSeam2 y) :
    transportHom H0 t k (s, seamInv2 y) = transportHom H0 t k (s, y) := by
  simp only [transportHom]
  rw [hH (timeSat s) y hy]

lemma transportHom_zero_eq (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    {A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : (fun y => H0 k (0, y)) = A) :
    (fun y => transportHom H0 t k (0, y)) = classMap ((blk k) t) ∘ A := by
  funext y
  simp only [Function.comp_apply, transportHom, timeSat_zero, congrFun h y]

lemma transportHom_one_eq (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    {A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : (fun y => H0 k (1, y)) = A) :
    (fun y => transportHom H0 t k (1, y)) = classMap ((blk k) t) ∘ A := by
  funext y
  simp only [Function.comp_apply, transportHom, timeSat_of_one_le (le_refl 1), congrFun h y]

/-- **The chain smoothness of the transported homotopy**, from the chain smoothness of `H0` and the
time reparametrisation pushed to `𝔼³`. -/
lemma contMDiff_transportHom_chain
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (h : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => transportHom H0 t k (x 2, mk2 (x 0) (x 1))) := by
  have hcomp := (contMDiff_classMap_fixed_cr ((blk k) t)).comp (h.comp contMDiff_satMap)
  have heq : (fun x : EuclideanSpace ℝ (Fin 3) =>
        transportHom H0 t k (x 2, mk2 (x 0) (x 1)))
      = fun x : EuclideanSpace ℝ (Fin 3) =>
          classMap ((blk k) t) (H0 k (satMap x 2, mk2 (satMap x 0) (satMap x 1))) := by
    funext x
    simp only [transportHom, satMap_apply_two, satMap_apply_zero, satMap_apply_one]
  rw [heq]
  exact hcomp

/-! ## 4. The design-level ends of the transported homotopy -/

/-- **The `s = 0` end of the transported homotopy is the perturbed design plane.** -/
theorem transportHom_zero_design (Q : ℂ → CappingSpace)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (u : Fin 3 → UnitAddCircle)
    (hH0 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (0, y) = planeClassMap (rotPresentation Q (u k)) y)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    (fun y => transportHom H0 t k (0, y))
      = designPertClass Q (u k) t k := by
  rw [transportHom_zero_eq H0 t k (funext (hH0 k))]
  funext y
  show classMap ((blk k) t) (planeClassMap (rotPresentation Q (u k)) y)
      = planeClassMap (fun y' => chartPert ((blk k) t) (rotPresentation Q (u k) y')) y
  rw [planeClassMap_chartPert_comp_cr]
  rfl

/-- **The `s = 1` end of the transported homotopy is the transported linear model.** -/
theorem transportHom_one_design (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hH0 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (1, y) = planeClassMap (diskPlane (linPlaneChart (Φ k) cl hcl)) y)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    (fun y => transportHom H0 t k (1, y))
      = linTransClass (Φ k) ((blk k) t) cl hcl := by
  rw [transportHom_one_eq H0 t k (funext (hH0 k))]
  funext y
  show classMap ((blk k) t) (planeClassMap (diskPlane (linPlaneChart (Φ k) cl hcl)) y)
      = planeClassMap (diskPlane (linPlaneChart ((Φ k).trans (classEquiv ((blk k) t))) cl hcl)) y
  rw [show classMap ((blk k) t) (planeClassMap (diskPlane (linPlaneChart (Φ k) cl hcl)) y)
        = planeClassMap (fun y' => chartPert ((blk k) t)
            (diskPlane (linPlaneChart (Φ k) cl hcl) y')) y
        from (congrFun (planeClassMap_chartPert_comp_cr ((blk k) t)
          (diskPlane (linPlaneChart (Φ k) cl hcl))) y).symm,
      planeClassMap_chartPert_diskPlane_linPlaneChart]

/-! ## 5. The fold-flatness of the design's presentations -/

theorem foldFlat_designPertClass (Q : ℂ → CappingSpace) (hQ : IsSmoothChart Q)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    FoldFlat (designPertClass Q (u k) t k) :=
  foldFlat_chartPert_rotPresentation Q (u k) ((blk k) t) hQ

theorem foldFlat_linTransClass (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (τ : Eucl 3) : FoldFlat (linTransClass Φ τ cl hcl) :=
  foldFlat_diskPlane_linPlaneChart (Φ.trans (classEquiv τ)) cl hcl

end

end Work.Drive
