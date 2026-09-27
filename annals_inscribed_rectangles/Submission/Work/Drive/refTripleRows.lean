import Mathlib
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.sweepTripleRot
import Submission.Work.Drive.diskLiftHomotopy
import Submission.Work.Drive.refTripleClause
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.chartPlaneDisjoint
import Submission.Work.Drive.chartPert_disjoint_image
import Submission.Work.Drive.goodPair_rotCapping

/-!
# The elementary interface facts of the reference triple (`hn2` node)

This module collects the small, parameter-free facts about the reference triple
`Work.Drive.refTriple Q R u v = ![rotPresentation Q u, rotPresentation Q v, R]` that the two
genericity chapters of `Work.Drive.hn2_refTripleAt_producer` consume:

* `Work.Drive.cls_linPlaneChart_eq_of_pos` / `Work.Drive.planeClassMap_linPlaneChart_eq_of_pos` — the
  *class* of a linear plane chart does not depend on the level, since
  `cappingSpaceHomeoProj (linPlaneChart φ c hc z) = (c, [φ (linVecC z)])` carries `c` only in the level
  coordinate.  Consequently the class maps of the two disk models of the reference plane (level `lam`
  and level `c`) agree (`Work.Drive.planeClassMap_refPlanePres_eq`), which is what lets the clause-`2`
  homotopy of `Work.Drive.hasClassLinearization_of_endData` be the **constant** one;
* `Work.Drive.refTriple_seam` — the seam invariance of the reference triple, from the seam invariance
  of the chart's plane presentation and of the reference plane (the `hPseam` input of
  `Work.Drive.hasClassLinearization_of_endData`);
* `Work.Drive.exists_homotopyClause_refPlane` — the constant homotopy of the class map of the reference
  plane, with the five properties (`s = 0` and `s = 1` ends, seam invariance, continuity, `C^∞` of the
  chain) that `Work.Drive.HasClassLinearization` asks of its third slot.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000

/-! ## 1. The class of a linear plane chart is level-independent -/

/-- **The class of a linear plane chart is independent of the level.** -/
lemma cls_linPlaneChart_eq_of_pos (φ : Eucl 3 ≃L[ℝ] Eucl 3) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 < c') (z : ℂ) :
    cls (linPlaneChart φ c hc z) = cls (linPlaneChart φ c' hc' z) := by
  simp only [cls_apply, cappingSpaceHomeoProj_linPlaneChart]

/-- **The class map of the disk model of a linear plane is level-independent.** -/
lemma planeClassMap_linPlaneChart_eq_of_pos (φ : Eucl 3 ≃L[ℝ] Eucl 3) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 < c') :
    planeClassMap (diskPlane (linPlaneChart φ c hc))
      = planeClassMap (diskPlane (linPlaneChart φ c' hc')) := by
  funext y
  simp only [planeClassMap, diskPlane_apply, cls_apply]
  exact cls_linPlaneChart_eq_of_pos φ hc hc' _

/-- **The class of a point of the reference plane is the class of the corresponding point of the disk
model of `φ 2` at any level.** -/
lemma cls_refPlanePres_eq (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    {c : ℝ} (hc : 0 < c) (y : EuclideanSpace ℝ (Fin 2)) :
    cls (refPlanePres φ lam hlam y)
      = cls (diskPlane (linPlaneChart (φ 2) c hc) y) :=
  congrFun (planeClassMap_linPlaneChart_eq_of_pos (φ 2) hlam hc) y

/-- **The class map of the reference plane is the class map of the disk model of `φ 2` at any level.**
This is the identity that makes the third clause-homotopy of `HasClassLinearization` constant. -/
lemma planeClassMap_refPlanePres_eq (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    {c : ℝ} (hc : 0 < c) :
    planeClassMap (refPlanePres φ lam hlam)
      = planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)) :=
  planeClassMap_linPlaneChart_eq_of_pos (φ 2) hlam hc

/-! ## 2. The seam invariance of the reference triple -/

/-- **The seam invariance of the reference triple**: if the chart `Q` is antipodally invariant on the
boundary circle and the reference plane `R` is seam-invariant, then so is every block of the reference
triple. -/
lemma refTriple_seam (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → R (seamInv2 y) = R y)
    (u v : UnitAddCircle) :
    ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → refTriple Q R u v k (seamInv2 y) = refTriple Q R u v k y := by
  intro k y hy
  fin_cases k
  · simpa [refTriple] using (rotPresentation_seamInv Q hQseam u y hy).symm
  · simpa [refTriple] using (rotPresentation_seamInv Q hQseam v y hy).symm
  · simpa [refTriple] using hRseam y hy

/-! ## 3. Continuity of the class projection -/

lemma continuous_cls : Continuous (cls : CappingSpace → Projectivization ℝ (Eucl 3)) :=
  continuous_snd.comp cappingSpaceHomeoProj.continuous

/-! ## 4. The constant clause-homotopy of the reference plane -/

/-- **The constant homotopy of the class map of the reference plane.**  Its two ends are the class map
of the reference plane and the disk model of the linear plane `φ 2` (equal by
`planeClassMap_refPlanePres_eq`); it is seam-invariant, continuous, and its chain is `C^∞`. -/
theorem exists_homotopyClause_refPlane (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    {c : ℝ} (hc : 0 < c) :
    ∃ H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ y : EuclideanSpace ℝ (Fin 2),
        H (0, y) = planeClassMap (refPlanePres φ lam hlam) y) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2),
        H (1, y) = planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)) y) ∧
      (∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        onSeam2 y → H (s, seamInv2 y) = H (s, y)) ∧
      Continuous H ∧
      ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) := by
  classical
  refine ⟨fun q => cls (refPlanePres φ lam hlam q.2), fun y => rfl, fun y => ?_, ?_, ?_, ?_⟩
  · exact (cls_refPlanePres_eq φ lam hlam hc y).trans rfl
  · intro s y hy
    refine congrArg cls ?_
    simpa only [refPlanePres] using diskPlane_seamInv2 (Q := linPlaneChart (φ 2) lam hlam)
      (fun z hz => linPlaneChart_neg (φ 2) lam hlam hz) hy
  · exact continuous_cls.comp (((refPlanePres_contMDiff φ lam hlam).continuous).comp
      continuous_snd)
  · have hf : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin 2) => cls (refPlanePres φ lam hlam y)) := fun y =>
      contMDiffAt_cls_of_contMDiff_gen (k := 2) (refPlanePres_contMDiff φ lam hlam) y
    exact hf.comp mk2CLM.contMDiff

/-! ## 5. The range of a plane presentation, and the disjointness bridge of the transport -/

/-- **The folded square parametrisation covers exactly the closed disk.** -/
lemma range_sqDisk_foldBox :
    Set.range (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y))
      = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
  · intro hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    obtain ⟨y, ⟨-, hy⟩, -⟩ := sqDisk_foldBox_existsUnique z hz
    exact ⟨y, hy⟩

/-- **The range of the plane presentation is the chart's disk.** -/
lemma range_diskPlane_eq_chartDisk (Q : ℂ → CappingSpace) :
    Set.range (diskPlane Q) = chartDisk Q := by
  have h1 : diskPlane Q = Q ∘ (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) := rfl
  rw [h1, chartDisk, Set.range_comp, range_sqDisk_foldBox]

/-- **The transport's whole-plane disjointness at a collision-free angle difference, from `hdisjZc`.**

`Work.Drive.hn2_refTripleAt_producer` carries the *abstract* disjointness `hdisjZc` of the chart's disk
against its rotations at the angles of `Zc γ`.  The transport clauses of `RefTripleAt` need the
disjointness of the two *rotated planes* at the angle difference, which is the case `w = v - u` of
`hdisjZc` — this lemma is that bridge. -/
theorem disjoint_range_rotPresentation_of_mem_Zc {γ : Circle → ℝ × ℝ}
    {Q : ℂ → CappingSpace}
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    {u v : UnitAddCircle} (huv : v - u ∈ Zc γ) :
    Disjoint (Set.range (rotPresentation Q u)) (Set.range (rotPresentation Q v)) := by
  have hbase : Disjoint (chartDisk Q) (rotCapping (v - u) '' chartDisk Q) := hdisjZc (v - u) huv
  rw [Set.disjoint_left] at hbase ⊢
  intro p hp hp'
  rw [range_rotPresentation_eq, range_diskPlane_eq_chartDisk] at hp hp'
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hbp⟩ := hp'
  have h1 : a = rotCapping (v - u) b := by
    apply rotCapping_injective u
    rw [rotCapping_apply_add, ← hbp]
    congr 1
    abel
  exact hbase ha ⟨b, hb, h1.symm⟩

/-! ## 7. The level separation of the reference blocks

The perturbed configuration blocks lie strictly below the perturbed reference plane as soon as
`2 ‖t‖ < log (lam / β)` (`Work.Drive.refBlock_level_lt_of_small`).  Since the level is a function, two
points at different levels are different: this is the *whole-plane disjointness* of the transport's
blocks `0`/`1` against the reference block `2`, which the T6 wrapper consumes
(`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp`, hypotheses `hdisj₂`, `hdisj₁₂`), and it
needs no geometry at all. -/

/-- **The two configuration blocks and the reference block have disjoint ranges.** -/
lemma disjoint_range_refBlock_config_refPlane {Q : ℂ → CappingSpace} {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (hβlam : β < lam) (u v : UnitAddCircle) {t : EuclideanSpace ℝ (Fin 12)}
    (ht : 2 * ‖t‖ < Real.log (lam / β)) {k : Fin 3} (hk : k ≠ 2) :
    Disjoint (Set.range (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k))
      (Set.range (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) := by
  rw [Set.disjoint_left]
  rintro p ⟨y, rfl⟩ ⟨y', hy'⟩
  have h := refBlock_level_lt_of_small hβpos hβ φ lam hlam hβlam u v ht hk y y'
  rw [hy'] at h
  exact (lt_irrefl _) h

/-- The strict level separation `β exp ‖t‖ < lam exp (-‖t‖)` of the reference triple, from
`2 ‖t‖ < log (lam / β)`. -/
lemma beta_exp_lt_lam_exp {β lam : ℝ} (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : 2 * ‖t‖ < Real.log (lam / β)) :
    β * Real.exp ‖t‖ < lam * Real.exp (-‖t‖) := by
  have hlog : Real.log β + ‖t‖ < Real.log lam - ‖t‖ := by
    have h := Real.log_lt_log hβpos hβlam
    rw [Real.log_div (ne_of_gt hlam) (ne_of_gt hβpos)] at ht
    linarith
  calc β * Real.exp ‖t‖ = Real.exp (Real.log β + ‖t‖) := by
        rw [Real.exp_add, Real.exp_log hβpos]
    _ < Real.exp (Real.log lam - ‖t‖) := Real.exp_lt_exp.mpr hlog
    _ = lam * Real.exp (-‖t‖) := by
        rw [Real.exp_sub, Real.exp_log hlam, Real.exp_neg, div_eq_mul_inv]

/-- **The perturbed configuration *chart* (on the closed disk) misses the perturbed reference block.**

This is the `hdisj₂` input of the T6 wrapper at the reference triple, in the pointwise form in which the
wrapper states it, with the chart parameter `z` restricted to the closed disk. -/
lemma chartPert_rotCapping_ne_refBlock_of_small {Q : ℂ → CappingSpace} {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (hβlam : β < lam) (w u v : UnitAddCircle) {t : EuclideanSpace ℝ (Fin 12)}
    (ht : 2 * ‖t‖ < Real.log (lam / β)) {k : Fin 3} (hk : k ≠ 2) :
    ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk k t) (rotCapping w (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y := by
  intro z y hz heq
  have hle : levelOf (chartPert (blk k t) (rotCapping w (Q z))) ≤ β * Real.exp ‖t‖ := by
    have hbound : levelOf (rotCapping w (Q z)) ≤ β := by
      rw [levelOf_rotCapping]; exact hβ z hz
    have hβnn : 0 ≤ β := le_trans (levelOf_pos (Q 0)).le (hβ 0 (by simp))
    rw [levelOf_chartPert_mul]
    exact mul_le_mul hbound (exp_coord_blk_le k t) (Real.exp_pos _).le hβnn
  have hbot : lam * Real.exp (-‖t‖)
      ≤ levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y) :=
    refBlock_level_ge φ lam hlam Q u v t y
  have hlt := beta_exp_lt_lam_exp hβpos hlam hβlam ht
  rw [heq] at hle
  linarith

/-- **The perturbed configuration chart on the closed disk misses the reference block's level.**

This is the `hlev` input of the T6 wrapper at the reference triple: the level of the perturbed
configuration chart on the closed disk stays strictly above the truncation level `cblk 2 = c / 4` of the
reference block, as soon as `‖t‖ < log 4` and the chart's disk levels are above `c`. -/
lemma levelOf_chartPert_rotCapping_ne_cblk {Q : ℂ → CappingSpace} (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) (u : UnitAddCircle)
    {cblk : Fin 3 → ℝ} (hcblk : cblk 2 = c / 4) {t : EuclideanSpace ℝ (Fin 12)}
    (ht : ‖t‖ < Real.log 4) (k : Fin 3) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (chartPert (blk k t) (rotCapping u (Q z))) ≠ cblk 2 := by
  intro z hz heq
  have hlow : c * Real.exp (-‖t‖) ≤ levelOf (chartPert (blk k t) (rotCapping u (Q z))) := by
    rw [levelOf_chartPert_mul, levelOf_rotCapping]
    exact mul_le_mul (le_of_lt (hcbot z hz)) (exp_coord_blk_ge k t) (Real.exp_pos _).le
        (levelOf_pos (Q z)).le
  have h4 : (1 : ℝ) / 4 < Real.exp (-‖t‖) := by
    have h := Real.exp_lt_exp.mpr (show -Real.log 4 < -‖t‖ by linarith)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using h
  have hquarter : c / 4 < c * Real.exp (-‖t‖) := by nlinarith [hc, h4]
  rw [heq, hcblk] at hlow
  linarith

/-! ## 8. The transport disjointness of the reference blocks at a small parameter

The T6 wrapper `Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` at block `0` of the
reference triple needs four disjointness/level facts about the *perturbed* blocks:

* the core chart (the perturbed rotated chart `chartPert (blk 0 t) ∘ rotCapping u ∘ Q`, on the closed
  disk) misses the *plane* of block `1` (`chartPert (blk 1 t) ∘ rotPresentation Q v`);
* it misses the reference block `2` — this is the level separation (§7);
* the planes of blocks `1` and `2` are disjoint — also the level separation;
* the level of the core chart on the disk differs from the truncation level `cblk 2`.

The first is the only one with geometric content: at `t = 0` the two images are
`rotCapping u '' chartDisk Q` and `rotCapping v '' chartDisk Q`, which are disjoint **exactly when
`v - u ∈ Zc γ`** (`Work.Drive.disjoint_range_rotPresentation_of_mem_Zc`); the robustness of the
disjointness under the chart perturbation is
`Work.Drive.chartPert_disjoint_image`. -/

/-- **The perturbed rotated charts are disjoint at a collision-free angle difference.**

`hdisjZc` at the angle `w = v - u` gives the disjointness of the two unperturbed rotated chart disks;
`Work.Drive.chartPert_disjoint_image` (with the compactness of the rotated chart disks) transfers it to
two independent small chart perturbations. -/
theorem chartPert_rotCapping_ne_chartPert_rotCapping_of_small {γ : Circle → ℝ × ℝ}
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace} (hQcont : Continuous Q)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    {u v : UnitAddCircle} (huv : v - u ∈ Zc γ) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ₀ τ₁ : Eucl 3, ‖τ₀‖ < r → ‖τ₁‖ < r →
      ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        chartPert τ₀ (rotCapping u (Q z))
          ≠ chartPert τ₁ (rotCapping v (Q (sqDisk (foldBox y)))) := by
  have hK : IsCompact (chartDisk Q) := chartDisk_compact hQcont
  have hKu : IsCompact (rotCapping u '' chartDisk Q) :=
    hK.image (continuous_rotCapping u)
  have hKv : IsCompact (rotCapping v '' chartDisk Q) :=
    hK.image (continuous_rotCapping v)
  have hdisj : Disjoint (rotCapping u '' chartDisk Q) (rotCapping v '' chartDisk Q) := by
    have h := disjoint_range_rotPresentation_of_mem_Zc (Q := Q) hdisjZc huv
    rwa [range_rotPresentation_eq, range_rotPresentation_eq, range_diskPlane_eq_chartDisk] at h
  obtain ⟨r, hr, hmain⟩ := chartPert_disjoint_image hKu hKv hdisj
  refine ⟨min r 1, lt_min hr one_pos, fun τ₀ τ₁ hτ₀ hτ₁ z y hz => ?_⟩
  intro heq
  have hz1 : ‖z‖ ≤ 1 := hz
  have hzmem : Q z ∈ chartDisk Q := by
    refine ⟨z, ?_, rfl⟩
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hymem : Q (sqDisk (foldBox y)) ∈ chartDisk Q := by
    refine ⟨sqDisk (foldBox y), ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
  have ht₀ : ‖τ₀‖ < r := lt_of_lt_of_le hτ₀ (min_le_left _ _)
  have ht₁ : ‖τ₁‖ < r := lt_of_lt_of_le hτ₁ (min_le_left _ _)
  have hmem₀ : chartPert τ₀ (rotCapping u (Q z))
      ∈ chartPert τ₀ '' (rotCapping u '' chartDisk Q) :=
    ⟨rotCapping u (Q z), ⟨Q z, hzmem, rfl⟩, rfl⟩
  have hmem₁ : chartPert τ₀ (rotCapping u (Q z))
      ∈ chartPert τ₁ '' (rotCapping v '' chartDisk Q) :=
    ⟨rotCapping v (Q (sqDisk (foldBox y))),
      ⟨Q (sqDisk (foldBox y)), hymem, rfl⟩, heq.symm⟩
  exact Set.disjoint_left.mp (hmain τ₀ τ₁ ht₀ ht₁) hmem₀ hmem₁

/-- **The transport disjointness of block `1` of the reference triple** (the exchange of the two
configuration blocks in `Work.Drive.transport_disins_reference_block`). -/
theorem transport_disins_reference_block' {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQcont : Continuous Q) {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (hβlam : β < lam)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    {u v : UnitAddCircle} (huv : v - u ∈ Zc γ) (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) {cblk : Fin 3 → ℝ}
    (hcblk : cblk 2 = c / 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      (∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        chartPert (blk 1 t) (rotCapping v (Q z))
          ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y) ∧
      (∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        chartPert (blk 1 t) (rotCapping v (Q z))
          ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y) ∧
      Disjoint (Set.range (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0))
        (Set.range (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 →
        levelOf (chartPert (blk 1 t) (rotCapping v (Q z))) ≠ cblk 2) := by
  obtain ⟨r₁, hr₁, h₁⟩ :=
    chartPert_rotCapping_ne_chartPert_rotCapping_of_small (hγne := hγne) (Q := Q) hQcont hdisjZc
      (u := v) (v := u) (by simpa using neg_mem_Zc huv)
  obtain ⟨r₂, hr₂, h₂⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      2 * ‖t‖ < Real.log (lam / β) := by
    refine ⟨Real.log (lam / β) / 4, ?_, ?_⟩
    · have h1 : 1 < lam / β := (one_lt_div hβpos).mpr hβlam
      have h2 : 0 < Real.log (lam / β) := Real.log_pos h1
      linarith
    · intro t ht
      linarith [norm_nonneg t]
  obtain ⟨r₃, hr₃, h₃⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      ‖t‖ < Real.log 4 :=
    ⟨Real.log 4, Real.log_pos (by norm_num), fun t ht => ht⟩
  refine ⟨min (min r₁ r₂) r₃, lt_min (lt_min hr₁ hr₂) hr₃, fun t ht => ?_⟩
  have ht₁ : ‖t‖ < r₁ :=
    lt_of_lt_of_le ht (le_trans (min_le_left (min r₁ r₂) r₃) (min_le_left r₁ r₂))
  have ht₂ : ‖t‖ < r₂ :=
    lt_of_lt_of_le ht (le_trans (min_le_left (min r₁ r₂) r₃) (min_le_right r₁ r₂))
  have ht₃ : ‖t‖ < r₃ := lt_of_lt_of_le ht (min_le_right (min r₁ r₂) r₃)
  have hsmall : 2 * ‖t‖ < Real.log (lam / β) := h₂ t ht₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z y hz heq
    have h := h₁ (blk 1 t) (blk 0 t) (lt_of_le_of_lt (norm_blk_le 1 t) ht₁)
      (lt_of_le_of_lt (norm_blk_le 0 t) ht₁) z y hz
    rw [show refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y
        = chartPert (blk 0 t) (rotCapping u (Q (sqDisk (foldBox y)))) from rfl] at heq
    exact h heq
  · intro z y hz
    exact chartPert_rotCapping_ne_refBlock_of_small hβpos hβ φ lam hlam hβlam v u v hsmall
      (k := 1) (by decide) z y hz
  · exact disjoint_range_refBlock_config_refPlane hβpos hβ φ lam hlam hβlam u v hsmall
      (k := 0) (by decide)
  · intro z hz
    exact levelOf_chartPert_rotCapping_ne_cblk c hc hcbot v hcblk (h₃ t ht₃) 1 z hz

/-! ## 9. The smoothness and seam invariance of the perturbed blocks

The remaining mechanical inputs of the T6 wrapper
(`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp`, hypotheses `hQ`, `hQseam`, `hP₁`,
`hP₂`, `hP₁seam`, `hP₂seam`) at the reference triple: the perturbed configuration *chart*
(`chartPert (blk k t) ∘ rotCapping u ∘ Q`, whose seam condition is the antipodal invariance of `Q` on
the circle) and the three perturbed *blocks* `refBlock … t k`. -/

/-- **The perturbed reference blocks are smooth.** -/
theorem contMDiff_refBlock {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (t : EuclideanSpace ℝ (Fin 12)) :
    ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k) := by
  intro k
  have h := contMDiff_chartPert.comp
    ((contMDiff_const (c := blk k t)).prodMk
      (refTriple_contMDiff Q hQsm φ lam hlam u v k))
  exact h

/-- **The perturbed configuration chart is smooth.** -/
theorem contMDiff_chartPert_rotCapping {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (u : UnitAddCircle) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => chartPert (blk k t) (rotCapping u (Q z))) := by
  have h1 : ContMDiff (modelWithCornersSelf ℝ ℂ) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => rotCapping u (Q z)) :=
    (contMDiff_rotCapping_apply u).comp hQsm
  have h := contMDiff_chartPert.comp
    ((contMDiff_const (c := blk k t)).prodMk h1)
  exact h

/-- **The seam invariance of the perturbed configuration chart** (the antipodal invariance of the
plane chart on the boundary circle). -/
theorem chartPert_rotCapping_seam {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (u : UnitAddCircle) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    ∀ z : ℂ, ‖z‖ = 1 →
      chartPert (blk k t) (rotCapping u (Q (-z))) = chartPert (blk k t) (rotCapping u (Q z)) := by
  intro z hz
  rw [hQseam z hz]

/-- **The seam invariance of the perturbed reference blocks.** -/
theorem refBlock_seam (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → R (seamInv2 y) = R y)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) :
    ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y →
        refBlock (fun s p => chartPert s p) Q R u v t k (seamInv2 y)
          = refBlock (fun s p => chartPert s p) Q R u v t k y := by
  intro k y hy
  exact congrArg (chartPert (blk k t)) (refTriple_seam Q R hQseam hRseam u v k y hy)

end

end Work.Drive
