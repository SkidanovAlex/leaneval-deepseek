import Mathlib
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.chartLevelData
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.odd_ncard_zeros_of_neg_pos
import Submission.Work.Drive.linStd_finrank
import Submission.Work.Drive.linVecC_smul_surjective

/-!
# Level separation of the loop-vs-sweep pairing, and the reference plane's parity factor

`Work.Drive.coreSideCount Q c P` counts the parameter pairs at which the *core loop* of the chart `Q`
meets the clamped sweep of the plane presentation `P` at truncation level `c`
(`Submission/Work/Drive/sideCountDefs.lean`).  The sweep is a *radial* rescaling of the plane
(`Work.Drive.clampedSweep_apply`), so its level at a parameter `x` is
`c ^ (ψ (x 2)) · levelOf (P (x 0, x 1)) ^ (1 - ψ (x 2))` (`Work.Drive.log_levelOf_clampedSweep`), hence
between the truncation level `c` and the plane's level `levelOf (P (x 0, x 1))` whenever the cutoff
takes values in `[0,1]` (`Work.Drive.levelOf_clampedSweep_le_local`,
`Work.Drive.le_levelOf_clampedSweep_local`).

This file records the **separation principle** that follows: if the loop of the chart lies *strictly
above* every level of the swept plane, then there is no meet at all — the pairing is `0`, not merely
even.  Two specialisations are the ones the counting route consumes:

* the general `Work.Drive.coreMeet_eq_empty_of_level_lt` / `Work.Drive.coreSideCount_eq_zero_of_level_lt`
  (an *empty* meet set, so the statement is parameterisation-free);
* **the reference-plane factor** `Work.Drive.coreSideCount_linPlaneChart_eq_zero`: for the *linear*
  plane chart `Work.Drive.linPlaneChart φ lam hlam` — the disk model of the projective plane `φ (linStd)`
  at the level `lam` (`Submission/Work/Drive/linearPlaneChart.lean`) — whose loop lies at the single
  level `lam` (`Work.Drive.level_linPlaneChart`), the pairing against any plane swept at a level below
  `lam` vanishes.

## Why this matters (the `hn2` reference triple)

Hugelmeyer's Lemma 3 (antisymmetry of `≺`, i.e. `b u + b (-u) = 1` on `Zc γ`) is obtained in the
counting route by applying the triple parity identity
(`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`) to the triple
`(P_u, P_v, R)` where `R` is a **reference plane above the whole configuration**, together with the
multiplicativity (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`): the two factors of the
reference block are `Odd (coreSideCount (chart of R) c (sweep of P_u))` and the same with `P_v`, and
*both vanish* because the loop of `R` is at the level `lam` of `R`, above the levels swept by `P_u`
and `P_v`.  That is exactly the statement proved here (the level half of the reference data; the other
half — `Odd (coreSideCount (chart of P_u) c (sweep of R)) = 1`, the *essentiality* of the loop in the
class image of `R` — is the remaining input of `hn2`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **Level separation.**  If the truncation level `c` is positive and below every level of the swept
plane, and if the core loop of the chart lies *strictly above* every level of the swept plane, then the
core loop does not meet the sweep at all: `coreMeet Q c P = ∅`.

The hypothesis is stated so that it applies to the pairings where the chart is a plane of a *single*
level `lam` above the swept plane's levels. -/
theorem coreMeet_eq_empty_of_level_lt (Q : ℂ → CappingSpace) {c : ℝ} (hc : 0 < c)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPμ : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ y : EuclideanSpace ℝ (Fin 2),
      levelOf (P y) < levelOf (coreLoop Q t)) :
    coreMeet Q c P = ∅ := by
  by_contra hne
  obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hne
  simp only [coreMeet, Set.mem_setOf_eq] at hq
  obtain ⟨ht, hx, hmeet⟩ := hq
  have hxt : q.2 2 ∈ Set.Icc (0 : ℝ) 1 := hx 2
  have hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => 1 - t) s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hub : levelOf (clampedSweep c (fun t : ℝ => 1 - t) P q.2)
      ≤ levelOf (P (mk2 (q.2 0) (q.2 1))) :=
    levelOf_clampedSweep_le_local hc hψ01 P q.2 hxt (hPc (mk2 (q.2 0) (q.2 1)))
  have hlev : levelOf (coreLoop Q q.1)
      = levelOf (clampedSweep c (fun t : ℝ => 1 - t) P q.2) := congrArg levelOf hmeet
  have hhi := hPμ q.1 ht (mk2 (q.2 0) (q.2 1))
  have hlo := hPc (mk2 (q.2 0) (q.2 1))
  linarith

/-- **The separated pairing is `0`.** -/
theorem coreSideCount_eq_zero_of_level_lt (Q : ℂ → CappingSpace) {c : ℝ} (hc : 0 < c)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPμ : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ y : EuclideanSpace ℝ (Fin 2),
      levelOf (P y) < levelOf (coreLoop Q t)) :
    coreSideCount Q c P = 0 := by
  rw [coreSideCount, coreMeet_eq_empty_of_level_lt Q hc P hPc hPμ]
  simp

/-- **The separated pairing is even** (the form consumed by the parity engines). -/
theorem not_odd_coreSideCount_of_level_lt (Q : ℂ → CappingSpace) {c : ℝ} (hc : 0 < c)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPμ : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ y : EuclideanSpace ℝ (Fin 2),
      levelOf (P y) < levelOf (coreLoop Q t)) :
    ¬ Odd (coreSideCount Q c P) := by
  rw [coreSideCount_eq_zero_of_level_lt Q hc P hPc hPμ]
  simp

/-- **The separated pairing is `0` in `ZMod 2`.** -/
theorem coreSideCount_cast_eq_zero_of_level_lt (Q : ℂ → CappingSpace) {c : ℝ} (hc : 0 < c)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPμ : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ y : EuclideanSpace ℝ (Fin 2),
      levelOf (P y) < levelOf (coreLoop Q t)) :
    ((coreSideCount Q c P : ℕ) : ZMod 2) = 0 := by
  rw [coreSideCount_eq_zero_of_level_lt Q hc P hPc hPμ]
  simp

/-! ## The reference plane: the loop of a level plane lies above the swept levels -/

/-- **The loop of the linear plane chart lies at the level `lam` of the chart.**  `linPlaneChart φ lam hlam`
is the disk model of the projective plane `φ (linStd)` at the level `lam`
(`Work.Drive.cappingSpaceHomeoProj_linPlaneChart`), so every point of its core loop — which is the
image of the unit circle under the chart — has level `lam`. -/
theorem levelOf_coreLoop_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    levelOf (coreLoop (linPlaneChart φ lam hlam) t) = lam := by
  show ((cappingSpaceHomeoProj (linPlaneChart φ lam hlam
    (Complex.exp (Real.pi * (t : ℂ) * Complex.I)))).1 : ℝ) = lam
  exact level_linPlaneChart φ lam hlam _

/-- **The reference-plane factor.**  The pairing of the loop of the level-`lam` plane `φ (linStd)` with
a plane swept at levels strictly below `lam` and above the truncation level `c` is `0`: the sweep stays
below the loop (`Work.Drive.levelOf_clampedSweep_le_local`), so there is no meet.

This is the vanishing of the two factors of the reference block in the antisymmetry computation of
`hn2` (Hugelmeyer's Lemma 3 with a reference plane above the configuration). -/
theorem coreSideCount_linPlaneChart_eq_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) {lam c : ℝ} (hlam : 0 < lam)
    (hc : 0 < c) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPlam : ∀ y : EuclideanSpace ℝ (Fin 2), levelOf (P y) < lam) :
    coreSideCount (linPlaneChart φ lam hlam) c P = 0 := by
  refine coreSideCount_eq_zero_of_level_lt (linPlaneChart φ lam hlam) hc P hPc ?_
  intro t _ y
  rw [levelOf_coreLoop_linPlaneChart φ hlam t]
  exact hPlam y

/-- **The reference-plane factor, `Odd` form.** -/
theorem not_odd_coreSideCount_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) {lam c : ℝ} (hlam : 0 < lam)
    (hc : 0 < c) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPlam : ∀ y : EuclideanSpace ℝ (Fin 2), levelOf (P y) < lam) :
    ¬ Odd (coreSideCount (linPlaneChart φ lam hlam) c P) := by
  rw [coreSideCount_linPlaneChart_eq_zero φ hlam hc P hPc hPlam]
  simp

/-- **The reference-plane factor, `ZMod 2` form.** -/
theorem coreSideCount_cast_linPlaneChart_eq_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) {lam c : ℝ} (hlam : 0 < lam)
    (hc : 0 < c) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPc : ∀ y : EuclideanSpace ℝ (Fin 2), c ≤ levelOf (P y))
    (hPlam : ∀ y : EuclideanSpace ℝ (Fin 2), levelOf (P y) < lam) :
    ((coreSideCount (linPlaneChart φ lam hlam) c P : ℕ) : ZMod 2) = 0 := by
  rw [coreSideCount_linPlaneChart_eq_zero φ hlam hc P hPc hPlam]
  simp

/-! ## The rotated presentations inherit the disk bounds

`rotPresentation Q v y = rotCapping v (Q (sqDisk (foldBox y)))` and `sqDisk (foldBox y)` always lies in
the closed unit disk, so any level bound holding on `‖z‖ ≤ 1` holds for every rotated presentation at
every point of `ℝ²` (not only on the unit box). -/

theorem le_levelOf_rotPresentation (Q : ℂ → CappingSpace) {c : ℝ}
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z)) (v : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) : c ≤ levelOf (rotPresentation Q v y) := by
  rw [show rotPresentation Q v y = rotCapping v (Q (sqDisk (foldBox y))) from rfl, levelOf_rotCapping]
  exact h _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox y))

theorem levelOf_rotPresentation_le (Q : ℂ → CappingSpace) {β : ℝ}
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (v : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) : levelOf (rotPresentation Q v y) ≤ β := by
  rw [show rotPresentation Q v y = rotCapping v (Q (sqDisk (foldBox y))) from rfl, levelOf_rotCapping]
  exact h _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox y))

/-! ## Placing the reference plane above the configuration: the *upper* level bound

The truncation data `Work.Drive.exists_levelData_of_isPlaneChart` provides a level `c > 0` *below* the
chart's levels (and those of the rotated presentations).  The reference plane of the antisymmetry
argument has to be placed *above* them instead, which needs the complementary bound: the chart is a
continuous map of the *compact* closed disk into the capping space, and the level is a strictly positive
continuous function on it, so its image has a maximum `β`.

With that `β`, the linear plane chart at any level `lam > β` is a plane above the whole configuration,
and the vanishing of the reference block's factors is
`Work.Drive.not_odd_coreSideCount_reference` below. -/

/-- **The upper level bound of a plane chart.**  For a plane chart `Q` of `γ` there is `β > 0` above
the levels of `Q` on the closed unit disk. -/
theorem exists_levelUpper_of_isPlaneChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (Q : ℂ → CappingSpace) (hQ : IsPlaneChart γ hγne Q) :
    ∃ β : ℝ, 0 < β ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β := by
  have hcont : Continuous Q := continuous_of_isPlaneChart γ hγne Q hQ
  have hcontlvl : Continuous fun x : EuclideanSpace ℝ (Fin 2) => levelOf (Q (cplxOf x)) :=
    continuous_levelOf.comp (hcont.comp continuous_cplxOf)
  obtain ⟨x₀, -, hmax₀⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_isMaxOn
      (Metric.nonempty_closedBall.mpr zero_le_one) hcontlvl.continuousOn
  have hmax : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      levelOf (Q (cplxOf y)) ≤ levelOf (Q (cplxOf x₀)) := isMaxOn_iff.mp hmax₀
  refine ⟨levelOf (Q (cplxOf x₀)), levelOf_pos _, ?_⟩
  intro z hz
  have hz' : cplxOfInv z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← norm_cplxOf (cplxOfInv z),
      cplxOf_cplxOfInv]
    exact hz
  have h := hmax _ hz'
  simpa [cplxOf_cplxOfInv] using h

/-- **The reference block's factors vanish for the design's family.**  Let `Q` be a plane chart, `β` an
upper bound for its levels on the closed disk, `c` a truncation level below them and `φ` a linear
equivalence.  Then for every angle `v`, the pairing of the loop of the level-`lam` plane `φ (linStd)`
(`lam > β`) with the swept rotated presentation `rotPresentation Q v` is even.

This is the vanishing of the two factors of the *reference block* in the antisymmetry computation of
`hn2`: the reference plane lies above the configuration, so the loop of the reference is above the
sweeps of the rotated configuration planes (`Work.Drive.levelOf_clampedSweep_le_local`). -/
theorem not_odd_coreSideCount_reference (φ : Eucl 3 ≃L[ℝ] Eucl 3) (Q : ℂ → CappingSpace)
    {β c lam : ℝ} (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hc : 0 < c) (hlam : β < lam) (hlampos : 0 < lam) (v : UnitAddCircle) :
    ¬ Odd (coreSideCount (linPlaneChart φ lam hlampos) c (rotPresentation Q v)) :=
  not_odd_coreSideCount_linPlaneChart φ hlampos hc (rotPresentation Q v)
    (fun y => le_levelOf_rotPresentation Q hclow v y)
    (fun y => lt_of_le_of_lt (levelOf_rotPresentation_le Q hβ v y) hlam)

/-- **The reference block's factors vanish, `ZMod 2` form.**  The design's `designCount` consumes the
pairings as `ZMod 2` values. -/
theorem coreSideCount_cast_reference_eq_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) (Q : ℂ → CappingSpace)
    {β c lam : ℝ} (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hc : 0 < c) (hlam : β < lam) (hlampos : 0 < lam) (v : UnitAddCircle) :
    ((coreSideCount (linPlaneChart φ lam hlampos) c (rotPresentation Q v) : ℕ) : ZMod 2) = 0 :=
  coreSideCount_cast_linPlaneChart_eq_zero φ hlampos hc (rotPresentation Q v)
    (fun y => le_levelOf_rotPresentation Q hclow v y)
    (fun y => lt_of_le_of_lt (levelOf_rotPresentation_le Q hβ v y) hlam)

/-- **The level band of a plane chart.**  Every plane chart of `γ` lies in a *level band* `[c, β]` with
`0 < c < β`: the truncation data `Work.Drive.exists_levelData_of_isPlaneChart` supplies `c` below the
chart's levels on the closed disk (and those of all rotated presentations on the unit box), and the
upper bound `β` is `Work.Drive.exists_levelUpper_of_isPlaneChart`.

This is the exact datum a *reference plane* needs: `Work.Drive.linPlaneChart φ lam hlam` at any level
`lam > β` is a plane above the whole configuration, and the truncation level `c` is below it; then
`Work.Drive.not_odd_coreSideCount_reference` gives the vanishing of the reference block's two factors in
the antisymmetry computation (`hn2`, Hugelmeyer's Lemma 3). -/
theorem exists_levelBand_of_isPlaneChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (Q : ℂ → CappingSpace) (hQ : IsPlaneChart γ hγne Q) :
    ∃ c β : ℝ, 0 < c ∧ c ≤ β ∧ (∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z) ∧ levelOf (Q z) ≤ β) ∧
      (∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
        y ∈ Submission.Drive.unitBox 1 →
          c ≤ levelOf (rotPresentation Q v y) ∧ levelOf (rotPresentation Q v y) ≤ β) := by
  obtain ⟨c, hc, hlow, hrot⟩ := (exists_levelData_of_isPlaneChart γ hγne Q hQ).2
  obtain ⟨β, hβ, hup⟩ := exists_levelUpper_of_isPlaneChart γ hγne Q hQ
  have hcβ : c ≤ β :=
    le_trans (hlow 0 (by simp)) (hup 0 (by simp))
  exact ⟨c, β, hc, hcβ, fun z hz => ⟨hlow z hz, hup z hz⟩,
    fun v y hy => ⟨le_levelOf_rotPresentation Q hlow v y, levelOf_rotPresentation_le Q hup v y⟩⟩

/-! ## The reference plane is disjoint from the configuration (a transport input)

`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul` (the transport's T6) asks, for each swept
plane, that its *range* be disjoint from the chart's plane.  For the reference triple of `hn2` one of
the two swept planes is the reference plane itself; that disjointness is then free, because the two
planes have disjoint level ranges: the chart's plane lies in the level band `[c, β]` and the reference
plane at the level `lam > β`. -/

/-- **The configuration plane and a plane above it are disjoint.**  The range of any plane presentation
whose points all have level `≤ β` is disjoint from the range of a plane all of whose points have level
`lam > β`. -/
theorem disjoint_range_of_level_lt {P P' : EuclideanSpace ℝ (Fin 2) → CappingSpace} {β lam : ℝ}
    (hP : ∀ y, levelOf (P y) ≤ β) (hP' : ∀ y, lam ≤ levelOf (P' y)) (h : β < lam) :
    Disjoint (Set.range P) (Set.range P') := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy⟩ ⟨y', hy'⟩
  have h1 : levelOf p ≤ β := by rw [← hy]; exact hP y
  have h2 : lam ≤ levelOf p := by rw [← hy']; exact hP' y'
  linarith

/-- **The reference plane is disjoint from the configuration plane** (design shape): the rotated
configuration plane lies in the level band `[c, β]` of the chart, the linear plane at the level `lam` is
above it, so their ranges are disjoint.  This is the disjointness input `hdisj` of the transport
(`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`) at the reference triple of `hn2`. -/
theorem disjoint_range_rotPresentation_linPlanePt (φ : Eucl 3 ≃L[ℝ] Eucl 3) (Q : ℂ → CappingSpace)
    {β c lam : ℝ} (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (hlam : β < lam)
    (hlampos : 0 < lam) (v : UnitAddCircle) :
    Disjoint (Set.range (rotPresentation Q v)) (Set.range (linPlanePt φ lam hlampos)) := by
  refine disjoint_range_of_level_lt (P := rotPresentation Q v)
    (P' := linPlanePt φ lam hlampos) (β := β) (lam := lam) (fun y => ?_) (fun y => ?_) hlam
  · exact levelOf_rotPresentation_le Q hβ v y
  · simp [levelOf, cappingSpaceHomeoProj_linPlanePt]

/-! ## The equator crossing count of an anti-equivariant lift

The last ingredient of the reference factor `(F1)` of `hn2` (`HN2_REFERENCE_STATUS.md` §2): the class
loop of the chart is lifted to a *nonzero representative* `t ↦ V t ∈ Eucl 3` with the
**anti-equivariance** `V (t + 1) = -V t` (the essentiality of the core loop of the configuration
Möbius band), and the reference plane — which is ours to choose — is the projectivisation of the
hyperplane `{v : ℓ v = 0}` for a linear functional `ℓ` (for the standard linear plane,
`ℓ = (φ⁻¹ ·) 3`, `linearPlaneChart.lean`).  The class of `coreLoop Q t` then lies in the reference plane
iff `ℓ (V t) = 0`, and the number of such parameters in `[0,1)` is odd by
`Work.Drive.odd_ncard_zeros_of_neg_pos`, because `t ↦ ℓ (V t)` has opposite signs at `0` and `1`. -/

/-- **The parity of the equator crossings of an anti-equivariant lift.**  If `V : ℝ → Eucl 3` is
anti-equivariant (`V (t + 1) = -V t`), `ℓ : Eucl 3 →L[ℝ] ℝ` is a linear functional and the function
`f t = ℓ (V t)` is differentiable on `[0,1]` with finitely many zeros, all regular, and nonzero at
`t = 0`, then the number of parameters `t ∈ [0, 1)` at which the class of `V t` lies in the
projectivisation of `ker ℓ` is **odd**. -/
theorem odd_ncard_zeros_of_anti_lift (ℓ : Eucl 3 →L[ℝ] ℝ) (V : ℝ → Eucl 3)
    (hanti : ∀ t : ℝ, V (t + 1) = -V t) (h0 : ℓ (V 0) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => ℓ (V t))
      (deriv (fun t : ℝ => ℓ (V t)) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ ℓ (V t) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ℓ (V t) = 0 →
      deriv (fun t : ℝ => ℓ (V t)) t ≠ 0) :
    Odd ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ℓ (V t) = 0}).ncard := by
  have h1 : ℓ (V 1) = -ℓ (V 0) := by
    have := hanti 0
    simp only [zero_add] at this
    rw [this, map_neg]
  -- split on the sign of `f 0 = ℓ (V 0)`
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · refine odd_ncard_zeros_of_neg_pos hder hneg ?_ hfin hreg
    rw [h1]; linarith
  · -- `0 < ℓ (V 0)`: apply the lemma to the negated function
    set g : ℝ → ℝ := -(fun t : ℝ => ℓ (V t)) with hg
    have hg0 : g 0 < 0 := by
      rw [hg]
      simpa using neg_neg_of_pos hpos
    have hg1 : 0 < g 1 := by
      have hlt : ℓ (V 1) < 0 := by rw [h1]; linarith
      rw [hg]
      simpa using neg_pos.mpr hlt
    have hderg : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (deriv g x) x := by
      intro x hx
      have h := (hder x hx).neg
      have hd : deriv g x = -deriv (fun t : ℝ => ℓ (V t)) x := by
        rw [hg]
        exact deriv.neg
      rw [hd]
      simpa only [hg] using h
    have hfing : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0}).Finite := by
      rw [hg] at *
      simpa only [Pi.neg_apply, neg_eq_zero] using hfin
    have hregg : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 → deriv g t ≠ 0 := by
      intro t ht ht0
      have ht0' : ℓ (V t) = 0 := by
        rw [hg] at ht0
        simpa only [Pi.neg_apply, neg_eq_zero] using ht0
      have hd : deriv g t = -deriv (fun t : ℝ => ℓ (V t)) t := by
        rw [hg]
        exact deriv.neg
      rw [hd]
      exact neg_ne_zero.mpr (hreg t ht ht0')
    have hset : {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ℓ (V t) = 0}
        = {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ g t = 0} := by
      rw [hg]
      ext t
      simp only [Pi.neg_apply, neg_eq_zero, Set.mem_ofPred_eq]
    rw [hset]
    exact odd_ncard_zeros_of_neg_pos hderg hg0 hg1 hfing hregg

/-! ## The disk model of a linear plane covers the whole plane

`Work.Drive.linVecC z = (z, 1 - ‖z‖²) ∈ ℂ² = Eucl 3` and `linStd = span (range linVecC) = {v : v 3 = 0}`
(`Work.Drive.linStd_eq_ker_coord`).  The classes `[linVecC z]` sweep the whole projective plane
`projLine linStd` (the standard disk model of `ℝP²`), which is what makes the *plane presentation*
`linPlanePt`/`diskPlane (linPlaneChart …)` usable as a *cover* of the reference plane in the
identification `(1a)` of `HN2_REFERENCE_STATUS.md` §2 (a meet of the loop with the ramp exists as soon as
the loop's class lies in the plane's class image). -/

/-- **The disk model of the standard plane is onto it**: every class of `linStd` is the class of some
lift `linVecC z`. -/
theorem exists_mk_linVecC_eq (q : Projectivization ℝ (Eucl 3)) (hq : q ∈ projLine linStd) :
    ∃ z : ℂ, Projectivization.mk ℝ (linVecC z) (linVecC_ne_zero z) = q := by
  obtain ⟨v, hv0, hvU, rfl⟩ := hq
  have hv3 : v 3 = 0 := by
    have h := hvU
    rw [linStd_eq_ker_coord] at h
    simpa [linStdCoord_apply] using h
  have h3 : (c₂ v).im = 0 := by
    have h := congrArg (fun w : Eucl 3 => w 3) (ofComplex_c₁_c₂ v)
    simp [ofComplex] at h
    linarith [hv3]
  have hvrepr : v = ofComplex (c₁ v) (((c₂ v).re : ℝ) : ℂ) := by
    conv_lhs => rw [← ofComplex_c₁_c₂ v]
    congr 1
    exact Complex.ext rfl (by simpa using h3)
  have hw : c₁ v ≠ 0 ∨ (c₂ v).re ≠ 0 := by
    rcases eq_or_ne (c₁ v) 0 with h | h
    · right
      intro h0
      refine hv0 ?_
      rw [hvrepr, h, h0]
      simp [ofComplex]
    · exact Or.inl h
  obtain ⟨z, a, ha0, -, haeq⟩ := linVecC_smul_surjective hw
  refine ⟨z, ?_⟩
  rw [Projectivization.mk_eq_mk_iff' ℝ (linVecC z) v (linVecC_ne_zero z) hv0]
  refine ⟨a⁻¹, ?_⟩
  rw [hvrepr, ← haeq, smul_smul, inv_mul_cancel₀ ha0, one_smul]

/-- **The disk model of a linear plane covers it** (the `φ`-form): for every class `q` of the plane
`projLine (linSub φ) = φ (projLine linStd)` there is a disk parameter `z` whose linear plane chart has
class `q`.  This is the surjectivity that step `(1a)` of `HN2_REFERENCE_STATUS.md` §2 needs: a meet of
the loop with the ramp to the reference plane exists as soon as the loop's class lies in the plane. -/
theorem exists_linPlaneChart_class_eq (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (q : Projectivization ℝ (Eucl 3)) (hq : q ∈ projLine (linSub φ)) :
    ∃ z : ℂ, (cappingSpaceHomeoProj (linPlaneChart φ c hc z)).2 = q := by
  obtain ⟨w, hw0, hwU, rfl⟩ := hq
  obtain ⟨v, hvU, hvφ⟩ := Submodule.mem_map.mp hwU
  have hv0 : v ≠ 0 := fun h => hw0 (by rw [← hvφ, h, map_zero])
  obtain ⟨z, hz⟩ := exists_mk_linVecC_eq (Projectivization.mk ℝ v hv0) ⟨v, hv0, hvU, rfl⟩
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ (linVecC z) v (linVecC_ne_zero z) hv0).mp hz
  refine ⟨z, ?_⟩
  rw [cappingSpaceHomeoProj_linPlaneChart]
  refine (Projectivization.mk_eq_mk_iff' ℝ (φ (linVecC z)) w
    (fun h => linVecC_ne_zero z (φ.injective (by simpa using h))) hw0).mpr ⟨a, ?_⟩
  · have h1 : φ (a • v) = a • φ v := by simp
    have h2 : a • w = a • φ v := congrArg (fun x : Eucl 3 => a • x) hvφ.symm
    have h3 : φ (linVecC z) = φ (a • v) := congrArg (fun x : Eucl 3 => φ x) ha.symm
    exact h2.trans (h1.symm.trans h3.symm)

end

end Work.Drive
