import Mathlib
import Submission.Work.Drive.diskModelMap
import Submission.Work.Drive.linPlaneTripleCount
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.linPlaneChart_eq_iff

/-!
# The end contribution with *reparametrised* linear plane charts

`Work.Drive.ncard_linPlaneTriples_eq_one` computes the end contribution `Σ_k bottom_k ≡ 1` for the
three plane charts `linPlaneChart (φ k) c hc` themselves.  The sweep construction of the end
contribution, however, cannot use those charts directly: interpolating the *classes* from the curve's
plane presentation to a linear plane presentation degenerates on the "diagonal" where the two class
maps agree (and that diagonal is never empty, `END_CONTRIBUTION_STATUS.md` §2(a)).  The prescribed fix
(`END_CONTRIBUTION_STATUS.md` §5) is to *reparametrise* each bottom chart by a self-map `χ k` of the
disk model of `ℝP²`, so that the diagonal becomes a single point at which the sign can be flipped.

This file provides the counting half of that fix: the end contribution is still `1` when each chart is
replaced by `linPlaneChart (φ k) c hc ∘ χ k` with `χ k` a `Work.Drive.DiskModelMap` — a self-map of the
closed disk which is a bijection modulo the antipodal identification of the boundary circle.  The
argument is exactly the one of `Work.Drive.ncard_linPlaneTriples_eq_one`, with the single extra
observation that a disk-model self-map has a **unique interior preimage** of every interior point
(`Work.Drive.DiskModelMap.existsUnique_norm_lt_one`), which is what the fibre computation needs.

Note on the target of the fibre statement: the fibre is taken over the *plane point*
`linPlaneChart (φ k) c hc z` (not over `linPlaneChart (φ k) c hc (χ k z)`), because that is the value a
triple parameter must share: the common value of the three charts is `linCommonPt`
(`Work.Drive.tripleMeet_linPlaneCharts_comp`), and each chart attains it at an interior disk point.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The fibre of a reparametrised linear plane chart is a singleton.**  For an interior point `z` of
the disk, the folded square presentation of the reparametrised chart `linPlaneChart φ c hc ∘ χ`
attains the plane point `linPlaneChart φ c hc z` at exactly one point of the unit square.

(`χ` is only assumed to be a self-map of the disk model, so it may collapse the interior onto points
of the boundary; that is harmless here because the *target* of the fibre is the interior point
`linPlaneChart φ c hc z`, and `Work.Drive.linPlaneChart_eq_iff` then forces the attained disk point to
be `z` itself.) -/
theorem existsUnique_fibre_diskPlane_comp (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    {χ : ℂ → ℂ} (hχ : DiskModelMap χ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      diskPlane (linPlaneChart φ c hc ∘ χ) y = linPlaneChart φ c hc z := by
  classical
  -- the unique interior preimage of `z` under `χ`
  obtain ⟨w, ⟨hwlt, hwz⟩, hwuniq⟩ := hχ.existsUnique_norm_lt_one hz
  -- the unique square point with `sqDisk (foldBox y) = w`
  obtain ⟨y₀, ⟨hy₀box, hy₀w⟩, hy₀uniq⟩ := sqDisk_foldBox_existsUnique w (le_of_lt hwlt)
  refine ⟨y₀, ⟨hy₀box, ?_⟩, ?_⟩
  · simp only [diskPlane_apply, Function.comp_apply, hy₀w, hwz]
  · intro y hy
    -- the disk point attained at `y` is `z`
    have hln : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
    have heq : linPlaneChart φ c hc (χ (sqDisk (foldBox y))) = linPlaneChart φ c hc z := by
      simpa only [diskPlane_apply, Function.comp_apply] using hy.2
    rcases (linPlaneChart_eq_iff φ c hc (hχ.norm_le_one _ hln) (le_of_lt hz)).mp heq with h | ⟨-, hz1, -⟩
    · have hult : ‖sqDisk (foldBox y)‖ < 1 := by
        rcases lt_or_eq_of_le hln with h' | h'
        · exact h'
        · exfalso
          have h1 : ‖χ (sqDisk (foldBox y))‖ = 1 := hχ.norm_eq_one _ h'
          rw [h] at h1
          exact absurd h1 (ne_of_lt hz)
      exact hy₀uniq y ⟨hy.1, hwuniq _ ⟨hult, h⟩⟩
    · exact absurd hz1 (ne_of_lt hz)

/-- **The triple-parameter set of three reparametrised linear plane charts.**  The common value of the
three charts at a triple parameter is forced to be `Work.Drive.linCommonPt`; no hypothesis is needed on
the reparametrisations. -/
theorem tripleMeet_linPlaneCharts_comp (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) (χ : Fin 3 → ℂ → ℂ) :
    {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0)
          = diskPlane (linPlaneChart (φ 1) c hc ∘ χ 1) (x 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0)
          = diskPlane (linPlaneChart (φ 2) c hc ∘ χ 2) (x 2)}
      = {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        ∀ k, diskPlane (linPlaneChart (φ k) c hc ∘ χ k) (x k) = linCommonPt φ c hc h} := by
  ext x
  constructor
  · rintro ⟨hbox, h01, h02⟩
    have hlevel : ((cappingSpaceHomeoProj
        (diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0))).1 : ℝ) = c := by
      simp only [diskPlane_apply, Function.comp_apply]
      exact level_linPlaneChart (φ 0) c hc (χ 0 (sqDisk (foldBox (x 0))))
    have hclass : ∀ k : Fin 3,
        (cappingSpaceHomeoProj
          (diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0))).2
          ∈ projLine (linSub (φ k)) := by
      intro k
      fin_cases k
      · simp only [diskPlane_apply, Function.comp_apply]
        exact linPlaneChart_mem_projLine (φ 0) c hc (χ 0 (sqDisk (foldBox (x 0))))
      · rw [h01]
        simp only [diskPlane_apply, Function.comp_apply]
        exact linPlaneChart_mem_projLine (φ 1) c hc (χ 1 (sqDisk (foldBox (x 1))))
      · rw [h02]
        simp only [diskPlane_apply, Function.comp_apply]
        exact linPlaneChart_mem_projLine (φ 2) c hc (χ 2 (sqDisk (foldBox (x 2))))
    have hval0 : diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0) = linCommonPt φ c hc h :=
      eq_linCommonPt φ c hc h hlevel hclass
    refine ⟨hbox, fun k => ?_⟩
    fin_cases k
    · exact hval0
    · exact h01.symm.trans hval0
    · exact h02.symm.trans hval0
  · rintro ⟨hbox, hall⟩
    exact ⟨hbox, by rw [hall 0, hall 1], by rw [hall 0, hall 2]⟩

/-- **The end contribution with reparametrised linear plane charts is exactly one.**  Three linear
projective planes of one level in general position, presented as folded square maps through
disk-model self-maps `χ k`, with their common point off the three charts' lines at infinity (`hgen`),
have exactly one common triple of unit-square parameters. -/
theorem ncard_linPlaneReparamTriples_eq_one (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (χ : Fin 3 → ℂ → ℂ) (hχ : ∀ k, DiskModelMap (χ k))
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc h) :
    {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0)
          = diskPlane (linPlaneChart (φ 1) c hc ∘ χ 1) (x 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc ∘ χ 0) (x 0)
          = diskPlane (linPlaneChart (φ 2) c hc ∘ χ 2) (x 2)}.ncard = 1 := by
  rw [tripleMeet_linPlaneCharts_comp φ c hc h χ]
  have hfib : ∀ k : Fin 3, ∃! y : EuclideanSpace ℝ (Fin 2),
      y ∈ Submission.Drive.unitBox 1 ∧
        diskPlane (linPlaneChart (φ k) c hc ∘ χ k) y = linCommonPt φ c hc h := by
    intro k
    obtain ⟨z, hzlt, hzeq⟩ := exists_norm_lt_one_linPlaneChart_eq φ c hc h k (hgen k)
    have hf := existsUnique_fibre_diskPlane_comp (φ k) c hc (hχ k) hzlt
    rw [hzeq] at hf
    exact hf
  refine (Set.ncard_eq_one).mpr ⟨fun k => (hfib k).choose, ?_⟩
  ext x
  constructor
  · rintro ⟨hbox, hall⟩
    exact funext fun k => (hfib k).choose_spec.2 (x k) ⟨hbox k, hall k⟩
  · rintro rfl
    exact ⟨fun k => (hfib k).choose_spec.1.1, fun k => (hfib k).choose_spec.1.2⟩

/-! ## The seam condition of a reparametrised chart

The counting engine's `Meet3Hyp.seam` requires the chain of a plane to be invariant under the antipodal
involution of its parameter square.  For a folded presentation `diskPlane Q = Q ∘ sqDisk ∘ foldBox`
this is automatic as soon as `Q` identifies antipodal boundary points (`Work.Drive.diskPlane_seamInv2`,
the `χ = id` case).  For a *reparametrised* chart `Q ∘ χ` there are two ways in which the
identification survives:

* `χ` is **odd** on the boundary circle (`χ (-z) = -χ z`, the case of a self-map of `ℝP²`): then
  `(Q ∘ χ) (-z) = Q (-χ z) = Q (χ z) = (Q ∘ χ) z`, using the antipodal invariance of `Q` and the
  preservation of the boundary by `χ`;
* `χ` is **even** on the boundary circle, in which case the identification is immediate.

Both are recorded here, in the form the chain condition consumes. -/

/-- **A reparametrisation which is odd on the boundary circle preserves the seam identification.** -/
theorem diskPlane_comp_seamInv2_odd {Q : ℂ → CappingSpace}
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) {χ : ℂ → ℂ} (hχ : DiskModelMap χ)
    (hodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = -χ z) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : onSeam2 y) :
    diskPlane (Q ∘ χ) (seamInv2 y) = diskPlane (Q ∘ χ) y := by
  refine diskPlane_seamInv2 (Q := Q ∘ χ) ?_ hy
  intro z hz
  simp only [Function.comp_apply, hodd z hz, hQ (χ z) (hχ.norm_eq_one z hz)]

/-- **A reparametrisation which is even on the boundary circle preserves the seam identification.** -/
theorem diskPlane_comp_seamInv2_even {Q : ℂ → CappingSpace} {χ : ℂ → ℂ}
    (heven : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = χ z) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : onSeam2 y) :
    diskPlane (Q ∘ χ) (seamInv2 y) = diskPlane (Q ∘ χ) y := by
  refine diskPlane_seamInv2 (Q := Q ∘ χ) ?_ hy
  intro z hz
  simp only [Function.comp_apply, heven z hz]

end

end Work.Drive
