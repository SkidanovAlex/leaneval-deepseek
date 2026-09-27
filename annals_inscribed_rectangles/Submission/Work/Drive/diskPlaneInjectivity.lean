import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.sqDisk_injective
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.collapseFaceAvoid
import Submission.Work.Drive.linPlaneChart_eq_iff
import Submission.Work.Drive.coreLoop_injective_mod_one
import Submission.Work.Drive.meetBoxEngine

/-!
# Injectivity of a disk presentation of a plane, and the `hinj` clause of the locality engine

`Work.Drive.diskPlane Q y = Q (sqDisk (foldBox y))` presents the capped plane `Q '' closedBall` by the
unit square `[0,1]²`.  This file collects the *injectivity* statements about that presentation, which
are the ones the counting lane needs in order to identify a *parameter* meet set with a set of *points*
(the clause `hinj` of `Work.Drive.meetPt_ncard_eq_of_regular_manifold`, and the fibre statements of the
`(SURF)` transport, cf. `planePtFibre.lean`):

* `Work.Drive.sqDisk_foldBox_injOn_unitBox` — the square factor `sqDisk ∘ foldBox` is injective on the
  unit box (`sqDisk` on the square, `foldBox` on the interval, both proved elsewhere);
* `Work.Drive.diskPlane_injOn_unitBox_of_injOn_closedBall` — hence `diskPlane Q` is injective on the
  unit box as soon as `Q` is injective on the closed unit disk;
* `Work.Drive.diskPlane_injOn_interior_of_seamInjOn` — the honest form (the chart of `ℝP²` is never
  injective on the closed disk: it identifies *antipodal boundary points*), in which only the
  **strictly interior** box points are separated;
* `Work.Drive.diskPlane_linPlaneChart_injOn_interior` — the **unconditional** instance for the linear
  plane chart, from the proved `Work.Drive.linPlaneChart_eq_iff`;
* `Work.Drive.meetBox_hinj_of_chain_inj` — the `hinj` clause of the locality engine, with the *chain*
  half isolated as an explicit injectivity hypothesis and the *loop* half discharged by the proved
  `Work.Drive.coreLoop_injective_mod_one` (the core loop of a plane chart is a simple closed curve).

## A finding recorded for the counting lane (see `HANDOFF.md`)

`IsPlaneChart` does **not** imply that `Q` is injective on the closed disk, and the chart produced by
`Work.Drive.exists_planeChart` is in fact *constant* on a neighbourhood of `0`: its cap lift is
`V z = capProjVecOf (Ω z) (dc z)` with `dc z = 0` for `‖z‖ < ρ` and `Ω z = exp (i · χ z · ψ z)` where
`χ` is the bump `pStep rl ρ₁ ‖z‖ - pStep ρ₂ rh ‖z‖` of `smoothUnit_eqOn_annulus_of_periodicArgument`,
which vanishes for `‖z‖ ≤ ρ₀ < rl` — so `Ω` is `≡ 1` and `r ≡ 1` near `0`.  Consequently
`diskPlane Q` is **not injective** for that chart, and the engine's `hinj` clause cannot be obtained
from `diskPlane_injOn_interior_of_seamInjOn` for it: it has to be established *on the meet set* of the
design, not globally.  (For the **linear** plane chart, which is the reference plane of the
antisymmetry computation and the plane of the end faces, the injectivity *is* unconditional — the
statement below.)
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The square factor -/

/-- **`sqDisk ∘ foldBox` is injective on the unit box**: `sqDisk` is injective on the unit square
(`Work.Drive.sqDisk_injective`) and `foldBox` is injective on the unit square
(`Work.Drive.foldBox_injOn_unitBox`). -/
theorem sqDisk_foldBox_injOn_unitBox :
    Set.InjOn (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y))
      (Submission.Drive.unitBox 1) := fun y hy y' hy' h =>
  foldBox_injOn_unitBox hy hy'
    (sqDisk_injective _ _ (foldBox_mem_unitBox y) (foldBox_mem_unitBox y') h)

/-! ## 2. `diskPlane` is injective when the chart is -/

/-- **Injectivity of the disk presentation from injectivity of the chart on the closed disk.** -/
theorem diskPlane_injOn_unitBox_of_injOn_closedBall (Q : ℂ → CappingSpace)
    (hQ : Set.InjOn Q (Metric.closedBall (0 : ℂ) 1)) :
    Set.InjOn (diskPlane Q) (Submission.Drive.unitBox 1) := by
  intro y hy y' hy' h
  have hz : sqDisk (foldBox y) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
  have hz' : sqDisk (foldBox y') ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact norm_sqDisk_le_one _ (foldBox_mem_unitBox y')
  exact sqDisk_foldBox_injOn_unitBox hy hy' (hQ hz hz' h)

/-- **Injectivity of the disk presentation from injectivity of the chart modulo the seam.**  The seam
clause of a plane chart identifies the antipodal points of the *boundary circle* `‖z‖ = 1`, so `Q` is
never injective on the closed disk; on the **strictly interior** box points, whose `sqDisk`-images lie
in the *open* disk, no identification can occur, and `diskPlane Q` is injective. -/
theorem diskPlane_injOn_interior_of_seamInjOn (Q : ℂ → CappingSpace)
    (hQ : ∀ z z' : ℂ, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → Q z = Q z' → z = z' ∨ (‖z‖ = 1 ∧ z' = - z))
    {y y' : EuclideanSpace ℝ (Fin 2)}
    (hy : ∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) (hy' : ∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1)
    (h : diskPlane Q y = diskPlane Q y') : y = y' := by
  have hb : y ∈ Submission.Drive.unitBox 1 := fun i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hb' : y' ∈ Submission.Drive.unitBox 1 := fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩
  have hz : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
  have hz' : ‖sqDisk (foldBox y')‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y')
  rcases hQ _ _ hz hz' h with hzz | ⟨hze, _⟩
  · exact sqDisk_foldBox_injOn_unitBox hb hb' hzz
  · exact absurd hze (ne_of_lt (norm_sqDisk_foldBox_lt_one_of_mem_Ioo (hy 0) (hy 1)))

/-! ## 3. The linear plane chart: unconditional -/

/-- **The disk presentation of a linear plane chart is injective on the strictly interior box.**  This
is unconditional: `Work.Drive.linPlaneChart_eq_iff` computes the identifications of the linear plane
chart on the closed disk, and the interiority removes the antipodal boundary case. -/
theorem diskPlane_linPlaneChart_injOn_interior (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    {y y' : EuclideanSpace ℝ (Fin 2)}
    (hy : ∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) (hy' : ∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1)
    (h : diskPlane (linPlaneChart φ c hc) y = diskPlane (linPlaneChart φ c hc) y') : y = y' := by
  refine diskPlane_injOn_interior_of_seamInjOn (linPlaneChart φ c hc) (fun z z' hz hz' hzz => ?_)
    hy hy' h
  rcases (linPlaneChart_eq_iff φ c hc hz hz').mp hzz with h | ⟨h1, -, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

/-- **The disk presentation of a linear plane chart has no two *distinct points of the box* with the
same value, off the seam** — the form in which the transport consumes it. -/
theorem diskPlane_linPlaneChart_eq_imp (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    {y y' : EuclideanSpace ℝ (Fin 2)}
    (hy : ∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) (hy' : ∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1) :
    diskPlane (linPlaneChart φ c hc) y = diskPlane (linPlaneChart φ c hc) y' → y = y' :=
  diskPlane_linPlaneChart_injOn_interior φ c hc hy hy'

/-! ## 4. The `hinj` clause of the locality engine -/

/-- **The `hinj` clause of `Work.Drive.meetPt_ncard_eq_of_regular_manifold` for the design's pair**,
with its two halves separated: the *loop* half is the proved `Work.Drive.coreLoop_injective_mod_one`
(the core loop of a plane chart is a simple closed curve, `IsPlaneChart` + injective `γ`), and the
*chain* half is the injectivity of the clamped sweep on the parameter box, taken here as an explicit
hypothesis (for the honest chart of `exists_planeChart` it is *not* a consequence of `IsPlaneChart`:
see the file docstring). -/
theorem meetBox_hinj_of_chain_inj {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q₁ Q₂ : ℂ → CappingSpace} (hQ₁ : IsPlaneChart γ hγne Q₁) {c : ℝ} {ψ : ℝ → ℝ}
    (hchain : Set.InjOn (clampedSweep c ψ (diskPlane Q₂)) (Submission.Drive.unitBox 2))
    {p q : ℝ × EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ meetBox (coreLoop Q₁) (clampedSweep c ψ (diskPlane Q₂)))
    (hq : q ∈ meetBox (coreLoop Q₁) (clampedSweep c ψ (diskPlane Q₂)))
    (hL : coreLoop Q₁ p.1 = coreLoop Q₁ q.1)
    (hD : clampedSweep c ψ (diskPlane Q₂) p.2 = clampedSweep c ψ (diskPlane Q₂) q.2) :
    (∃ k : ℤ, q.1 = p.1 + (k : ℝ)) ∧ q.2 = p.2 :=
  ⟨coreLoop_injective_mod_one hγ hγne hQ₁ hL,
    (hchain (mem_meetBox.mp hp).2.1 (mem_meetBox.mp hq).2.1 hD).symm⟩

end

end Work.Drive
