import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# The two open discs of a `SchoenfliesData` are preconnected

Let `D : SchoenfliesData A ι c` be the conclusion of Jordan–Schoenflies on a sphere `A ⊆ ℝ³`
for a finite family of curves `c i`.  For each `i` the *open* parts of the two discs bounded by
`c i`,

`U i  = {x ∈ A | ∃ z : 𝔻, ‖z‖ < 1 ∧ D.e i z = x}`,
`U' i = {x ∈ A | ∃ z : 𝔻, ‖z‖ < 1 ∧ D.e' i z = x}`,

are **preconnected**: each is the image of the (connected, indeed convex) open unit disc under the
continuous embedding `z ↦ D.e i z` (resp. `z ↦ D.e' i z`), and a continuous image of a preconnected
space is preconnected.

Nothing about Jordan curves is needed for this: only the continuity of `D.e i` (a continuous map
`𝔻 → ℝ³`) and the clause `D.mem i` (its values lie in `A`).
-/

namespace Work.Topology.Classical

/-- **The open unit disc inside the model disc `𝔻` is preconnected.**
`{z : 𝔻 | ‖z‖ < 1}` is the image of the convex (hence preconnected) open unit ball
`Metric.ball 0 1 ⊆ ℂ` under the inclusion `Metric.ball 0 1 → 𝔻`, and `Subtype.val` on `𝔻` is an
inducing map, so preconnectedness transfers. -/
theorem isPreconnected_openUnitDisc :
    IsPreconnected ({z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1} : Set Work.InnermostDisk.Disc) := by
  rw [← (Topology.IsInducing.subtypeVal (t := Metric.closedBall (0:ℂ) 1)).isPreconnected_image]
  have himg : (Subtype.val '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1}) =
      Metric.ball (0:ℂ) 1 := by
    ext w
    simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      exact ⟨⟨w, by simp only [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hw⟩,
        hw, rfl⟩
  rw [himg]
  exact Metric.isPreconnected_ball

/-- **An open disc of a `SchoenfliesData`, as a subset of `A`, is preconnected.**

If `f : 𝔻 → A` is continuous then `{x : A | ∃ z : 𝔻, ‖z‖ < 1 ∧ f z = x}` is the image of the
preconnected open unit disc under `f`, hence preconnected. -/
theorem isPreconnected_image_openUnitDisc {A : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (f : Work.InnermostDisk.Disc → A) (hf : Continuous f) :
    IsPreconnected {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ f z = x} := by
  have himg : {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ f z = x} =
      f '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1} := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, hzx⟩
  rw [himg]
  exact isPreconnected_openUnitDisc.image f hf.continuousOn

theorem isPreconnected_openDiscs_of_schoenfliesData
    {A : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {ι : Type} [Fintype ι]
    {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Topology.Classical.SchoenfliesData A ι c) (i : ι) :
    IsPreconnected {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} ∧
      IsPreconnected {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ D.e' i z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} := by
  constructor
  · have hD : {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
        D.e i z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} =
        {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
          (fun z : Work.InnermostDisk.Disc => (⟨D.e i z, D.mem i z⟩ : A)) z = x} := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, Subtype.ext hzx⟩
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, congrArg Subtype.val hzx⟩
    rw [hD]
    exact isPreconnected_image_openUnitDisc _
      (Continuous.subtype_mk (D.e i).continuous (D.mem i))
  · have hD : {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
        D.e' i z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} =
        {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
          (fun z : Work.InnermostDisk.Disc => (⟨D.e' i z, D.mem' i z⟩ : A)) z = x} := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, Subtype.ext hzx⟩
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, congrArg Subtype.val hzx⟩
    rw [hD]
    exact isPreconnected_image_openUnitDisc _
      (Continuous.subtype_mk (D.e' i).continuous (D.mem' i))

end Work.Topology.Classical
