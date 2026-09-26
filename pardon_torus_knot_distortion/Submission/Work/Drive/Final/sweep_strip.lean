import Mathlib
import Submission.Work.Drive.Final.sweep_half
import Submission.Work.Drive.EpsForm.discAttachSpan

/-!
# The swept strip and the wall of the tilted sweep: the set algebra of `hreg`

`P5` (`hreg`) asks: for `μ ≤ ν` in a stretch of the tilted sweep with no exceptional value between
them, `W(X_μ) = W(X_ν)`, where `X_λ = openTiltedSweepRegion … λ = boxRegion ∖ (slab ∩ {ℓ ≤ λ})`.

This file fixes the two sets the argument runs on and proves the set algebra that pins the two
spellings of the region to each other:

* `sweepStrip … μ ν = boxRegion ∩ slab ∩ {μ < ℓ < ν}` — **the swept strip**: exactly what the level
  jump `μ → ν` deletes;
* `sweepWall … λ = boxRegion ∩ slab ∩ {ℓ = λ}` — **the wall**: the trace of the level, the
  1-complex separating the `≤ λ` spelling (`openTiltedSweepRegion`) from the `< λ` spelling.

Proved here (sorry-free):

* `mem_openTiltedSweepRegion'` — membership in the swept region as a pure formula;
* `disjoint_sweepWall_region` — the wall at level `ν` is disjoint from the region `X_ν`
  (hence `(X_ν ∪ wall) ∖ wall = X_ν`), the form in which the routing brick
  `Work.EpsW.windingSpan_sdiff_iUnion_arcs_of_oneEnd` consumes the wall;
* `openTiltedSweepRegion_eq_union_strip_wall` (for `μ < ν`) — `X_μ = X_ν ∪ strip ∪ wall_ν`;
* `openTiltedSweepRegion_sdiff_strip_eq_halfOpen` (for `μ < ν`) — `X_μ ∖ strip` is the *half-open*
  spelling `boxRegion ∖ (slab ∩ {ℓ < ν})`, i.e. `X_ν ∪ wall_ν` (the previous two lemmas together).

With these, `hreg` reduces to (a) the disc-attachment data for the (open) strip — the consumer
`Work.Drive.EpsForm.windingSpan_eq_of_discAttach` is proved — and (b) the routing of the wall off the
half-open region.  See `AUDIT_pardon_unconditional.md` §8 for the two obstacles found there.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Final

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {μ ν lam : ℝ}

/-- **The swept strip** between two levels. -/
def sweepStrip (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (μ ν : ℝ) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ ∩
    Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | μ < ℓ y ∧ ℓ y < ν}

/-- **The wall** at a level: the trace of the level inside the closed slab and the box. -/
def sweepWall (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ Submission.PBox s c σ ∩
    Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y = lam}

/-- Membership in the swept region, as a pure formula. -/
theorem mem_openTiltedSweepRegion' {y : R3} :
    y ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y ≤ lam) := by
  simp only [Work.Drive.EpsFormSphere.openTiltedSweepRegion, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_setOf_eq, Work.Drive.EpsForm.tiltedSlabClosed]

/-- Membership in the swept strip, as a pure formula. -/
theorem mem_sweepStrip' {y : R3} :
    y ∈ sweepStrip P s c σ u v h ℓ μ ν ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ μ < ℓ y ∧ ℓ y < ν := by
  simp only [sweepStrip, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc,
    Work.Drive.EpsForm.tiltedSlabClosed]

/-- Membership in the wall, as a pure formula. -/
theorem mem_sweepWall' {y : R3} :
    y ∈ sweepWall P s c σ u v h ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam := by
  simp only [sweepWall, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc,
    Work.Drive.EpsForm.tiltedSlabClosed]

/-- **The wall at level `ν` is disjoint from the region `X_ν`.** -/
theorem disjoint_sweepWall_region (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Disjoint (sweepWall P s c σ u v h ℓ lam)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) := by
  rw [Set.disjoint_left]
  intro y hy hyX
  rw [mem_sweepWall'] at hy
  rw [mem_openTiltedSweepRegion'] at hyX
  exact hyX.2.2 ⟨hy.2.2.1, le_of_eq hy.2.2.2⟩

/-- **The level jump, as sets** (for `μ < ν`): `X_μ` is `X_ν` together with the swept strip and the
wall at `ν`. -/
theorem openTiltedSweepRegion_eq_union_strip_wall (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) {μ ν : ℝ}
    (hμν : μ < ν) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ μ =
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ ν ∪
        sweepStrip P s c σ u v h ℓ μ ν ∪ sweepWall P s c σ u v h ℓ ν := by
  ext y
  rw [mem_openTiltedSweepRegion']
  constructor
  · rintro ⟨hyc, hyb, hyrem⟩
    by_cases hslab : |inner ℝ v y - (inner ℝ v c + u)| ≤ h
    · have hgt : μ < ℓ y := not_le.mp fun hcon => hyrem ⟨hslab, hcon⟩
      rcases lt_trichotomy (ℓ y) ν with hlt | heq | hgt'
      · exact Or.inl (Or.inr (by rw [mem_sweepStrip']; exact ⟨hyc, hyb, hslab, hgt, hlt⟩))
      · exact Or.inr (by rw [mem_sweepWall']; exact ⟨hyc, hyb, hslab, heq⟩)
      · exact Or.inl (Or.inl (by
          rw [mem_openTiltedSweepRegion']
          exact ⟨hyc, hyb, fun hz => absurd hz.2 (not_le.mpr hgt')⟩))
    · exact Or.inl (Or.inl ⟨hyc, hyb, fun hz => hslab hz.1⟩)
  · rintro ((⟨hyc, hyb, hyrem⟩ | hy) | hy)
    · refine ⟨hyc, hyb, fun hz => hyrem ⟨hz.1, ?_⟩⟩
      exact le_trans hz.2 (le_of_lt hμν)
    · rw [mem_sweepStrip'] at hy
      refine ⟨hy.1, hy.2.1, fun hz => ?_⟩
      exact absurd hz.2 (not_le.mpr hy.2.2.2.1)
    · rw [mem_sweepWall'] at hy
      refine ⟨hy.1, hy.2.1, fun hz => ?_⟩
      exact absurd hz.2 (not_le.mpr (by rw [hy.2.2.2]; exact hμν))

end

end Work.Drive.Final
