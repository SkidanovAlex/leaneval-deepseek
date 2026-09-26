import Mathlib
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.Final.dentOut_sweep_subset

/-!
# The two sides of the wall of a level of the tilted sweep

At a level `lam` of the tilted sweep the *wall* is the surface's part of the frontier of the level's
removed set, `P.carrier ∩ frontier (tiltedLevelRemoved … lam)`.  The *region* is
`Work.Drive.Final.sweep … lam` (the open sweep region), which lies in the interior of the removed set
and is therefore disjoint from the wall.  The present module introduces the "far side"

    wallSide … lam = P.carrier \ (sweep … lam ∪ wall … lam),

i.e. the surface points which are neither in the region nor on the wall.  By construction the
complement of the wall in the surface is the disjoint union `sweep … lam ∪ wallSide … lam`, which is
the hypothesis `hcover` of the abstract wall dichotomy
(`Work.Drive.EpsForm.Wall.existsUnique_top_of_two_pieces`).

The point of this spelling (rather than the more naive `P.carrier ∩ (closure (sweep … lam))ᶜ`) is that
the cover clause then holds *by construction*, with no hypothesis on the trace; the price is that the
monotonicity of the far side in the level is a geometric statement about the removed set, proved in
`Submission/Work/Drive/Mono/wallSide.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono

noncomputable section

/-- **The wall** at a level: the part of the surface lying in the frontier of the level's removed
set (the "trace" of the level). -/
def wall (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)

/-- **The far side of the wall** at a level: the surface points which are neither in the level's
region nor on the wall. -/
def wallSide (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier \ (Work.Drive.Final.sweep P s c σ u v h ℓ lam ∪ wall P s c σ u v h ℓ lam)

/-- **The region lies in the interior of the removed set.**  A point of the sweep region is in the
open box and is either strictly outside the closed slab or strictly above the level, so a whole
neighbourhood of it is in the removed set. -/
theorem sweep_subset_interior_removed (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Work.Drive.Final.sweep P s c σ u v h ℓ lam ⊆
      interior (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  intro y hy
  rw [Work.Drive.Mono.mem_openTiltedSweepRegion_iff] at hy
  obtain ⟨hyc, hyP, hyrem⟩ := hy
  have hbox : IsOpen (Submission.PBox s c σ) := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  rcases not_and_or.mp hyrem with hslab | hlt
  · -- strictly outside the closed slab
    have hslab' : h < |inner ℝ v y - (inner ℝ v c + u)| := not_le.mp hslab
    refine mem_interior_iff_mem_nhds.mpr ?_
    have hopen : IsOpen {x : R3 | h < |inner ℝ v x - (inner ℝ v c + u)|} :=
      isOpen_lt continuous_const (continuous_abs.comp (by fun_prop))
    have hsub : {x : R3 | h < |inner ℝ v x - (inner ℝ v c + u)|} ∩ Submission.PBox s c σ ⊆
        tiltedLevelRemoved s c σ u v h ℓ lam := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨hx2, fun hc => ?_⟩
      have h1 : |inner ℝ v x - (inner ℝ v c + u)| ≤ h := hc.1
      exact (not_le.mpr hx1) h1
    exact Filter.mem_of_superset ((hopen.inter hbox).mem_nhds ⟨hslab', hyP⟩) hsub
  · -- strictly above the level
    have hlt' : lam < ℓ y := not_le.mp hlt
    refine mem_interior_iff_mem_nhds.mpr ?_
    have hopen : IsOpen {x : R3 | lam < ℓ x} := isOpen_lt continuous_const ℓ.continuous
    have hsub : {x : R3 | lam < ℓ x} ∩ Submission.PBox s c σ ⊆
        tiltedLevelRemoved s c σ u v h ℓ lam := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨hx2, fun hc => ?_⟩
      have h1 : ℓ x < lam := hc.2
      exact (not_lt.mpr (show lam ≤ ℓ x from le_of_lt hx1)) h1
    exact Filter.mem_of_superset ((hopen.inter hbox).mem_nhds ⟨hlt', hyP⟩) hsub

/-- **The region is disjoint from the wall** (the region lies in the interior of the removed set, the
wall in its frontier). -/
theorem disjoint_sweep_wall (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    Disjoint (Work.Drive.Final.sweep P s c σ u v h ℓ lam) (wall P s c σ u v h ℓ lam) := by
  rw [Set.disjoint_left]
  intro y hys hyw
  have hint : y ∈ interior (tiltedLevelRemoved s c σ u v h ℓ lam) :=
    sweep_subset_interior_removed P s c σ u v h ℓ lam hys
  exact ((mem_interior_iff_notMem_frontier (interior_subset hint)).mp hint) hyw.2

/-- **The cover clause for the wall dichotomy, by construction**: the complement of the wall in the
surface is the disjoint union of the region and the far side. -/
theorem carrier_sdiff_wall_eq_union (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    P.carrier \ wall P s c σ u v h ℓ lam =
      Work.Drive.Final.sweep P s c σ u v h ℓ lam ∪ wallSide P s c σ u v h ℓ lam := by
  have hsub : Work.Drive.Final.sweep P s c σ u v h ℓ lam ⊆ P.carrier := by
    intro y hy
    exact (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mp hy).1
  have hwall : wall P s c σ u v h ℓ lam ⊆ P.carrier := Set.inter_subset_left
  ext y
  constructor
  · rintro ⟨hyc, hyw⟩
    by_cases hys : y ∈ Work.Drive.Final.sweep P s c σ u v h ℓ lam
    · exact Or.inl hys
    · exact Or.inr ⟨hyc, fun hcon => hcon.elim hys hyw⟩
  · rintro (hys | hys)
    · exact ⟨hsub hys, fun hcon => (Set.disjoint_left.mp
        (disjoint_sweep_wall P s c σ u v h ℓ lam)) hys hcon⟩
    · exact ⟨hys.1, fun hcon => hys.2 (Or.inr hcon)⟩

/-- Membership in the far side, unwound. -/
theorem mem_wallSide_iff {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ wallSide P s c σ u v h ℓ lam ↔
      y ∈ P.carrier ∧ y ∉ Work.Drive.Final.sweep P s c σ u v h ℓ lam ∧
        y ∉ wall P s c σ u v h ℓ lam := by
  constructor
  · rintro ⟨hyc, hy⟩
    exact ⟨hyc, fun hcon => hy (Or.inl hcon), fun hcon => hy (Or.inr hcon)⟩
  · rintro ⟨hyc, h1, h2⟩
    exact ⟨hyc, fun hcon => Or.elim hcon h1 h2⟩


/-- **The far side is monotone in the level.**  As the level rises the region shrinks (`sweep_anti`)
and the wall moves; a point of the far side at `ν` is a point of the far side at every `ν' ≥ ν`.  The
only geometric input is that the region lies in the *interior* of the removed set
(`sweep_subset_interior_removed`), which converts "not in the interior of the removed set at `ν`"
into membership of the wall at `ν`. -/
theorem wallSide_mono (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ)
    (hv : v ≠ 0) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0) {ν ν' : ℝ}
    (hνν' : ν ≤ ν') :
    wallSide P s c σ u v h ℓ ν ⊆ wallSide P s c σ u v h ℓ ν' := by
  have hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 :=
    Work.Drive.Final.exists_descend_of_inner_eq_zero hv hℓne hℓv
  intro y hy
  obtain ⟨hyc, hys, hyw⟩ := mem_wallSide_iff.mp hy
  refine mem_wallSide_iff.mpr ⟨hyc, ?_, ?_⟩
  · intro hcon
    exact hys (Work.Drive.Final.sweep_anti hνν' hcon)
  · intro hcon
    obtain ⟨-, hyfr⟩ := hcon
    have hsub : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ ν' ⊆
        Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ ν := by
      intro z hz
      obtain ⟨hzP, hzr⟩ := hz
      exact ⟨hzP, fun hc => hzr ⟨hc.1, lt_of_lt_of_le hc.2 hνν'⟩⟩
    have hcl : y ∈ closure (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ ν) :=
      closure_mono hsub hyfr.1
    have hnotint : y ∉ interior (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ ν) :=
      fun hint =>
        hys ⟨hyc, Work.Drive.Final.interior_tiltedLevelRemoved_subset_sweepRegion
          (s := s) (u := u) (c := c) (v := v) (σ := σ) (h := h) (lam := ν) (ℓ := ℓ) hdesc hint⟩
    exact hyw ⟨hyc, ⟨hcl, hnotint⟩⟩

end

end Work.Drive.Mono

