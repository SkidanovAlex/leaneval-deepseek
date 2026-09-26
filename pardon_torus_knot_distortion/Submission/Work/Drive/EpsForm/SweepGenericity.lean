import Submission.Work.Drive.EpsFormSphere.Sideways
import Submission.Work.Smooth.Morse.Surface.isCompact_torus
import Submission.Work.BoxShrink.Pinch.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# P1 of the sideways slab sweep: the ambient setup and the two end levels

This module isolates **P1** of the lead's design for field 2 (`EpsFormSphere/Sideways.lean`, the
residual `SideSweepExists`): the *data* of the sweep at a counted configuration — a slab half-width
`h > 0`, a horizontal sweep functional `ℓ` (vanishing on the `σ 2` direction), the two end levels
`lam0 < lam1`, and the finite set `exc` of the critical values of `ℓ` on the surface-with-boundary
cut out by the slab — together with the general position of the sweep in the form P2 and P3 consume
it.

Contents (this file):

* `slabDomain` / `isClosed_slabDomain` / `isCompact_slabDomain` — the compact
  surface-with-boundary `F ∩ closure (slab)` on which `ℓ` is the height driving the sweep; its
  boundary is the trace of the two slab faces;
* `endSet` / `isCompact_endSet` and the three lemmas
  `sideRegion_eq_boxRegion_of_forall_lt`, `sideRegion_eq_sdiff_slab_of_forall_gt`,
  `exists_sweep_endpoints` (**proved**) — the two *end* levels of the sweep: below the `ℓ`-range of
  the box the swept region is the whole box region, above it the box region with the whole slab
  removed.  These are exactly the `start` and `finish` fields of
  `Work.Drive.EpsSphere.SideSweepData`, so P1 discharges two of its six fields for every
  configuration, with no genericity needed.

The remaining, *analytic* half of P1 — the existence of a horizontal functional `ℓ` and a width `h`
for which

  (i) away from a finite set `exc` the wall `{ℓ = lam}` meets the surface transversally inside the
      slab (what P2 needs to slide the wall, and P4 to see the trace as circles);
  (ii) the critical points of `ℓ` inside the slab are nondegenerate, their values lie in `exc`, and
      distinct critical points have distinct values (what P3 needs: a *single* nondegenerate handle
      at a time);
  (iii) the wall meets the two slab *faces* transversally away from `exc` (the sweep trace is a
      family of arcs with endpoints on the faces, and the endpoints must move injectively),

is stated next in the sibling vocabulary (`EpsFormSphere/Sideways.lean`, `SwingGeometry` /
`SwingCounting`), with those requirements *built into the hypothesis* rather than left implicit —
note the audit recorded there: `SwingGeometry` as formalised is degenerate (`ℓ = 0` satisfies it,
`swingGeometry_of_zero_functional`) and `SwingCounting` as formalised is false for non-generic data.
The proof is the genericity argument sketched in `EpsFormSphere/DESIGN.md`; the existing bricks are
`Work.Drive.N2.exists_isMorseDistinct` (a generic height is Morse with *distinct* critical values on
a compact surface), `Work.Smooth.Morse.aeRegularValues_of_contDiffTwo`,
`Work.Smooth.Morse.exists_isRegularValue_mem_Ioo` and
`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

/-- **The slab-domain**: the closed surface-with-boundary cut out of the carrier by the closed slab
`|y (σ 2) - (c (σ 2) + u)| ≤ h`.  It is the set on which the sweep functional `ℓ` drives the sweep:
its boundary is the trace of the two slab faces, and the wall `{ℓ = lam}` cuts off the piece that has
been removed from the region that is kept. -/
def slabDomain (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) :
    Set R3 :=
  P.carrier ∩ {y : R3 | |y (σ 2) - (c (σ 2) + u)| ≤ h}

theorem mem_slabDomain {P : Work.CoreTopology.ParamTorus} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u h : ℝ} {y : R3} :
    y ∈ slabDomain P c σ u h ↔ y ∈ P.carrier ∧ |y (σ 2) - (c (σ 2) + u)| ≤ h := Iff.rfl

theorem isClosed_slabDomain (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) :
    IsClosed (slabDomain (Work.Smooth.Morse.torus ψ) c σ u h) :=
  (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed.inter
    (isClosed_le (continuous_abs.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).sub continuous_const)) continuous_const)

/-- The slab-domain is compact: it is a closed subset of the compact surface. -/
theorem isCompact_slabDomain (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) :
    IsCompact (slabDomain (Work.Smooth.Morse.torus ψ) c σ u h) :=
  (Work.Smooth.Morse.Surface.isCompact_torus ψ).of_isClosed_subset
    (isClosed_slabDomain ψ c σ u h) inter_subset_left

/-- The slab-domain is contained in the carrier. -/
theorem slabDomain_subset_carrier (P : Work.CoreTopology.ParamTorus) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u h : ℝ) : slabDomain P c σ u h ⊆ P.carrier := inter_subset_left

/-! ## The two end levels of the sweep -/

/-- **The compact set whose `ℓ`-range controls the two ends of the sweep**: the carrier inside the
closure of the box and inside the closed slab.  It contains the trace of the open box with the slab,
which is all the sweep ever removes. -/
def endSet (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u h : ℝ) : Set R3 :=
  slabDomain P c σ u h ∩ closure (Submission.PBox s c σ)

theorem isCompact_endSet (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u h : ℝ) : IsCompact (endSet (Work.Smooth.Morse.torus ψ) s c σ u h) :=
  (isCompact_slabDomain ψ c σ u h).inter_right isClosed_closure

theorem endSet_subset_slabDomain (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u h : ℝ) : endSet P s c σ u h ⊆ slabDomain P c σ u h :=
  inter_subset_left

/-- **The swept region removes nothing when the level is below the `ℓ`-range of the box.** -/
theorem sideRegion_eq_boxRegion_of_forall_lt {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hlt : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, y ∈ Submission.PBox s c σ →
      y ∈ Work.Drive.EpsSphere.slabZ c σ u h → lam < ℓ y) :
    Work.Drive.EpsSphere.sideRegion (Work.Smooth.Morse.torus ψ) s c σ u h ℓ lam =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
  rw [Work.Drive.EpsSphere.sideRegion, Work.Drive.EpsSphere.wallRegion,
    Work.BoxShrink.Core.boxRegion]
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hcar, hP, -⟩
    exact ⟨hcar, hP⟩
  · rintro y ⟨hcar, hP⟩
    exact ⟨hcar, hP, fun hy => absurd (hlt y hcar hP hy.1) (not_lt.mpr hy.2.le)⟩

/-- **The swept region is the box region with the whole slab removed when the level is above the
`ℓ`-range of the box.** -/
theorem sideRegion_eq_sdiff_slab_of_forall_gt {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hgt : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, y ∈ Submission.PBox s c σ →
      y ∈ Work.Drive.EpsSphere.slabZ c σ u h → ℓ y < lam) :
    Work.Drive.EpsSphere.sideRegion (Work.Smooth.Morse.torus ψ) s c σ u h ℓ lam =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
        Work.Drive.EpsSphere.slabZ c σ u h := by
  rw [Work.Drive.EpsSphere.sideRegion, Work.Drive.EpsSphere.wallRegion,
    Work.BoxShrink.Core.boxRegion]
  ext y
  constructor
  · rintro ⟨hcar, hP, hnot⟩
    refine ⟨⟨hcar, hP⟩, ?_⟩
    intro hslab
    exact hnot ⟨hslab, hgt y hcar hP hslab⟩
  · rintro ⟨⟨hcar, hP⟩, hslab⟩
    exact ⟨hcar, hP, fun hy => hslab hy.1⟩

/-- **The two end levels of the sideways sweep** (the `start` and `finish` fields of
`Work.Drive.EpsSphere.SideSweepData`): there are levels `lam0 < lam1` at which the swept region is,
respectively, the whole box region and the box region with the whole slab removed. -/
theorem exists_sweep_endpoints (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u h : ℝ) (ℓ : R3 →L[ℝ] ℝ) :
    ∃ lam0 lam1 : ℝ, lam0 < lam1 ∧
      Work.Drive.EpsSphere.sideRegion (Work.Smooth.Morse.torus ψ) s c σ u h ℓ lam0 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ ∧
      Work.Drive.EpsSphere.sideRegion (Work.Smooth.Morse.torus ψ) s c σ u h ℓ lam1 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
          Work.Drive.EpsSphere.slabZ c σ u h := by
  classical
  have hmem : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, y ∈ Submission.PBox s c σ →
      y ∈ Work.Drive.EpsSphere.slabZ c σ u h →
      y ∈ endSet (Work.Smooth.Morse.torus ψ) s c σ u h := by
    intro y hcar hP hslab
    have hle : |y (σ 2) - (c (σ 2) + u)| ≤ h := le_of_lt hslab
    exact ⟨⟨hcar, hle⟩, subset_closure hP⟩
  by_cases hne : (endSet (Work.Smooth.Morse.torus ψ) s c σ u h).Nonempty
  · obtain ⟨x₀, hx₀, hmin₀⟩ :=
      (isCompact_endSet ψ s c σ u h).exists_isMinOn hne ℓ.continuous.continuousOn
    obtain ⟨x₁, hx₁, hmax₁⟩ :=
      (isCompact_endSet ψ s c σ u h).exists_isMaxOn hne ℓ.continuous.continuousOn
    have hmin : ∀ y ∈ endSet (Work.Smooth.Morse.torus ψ) s c σ u h, ℓ x₀ ≤ ℓ y :=
      fun y hy => hmin₀ hy
    have hmax : ∀ y ∈ endSet (Work.Smooth.Morse.torus ψ) s c σ u h, ℓ y ≤ ℓ x₁ :=
      fun y hy => hmax₁ hy
    exact ⟨ℓ x₀ - 1, ℓ x₁ + 1, by linarith [hmin x₁ hx₁],
      sideRegion_eq_boxRegion_of_forall_lt
        (fun y hcar hP hslab => by linarith [hmin y (hmem y hcar hP hslab)]),
      sideRegion_eq_sdiff_slab_of_forall_gt
        (fun y hcar hP hslab => by linarith [hmax y (hmem y hcar hP hslab)])⟩
  · have hzero : Work.Drive.EpsSphere.slabZ c σ u h ∩ Submission.PBox s c σ ∩
        (Work.Smooth.Morse.torus ψ).carrier = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨hslab, hbox⟩, hcar⟩
      exact hne ⟨y, hmem y hcar hbox hslab⟩
    refine ⟨0, 1, one_pos, ?_, ?_⟩
    · refine sideRegion_eq_boxRegion_of_forall_lt fun y hcar hP hslab => ?_
      exact absurd (show y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∩ Submission.PBox s c σ ∩
          (Work.Smooth.Morse.torus ψ).carrier from ⟨⟨hslab, hP⟩, hcar⟩)
        (by rw [hzero]; exact Set.notMem_empty y)
    · refine sideRegion_eq_sdiff_slab_of_forall_gt fun y hcar hP hslab => ?_
      exact absurd (show y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∩ Submission.PBox s c σ ∩
          (Work.Smooth.Morse.torus ψ).carrier from ⟨⟨hslab, hP⟩, hcar⟩)
        (by rw [hzero]; exact Set.notMem_empty y)

end

end Work.Drive.EpsForm

namespace Work.Drive.EpsForm

noncomputable section

open Work.Drive.EpsSphere

/-- **`SideSweepData` with the two end fields discharged.**  The sibling design
(`EpsFormSphere/Sideways.lean`) records the sweep through the four ingredients P1–P4; the two *end*
fields of the record (`start`, `finish`) are exactly the conclusion of `exists_sweep_endpoints`, so
only the genericity (the finite critical set and the regular levels), P2 (`regular_span`), P3
(`jump`) and P4 (`dichotomy`) remain as input.

This constructor is the P1 part of the residual `SideSweepExists`: it shows that two of the six
fields of `SideSweepData` are *free*, for every configuration. -/
def sideSweepData_of_regular_span_jump_dichotomy {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {ψ : Submission.Diffeo}
    (h : ℝ) (hpos : 0 < h) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (hlt : lam0 < lam1)
    (exc : Finset ℝ) (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hstart : sideRegion P s c σ u h ℓ lam0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hfinish : sideRegion P s c σ u h ℓ lam1 =
      Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u h)
    (hregular : ∀ lam lam' : ℝ, lam0 ≤ lam → lam ≤ lam' → lam' ≤ lam1 →
      (∀ t ∈ exc, t < lam ∨ lam' < t) →
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) =
        Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam'))
    (hjump : ∀ lam ∈ exc, ∀ mu nu : ℝ, lam0 ≤ mu → mu < lam → lam < nu → nu ≤ lam1 →
      (∀ t ∈ exc, t < mu ∨ t = lam ∨ nu < t) →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) + 1)
    (hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊤) :
    Nonempty (SideSweepData P s c σ u) :=
  ⟨⟨h, hpos, ℓ, lam0, lam1, hlt, exc, hexc, hstart, hfinish, hregular, hjump, hdich⟩⟩

end


/-! ## P1, the analytic half: the genericity of the sweep

The two end levels are free (above).  What remains is the existence of a *horizontal* functional `ℓ`
and a slab width `h` for which the sweep is in general position: away from a finite set `exc` the wall
`{ℓ = lam}` cuts the surface transversally, and at the critical points inside the slab `ℓ` is Morse
with distinct critical values.  The statement below is the form P2 and P3 consume; its proof is the
genericity argument (Sard for the Gauss map plus the one-dimensional argument on the two face-traces,
and Sard for the slab width).

`pullback ψ ℓ` is the height `y ↦ ℓ y` read in the parameter plane, and
`Work.BoxShrink.shiftVσ σ 1` is the unit vector in the `σ 2` direction, so
`ℓ (shiftVσ σ 1) = 0` says that `ℓ` is *horizontal* (constant along the direction across the slab) —
the condition that makes the wall move sideways through the slab rather than along it. -/

noncomputable section

/-- **The height of the sweep functional in the parameter plane.** -/
def sweepHeight (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) : ℝ × ℝ → ℝ :=
  Work.Smooth.Morse.pullback ψ (fun y => ℓ y)

/-- **The genericity predicate of the sweep**: a slab half-width `h > 0`, a horizontal functional
`ℓ` and a finite set `exc` of levels such that

* (regular levels) away from `exc`, at every surface point of the box inside the slab, the wall
  `{ℓ = ·}` meets the surface transversally;
* (Morse) at every critical point of the height inside the box and the slab, the height is
  nondegenerate (its Hessian in the parameter plane is injective) and the critical value lies in
  `exc`.

This is the analytic content of P1.  It is deliberately stated at a *single* configuration (the
`SweepGenericity` is then existentially quantified over the data in the residual). -/
def SweepGenericity (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Prop :=
  ∃ (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ),
    0 < h ∧ ℓ (Work.BoxShrink.shiftVσ σ 1) = 0 ∧
    (∀ lam ∉ exc, ∀ p : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - (c (σ 2) + u)| ≤ h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam → fderiv ℝ (sweepHeight ψ ℓ) p ≠ 0) ∧
    (∀ p : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - (c (σ 2) + u)| ≤ h →
      fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (sweepHeight ψ ℓ)) p) ∧
        ℓ (Work.BoxShrink.Pinch.par ψ p) ∈ exc)

end


/-! ## The general form of the two end levels, and the tilted slab

The two end levels of a sweep only need the *removed set* `W` to be bounded and closed (so that the
`ℓ`-range of `closure (PBox) ∩ W ∩ carrier` is compact) and the sweeping functional `ℓ`; the slab of
the design is one instance.  This is the form in which the endpoint statement survives the correction
necessitated by `NOTES_P1_horizontality_OBSTRUCTION.md`: the slab may be *tilted* (its normal a
generic unit vector `v`, not the fixed `σ 2` direction), which is what makes the genericity of P1
attainable, while the two end levels remain free. -/

noncomputable section

/-- **The swept region of a general sideways sweep**: the box region with the part of the removed set
`W` behind the level `lam` of `ℓ` taken out.  For `W = slabZ c σ u h` this is
`Work.Drive.EpsSphere.sideRegion`. -/
def sweepRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (W : Set R3) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ (Submission.PBox s c σ \ (W ∩ {y : R3 | ℓ y < lam}))

theorem mem_sweepRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {W : Set R3} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ sweepRegion P s c σ W ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ (y ∈ W → lam ≤ ℓ y) := by
  simp only [sweepRegion, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_and, not_lt]

/-- **The two end levels of a sideways sweep, for a closed removed set** (in the application: a
slab, possibly tilted).  Below the `ℓ`-range of the box the sweep removes nothing; above it, the
whole removed set is taken out. -/
theorem exists_sweepRegion_endpoints (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {W : Set R3} (hW : IsClosed W) (ℓ : R3 →L[ℝ] ℝ) :
    ∃ lam0 lam1 : ℝ, lam0 < lam1 ∧
      sweepRegion (Work.Smooth.Morse.torus ψ) s c σ W ℓ lam0 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ ∧
      sweepRegion (Work.Smooth.Morse.torus ψ) s c σ W ℓ lam1 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \ W := by
  classical
  have hK : IsCompact ((Work.Smooth.Morse.torus ψ).carrier ∩
      closure (Submission.PBox s c σ) ∩ W) :=
    (Work.Smooth.Morse.Surface.isCompact_torus ψ).of_isClosed_subset
      (((Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed.inter isClosed_closure).inter hW)
      (by intro y hy; exact hy.1.1)
  have hmem : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, y ∈ Submission.PBox s c σ → y ∈ W →
      y ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ closure (Submission.PBox s c σ) ∩ W :=
    fun y hcar hP hWy => ⟨⟨hcar, subset_closure hP⟩, hWy⟩
  by_cases hne : ((Work.Smooth.Morse.torus ψ).carrier ∩ closure (Submission.PBox s c σ) ∩
      W).Nonempty
  · obtain ⟨x₀, hx₀, hmin₀⟩ := hK.exists_isMinOn hne ℓ.continuous.continuousOn
    obtain ⟨x₁, hx₁, hmax₁⟩ := hK.exists_isMaxOn hne ℓ.continuous.continuousOn
    have hmin : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ closure (Submission.PBox s c σ) ∩ W,
        ℓ x₀ ≤ ℓ y := fun y hy => hmin₀ hy
    have hmax : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ closure (Submission.PBox s c σ) ∩ W,
        ℓ y ≤ ℓ x₁ := fun y hy => hmax₁ hy
    refine ⟨ℓ x₀ - 1, ℓ x₁ + 1, by linarith [hmin x₁ hx₁], ?_, ?_⟩
    · ext y
      rw [mem_sweepRegion, Work.BoxShrink.Core.boxRegion]
      constructor
      · rintro ⟨hcar, hP, -⟩
        exact ⟨hcar, hP⟩
      · rintro ⟨hcar, hP⟩
        refine ⟨hcar, hP, ?_⟩
        intro hyW
        exact le_of_lt (by linarith [hmin y (hmem y hcar hP hyW)])
    · ext y
      rw [mem_sweepRegion, Work.BoxShrink.Core.boxRegion, Set.mem_sdiff]
      constructor
      · rintro ⟨hcar, hP, hnot⟩
        exact ⟨⟨hcar, hP⟩, fun hyW => absurd (le_trans (hmax y (hmem y hcar hP hyW))
          (le_refl (ℓ x₁))) (by linarith [hnot hyW])⟩
      · rintro ⟨⟨hcar, hP⟩, hyW⟩
        exact ⟨hcar, hP, fun h => absurd h hyW⟩
  · have hempty : W ∩ Submission.PBox s c σ ∩ (Work.Smooth.Morse.torus ψ).carrier = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨hyW, hP⟩, hcar⟩
      exact hne ⟨y, hmem y hcar hP hyW⟩
    refine ⟨0, 1, one_pos, ?_, ?_⟩
    · ext y
      rw [mem_sweepRegion, Work.BoxShrink.Core.boxRegion]
      constructor
      · rintro ⟨hcar, hP, -⟩
        exact ⟨hcar, hP⟩
      · rintro ⟨hcar, hP⟩
        refine ⟨hcar, hP, ?_⟩
        intro hyW
        exact absurd (show y ∈ W ∩ Submission.PBox s c σ ∩
            (Work.Smooth.Morse.torus ψ).carrier from ⟨⟨hyW, hP⟩, hcar⟩)
          (by rw [hempty]; exact Set.notMem_empty y)
    · ext y
      rw [mem_sweepRegion, Work.BoxShrink.Core.boxRegion, Set.mem_sdiff]
      constructor
      · rintro ⟨hcar, hP, hnot⟩
        exact ⟨⟨hcar, hP⟩, fun hyW => absurd (show y ∈ W ∩ Submission.PBox s c σ ∩
            (Work.Smooth.Morse.torus ψ).carrier from ⟨⟨hyW, hP⟩, hcar⟩)
          (by rw [hempty]; exact Set.notMem_empty y)⟩
      · rintro ⟨⟨hcar, hP⟩, hyW⟩
        exact ⟨hcar, hP, fun h => absurd h hyW⟩

/-! ## The tilted slab

The obstruction recorded in `EpsForm/NOTES_P1_horizontality_OBSTRUCTION.md` is that the *fixed* slab
(orthogonal to `e_{σ 2}`) leaves no generic direction for the wall: a surface with an exactly
cylindrical band whose generators are parallel to `e_{σ 2}` makes every horizontal functional
degenerate.  The repair is to let the slab *tilt*: choose a unit normal `v` close to `e_{σ 2}` and a
wall direction `ℓ` with `ℓ v = 0`; genericity in `v` is what removes the obstruction.  The two end
levels are unaffected, the removed set still being a slab. -/

/-- **The tilted slab**: the band of half-width `h` around the plane `⟪v, ·⟫ = a`. -/
def tiltedSlab (a : ℝ) (v : R3) (h : ℝ) : Set R3 :=
  {y : R3 | |inner ℝ v y - a| < h}

/-- The *closed* tilted slab, whose trace in the box is compact. -/
def tiltedSlabClosed (a : ℝ) (v : R3) (h : ℝ) : Set R3 :=
  {y : R3 | |inner ℝ v y - a| ≤ h}

theorem tiltedSlab_subset_tiltedSlabClosed (a : ℝ) (v : R3) (h : ℝ) :
    tiltedSlab a v h ⊆ tiltedSlabClosed a v h :=
  fun y hy => le_of_lt (show |inner ℝ v y - a| < h from hy)

theorem isClosed_tiltedSlabClosed (a : ℝ) (v : R3) (h : ℝ) : IsClosed (tiltedSlabClosed a v h) :=
  isClosed_le (continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const))
    continuous_const

/-- **The two end levels of the tilted sweep** (closed slab form): as for the fixed slab, the `start`
and `finish` fields of the sweep data are free. -/
theorem exists_tiltedSweepRegion_endpoints (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (a : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) :
    ∃ lam0 lam1 : ℝ, lam0 < lam1 ∧
      sweepRegion (Work.Smooth.Morse.torus ψ) s c σ (tiltedSlabClosed a v h) ℓ lam0 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ ∧
      sweepRegion (Work.Smooth.Morse.torus ψ) s c σ (tiltedSlabClosed a v h) ℓ lam1 =
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
          tiltedSlabClosed a v h :=
  exists_sweepRegion_endpoints ψ s c σ (isClosed_tiltedSlabClosed a v h) ℓ

end

end Work.Drive.EpsForm
