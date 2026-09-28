import Submission.Work.ThreeConnected.Trace

set_option synthInstance.maxHeartbeats 400000

/-!
# The open cover of the trace used for excision

This module sets up the point-set data for the computation of the homology of the **concrete trace**
`W = Trace φ hφ = M × ℝ ∪_φ (D^{k+1} × D^{l+1})` of `Submission/Work/ThreeConnected/Trace.lean`
relative to its two ends, following the classical computation of the effect of a surgery
(excision + the disc pair).

## The cover

Write `p : Disk k × Disk l ↦ ‖p.1‖` for the radius of the `D^{k+1}`-coordinate of a point of the
handle.  The trace is covered by the two pieces

* `Work.ThreeConnected.traceV` — the image of the part `{‖a‖ < 1}` of the handle; this is **open**
  (the identification only involves the points with `‖a‖ = 1`), and it is homeomorphic to the convex
  set `{‖a‖ < 1} × D^{l+1}`, hence contractible;
* `Work.ThreeConnected.traceU` — the complement of `Work.ThreeConnected.traceSmall`, the image of the
  part `{‖a‖ ≤ 1/2}` of the handle; that piece is closed (again the identification only involves
  `‖a‖ = 1`), so `traceU` is open.

Their intersection is the image of the collar `{1/2 < ‖a‖ < 1} × D^{l+1}`, a product annulus which
is homotopy equivalent to `S^k × D^{l+1}`; and the `M`-end `Work.ThreeConnected.traceA` is contained
in `traceU` and is a deformation retract of it.  These are exactly the hypotheses with which the
relative Mayer–Vietoris sequence (`Work.Cohomology.relMV_exact₁/₂/₃`) computes the relative homology
of `(W, M-end)` from the collar, and hence proves the excision statements `excA` of
`Work.ThreeConnected.TraceExcision`.

## Status

The statements of the point-set facts are listed here and proved in the companion modules
`Submission/Work/ThreeConnected/Excision/`; the ones that are already proved are imported at the end
of this file.  See `README.md` §3.2 for the precise state.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold Topology ContDiff
open Function
open Classical

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {k l : ℕ} {M : Type} [TopologicalSpace M]

/-- The radius of the `D^{k+1}`-coordinate of a point of the handle `D^{k+1} × D^{l+1}`. -/
def tubeRad (k l : ℕ) (u : Work.Surgery.Disk k × Work.Surgery.Disk l) : ℝ :=
  ‖(u.1 : EuclideanSpace ℝ (Fin (k + 1)))‖

@[simp] theorem tubeRad_apply (u : Work.Surgery.Disk k × Work.Surgery.Disk l) :
    tubeRad k l u = ‖(u.1 : EuclideanSpace ℝ (Fin (k + 1)))‖ := rfl

theorem tubeRad_nonneg (u : Work.Surgery.Disk k × Work.Surgery.Disk l) : 0 ≤ tubeRad k l u :=
  norm_nonneg _

theorem tubeRad_le_one (u : Work.Surgery.Disk k × Work.Surgery.Disk l) : tubeRad k l u ≤ 1 := by
  have h := u.1.2
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

theorem tubeRad_eq_one_iff (u : Work.Surgery.Disk k × Work.Surgery.Disk l) :
    tubeRad k l u = 1 ↔ u.1 ∈ Work.Surgery.diskSphere k :=
  (Work.Surgery.mem_diskSphere_iff k u.1).symm

/-- The part `{‖a‖ < 1}` of the handle, where `a` is the `D^{k+1}`-coordinate. -/
def traceOpenTube (k l : ℕ) : Set (Work.Surgery.Disk k × Work.Surgery.Disk l) :=
  {u | tubeRad k l u < 1}

/-- The part `{‖a‖ ≤ 1/2}` of the handle. -/
def traceSmallTube (k l : ℕ) : Set (Work.Surgery.Disk k × Work.Surgery.Disk l) :=
  {u | tubeRad k l u ≤ 1/2}

/-- The collar `{1/2 < ‖a‖ < 1}` of the handle. -/
def traceCollar (k l : ℕ) : Set (Work.Surgery.Disk k × Work.Surgery.Disk l) :=
  {u | 1/2 < tubeRad k l u ∧ tubeRad k l u < 1}

@[simp] theorem mem_traceOpenTube {u : Work.Surgery.Disk k × Work.Surgery.Disk l} :
    u ∈ traceOpenTube k l ↔ tubeRad k l u < 1 := Iff.rfl

@[simp] theorem mem_traceSmallTube {u : Work.Surgery.Disk k × Work.Surgery.Disk l} :
    u ∈ traceSmallTube k l ↔ tubeRad k l u ≤ 1/2 := Iff.rfl

@[simp] theorem mem_traceCollar {u : Work.Surgery.Disk k × Work.Surgery.Disk l} :
    u ∈ traceCollar k l ↔ 1/2 < tubeRad k l u ∧ tubeRad k l u < 1 := Iff.rfl

theorem traceCollar_eq (k l : ℕ) :
    traceCollar k l = traceOpenTube k l \ traceSmallTube k l := by
  ext u
  simp only [traceCollar, traceOpenTube, traceSmallTube, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun h => absurd h (by linarith)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨not_le.mp h3, h2⟩

/-- **The open piece `V` of the cover**: the image in the trace of the part of the handle with
`‖a‖ < 1`. -/
def traceV (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Set (Trace φ hφ) :=
  traceQ φ hφ '' (Sum.inr '' traceOpenTube k l)

/-- **The small closed piece**: the image in the trace of the part of the handle with `‖a‖ ≤ 1/2`. -/
def traceSmall (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Set (Trace φ hφ) :=
  traceQ φ hφ '' (Sum.inr '' traceSmallTube k l)

/-- **The second open piece `U` of the cover**: the complement of the small closed piece. -/
def traceU (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Set (Trace φ hφ) :=
  (traceSmall φ hφ)ᶜ

/-- **The `M`-end of the trace**: the image of the level-`0` slice. -/
def traceA (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Set (Trace φ hφ) :=
  Set.range (traceιM φ hφ)

/-- **The collar of the cover**, as a subset of the trace: the image of `{1/2 < ‖a‖ < 1} × D^{l+1}`;
this is the intersection of the two pieces `traceU` and `traceV` of the cover. -/
def traceC (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M) (hφ : Function.Injective φ) :
    Set (Trace φ hφ) :=
  traceQ φ hφ '' (Sum.inr '' traceCollar k l)

/-- The quotient map of the trace is continuous. -/
theorem continuous_traceQ (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) : Continuous (traceQ φ hφ) := by
  change Continuous (Quotient.mk'' (s₁ := Setoid.ker (traceNF φ hφ)))
  exact continuous_quotient_mk'

@[simp] theorem mem_traceU {φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M}
    {hφ : Function.Injective φ} {x : Trace φ hφ} :
    x ∈ traceU φ hφ ↔ x ∉ traceSmall φ hφ := Iff.rfl

@[simp] theorem mem_traceA {φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M}
    {hφ : Function.Injective φ} {x : Trace φ hφ} :
    x ∈ traceA φ hφ ↔ ∃ m : M, traceιM φ hφ m = x := Iff.rfl


open CategoryTheory in
/-- **A deformation retraction datum for a pair of subsets `A ⊆ U ⊆ X`.**  There are continuous maps
`i : A ⟶ U` (the inclusion) and `r : U ⟶ A` with `r ∘ i = id_A` and a homotopy `i ∘ r ≃ id_U`; the
inclusion of `A` into `U` is *both* a section and a retract of `r`.  For such a pair the quotient map
`C_*(U) ⟶ C_*(U, U ∩ A)` is null-homotopic, so the relative homology of the pair vanishes in every
degree (see `Submission/Work/ThreeConnected/Excision/PairVanish.lean`). -/
def IsDeformationRetractPair {X : TopCat.{0}} (U A : Set X) : Prop :=
  ∃ (hAU : A ⊆ U) (r : TopCat.of U ⟶ TopCat.of A) (i : TopCat.of A ⟶ TopCat.of U),
    (∀ a : A, i a = (⟨a.1, hAU a.2⟩ : U)) ∧ (∀ a : A, r (i a) = a) ∧
      Nonempty (TopCat.Homotopy (r ≫ i) (𝟙 (TopCat.of U)))

open CategoryTheory in
/-- **The deformation retraction of the open piece `U` of the cover of the trace onto its `M`-end
`A`.**  This is the point-set input which shows that the relative homology of `(U, A)` vanishes, and
hence — through the relative Mayer–Vietoris sequence — that the relative homology of the trace over
its `M`-end is that of the handle pair. -/
def TraceRetractData (φ : Work.Surgery.Sph k × Work.Surgery.Disk l → M)
    (hφ : Function.Injective φ) (hφc : Continuous φ) : Prop :=
  IsDeformationRetractPair (X := TopCat.of (Trace φ hφ)) (traceU φ hφ) (traceA φ hφ)

end

end Work.ThreeConnected
