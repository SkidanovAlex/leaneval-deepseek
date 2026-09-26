import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.ne_top_left_of_trace
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq

/-!
# The trace data of the tilted sweep, split into three clauses

`Work.Drive.Mono.TiltedTraceData` (`Submission/Work/Drive/Mono/TiltedTraceData.lean`) bundles four
clauses at the data of the tilted sweep.  This module *splits* them and *derives* the clause which
is a consequence of the others, so that the residual which the fleet has to prove has only three
geometric clauses:

* `TraceCurvesAt P s c σ u v h ℓ lam` (**clause 1**): at the level `lam` the trace of the level —
  the intersection of the surface `P.carrier` with the frontier of the level's removed set — is the
  union of the ranges of finitely many pairwise disjoint simple closed curves of `P`, each
  *inessential* in `P` (Pardon's Lemma 2 at the level, whose counting hypothesis is the level
  count `Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`).
* `AboveGenericAt P s c σ u v h ℓ lam` (**clause 2**): every point of the surface in the closed box
  and the closed tilted slab at the level `lam` is either a limit of points of the region
  `openTiltedSweepRegion … lam`, or lies on the trace (the frontier of the level's removed set).
* `NoJumpBelowAt P s c σ u v h ℓ lam` (**clause 4**): if the span of the region at the level `lam`
  vanishes then no level just below carries the full span — the content of Pardon's `2`-surgery
  count at the exceptional levels.

The fourth clause of `TiltedTraceData` — the *no-jump at the non-exceptional levels* — is
**derived** here from clauses 1 and 2 (`noJumpBelow_of_traceCurves`).

## Two corrections to `ne_top_left_of_trace`

1. **The cover hypothesis.**  `Work.Drive.Mono.ne_top_left_of_trace` assumes the trace curves to
   cover `P.carrier ∩ frontier (region)`, where `frontier` is the **ambient** frontier of `ℝ³`.
   Since the region is contained in the surface, its ambient interior is empty, so this hypothesis
   forces `region ⊆ ⋃ range`; together with `hsub` (the curves lie in the frontier of the removed
   set, disjoint from the region) it is *unsatisfiable* whenever the region is nonempty.  What is
   needed is the **relative** frontier version — every point of the surface in the *closure* of the
   region which is not in the region lies on the trace — and that version *follows* from the
   equality clause of `TraceCurvesAt` (`mem_frontier_removed_of_mem_closure` below: a point of the
   surface in the closure of the region is in the closure of the removed set's box part, and if it
   is outside the region it is outside the interior of that box part, hence in its frontier — which
   is the frontier of the level's removed set by the proved
   `Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq`, where `ℓ v = 0`, `ℓ ≠ 0` are used).

2. **The genericity hypothesis.**  `ne_top_left_of_trace` assumes every point `z` of the surface in
   the closed box and the closed slab at the level is a limit of points of the *region*
   (`z ∈ closure X`).  This is false at a point of the box sphere at which the surface touches the
   box from the outside (there the region has no points nearby at all): such a point is in the
   frontier of the removed set — i.e. *on the trace* — but not in `closure X`.  The hypothesis used
   here is therefore the *union* form `z ∈ closure X ∪ trace`, which is what the argument actually
   needs (the loop `δ` of the proof avoids the trace), and which is a direct consequence of the
   genericity of the sweep height at the points *inside* the box.

## The window

All the clauses are stated for levels in a window `[lam0, lam1]` containing the `ℓ`-range of the
box.  Outside the window the region of the sweep is the whole box region (below `lam0`) or the whole
box region minus the whole slab (above `lam1`), whose traces are *different* surfaces (the box
sphere, resp. the two caps of the box cut by a slab); their traces are families of inessential
curves as well, but by the *other* counting argument (`Work.EpsW.sphereTrace_inessential_of_countsWd`
and the half-box walls).  The assembly `tiltedSweepMono_of_traceDataW` only ever uses the window, so
the residual is stated with the window only.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}

/-- **Clause 1 of the trace data**: at the level `lam` the trace of the level is the union of the
ranges of finitely many pairwise disjoint simple closed curves of the surface, each inessential. -/
def TraceCurvesAt (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Prop :=
  ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P),
    (∀ i, Work.CoreTopology.IsSimple P (cs i)) ∧
    (∀ i, ¬ Work.CoreTopology.IsEssential P (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    (⋃ i, Set.range (cs i).γ) = P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)

/-- **Clause 2 of the trace data**: every point of the surface in the closed box and the closed
tilted slab at the level `lam` is either a limit of points of the level's region, or lies on the
level's trace. -/
def AboveGenericAt (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Prop :=
  ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
    |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
    z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ∪
      (P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))

/-- **Clause 4 of the trace data**: no level below a level of vanishing span carries the full
span. -/
def NoJumpBelowAt (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Prop :=
  Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊥ →
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤

/-- **The trace data of the tilted sweep, windowed**: clause 1 and clause 2 at every
non-exceptional level of the window, clause 4 at every exceptional level of the window. -/
def TiltedTraceDataW (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ)
    (lam0 lam1 : ℝ) : Prop :=
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → TraceCurvesAt P s c σ u v h ℓ lam) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → AboveGenericAt P s c σ u v h ℓ lam) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∈ (exc : Set ℝ) → NoJumpBelowAt P s c σ u v h ℓ lam)

/-- **A point of the surface in the closure of the level's region, off the region, lies in the
frontier of the level's removed set.**  This is the relative cover which the corrected no-jump
argument needs; it is a pure consequence of the box part of the region being open and of
`frontier_tiltedSweptBall_eq` (for which `ℓ v = 0` and `ℓ ≠ 0` are needed). -/
theorem mem_frontier_removed_of_mem_closure (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {z : R3} (hzc : z ∈ P.carrier)
    (hzcl : z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam))
    (hznx : z ∉ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) :
    z ∈ P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  set Rle : Set R3 := Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam})
    with hRledef
  have hfr : frontier Rle = frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
    rw [hRledef, tiltedLevelRemoved]
    exact Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq σ u ℓ hv hℓv hℓne
  have hregion : Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam =
      P.carrier ∩ Rle := rfl
  have hcl : z ∈ closure Rle :=
    closure_mono (by rw [hregion] at hzcl; exact fun y hy => hy.2) hzcl
  have hnotint : z ∉ interior Rle := by
    intro hint
    exact hznx (by rw [hregion]; exact ⟨hzc, interior_subset hint⟩)
  refine ⟨hzc, ?_⟩
  rw [← hfr]
  exact ⟨hcl, hnotint⟩

/-- **The strip between `mu` and `lamstar` misses a compact curve for `mu` close enough to
`lamstar`**, in the corrected (union) form of the genericity hypothesis: every point of the surface
in the closed box and the closed slab at the level `lamstar` is in `closure X lamstar` or on the
trace, and `δ` avoids both. -/
theorem exists_levelStrip_disjoint_of_generic' {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ}
    {δ : Work.CoreTopology.ClosedCurve P} {Z : Set R3}
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar) ∪ Z)
    (hdis : Disjoint (Set.range δ.γ)
      (closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar) ∪ Z)) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Disjoint (Set.range δ.γ) (levelStrip P s c σ u v h ℓ mu lamstar) := by
  classical
  have hmu_lt : ∀ k : ℕ, lamstar - 1 / ((k : ℝ) + 1) < lamstar := by
    intro k
    have hpos : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
    linarith
  have hmono : ∀ k k' : ℕ, k ≤ k' →
      lamstar - 1 / ((k : ℝ) + 1) ≤ lamstar - 1 / ((k' : ℝ) + 1) := by
    intro k k' hkk'
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
      have hc : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk'
      linarith
    have h3 : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
    linarith
  have hcl : ∀ k : ℕ,
      IsClosed (levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar) :=
    fun k => isClosed_levelStrip
  have hempty : Set.range δ.γ ∩
      ⋂ k : ℕ, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, rfl⟩ := hz1
    have hzk : ∀ k : ℕ,
        δ.γ t ∈ levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar :=
      fun k => Set.mem_iInter.mp hz2 k
    have hle : ℓ (δ.γ t) ≤ lamstar := (hzk 0).2.2.2
    have hge : ∀ k : ℕ, lamstar - 1 / ((k : ℝ) + 1) ≤ ℓ (δ.γ t) :=
      fun k => (hzk k).2.2.1
    have hlam : ℓ (δ.γ t) = lamstar := by
      refine le_antisymm hle ?_
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hcon)
      have h1 := hge k
      have h2 : lamstar - (lamstar - ℓ (δ.γ t)) < lamstar - 1 / ((k : ℝ) + 1) := by
        linarith
      linarith
    have hmem := hgen (δ.γ t) (δ.mem t) (hzk 0).1 (hzk 0).2.1 hlam
    exact (Set.disjoint_left.mp hdis) ⟨t, rfl⟩ hmem
  obtain ⟨ufin, hufin⟩ :=
    (Work.BoxShrink.PinchOff.isCompact_range_closedCurve δ).elim_finite_subfamily_closed
      (fun k : ℕ => levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar)
      hcl (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  replace hufin := Set.disjoint_iff_inter_eq_empty.mp hufin
  let k0 : ℕ := ufin.sup id
  have hk0_lt : lamstar - 1 / ((k0 : ℝ) + 1) < lamstar := hmu_lt k0
  refine ⟨lamstar - 1 / ((k0 : ℝ) + 1), hk0_lt, ?_⟩
  intro mu hmu
  have hsub : levelStrip P s c σ u v h ℓ mu lamstar ⊆
      ⋂ k ∈ ufin, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar := by
    intro z hz
    rw [Set.mem_iInter₂]
    intro k hk
    have hk_le : k ≤ k0 := Finset.le_sup (s := ufin) (f := id) hk
    have h1 : lamstar - 1 / ((k : ℝ) + 1) ≤ lamstar - 1 / ((k0 : ℝ) + 1) :=
      hmono k k0 hk_le
    exact levelStrip_anti (le_trans h1 hmu.1) hz
  rw [Set.disjoint_left]
  intro z hzr hz2
  have hmem : z ∈ Set.range δ.γ ∩
      (⋂ k ∈ ufin, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar) :=
    ⟨hzr, hsub hz2⟩
  rw [hufin] at hmem
  exact hmem

/-- **Clause 4 at a non-exceptional level, from the trace data**: the no-jump at a level whose
trace is a family of pairwise disjoint simple inessential curves equal to the frontier of the
removed set, which is approached from above on the surface (in the corrected union form).

This is `Work.Drive.Mono.ne_top_left_of_trace` with the two corrections described at the head of
this file; the proof is that of the sibling module, with the identity `closure X ∩ C = X` obtained
directly from the relative cover instead of from the ambient frontier, and with the strip lemma
applied to the union-form genericity. -/
theorem noJumpBelow_of_traceCurves (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcurves : TraceCurvesAt P s c σ u v h ℓ lam)
    (hgen : AboveGenericAt P s c σ u v h ℓ lam) :
    NoJumpBelowAt P s c σ u v h ℓ lam := by
  obtain ⟨n, cs, hsimple, hess, hdisj, hunion⟩ := hcurves
  intro hbot
  classical
  set T : Set R3 := ⋃ i, Set.range (cs i).γ with hT
  set X : Set R3 := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam with hX
  set A : Set R3 := Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) with hA
  set B : Set R3 := Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam}) with hB
  set C : Set R3 := P.carrier \ T with hC
  have hTclosed : IsClosed T := by
    rw [hT]
    exact Work.Drive.EpsFormSphere.isClosed_iUnion_range_closedCurve cs
  have hXeq : X = P.carrier ∩ B := by
    rw [hB]; rfl
  have hBopen : IsOpen B := by
    rw [hB]
    exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
      ((Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).inter
        (isClosed_Iic.preimage ℓ.continuous))
  have hBsubA : B ⊆ A := by
    rw [hB, hA]
    rintro z ⟨hzb, hrem⟩
    refine ⟨hzb, fun hcon => hrem ⟨hcon.1, ?_⟩⟩
    show ℓ z ≤ lam
    exact le_of_lt hcon.2
  have hXsubIntA : X ⊆ interior A := by
    rw [hXeq]
    exact fun z hz => interior_maximal hBsubA hBopen hz.2
  -- the trace lies in the frontier of the removed set (the equality clause)
  have hTsubA : T ⊆ P.carrier ∩ frontier A := by
    rw [hunion, hA, tiltedLevelRemoved]
  have hXdisjT : Disjoint X T := by
    rw [Set.disjoint_left]
    intro z hzX hzT
    have hzint : z ∈ interior A := hXsubIntA hzX
    have hzfr : z ∈ frontier A := (hTsubA hzT).2
    rw [← closure_sdiff_interior A] at hzfr
    exact hzfr.2 hzint
  -- the *relative* cover: points of the surface in the closure of the region, off the region,
  -- lie on the trace
  have hcover : ∀ z : R3, z ∈ P.carrier → z ∈ closure X → z ∉ X → z ∈ T := by
    intro z hzc hzcl hznx
    have hzf : z ∈ P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) :=
      mem_frontier_removed_of_mem_closure (P := P) hv hℓv hℓne hzc hzcl hznx
    exact hunion.symm ▸ hzf
  have hclC : closure X ∩ C = X := by
    apply Subset.antisymm
    · rintro z ⟨hzcl, hzC⟩
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      by_contra hznot
      exact hzC'.2 (hcover z hzC'.1 hzcl hznot)
    · intro z hz
      refine ⟨subset_closure hz, ?_⟩
      rw [hC]
      exact ⟨(hXeq ▸ hz).1, fun hzT => (Set.disjoint_left.mp hXdisjT) hz hzT⟩
  have hCB : C ∩ B = X := by
    rw [hXeq]
    apply Subset.antisymm
    · rintro z ⟨hzC, hzB⟩
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      exact ⟨hzC'.1, hzB⟩
    · intro z hz
      exact ⟨⟨hz.1, fun hzT => (Set.disjoint_left.mp hXdisjT) hz hzT⟩, hz.2⟩
  obtain ⟨K, hKpre, hKsub, hKW, hKother⟩ :=
    Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves (P := P) cs hsimple hess hdisj
  have hKsubC : K ⊆ C := by
    rw [hC, hT]
    exact hKsub
  obtain ⟨δ, hδess, hδmem⟩ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P K).mp (by rw [hKW]; exact top_ne_bot)
  have hδrange : Set.range δ.γ ⊆ K := fun z ⟨t, ht⟩ => ht ▸ hδmem t
  have hSpre : IsPreconnected (Set.range δ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P δ]
    exact isPreconnected_Ico.image δ.γ δ.cont.continuousOn
  have hδdisjT : Disjoint (Set.range δ.γ) T := by
    rw [Set.disjoint_left]
    intro z hzS hzT
    have hzC : z ∈ C := hKsubC (hδrange hzS)
    rw [hC] at hzC
    exact hzC.2 hzT
  have hSU : Set.range δ.γ ⊆ B ∪ (closure X)ᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · refine Or.inr ?_
      have hzC : z ∈ C := hKsubC (hδrange hz)
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      have hzX : z ∉ X := fun hzX => hzB (by rw [hXeq] at hzX; exact hzX.2)
      intro hzcl
      exact hzC'.2 (hcover z hzC'.1 hzcl hzX)
  have hSZdis : Set.range δ.γ ∩ (B ∩ (closure X)ᶜ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzS, hzB, hzV⟩
    have hzCB : z ∈ C ∩ B := ⟨hKsubC (hδrange hzS), hzB⟩
    rw [hCB] at hzCB
    exact hzV (subset_closure hzCB)
  have hSdisjClosure : Disjoint (Set.range δ.γ) (closure X) := by
    by_cases hSU0 : (Set.range δ.γ ∩ B).Nonempty
    · exfalso
      have hSV0 : Set.range δ.γ ∩ (closure X)ᶜ = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        intro hne
        have h1 : (Set.range δ.γ ∩ (B ∩ (closure X)ᶜ)).Nonempty :=
          hSpre B (closure X)ᶜ hBopen isClosed_closure.isOpen_compl hSU hSU0 hne
        rw [hSZdis] at h1
        exact Set.not_nonempty_empty h1
      have hSsubB : Set.range δ.γ ⊆ B := by
        intro z hz
        rcases hSU hz with h | h
        · exact h
        · have h2 : (Set.range δ.γ ∩ (closure X)ᶜ).Nonempty := ⟨z, hz, h⟩
          rw [hSV0] at h2
          exact absurd h2 (Set.not_nonempty_empty)
      have hSsubX : Set.range δ.γ ⊆ X := by
        intro z hz
        have hz' : z ∈ C ∩ B := ⟨hKsubC (hδrange hz), hSsubB hz⟩
        rwa [hCB] at hz'
      have hWne : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≠ ⊥ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
          ⟨δ, hδess, fun t => ⟨t, rfl⟩⟩
      have hle : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≤
          Work.SurgeryInvariance.WindingSpan P X :=
        Work.SurgeryInvariance.WindingSpan_mono P hSsubX
      rw [hbot] at hle
      exact hWne (le_bot_iff.mp hle)
    · rw [Set.disjoint_left]
      intro z hzrange hzcl
      rcases hSU hzrange with h | h
      · have h2 : (Set.range δ.γ ∩ B).Nonempty := ⟨z, hzrange, h⟩
        rw [Set.not_nonempty_iff_eq_empty.mp hSU0] at h2
        exact Set.not_nonempty_empty h2
      · exact h hzcl
  obtain ⟨mu0, hmu0lt, hstrip⟩ :=
    exists_levelStrip_disjoint_of_generic' (P := P) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (lamstar := lam) (δ := δ) (Z := T)
      (by
        intro z hzc hzcl hslab hlam
        rcases hgen z hzc hzcl hslab hlam with h | h
        · exact Or.inl h
        · exact Or.inr (hunion.symm ▸ h))
      (hSdisjClosure.union_right hδdisjT)
  refine ⟨mu0, hmu0lt, ?_⟩
  intro mu hmu
  have hdisX : Disjoint (Set.range δ.γ)
      (closure X ∪ levelStrip P s c σ u v h ℓ mu lam) :=
    hSdisjClosure.union_right (hstrip mu hmu)
  have hsubX : Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
      closure X ∪ levelStrip P s c σ u v h ℓ mu lam :=
    levelRegion_subset_closure_union_levelStrip (P := P) (mu := mu) (lamstar := lam)
  exact Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential P
    (fun z hz => (mem_openTiltedSweepRegion_iff.mp hz).1)
    (fun t hcon => (Set.disjoint_left.mp hdisX) ⟨t, rfl⟩ (hsubX hcon))
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P δ).mp hδess)


/-- **The windowed assembly**: if at every crux configuration one can choose the data of the tilted
sweep satisfying the size conditions and the *windowed* trace data `TiltedTraceDataW`, then
`Work.Drive.Final.TiltedSweepMono` holds.

This is `Work.Drive.Mono.tiltedSweepMono_of_traceData` with two changes: the levels of the two span
fields are taken in the window (which is all that the fields use), and the no-jump field (L) at the
non-exceptional levels is *derived* from the trace data (`noJumpBelow_of_traceCurves`) instead of
being an independent clause. -/
theorem tiltedSweepMono_of_traceDataW
    (H : ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              ‖v‖ = 1 ∧ ℓ ≠ 0 ∧ ℓ v = 0 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
              (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
              (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
              (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
              (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
              TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1) :
    Work.Drive.Final.TiltedSweepMono := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hℓne, hℓv, hvtilt, hh, hR, hlow, hhigh, hl, hexc,
    hTD⟩ :=
    H p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  refine ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hvtilt, hh, hR, hlow, hhigh, hl, hexc, ?_, ?_⟩
  · -- (D): the dichotomy at every non-exceptional level of the window
    intro lam hlam hne
    obtain ⟨n, cs, hsimple, hiness, hdisj, hunion⟩ := hTD.1 lam hlam hne
    set Rle : Set R3 := Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam})
      with hRledef
    set Rlt : Set R3 := Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam})
      with hRltdef
    have hfr : frontier Rle = frontier Rlt :=
      Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq σ u ℓ hvne hℓv hℓne
    have hleopen : IsOpen Rle := by
      rw [hRledef]
      exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
        ((Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).inter
          (isClosed_Iic.preimage ℓ.continuous))
    have htrace : (⋃ i, Set.range (cs i).γ) =
        (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier Rle := by
      rw [hunion]
      show (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier Rlt =
        (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier Rle
      rw [← hfr]
    have hTclosed : IsClosed (⋃ i, Set.range (cs i).γ) :=
      (isCompact_iUnion (fun i =>
        Work.BoxShrink.PinchOff.isCompact_range_closedCurve (cs i))).isClosed
    set X : Set R3 := Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam
      with hXdef
    have hXeq : X = (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Rle := rfl
    set Y : Set R3 := (Work.Drive.EpsSphere.torusOf ψ).carrier \
      ((⋃ i, Set.range (cs i).γ) ∪ closure X) with hYdef
    refine Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
      (P := Work.Drive.EpsSphere.torusOf ψ) (X := X) (Y := Y) (n := n) (γ := cs)
      hsimple hiness hdisj ?_ ?_ ?_ ?_
    · exact Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion
    · rw [hYdef, Set.sdiff_eq]
      refine Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := _) ?_
      exact (hTclosed.union isClosed_closure).isOpen_compl
    · rw [Set.disjoint_left]
      intro z hzX hzY
      exact hzY.2 (Or.inr (subset_closure hzX))
    · ext z
      constructor
      · rintro ⟨hzc, hzT⟩
        by_cases hzX : z ∈ X
        · exact Or.inl hzX
        · refine Or.inr ⟨hzc, ?_⟩
          intro hmem
          rcases hmem with hzT' | hzcl
          · exact hzT hzT'
          · have hzfr : z ∉ frontier Rle := by
              intro hfr'
              exact hzT (by rw [htrace]; exact ⟨hzc, hfr'⟩)
            have hzRle : z ∉ Rle := fun hzRle => hzX (by rw [hXeq]; exact ⟨hzc, hzRle⟩)
            have hsub : closure X ⊆ closure Rle :=
              closure_mono (by rw [hXeq]; exact Set.inter_subset_right)
            have hclR : z ∈ closure Rle := hsub hzcl
            rw [closure_eq_self_union_frontier] at hclR
            rcases hclR with hcl | hfr'
            · exact hzRle hcl
            · exact hzfr hfr'
      · rintro (hzX | hzY)
        · refine ⟨?_, ?_⟩
          · rw [hXeq] at hzX
            exact hzX.1
          · intro hzT'
            have hzfr : z ∈ frontier Rle := by rw [htrace] at hzT'; exact hzT'.2
            rw [hXeq] at hzX
            have h2 : z ∈ closure Rle \ Rle := hleopen.frontier_eq ▸ hzfr
            exact h2.2 hzX.2
        · exact ⟨hzY.1, fun hzT' => hzY.2 (Or.inl hzT')⟩
  · -- (L): no level of the window with span `⊥` is reached by a drop from `⊤`
    intro lam hlam hbot
    by_cases he : lam ∈ (exc : Set ℝ)
    · exact hTD.2.2 lam hlam he hbot
    · exact noJumpBelow_of_traceCurves (P := Work.Drive.EpsSphere.torusOf ψ) (s := s) (c := c)
        (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hvne hℓv hℓne
        (hTD.1 lam hlam he) (hTD.2.1 lam hlam he) hbot

end

end Work.Drive.Mono
