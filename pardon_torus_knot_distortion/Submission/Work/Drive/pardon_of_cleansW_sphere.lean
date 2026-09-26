import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.InterfacesD
import Submission.Work.BoxShrink.ledger
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.EpsFormSphere.Sideways
import Submission.Work.Drive.EpsFormSphere.thickHalf_of_sideSweepData
import Submission.Work.Drive.EpsFormSphere.Convert
import Submission.Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.Drive.EpsFormSphere.OpenTiltedRegion
import Submission.Work.Drive.EpsForm.exists_innermostDisc_essential_winding
import Submission.Work.Drive.cleansDiscsAllWd

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — field 2 in Pardon's ε-FORM

Read HANDOFF.md and Submission/Work/Drive/Interfaces.lean. PROVED: Work.Drive.pardon_of_weakInputs
(Drive/pardon_of_weakInputs.lean): the challenge follows from CleansDiscsAllW + CountingHalfW.
PROBLEM: a colleague's audit (Drive/countingHalfW_morse.lean,
`geometricHypotheses_insufficient_conclusion`) shows CountingHalfW is strictly stronger than
Pardon's Lemma 3. Your deliverable: the full distortion bound from CleansDiscsAllW ALONE, field 2
in Pardon's ε-form.

# What this file contains

1. `boxShrink_of_eps`, `pardon_of_boxShrink`, `pardon_of_cleansWd_sphere`: the *proved* re-threading
   of the crux which consumes the ε-form `Work.Drive.EpsSphere.CountingHalfEpsSphere` instead of
   `CountingHalfW` (the ε-margin `ε₀ = (shrinkFactor * r - (b * s + |u| / 2)) / 8` is spent by
   `EpsSphere.hasEssBox_of_thickHalf`).

2. **The correction of the sideways sweep.**  The frozen `Work.Drive.EpsSphere.SideSweepData`
   (`EpsFormSphere/Sideways.lean`) sweeps a *slab* `slabZ` whose two faces
   `{y (σ 2) = c (σ 2) + u ± h}` contribute K-points to the trace at every level that no hypothesis
   of the crux controls, so its `dichotomy` field is *not* derivable from the counting data (see
   `Submission/Work/Drive/EpsFormSphere/NOTES_H7_faceCounts.md`).  The wall must instead be the
   **flat cutting disc** itself:

     `wallDisc ℓ lam = cutDisc ∩ {y | ℓ y < lam}`,  `sideRegionD ℓ lam = P ∩ (PBox \ wallDisc ℓ lam)`.

   The removed set is then a subset of `cutDisc`, so the trace of every level carries
   `≤ #(K ∩ ∂PBox) + 2 #(K ∩ cutDisc)`-worth of the knot: exactly Pardon's count
   `countConst = 150`, *uniformly in the level* — which is what his `doublebubble` uses.  The
   endpoint of the corrected sweep is `boxRegion \ cutDisc = upperRegion ∪ lowerRegion` *exactly*
   (no ε-margin needed at the end), and the assembly `thickHalf_of_sideSweepDataD` below proves that
   the corrected data give Pardon's ε-form, exactly as `thickHalf_of_sideSweepData` does for the slab.

3. `SideSweepExistsD` — the residual of the corrected design (the four fields of the corrected
   `SideSweepDataD` at the counted configurations), and `countingHalfEpsSphere_of_sideSweepExistsD`:
   the residual gives the ε-form.

4. `not_cleansDiscsAllW_of_badDatum`: the vacuity route — *one* innermost-disc datum of the standard
   torus whose boundary has both winding components non-zero refutes `CleansDiscsAllW` (via the
   proved classification `Work.Drive.compressing_winding_dichotomyW` and the transport
   `Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph`).

Either the ε-form (route 3) or the refutation (route 4) closes the deliverable.

## Session 7: the refutation has landed — the frozen statement is closed, and why

The bad innermost-disc datum of route 4 is now **machine-checked and axiom-clean** in this workspace
(`Work.Drive.EpsForm.exists_innermostDisc_essential_winding`, assembled from the explicit waypoint
design `work_datumCore`), so `Work.Drive.CleansDiscsAllW` — the *hypothesis of this deliverable* — is
**false**: see `not_cleansDiscsAllW` below, one line from it and the proved classification
`compressing_winding_dichotomyW`.  Every statement whose hypotheses contain the legacy `CleansDiscsW`
is therefore vacuously true; the fleet closed its sibling legacy residual
`Work.Drive.EpsForm.countingHalfEps_holds` the same way, with the same warning.

Consequently:

* `pardon_of_cleansW_sphere` (the deliverable, statement untouched) is **proved**, by the vacuity
  proof `absurd hW not_cleansDiscsAllW` — it is true, but its content is *empty*, and it does **not**
  say that Pardon's bound follows from the weak cut-and-paste input (nothing does: that input is
  inconsistent);
* the **honest** statement is `pardon_of_cleansWd_of_epsSphere` (*also proved below*): the challenge
  from Pardon's ε-form `EpsSphere.CountingHalfEpsSphere` together with the claused cut-and-paste
  input `Work.Drive.CleansDiscsAllWd`, which is itself proved
  (`Work.Drive.cleansDiscsAllWd`).  Its only residual content is the ε-form, the fleet's live
  obligation for field 2 (`Work.Drive.EpsForm.epsBodyResidual`, `…PlateSweepExists`, or the tilted
  sweep `TiltedSweepExists` of this file through
  `countingHalfEpsShifted_of_tiltedSweepExists`);
* the tilted-sweep route (§7) is kept in full as *proved implications*: `TiltedSweepExists ⟹` its
  solid ε-form ⟹ the shifted ε-form ⟹ the crux's box shrink ⟹ the challenge.  Its residual is phrased
  over the *corrected* `CleansDiscsWd`, so it is **not** vacuous; the three geometric fields it still
  needs (P2'-P4') are recorded in `EpsFormSphere/NOTES_H7_session7_refutation.md` §4.

Report for the fleet: `EpsFormSphere/NOTES_H7_session7_refutation.md`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-! ## 1. The crux from the ε-form (proved) -/

theorem boxShrink_of_eps (hW : Work.Drive.CleansDiscsAllWd)
    (hE : EpsSphere.CountingHalfEpsSphere) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ hbox
  obtain ⟨s, hs, hslice, hS, u, hu, hU⟩ :=
    Work.BoxShrink.SweepNice.of_aeAll
      (Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis)
      p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ
  have hu' : |u| < Submission.eps * r := abs_lt.mpr hu
  have hmargin : 0 < Submission.shrinkFactor * r - (Submission.b * s + |u| / 2) :=
    EpsSphere.margin_pos hr hs.1 hs.2 hu'
  have hε₀pos : 0 < (Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8 := by
    linarith
  have hε₀8 : 8 * ((Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8)
      ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2) := by linarith
  have hhalf := hE p q hp hq hc ψ K d hd hbound himg hsmall
    (hW ψ) r hr c σ hbox
    s hs.1 hs.2 hslice u hu' hS hU
    ((Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8) hε₀pos
  exact EpsSphere.hasEssBox_of_thickHalf hr hs.1 hs.2 hu' hε₀pos hε₀8 hhalf

theorem pardon_of_boxShrink (hW : Work.Drive.CleansDiscsAllWd)
    (hE : EpsSphere.CountingHalfEpsSphere)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Submission.theorem_of_core
    (Submission.CoreStatement_of_boxShrink (boxShrink_of_eps hW hE))
    p q hp hq hc K hclass

theorem cleansDiscsAllWd_of_W (h : Work.Drive.CleansDiscsAllW) : Work.Drive.CleansDiscsAllWd :=
  fun ψ => Work.Drive.cleansDiscsWd_of_W (h ψ)

theorem pardon_of_cleansWd_sphere (hW : Work.Drive.CleansDiscsAllWd)
    (hE : EpsSphere.CountingHalfEpsSphere)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_of_boxShrink hW hE p q hp hq hc K hclass

/-! ## 2. The corrected sweep: walling by the flat cutting disc -/

/-- **The moving wall of the corrected sweep**: the piece of the flat cutting disc behind the level
`lam` of the generic functional `ℓ`. -/
def wallDisc (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (ℓ : R3 →L[ℝ] ℝ)
    (lam : ℝ) : Set R3 :=
  Work.BoxShrink.Core.cutDisc s c σ u ∩ {y : R3 | ℓ y < lam}

/-- **The region of the corrected sweep**: the box region with the part of the cutting disc behind
the wall removed. -/
def sideRegionD (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ (Submission.PBox s c σ \ wallDisc s c σ u ℓ lam)

theorem mem_sideRegionD {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ sideRegionD P s c σ u ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        (y ∉ Work.BoxShrink.Core.cutDisc s c σ u ∨ lam ≤ ℓ y) := by
  constructor
  · rintro ⟨hyc, hyb, hyw⟩
    refine ⟨hyc, hyb, ?_⟩
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.mp h
    exact hyw ⟨by simpa using h1, not_le.mp h2⟩
  · rintro ⟨hyc, hyb, h⟩
    refine ⟨hyc, hyb, ?_⟩
    rintro ⟨hcd, hlt⟩
    rcases h with h | h
    · exact h hcd
    · exact absurd hlt (not_lt.mpr h)

theorem sideRegionD_anti {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {ℓ : R3 →L[ℝ] ℝ} {μ ν : ℝ} (h : μ ≤ ν) :
    sideRegionD P s c σ u ℓ ν ⊆ sideRegionD P s c σ u ℓ μ := by
  intro y hy
  rw [mem_sideRegionD] at hy ⊢
  refine ⟨hy.1, hy.2.1, ?_⟩
  rcases hy.2.2 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (le_trans h h')

/-- At a level below the whole wall, the region of the corrected sweep is the whole box region. -/
theorem sideRegionD_eq_boxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (h : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, lam ≤ ℓ y) :
    sideRegionD P s c σ u ℓ lam = Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  rw [mem_sideRegionD, Work.BoxShrink.Core.mem_boxRegion]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    by_cases hy : y ∈ Work.BoxShrink.Core.cutDisc s c σ u
    · exact Or.inr (h y hy)
    · exact Or.inl hy

/-- At a level above the whole wall, the region of the corrected sweep is the box region with the
cutting disc removed — i.e. the two half-regions. -/
theorem sideRegionD_eq_sdiff {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (h : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, ℓ y < lam) :
    sideRegionD P s c σ u ℓ lam =
      Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.cutDisc s c σ u := by
  ext y
  rw [mem_sideRegionD, Set.mem_sdiff, Work.BoxShrink.Core.mem_boxRegion]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro hcd
    rcases h3 with h3 | h3
    · exact h3 hcd
    · exact absurd (h y hcd) (not_lt.mpr h3)
  · rintro ⟨⟨h1, h2⟩, hcd⟩
    exact ⟨h1, h2, Or.inl hcd⟩

/-- **The end region of the corrected sweep is exactly the two half-regions.** -/
theorem boxRegion_sdiff_cutDisc (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.cutDisc s c σ u =
      Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u := by
  ext y
  rw [Set.mem_sdiff, Work.BoxShrink.Core.mem_boxRegion, Work.BoxShrink.Core.mem_cutDisc,
    Set.mem_union, Work.BoxShrink.Core.mem_upperRegion, Work.BoxShrink.Core.mem_lowerRegion]
  constructor
  · rintro ⟨⟨hyc, hyb⟩, hne⟩
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inr ⟨hyc, hyb, h⟩
    · exact absurd ⟨hyb, h⟩ hne
    · exact Or.inl ⟨hyc, hyb, h⟩
  · rintro (⟨hyc, hyb, h⟩ | ⟨hyc, hyb, h⟩)
    · exact ⟨⟨hyc, hyb⟩, fun hcon => absurd hcon.2 (ne_of_gt h)⟩
    · exact ⟨⟨hyc, hyb⟩, fun hcon => absurd hcon.2 (ne_of_lt h)⟩

/-- A closed curve of the end region of the corrected sweep lies entirely in one of the two
half-regions: its image is connected and the coordinate function misses `0` on it. -/
theorem forall_mem_half_of_forall_mem_sdiff_cutDisc {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {γ : Work.CoreTopology.ClosedCurve P}
    (hmem : ∀ t : ℝ,
      γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.cutDisc s c σ u) :
    (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have hcoord : Continuous fun y : R3 => y (σ 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)
  have hcont : Continuous fun t : ℝ => (γ t) (σ 2) - (c (σ 2) + u) :=
    (hcoord.comp γ.cont).sub continuous_const
  have hne : ∀ t : ℝ, (γ t) (σ 2) - (c (σ 2) + u) ≠ 0 := by
    intro t h0
    exact (hmem t).2 (by
      rw [Work.BoxShrink.Core.mem_cutDisc]
      exact ⟨(hmem t).1.2, by linarith⟩)
  by_cases hup : ∃ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u
  · left
    intro t
    have hpos : 0 < (γ t) (σ 2) - (c (σ 2) + u) := by
      by_contra hcon
      have hlt : (γ t) (σ 2) - (c (σ 2) + u) < 0 :=
        lt_of_le_of_ne (not_lt.mp hcon) (hne t)
      obtain ⟨t₁, ht₁⟩ := hup
      have h₁ : 0 < (γ t₁) (σ 2) - (c (σ 2) + u) := by
        have h := (Work.BoxShrink.Core.mem_upperRegion.mp ht₁).2.2
        linarith
      obtain ⟨τ, hτ⟩ := intermediate_value_univ t t₁ hcont
        (⟨le_of_lt hlt, le_of_lt h₁⟩ : (0 : ℝ) ∈ Set.Icc ((γ t) (σ 2) - (c (σ 2) + u))
          ((γ t₁) (σ 2) - (c (σ 2) + u)))
      exact hne τ hτ
    exact Work.BoxShrink.Core.mem_upperRegion.mpr ⟨γ.mem t, ((hmem t).1).2, by linarith⟩
  · right
    intro t
    have hneg : (γ t) (σ 2) - (c (σ 2) + u) < 0 := by
      by_contra hcon
      have hpos : 0 < (γ t) (σ 2) - (c (σ 2) + u) :=
        lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (hne t))
      exact hup ⟨t, Work.BoxShrink.Core.mem_upperRegion.mpr
        ⟨γ.mem t, ((hmem t).1).2, by linarith⟩⟩
    exact Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨γ.mem t, ((hmem t).1).2, by linarith⟩

/-! NOTE on the `start`/`finish` fields of `SideSweepDataD`: they are *available at every functional*
`ℓ` — `Work.Drive.EpsFormSphere.sideSweepEndpointsDisc`
(`Submission/Work/Drive/EpsFormSphere/sideSweepEndpointsDisc.lean`, **proved**) gives, for every
`P s c σ u ℓ`, levels `lam0 < lam1` with `sideRegionD · lam0 = boxRegion` and
`sideRegionD · lam1 = boxRegion \ cutDisc`.  (That module imports this one for the definitions, so
this file cannot import it back; the fact is recorded here and in
`EpsFormSphere/NOTES_H7_faceCounts.md`.)  So `SideSweepExistsD` reduces to its three analytic fields
`regular_span`, `jump`, `dichotomy`. -/

/-! ## 3. The corrected sweep data and its assembly into the ε-form -/

/-- **The four ingredients of the corrected sideways sweep** (with the flat disc as the wall).

`exc` is the finite set of critical values of `ℓ` on the trace `carrier ∩ cutDisc` (the levels at
which the moving line `{ℓ = lam}` is tangent to the trace, or passes one of its boundary points).
The removed set at the level `lam` is a subset of `cutDisc`, so the trace of every level carries at
most the box-sphere trace together with (two copies of) the cutting-disc trace: the crux's two
counts `hS`, `hU` bound the knot's crossings of the trace *uniformly in the level*, which is what
Pardon's `doublebubble` uses. -/
structure SideSweepDataD (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the horizontal functional -/
  ℓ : R3 →L[ℝ] ℝ
  /-- the lower end of the sweep -/
  lam0 : ℝ
  /-- the upper end of the sweep -/
  lam1 : ℝ
  /-- the sweep is nondegenerate -/
  hlt : lam0 < lam1
  /-- the critical values of `ℓ` on the trace (inside the swept interval) -/
  exc : Finset ℝ
  /-- they all lie strictly inside the swept interval -/
  exc_mem : ∀ t ∈ exc, lam0 < t ∧ t < lam1
  /-- at the lower end nothing is removed yet -/
  start : sideRegionD P s c σ u ℓ lam0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- at the upper end the whole cutting disc is removed: the two half-regions -/
  finish : sideRegionD P s c σ u ℓ lam1 =
    Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.cutDisc s c σ u
  /-- **P2**: between two levels with no critical value in between, the winding span is constant. -/
  regular_span : ∀ lam lam' : ℝ, lam0 ≤ lam → lam ≤ lam' → lam' ≤ lam1 →
    (∀ t ∈ exc, t < lam ∨ lam' < t) →
    Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ lam) =
      Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ lam')
  /-- **P3**: across a single critical value the `H₁`-image rank changes by at most one. -/
  jump : ∀ lam ∈ exc, ∀ mu nu : ℝ, lam0 ≤ mu → mu < lam → lam < nu → nu ≤ lam1 →
    (∀ t ∈ exc, t < mu ∨ t = lam ∨ nu < t) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ mu)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ nu)) + 1 ∧
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ nu)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ mu)) + 1
  /-- **P4**: at a regular level the winding span is `⊥` or `⊤` (Pardon's dichotomy: the trace of
  the level is a family of inessential curves, from the two counts). -/
  dichotomy : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
    Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ lam) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u ℓ lam) = ⊤

/-- The winding span of the level `lam` of the corrected sweep. -/
def sideSpanD {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (D : SideSweepDataD P s c σ u) (lam : ℝ) : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P (sideRegionD P s c σ u D.ℓ lam)

theorem sideSpanD_anti {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : SideSweepDataD P s c σ u) {μ ν : ℝ} (h : μ ≤ ν) :
    sideSpanD D ν ≤ sideSpanD D μ :=
  Work.SurgeryInvariance.WindingSpan_mono P (sideRegionD_anti h)

/-- **The winding span is constant along the corrected sweep.** -/
theorem span_eq_of_sideSweepDataD {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : SideSweepDataD P s c σ u) :
    sideSpanD D D.lam0 = sideSpanD D D.lam1 := by
  have h := Work.Drive.EpsFormSphere.span_const_of_sweep_axioms P
    (fun lam : ℝ => sideRegionD P s c σ u D.ℓ lam) D.lam0 D.lam1 D.exc D.hlt D.exc_mem
    (fun μ ν h => sideRegionD_anti h) D.regular_span D.jump D.dichotomy
  simpa only [sideSpanD] using h

/-- **The end region of the corrected sweep is essential**, since the box region is. -/
theorem containsEssentialLoop_sdiff_cutDisc {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : SideSweepDataD P s c σ u)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    P.ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.cutDisc s c σ u) := by
  have h0 : sideSpanD D D.lam0 ≠ ⊥ := by
    rw [sideSpanD, D.start]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have h1 : sideSpanD D D.lam1 ≠ ⊥ := by
    rw [← span_eq_of_sideSweepDataD D]; exact h0
  rw [← D.finish]
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h1

/-- **The assembly (P5) of the corrected sweep**: its data give Pardon's ε-form. -/
theorem thickHalf_of_sideSweepDataD {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (D : SideSweepDataD P s c σ u)
    (ε : ℝ) (hε : 0 < ε)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    Work.Drive.EpsSphere.ThickHalf P s c σ u ε := by
  obtain ⟨γ, hess, hmem⟩ := containsEssentialLoop_sdiff_cutDisc D hbox
  rcases forall_mem_half_of_forall_mem_sdiff_cutDisc hmem with h | h
  · exact Or.inl ⟨γ, hess, fun t =>
      Metric.mem_thickening_iff.mpr ⟨γ t, h t, by rw [dist_self]; exact hε⟩⟩
  · exact Or.inr ⟨γ, hess, fun t =>
      Metric.mem_thickening_iff.mpr ⟨γ t, h t, by rw [dist_self]; exact hε⟩⟩

/-! ## 4. The residual of the corrected design and its consequence -/

/-- **The residual of the corrected design** (P1–P4 with the flat-disc wall): at every configuration
carrying the counting data of the crux there are a functional `ℓ`, endpoints and the critical values
such that the corrected sweep starts at the box region, ends at the two half-regions, has constant
span between critical values, changes the rank by at most one at each of them, and has span `⊥` or
`⊤` at every regular level (Pardon's dichotomy, from the two counts). -/
def SideSweepExistsD : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Nonempty (SideSweepDataD (EpsSphere.torusOf ψ) s c σ u)

/-- **The residual of the corrected design gives Pardon's ε-form.** -/
theorem countingHalfEpsSphere_of_sideSweepExistsD (h : SideSweepExistsD) :
    EpsSphere.CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  obtain ⟨D⟩ := h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice
    u hu hS hU
  exact thickHalf_of_sideSweepDataD D ε hε
    (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)

/-! ## 5. The vacuity route: one bad innermost-disc datum refutes `CleansDiscsAllW` -/

/-- **A bad innermost-disc datum refutes `CleansDiscsW standard`**: the proved classification
`Work.Drive.compressing_winding_dichotomyW` says that a weak bounding disc forces one winding
component of every lift to vanish. -/
theorem not_cleansDiscsW_standard_of_badDatum
    (h : ∃ (S : Set R3) (D : Work.InnermostDisk.InnermostDisc Work.CoreTopology.standard S),
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).1 ≠ 0) ∧
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).2 ≠ 0)) :
    ¬ Work.Drive.CleansDiscsW Work.CoreTopology.standard := by
  rintro hcl
  obtain ⟨S, D, ⟨L₁, h₁⟩, ⟨L₂, h₂⟩⟩ := h
  rcases Work.Drive.compressing_winding_dichotomyW D.α D.essential (hcl S D) with hd | hd
  · exact h₂ (hd L₂)
  · exact h₁ (hd L₁)

/-- **A bad innermost-disc datum refutes `CleansDiscsAllW`** (the hypothesis of the deliverable):
the datum transports along an ambient homeomorphism of `ℝ³`
(`Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph`), so it suffices to apply the hypothesis at any
one diffeomorphism. -/
theorem not_cleansDiscsAllW_of_badDatum
    (h : ∃ (S : Set R3) (D : Work.InnermostDisk.InnermostDisc Work.CoreTopology.standard S),
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).1 ≠ 0) ∧
      (∃ L : Work.CoreTopology.LiftOf Work.CoreTopology.standard D.α, (L.winding).2 ≠ 0)) :
    ¬ Work.Drive.CleansDiscsAllW := by
  intro hW
  let ψ₀ : Submission.Diffeo :=
    ⟨id, id, contDiff_id, contDiff_id, fun _ => rfl, fun _ => rfl⟩
  exact (Work.Drive.EpsForm.not_cleansDiscsW_mapHomeomorph
    (not_cleansDiscsW_standard_of_badDatum h) ψ₀.toHomeomorph) (hW ψ₀)

/-- **`Work.Drive.CleansDiscsAllW` is REFUTED** — the key finding of session 7.

The bad datum is *machine-checked* in this workspace: `Work.Drive.EpsForm.exists_innermostDisc_essential_winding`
(`Submission/Work/Drive/EpsForm/exists_innermostDisc_essential_winding.lean`, axiom-clean, resting on
the explicit waypoint design `work_datumCore`) exhibits an `InnermostDisc` datum of the standard torus
whose boundary curve is the standard `(1,1)`-curve, together with lifts of that curve with non-zero
first, resp. non-zero second, winding component.  By the *proved* classification
`Work.Drive.compressing_winding_dichotomyW` (`Work.CoreTopology.compressing_winding_dichotomyW`) a
weak bounding disc would force one component to vanish — so no weak (hence no injective) disc bounds
that boundary curve, and the legacy unclaused cut-and-paste input fails.

**Consequences for the fleet** (see `EpsFormSphere/NOTES_H7_session7_refutation.md`):

* the *hypothesis* of the deliverable `Work.Drive.pardon_of_cleansW_sphere` (and of every residual
  phrased over the legacy `CleansDiscsW`: `Work.Drive.CountingHalfW`, `Work.Drive.CountingHalfEps`,
  `Work.Drive.EpsForm.ArcBodyOff`, `Work.Drive.EpsForm.FingerSweepExists`, `…PlateSweepExists`) is
  *unsatisfiable*: every such statement is *vacuously* true, and in particular says nothing about any
  actual knot;
* the honest input is the claused `Work.Drive.CleansDiscsAllWd`, which is *proved* in this workspace
  (`Submission/Work/Drive/cleansDiscsAllWd.lean`), and every residual has a `…Wd` spelling
  (`Work.Drive.CountingHalfEpsD`, `Work.Drive.EpsForm.ArcBodyOffD`, …);
* the deliverable is closed *non-vacuously* by `pardon_of_cleansWd_sphere` below (the corrected input
  together with Pardon's ε-form), whose only residual is the ε-form itself.

This brick is recorded so that the finding is usable by the whole fleet (it is the Lean form of
`report lemma-Drive_cleansDiscsAllW.md`). -/
theorem not_cleansDiscsAllW : ¬ Work.Drive.CleansDiscsAllW :=
  not_cleansDiscsAllW_of_badDatum Work.Drive.EpsForm.exists_innermostDisc_essential_winding

/-! ## 6. The slab residual of the design (P1-P4 of the frozen sideways sweep)

The frozen design (`EpsFormSphere/Sideways.lean`, the project lead's formulation) uses the *slab*
`slabZ c σ u h` of half-width `h` around the cutting plane, swept by the wall
`wallRegion = slabZ ∩ {ℓ < lam}`, with region `sideRegion P s c σ u h ℓ lam`.  Its residual is
`EpsSphere.SideSweepExists` (P1-P4 at the counted configurations), and its assembly into Pardon's
ε-form is the *proved* `thickHalf_of_sideSweepData`.  The slab is the right geometry for the count at
a regular level: the frontier `∂R_lam` of the swept ball `R_lam = PBox \ (slabZ ∩ {ℓ < lam})` is a
*sphere*, so the trace `F ∩ ∂R_lam` consists of **closed** curves of the surface — each of them
bounds a disc inside the sphere, whose intersections with the knot are counted by
`#(K ∩ ∂R_lam) ≤ #(K ∩ ∂PBox) + 2 #(K ∩ D) < min p q` (the slab's short arcs, one per crossing of
the cutting disc), and `mustbeinessential` (`min_le_encard_inter_of_boundsDiskW` with
`CleansDiscsWd`) then makes each of them inessential.  Pardon's dichotomy
(`EpsFormSphere.windingSpan_bot_or_top_of_trace_inessential`) converts that into
`W(sideRegion · lam) ∈ {⊥, ⊤}`.

The `SideSweepDataD` material above (the disc-wall variant) is kept for the record: its
`dichotomy` field demanded `W ∈ {⊥, ⊤}` at levels whose trace is only *partially* covered by the
cutting disc, which is why the slab — whose removed piece is a *thickened* half-disc, making
`∂R_lam` a sphere — is the shape in which the count actually lands. -/

/-- **The slab residual gives Pardon's ε-form** through the *proved* assembly
`EpsFormSphere.thickHalf_of_sideSweepData`. -/
theorem countingHalfEpsSphere_of_sideSweepExists (h : EpsSphere.SideSweepExists) :
    EpsSphere.CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  obtain ⟨D⟩ := h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice
    u hu hS hU
  exact EpsFormSphere.thickHalf_of_sideSweepData D ε hε
    (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)

/-! ### The state of P1-P4 of the slab design (H7's session of 2026-09-25)

The four ingredients of `EpsSphere.SideSweepExists` are now the following proved bricks plus **P1**,
the single remaining geometric input (the generic data of the sweep at every counted configuration):

* **P2** (`regular_span`, the span is constant between critical values): the transport machinery
  (`Work.SurgeryInvariance.RegionIsotopic` / `RegionEquivalent`), together with P1's statement that the
  regions between consecutive critical values are ambient-isotopic;
* **P3** (`jump`, the rank changes by at most one at a critical value):
  `Work.Drive.EpsFormSphere.finrank_jump_of_discAttachment`
  (from the disc-attachment bound `finrank_windingSpan_le_of_discAttachment`, in the form the lead
  fixed on 2026-09-25 after three variants were refuted: the attaching pieces must be path-connected
  and the *accumulation* of the region on the disc must sit in them), together with P1's
  identification of the level change with an attached disc of the surface;
* **P4** (`dichotomy`, the span is `⊥` or `⊤` at a regular level):
  `Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_slicing_of_countsWd`, whose inputs are P1's
  slicing of the level sphere and the two frontier clauses, Pardon's Lemma 2 in the corrected
  vocabulary (`Work.EpsW.trace_inessential_of_slicing_of_countsWd`), the count
  `Work.Drive.EpsFormSphere.encard_frontier_inter_lt_min` and the arithmetic
  `Work.Drive.EpsFormSphere.count_bound_of_hS_hU` (`10(1+ε)/ε·d + 2·5(1+ε)/ε·d = 150 d < min p q`);
* **the endpoints** (`start`, `finish`): P1, and the `ε`-clause is *not* needed at the end — the proved
  `EpsFormSphere.thickHalf_of_sideSweepData` already derives `ThickHalf … ε` for every `ε > 0` from the
  exact `finish` (`boxRegion \ slabZ ⊆ upperRegion ∪ lowerRegion`);
* the swept region must be taken **open** in the carrier for P4 (`openSideRegion`, and
  `EpsFormSphere/NOTES_H7_P4_dichotomy.md` §7): the design's `sideRegion` contains the 1-dimensional
  trace, and the wall dichotomies need open pieces.

The analysis, the four counterexamples that pin the statement of the count, and the full module list
are in `EpsFormSphere/NOTES_H7_P4_dichotomy.md`. -/

/-! ## 7. The corrected design: the *tilted* sweep and the solid ε-form

The residual `EpsSphere.SideSweepExists` of §6 sweeps a slab *orthogonal* to the direction
`e_{σ 2}` of the cutting plane.  `EpsForm/NOTES_P1_horizontality_OBSTRUCTION.md` records that the
genericity clause of P1 is then unsatisfiable: for a surface carrying an exactly cylindrical band
whose generators are parallel to `e_{σ 2}`, every horizontal functional `ℓ` is degenerate and no
finite set of critical values with a single handle per level exists.  The corrected design (the
project lead's and H6's) lets the slab **tilt**: the removed set is
`tiltedSlabClosed (⟪v, c⟫ + u) v h` for a unit normal `v` within `ε` of `e_{σ 2}`, and the sweep is
run with a wall functional `ℓ` perpendicular to `v`.  Genericity in the *pair* `(v, ℓ)` removes the
obstruction, and the conclusion needed at the end of the sweep is only Pardon's *solid* form
(`F ∩ (B(ε) + int(H_i))` carries the genus), which is what the perturbation into general position
produces — declared as the residual below.

The assembly of the tilted data into the solid ε-form is *proved* in the workspace:

* `Work.Drive.EpsForm.epsConclusion_of_sweep_axioms` — the five fields of the tilted sweep
  (regularity between critical levels, the rank jump across one of them, the dichotomy at the
  regular levels, and the two endpoints) plus the tilt conditions give the solid ε-conclusion;
* `EpsFormSphere.span_const_of_sweep_axioms` — the bookkeeping making the span constant along the
  sweep (the `jump` and `dichotomy` fields force it).

What is proved *here* is the rest of the chain: the solid ε-conclusion implies the shifted ε-form
`EpsSphere.ThickHalfShifted` (a short estimate in the box norm), which `EpsSphere.hasEssBox_of_thickHalfShifted`
converts into the crux's box shrink, giving the challenge. -/

/-- **The region of the tilted sweep at the level `lam`**: the surface inside the box with the part
of the tilted slab in front of the level removed. -/
def tiltedSweepRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  Work.Drive.EpsForm.sweepRegion P s c σ
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam

/-- **Pardon's `doublebubble2` conclusion in its *solid* form** at one configuration: for every
`ε > 0` an essential loop of the surface lies within `ε` of one of the two *solid* half-boxes
`{y ∈ PBox s c σ | y (σ 2) < c (σ 2) + u}` (resp. `>`).  This is the conclusion of Pardon's
perturbation of the double bubble into general position. -/
def SolidEpsConclusion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u ε : ℝ) : Prop :=
  (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
        dist (γ t) x < ε) ∨
    (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
        dist (γ t) x < ε)

/-! ### The dichotomy: one level per regular stretch suffices

Pardon's own argument chooses the intermediate spheres *by averaging* (integral geometry), precisely
so that the number of intersections of the chosen sphere with the knot is small.  The corresponding
formal statement is weaker than "at *every* regular level the span is `⊥` or `⊤`": it is enough that
on every stretch without critical values there is *one* regular level whose span is `⊥` or `⊤`, since
the span is constant on the stretch (P2').  The bookkeeping of
`EpsFormSphere.submodule_const_of_finrank_jumps` only consumes the resulting every-level form, and
the following lemma produces it. -/

/-- **The dichotomy at every regular level, from the dichotomy at one level per regular stretch.**
Let `V` be the family of winding spans along a sweep with critical set `exc ⊆ (lam0, lam1)`, constant
between critical levels (`hreg`).  If on every interval `[μ, ν]` free of critical values there is a
level `mu` (of the interval, not critical) at which `V mu` is `⊥` or `⊤`, then *every* regular level
of `[lam0, lam1]` has that property. -/
theorem dichotomy_every_level_of_one_per_stretch {V : ℝ → Submodule ℚ (ℚ × ℚ)} {lam0 lam1 : ℝ}
    (exc : Finset ℝ) (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hreg : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → (∀ t ∈ exc, t < μ ∨ ν < t) → V μ = V ν)
    (hone : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → (∀ t ∈ exc, t < μ ∨ ν < t) →
      ∃ mu : ℝ, μ ≤ mu ∧ mu ≤ ν ∧ (∀ t ∈ exc, t ≠ mu) ∧ (V mu = ⊥ ∨ V mu = ⊤)) :
    ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) → V lam = ⊥ ∨ V lam = ⊤ := by
  intro lam h0 h1 hnx
  by_cases hup : ∃ t ∈ exc, lam < t
  · -- a critical value above `lam`: take the smallest one and work on `[lam, (lam + hi)/2]`
    obtain ⟨t₀, ht₀⟩ := hup
    set S : Finset ℝ := exc.filter (fun t => lam < t) with hS
    have hSne : S.Nonempty := ⟨t₀, Finset.mem_filter.mpr ht₀⟩
    set hi : ℝ := S.min' hSne with hhi
    have hhi_mem : hi ∈ S := Finset.min'_mem S hSne
    have hhi_exc : hi ∈ exc := (Finset.mem_filter.mp hhi_mem).1
    have hhi_gt : lam < hi := (Finset.mem_filter.mp hhi_mem).2
    have hhi_le : hi ≤ lam1 := le_of_lt (hexc hi hhi_exc).2
    set nu : ℝ := (lam + hi) / 2 with hnu
    have hnu_ge : lam ≤ nu := by rw [hnu]; linarith
    have hnu_le : nu ≤ lam1 := by rw [hnu]; linarith
    have hstep : ∀ t ∈ exc, lam < t → hi ≤ t := by
      intro t ht hlt
      exact Finset.min'_le S t (Finset.mem_filter.mpr ⟨ht, hlt⟩)
    have hsep : ∀ t ∈ exc, t < lam ∨ nu < t := by
      intro t ht
      by_cases hlt : t < lam
      · exact Or.inl hlt
      · have hlt' : lam < t := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hnx t ht h.symm)
        exact Or.inr (by have := hstep t ht hlt'; rw [hnu]; linarith)
    obtain ⟨mu, hmu_ge, hmu_le, hmu_nx, hmu_dich⟩ := hone lam nu h0 hnu_ge hnu_le hsep
    have hmu_lt : mu < hi := lt_of_le_of_lt hmu_le (by rw [hnu]; linarith)
    have hreg' : V lam = V mu :=
      hreg lam mu h0 hmu_ge (by linarith) (fun t ht => by
        by_cases hlt : t < lam
        · exact Or.inl hlt
        · have hlt' : lam < t := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hnx t ht h.symm)
          exact Or.inr (by have := hstep t ht hlt'; linarith))
    rw [hreg']; exact hmu_dich
  · -- no critical value above `lam`: the stretch `[lam, lam1]` is free of critical values
    simp only [not_exists, not_and, not_lt] at hup
    have hsep : ∀ t ∈ exc, t < lam ∨ lam1 < t := by
      intro t ht
      have htle : t ≤ lam := hup t ht
      rcases lt_or_eq_of_le htle with h | h
      · exact Or.inl h
      · exact absurd h (hnx t ht)
    obtain ⟨mu, hmu_ge, hmu_le, hmu_nx, hmu_dich⟩ := hone lam lam1 h0 h1 le_rfl hsep
    have hreg' : V lam = V mu :=
      hreg lam mu h0 hmu_ge hmu_le (fun t ht => by
        by_cases hlt : t < lam
        · exact Or.inl hlt
        · have hle : t ≤ lam := hup t ht
          exact absurd (lt_of_le_of_ne hle (fun h => hnx t ht h)) (not_lt.mpr (not_lt.mp hlt)))
    rw [hreg']; exact hmu_dich

/-! ## 7. The tilted-sweep route (P1'-P4'): the residual, and its proved consequences

`TiltedSweepExists` is the residual of the corrected, *tilted* sweep design: at every counted crux
configuration and every `ε > 0` there are a unit normal `v` within `ε` of `e_{σ 2}`, a slab
half-width `h` and a radius `R` with `ε * R < h` bounding the box, a wall functional `ℓ`, end levels
`lam0 < lam1` and a finite set `exc` of critical levels such that the tilted sweep of the *open*
region `EpsFormSphere.openTiltedSweepRegion` starts at the box region (the `ℓ`-range conditions),
ends at the box region with the closed tilted slab removed, and satisfies the regularity, jump and
dichotomy fields.  Its four ingredients are the fleet's live workstreams: P1'
(`Work.Drive.EpsForm.tiltedSweepGenericity_holds`, H6-L226), P2' (the span constancy on a stretch,
i.e. the stratified transport recorded in
`EpsFormSphere/NOTES_H7_session7_refutation.md` §4), P3'
(`Work.Drive.EpsFormSphere.finrank_jump_of_discAttachment` plus the identification of a level change
with an attached disc) and P4' (`Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_slicing_of_countsWd`
plus the slicing of the level spheres and the level-local count
`Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`); the two endpoints are free
(`EpsFormSphere.openTiltedSweepRegion_eq_boxRegion`/`_eq_sdiff`).

The residual is *not* asserted here (that is the content of P2'-P4'); what this file proves is that
it **implies** Pardon's ε-form, through `solidEpsConclusion_of_tiltedSweepExists` and
`countingHalfEpsShifted_of_tiltedSweepExists`.  Note that this residual is phrased over the
*corrected* `Work.Drive.CleansDiscsWd`, so it is **not** one of the vacuous statements of §6. -/
def TiltedSweepExists : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∀ ε : ℝ, 0 < ε →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ ε ∧ 0 < h ∧ ε * R < h ∧
              (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
              (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
              (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
              (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
              (∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ ν < t) →
                Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ μ) =
                  Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) ∧
              (∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
                Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ μ)) ≤
                  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) + 1 ∧
                Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) ≤
                  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ μ)) + 1) ∧
              (∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ ν < t) →
                ∃ mu : ℝ, μ ≤ mu ∧ mu ≤ ν ∧ (∀ t ∈ exc, t ≠ mu) ∧
                  (Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                        (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ mu) = ⊥ ∨
                   Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
                        (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ mu) = ⊤))

/-- **The tilted sweep data give the solid ε-form.**  This is the *proved* assembly
`Work.Drive.EpsForm.epsConclusion_of_sweep_axioms`, fed by the crux's `HasEssBox` (which makes the
box region's winding span non-zero, hence — along the sweep — the end region's). -/
theorem solidEpsConclusion_of_tiltedSweepExists (h : TiltedSweepExists) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
      (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
      Work.Sweep.IsDistortionBound K d →
      Set.range K.curve = Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ →
      Submission.countConst * d < (Nat.min p q : ℝ) →
      Work.Drive.CleansDiscsWd (EpsSphere.torusOf ψ) →
      ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
        Submission.HasEssBox (EpsSphere.torusOf ψ) r c σ →
        ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
          Work.BoxShrink.SlicedSphere (EpsSphere.torusOf ψ)
              {y : R3 | Submission.boxNorm c σ y = s} →
          ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
              ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
            ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
                K.curve t ∈ Submission.PBox s c σ ∧
                (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
              ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∀ ε : ℝ, 0 < ε → SolidEpsConclusion (EpsSphere.torusOf ψ) s c σ u ε := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU ε hε
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hv, hh, hsize, hR, hlow, hhigh, hl, hexc, hreg, hjump,
    hone⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU ε hε
  -- the two endpoints of the sweep are free
  have hstart : EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam0 =
      Work.BoxShrink.Core.boxRegion (EpsSphere.torusOf ψ) s c σ :=
    EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow
  have hfinish : EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam1 =
      Work.BoxShrink.Core.boxRegion (EpsSphere.torusOf ψ) s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h :=
    EpsFormSphere.openTiltedSweepRegion_eq_sdiff hhigh
  -- the dichotomy at *every* regular level, from one level per regular stretch
  have hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
          (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
          (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤ :=
    dichotomy_every_level_of_one_per_stretch (V := fun lam =>
      Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
        (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam)) exc hexc hreg hone
  -- the span is constant along the sweep
  have hspan := Work.Drive.EpsFormSphere.span_const_of_sweep_axioms (EpsSphere.torusOf ψ)
    (fun lam : ℝ => EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam)
    lam0 lam1 exc hl hexc
    (fun μ ν hμν y hy =>
      ⟨hy.1, hy.2.1, fun hmem => hy.2.2 ⟨hmem.1, le_trans hmem.2 hμν⟩⟩)
    hreg hjump hdich
  have h0 : Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.boxRegion (EpsSphere.torusOf ψ) s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  -- an essential loop of the end region, hence off the (open) tilted slab
  have hne : Work.SurgeryInvariance.WindingSpan (EpsSphere.torusOf ψ)
      (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam1) ≠ ⊥ := by
    rw [← hspan, hstart]
    exact h0
  obtain ⟨γ, hess, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff
    (EpsSphere.torusOf ψ)
    (EpsFormSphere.openTiltedSweepRegion (EpsSphere.torusOf ψ) s c σ u v h ℓ lam1)).mp hne
  have hγ' : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (EpsSphere.torusOf ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlab (inner ℝ v c + u) v h := by
    intro t
    have h1 : γ t ∈ Work.BoxShrink.Core.boxRegion (EpsSphere.torusOf ψ) s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
      rw [← hfinish]; exact hγ t
    exact ⟨h1.1, fun hs => h1.2
      (Work.Drive.EpsForm.tiltedSlab_subset_tiltedSlabClosed _ _ _ hs)⟩
  exact Work.Drive.EpsForm.epsConclusion_of_essentialLoop_sdiff_tiltedSlab hε hv1 hv hR hsize
    hess hγ'

/-- **The solid ε-conclusion implies the shifted ε-form.**  If an essential loop `γ` has, at every
point, a witness `x` inside the box `PBox s c σ` on the correct side of the cutting plane at
distance `< ε`, then `γ` lies in the larger box `PBox (s + ε) c σ` (the box norm is `1`-Lipschitz in
the coordinate directions, and `1 ≤ boxSide i`) and on the same side of the plane shifted by `ε`.
This is the form `EpsSphere.hasEssBox_of_thickHalfShifted` consumes. -/
theorem thickHalfShifted_of_solidEpsConclusion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u ε : ℝ} (h : SolidEpsConclusion P s c σ u ε) :
    EpsSphere.ThickHalfShifted P s c σ u ε := by
  have hcoord : ∀ (y x : R3) (i : Fin 3),
      |y (σ i) - x (σ i)| ≤ dist y x := by
    intro y x i
    have h1 : (y - x) (σ i) = y (σ i) - x (σ i) := rfl
    rw [dist_eq_norm, ← h1]
    exact PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) (y - x) (σ i)
  have hbox : ∀ (y x : R3), x ∈ Submission.PBox s c σ → dist y x < ε →
      y ∈ Submission.PBox (s + ε) c σ := by
    intro y x hx hd
    rw [Submission.mem_PBox] at hx ⊢
    intro i
    have h1 : |y (σ i) - x (σ i)| < ε := lt_of_le_of_lt (hcoord y x i) hd
    have h2 : |y (σ i) - c (σ i)| ≤ |y (σ i) - x (σ i)| + |x (σ i) - c (σ i)| := by
      have h3 : y (σ i) - c (σ i) = (y (σ i) - x (σ i)) + (x (σ i) - c (σ i)) := by ring
      rw [h3]
      exact abs_add_le _ _
    have h4 := hx i
    have h5 : Submission.boxSide i * s + ε ≤ Submission.boxSide i * (s + ε) := by
      have hε0 : 0 ≤ ε := le_of_lt (lt_of_le_of_lt dist_nonneg hd)
      have hbs : 1 ≤ Submission.boxSide i := Submission.one_le_boxSide i
      nlinarith
    linarith
  rcases h with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · refine Or.inr ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨x, hxbox, hxlt, hd⟩ := hmem t
    have h2 := hcoord (γ t) x (2 : Fin 3)
    have h3 : γ t (σ 2) - x (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := le_abs_self _
    exact ⟨hbox (γ t) x hxbox hd, by linarith⟩
  · refine Or.inl ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨x, hxbox, hxgt, hd⟩ := hmem t
    have h2 := hcoord (γ t) x (2 : Fin 3)
    have h3 : x (σ 2) - γ t (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    exact ⟨hbox (γ t) x hxbox hd, by linarith⟩

/-- **The tilted sweep residual gives the shifted ε-form for the crux configurations**, hence (with
`EpsSphere.hasEssBox_of_thickHalfShifted`) the crux's box shrink. -/
theorem countingHalfEpsShifted_of_tiltedSweepExists (h : TiltedSweepExists) :
    EpsSphere.CountingHalfEpsShifted := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  exact thickHalfShifted_of_solidEpsConclusion
    (solidEpsConclusion_of_tiltedSweepExists h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr
      c σ hbox s hrs hs hslice u hu hS hU ε hε)

/-- **The crux's box shrink from the shifted ε-form** (the shifted analogue of `boxShrink_of_eps`,
closing through `EpsSphere.hasEssBox_of_thickHalfShifted`). -/
theorem boxShrink_of_epsShifted (hW : Work.Drive.CleansDiscsAllWd)
    (hE : EpsSphere.CountingHalfEpsShifted) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ hbox
  obtain ⟨s, hs, hslice, hS, u, hu, hU⟩ :=
    Work.BoxShrink.SweepNice.of_aeAll
      (Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis)
      p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ
  have hu' : |u| < Submission.eps * r := abs_lt.mpr hu
  have hmargin : 0 < Submission.shrinkFactor * r - (Submission.b * s + |u| / 2) :=
    EpsSphere.margin_pos hr hs.1 hs.2 hu'
  have hε₀pos : 0 < (Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8 := by
    linarith
  have hε₀8 : 8 * ((Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8)
      ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2) := by linarith
  have hhalf := hE p q hp hq hc ψ K d hd hbound himg hsmall
    (hW ψ) r hr c σ hbox
    s hs.1 hs.2 hslice u hu' hS hU
    ((Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8) hε₀pos
  exact EpsSphere.hasEssBox_of_thickHalfShifted hr hs.1 hu' hε₀pos hε₀8 hhalf

theorem pardon_of_boxShrinkShifted (hW : Work.Drive.CleansDiscsAllWd)
    (hE : EpsSphere.CountingHalfEpsShifted)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Submission.theorem_of_core
    (Submission.CoreStatement_of_boxShrink (boxShrink_of_epsShifted hW hE))
    p q hp hq hc K hclass

open LeanEval.KnotTheory.PardonDistortion in
open scoped ENNReal in
/-- **The challenge from Pardon's ε-form alone** — the honest ending of the deliverable.

The claused cut-and-paste input `Work.Drive.CleansDiscsAllWd` is *proved* in this workspace
(`Work.Drive.cleansDiscsAllWd`, axiom-clean), so the content of the deliverable, once the frozen
(and refuted, see `not_cleansDiscsAllW` below) hypothesis `Work.Drive.CleansDiscsAllW` is replaced by
the corrected one, is exactly Pardon's ε-form
`Work.Drive.EpsSphere.CountingHalfEpsSphere` (`doublebubble2` at the crux configurations) — the
fleet's live residual for field 2 (`Work.Drive.EpsForm.epsBodyResidual`, `…PlateSweepExists`, or the
tilted-sweep residual `TiltedSweepExists` of this file, discharged through
`countingHalfEpsShifted_of_tiltedSweepExists`). -/
theorem pardon_of_cleansWd_of_epsSphere (hE : EpsSphere.CountingHalfEpsSphere)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_of_cleansWd_sphere Work.Drive.cleansDiscsAllWd hE p q hp hq hc K hclass

/-! ## 7. The two endings of the deliverable

**Honest ending.**  `pardon_of_cleansWd_sphere` above (and `pardon_of_cleansWd_of_epsSphere` just
below) is the deliverable over the *corrected*, **proved** cut-and-paste input
`Work.Drive.CleansDiscsAllWd` (`Submission/Work/Drive/cleansDiscsAllWd.lean`); its only content is
Pardon's ε-form `Work.Drive.EpsSphere.CountingHalfEpsSphere`.  This is what the crux actually
consumes, and it is *not* vacuous.

**The frozen ending.**  The deliverable as requested has the hypothesis `hW :
Work.Drive.CleansDiscsAllW`, which is **refuted in this workspace** — machine-checked, axiom-clean,
by `not_cleansDiscsAllW` above (`EpsForm.exists_innermostDisc_essential_winding` +
`compressing_winding_dichotomyW`).  Every statement whose hypotheses contain the legacy
`CleansDiscsW` is therefore vacuously true; the fleet has taken the same step for the legacy residual
`Work.Drive.EpsForm.countingHalfEps_holds` (whose closing carries the same warning).  The proof below
is that vacuity proof, and it is the *only* correct proof of the frozen statement: the statement is
true, but its content is empty, and in particular it does **not** say that Pardon's bound follows
from the weak cut-and-paste input.  The honest replacement is the theorem just above. -/
theorem pardon_of_cleansW_sphere (hW : Work.Drive.CleansDiscsAllW)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  absurd hW not_cleansDiscsAllW

end

end Work.Drive
