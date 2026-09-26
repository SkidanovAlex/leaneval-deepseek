import Mathlib
import ChallengeDeps
import Submission.ChordFamily
import Submission.BandDisk
import Submission.Commons.Topology.AddCircle.coe_Icc_surjective

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-!
# Layer B, first half — the non-separating band arc sweeps the knot

**Context.**  `ChordFamily.lean` builds, from a band arc `d : BandArcData`
(two continuous endpoint-branch families `a s`, `b s` on the parameter
circle, collapsed at the two ends of `I` and distinct in the interior), the
chord-family disk `chordFamilyDisk r d : I × I → Space`, whose two
horizontal edges are the two branches and whose vertical edges are the
collapsed ends.  `BandDisk.lean` (`classBandArc_disk_bounds`) turns that
square into `PathsBoundDiskInteriorFree (range (knotMap r)) γ δ` whenever the
arc avoids the trisecant set `O` (interior of the disk avoids the knot).

**What was missing (Kuperberg §3, "Suppose that `A` is a non-separating arc
of `M` which avoids `O` … This family of secants induces a map `D` from the
unit disk to `ℝ³` whose boundary is `K`").**  Avoiding `O` only gives a disk
whose two boundary arcs are the two branches; for that boundary to *be* the
knot, the arc must be **non-separating** — the two branches must together
sweep every point of `K`.  This module fixes that notion and proves the
sweeping statement:

* **`BandArcNonSeparating d`** — the two branches admit continuous real lifts
  `ta`, `tb` with `ta 0 = tb 0` (the two branches meet at the left
  collapsed end) and `tb 1 = ta 1 + period` (after one traversal the second
  branch has gained exactly one knot period on the first).  Equivalently the
  boundary loop of the chord-family disk winds once around the knot.  The
  condition is choice-free (`∃`-form); the lifts are the `AddCircle period`
  covering lifts of the two branch paths.
* **`bandArcNonSeparating_covers`** — the two branches then cover the whole
  knot: `range (K ∘ a) ∪ range (K ∘ b) = range K`.  Proof: the range of each
  real lift is an interval (`IsPreconnected.ordConnected`); the first contains
  `ta 0` and `ta 1`, the second `tb 0 = ta 0` and `tb 1 = ta 1 + period`; the
  union therefore contains the full period window `Icc (ta 1) (ta 1 + period)`
  (case split on whether the point lies below or above `tb 0`), and every
  class in `AddCircle period` has a representative in that window
  (`AddCircle.eq_coe_Ico`).
* **`bandArc_spanningDisk`** — the combination with `bandArcDisk_bounds`: a
  non-separating band arc which avoids `O` yields two knot paths bounding a
  disk whose interior avoids the knot and whose two arcs together cover the
  knot — i.e. Kuperberg's "map from the unit disk whose boundary is `K`".
* **`NonSeparatingArcAvoidingO r`** (PIN, a `def Prop`) — the exact remaining
  content of brick (d): such an arc exists for a quadrisecant-free knot in
  general position (Kuperberg's "elementary homology theory" step, vacuous by
  the S280/S281 null-homotopy of every circular component of `O`).
* **`SpanningDisk_implies_IsUnknotted`** (PIN, a `def Prop`) — Layer B: the
  Dehn-lemma/Alexander-trick bridge from a spanning disk to `IsUnknotted`.

Everything proved here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-- **A non-separating band arc.**  The two endpoint branches of the band
arc admit continuous real lifts `ta`, `tb` over the traversal interval which
agree at the left collapsed end (`ta 0 = tb 0`) and differ by exactly one
knot `period` at the right collapsed end (`tb 1 = ta 1 + period`).  This is
the invariant meaning of Kuperberg's "non-separating arc of `M`": the two
branches together travel once around the knot, so the boundary loop of the
chord-family disk is a generator of `π₁` of the knot. -/
def BandArcNonSeparating (d : BandArcData) : Prop :=
  ∃ ta tb : I → ℝ, Continuous ta ∧ Continuous tb ∧
    (∀ s : I, (ta s : AddCircle period) = d.a s) ∧
    (∀ s : I, (tb s : AddCircle period) = d.b s) ∧
    ta 0 = tb 0 ∧ tb 1 = ta 1 + period

/-- **The non-separating band arc sweeps the whole knot.**  The two branches
of a non-separating band arc cover every point of the knot:
`range (K ∘ a) ∪ range (K ∘ b) = range K`. -/
theorem bandArcNonSeparating_covers {r : ℝ → Space} {d : BandArcData}
    (h : BandArcNonSeparating d) :
    Set.range (fun s : I => knotMap r (d.a s)) ∪
      Set.range (fun s : I => knotMap r (d.b s)) = Set.range (knotMap r) := by
  obtain ⟨ta, tb, hca, hcb, hma, hmb, h00, h11⟩ := h
  have hordA : (Set.range ta).OrdConnected := (isPreconnected_range hca).ordConnected
  have hordB : (Set.range tb).OrdConnected := (isPreconnected_range hcb).ordConnected
  have hXmem : ta 1 ∈ Set.range ta := ⟨1, rfl⟩
  have he0A : tb 0 ∈ Set.range ta := by rw [← h00]; exact ⟨0, rfl⟩
  have he0B : tb 0 ∈ Set.range tb := ⟨0, rfl⟩
  have hb1mem : ta 1 + period ∈ Set.range tb := by rw [← h11]; exact ⟨1, rfl⟩
  -- the union of the two real branch images contains a full period window
  have hwindow : Set.Icc (ta 1) (ta 1 + period) ⊆ Set.range ta ∪ Set.range tb := by
    intro u hu
    rw [Set.mem_union]
    rcases le_total u (tb 0) with huL | huR
    · exact Or.inl (hordA.out' hXmem he0A ⟨hu.1, huL⟩)
    · exact Or.inr (hordB.out' he0B hb1mem ⟨huR, hu.2⟩)
  apply Set.Subset.antisymm
  · rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact ⟨d.a s, rfl⟩
    · exact ⟨d.b s, rfl⟩
  · rintro x ⟨t, rfl⟩
    have hsurj := Commons.Topology.AddCircle.coe_Icc_surjective period (ta 1) period_pos
    have hmem' : t ∈ ((↑) : ℝ → AddCircle period) '' Set.Icc (ta 1) (ta 1 + period) := by
      rw [hsurj]; exact Set.mem_univ t
    simp only [Set.mem_image] at hmem'
    obtain ⟨y, hy, hyeq⟩ := hmem'
    have hmem := hwindow hy
    rw [Set.mem_union] at hmem
    rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨s, by
        have hcl : (d.a s : AddCircle period) = t := by rw [← hma s, ← hyeq, hs]
        show knotMap r (d.a s) = knotMap r t
        rw [hcl]⟩
    · exact Or.inr ⟨s, by
        have hcl : (d.b s : AddCircle period) = t := by rw [← hmb s, ← hyeq, hs]
        show knotMap r (d.b s) = knotMap r t
        rw [hcl]⟩

/-- **The spanning disk of a non-separating arc avoiding `O` (Layer B, first
half).**  A non-separating band arc whose interior avoids the trisecant set
`O` yields two knot paths `bandArcPathA`, `bandArcPathB` (the two branches)
which bound a disk whose interior avoids the knot
(`PathsBoundDiskInteriorFree`) and whose two arcs together cover the whole
knot (`range γ ∪ range δ = range K`) — Kuperberg's "map from the unit disk to
`ℝ³` whose boundary is `K` and whose interior does not intersect `K`". -/
theorem bandArc_spanningDisk {r : ℝ → Space} (h : IsSmoothKnot r) (d : BandArcData)
    (hns : BandArcNonSeparating d)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) :
    PathsBoundDiskInteriorFree (Set.range (knotMap r)) (bandArcPathA h d) (bandArcPathB h d) ∧
      Set.range (bandArcPathA h d) ∪ Set.range (bandArcPathB h d) = Set.range (knotMap r) := by
  have hcov := bandArcNonSeparating_covers (r := r) hns
  have hA : Set.range (bandArcPathA h d) = Set.range (fun s : I => knotMap r (d.a s)) :=
    congrArg Set.range (funext fun s => rfl)
  have hB : Set.range (bandArcPathB h d) = Set.range (fun s : I => knotMap r (d.b s)) :=
    congrArg Set.range (funext fun s => rfl)
  refine ⟨bandArcDisk_bounds h d havoid, ?_⟩
  rw [hA, hB]
  exact hcov

/-- **Brick (d) PIN — the avoidance existence.**  For a smooth knot in
general position with no quadrisecant there is a band arc which is
non-separating and avoids the trisecant set `O` at every interior parameter.
This is Kuperberg's §3 step "if `O` obstructs all non-separating arcs, there
is a circular component `C` of `O` which winds around `M` either one or two
times": S280/S281 show that every circular component of `O` is
null-homotopic, so no obstruction exists.  Stated as a `def Prop` (no
`sorry`) to record the exact remaining content of brick (d). -/
def NonSeparatingArcAvoidingO (r : ℝ → Space) : Prop :=
  ∃ d : BandArcData, BandArcNonSeparating d ∧
    ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r

/-- **Layer B PIN — the Dehn-lemma/Alexander-trick bridge.**  A smooth knot
whose two complementary knot arcs bound a disk with interior avoiding the
knot is unknotted.  This is the classical "a knot bounding a disk is
trivial" (Dehn's lemma / the Alexander–Schoenflies route to an explicit
smooth isotopy to `standardCircle`), the largest single missing piece of the
development.  Stated as a `def Prop` (no `sorry`). -/
def SpanningDisk_implies_IsUnknotted : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r →
    (∃ u v : AddCircle period, ∃ γ δ : Path (knotMap r u) (knotMap r v),
      PathsBoundDiskInteriorFree (Set.range (knotMap r)) γ δ ∧
        Set.range γ ∪ Set.range δ = Set.range (knotMap r)) →
    IsUnknotted r

/-- **The Layer-B conclusion from a single avoiding non-separating arc**
(modulo the pin).  Granting `SpanningDisk_implies_IsUnknotted`, a
non-separating band arc which avoids the trisecant set `O` makes the knot
unknotted: its two branches are the complementary knot arcs bounding the
interior-free spanning disk.  This is the exact shape in which the brick-(d)
avoidance statement `NonSeparatingArcAvoidingO` feeds Layer B. -/
theorem isUnknotted_of_nonSeparatingArc {r : ℝ → Space}
    (hpin : SpanningDisk_implies_IsUnknotted) (h : IsSmoothKnot r) (d : BandArcData)
    (hns : BandArcNonSeparating d)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) :
    IsUnknotted r := by
  obtain ⟨hdisk, hcov⟩ := bandArc_spanningDisk h d hns havoid
  exact hpin r h ⟨d.a 0, d.a 1, bandArcPathA h d, bandArcPathB h d, hdisk, hcov⟩

end LeanEval.KnotTheory.Quadrisecant
