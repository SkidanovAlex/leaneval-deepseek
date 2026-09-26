import Mathlib
import ChallengeDeps
import Submission.KnotMap
import Submission.Helpers
import Submission.QuadrisecantChord
import Submission.SecantSpace
import Submission.TrisecantLocus
import Submission.Commons.Topology.Covering.exists_liftOnIoo

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

/-!
# Layer A1 / Layer B interface — the chord-family disk over a band arc
(supporting object (1) of the D3 dependency list)

Kuperberg (Lemma 3 proof): let `A` be a properly embedded non-separating arc
of the Möbius band of secants avoiding the trisecant set `O`; *the family of
secants over `A` induces a map `D` from the unit disk to `R³` whose boundary
is `K` and whose interior does not intersect `K`* — the spanning disk to
which Dehn's lemma is applied.  This module pins the **precise statement**
of that construction:

1. **`BandArcData`** — what a band arc is, in the parameter-branch form: a
   continuous 1-parameter family of secant classes over the interval,
   described by its two ordered endpoint branches `a b : I → AddCircle
   period` (the unordered class `{a s, b s}` is the secant at time `s`).
   The two branches are continuous; at the two ends of the interval the
   chord collapses to single knot parameters (`collapse_left :
   a 0 = b 0`, `collapse_right : a 1 = b 1` — the two endpoints of the arc
   on the diagonal boundary of the band); in the interior the branches stay
   distinct (`offdiag` — the arc stays in the open band, off the diagonal).
2. **`chordFamilyDisk r d`** — what the chord family assigns: the map of the
   unit square `(s, t) ↦` the point at fraction `t` of the straight chord
   from `knotMap r (d.a s)` to `knotMap r (d.b s)` (the disk over the arc).
   Boundary conditions, proved: the `t = 0` and `t = 1` edges are the two
   endpoint branches of the arc on the knot (`chordFamilyDisk_t0/_t1`), the
   `s = 0` and `s = 1` edges are degenerate knot points
   (`chordFamilyDisk_s0/_s1`); so the boundary loop of the square is the
   knot itself.  The map is continuous (`continuous_chordFamilyDisk`).
   Interior condition, proved: every interior point of the disk lies
   *strictly inside* its chord (`chordFamilyDisk_mem_openSegment`), which is
   the mechanism by which "the arc avoids `O`" will yield "the interior
   avoids `K`" (a knot point on an interior disk point would be a strict
   middle point of its chord, i.e. the class would lie in `O`).

Nothing here depends on the arc avoiding `O` — that hypothesis belongs to
the corollary (interior of the disk avoids the knot), to be proved on top of
`chordFamilyDisk_mem_openSegment` + the trisecant vocabulary once the arc is
glued to `O`/`OPrime` (next step of supporting object (1)).  Everything here
is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- A **band arc** of the secant Möbius band: a 1-parameter family of secant
classes over the interval, described by its two ordered endpoint branches
`a s` and `b s` (the unordered class `{a s, b s}` is the secant at time `s`).
The branches are continuous; at the two ends of the interval the chord
collapses to the single knot parameters `a 0 = b 0` and `a 1 = b 1` (the
endpoints of the arc on the diagonal boundary of the band); in the interior
the two branches stay distinct (the arc stays in the open band, off the
diagonal). -/
structure BandArcData where
  a : I → AddCircle period
  b : I → AddCircle period
  cont_a : Continuous a
  cont_b : Continuous b
  collapse_left : a (0 : I) = b (0 : I)
  collapse_right : a (1 : I) = b (1 : I)
  offdiag : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → a s ≠ b s

/-- The **chord-family disk over the band arc** `d`: the map of the unit
square which at the secant parameter `s` sweeps the straight chord from
`knotMap r (d.a s)` to `knotMap r (d.b s)` as `t` runs over the interval.
The two horizontal edges (`t = 0` and `t = 1`) are the two endpoint branches
of the arc on the knot; the two vertical edges (`s = 0` and `s = 1`) are
degenerate (the chord has collapsed to the knot point at the arc's ends), so
the boundary loop of the square is the knot itself. -/
noncomputable def chordFamilyDisk (r : ℝ → Space) (d : BandArcData) : I × I → Space :=
  fun (s, t) => knotMap r (d.a s) + (t : ℝ) • (knotMap r (d.b s) - knotMap r (d.a s))

lemma continuous_chordFamilyDisk {r : ℝ → Space} (h : IsSmoothKnot r) (d : BandArcData) :
    Continuous (chordFamilyDisk r d) := by
  unfold chordFamilyDisk
  have hk : Continuous (knotMap r) := h.knotMap_continuous
  have hc1 : Continuous (fun p : I × I => knotMap r (d.a p.1)) := hk.comp (d.cont_a.comp continuous_fst)
  have hc2 : Continuous (fun p : I × I => knotMap r (d.b p.1)) := hk.comp (d.cont_b.comp continuous_fst)
  have hcv : Continuous (fun p : I × I => (p.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
  have hsub : Continuous (fun p : I × I => knotMap r (d.b p.1) - knotMap r (d.a p.1)) := hc2.sub hc1
  have hsl : Continuous (fun p : I × I => (p.2 : ℝ) • (knotMap r (d.b p.1) - knotMap r (d.a p.1))) := hcv.smul hsub
  exact hc1.add hsl

/-- The `t = 0` edge of the chord-family disk is the `a`-branch of the arc on
the knot. -/
lemma chordFamilyDisk_t0 {r : ℝ → Space} (d : BandArcData) (s : I) :
    chordFamilyDisk r d (s, (0 : I)) = knotMap r (d.a s) := by
  simp [chordFamilyDisk]

/-- The `t = 1` edge of the chord-family disk is the `b`-branch of the arc on
the knot. -/
lemma chordFamilyDisk_t1 {r : ℝ → Space} (d : BandArcData) (s : I) :
    chordFamilyDisk r d (s, (1 : I)) = knotMap r (d.b s) := by
  simp [chordFamilyDisk]

/-- The `s = 0` edge is degenerate: the chord has collapsed to the knot point
`knotMap r (d.a 0)` at the start of the arc. -/
lemma chordFamilyDisk_s0 {r : ℝ → Space} (d : BandArcData) (t : I) :
    chordFamilyDisk r d ((0 : I), t) = knotMap r (d.a (0 : I)) := by
  simp [chordFamilyDisk, d.collapse_left]

/-- The `s = 1` edge is degenerate: the chord has collapsed to the knot point
`knotMap r (d.a 1)` at the end of the arc. -/
lemma chordFamilyDisk_s1 {r : ℝ → Space} (d : BandArcData) (t : I) :
    chordFamilyDisk r d ((1 : I), t) = knotMap r (d.a (1 : I)) := by
  simp [chordFamilyDisk, d.collapse_right]

/-- **Interior points of the chord-family disk lie strictly inside their
chord.**  For an interior parameter `s` (off-diagonal class) and a strict
interior chord fraction `t ∈ (0,1)`, the disk point lies in the *open*
segment between the two knot endpoints of the chord.  (This is the reason an
arc avoiding the trisecant set `O` yields a disk whose interior avoids the
knot: every interior disk point would otherwise be a middle point of its
chord.) -/
lemma chordFamilyDisk_mem_openSegment {r : ℝ → Space} (d : BandArcData) {s t : I}
    (_hs0 : (s : ℝ) ≠ 0) (_hs1 : (s : ℝ) ≠ 1) (ht0 : (t : ℝ) ≠ 0) (ht1 : (t : ℝ) ≠ 1) :
    chordFamilyDisk r d (s, t) ∈ openSegment ℝ (knotMap r (d.a s)) (knotMap r (d.b s)) := by
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
  refine ⟨1 - (t : ℝ), (t : ℝ), ?_, htpos, ?_, ?_⟩
  · linarith
  · linarith
  · have hsum : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
    have h := smul_add_smul_eq_add_smul_sub (E := Space)
      (A := knotMap r (d.a s)) (B := knotMap r (d.b s)) (s := 1 - (t : ℝ)) (t := (t : ℝ)) hsum
    rw [h]
    rfl


/-! ## The `O`-avoidance corollary

Kuperberg's disk construction concludes: if the arc `A` avoids the trisecant
set `O`, the interior of the chord-family disk avoids the knot `K`.  The
mechanism (proved above) is that every interior disk point lies strictly
inside its chord; a knot point at such a disk point would therefore be a
*strict middle point* of the chord, i.e. the secant class of that interior
parameter would lie in `O`.  Contrapositively, avoiding `O` on every interior
class forces the interior of the disk off `K`:

* `not_HasMiddleOnClass_iff_no_middle_rep` — glue: "no strict middle point
  on the chord of the representative `p`" is exactly "the class
  `mobiusCover p` is not in `O`" (`HasMiddleOnClass_iff` + `not_congr`);
* **`chordFamilyDisk_interior_avoids_knot`** — the direct corollary (arc
  has no strict-middle class on any interior parameter);
* **`chordFamilyDisk_interior_avoids_knot_of_avoids_O`** — the
  `trisecantSet`/class-level phrasing (the arc avoids `O`).
-/

/-- Glue: a representative `p` of a secant class whose chord has **no strict
middle point** is exactly the class not belonging to `O` (`trisecantSet`). -/
lemma not_HasMiddleOnClass_iff_no_middle_rep {r : ℝ → Space} (p : OrderedPairs) :
    ¬ HasMiddleOnClass r (mobiusCover p) ↔
      ¬ ∃ m : AddCircle period, IsMiddleOnChord r p.1.1 p.1.2 m := by
  exact not_congr (HasMiddleOnClass_iff r p)

/-- **The interior of the chord-family disk avoids the knot (direct form).**
  If no interior secant class of the arc has a strict middle point, then no
  knot point lies at an interior point of the disk: an interior disk point
  lies strictly inside its chord
  (`chordFamilyDisk_mem_openSegment`), so a knot point there would be a
  strict middle of that chord, contradicting the avoidance hypothesis. -/
theorem chordFamilyDisk_interior_avoids_knot {r : ℝ → Space} (d : BandArcData)
    (havoid : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 →
      ¬ ∃ m : AddCircle period, IsMiddleOnChord r (d.a s) (d.b s) m) :
    ∀ (s t : I), (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → (t : ℝ) ≠ 0 → (t : ℝ) ≠ 1 →
      chordFamilyDisk r d (s, t) ∉ Set.range (knotMap r) := by
  intro s t hs0 hs1 ht0 ht1 hrange
  rcases hrange with ⟨m, hm⟩
  have hseg : knotMap r m ∈ openSegment ℝ (knotMap r (d.a s)) (knotMap r (d.b s)) := by
    simpa [hm] using chordFamilyDisk_mem_openSegment d hs0 hs1 ht0 ht1
  exact havoid s hs0 hs1 ⟨m, by simpa [IsMiddleOnChord] using hseg⟩

/-- **The interior of the chord-family disk avoids the knot (arc avoids
`O`).**  If the arc's secant classes (at every interior parameter) are not in
the trisecant set `O = trisecantSet r`, then no knot point lies at an
interior point of the disk.  (Kuperberg: the family of secants over an arc
`A` avoiding `O` induces a disk whose interior does not intersect `K`.) -/
theorem chordFamilyDisk_interior_avoids_knot_of_avoids_O {r : ℝ → Space} (d : BandArcData)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) :
    ∀ (s t : I), (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → (t : ℝ) ≠ 0 → (t : ℝ) ≠ 1 →
      chordFamilyDisk r d (s, t) ∉ Set.range (knotMap r) := by
  apply chordFamilyDisk_interior_avoids_knot d
  intro s hs0 hs1 hm
  have hcls : mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r :=
    havoid s hs0 hs1
  apply hcls
  change HasMiddleOnClass r (mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩)
  exact (HasMiddleOnClass_iff r ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩).2 hm
/-! ## The band arc of a `BandArcData` (interface glue)

The Layer-C dichotomy will supply a properly embedded non-separating arc of
the secant band avoiding `O`; the disk construction consumes `BandArcData`
(branch functions).  This section fixes the **band-level shape** and proves
the direction that is available now:

* `arcClosedClass d : I → UnordCirclePairs` — the unordered-class family
  `{a s, b s}` in the *closed* band (including the diagonal boundary),
  continuous (`continuous_arcClosedClass`);
* its ends lie on the diagonal boundary at the collapsed parameters
  (`arcClosedClass_zero`/`_one`, = `diagClass (d.a 0)` resp.
  `diagClass (d.a 1)`), and its interior classes are off the diagonal
  (`arcClosedClass_ne_diag`);
* `arcOpenClass d hs0 hs1 : OpenMobius` — the interior classes as elements
  of the *open* band (`arcOpenClass_val`: its value is `arcClosedClass`),
  the object that the `O`-avoidance vocabulary talks about;
* **`BandArcData.toBandArc`** and the provisional **`BandArc`** record (a
  continuous path in the closed band with diagonal endpoints and
  off-diagonal interior) — every `BandArcData` satisfies the band-arc
  obligations.

The *reverse* direction — producing the continuous branch functions `a b`
from a band arc — is the covering-lift glue over the interior
(`mobiusCover : OrderedPairs → OpenMobius` is a two-sheeted covering map,
`isCoveringMap_mobiusCover`) with the two branches collapsing to the
diagonal endpoints; it becomes provable when the Layer-C dichotomy fixes the
`BandArc` object it supplies (see ROADMAP D3 / supporting object (1)).
-/

/-- The class family over a band-arc datum: the unordered pair class
`{a s, b s}` in the closed band (including the diagonal boundary). -/
def arcClosedClass (d : BandArcData) : I → UnordCirclePairs :=
  fun s : I => (⟦(d.a s, d.b s)⟧ : UnordCirclePairs)

lemma continuous_arcClosedClass (d : BandArcData) : Continuous (arcClosedClass d) := by
  change Continuous (fun s : I => (⟦(d.a s, d.b s)⟧ : UnordCirclePairs))
  exact continuous_classOf.comp (d.cont_a.prodMk d.cont_b)

lemma arcClosedClass_zero (d : BandArcData) :
    arcClosedClass d (0 : I) = diagClass (d.a (0 : I)) := by
  simp [arcClosedClass, diagClass, d.collapse_left]

lemma arcClosedClass_one (d : BandArcData) :
    arcClosedClass d (1 : I) = diagClass (d.a (1 : I)) := by
  simp [arcClosedClass, diagClass, d.collapse_right]

lemma arcClosedClass_ne_diag {d : BandArcData} {s : I} (hs0 : (s : ℝ) ≠ 0)
    (hs1 : (s : ℝ) ≠ 1) (a : AddCircle period) : arcClosedClass d s ≠ diagClass a := by
  intro h
  have hp := (classOf_eq_diag_iff (d.a s, d.b s) a).mp h
  exact d.offdiag s hs0 hs1 (hp.1.trans hp.2.symm)

/-- The interior classes of a band-arc datum as elements of the open band. -/
noncomputable def arcOpenClass (d : BandArcData) {s : I} (hs0 : (s : ℝ) ≠ 0)
    (hs1 : (s : ℝ) ≠ 1) : OpenMobius :=
  mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩

lemma arcOpenClass_val (d : BandArcData) {s : I} (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1) :
    (arcOpenClass d hs0 hs1 : UnordCirclePairs) = arcClosedClass d s := by
  simp [arcOpenClass, arcClosedClass, mobiusCover, unordOfOrdered]

/-- A **properly embedded band arc** (provisional interface, fixed by the
Layer-C dichotomy): a continuous path in the closed band `UnordCirclePairs`
whose two endpoints lie on the diagonal boundary circle and whose interior
lies in the open band (off the diagonal).  The essential/non-separating
property and interior injectivity are Layer-C additions on top of this
record. -/
structure BandArc where
  toFun : I → UnordCirclePairs
  continuous_toFun : Continuous toFun
  end_left : ∃ u : AddCircle period, toFun (0 : I) = diagClass u
  end_right : ∃ v : AddCircle period, toFun (1 : I) = diagClass v
  interior_open : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 →
    ¬ ∃ a : AddCircle period, toFun s = diagClass a

/-- **Every `BandArcData` is a band arc**: its class family is continuous,
its ends are on the diagonal boundary (at the collapsed parameters
`d.a 0`, `d.a 1`), and its interior lies in the open band.  (The reverse
direction — producing the branch functions `a b` from a band arc — is the
covering-lift glue that Layer C's arc object will feed; it is documented as
future work at the end of this module.) -/
noncomputable def BandArcData.toBandArc (d : BandArcData) : BandArc where
  toFun := arcClosedClass d
  continuous_toFun := continuous_arcClosedClass d
  end_left := ⟨d.a (0 : I), arcClosedClass_zero d⟩
  end_right := ⟨d.a (1 : I), arcClosedClass_one d⟩
  interior_open := by
    intro s hs0 hs1
    rintro ⟨a, ha⟩
    exact (arcClosedClass_ne_diag (d := d) (s := s) hs0 hs1 a) ha




/-! ## Endpoint collapse: fibre geometry at the diagonal (step 3)

The reverse glue (`bandArc_lift`, see `Submission/Work/BandArcLift.lean`)
needs the chord coordinates of an interior lift to collapse to the diagonal
parameter as the class family approaches the diagonal boundary of the band.
That collapse is pure fibre geometry of the class map — independent of the
path-lifting lemma — and is proved here:

* `coords_mem_of_class_mem_image` — membership form: if the class `{x, y}`
  lies in the image of `W ×ˢ W` under the class map (a neighbourhood of
  `diagClass u` when `W ∋ u` is open), then both coordinates lie in `W`
  (two pairs with the same class are equal or swapped);
* `coords_tendsto_of_class_tendsto_diag` — filter form: if the class family
  `⟦(x z, y z)⟧` tends to `diagClass u` along a filter, then both coordinate
  families tend to `u` (the class map is open (`isOpenMap_unordClass`), so
  the image of `W ×ˢ W` is a neighbourhood of `diagClass u`);
* `coords_eq_of_class_eq_diag` — exactly-diagonal classes have collapsed
  coordinates (`classOf_eq_diag_iff`).

Step 3 of `bandArc_lift` instantiates these with the filter `𝓝[>] 0` (and
`𝓝[<] 1`) over the interior parameter.
-/

/-- **Fibre geometry at the diagonal (membership form).**  If the unordered
class `{x, y}` lies in the image of `W ×ˢ W` under the class map — a
neighbourhood of the diagonal class `diagClass u` when `W ∋ u` is open —
then both coordinates lie in `W`.  (Two pairs with the same class are equal
or swapped, so each coordinate of one is a coordinate of the other.) -/
lemma coords_mem_of_class_mem_image {W : Set (AddCircle period)} {x y : AddCircle period}
    (h : (⟦(x, y)⟧ : UnordCirclePairs) ∈
      (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W)) :
    x ∈ W ∧ y ∈ W := by
  rcases h with ⟨p, hp, hcl⟩
  have hp1 : p.1 ∈ W := hp.1
  have hp2 : p.2 ∈ W := hp.2
  have hrel : pairRel p (x, y) := (class_eq_iff p (x, y)).mp hcl
  rcases hrel with h | h
  · have hx : x = p.1 := (congrArg Prod.fst h).symm
    have hy : y = p.2 := (congrArg Prod.snd h).symm
    exact ⟨hx.symm ▸ hp1, hy.symm ▸ hp2⟩
  · have hx : x = p.2 := by simpa [pairFlip] using (congrArg Prod.fst h).symm
    have hy : y = p.1 := by simpa [pairFlip] using (congrArg Prod.snd h).symm
    exact ⟨hx.symm ▸ hp2, hy.symm ▸ hp1⟩

/-- **Endpoint collapse of the chord coordinates (filter form).**  If the
class family `⟦(x z, y z)⟧` tends to the diagonal class `diagClass u` along
a filter `F`, then both coordinate families tend to `u` along `F`.  (The
class map is open, so the image of `W ×ˢ W` under it is a neighbourhood of
`diagClass u` whenever `W` is an open neighbourhood of `u`, and the
membership form above forces the coordinates into `W`.) -/
lemma coords_tendsto_of_class_tendsto_diag {u : AddCircle period} {X : Type*}
    [TopologicalSpace X] {F : Filter X} {x y : X → AddCircle period}
    (hxy : Tendsto (fun z : X => (⟦(x z, y z)⟧ : UnordCirclePairs)) F (𝓝 (diagClass u))) :
    Tendsto x F (𝓝 u) ∧ Tendsto y F (𝓝 u) := by
  constructor
  · intro V hV
    rcases (mem_nhds_iff.mp hV) with ⟨W, hWV, hWo, huW⟩
    have hWW : IsOpen (W ×ˢ W) := hWo.prod hWo
    have hVopen : IsOpen
        ((fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W)) :=
      isOpenMap_unordClass (W ×ˢ W) hWW
    have hVmem : (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W) ∈
        𝓝 (diagClass u) := by
      refine IsOpen.mem_nhds hVopen ⟨(u, u), ⟨huW, huW⟩, ?_⟩
      simp [diagClass]
    have hev : ∀ᶠ z in F, (⟦(x z, y z)⟧ : UnordCirclePairs) ∈
        (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W) :=
      hxy hVmem
    exact hev.mono (fun z hz => hWV (coords_mem_of_class_mem_image hz).1)
  · intro V hV
    rcases (mem_nhds_iff.mp hV) with ⟨W, hWV, hWo, huW⟩
    have hWW : IsOpen (W ×ˢ W) := hWo.prod hWo
    have hVopen : IsOpen
        ((fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W)) :=
      isOpenMap_unordClass (W ×ˢ W) hWW
    have hVmem : (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W) ∈
        𝓝 (diagClass u) := by
      refine IsOpen.mem_nhds hVopen ⟨(u, u), ⟨huW, huW⟩, ?_⟩
      simp [diagClass]
    have hev : ∀ᶠ z in F, (⟦(x z, y z)⟧ : UnordCirclePairs) ∈
        (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' (W ×ˢ W) :=
      hxy hVmem
    exact hev.mono (fun z hz => hWV (coords_mem_of_class_mem_image hz).2)

/-- **Exactly-diagonal classes have collapsed coordinates**: if the class
`{x, y}` IS the diagonal class `diagClass u`, then `x = u = y`. -/
lemma coords_eq_of_class_eq_diag {u x y : AddCircle period}
    (h : (⟦(x, y)⟧ : UnordCirclePairs) = diagClass u) : x = u ∧ y = u := by
  exact (classOf_eq_diag_iff (x, y) u).mp h



/-! ## Endpoint collapse of an interior lift (step 4a)

`bandArc_lift`'s step 4 extends the interior lift to the closed interval.
The geometric half of that extension — the collapse limits — is proved here
standalone (independent of the path-lifting lemma): given continuous
class-agreement of an interior lift `a₀ b₀` with the band arc `A`
(`⟦(a₀ s, b₀ s)⟧ = A s.1` on `ParamInterior`), continuity of `A`, and the
diagonal end values, the coordinates collapse to the diagonal parameter as
the interior parameter approaches each end:

* `interiorLift_coords_tendsto_left` — `Tendsto a₀ interiorFilterLeft (𝓝 u)`
  and the same for `b₀` (where `interiorFilterLeft` is the filter of
  interior parameters approaching `0`, expressed through the *subspace*
  neighbourhoods of `0 : I`, which are automatically one-sided);
* `interiorLift_coords_tendsto_right` — the same at the right end with `v`.

Proof: the class family equals `A ∘ val` on the interior, so it tends to
`diagClass u` / `diagClass v` by continuity of `A` at the ends; the fibre
geometry of step 3 (`coords_tendsto_of_class_tendsto_diag`) transfers that
to the coordinates.  Step 4b (extending continuous functions on the interior
with these endpoint limits to continuous functions on `I`) and step 5
(`BandArcData` assembly) build on these.
-/

/-- The interior of the parameter interval: times strictly between the two
ends of the band arc. -/
abbrev ParamInterior : Type := {s : I // (s : ℝ) ≠ 0 ∧ (s : ℝ) ≠ 1}

/-- The filter of interior parameters approaching the left end `0` (in the
subspace `I`, whose neighbourhoods at `0` are automatically one-sided). -/
abbrev interiorFilterLeft : Filter ParamInterior :=
  Filter.comap (fun s : ParamInterior => (s.1 : I)) (𝓝 (0 : I))

/-- The filter of interior parameters approaching the right end `1`. -/
abbrev interiorFilterRight : Filter ParamInterior :=
  Filter.comap (fun s : ParamInterior => (s.1 : I)) (𝓝 (1 : I))

/-- **Collapse of interior-lift coordinates at the left end (step 4a).**
  Let `a₀ b₀` lift the interior of the band arc `A` (their class equals
  `A` at every interior parameter).  As the interior parameter approaches
  the left end, the class family approaches the diagonal class `diagClass u`
  (continuity of `A` at `0`, `A 0 = diagClass u`), so by the fibre geometry
  of step 3 both coordinates collapse to `u`. -/
theorem interiorLift_coords_tendsto_left {u : AddCircle period} {A : I → UnordCirclePairs}
    (hA : Continuous A) (h0 : A (0 : I) = diagClass u)
    (a₀ b₀ : ParamInterior → AddCircle period)
    (hclass : ∀ s : ParamInterior, (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs) = A s.1) :
    Tendsto a₀ interiorFilterLeft (𝓝 u) ∧ Tendsto b₀ interiorFilterLeft (𝓝 u) := by
  have hAval : Tendsto (fun s : ParamInterior => A s.1) interiorFilterLeft (𝓝 (diagClass u)) := by
    have ht : Tendsto (fun s : ParamInterior => A s.1) interiorFilterLeft (𝓝 (A (0 : I))) := by
      dsimp [interiorFilterLeft]
      exact (hA.tendsto (0 : I)).comp tendsto_comap
    simpa [h0] using ht
  have heq : (fun s : ParamInterior => (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs)) =
      fun s : ParamInterior => A s.1 := funext hclass
  have hcls : Tendsto (fun s : ParamInterior => (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs))
      interiorFilterLeft (𝓝 (diagClass u)) := by
    rw [heq]
    exact hAval
  exact coords_tendsto_of_class_tendsto_diag (u := u) (X := ParamInterior)
    (F := interiorFilterLeft) (x := a₀) (y := b₀) hcls

/-- **Collapse of interior-lift coordinates at the right end (step 4a).**
  Symmetric: the coordinates collapse to `v` as the interior parameter
  approaches the right end (`A 1 = diagClass v`). -/
theorem interiorLift_coords_tendsto_right {v : AddCircle period} {A : I → UnordCirclePairs}
    (hA : Continuous A) (h1 : A (1 : I) = diagClass v)
    (a₀ b₀ : ParamInterior → AddCircle period)
    (hclass : ∀ s : ParamInterior, (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs) = A s.1) :
    Tendsto a₀ interiorFilterRight (𝓝 v) ∧ Tendsto b₀ interiorFilterRight (𝓝 v) := by
  have hAval : Tendsto (fun s : ParamInterior => A s.1) interiorFilterRight (𝓝 (diagClass v)) := by
    have ht : Tendsto (fun s : ParamInterior => A s.1) interiorFilterRight (𝓝 (A (1 : I))) := by
      dsimp [interiorFilterRight]
      exact (hA.tendsto (1 : I)).comp tendsto_comap
    simpa [h1] using ht
  have heq : (fun s : ParamInterior => (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs)) =
      fun s : ParamInterior => A s.1 := funext hclass
  have hcls : Tendsto (fun s : ParamInterior => (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs))
      interiorFilterRight (𝓝 (diagClass v)) := by
    rw [heq]
    exact hAval
  exact coords_tendsto_of_class_tendsto_diag (u := v) (X := ParamInterior)
    (F := interiorFilterRight) (x := a₀) (y := b₀) hcls

/-! ## Step 4b: closed-interval extension (step 4b)

Step 4a gave the endpoint limits of the interior coordinates.  Step 4b
finishes the analytic half of step 4 of `bandArc_lift`: a continuous
interior function `f : ParamInterior → AddCircle period` with endpoint
limits `u` (left) and `v` (right) extends to a continuous function
`extendInterior u v f : I → AddCircle period` on the whole closed interval.

* `ParamInteriorSet` — the interior as an open subset of `I`;
* `extendInterior` — `f` on the interior, `u` at `0`, `v` at `1`;
* `continuous_extendInterior` — continuity given the endpoint limits in
  explicit neighbourhood form;
* `continuous_extendInterior_of_tendsto` — the same from the `Tendsto`
  form of the limits along `interiorFilterLeft`/`interiorFilterRight`
  (the shape produced by step 4a's `interiorLift_coords_tendsto_*`).

The proof of continuity at an interior point transfers continuity of `f`
through the open interior; at the endpoints one uses the limit
neighbourhood together with a one-sided neighbourhood inside `I` (`< 1`
near `0`, `> 0` near `1`) to force every nearby point either to be the
endpoint itself or to lie in the interior where `f` applies.
-/


/-- The interior of the parameter interval as a subset of `I` (open). -/
def ParamInteriorSet : Set I := {t : I | (t : ℝ) ≠ 0 ∧ (t : ℝ) ≠ 1}

lemma isOpen_ParamInteriorSet : IsOpen (ParamInteriorSet : Set I) := by
  rw [ParamInteriorSet]
  have hset : {t : I | (t : ℝ) ≠ 0 ∧ (t : ℝ) ≠ 1} =
      ({t : I | t ≠ (0 : I)} ∩ {t : I | t ≠ (1 : I)}) := by
    ext t
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨(by intro ht; apply h0; exact congrArg (fun z : I => (z : ℝ)) ht),
        (by intro ht; apply h1; exact congrArg (fun z : I => (z : ℝ)) ht)⟩
    · rintro ⟨h0, h1⟩
      exact ⟨(by intro hz; apply h0; apply Subtype.ext; exact hz),
        (by intro hz; apply h1; apply Subtype.ext; exact hz)⟩
  rw [hset]
  exact (isClosed_singleton (x := (0 : I))).isOpen_compl.inter
    (isClosed_singleton (x := (1 : I))).isOpen_compl

lemma mem_ParamInteriorSet_iff (t : I) :
    t ∈ ParamInteriorSet ↔ (t : ℝ) ≠ 0 ∧ (t : ℝ) ≠ 1 := by
  rfl

/-- Extending a continuous interior function by its endpoint limits. -/
noncomputable def extendInterior (u v : AddCircle period)
    (f : ParamInterior → AddCircle period) : I → AddCircle period :=
  fun t => if h0 : (t : ℝ) = 0 then u
    else if h1 : (t : ℝ) = 1 then v
    else f ⟨t, ⟨h0, h1⟩⟩

lemma extendInterior_zero (u v : AddCircle period) (f : ParamInterior → AddCircle period) :
    extendInterior u v f (0 : I) = u := by
  simp [extendInterior]

lemma extendInterior_one (u v : AddCircle period) (f : ParamInterior → AddCircle period) :
    extendInterior u v f (1 : I) = v := by
  simp [extendInterior]

lemma extendInterior_eq_on_interior (u v : AddCircle period)
    (f : ParamInterior → AddCircle period) {t : I} (h0 : (t : ℝ) ≠ 0) (h1 : (t : ℝ) ≠ 1) :
    extendInterior u v f t = f ⟨t, ⟨h0, h1⟩⟩ := by
  simp [extendInterior, h0, h1]

/-- Continuity at an interior point: on the open interior `g` agrees with
`f`, so continuity transfers from `f`. -/
lemma continuousAt_extendInterior_at_interior {u v : AddCircle period}
    {f : ParamInterior → AddCircle period} (hf : Continuous f) {t : I}
    (ht0 : (t : ℝ) ≠ 0) (ht1 : (t : ℝ) ≠ 1) :
    ContinuousAt (extendInterior u v f) t := by
  intro W hW
  rw [Filter.mem_map]
  rcases (mem_nhds_iff.mp hW) with ⟨W₀, hW₀W, hW₀o, hgt⟩
  have hfW₀ : f ⟨t, ⟨ht0, ht1⟩⟩ ∈ W₀ := by
    simpa [extendInterior_eq_on_interior u v f ht0 ht1] using hgt
  have hS : {q : ParamInterior | f q ∈ W₀} ∈ 𝓝 (⟨t, ⟨ht0, ht1⟩⟩ : ParamInterior) :=
    hf.continuousAt (IsOpen.mem_nhds hW₀o hfW₀)
  have htPS : t ∈ ParamInteriorSet := (mem_ParamInteriorSet_iff t).2 ⟨ht0, ht1⟩
  have himg : ((↑) : ParamInterior → I) '' {q : ParamInterior | f q ∈ W₀} ∈ 𝓝 t := by
    have himg' : ((↑) : ParamInterior → I) '' {q : ParamInterior | f q ∈ W₀} ∈
        𝓝[ParamInteriorSet] t :=
      (mem_nhds_subtype_iff_nhdsWithin (s := ParamInteriorSet)
        (a := ⟨t, htPS⟩) (t := {q : ParamInterior | f q ∈ W₀})).mp hS
    simpa [IsOpen.nhdsWithin_eq isOpen_ParamInteriorSet htPS] using himg'
  refine mem_of_superset himg ?_
  intro x hx
  rcases hx with ⟨q, hq, hxq⟩
  have hx0 : (x : ℝ) ≠ 0 := by
    simpa [hxq] using (q.2.1 : ((q : I) : ℝ) ≠ 0)
  have hx1 : (x : ℝ) ≠ 1 := by
    simpa [hxq] using (q.2.2 : ((q : I) : ℝ) ≠ 1)
  have hxeq : (⟨x, ⟨hx0, hx1⟩⟩ : ParamInterior) = q := by
    apply Subtype.ext
    exact hxq.symm
  have : extendInterior u v f x ∈ W₀ := by
    rw [extendInterior_eq_on_interior u v f hx0 hx1]
    simpa [hxeq] using hq
  exact hW₀W this

/-- Continuity of the extension at the left end, given the left-limit in
neighbourhood form. -/
lemma continuousAt_extendInterior_at_zero {u v : AddCircle period}
    {f : ParamInterior → AddCircle period}
    (hleft : ∀ W ∈ 𝓝 u, ∃ V ∈ 𝓝 (0 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W) :
    ContinuousAt (extendInterior u v f) (0 : I) := by
  intro W hW
  rw [Filter.mem_map]
  rcases (mem_nhds_iff.mp hW) with ⟨W₀, hW₀W, hW₀o, huW₀⟩
  have hu' : u ∈ W₀ := by simpa [extendInterior_zero] using huW₀
  rcases hleft W₀ (IsOpen.mem_nhds hW₀o hu') with ⟨V, hV, hVp⟩
  have hsmall : {x : I | (x : ℝ) < 1} ∈ 𝓝 (0 : I) := by
    refine IsOpen.mem_nhds (isOpen_Iio.preimage continuous_subtype_val) ?_
    simp
  refine mem_of_superset (Filter.inter_mem hV hsmall) ?_
  intro x hx
  by_cases hx0 : x = (0 : I)
  · exact hW₀W (by simpa [hx0, extendInterior] using huW₀)
  · have hval0 : (x : ℝ) ≠ 0 := by
      intro hz
      apply hx0
      apply Subtype.ext
      exact hz
    have hval1 : (x : ℝ) ≠ 1 := by
      intro hz
      have hlt : (x : ℝ) < 1 := by simpa using hx.2
      linarith
    have hfx : f ⟨x, ⟨hval0, hval1⟩⟩ ∈ W₀ := hVp x hval0 hval1 hx.1
    exact hW₀W (by simpa [extendInterior_eq_on_interior u v f hval0 hval1] using hfx)

/-- Continuity of the extension at the right end, given the right-limit in
neighbourhood form. -/
lemma continuousAt_extendInterior_at_one {u v : AddCircle period}
    {f : ParamInterior → AddCircle period}
    (hright : ∀ W ∈ 𝓝 v, ∃ V ∈ 𝓝 (1 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W) :
    ContinuousAt (extendInterior u v f) (1 : I) := by
  intro W hW
  rw [Filter.mem_map]
  rcases (mem_nhds_iff.mp hW) with ⟨W₀, hW₀W, hW₀o, hvW₀⟩
  have hv' : v ∈ W₀ := by simpa [extendInterior_one] using hvW₀
  rcases hright W₀ (IsOpen.mem_nhds hW₀o hv') with ⟨V, hV, hVp⟩
  have hsmall : {x : I | 0 < (x : ℝ)} ∈ 𝓝 (1 : I) := by
    refine IsOpen.mem_nhds (isOpen_Ioi.preimage continuous_subtype_val) ?_
    simp
  refine mem_of_superset (Filter.inter_mem hV hsmall) ?_
  intro x hx
  by_cases hx1 : x = (1 : I)
  · exact hW₀W (by simpa [hx1, extendInterior] using hvW₀)
  · have hval0 : (x : ℝ) ≠ 0 := by
      intro hz
      have hpos : 0 < (x : ℝ) := by simpa using hx.2
      linarith
    have hval1 : (x : ℝ) ≠ 1 := by
      intro hz
      apply hx1
      apply Subtype.ext
      exact hz
    have hfx : f ⟨x, ⟨hval0, hval1⟩⟩ ∈ W₀ := hVp x hval0 hval1 hx.1
    exact hW₀W (by simpa [extendInterior_eq_on_interior u v f hval0 hval1] using hfx)

/-- **Step 4b: a continuous interior function with the two endpoint limits
extends to a continuous function on all of `I`.** -/
theorem continuous_extendInterior {u v : AddCircle period}
    {f : ParamInterior → AddCircle period} (hf : Continuous f)
    (hleft : ∀ W ∈ 𝓝 u, ∃ V ∈ 𝓝 (0 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W)
    (hright : ∀ W ∈ 𝓝 v, ∃ V ∈ 𝓝 (1 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W) :
    Continuous (extendInterior u v f) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht0 : t = (0 : I)
  · subst ht0
    exact continuousAt_extendInterior_at_zero hleft
  · by_cases ht1 : t = (1 : I)
    · subst ht1
      exact continuousAt_extendInterior_at_one hright
    · have hval0 : (t : ℝ) ≠ 0 := by
        intro hz
        apply ht0
        apply Subtype.ext
        exact hz
      have hval1 : (t : ℝ) ≠ 1 := by
        intro hz
        apply ht1
        apply Subtype.ext
        exact hz
      exact continuousAt_extendInterior_at_interior hf hval0 hval1

/-- The neighbourhood-form conversion of the left-limit `Tendsto` along
`interiorFilterLeft`. -/
lemma tendsto_left_neighbourhood_form {u : AddCircle period}
    {f : ParamInterior → AddCircle period}
    (hleft : Tendsto f interiorFilterLeft (𝓝 u)) :
    ∀ W ∈ 𝓝 u, ∃ V ∈ 𝓝 (0 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W := by
  intro W hW
  have hmem : {s : ParamInterior | f s ∈ W} ∈ interiorFilterLeft := hleft hW
  rcases (Filter.mem_comap).mp hmem with ⟨V, hV, hVs⟩
  refine ⟨V, hV, ?_⟩
  intro x hx0 hx1 hxV
  have hmem' : (⟨x, ⟨hx0, hx1⟩⟩ : ParamInterior) ∈
      (fun s : ParamInterior => (s : I)) ⁻¹' V := by
    simpa using hxV
  exact hVs hmem'

/-- The neighbourhood-form conversion of the right-limit `Tendsto` along
`interiorFilterRight`. -/
lemma tendsto_right_neighbourhood_form {v : AddCircle period}
    {f : ParamInterior → AddCircle period}
    (hright : Tendsto f interiorFilterRight (𝓝 v)) :
    ∀ W ∈ 𝓝 v, ∃ V ∈ 𝓝 (1 : I), ∀ x : I, ∀ hx0 : (x : ℝ) ≠ 0,
      ∀ hx1 : (x : ℝ) ≠ 1, x ∈ V → f ⟨x, ⟨hx0, hx1⟩⟩ ∈ W := by
  intro W hW
  have hmem : {s : ParamInterior | f s ∈ W} ∈ interiorFilterRight := hright hW
  rcases (Filter.mem_comap).mp hmem with ⟨V, hV, hVs⟩
  refine ⟨V, hV, ?_⟩
  intro x hx0 hx1 hxV
  have hmem' : (⟨x, ⟨hx0, hx1⟩⟩ : ParamInterior) ∈
      (fun s : ParamInterior => (s : I)) ⁻¹' V := by
    simpa using hxV
  exact hVs hmem'

/-- **Step 4b (interface form): extension theorem for the `bandArc_lift`
interior lift.** -/
theorem continuous_extendInterior_of_tendsto {u v : AddCircle period}
    {f : ParamInterior → AddCircle period} (hf : Continuous f)
    (hleft : Tendsto f interiorFilterLeft (𝓝 u))
    (hright : Tendsto f interiorFilterRight (𝓝 v)) :
    Continuous (extendInterior u v f) :=
  continuous_extendInterior hf (tendsto_left_neighbourhood_form hleft)
    (tendsto_right_neighbourhood_form hright)

/-! ## Band-arc lifting: `BandArcData` from a class family (step 5)

The converse of `BandArcData.toBandArc` (S75): every class family `A` of a
band arc — continuous on the closed band, diagonal at the ends `u`,`v`, and
off-diagonal on the interior — admits the continuous branch functions of a
`BandArcData` realising `A`:

* `paramInteriorToIoo` — the re-embedding of the interior of the parameter
  interval into the open unit interval `(0,1)` of `ℝ` (continuous); the
  generic covering path-lift `Commons.Topology.Covering.exists_liftOnIoo`
  is stated over `(0,1) ⊆ ℝ`, while the collapse filters and extensions of
  steps 4a/4b live on `ParamInterior`, so the lift is transported through
  this homeomorphism;
* `openUnitClass A hopen` — the restriction of `A` to `(0,1)` as a
  continuous family of classes in the *open* Möbius band;
* `exists_lift_branch_family` — via the covering map `mobiusCover` and the
  fleet lift lemma, continuous interior branch functions `a₀ b₀` with
  `⟦(a₀ s, b₀ s)⟧ = A s` on the interior (distinct there);
* **`bandArc_lift`** — the closed-interval assembly: extend the interior
  branches with the endpoint values `u`,`v` (`extendInterior`, continuous
  by step 4b using the step-4a collapse limits `interiorLift_coords_tendsto_*`),
  and package the resulting `BandArcData` (endpoint values `u`,`v`, off-
  diagonal interior, closed class family `= A`).

Together with `BandArcData.toBandArc`, `BandArc` and `BandArcData` are now
mutually inverse interface objects: the Layer-C dichotomy may supply either
the record or the branch functions.
-/


/-- Re-embed the interior of the parameter interval into the open unit
interval of `ℝ` (identifies `ParamInterior` with `(0,1)`). -/
def paramInteriorToIoo (s : ParamInterior) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(s.1 : ℝ), ⟨lt_of_le_of_ne s.1.2.1 (Ne.symm s.2.1), lt_of_le_of_ne s.1.2.2 s.2.2⟩⟩

lemma continuous_paramInteriorToIoo : Continuous paramInteriorToIoo := by
  unfold paramInteriorToIoo
  refine Continuous.subtype_mk ?_ ?_
  exact (continuous_subtype_val : Continuous (fun t : I => (t : ℝ))).comp
    (continuous_subtype_val : Continuous (fun s : ParamInterior => (s.1 : I)))

/-- The class family over the open unit interval, viewed inside the open
Möbius band (the restriction of the band arc to the interior). -/
def openUnitClass (A : I → UnordCirclePairs)
    (hopen : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → ¬ ∃ a : AddCircle period, A s = diagClass a) :
    Set.Ioo (0 : ℝ) 1 → OpenMobius := fun t =>
  ⟨A ⟨(t : ℝ), ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩,
    hopen ⟨(t : ℝ), ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ (ne_of_gt t.2.1) (ne_of_lt t.2.2)⟩

lemma continuous_openUnitClass (A : I → UnordCirclePairs) (hA : Continuous A)
    (hopen : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → ¬ ∃ a : AddCircle period, A s = diagClass a) :
    Continuous (openUnitClass A hopen) := by
  unfold openUnitClass
  refine Continuous.subtype_mk ?_ ?_
  have htoI : Continuous (fun t : Set.Ioo (0 : ℝ) 1 =>
      (⟨(t : ℝ), ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ : I)) := by
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val
  exact hA.comp htoI

/-- **Interior lift of a band arc (converse glue, steps 1–2).**  Given a
continuous class family `A` on the closed band that stays in the open band
on the interior, the double cover `mobiusCover` gives continuous branch
functions `a₀ b₀` on the interior realising the class family, necessarily
distinct there. -/
lemma exists_lift_branch_family {A : I → UnordCirclePairs} (hA : Continuous A)
    (hopen : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → ¬ ∃ a : AddCircle period, A s = diagClass a) :
    ∃ a₀ b₀ : ParamInterior → AddCircle period,
      Continuous a₀ ∧ Continuous b₀ ∧
      (∀ s : ParamInterior, (⟦(a₀ s, b₀ s)⟧ : UnordCirclePairs) = A s.1) ∧
      (∀ s : ParamInterior, a₀ s ≠ b₀ s) := by
  let Aioo := openUnitClass A hopen
  have hAioo : Continuous Aioo := continuous_openUnitClass A hA hopen
  let t₀ : Set.Ioo (0 : ℝ) 1 := ⟨(1 : ℝ) / 2, by norm_num⟩
  rcases mobiusCover_surjective (Aioo t₀) with ⟨x₀, hx₀⟩
  rcases Commons.Topology.Covering.exists_liftOnIoo (E := OrderedPairs) (X := OpenMobius)
      (p := mobiusCover) isCoveringMap_mobiusCover (t₀ := t₀) (x₀ := x₀) (γ := ⟨Aioo, hAioo⟩) hx₀
    with ⟨G, hGlift, hGt₀⟩
  let F : ParamInterior → OrderedPairs := fun s => G (paramInteriorToIoo s)
  have hF : Continuous F := G.continuous.comp continuous_paramInteriorToIoo
  let a₀ : ParamInterior → AddCircle period := fun s => (F s).1.1
  let b₀ : ParamInterior → AddCircle period := fun s => (F s).1.2
  have hp1 : Continuous (fun q : OrderedPairs => q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hp2 : Continuous (fun q : OrderedPairs => q.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have ha₀ : Continuous a₀ := by
    change Continuous (fun s : ParamInterior => (G (paramInteriorToIoo s)).1.1)
    simpa only [Function.comp_def] using hp1.comp hF
  have hb₀ : Continuous b₀ := by
    change Continuous (fun s : ParamInterior => (G (paramInteriorToIoo s)).1.2)
    simpa only [Function.comp_def] using hp2.comp hF
  refine ⟨a₀, b₀, ha₀, hb₀, ?hcls, ?hne⟩
  · intro s
    let t := paramInteriorToIoo s
    have h1 := congrArg (fun z : OpenMobius => (z : UnordCirclePairs)) (hGlift t)
    have hId : (⟨(t : ℝ), ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ : I) = s.1 := by
      apply Subtype.ext
      rfl
    simpa [a₀, b₀, F, t, Aioo, openUnitClass, mobiusCover, unordOfOrdered, hId] using h1
  · intro s
    let t := paramInteriorToIoo s
    simpa [a₀, b₀, F, t] using (G t).2


/-- **Every band arc lifts to continuous branch functions (steps 3–5).**
  Given the class family `A` of a band arc (continuous, diagonal at the two
  ends `u`,`v`, off-diagonal on the interior), there is a `BandArcData` with
  endpoint values `u`, `v` and whose closed class family is exactly `A`.  -/
theorem bandArc_lift {u v : AddCircle period} {A : I → UnordCirclePairs}
    (hA : Continuous A)
    (h0 : A (0 : I) = diagClass u) (h1 : A (1 : I) = diagClass v)
    (hopen : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → ¬ ∃ a : AddCircle period, A s = diagClass a) :
    ∃ d : BandArcData,
      d.a (0 : I) = u ∧ d.b (0 : I) = u ∧ d.a (1 : I) = v ∧ d.b (1 : I) = v ∧
        ∀ s : I, arcClosedClass d s = A s := by
  rcases exists_lift_branch_family (A := A) hA hopen with ⟨a₀, b₀, ha₀c, hb₀c, hcls, hne⟩
  have hlimL := interiorLift_coords_tendsto_left (u := u) (A := A) hA h0 a₀ b₀ hcls
  have hlimR := interiorLift_coords_tendsto_right (v := v) (A := A) hA h1 a₀ b₀ hcls
  let α : I → AddCircle period := extendInterior u v a₀
  let β : I → AddCircle period := extendInterior u v b₀
  have hcα : Continuous α := by
    simpa [α] using continuous_extendInterior_of_tendsto (u := u) (v := v) (f := a₀) ha₀c hlimL.1 hlimR.1
  have hcβ : Continuous β := by
    simpa [β] using continuous_extendInterior_of_tendsto (u := u) (v := v) (f := b₀) hb₀c hlimL.2 hlimR.2
  have hα0 : α (0 : I) = u := by simpa [α] using extendInterior_zero u v a₀
  have hβ0 : β (0 : I) = u := by simpa [β] using extendInterior_zero u v b₀
  have hα1 : α (1 : I) = v := by simpa [α] using extendInterior_one u v a₀
  have hβ1 : β (1 : I) = v := by simpa [β] using extendInterior_one u v b₀
  have hoff : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → α s ≠ β s := by
    intro s hs0 hs1
    have hαs : α s = a₀ ⟨s, ⟨hs0, hs1⟩⟩ := extendInterior_eq_on_interior u v a₀ hs0 hs1
    have hβs : β s = b₀ ⟨s, ⟨hs0, hs1⟩⟩ := extendInterior_eq_on_interior u v b₀ hs0 hs1
    intro h
    have h' : a₀ ⟨s, ⟨hs0, hs1⟩⟩ = b₀ ⟨s, ⟨hs0, hs1⟩⟩ := hαs.symm.trans (h.trans hβs)
    exact hne ⟨s, ⟨hs0, hs1⟩⟩ h'
  let d : BandArcData :=
    { a := α, b := β, cont_a := hcα, cont_b := hcβ,
      collapse_left := hα0.trans hβ0.symm, collapse_right := hα1.trans hβ1.symm,
      offdiag := hoff }
  refine ⟨d, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [d, α] using extendInterior_zero u v a₀
  · simpa [d, β] using extendInterior_zero u v b₀
  · simpa [d, α] using extendInterior_one u v a₀
  · simpa [d, β] using extendInterior_one u v b₀
  · intro s
    by_cases hs0 : (s : ℝ) = 0
    · have hs : s = (0 : I) := by
        apply Subtype.ext
        simpa using hs0
      rw [hs]
      rw [arcClosedClass_zero]
      rw [show d.a (0 : I) = u by simpa [d, α] using extendInterior_zero u v a₀]
      rw [h0]
    · by_cases hs1 : (s : ℝ) = 1
      · have hs : s = (1 : I) := by
          apply Subtype.ext
          simpa using hs1
        rw [hs]
        rw [arcClosedClass_one]
        rw [show d.a (1 : I) = v by simpa [d, α] using extendInterior_one u v a₀]
        rw [h1]
      · have hs0n : (s : ℝ) ≠ 0 := hs0
        have hs1n : (s : ℝ) ≠ 1 := hs1
        have hαs : α s = a₀ ⟨s, ⟨hs0n, hs1n⟩⟩ := extendInterior_eq_on_interior u v a₀ hs0n hs1n
        have hβs : β s = b₀ ⟨s, ⟨hs0n, hs1n⟩⟩ := extendInterior_eq_on_interior u v b₀ hs0n hs1n
        have hcl := hcls ⟨s, ⟨hs0n, hs1n⟩⟩
        change (⟦(α s, β s)⟧ : UnordCirclePairs) = A s
        rw [hαs, hβs]
        exact hcl

end LeanEval.KnotTheory.Quadrisecant
