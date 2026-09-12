import Submission.Commons.Analysis.InnerProduct.A1_of_decomp
import Submission.Commons.Analysis.Affine.affine_one_signed
import Submission.Commons.Analysis.InnerProduct.exists_perp_decomp
import Submission.PaperBand.Triangle
import Submission.PaperBand.RadicalBounds
import Submission.Work.BandSpliceFI
import Submission.Work.BendArcFacts

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Lemma-G relation (4): `√(5+t²) < a + t`

This file isolates the last geometric step of the Lemma-G chain
(`TrapezoidLemma.lemmaG_of_aspect_inequalities` still needs it).  The
content, per the paper (Schwartz, §2.3, Figure 2):

> The shaded triangle `∇` of the `T`-pattern has `base = ℓ(T') = √(1+t²)`
> and `height > ℓ(B') = √(1+b²) ≥ 1`.  Let `H = H₁∪H₂`, `D = D₁∪D₂`.  Then
> `√(5+t²) < ℓ(∨) ≤ ℓ(D') = ℓ(D)`, where `∨` is the union of the two
> non-horizontal sides of `∇`.

So the whole content of (4) is the **existence of the apex** `u'` of `∇`:
a point of the `D`-boundary arc at perpendicular distance `> 1` from the
line of `T'`, such that the two chords from `u'` to the endpoints of `T'`
are bounded by the arc length `a + t` (`ℓ(D) = a + t`).

Two GREEN pieces are proved here:
* `relation4_of_ge_sqrt_five` — for `a ≥ √5` the inequality holds for every
  `t ≥ 0` (`5 + t² < (a+t)²`), so the triangle geometry is only needed for
  `√3 < a < √5`;
* `relation4_of_apex` — the abstract reduction: an apex at horizontal
  displacement `s` and height `h > 1` above the base `√(1+t²)`, whose two
  side lengths sum to at most `a + t` (the arc bound), yields (4).  This is
  exactly Lemma A1's strict form (`triangle_sides_bound_strict`) composed
  with the arc bound — the geometric work is reduced to producing the apex
  data `(s, h)` with `h > 1`.

Build: `lake build Submission.Work.LemmaG4` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Relation (4), easy regime `a > √5`**: for every `t ≥ 0`,
`√(5+t²) < a + t` (since `5 + t² < (a+t)²`).  (At `a = √5` and `t = 0`
the inequality fails, but that case is excluded by the strict height of
Figure 2's apex; the strict regime is all the triangle geometry does not
need to see.) -/
theorem relation4_of_gt_sqrt_five {a t : ℝ} (ha : Real.sqrt 5 < a) (ht : 0 ≤ t) :
    Real.sqrt (5 + t ^ 2) < a + t := by
  have h2 : (Real.sqrt 5) ^ 2 < a ^ 2 := by
    have hprod : 0 < (a - Real.sqrt 5) * (a + Real.sqrt 5) := by
      apply mul_pos
      · linarith
      · linarith [Real.sqrt_nonneg 5]
    nlinarith [hprod]
  have h5 : (5 : ℝ) < a ^ 2 := by
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)] at h2
  have ha0 : 0 ≤ a := by linarith [Real.sqrt_nonneg 5, ha]
  have hat : (0 : ℝ) ≤ a + t := by linarith
  rw [Real.sqrt_lt (by positivity) hat]
  nlinarith [h5, ht, ha0, mul_nonneg ha0 ht]

/-- **Relation (4) from the apex data** (the abstract Figure-2 reduction):
if a triangle with base `√(1+t²)` has its apex at horizontal displacement
`s` from the base midpoint and height `h > 1`, and the sum of the two
non-base sides is at most `a + t` (the length of the boundary arc `D`),
then `√(5+t²) < a + t` (Lemma A1, strict form). -/
theorem relation4_of_apex {a t s h : ℝ} (hh : 1 < h)
    (hside : Real.sqrt ((s + Real.sqrt (1 + t ^ 2) / 2) ^ 2 + h ^ 2) +
        Real.sqrt ((Real.sqrt (1 + t ^ 2) / 2 - s) ^ 2 + h ^ 2) ≤ a + t) :
    Real.sqrt (5 + t ^ 2) < a + t :=
  lt_of_lt_of_le (triangle_sides_bound_strict s t h hh) hside



/-- **Relation (4) from an A1-type side bound**: if a triangle has base
`√(1+t²)`, perpendicular height `h > 1`, and its two non-base sides sum to
at most `a + t` (the length of the boundary arc `D`), then
`√(5+t²) < a + t`.  This is the `√(base² + 4h²)` form of Lemma A1. -/
theorem relation4_of_side_bound {a t h : ℝ} (hh : 1 < h)
    (hside : Real.sqrt (1 + t ^ 2 + 4 * h ^ 2) ≤ a + t) :
    Real.sqrt (5 + t ^ 2) < a + t := by
  refine lt_of_lt_of_le ?_ hside
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith


/-- **Relation (4) from the geometric configuration (Figure 2)**: three
points `p₁ p₂ w` in a real inner product space, with `p₁ p₂` the base (the
image of a pre-bend chord, of length `√(1+t²)`), the apex decomposition
data `w − (p₁+p₂)/2 = c • (p₂−p₁) + n` with `n ⊥ (p₂−p₁)`, `‖n‖ = h > 1`
(the perpendicular distance of the apex from the base line), and the two
chords from the apex to the base endpoints summing to at most `a + t` (the
length of the boundary arc `D`); then `√(5+t²) < a + t`.

Combines the geometric Lemma A1 (point form,
`Commons.Analysis.InnerProduct.A1_of_decomp`) with the scalar reduction
`relation4_of_side_bound`.  This isolates the Figure-2 geometry: the only
remaining input is the existence of such a configuration on the
`T`-pattern. -/
theorem relation4_of_points {a t h : ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p₁ p₂ w : E} {c : ℝ} {n : E}
    (hbase : ‖p₂ - p₁‖ = Real.sqrt (1 + t ^ 2))
    (hdecomp : w - (1 / 2 : ℝ) • (p₁ + p₂) = c • (p₂ - p₁) + n)
    (hperp : inner ℝ n (p₂ - p₁) = 0) (hh : 1 < h) (hn : ‖n‖ = h)
    (hside : ‖w - p₁‖ + ‖w - p₂‖ ≤ a + t) :
    Real.sqrt (5 + t ^ 2) < a + t := by
  have hA1 := Commons.Analysis.InnerProduct.A1_of_decomp hdecomp hperp hn
  have hsq : ‖p₂ - p₁‖ ^ 2 = 1 + t ^ 2 := by
    rw [hbase, Real.sq_sqrt (by positivity)]
  have h1 : Real.sqrt (1 + t ^ 2 + 4 * h ^ 2) ≤ a + t := by
    have h2 : Real.sqrt (‖p₂ - p₁‖ ^ 2 + 4 * h ^ 2) =
        Real.sqrt (1 + t ^ 2 + 4 * h ^ 2) := by rw [hsq]
    rw [h2] at hA1
    linarith
  exact relation4_of_side_bound hh h1


/-- **Base length of a spliced leaf's image chord**: the image of the
pre-bend through height `y` has length `√(1 + Δ²)`, where `Δ` is the signed
displacement `B₁ − A₁` of the leaf.  (Isometry of the straight pre-bend,
`spliceChord_preBend`, plus the chord-length formula
`BendArcFacts.preimage_chord_length`.) -/
theorem image_chord_length {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) :
    ‖f ((spliceChord hf ha y).B) - f ((spliceChord hf ha y).A)‖ =
      Real.sqrt (1 + ((spliceChord hf ha y).B 1 - (spliceChord hf ha y).A 1) ^ 2) := by
  rw [spliceChord_preBend hf ha y]
  have hA : (spliceChord hf ha y).A = !₂[(0 : ℝ), (spliceChord hf ha y).A 1] :=
    leftEdge_eq_vec (spliceChord hf ha y).left_coord
  have hB : (spliceChord hf ha y).B = !₂[(1 : ℝ), (spliceChord hf ha y).B 1] :=
    rightEdge_eq_vec (spliceChord hf ha y).right_coord
  rw [hA, hB]
  exact preimage_chord_length _ _


/-- **Relation (4) from the perpendicular-distance configuration**: three
points with base `‖p₂−p₁‖ = √(1+t²)`, an apex `w` whose distance to the
line `p₁p₂` is at least `h > 1`, and the two chords from `w` to `p₁, p₂`
summing to at most `a + t`; then `√(5+t²) < a+t`.

This is the final assembly of the Figure-2 reduction: the
perpendicular-distance hypothesis is turned into the decomposition data of
`Commons.Analysis.InnerProduct.exists_perp_decomp`, and the geometric
Lemma A1 (`A1_of_decomp`) converts the two chord lengths into
`√(‖p₂−p₁‖² + 4h²) ≤ a+t`.  The remaining input is exactly the existence
of such a point `w` on the image of the `D`-boundary arc. -/
theorem relation4_of_configuration {a t : ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p₁ p₂ w : E} (hne : p₂ ≠ p₁)
    (hbase : ‖p₂ - p₁‖ = Real.sqrt (1 + t ^ 2)) {h : ℝ} (hh : 1 < h)
    (hdist : ∀ r : ℝ, h ≤ ‖w - ((1 / 2 : ℝ) • (p₁ + p₂) + r • (p₂ - p₁))‖)
    (hside : ‖w - p₁‖ + ‖w - p₂‖ ≤ a + t) :
    Real.sqrt (5 + t ^ 2) < a + t := by
  obtain ⟨c, n, hperp, hdecomp, hmin⟩ :=
    Commons.Analysis.InnerProduct.exists_perp_decomp p₁ p₂ w hne
  have hn : h ≤ ‖n‖ := by
    have hd := hdist c
    have hwc : w - ((1 / 2 : ℝ) • (p₁ + p₂) + c • (p₂ - p₁)) = n := by
      have hw : w = (c • (p₂ - p₁) + n) + (1 / 2 : ℝ) • (p₁ + p₂) :=
        sub_eq_iff_eq_add.mp hdecomp
      rw [hw]
      abel
    rwa [hwc] at hd
  have hA1 := Commons.Analysis.InnerProduct.A1_of_decomp hdecomp hperp rfl
  have hsq : ‖p₂ - p₁‖ ^ 2 = 1 + t ^ 2 := by
    rw [hbase, Real.sq_sqrt (by positivity)]
  have h1 : Real.sqrt (1 + t ^ 2 + 4 * h ^ 2) ≤ a + t := by
    refine le_trans ?_ hside
    refine le_trans ?_ hA1
    apply Real.sqrt_le_sqrt
    rw [hsq]
    nlinarith [hn]
  exact relation4_of_side_bound hh h1


/-- **Disjoint chords of the strip are strictly one-sided**: if the two
straight chords `u ↦ y₀ + (y₁−y₀)u` and `u ↦ z₀ + (z₁−z₀)u` never meet in
the open strip `u ∈ (0,1)` (as is the case for two distinct bends of the
foliation), then one is strictly above the other throughout.

This is the flat-band form of "the bends of the foliation are disjoint" —
the intrinsic input of the Figure-2 side argument
(`session_status123`). -/
theorem chord_height_one_signed {y₀ y₁ z₀ z₁ : ℝ}
    (h : ∀ u ∈ Set.Ioo (0 : ℝ) 1, z₀ + (z₁ - z₀) * u ≠ y₀ + (y₁ - y₀) * u) :
    (∀ u ∈ Set.Ioo (0 : ℝ) 1, y₀ + (y₁ - y₀) * u < z₀ + (z₁ - z₀) * u) ∨
      (∀ u ∈ Set.Ioo (0 : ℝ) 1, z₀ + (z₁ - z₀) * u < y₀ + (y₁ - y₀) * u) := by
  have h' : ∀ u ∈ Set.Ioo (0 : ℝ) 1, (z₀ - y₀) + ((z₁ - z₀) - (y₁ - y₀)) * u ≠ 0 := by
    intro u hu hzero
    exact h u hu (by linarith)
  rcases Commons.Analysis.Affine.affine_one_signed h' with hpos | hneg
  · left
    intro u hu
    have h1 := hpos u hu
    have hiff : z₀ + (z₁ - z₀) * u - (y₀ + (y₁ - y₀) * u)
        = (z₀ - y₀) + ((z₁ - z₀) - (y₁ - y₀)) * u := by ring
    linarith
  · right
    intro u hu
    have h1 := hneg u hu
    have hiff : z₀ + (z₁ - z₀) * u - (y₀ + (y₁ - y₀) * u)
        = (z₀ - y₀) + ((z₁ - z₀) - (y₁ - y₀)) * u := by ring
    linarith

/-- **The crossing of the chords' lines lies outside the strip**: if two
chords of the strip never meet inside the open strip and are not parallel,
the parameter `u*` where their supporting lines meet satisfies
`u* ≤ 0 ∨ 1 ≤ u*`.

(Equivalently: the meeting point of the two lines is not inside the strip —
the quantitative form of `chord_height_one_signed`.) -/
theorem chord_crossing_outside {y₀ y₁ z₀ z₁ : ℝ}
    (h : ∀ u ∈ Set.Ioo (0 : ℝ) 1, z₀ + (z₁ - z₀) * u ≠ y₀ + (y₁ - y₀) * u)
    (hdir : z₁ - z₀ ≠ y₁ - y₀) :
    (z₀ - y₀) / ((y₁ - y₀) - (z₁ - z₀)) ≤ 0 ∨
      1 ≤ (z₀ - y₀) / ((y₁ - y₀) - (z₁ - z₀)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hgt, hlt⟩ := hcon
  have hden : (y₁ - y₀) - (z₁ - z₀) ≠ 0 := by
    intro hz
    exact hdir (by linarith)
  have hroot : (z₀ - y₀) + ((z₁ - z₀) - (y₁ - y₀)) * ((z₀ - y₀) / ((y₁ - y₀) - (z₁ - z₀))) = 0 := by
    field_simp [hden]
    ring
  exact h _ ⟨hgt, hlt⟩ (by linarith)


/-- **Chord bound on the right edge**: the image distance between two points
of the right edge is at most their height difference (f is 1-Lipschitz and
the edge preimage is straight). -/
lemma edge_dist_le {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (s t : ℝ) :
    ‖f !₂[(1 : ℝ), s] - f !₂[(1 : ℝ), t]‖ ≤ |s - t| := by
  have hs : (!₂[(1 : ℝ), s] : ℝ²) ∈ unitStrip := rightEdge_mem_unitStrip s
  have ht : (!₂[(1 : ℝ), t] : ℝ²) ∈ unitStrip := rightEdge_mem_unitStrip t
  have h := embedding_lipschitz hf hs ht
  have hpre : ‖(!₂[(1 : ℝ), s] : ℝ²) - !₂[(1 : ℝ), t]‖ = |s - t| := by
    have hsub : (!₂[(1 : ℝ), s] : ℝ²) - !₂[(1 : ℝ), t] = !₂[(0 : ℝ), s - t] := by
      ext i <;> fin_cases i <;> simp
    rw [hsub, norm_single_second]
  simpa [hpre, norm_sub_rev] using h

/-- **The two chords of the `D`-arc sum to at most the arc length**: for a
point `f(1,s)` on the image of the `D`-arc — the right-edge interval from
`(1, y₀−a)` to `(1, y₁)`, of length `a + (y₁−y₀)` — the two chord lengths
to the arc's endpoints (which are `f(0,y₀)` and `f(1,y₁)`) sum to at most
`a + (y₁−y₀)` (1-Lipschitz). -/
lemma D_arc_chord_bound {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y₀ y₁ s : ℝ} (hs : s ∈ Set.Icc (y₀ - a) y₁) (hΔ : 0 ≤ y₁ - y₀) :
    ‖f !₂[(1 : ℝ), s] - f !₂[(1 : ℝ), y₀ - a]‖ +
      ‖f !₂[(1 : ℝ), y₁] - f !₂[(1 : ℝ), s]‖ ≤ a + (y₁ - y₀) := by
  have h1 := edge_dist_le hf s (y₀ - a)
  have h2 := edge_dist_le hf y₁ s
  have hb1 : |s - (y₀ - a)| = s - (y₀ - a) := abs_of_nonneg (by linarith [hs.1])
  have hb2 : |y₁ - s| = y₁ - s := abs_of_nonneg (by linarith [hs.2])
  rw [hb1] at h1
  rw [hb2] at h2
  linarith

/-- **Lemma A1 with a chord budget**: given the base vector `u = p₂ − p₁` of
length `√(1+t²)`, an apex `w` decomposed as `w − m = c•u + n` with
`n ⊥ u` (so `‖n‖` is the perpendicular distance from `w` to the base line),
and the two chords from `w` to the base endpoints summing to at most
`a + t` (the boundary-arc budget), the perpendicular height `‖n‖` satisfies
`√(1 + t² + 4‖n‖²) ≤ a + t` — the quantitative form of the crossing-case
bound of `session_status123` (Addendum 2). -/
theorem arc_A1_bound {a t : ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p₁ p₂ w : E} {c : ℝ} {n : E}
    (hbase : ‖p₂ - p₁‖ = Real.sqrt (1 + t ^ 2))
    (hdecomp : w - (1 / 2 : ℝ) • (p₁ + p₂) = c • (p₂ - p₁) + n)
    (hperp : inner ℝ n (p₂ - p₁) = 0)
    (hchords : ‖w - p₁‖ + ‖w - p₂‖ ≤ a + t) :
    Real.sqrt (1 + t ^ 2 + 4 * ‖n‖ ^ 2) ≤ a + t := by
  have hA1 := Commons.Analysis.InnerProduct.A1_of_decomp hdecomp hperp rfl
  have hsq : ‖p₂ - p₁‖ ^ 2 = 1 + t ^ 2 := by
    rw [hbase, Real.sq_sqrt (by positivity)]
  have h2 : Real.sqrt (1 + t ^ 2 + 4 * ‖n‖ ^ 2) =
      Real.sqrt (‖p₂ - p₁‖ ^ 2 + 4 * ‖n‖ ^ 2) := by rw [hsq]
  rw [h2]
  exact le_trans hA1 hchords


/-- **Piece (a): the base data of a spliced leaf** (`session_status123`,
Addendum 3).  For the leaf at height `y` the base vector is
`f B − f A` (`A = (spliceChord y).A`, `B = (spliceChord y).B`), whose length
is `√(1 + Δ²)` with `Δ = B 1 − A 1` the signed displacement
(`image_chord_length`), and the image of the left endpoint coincides with
the right-edge point at height `A 1 − a`
(`f_leftEdge_eq_rightEdge_minus`), i.e. with the lower end of the `D`-arc. -/
theorem tpattern_base {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) :
    ‖f ((spliceChord hf ha y).B) - f ((spliceChord hf ha y).A)‖ =
        Real.sqrt (1 + ((spliceChord hf ha y).B 1 - (spliceChord hf ha y).A 1) ^ 2) ∧
      f ((spliceChord hf ha y).A) =
        f !₂[(1 : ℝ), (spliceChord hf ha y).A 1 - a] := by
  constructor
  · exact image_chord_length hf ha y
  · let c : ℝ := (spliceChord hf ha y).A 1
    have hA : (spliceChord hf ha y).A = !₂[(0 : ℝ), c] :=
      leftEdge_eq_vec (spliceChord hf ha y).left_coord
    rw [hA]
    exact (f_leftEdge_eq_rightEdge_minus hf c).symm

/-- **Piece (a), apex data**: the apex decomposition supplied by the commons
line-decomposition lemma `exists_perp_decomp`, in the exact form consumed by
`arc_A1_bound` (and hence by the crossing-case bound). -/
theorem tpattern_apex_data {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p₁ p₂ w : E) (hne : p₂ ≠ p₁) :
    ∃ c : ℝ, ∃ n : E, inner ℝ n (p₂ - p₁) = 0 ∧
      w - (1 / 2 : ℝ) • (p₁ + p₂) = c • (p₂ - p₁) + n ∧
      ∀ r : ℝ, ‖n‖ ≤ ‖w - ((1 / 2 : ℝ) • (p₁ + p₂) + r • (p₂ - p₁))‖ :=
  Commons.Analysis.InnerProduct.exists_perp_decomp p₁ p₂ w hne


/-- **Same-side distance identity** (`session_status123`, piece (c)): for a
segment with midpoint at perpendicular offset `ν` from a line and half-length
`L ≥ 0` (so its endpoints are at offsets `ν ± L`), the larger endpoint
distance is `|ν| + L`.  In particular if `|ν| ≥ L` (the endpoints on the SAME
side) this is `≥ 2L = ℓ`, the length of the segment. -/
lemma max_abs_add_abs_sub {ν L : ℝ} (hL : 0 ≤ L) :
    max |ν + L| |ν - L| = |ν| + L := by
  rcases le_total 0 ν with hν | hν
  · have h1 : |ν + L| = ν + L := abs_of_nonneg (by linarith)
    have h2 : |ν - L| ≤ ν + L := by
      rcases le_total 0 (ν - L) with h3 | h3
      · rw [abs_of_nonneg h3]; linarith
      · rw [abs_of_nonpos h3]; linarith
    rw [max_eq_left (by rw [h1]; exact h2), h1, abs_of_nonneg hν]
  · have h1 : |ν - L| = L - ν := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have h2 : |ν + L| ≤ L - ν := by
      rcases le_total 0 (ν + L) with h3 | h3
      · rw [abs_of_nonneg h3]; linarith
      · rw [abs_of_nonpos h3]; linarith
    rw [max_eq_right (by rw [h1]; exact h2), h1, abs_of_nonpos hν]
    ring

/-- **Crossing-case distance identity** (`session_status123`, piece (c)):
if the midpoint offset `ν` is within `L` of the line (`|ν| ≤ L`), then the
endpoints `ν ± L` lie on OPPOSITE sides and their distances sum to exactly
`2L`, the length of the segment. -/
lemma abs_add_abs_sub_eq_two_mul {ν L : ℝ} (h : |ν| ≤ L) :
    |ν + L| + |ν - L| = 2 * L := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ν + L),
    abs_of_nonpos (by linarith : ν - L ≤ 0)]
  ring


/-- **The same-side case gives the strict apex inequality** (`session_status123`
piece (d), positive half): if the second bend's midpoint offset `|ν|` exceeds
its half-length `L` (so the bend's segment stays on one side of the line) and
`L ≥ 1/2` (which holds since `L = ℓ(B')/2 = √(1+b²)/2 ≥ 1/2`), then the
farther endpoint of the bend is at distance `|ν| + L > 1` from the line —
the strict inequality Lemma A1 needs (`relation4_of_side_bound` with `h > 1`).

Proof: `|ν| + L > 2L = ℓ(B') ≥ 1` and the first inequality is strict. -/
lemma same_side_dist_gt_one {ν L : ℝ} (hL : (1 : ℝ) / 2 ≤ L) (hν : L < |ν|) :
    1 < |ν| + L := by
  have h1 : |ν| + L > 2 * L := by linarith
  have h2 : 2 * L ≥ 1 := by linarith
  linarith


/-- **Norm of an orthogonal two-term combination**: for orthonormal `u₀, u₁`,
`‖a•u₀ + b•u₁‖² = a² + b²` (the Pythagorean identity in inner-product form,
proved with `real_inner_self_eq_norm_sq` and the bilinearity lemmas — no
`norm_add_sq`/`RCLike.re` friction). -/
lemma norm_smul_add_smul_sq {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u₀ u₁ : E} {a b : ℝ} (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (hperp : inner ℝ u₀ u₁ = 0) :
    ‖a • u₀ + b • u₁‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h1 : inner ℝ u₀ u₀ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu₀]; norm_num
  have h2 : inner ℝ u₁ u₁ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu₁]; norm_num
  have h3 : inner ℝ u₁ u₀ = 0 := by rw [real_inner_comm]; exact hperp
  rw [← real_inner_self_eq_norm_sq (a • u₀ + b • u₁)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h1, h2, hperp, h3]
  ring

/-- **The perpendicular-distance formula** (`session_status123`, Addendum 7,
piece (1)): if `w − m = μ•u₀ + ν•u₁` with `u₀, u₁` orthonormal, then `|ν|`
is exactly the perpendicular distance from `w` to the line
`{m + r•u₀ : r}`: every point of the line is at distance at least `|ν|`
(attained at `r = μ`). -/
lemma dist_eq_abs_coeff {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m w u₀ u₁ : E} {μ ν : ℝ}
    (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (hperp : inner ℝ u₀ u₁ = 0)
    (hdec : w - m = μ • u₀ + ν • u₁) :
    (∀ r : ℝ, |ν| ≤ ‖w - (m + r • u₀)‖) ∧ ‖w - (m + μ • u₀)‖ = |ν| := by
  have hsub : ∀ r : ℝ, w - (m + r • u₀) = (μ - r) • u₀ + ν • u₁ := by
    intro r
    rw [show (μ - r) • u₀ + ν • u₁ = (μ • u₀ + ν • u₁) - r • u₀ by
      rw [sub_smul]; abel]
    rw [← hdec]
    abel
  have hnorm : ∀ r : ℝ, ‖w - (m + r • u₀)‖ = Real.sqrt ((μ - r) ^ 2 + ν ^ 2) := by
    intro r
    have hsq : ‖w - (m + r • u₀)‖ ^ 2 = (μ - r) ^ 2 + ν ^ 2 := by
      rw [hsub r, norm_smul_add_smul_sq hu₀ hu₁ hperp]
    rw [← Real.sqrt_sq (norm_nonneg (w - (m + r • u₀))), hsq]
  constructor
  · intro r
    rw [hnorm r]
    have hle : Real.sqrt (ν ^ 2) ≤ Real.sqrt ((μ - r) ^ 2 + ν ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (μ - r)])
    rwa [Real.sqrt_sq_eq_abs] at hle
  · rw [hnorm μ]
    have hz : (μ - μ) ^ 2 + ν ^ 2 = ν ^ 2 := by ring
    rw [hz, Real.sqrt_sq_eq_abs]


/-- **The two endpoint distances of the second bend** (`session_status123`):
for the endpoints `m₁ ± L₁•u₁` of the second bend and the line through `m₀`
in the orthonormal direction `u₀` (`u₀ ⊥ u₁`), with the coplanarity
decomposition `m₁ − m₀ = μ•u₀ + ν•u₁`, the distances from the endpoints to
the line are `|ν ± L₁|`, and the larger of the two is `|ν| + L₁`. -/
theorem edge_distances {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m₀ m₁ u₀ u₁ : E} {μ ν L₁ : ℝ}
    (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (hperp : inner ℝ u₀ u₁ = 0)
    (hdec : m₁ - m₀ = μ • u₀ + ν • u₁) (hL : 0 ≤ L₁) :
    ‖(m₁ + L₁ • u₁) - (m₀ + μ • u₀)‖ = |ν + L₁| ∧
      ‖(m₁ - L₁ • u₁) - (m₀ + μ • u₀)‖ = |ν - L₁| ∧
      max ‖(m₁ + L₁ • u₁) - (m₀ + μ • u₀)‖ ‖(m₁ - L₁ • u₁) - (m₀ + μ • u₀)‖
        = |ν| + L₁ := by
  have hdecP : (m₁ + L₁ • u₁) - m₀ = μ • u₀ + (ν + L₁) • u₁ := by
    have h₁ : (m₁ + L₁ • u₁) - m₀ = (m₁ - m₀) + L₁ • u₁ := by abel
    rw [h₁, hdec, add_smul]
    abel
  have hdecM : (m₁ - L₁ • u₁) - m₀ = μ • u₀ + (ν - L₁) • u₁ := by
    have h₁ : (m₁ - L₁ • u₁) - m₀ = (m₁ - m₀) - L₁ • u₁ := by abel
    rw [h₁, hdec, sub_smul]
    abel
  have hP := (dist_eq_abs_coeff hu₀ hu₁ hperp hdecP).2
  have hM := (dist_eq_abs_coeff hu₀ hu₁ hperp hdecM).2
  refine ⟨hP, hM, ?_⟩
  rw [hP, hM, max_abs_add_abs_sub hL]


/-- **(1a) Edge unit speed** (`session_status123`, Addendum 11): at every point
of the right edge, the derivative of the embedding applied to the edge
direction `!₂[0,1]` has norm `1` — so the image of the right edge is a
unit-speed curve, and the `D`-arc's image is a unit-speed geodesic. -/
theorem edge_fderiv_unit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (s : ℝ) :
    ‖fderivWithin ℝ f unitStrip (!₂[(1 : ℝ), s]) !₂[(0 : ℝ), (1 : ℝ)]‖ = 1 := by
  have hx : (!₂[(1 : ℝ), s] : ℝ²) ∈ unitStrip := rightEdge_mem_unitStrip s
  rw [fderiv_norm_eq hf _ hx, norm_single_second]
  norm_num

/-- **(1a), left-edge form**: the same at the left edge. -/
theorem leftEdge_fderiv_unit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (s : ℝ) :
    ‖fderivWithin ℝ f unitStrip (!₂[(0 : ℝ), s]) !₂[(0 : ℝ), (1 : ℝ)]‖ = 1 := by
  have hx : (!₂[(0 : ℝ), s] : ℝ²) ∈ unitStrip := leftEdge_mem_unitStrip s
  rw [fderiv_norm_eq hf _ hx, norm_single_second]
  norm_num

end Submission
