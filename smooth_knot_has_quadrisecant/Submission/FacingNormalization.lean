import Mathlib
import Submission.AmbientTwoArc
import Submission.IntervalHomeoEnds

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/-!
# S164 — the facing-normalization vocabulary and the coordinate overlap
shape (module Submission/FacingNormalization.lean)

The remaining step of the ambient two-arc theorem (ROADMAP S163, step (3))
is the **facing-normalization lemma**: in a Hausdorff locally-interval
ambient, two open arcs whose overlap is connected can only overlap in the
facing/containment end-arrangements — a middle or same-side overlap would
force a seam configuration in which the union is not locally interval or
the two seam points are inseparable, contradicting Hausdorffness.  This
module fixes the vocabulary and proves the coordinate-overlap foundation:

1. **`coordRealSet φ V`** — the `V`-part of the `U`-chart as a subset of
   ℝ (the coordinate values `r ∈ (0,1)` whose chart point lies in `V`);
2. `coordRealSet_isOpen` (the coordinate set is open in ℝ: the chart
   pullback is open and `subtype.val : (0,1) → ℝ` is an open map),
   `coordRealSet_isConnected` (connected + nonempty when the overlap
   subspace `{x // x ∈ U ∩ V}` is connected), and
   `coordRealSet_subset_openUnit`;
3. **`overlap_coord_shape`** (headline): the coordinate overlap is an open
   interval `(a,b)` with `0 ≤ a < b ≤ 1` (classification of
   RealIntervalShape S162 + the openness/connectedness transport).  The
   **seam points** of the `U`-chart live at the chart points with
   coordinates `a` (left seam, present iff `0 < a`) and `b` (right seam,
   present iff `b < 1`); the `ψ`-analogue gives the `V`-seams;
4. `coord_mem_iff_mem_coordRealSet` (membership translation at a
   coordinate) and the first exclusion facts
   **`left_seam_not_in_V_of_shape`** / **`right_seam_not_in_V_of_shape`**:
   a seam point of `U` is NOT in `V` (it lies in `U ∖ V`, at the chart
   boundary of the overlap) — the elementary half of the seam analysis.
   The symmetric statements for the `ψ`-chart (`ψ`-seams not in `U`)
   follow by interchanging `U ↔ V` and `φ ↔ ψ`.

THE FACING-NORMALIZATION LEMMA (statement for the next sessions; the
model inputs — the shape classification and the seam exclusions — are the
lemmas of this module + AmbientTwoArc S163 + RealIntervalShape S162):
given a Hausdorff ambient, charts `φ ψ`, and `U ∩ V` nonempty connected
with shapes `(a,b)`, `(c,d)`, the seams of `U` and `V` at the two ends of
the overlap must be paired compatibly or absent (each end of the overlap
is an end of at least one chart); hence there are sub-arcs `U' ⊆ U`,
`V' ⊆ V` with `U' ∪ V' = U ∪ V` and terminal-facing overlap in the
charts (the `two_chart_glue_homeo` input of TwoChartGlue S157).  Proof
structure (from the S154/S163 analysis): at an end of the overlap where
BOTH charts have a strict seam (`0 < a ∧ 0 < c`, etc., with the
orientation of the interval homeo matching the ends), the two seam points
both lie in the closure of the overlap and are inseparable in `X`, so
Hausdorffness forces them equal — but the `U`-seam is in `U ∖ V` and the
`V`-seam in `V ∖ U`, which are disjoint — a contradiction.  The
remaining sub-lemmas are: the endpoint correspondence of the interval
homeo between the two overlap intervals (a homeo between open intervals
is monotone and maps ends to ends — real-analysis), and the
inseparability argument (both seam points are approached by common
overlap points).  Everything in this module is verified (no axioms, no
`sorry`).
-/
open Set
open scoped Topology

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

abbrev ORI (lo hi : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo lo hi}

/-- The overlap `V`-part of the chart of `U`, seen as a subset of ℝ through the
coordinate value. -/
def coordRealSet {X : Type*} [TopologicalSpace X] {U : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (V : Set X) : Set ℝ :=
  (fun t : ORI 0 1 => (t : ℝ)) '' {t : ORI 0 1 | (φ t : X) ∈ V}

/-- The coordinate real set is open in ℝ: `{t | φ t ∈ V}` is open in the chart
(`overlapPullback_isOpen`), and `subtype.val` from the open interval `(0,1)` to
ℝ is an open map (`IsOpen.isOpenMap_subtype_val`). -/
theorem coordRealSet_isOpen {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V) :
    IsOpen (coordRealSet φ V) := by
  dsimp [coordRealSet]
  exact (IsOpen.isOpenMap_subtype_val (X := ℝ) (s := Set.Ioo (0 : ℝ) 1)
      (show IsOpen (Set.Ioo (0 : ℝ) 1) from isOpen_Ioo))
    {t : ORI 0 1 | (φ t : X) ∈ V} (overlapPullback_isOpen φ hV)

/-- The coordinate real set is connected and nonempty when the overlap subspace
`{x // x ∈ U ∩ V}` is connected. -/
theorem coordRealSet_isConnected {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U})
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    IsConnected (coordRealSet φ V) := by
  let A := {t : ORI 0 1 // (φ t : X) ∈ V}
  let At : Set (ORI 0 1) := {t : ORI 0 1 | (φ t : X) ∈ V}
  have hAhomeo : A ≃ₜ {x : X // x ∈ U ∩ V} := by
    dsimp [A]
    exact overlapPullbackHomeo φ
  have hAconn : ConnectedSpace A := (hAhomeo.symm.connectedSpace_iff).mp hconn
  have hAtconn : IsConnected At := by
    dsimp [A, At] at hAconn ⊢
    exact (isConnected_iff_connectedSpace (s := {t : ORI 0 1 | (φ t : X) ∈ V})).mpr hAconn
  have hval : ContinuousOn (fun t : ORI 0 1 => (t : ℝ)) At := continuous_subtype_val.continuousOn
  have himg : IsConnected ((fun t : ORI 0 1 => (t : ℝ)) '' At) :=
    IsConnected.image hAtconn (fun t : ORI 0 1 => (t : ℝ)) hval
  dsimp [coordRealSet, At]
  exact himg

/-- The coordinate real set is contained in `(0,1)`. -/
theorem coordRealSet_subset_openUnit {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) :
    coordRealSet φ V ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro r hr
  rcases hr with ⟨t, ht, rfl⟩
  exact t.2

/-- **The overlap shape**: the `V`-part of the `U`-chart, as a real set, is an
open interval `(a,b)` with `0 ≤ a < b ≤ 1`.  Seam points of `U` live at the
chart points with coordinates `a` (left, present iff `0 < a`) and `b` (right,
present iff `b < 1`); the `ψ`-analogue for `V` is symmetric. -/
theorem overlap_coord_shape {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V)
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ coordRealSet φ V = Set.Ioo a b := by
  let S := coordRealSet φ V
  have hSopen : IsOpen S := by dsimp [S]; exact coordRealSet_isOpen φ hV
  have hSconn : IsConnected S := by dsimp [S]; exact coordRealSet_isConnected φ hconn
  have hSsub : S ⊆ Set.Ioo (0 : ℝ) 1 := by dsimp [S]; exact coordRealSet_subset_openUnit φ
  rcases open_preconnected_nonempty_ℝ_shape hSopen hSconn.2 hSconn.1 with h | h | h | h
  · rcases h with ⟨a, b, h⟩
    have hab : a < b := by
      rcases hSconn.1 with ⟨x, hxS⟩
      have hx' : x ∈ Ioo a b := by simpa [h] using hxS
      exact hx'.1.trans hx'.2
    have ha0 : 0 ≤ a := by
      by_contra ha
      have hlt : a < 0 := lt_of_not_ge ha
      by_cases hb0 : b ≤ 0
      · rcases hSconn.1 with ⟨x, hxS⟩
        have hxpos : 0 < x := (hSsub hxS).1
        have hx' : x ∈ Ioo a b := by simpa [h] using hxS
        rcases hx' with ⟨_hxa, hxb⟩
        linarith
      · have hbpos : 0 < b := lt_of_not_ge hb0
        have h0S : (0 : ℝ) ∈ S := by
          have h0 : (0 : ℝ) ∈ Ioo a b := ⟨hlt, hbpos⟩
          simpa [h] using h0
        have h0pos : 0 < (0 : ℝ) := (hSsub h0S).1
        linarith
    have hb1 : b ≤ 1 := by
      by_contra hb
      have hgt : 1 < b := lt_of_not_ge hb
      by_cases ha1 : 1 ≤ a
      · rcases hSconn.1 with ⟨x, hxS⟩
        have hxlt : x < 1 := (hSsub hxS).2
        have hx' : x ∈ Ioo a b := by simpa [h] using hxS
        rcases hx' with ⟨hxa, _hxb⟩
        linarith
      · have h1lt : a < 1 := lt_of_not_ge ha1
        have h1S : (1 : ℝ) ∈ S := by
          have h1 : (1 : ℝ) ∈ Ioo a b := ⟨h1lt, hgt⟩
          simpa [h] using h1
        have h1lt' : (1 : ℝ) < 1 := (hSsub h1S).2
        linarith
    exact ⟨a, b, ha0, hab, hb1, h⟩
  · exfalso
    rcases h with ⟨α, h⟩
    -- S = Ioi α ⊆ (0,1) is impossible (Ioi α unbounded above)
    let y : ℝ := max α 1 + 1
    have hyα : α < y := by
      dsimp [y]
      exact lt_of_le_of_lt (le_max_left α 1) (lt_add_one (max α 1))
    have hyS : y ∈ S := by rw [h]; exact Set.mem_Ioi.mpr hyα
    have hyb : y < 1 := (hSsub hyS).2
    have hygt : 1 < y := by
      dsimp [y]
      by_cases hα1 : α ≤ 1
      · have hmax : max α 1 = 1 := max_eq_right hα1
        rw [hmax]
        norm_num
      · have h1α : 1 ≤ α := le_of_lt (lt_of_not_ge hα1)
        have hmax : max α 1 = α := max_eq_left h1α
        rw [hmax]
        linarith
    linarith
  · exfalso
    rcases h with ⟨α, h⟩
    -- S = Iio α ⊆ (0,1) impossible (Iio α unbounded below)
    let y : ℝ := min α 0 - 1
    have hyα : y < α := by
      dsimp [y]
      exact lt_of_lt_of_le (sub_lt_self (min α 0) (by norm_num)) (min_le_left α 0)
    have hyS : y ∈ S := by rw [h]; exact Set.mem_Iio.mpr hyα
    have hyp : 0 < y := (hSsub hyS).1
    have hylt : y < 0 := by
      dsimp [y]
      have hmin : min α 0 ≤ 0 := min_le_right α 0
      linarith
    linarith
  · exfalso
    -- S = univ ⊆ (0,1) impossible (1 ∈ univ)
    have h1S : (1 : ℝ) ∈ S := by rw [h]; trivial
    have h1b : (1 : ℝ) < 1 := (hSsub h1S).2
    linarith


/-- Membership translation: the chart point at real coordinate `r` lies in `V`
iff `r` lies in the coordinate real set of the overlap. -/
theorem coord_mem_iff_mem_coordRealSet {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    ((φ ⟨r, hr⟩ : X) ∈ V) ↔ r ∈ coordRealSet φ V := by
  constructor
  · intro h
    dsimp [coordRealSet]
    exact ⟨⟨r, hr⟩, h, rfl⟩
  · intro h
    rcases h with ⟨t, ht, htv⟩
    have ht_eq : t = ⟨r, hr⟩ := by
      apply Subtype.ext
      exact htv
    rw [← ht_eq]
    exact ht

/-- The left seam point of the `U`-chart (coordinate `a`, when `0 < a`) is NOT in
`V`: it lies in `U ∖ V`, in the closure of the overlap from within the chart. -/
theorem left_seam_not_in_V_of_shape {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1) :
    ¬ ((φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X) ∈ V) := by
  have haV : a ∉ coordRealSet φ V := by
    intro hmem
    have hmem' : a ∈ Ioo a b := by simpa [hshape] using hmem
    exact (lt_irrefl a) hmem'.1
  intro hφ
  have hmem : a ∈ coordRealSet φ V :=
    (coord_mem_iff_mem_coordRealSet φ ⟨ha0, lt_of_lt_of_le hab hb1⟩).mp hφ
  exact haV hmem

/-- The right seam point of the `U`-chart (coordinate `b`, when `b < 1`) is NOT in
`V`: it lies in `U ∖ V`, in the closure of the overlap from within the chart. -/
theorem right_seam_not_in_V_of_shape {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1) :
    ¬ ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1⟩⟩ : X) ∈ V) := by
  have hbV : b ∉ coordRealSet φ V := by
    intro hmem
    have hmem' : b ∈ Ioo a b := by simpa [hshape] using hmem
    exact (lt_irrefl b) hmem'.2
  intro hφ
  have hmem : b ∈ coordRealSet φ V :=
    (coord_mem_iff_mem_coordRealSet φ ⟨lt_of_le_of_lt ha0 hab, hb1⟩).mp hφ
  exact hbV hmem

/-- **U-side seam approach**: every neighbourhood `N` of the left seam point
`φ⟨a⟩` of the `U`-chart contains the `φ`-images of the overlap points with
coordinates in `(a, a+δ)` — the overlap approaches the seam from within the
chart. -/
theorem left_seam_approached_by_overlap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1) :
    ∀ N : Set X, N ∈ 𝓝 ((φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 - a ∧ δ ≤ b - a ∧
        (∀ u : ORI 0 1, (u : ℝ) ∈ Ioo a (a + δ) →
          (φ u : X) ∈ N ∧ (φ u : X) ∈ V) := by
  intro N hN
  let x0 : ORI 0 1 := ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩
  have hg : Continuous (fun t : ORI 0 1 => (φ t : X)) := Continuous.subtype_val φ.continuous
  have hpre : (fun t : ORI 0 1 => (φ t : X)) ⁻¹' N ∈ 𝓝 x0 :=
    hg.continuousAt.preimage_mem_nhds (by simpa [x0] using hN)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε0, hball⟩
  let δ : ℝ := min ε (min (b - a) (1 - a))
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have hba : 0 < b - a := by linarith
    have h1a : 0 < 1 - a := by linarith
    positivity
  have hδε : δ ≤ ε := by dsimp [δ]; exact min_le_left ε (min (b - a) (1 - a))
  have hδb : δ ≤ b - a := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (b - a) (1 - a))) (min_le_left (b - a) (1 - a))
  have hδ1 : δ ≤ 1 - a := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (b - a) (1 - a))) (min_le_right (b - a) (1 - a))
  refine ⟨δ, hδ0, hδ1, hδb, ?_⟩
  intro u hu
  rcases hu with ⟨hua, huδ⟩
  have huε : dist u x0 < ε := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hlt : (u : ℝ) - a < ε := by linarith
    rw [abs_of_pos (sub_pos.mpr hua)]
    exact hlt
  have huN : u ∈ (fun t : ORI 0 1 => (φ t : X)) ⁻¹' N := hball huε
  have hφN : (φ u : X) ∈ N := huN
  have hφV : (φ u : X) ∈ V := by
    have htb : (u : ℝ) < b := by linarith
    exact (coord_mem_iff_mem_coordRealSet φ u.2).mpr (by
      rw [hshape]
      exact ⟨hua, htb⟩)
  exact ⟨hφN, hφV⟩

/-- **U-side seam in the closure of the overlap**: the left seam point of the
`U`-chart lies in the closure of `U ∩ V` (approached from within the overlap,
by the approach lemma). -/
theorem left_seam_mem_closure_overlap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1) :
    (φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X) ∈ closure (U ∩ V) := by
  rw [mem_closure_iff]
  intro N hNopen hxN
  have hNN : N ∈ 𝓝 (φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X) := hNopen.mem_nhds hxN
  rcases left_seam_approached_by_overlap φ hshape ha0 hab hb1 N hNN with ⟨δ, hδ0, hδ1, hδb, hδ⟩
  let u : ORI 0 1 := ⟨a + δ / 2, ⟨by linarith, by linarith⟩⟩
  have hu : (u : ℝ) ∈ Ioo a (a + δ) := ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
  rcases hδ u hu with ⟨hφN, hφV⟩
  exact ⟨(φ u : X), ⟨hφN, ⟨(φ u).2, hφV⟩⟩⟩

/-- **V-side seam approach** (the mirror of `left_seam_approached_by_overlap`
under `U ↔ V`, `φ ↔ ψ`): every neighbourhood `N` of the left seam point
`ψ⟨c⟩` of the `V`-chart contains the `ψ`-images of the overlap points with
coordinates in `(c, c+δ)`. -/
theorem left_seam_approached_by_overlap_swap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) {c d : ℝ}
    (hshape : coordRealSet ψ U = Set.Ioo c d) (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    ∀ N : Set X, N ∈ 𝓝 ((ψ ⟨c, ⟨hc0, lt_of_lt_of_le hcd hd1⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 - c ∧ δ ≤ d - c ∧
        (∀ u : ORI 0 1, (u : ℝ) ∈ Ioo c (c + δ) →
          (ψ u : X) ∈ N ∧ (ψ u : X) ∈ U) := by
  simpa [inter_comm] using
    (left_seam_approached_by_overlap (U := V) (V := U) (φ := ψ) (a := c) (b := d)
      hshape hc0 hcd hd1)

/-- **V-side seam in the closure of the overlap** (mirror of
`left_seam_mem_closure_overlap`): the left seam point of the `V`-chart lies in
the closure of `U ∩ V`. -/
theorem left_seam_mem_closure_overlap_swap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) {c d : ℝ}
    (hshape : coordRealSet ψ U = Set.Ioo c d) (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    (ψ ⟨c, ⟨hc0, lt_of_lt_of_le hcd hd1⟩⟩ : X) ∈ closure (U ∩ V) := by
  simpa [inter_comm] using
    (left_seam_mem_closure_overlap (U := V) (V := U) (φ := ψ) (a := c) (b := d)
      hshape hc0 hcd hd1)
theorem seam_pair_common_point {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1)
    (hcomp : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          (φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1).1 < a + ε)
    (N : Set X) (hN : N ∈ 𝓝 ((φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X)))
    (M : Set X) (hM : M ∈ 𝓝 ((ψ ⟨c, ⟨hc0, lt_of_lt_of_le hcd hd1⟩⟩ : X))) :
    (N ∩ M).Nonempty := by
  rcases left_seam_approached_by_overlap φ hA ha0 hab hb1 N hN with ⟨δ, hδ0, _hδ1a, _hδb, hδ⟩
  rcases hcomp δ hδ0 with ⟨ηc, hηc0, hηc1, hηcd, hηc⟩
  rcases left_seam_approached_by_overlap_swap ψ hB hc0 hcd hd1 M hM with ⟨ηm, hηm0, hηm1, hηmd, hηm⟩
  let η : ℝ := min ηm ηc
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min hηm0 hηc0
  have hηm1c : η ≤ 1 - c := by
    dsimp [η]
    exact le_trans (min_le_left ηm ηc) hηm1
  have hηmdc : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_left ηm ηc) hηmd
  have hηc1c : η ≤ 1 - c := by
    dsimp [η]
    exact le_trans (min_le_right ηm ηc) hηc1
  have hηcdc : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_right ηm ηc) hηcd
  have hη2pos : 0 < η / 2 := div_pos hη0 (by norm_num)
  have hη2lt : η / 2 < η := by linarith
  have hηleM : η ≤ ηm := by dsimp [η]; exact min_le_left ηm ηc
  have hηleC : η ≤ ηc := by dsimp [η]; exact min_le_right ηm ηc
  -- pick the V-overlap point at coordinate c + η/2
  let w0 : ORI 0 1 := ⟨c + η / 2, ⟨by linarith, by linarith⟩⟩
  have hw0m : (w0 : ℝ) ∈ Ioo c (c + ηm) := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleM], by linarith⟩
  have hw0c' : (w0 : ℝ) ∈ Ioo c (c + ηc) := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleC], by linarith⟩
  have hψU0 : (ψ w0 : X) ∈ U := by
    -- w0 ∈ (c,d): from η ≤ d−c: (w0:ℝ) < c+η ≤ d? need w0<d: w0 < c+η: η≤d−c: w0 < c+η ≤ d ✓ wait need < d: η/2<η: w0 = c+η/2 < c+η ≤ d ✓
    have hwd : (w0 : ℝ) < d := by
      have hle : c + η ≤ d := by linarith
      exact lt_of_lt_of_le (by dsimp [w0]; linarith) hle
    exact (coord_mem_iff_mem_coordRealSet ψ w0.2).mpr (by
      rw [hB]
      exact ⟨by dsimp [w0]; linarith, hwd⟩)
  -- M-side: ψw0 ∈ M via the swap approach:
  rcases hηm w0 hw0m with ⟨hψM, _hψU'⟩
  -- U-coordinate of ψw0 is < a+δ (compat) and > a (w0 in the overlap (a,b)-side)
  let u0 : ORI 0 1 := φ.symm ⟨(ψ w0 : X), hψU0⟩
  have htδ : (u0 : ℝ) < a + δ := by
    -- apply hηc to the B-element wB := ⟨w0, hψU0⟩
    exact hηc ⟨w0, hψU0⟩ (by simpa [u0] using hw0c')
  have htA : (u0 : ℝ) ∈ Ioo a b := by
    have heq : (φ u0 : X) = (ψ w0 : X) := by
      dsimp [u0]
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
    have hφV : (φ u0 : X) ∈ V := by
      rw [heq]
      exact (ψ w0).2
    have hu0 : (u0 : ℝ) ∈ coordRealSet φ V :=
      (coord_mem_iff_mem_coordRealSet φ u0.2).mp hφV
    rwa [hA] at hu0
  -- so u0 ∈ (a, a+δ):
  have hu0 : (u0 : ℝ) ∈ Ioo a (a + δ) := ⟨(by
    rcases htA with ⟨h1, _⟩
    exact h1), htδ⟩
  rcases hδ u0 hu0 with ⟨hφu0N, _⟩
  -- φu0 = ψw0 ∈ M: common point is (ψ w0 : X)
  have heq2 : (φ u0 : X) = (ψ w0 : X) := by
    dsimp [u0]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
  refine ⟨(ψ w0 : X), ?_, ?_⟩
  · exact heq2 ▸ hφu0N
  · exact hψM


/-- **Left strict seams are impossible in a Hausdorff ambient**: if both left
seams are strict and the transition is left-to-left compatible (the
`hcomp` hypothesis of `seam_pair_common_point`, supplied by the increasing
case of IntervalHomeoEnds S165), then `X` cannot be `T2`.  (If the two seam
points are equal, the point lies in both `U` (as `φ⟨a⟩`) and `V` (as
`ψ⟨c⟩`), contradicting `left_seam_not_in_V_of_shape`; if they differ,
`t2_separation` gives disjoint open neighbourhoods which the common-point
lemma forces to meet.) -/
theorem not_T2_of_left_strict_seams {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1)
    (hcomp : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          (φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1).1 < a + ε) : False := by
  let p : X := (φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X)
  let q : X := (ψ ⟨c, ⟨hc0, lt_of_lt_of_le hcd hd1⟩⟩ : X)
  by_cases hpq : p = q
  · have hpV : p ∈ V := by
      rw [hpq]
      exact (ψ ⟨c, ⟨hc0, lt_of_lt_of_le hcd hd1⟩⟩).2
    have hφaV : ¬ ((φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X) ∈ V) :=
      left_seam_not_in_V_of_shape φ hA ha0 hab hb1
    exact hφaV (by simpa [p] using hpV)
  · rcases t2_separation hpq with ⟨O, P, hOo, hPo, hpO, hqP, hdisj⟩
    have hNO : O ∈ 𝓝 p := hOo.mem_nhds hpO
    have hMP : P ∈ 𝓝 q := hPo.mem_nhds hqP
    rcases seam_pair_common_point φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hcomp
        O (by simpa [p] using hNO) P (by simpa [q] using hMP) with ⟨z, hzO, hzP⟩
    have hOem : O ∩ P = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
    have hz : z ∈ O ∩ P := ⟨hzO, hzP⟩
    rw [hOem] at hz
    exact hz
noncomputable def pullbackToRealCoordHomeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) :
    ({t : ORI 0 1 // (φ t : X) ∈ V}) ≃ₜ ({r : ℝ // r ∈ coordRealSet φ V}) := by
  let A := {t : ORI 0 1 // (φ t : X) ∈ V}
  let R := {r : ℝ // r ∈ coordRealSet φ V}
  let F : A → R := fun t => by
    let rt : ℝ := ((t : ORI 0 1) : ℝ)
    have hmem : (φ (⟨rt, (t : ORI 0 1).2⟩ : ORI 0 1) : X) ∈ V := by
      simpa [rt] using t.2
    exact ⟨rt, (coord_mem_iff_mem_coordRealSet φ (⟨rt, (t : ORI 0 1).2⟩ : ORI 0 1).2).mp hmem⟩
  let G : R → A := fun r => by
    let hr01 : (r : ℝ) ∈ Ioo (0 : ℝ) 1 := coordRealSet_subset_openUnit φ r.2
    let u : ORI 0 1 := ⟨(r : ℝ), hr01⟩
    exact ⟨u, (coord_mem_iff_mem_coordRealSet φ u.2).mpr r.2⟩
  have hFG : Function.LeftInverse G F := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    simp [F, G]
  have hGF : Function.RightInverse G F := by
    intro r
    apply Subtype.ext
    simp [F, G]
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_mk continuous_subtype_val (by intro r; exact coordRealSet_subset_openUnit φ r.2)
  let e : A ≃ R := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- **The transition homeomorphism** `g : (c,d) ≃ₜ (a,b)`: the coordinate
change between the two overlap charts, assembled from the canonical
interval identifications (`pullbackToRealCoordHomeo`) and the overlap
pullback homeos (`overlapPullbackHomeo`, S163): source coordinate `s`
(lifting to the `ψ`-chart point in `U`) maps through the overlap to the
`φ`-coordinate of the same point. -/
noncomputable def transitionHomeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) :
    ({s : ℝ // s ∈ Ioo c d}) ≃ₜ ({t : ℝ // t ∈ Ioo a b}) := by
  let B := {s : ORI 0 1 // (ψ s : X) ∈ U}
  let Rb := {r : ℝ // r ∈ coordRealSet ψ U}
  let A := {t : ORI 0 1 // (φ t : X) ∈ V}
  let Ra := {r : ℝ // r ∈ coordRealSet φ V}
  -- e_b : (c,d)-type ≃ₜ B
  let e_b : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ B := by
    dsimp [B, Rb]
    exact ((setEqSubtypeHomeoX hB).symm.trans (pullbackToRealCoordHomeo ψ).symm)
  -- e1 : B ≃ₜ {x // x ∈ V ∩ U}
  let e1 : B ≃ₜ {x : X // x ∈ V ∩ U} := by
    dsimp [B]
    exact overlapPullbackHomeo ψ
  -- e2 : {x//x∈V∩U} ≃ₜ {x//x∈U∩V}
  let e2 : ({x : X // x ∈ V ∩ U}) ≃ₜ ({x : X // x ∈ U ∩ V}) := by
    exact setEqSubtypeHomeoX (Set.inter_comm V U)
  -- e3 : {x//x∈U∩V} ≃ₜ A
  let e3 : ({x : X // x ∈ U ∩ V}) ≃ₜ A := by
    dsimp [A]
    exact (overlapPullbackHomeo φ).symm
  -- e4 : A ≃ₜ Ra
  let e4 : A ≃ₜ Ra := by
    dsimp [A, Ra]
    exact pullbackToRealCoordHomeo φ
  -- e5 : Ra ≃ₜ (a,b)-type
  let e5 : Ra ≃ₜ ({t : ℝ // t ∈ Ioo a b}) := by
    dsimp [Ra]
    exact setEqSubtypeHomeoX hA
  let g1 : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ ({x : X // x ∈ V ∩ U}) := e_b.trans e1
  let g2 : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ ({x : X // x ∈ U ∩ V}) := g1.trans e2
  let g3 : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ A := g2.trans e3
  let g4 : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ Ra := g3.trans e4
  let g5 : ({s : ℝ // s ∈ Ioo c d}) ≃ₜ ({t : ℝ // t ∈ Ioo a b}) := g4.trans e5
  exact g5
theorem overlapPullbackHomeo_apply_val {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (t : {t : ORI 0 1 // (φ t : X) ∈ V}) :
    ((overlapPullbackHomeo φ t : {x : X // x ∈ U ∩ V}) : X) = (φ t : X) := by
  dsimp [overlapPullbackHomeo]

/-- Value of the inverse of `overlapPullbackHomeo` (the `φ.symm` coordinate). -/
theorem overlapPullbackHomeo_symm_apply_val {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (w : {x : X // x ∈ U ∩ V}) :
    ((overlapPullbackHomeo φ).symm w : ORI 0 1) = φ.symm ⟨(w : X), (w.2).1⟩ := by
  dsimp [overlapPullbackHomeo]

/-- Value of `pullbackToRealCoordHomeo` (the coordinate). -/
theorem pullbackToRealCoordHomeo_apply_val {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (t : {t : ORI 0 1 // (φ t : X) ∈ V}) :
    ((pullbackToRealCoordHomeo φ t : {r : ℝ // r ∈ coordRealSet φ V}) : ℝ) =
      ((t : ORI 0 1) : ℝ) := by
  dsimp [pullbackToRealCoordHomeo]

/-- Value of the inverse of `pullbackToRealCoordHomeo` (the lift). -/
theorem pullbackToRealCoordHomeo_symm_apply_val {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (r : {r : ℝ // r ∈ coordRealSet φ V}) :
    ((pullbackToRealCoordHomeo φ).symm r : ORI 0 1) = ⟨(r : ℝ), coordRealSet_subset_openUnit φ r.2⟩ := by
  dsimp [pullbackToRealCoordHomeo]

/-- `setEqSubtypeHomeoX` is identity on values. -/
theorem setEqSubtypeHomeoX_apply_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) (x : {x : X // x ∈ s}) :
    ((setEqSubtypeHomeoX h x : {x : X // x ∈ t}) : X) = (x : X) := by
  dsimp [setEqSubtypeHomeoX]


/-- **The coordinate value lemma of the transition homeo**: for `s` a
coordinate in `(c,d)` (the overlap in the `ψ`-chart), `g s` is the
`φ`-coordinate of the common chart point `ψ⟨s⟩` — the two chart points at
the matching coordinates coincide. -/
theorem transitionHomeo_coord {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (s : {s : ℝ // s ∈ Ioo c d})
    (hs01 : (s : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hψU : (ψ ⟨(s : ℝ), hs01⟩ : X) ∈ U) :
    ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) : ℝ)
      = ((φ.symm (⟨(ψ ⟨(s : ℝ), hs01⟩ : X), hψU⟩ : {x : X // x ∈ U}) : ORI 0 1) : ℝ) := by
  let Rb := {r : ℝ // r ∈ coordRealSet ψ U}
  let B := {s : ORI 0 1 // (ψ s : X) ∈ U}
  let W1 := {x : X // x ∈ V ∩ U}
  let W2 := {x : X // x ∈ U ∩ V}
  let A := {t : ORI 0 1 // (φ t : X) ∈ V}
  let Ra := {r : ℝ // r ∈ coordRealSet φ V}
  let x1 : Rb := (setEqSubtypeHomeoX hB).symm s
  have hx1 : (x1 : ℝ) = (s : ℝ) := by dsimp [x1]; rfl
  let x2 : B := (pullbackToRealCoordHomeo ψ).symm x1
  have hx2 : (x2 : ORI 0 1) = ⟨(s : ℝ), hs01⟩ := by
    rw [pullbackToRealCoordHomeo_symm_apply_val ψ x1]
    apply Subtype.ext
    exact hx1
  let x3 : W1 := overlapPullbackHomeo ψ x2
  have hx3 : (x3 : X) = (ψ ⟨(s : ℝ), hs01⟩ : X) := by
    rw [overlapPullbackHomeo_apply_val ψ x2, hx2]
  let x4 : W2 := setEqSubtypeHomeoX (Set.inter_comm V U) x3
  have hx4 : (x4 : X) = (x3 : X) := by
    dsimp [x4]
    rfl
  let x5 : A := (overlapPullbackHomeo φ).symm x4
  have hx5 : (x5 : ORI 0 1) = φ.symm (⟨(x4 : X), (x4.2).1⟩ : {x : X // x ∈ U}) :=
    overlapPullbackHomeo_symm_apply_val φ x4
  let x6 : Ra := pullbackToRealCoordHomeo φ x5
  have hx6 : (x6 : ℝ) = ((x5 : ORI 0 1) : ℝ) := pullbackToRealCoordHomeo_apply_val φ x5
  let x7 : {t : ℝ // t ∈ Ioo a b} := setEqSubtypeHomeoX hA x6
  have hx7 : (x7 : ℝ) = (x6 : ℝ) := by dsimp [x7]; rfl
  have hg : (transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) = x7 := by
    dsimp [transitionHomeo, x7, x6, x5, x4, x3, x2, x1]
  rw [hg]
  rw [hx7]
  rw [hx6]
  rw [hx5]
  -- goal: ((φ.symm (⟨(x4 : X), (x4.2).1⟩ : {x : X // x ∈ U})) : ORI 0 1) : ℝ) = RHS
  have hsubU : (⟨(x4 : X), (x4.2).1⟩ : {x : X // x ∈ U}) =
      ⟨(ψ ⟨(s : ℝ), hs01⟩ : X), hψU⟩ := by
    apply Subtype.ext
    exact hx4.trans hx3
  exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hsubU
theorem left_seam_hcomp {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 < a + ε := by
  intro ε hε
  rcases hg ε hε with ⟨δ, hδ0, hδ⟩
  let η : ℝ := min δ (min (1 - c) (d - c))
  have hη0 : 0 < η := by
    dsimp [η]
    have h1c : 0 < 1 - c := by linarith
    have hdc : 0 < d - c := by linarith
    positivity
  have hηδ : η ≤ δ := by dsimp [η]; exact min_le_left δ (min (1 - c) (d - c))
  have hη1 : η ≤ 1 - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (1 - c) (d - c))) (min_le_left (1 - c) (d - c))
  have hηd : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (1 - c) (d - c))) (min_le_right (1 - c) (d - c))
  refine ⟨η, hη0, hη1, hηd, ?_⟩
  intro w hw
  rcases hw with ⟨hwc, hwδ⟩
  have hwd : (w.1 : ℝ) < d := by
    have hle : c + η ≤ d := by linarith
    exact lt_of_lt_of_le hwδ hle
  have hs01 : (w.1 : ℝ) ∈ Ioo (0 : ℝ) 1 := w.1.2
  have hcd' : (w.1 : ℝ) ∈ Ioo c d := ⟨hwc, hwd⟩
  let s : {s : ℝ // s ∈ Ioo c d} := ⟨(w.1 : ℝ), hcd'⟩
  have hsw : (s : ℝ) < c + δ := by
    dsimp [s]
    have hle : c + η ≤ c + δ := by linarith
    exact lt_of_lt_of_le hwδ hle
  have hδs := hδ s hsw
  have hwlift : (⟨((s : ℝ) : ℝ), hs01⟩ : ORI 0 1) = w.1 := by
    apply Subtype.ext
    dsimp [s]
  have hψU : (ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X) ∈ U := by
    rw [hwlift]
    exact w.2
  have hc := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s hs01 hψU
  have hUel : (⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : {x : X // x ∈ U}) =
      ⟨(ψ w.1 : X), w.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : ORI 0 1 => (ψ z : X)) hwlift
  have hUeq2 : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((φ.symm ⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hUel.symm
  have hrew : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
    rw [hUeq2]
    exact hc.symm
  rw [hrew]
  exact hδs

/-- **The strict-left-seam case is closed**: in a Hausdorff ambient, both left
seams strict (`0 < a`, `0 < c`) together with the increasing-case left-end
approach of the transition (`hg`, from the first disjunct of
`intervalHomeo_left_end_reaches_endpoint` applied to `transitionHomeo`)
is impossible. -/
theorem not_T2_of_left_strict_seams_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (ha0s : 0 < a) (hc0s : 0 < c)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    False := by
  exact not_T2_of_left_strict_seams φ ψ hA hB ha0s hab hb1 hc0s hcd hd1
    (left_seam_hcomp φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hg)
theorem right_seam_approached_by_overlap_swap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) {c d : ℝ}
    (hshape : coordRealSet ψ U = Set.Ioo c d) (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d < 1) :
    ∀ M : Set X, M ∈ 𝓝 ((ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ d - c ∧ δ ≤ d ∧
        (∀ u : ORI 0 1, (u : ℝ) ∈ Ioo (d - δ) d →
          (ψ u : X) ∈ M ∧ (ψ u : X) ∈ U) := by
  intro M hM
  let x0 : ORI 0 1 := ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1⟩⟩
  have hg : Continuous (fun t : ORI 0 1 => (ψ t : X)) := Continuous.subtype_val ψ.continuous
  have hpre : (fun t : ORI 0 1 => (ψ t : X)) ⁻¹' M ∈ 𝓝 x0 :=
    hg.continuousAt.preimage_mem_nhds (by simpa [x0] using hM)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε0, hball⟩
  let δ : ℝ := min ε (min (d - c) d)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have hdc : 0 < d - c := by linarith
    have hdpos : 0 < d := by linarith
    positivity
  have hδε : δ ≤ ε := by dsimp [δ]; exact min_le_left ε (min (d - c) d)
  have hδc : δ ≤ d - c := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (d - c) d)) (min_le_left (d - c) d)
  have hδd : δ ≤ d := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (d - c) d)) (min_le_right (d - c) d)
  refine ⟨δ, hδ0, hδc, hδd, ?_⟩
  intro u hu
  rcases hu with ⟨hud, huδ⟩   -- d − δ < u < d
  have huε : dist u x0 < ε := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hlt : d - (u : ℝ) < ε := by
      have hle : d - δ ≤ (u : ℝ) := le_of_lt hud
      have hdδ : d - (u : ℝ) < δ := by linarith
      linarith
    have hneg : (u : ℝ) - d < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have huN : u ∈ (fun t : ORI 0 1 => (ψ t : X)) ⁻¹' M := hball huε
  have hψM : (ψ u : X) ∈ M := huN
  have hψU : (ψ u : X) ∈ U := by
    have huc : c < (u : ℝ) := by
      have hle : c ≤ d - δ := by linarith
      exact lt_of_le_of_lt hle hud
    have hud' : (u : ℝ) < d := huδ
    exact (coord_mem_iff_mem_coordRealSet ψ u.2).mpr (by
      rw [hshape]
      exact ⟨huc, hud'⟩)
  exact ⟨hψM, hψU⟩

/-- **The `hcomp` inequality for the left-`U` / right-`V` pair**: assuming the
decreasing-case right-end approach of the transition
(`hgR`: every `ε > 0` gives a `(d−δ, d)`-strip on which `g s < a + ε` —
the second disjunct of `intervalHomeo_right_end_reaches_endpoint` applied
to `transitionHomeo`), the `V`-overlap points near the right seam `ψ⟨d⟩`
have `U`-coordinate below `a + ε`. -/
theorem leftU_rightV_hcomp {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hgR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 < a + ε := by
  intro ε hε
  rcases hgR ε hε with ⟨δ, hδ0, hδ⟩
  let η : ℝ := min δ (min (d - c) d)
  have hη0 : 0 < η := by
    dsimp [η]
    have hdc : 0 < d - c := by linarith
    have hdpos : 0 < d := by linarith
    positivity
  have hηδ : η ≤ δ := by dsimp [η]; exact min_le_left δ (min (d - c) d)
  have hηc : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (d - c) d)) (min_le_left (d - c) d)
  have hηd : η ≤ d := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (d - c) d)) (min_le_right (d - c) d)
  refine ⟨η, hη0, hηc, hηd, ?_⟩
  intro w hw
  rcases hw with ⟨hwd, hwη⟩  -- d − η < w.1 < d
  have hwc : c < (w.1 : ℝ) := by
    have hle : c ≤ d - η := by linarith
    exact lt_of_le_of_lt hle hwd
  have hs01 : (w.1 : ℝ) ∈ Ioo (0 : ℝ) 1 := w.1.2
  have hcd' : (w.1 : ℝ) ∈ Ioo c d := ⟨hwc, hwη⟩
  let s : {s : ℝ // s ∈ Ioo c d} := ⟨(w.1 : ℝ), hcd'⟩
  have hsw : d - δ < (s : ℝ) := by
    dsimp [s]
    have hle : d - δ ≤ d - η := by linarith
    exact lt_of_le_of_lt hle hwd
  have hδs := hδ s hsw
  have hwlift : (⟨((s : ℝ) : ℝ), hs01⟩ : ORI 0 1) = w.1 := by
    apply Subtype.ext
    dsimp [s]
  have hψU : (ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X) ∈ U := by
    rw [hwlift]
    exact w.2
  have hc := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s hs01 hψU
  have hUel : (⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : {x : X // x ∈ U}) =
      ⟨(ψ w.1 : X), w.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : ORI 0 1 => (ψ z : X)) hwlift
  have hUeq2 : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((φ.symm ⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hUel.symm
  have hrew : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
    rw [hUeq2]
    exact hc.symm
  rw [hrew]
  exact hδs


/-- **Common point for the left-`U` / right-`V` pair**: if the `U`-left seam
is strict and the transition has the decreasing right-end approach
(`hcompR`), every neighbourhood of `φ⟨a⟩` and every neighbourhood of
`ψ⟨d⟩` share a common overlap point. -/
theorem seam_pair_common_point_rightV {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d < 1)
    (hcompR : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 < a + ε)
    (N : Set X) (hN : N ∈ 𝓝 ((φ ⟨a, ⟨ha0, lt_of_lt_of_le hab hb1⟩⟩ : X)))
    (M : Set X) (hM : M ∈ 𝓝 ((ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1⟩⟩ : X))) :
    (N ∩ M).Nonempty := by
  rcases left_seam_approached_by_overlap φ hA ha0 hab hb1 N hN with ⟨δ, hδ0, _hδ1a, _hδb, hδ⟩
  rcases hcompR δ hδ0 with ⟨ηc, hηc0, hηc1, hηcd, hηc⟩
  rcases right_seam_approached_by_overlap_swap ψ hB hc0 hcd hd1 M hM with ⟨ηm, hηm0, hηm1, hηmd, hηm⟩
  let η : ℝ := min ηm ηc
  have hη0 : 0 < η := by dsimp [η]; exact lt_min hηm0 hηc0
  have hηm1c : η ≤ d - c := by dsimp [η]; exact le_trans (min_le_left ηm ηc) hηm1
  have hηm1d : η ≤ d := by dsimp [η]; exact le_trans (min_le_left ηm ηc) hηmd
  have hηc1c : η ≤ d - c := by dsimp [η]; exact le_trans (min_le_right ηm ηc) hηc1
  have hηc1d : η ≤ d := by dsimp [η]; exact le_trans (min_le_right ηm ηc) hηcd
  have hη2pos : 0 < η / 2 := div_pos hη0 (by norm_num)
  have hη2lt : η / 2 < η := by linarith
  have hηleM : η ≤ ηm := by dsimp [η]; exact min_le_left ηm ηc
  have hηleC : η ≤ ηc := by dsimp [η]; exact min_le_right ηm ηc
  let w0 : ORI 0 1 := ⟨d - η / 2, ⟨by linarith, by linarith⟩⟩
  have hw0m : (w0 : ℝ) ∈ Ioo (d - ηm) d := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleM], by linarith⟩
  have hw0c : (w0 : ℝ) ∈ Ioo (d - ηc) d := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleC], by linarith⟩
  have hψU0 : (ψ w0 : X) ∈ U := by
    have hwc : c < (w0 : ℝ) := by
      have hle : c ≤ d - η := by linarith
      exact lt_of_le_of_lt hle (by dsimp [w0]; linarith)
    have hwd : (w0 : ℝ) < d := by dsimp [w0]; linarith
    exact (coord_mem_iff_mem_coordRealSet ψ w0.2).mpr (by
      rw [hB]
      exact ⟨hwc, hwd⟩)
  rcases hηm w0 hw0m with ⟨hψM, _hψU'⟩
  let u0 : ORI 0 1 := φ.symm ⟨(ψ w0 : X), hψU0⟩
  have htδ : (u0 : ℝ) < a + δ := hηc ⟨w0, hψU0⟩ (by simpa [u0] using hw0c)
  have htA : (u0 : ℝ) ∈ Ioo a b := by
    have heq : (φ u0 : X) = (ψ w0 : X) := by
      dsimp [u0]
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
    have hφV : (φ u0 : X) ∈ V := by
      rw [heq]
      exact (ψ w0).2
    have hu0 : (u0 : ℝ) ∈ coordRealSet φ V :=
      (coord_mem_iff_mem_coordRealSet φ u0.2).mp hφV
    rwa [hA] at hu0
  have hu0 : (u0 : ℝ) ∈ Ioo a (a + δ) := ⟨(by
    rcases htA with ⟨h1, _⟩
    exact h1), htδ⟩
  rcases hδ u0 hu0 with ⟨hφu0N, _⟩
  have heq2 : (φ u0 : X) = (ψ w0 : X) := by
    dsimp [u0]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
  refine ⟨(ψ w0 : X), ?_, ?_⟩
  · exact heq2 ▸ hφu0N
  · exact hψM

/-- **The left-`U` / right-`V` seam pair is impossible in a Hausdorff ambient**:
`0 < a`, `d < 1`, and the decreasing right-end approach `hgR` of the
transition give `False` under `[T2Space X]`. -/
theorem not_T2_of_leftU_rightV_decreasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (ha0s : 0 < a) (hd1s : d < 1)
    (hgR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    False := by
  let p : X := (φ ⟨a, ⟨ha0s, lt_of_lt_of_le hab hb1⟩⟩ : X)
  let q : X := (ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1s⟩⟩ : X)
  by_cases hpq : p = q
  · have hpV : p ∈ V := by
      rw [hpq]
      exact (ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1s⟩⟩).2
    have hφaV : ¬ ((φ ⟨a, ⟨ha0s, lt_of_lt_of_le hab hb1⟩⟩ : X) ∈ V) :=
      left_seam_not_in_V_of_shape φ hA ha0s hab hb1
    exact hφaV (by simpa [p] using hpV)
  · rcases t2_separation hpq with ⟨O, P, hOo, hPo, hpO, hqP, hdisj⟩
    have hNO : O ∈ 𝓝 p := hOo.mem_nhds hpO
    have hMP : P ∈ 𝓝 q := hPo.mem_nhds hqP
    have hcompR : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 < a + ε :=
      leftU_rightV_hcomp φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hgR
    rcases seam_pair_common_point_rightV φ ψ hA hB ha0s hab hb1 hc0 hcd hd1s hcompR
        O (by simpa [p] using hNO) P (by simpa [q] using hMP) with ⟨z, hzO, hzP⟩
    have hOem : O ∩ P = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
    have hz : z ∈ O ∩ P := ⟨hzO, hzP⟩
    rw [hOem] at hz
    exact hz
theorem right_seam_approached_by_overlap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 ≤ a) (hab : a < b) (hb1s : b < 1) :
    ∀ N : Set X, N ∈ 𝓝 ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ b - a ∧ δ ≤ b ∧
        (∀ u : ORI 0 1, (u : ℝ) ∈ Ioo (b - δ) b →
          (φ u : X) ∈ N ∧ (φ u : X) ∈ V) := by
  intro N hN
  let x0 : ORI 0 1 := ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩
  have hg : Continuous (fun t : ORI 0 1 => (φ t : X)) := Continuous.subtype_val φ.continuous
  have hpre : (fun t : ORI 0 1 => (φ t : X)) ⁻¹' N ∈ 𝓝 x0 :=
    hg.continuousAt.preimage_mem_nhds (by simpa [x0] using hN)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε0, hball⟩
  let δ : ℝ := min ε (min (b - a) b)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have hba : 0 < b - a := by linarith
    have hbpos : 0 < b := by linarith
    positivity
  have hδε : δ ≤ ε := by dsimp [δ]; exact min_le_left ε (min (b - a) b)
  have hδa : δ ≤ b - a := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (b - a) b)) (min_le_left (b - a) b)
  have hδb : δ ≤ b := by
    dsimp [δ]
    exact le_trans (min_le_right ε (min (b - a) b)) (min_le_right (b - a) b)
  refine ⟨δ, hδ0, hδa, hδb, ?_⟩
  intro u hu
  rcases hu with ⟨hub, huδ⟩   -- b − δ < u < b
  have huε : dist u x0 < ε := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hlt : b - (u : ℝ) < ε := by
      have hle : b - δ ≤ (u : ℝ) := le_of_lt hub
      have hdδ : b - (u : ℝ) < δ := by linarith
      linarith
    have hneg : (u : ℝ) - b < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have huN : u ∈ (fun t : ORI 0 1 => (φ t : X)) ⁻¹' N := hball huε
  have hφN : (φ u : X) ∈ N := huN
  have hφV : (φ u : X) ∈ V := by
    have hua : a < (u : ℝ) := by
      have hle : a ≤ b - δ := by linarith
      exact lt_of_le_of_lt hle hub
    have hub' : (u : ℝ) < b := huδ
    exact (coord_mem_iff_mem_coordRealSet φ u.2).mpr (by
      rw [hshape]
      exact ⟨hua, hub'⟩)
  exact ⟨hφN, hφV⟩

/-- **U-side right seam in the closure of the overlap**: the right seam point
of the `U`-chart lies in the closure of `U ∩ V` (midpoint witness in the
left strip). -/
theorem right_seam_mem_closure_overlap {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hshape : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 ≤ a) (hab : a < b) (hb1s : b < 1) :
    (φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X) ∈ closure (U ∩ V) := by
  rw [mem_closure_iff]
  intro N hNopen hxN
  have hNN : N ∈ 𝓝 (φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X) := hNopen.mem_nhds hxN
  rcases right_seam_approached_by_overlap φ hshape ha0 hab hb1s N hNN with
    ⟨δ, hδ0, hδa, hδb, hδ⟩
  let u : ORI 0 1 := ⟨b - δ / 2, ⟨by linarith, by linarith⟩⟩
  have hu : (u : ℝ) ∈ Ioo (b - δ) b := ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
  rcases hδ u hu with ⟨hφN, hφV⟩
  exact ⟨(φ u : X), ⟨hφN, ⟨(φ u).2, hφV⟩⟩⟩
theorem rightU_leftV_hcomp {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hgD2 : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 := by
  intro ε hε
  rcases hgD2 ε hε with ⟨δ, hδ0, hδ⟩
  let η : ℝ := min δ (min (1 - c) (d - c))
  have hη0 : 0 < η := by
    dsimp [η]
    have h1c : 0 < 1 - c := by linarith
    have hdc : 0 < d - c := by linarith
    positivity
  have hηδ : η ≤ δ := by dsimp [η]; exact min_le_left δ (min (1 - c) (d - c))
  have hη1 : η ≤ 1 - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (1 - c) (d - c))) (min_le_left (1 - c) (d - c))
  have hηd : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (1 - c) (d - c))) (min_le_right (1 - c) (d - c))
  refine ⟨η, hη0, hη1, hηd, ?_⟩
  intro w hw
  rcases hw with ⟨hwc, hwδ⟩
  have hwd : (w.1 : ℝ) < d := by
    have hle : c + η ≤ d := by linarith
    exact lt_of_lt_of_le hwδ hle
  have hs01 : (w.1 : ℝ) ∈ Ioo (0 : ℝ) 1 := w.1.2
  have hcd' : (w.1 : ℝ) ∈ Ioo c d := ⟨hwc, hwd⟩
  let s : {s : ℝ // s ∈ Ioo c d} := ⟨(w.1 : ℝ), hcd'⟩
  have hsw : (s : ℝ) < c + δ := by
    dsimp [s]
    have hle : c + η ≤ c + δ := by linarith
    exact lt_of_lt_of_le hwδ hle
  have hδs := hδ s hsw
  have hwlift : (⟨((s : ℝ) : ℝ), hs01⟩ : ORI 0 1) = w.1 := by
    apply Subtype.ext
    dsimp [s]
  have hψU : (ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X) ∈ U := by
    rw [hwlift]
    exact w.2
  have hc := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s hs01 hψU
  have hUel : (⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : {x : X // x ∈ U}) =
      ⟨(ψ w.1 : X), w.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : ORI 0 1 => (ψ z : X)) hwlift
  have hUeq2 : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((φ.symm ⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hUel.symm
  have hrew : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
    rw [hUeq2]
    exact hc.symm
  rw [hrew]
  exact hδs

/-- **Common point for the right-`U` / left-`V` pair**: if the `U`-right seam
is strict and the transition has the decreasing left-end approach
(`hcompD2`), every neighbourhood of `φ⟨b⟩` and every neighbourhood of
`ψ⟨c⟩` share a common overlap point. -/
theorem seam_pair_common_point_rightU_leftV {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1s : b < 1)
    (hc0s : 0 < c) (hcd : c < d) (hd1 : d ≤ 1)
    (hcompD2 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1)
    (N : Set X) (hN : N ∈ 𝓝 ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X)))
    (M : Set X) (hM : M ∈ 𝓝 ((ψ ⟨c, ⟨hc0s, lt_of_lt_of_le hcd hd1⟩⟩ : X))) :
    (N ∩ M).Nonempty := by
  rcases right_seam_approached_by_overlap φ hA ha0 hab hb1s N hN with ⟨δ, hδ0, _hδa, _hδb, hδ⟩
  rcases hcompD2 δ hδ0 with ⟨ηc, hηc0, hηc1, hηcd, hηc⟩
  rcases left_seam_approached_by_overlap_swap ψ hB hc0s hcd hd1 M hM with ⟨ηm, hηm0, hηm1, hηmd, hηm⟩
  let η : ℝ := min ηm ηc
  have hη0 : 0 < η := by dsimp [η]; exact lt_min hηm0 hηc0
  have hη2pos : 0 < η / 2 := div_pos hη0 (by norm_num)
  have hη2lt : η / 2 < η := by linarith
  have hηleM : η ≤ ηm := by dsimp [η]; exact min_le_left ηm ηc
  have hηleC : η ≤ ηc := by dsimp [η]; exact min_le_right ηm ηc
  have hη1c : η ≤ 1 - c := by
    dsimp [η]
    exact le_trans (min_le_left ηm ηc) hηm1
  have hηdc : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_left ηm ηc) hηmd
  let w0 : ORI 0 1 := ⟨c + η / 2, ⟨by linarith, by linarith⟩⟩
  have hw0m : (w0 : ℝ) ∈ Ioo c (c + ηm) := by
    dsimp [w0]
    exact ⟨by linarith, by linarith [hη2lt, hηleM]⟩
  have hw0c : (w0 : ℝ) ∈ Ioo c (c + ηc) := by
    dsimp [w0]
    exact ⟨by linarith, by linarith [hη2lt, hηleC]⟩
  have hψU0 : (ψ w0 : X) ∈ U := by
    have hwd : (w0 : ℝ) < d := by
      have hle : c + η ≤ d := by linarith
      exact lt_of_lt_of_le (by dsimp [w0]; linarith) hle
    exact (coord_mem_iff_mem_coordRealSet ψ w0.2).mpr (by
      rw [hB]
      exact ⟨by dsimp [w0]; linarith, hwd⟩)
  rcases hηm w0 hw0m with ⟨hψM, _hψU'⟩
  let u0 : ORI 0 1 := φ.symm ⟨(ψ w0 : X), hψU0⟩
  have htδ : b - δ < (u0 : ℝ) := hηc ⟨w0, hψU0⟩ (by simpa [u0] using hw0c)
  have htA : (u0 : ℝ) ∈ Ioo a b := by
    have heq : (φ u0 : X) = (ψ w0 : X) := by
      dsimp [u0]
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
    have hφV : (φ u0 : X) ∈ V := by
      rw [heq]
      exact (ψ w0).2
    have hu0 : (u0 : ℝ) ∈ coordRealSet φ V :=
      (coord_mem_iff_mem_coordRealSet φ u0.2).mp hφV
    rwa [hA] at hu0
  have hu0 : (u0 : ℝ) ∈ Ioo (b - δ) b := ⟨htδ, (by
    rcases htA with ⟨_h1, h2⟩
    exact h2)⟩
  rcases hδ u0 hu0 with ⟨hφu0N, _⟩
  have heq2 : (φ u0 : X) = (ψ w0 : X) := by
    dsimp [u0]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
  refine ⟨(ψ w0 : X), ?_, ?_⟩
  · exact heq2 ▸ hφu0N
  · exact hψM

/-- **The right-`U` / left-`V` seam pair is impossible in a Hausdorff
ambient**: `b < 1`, `0 < c`, and the decreasing left-end approach `hgD2`
of the transition give `False` under `[T2Space X]`. -/
theorem not_T2_of_rightU_leftV_decreasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hb1s : b < 1) (hc0s : 0 < c)
    (hgD2 : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    False := by
  let p : X := (φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X)
  let q : X := (ψ ⟨c, ⟨hc0s, lt_of_lt_of_le hcd hd1⟩⟩ : X)
  by_cases hpq : p = q
  · have hpV : p ∈ V := by
      rw [hpq]
      exact (ψ ⟨c, ⟨hc0s, lt_of_lt_of_le hcd hd1⟩⟩).2
    have hφbV : ¬ ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X) ∈ V) :=
      right_seam_not_in_V_of_shape φ hA ha0 hab hb1s
    exact hφbV (by simpa [p] using hpV)
  · rcases t2_separation hpq with ⟨O, P, hOo, hPo, hpO, hqP, hdisj⟩
    have hNO : O ∈ 𝓝 p := hOo.mem_nhds hpO
    have hMP : P ∈ 𝓝 q := hPo.mem_nhds hqP
    have hcompD2 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 - c ∧ η ≤ d - c ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo c (c + η) →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 :=
      rightU_leftV_hcomp φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hgD2
    rcases seam_pair_common_point_rightU_leftV φ ψ hA hB ha0 hab hb1s hc0s hcd hd1 hcompD2
        O (by simpa [p] using hNO) P (by simpa [q] using hMP) with ⟨z, hzO, hzP⟩
    have hOem : O ∩ P = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
    have hz : z ∈ O ∩ P := ⟨hzO, hzP⟩
    rw [hOem] at hz
    exact hz
theorem rightU_rightV_hcomp {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hgD1 : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 := by
  intro ε hε
  rcases hgD1 ε hε with ⟨δ, hδ0, hδ⟩
  let η : ℝ := min δ (min (d - c) d)
  have hη0 : 0 < η := by
    dsimp [η]
    have hdc : 0 < d - c := by linarith
    have hdpos : 0 < d := by linarith
    positivity
  have hηδ : η ≤ δ := by dsimp [η]; exact min_le_left δ (min (d - c) d)
  have hηc : η ≤ d - c := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (d - c) d)) (min_le_left (d - c) d)
  have hηd : η ≤ d := by
    dsimp [η]
    exact le_trans (min_le_right δ (min (d - c) d)) (min_le_right (d - c) d)
  refine ⟨η, hη0, hηc, hηd, ?_⟩
  intro w hw
  rcases hw with ⟨hwd, hwη⟩  -- d − η < w.1 < d
  have hwc : c < (w.1 : ℝ) := by
    have hle : c ≤ d - η := by linarith
    exact lt_of_le_of_lt hle hwd
  have hs01 : (w.1 : ℝ) ∈ Ioo (0 : ℝ) 1 := w.1.2
  have hcd' : (w.1 : ℝ) ∈ Ioo c d := ⟨hwc, hwη⟩
  let s : {s : ℝ // s ∈ Ioo c d} := ⟨(w.1 : ℝ), hcd'⟩
  have hsw : d - δ < (s : ℝ) := by
    dsimp [s]
    have hle : d - δ ≤ d - η := by linarith
    exact lt_of_le_of_lt hle hwd
  have hδs := hδ s hsw
  have hwlift : (⟨((s : ℝ) : ℝ), hs01⟩ : ORI 0 1) = w.1 := by
    apply Subtype.ext
    dsimp [s]
  have hψU : (ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X) ∈ U := by
    rw [hwlift]
    exact w.2
  have hc := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s hs01 hψU
  have hUel : (⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : {x : X // x ∈ U}) =
      ⟨(ψ w.1 : X), w.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : ORI 0 1 => (ψ z : X)) hwlift
  have hUeq2 : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((φ.symm ⟨(ψ ⟨((s : ℝ) : ℝ), hs01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hUel.symm
  have hrew : ((φ.symm ⟨(ψ w.1 : X), w.2⟩ : ORI 0 1) : ℝ) =
      ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
    rw [hUeq2]
    exact hc.symm
  rw [hrew]
  exact hδs

/-- **Common point for the right-`U` / right-`V` pair**: if both right seams
are strict and the transition has the increasing right-end approach
(`hcompD1`), every neighbourhood of `φ⟨b⟩` and every neighbourhood of
`ψ⟨d⟩` share a common overlap point. -/
theorem seam_pair_common_point_rightU_rightV {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1s : b < 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1s : d < 1)
    (hcompD1 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1)
    (N : Set X) (hN : N ∈ 𝓝 ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X)))
    (M : Set X) (hM : M ∈ 𝓝 ((ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1s⟩⟩ : X))) :
    (N ∩ M).Nonempty := by
  rcases right_seam_approached_by_overlap φ hA ha0 hab hb1s N hN with ⟨δ, hδ0, _hδa, _hδb, hδ⟩
  rcases hcompD1 δ hδ0 with ⟨ηc, hηc0, hηc1, hηcd, hηc⟩
  rcases right_seam_approached_by_overlap_swap ψ hB hc0 hcd hd1s M hM with ⟨ηm, hηm0, hηm1, hηmd, hηm⟩
  let η : ℝ := min ηm ηc
  have hη0 : 0 < η := by dsimp [η]; exact lt_min hηm0 hηc0
  have hη2pos : 0 < η / 2 := div_pos hη0 (by norm_num)
  have hη2lt : η / 2 < η := by linarith
  have hηleM : η ≤ ηm := by dsimp [η]; exact min_le_left ηm ηc
  have hηleC : η ≤ ηc := by dsimp [η]; exact min_le_right ηm ηc
  let w0 : ORI 0 1 := ⟨d - η / 2, ⟨by linarith, by linarith⟩⟩
  have hw0m : (w0 : ℝ) ∈ Ioo (d - ηm) d := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleM], by linarith⟩
  have hw0c : (w0 : ℝ) ∈ Ioo (d - ηc) d := by
    dsimp [w0]
    exact ⟨by linarith [hη2lt, hηleC], by linarith⟩
  have hψU0 : (ψ w0 : X) ∈ U := by
    have hwc : c < (w0 : ℝ) := by
      have hle : c ≤ d - η := by linarith
      exact lt_of_le_of_lt hle (by dsimp [w0]; linarith)
    have hwd : (w0 : ℝ) < d := by dsimp [w0]; linarith
    exact (coord_mem_iff_mem_coordRealSet ψ w0.2).mpr (by
      rw [hB]
      exact ⟨hwc, hwd⟩)
  rcases hηm w0 hw0m with ⟨hψM, _hψU'⟩
  let u0 : ORI 0 1 := φ.symm ⟨(ψ w0 : X), hψU0⟩
  have htδ : b - δ < (u0 : ℝ) := hηc ⟨w0, hψU0⟩ (by simpa [u0] using hw0c)
  have htA : (u0 : ℝ) ∈ Ioo a b := by
    have heq : (φ u0 : X) = (ψ w0 : X) := by
      dsimp [u0]
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
    have hφV : (φ u0 : X) ∈ V := by
      rw [heq]
      exact (ψ w0).2
    have hu0 : (u0 : ℝ) ∈ coordRealSet φ V :=
      (coord_mem_iff_mem_coordRealSet φ u0.2).mp hφV
    rwa [hA] at hu0
  have hu0 : (u0 : ℝ) ∈ Ioo (b - δ) b := ⟨htδ, (by
    rcases htA with ⟨_h1, h2⟩
    exact h2)⟩
  rcases hδ u0 hu0 with ⟨hφu0N, _⟩
  have heq2 : (φ u0 : X) = (ψ w0 : X) := by
    dsimp [u0]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨(ψ w0 : X), hψU0⟩)
  refine ⟨(ψ w0 : X), ?_, ?_⟩
  · exact heq2 ▸ hφu0N
  · exact hψM

/-- **The right-`U` / right-`V` seam pair is impossible in a Hausdorff
ambient**: `b < 1`, `d < 1`, and the increasing right-end approach `hgD1`
of the transition give `False` under `[T2Space X]`. -/
theorem not_T2_of_rightU_rightV_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hb1s : b < 1) (hd1s : d < 1)
    (hgD1 : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    False := by
  let p : X := (φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X)
  let q : X := (ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1s⟩⟩ : X)
  by_cases hpq : p = q
  · have hpV : p ∈ V := by
      rw [hpq]
      exact (ψ ⟨d, ⟨lt_of_le_of_lt hc0 hcd, hd1s⟩⟩).2
    have hφbV : ¬ ((φ ⟨b, ⟨lt_of_le_of_lt ha0 hab, hb1s⟩⟩ : X) ∈ V) :=
      right_seam_not_in_V_of_shape φ hA ha0 hab hb1s
    exact hφbV (by simpa [p] using hpV)
  · rcases t2_separation hpq with ⟨O, P, hOo, hPo, hpO, hqP, hdisj⟩
    have hNO : O ∈ 𝓝 p := hOo.mem_nhds hpO
    have hMP : P ∈ 𝓝 q := hPo.mem_nhds hqP
    have hcompD1 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ d - c ∧ η ≤ d ∧
        ∀ w : {s : ORI 0 1 // (ψ s : X) ∈ U}, (w.1 : ℝ) ∈ Ioo (d - η) d →
          b - ε < (φ.symm (⟨(ψ w.1 : X), w.2⟩ : {x : X // x ∈ U}) : ORI 0 1).1 :=
      rightU_rightV_hcomp φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hgD1
    rcases seam_pair_common_point_rightU_rightV φ ψ hA hB ha0 hab hb1s hc0 hcd hd1s hcompD1
        O (by simpa [p] using hNO) P (by simpa [q] using hMP) with ⟨z, hzO, hzP⟩
    have hOem : O ∩ P = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
    have hz : z ∈ O ∩ P := ⟨hzO, hzP⟩
    rw [hOem] at hz
    exact hz
theorem transitionEndApproach {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε)
  ∨ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ))
  ∨ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε)
  ∨ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) := by
  rcases intervalHomeo_left_end_reaches_endpoint hab hcd
      (transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) with hl | hr
  · exact Or.inl hl
  · exact Or.inr (Or.inl hr)

/-- The right-end theorem supplies the remaining two disjuncts: as `s → d⁻`,
`g s` approaches `b` (increasing case) or `a` (decreasing case). -/
theorem transitionEndApproach_right {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε)
  ∨ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) := by
  rcases intervalHomeo_right_end_reaches_endpoint hab hcd
      (transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) with hb | ha
  · exact Or.inr hb
  · exact Or.inl ha
theorem left_end_strict_pair_forbidden {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    ¬ (0 < a ∧ 0 < c) := by
  intro hboth
  exact not_T2_of_left_strict_seams_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.1 hboth.2 hl

/-- **Assembly atom (left-U / right-V)**: with the decreasing right-end approach
(disjunct 3: `g s < a+ε` as `s → d⁻`), `0 < a` and `d < 1` cannot both hold
in a Hausdorff ambient. -/
theorem leftU_rightV_strict_pair_forbidden {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hr : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    ¬ (0 < a ∧ d < 1) := by
  intro hboth
  exact not_T2_of_leftU_rightV_decreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.1 hboth.2 hr

/-- **Assembly atom (right-U / left-V)**: with the decreasing left-end approach
(disjunct 2: `b − ε < g s` as `s → c⁺`), `b < 1` and `0 < c` cannot both
hold in a Hausdorff ambient. -/
theorem rightU_leftV_strict_pair_forbidden {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    ¬ (b < 1 ∧ 0 < c) := by
  intro hboth
  exact not_T2_of_rightU_leftV_decreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.1 hboth.2 hl

/-- **Assembly atom (right-right)**: with the increasing right-end approach
(disjunct 4: `b − ε < g s` as `s → d⁻`), the two right seams cannot both be
strict in a Hausdorff ambient. -/
theorem right_end_strict_pair_forbidden {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hr : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    ¬ (b < 1 ∧ d < 1) := by
  intro hboth
  exact not_T2_of_rightU_rightV_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.1 hboth.2 hr
theorem left_strict_pair_forbidden_of_leftToB {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) :
    ¬ (0 < a ∧ 0 < c ∧ b < 1) := by
  intro hboth
  exact not_T2_of_rightU_leftV_decreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.2.2 hboth.2.1 hl

/-- **Left-left strict pair under the decreasing right-end approach**: if the
transition maps the right end of the `V`-chart to the left end of the
`U`-chart (disjunct 3) and the `V`-right seam is strict (`d < 1`), then the
two left seams cannot both be strict in a Hausdorff ambient (the pair
`(φ⟨a⟩, ψ⟨d⟩)` of S171 closes it). -/
theorem left_strict_pair_forbidden_of_rightToA {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hr : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) :
    ¬ (0 < a ∧ 0 < c ∧ d < 1) := by
  intro hboth
  exact not_T2_of_leftU_rightV_decreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
    hboth.1 hboth.2.2 hr
def TransitionIncreasing {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
        b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ))

/-- **Under the consistent orientation, the two left seams cannot both be
strict** (`¬ (0 < a ∧ 0 < c)`): the left end of the overlap is an end of at
least one chart (S170 with the increasing left-end disjunct). -/
theorem left_seam_pair_free_of_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hinc : TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) :
    ¬ (0 < a ∧ 0 < c) := by
  exact left_end_strict_pair_forbidden φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc.1

/-- **Under the consistent orientation, the two right seams cannot both be
strict** (`¬ (b < 1 ∧ d < 1)`): the right end of the overlap is an end of at
least one chart (S174 with the increasing right-end disjunct). -/
theorem right_seam_pair_free_of_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hinc : TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) :
    ¬ (b < 1 ∧ d < 1) := by
  exact right_end_strict_pair_forbidden φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc.2

/-- **The packaging claim under the consistent orientation**: at each end of
the overlap (measured consistently), at least one chart's overlap reaches
that chart's end — equivalently both strict pairs are excluded. -/
theorem ends_of_at_least_one_chart_of_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hinc : TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) :
    (¬ (0 < a ∧ 0 < c)) ∧ (¬ (b < 1 ∧ d < 1)) := by
  constructor
  · exact left_seam_pair_free_of_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc
  · exact right_seam_pair_free_of_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc
theorem transitionHomeo_leftToA_of_strictMono {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) := by
  set g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  have hmono' : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} => ((g x) : ℝ)) := by
    simpa [g] using hmono
  rcases intervalHomeo_left_end_reaches_endpoint hab hcd g with hl | hr
  · simpa [g] using hl
  · exfalso
    let s₀ : {x : ℝ // x ∈ Ioo c d} := ⟨(c + d) / 2, ⟨by linarith, by linarith⟩⟩
    have hltb : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < b := (g s₀).2.2
    let ε : ℝ := (b - ((g s₀) : ℝ)) / 2
    have hε0 : 0 < ε := by
      dsimp [ε]
      have : 0 < b - ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by linarith
      positivity
    rcases hr ε hε0 with ⟨δ, hδ0, hδ⟩
    have hmin : c < min (c + δ) ((s₀ : ℝ)) := by
      exact lt_min (by linarith) (by dsimp [s₀]; linarith)
    rcases exists_between hmin with ⟨r, hcr, hrm⟩
    have hrδ : r < c + δ := lt_of_lt_of_le hrm (min_le_left (c + δ) (s₀ : ℝ))
    have hrs0 : r < (s₀ : ℝ) := lt_of_lt_of_le hrm (min_le_right (c + δ) (s₀ : ℝ))
    have hrd : r < d := lt_of_lt_of_le hrs0 (by dsimp [s₀]; linarith)
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hcd' : r ∈ Ioo c d := ⟨hcr, hrd⟩
    let s : {x : ℝ // x ∈ Ioo c d} := ⟨r, hcd'⟩
    have hsδ : (s : ℝ) < c + δ := by dsimp [s]; exact hrδ
    have hbε := hδ s hsδ
    have hs0 : (s : ℝ) < (s₀ : ℝ) := by dsimp [s]; exact hrs0
    have hmono_s : ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) :=
      hmono' hs0
    have hgt : b - ε < ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by simpa [g] using hbε
    have hltgs : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < b - ε := by
      dsimp [ε]
      linarith
    linarith

/-- A strictly increasing transition map sends the right end of the domain to
the right end of the range: `b − ε < g s` eventually as `s → d⁻` (the
increasing disjunct of `intervalHomeo_right_end_reaches_endpoint`, the
reversed disjunct being impossible under `StrictMono`). -/
theorem transitionHomeo_rightToB_of_strictMono {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) := by
  set g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  have hmono' : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} => ((g x) : ℝ)) := by
    simpa [g] using hmono
  rcases intervalHomeo_right_end_reaches_endpoint hab hcd g with hb | ha
  · simpa [g] using hb
  · exfalso
    let s₀ : {x : ℝ // x ∈ Ioo c d} := ⟨(c + d) / 2, ⟨by linarith, by linarith⟩⟩
    have hgta : a < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := (g s₀).2.1
    let ε : ℝ := (((g s₀) : ℝ) - a) / 2
    have hε0 : 0 < ε := by
      dsimp [ε]
      have : 0 < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) - a := by linarith
      positivity
    rcases ha ε hε0 with ⟨δ, hδ0, hδ⟩
    have hmaxlt : max (d - δ) ((s₀ : ℝ)) < d := by
      exact max_lt (by linarith) (by dsimp [s₀]; linarith)
    rcases exists_between hmaxlt with ⟨r, hmaxr, hrd⟩
    have hrδ : d - δ < r := lt_of_le_of_lt (le_max_left (d - δ) (s₀ : ℝ)) hmaxr
    have hrs0 : (s₀ : ℝ) < r := lt_of_le_of_lt (le_max_right (d - δ) (s₀ : ℝ)) hmaxr
    have hcr : c < r := lt_trans (by dsimp [s₀]; linarith : c < (s₀ : ℝ)) hrs0
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hcd' : r ∈ Ioo c d := ⟨hcr, hrd⟩
    let s : {x : ℝ // x ∈ Ioo c d} := ⟨r, hcd'⟩
    have hsδ : d - δ < (s : ℝ) := by dsimp [s]; exact hrδ
    have hltgs2 := hδ s hsδ
    have hs0 : (s₀ : ℝ) < (s : ℝ) := by dsimp [s]; exact hrs0
    have hmono_s : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) :=
      hmono' hs0
    have hlt : ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) < a + ε := by simpa [g] using hltgs2
    have haε : a + ε < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
      dsimp [ε]
      linarith
    linarith

/-- **The StrictMono branch realizes the consistent orientation**: if the
transition coordinate map is strictly increasing then `TransitionIncreasing`
holds (both increasing disjuncts of the end theorems, via the two helpers
above). -/
theorem increasing_of_strictMono {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 := by
  constructor
  · exact transitionHomeo_leftToA_of_strictMono φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
  · exact transitionHomeo_rightToB_of_strictMono φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
def TransitionDecreasing {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
        b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε)

/-- A strictly antitone transition map sends the left end of the domain to the
right end of the range: `b − ε < g s` eventually as `s → c⁺` (the
decreasing disjunct of `intervalHomeo_left_end_reaches_endpoint`, the
increasing disjunct being impossible under `StrictAnti`). -/
theorem transitionHomeo_leftToB_of_strictAnti {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hanti : StrictAnti (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, (s : ℝ) < c + δ →
          b - ε < ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ)) := by
  set g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  have hanti' : StrictAnti (fun x : {x : ℝ // x ∈ Ioo c d} => ((g x) : ℝ)) := by
    simpa [g] using hanti
  rcases intervalHomeo_left_end_reaches_endpoint hab hcd g with hl | hr
  · exfalso
    let s₀ : {x : ℝ // x ∈ Ioo c d} := ⟨(c + d) / 2, ⟨by linarith, by linarith⟩⟩
    have hgta : a < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := (g s₀).2.1
    let ε : ℝ := (((g s₀) : ℝ) - a) / 2
    have hε0 : 0 < ε := by
      dsimp [ε]
      have : 0 < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) - a := by linarith
      positivity
    rcases hl ε hε0 with ⟨δ, hδ0, hδ⟩
    have hmin : c < min (c + δ) ((s₀ : ℝ)) := by
      exact lt_min (by linarith) (by dsimp [s₀]; linarith)
    rcases exists_between hmin with ⟨r, hcr, hrm⟩
    have hrδ : r < c + δ := lt_of_lt_of_le hrm (min_le_left (c + δ) (s₀ : ℝ))
    have hrs0 : r < (s₀ : ℝ) := lt_of_lt_of_le hrm (min_le_right (c + δ) (s₀ : ℝ))
    have hrd : r < d := lt_of_lt_of_le hrs0 (by dsimp [s₀]; linarith)
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hcd' : r ∈ Ioo c d := ⟨hcr, hrd⟩
    let s : {x : ℝ // x ∈ Ioo c d} := ⟨r, hcd'⟩
    have hsδ : (s : ℝ) < c + δ := by dsimp [s]; exact hrδ
    have hlt1 := hδ s hsδ
    have hs0 : (s : ℝ) < (s₀ : ℝ) := by dsimp [s]; exact hrs0
    have hanti_s : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) :=
      hanti' hs0
    have hlt2 : ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) < a + ε := by simpa [g] using hlt1
    have haε : a + ε < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by
      dsimp [ε]
      linarith
    linarith
  · simpa [g] using hr

/-- A strictly antitone transition map sends the right end of the domain to the
left end of the range: `g s < a + ε` eventually as `s → d⁻` (the
decreasing disjunct of `intervalHomeo_right_end_reaches_endpoint`, the
increasing disjunct being impossible under `StrictAnti`). -/
theorem transitionHomeo_rightToA_of_strictAnti {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hanti : StrictAnti (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {s : ℝ // s ∈ Ioo c d}, d - δ < (s : ℝ) →
          ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s) : ℝ) < a + ε) := by
  set g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  have hanti' : StrictAnti (fun x : {x : ℝ // x ∈ Ioo c d} => ((g x) : ℝ)) := by
    simpa [g] using hanti
  rcases intervalHomeo_right_end_reaches_endpoint hab hcd g with hb | ha
  · exfalso
    let s₀ : {x : ℝ // x ∈ Ioo c d} := ⟨(c + d) / 2, ⟨by linarith, by linarith⟩⟩
    have hltb : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < b := (g s₀).2.2
    let ε : ℝ := (b - ((g s₀) : ℝ)) / 2
    have hε0 : 0 < ε := by
      dsimp [ε]
      have : 0 < b - ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by linarith
      positivity
    rcases hb ε hε0 with ⟨δ, hδ0, hδ⟩
    have hmaxlt : max (d - δ) ((s₀ : ℝ)) < d := by
      exact max_lt (by linarith) (by dsimp [s₀]; linarith)
    rcases exists_between hmaxlt with ⟨r, hmaxr, hrd⟩
    have hrδ : d - δ < r := lt_of_le_of_lt (le_max_left (d - δ) (s₀ : ℝ)) hmaxr
    have hrs0 : (s₀ : ℝ) < r := lt_of_le_of_lt (le_max_right (d - δ) (s₀ : ℝ)) hmaxr
    have hcr : c < r := lt_trans (by dsimp [s₀]; linarith : c < (s₀ : ℝ)) hrs0
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hcd' : r ∈ Ioo c d := ⟨hcr, hrd⟩
    let s : {x : ℝ // x ∈ Ioo c d} := ⟨r, hcd'⟩
    have hsδ : d - δ < (s : ℝ) := by dsimp [s]; exact hrδ
    have hgt1 := hδ s hsδ
    have hs0 : (s₀ : ℝ) < (s : ℝ) := by dsimp [s]; exact hrs0
    have hanti_s : ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) < ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) :=
      hanti' hs0
    have hgt2 : b - ε < ((g s : {t : ℝ // t ∈ Ioo a b}) : ℝ) := by simpa [g] using hgt1
    have hltgs : ((g s₀ : {t : ℝ // t ∈ Ioo a b}) : ℝ) < b - ε := by
      dsimp [ε]
      linarith
    linarith
  · simpa [g] using ha

/-- **The StrictAnti branch realises the decreasing orientation**: if the
transition coordinate map is strictly antitone then `TransitionDecreasing`
holds. -/
theorem decreasing_of_strictAnti {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hanti : StrictAnti (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x) : ℝ))) :
    TransitionDecreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 := by
  constructor
  · exact transitionHomeo_leftToB_of_strictAnti φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hanti
  · exact transitionHomeo_rightToA_of_strictAnti φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hanti

/-! ## S181 — chart-orientation reversal (the orientation-normalization half
of the two-arc assembly)

Under a DECREASING transition the seam-pair atoms of S170–S177 forbid only
the pairs the actual transition behavior joins, so the "each overlap end is
an end of at least one chart" packaging holds only in a CONSISTENT
orientation (S178 `TransitionIncreasing`; S177 finding).  S179/S180 closed
the monotone dichotomy: a strictly monotone transition realises
`TransitionIncreasing`, a strictly antitone one realises
`TransitionDecreasing`.  This section proves the S181 chart-orientation
lemma: **reversing the orientation of the `V`-chart** — composing it with
the coordinate reflection `u ↦ 1 − u` of S165 (`reversedChart`, built from
`intervalReflection 0 1`) — turns a decreasing transition into an
increasing one, mirroring the overlap shape `(c,d)` to `(1−d, 1−c)`.
Concretely:

1. **`reversedChart`** + `reversedChart_apply_val` (the chart whose
   coordinate is `u ↦ 1 − u`);
2. **`coordRealSet_reversedShape`** — in the reversed chart the overlap is
   the mirror interval `(1−d, 1−c)`;
3. **`transitionHomeo_reversedCoord`** — the value identity: the new
   transition at `t` equals the old transition at `reflectCoord c d t`
   (the reflected parameter `1 − t`, S181 coordinate lemma of
   IntervalHomeoEnds);
4. **`transitionDecreasing_reversed_increasing`** — the S181 theorem: a
   `TransitionDecreasing` transition becomes `TransitionIncreasing` after
   the reversal (proof: the coordinate-level
   `increasing_ends_after_reflection` + the value identity);
5. **`transition_increasing_or_decreasing`** — the orientation dichotomy
   of any two charts (S165 monotonicity + S179/S180 branches);
6. **`exists_increasing_orientation`** — the orientation-normalization
   packaging: either the transition is already increasing or it is
   increasing after reversing `ψ`, so the consistent-orientation
   hypothesis costs nothing (one chart orientation can always be chosen to
   realise it); then `ends_of_at_least_one_chart_of_increasing` (S178)
   applies to the normalised pair.

Everything here is verified (no axioms, no `sorry`).
-/

noncomputable def reversedChart {X : Type*} [TopologicalSpace X] {V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) : ORI 0 1 ≃ₜ {x : X // x ∈ V} :=
  (intervalReflection (0 : ℝ) 1).trans ψ

theorem reversedChart_apply_val {X : Type*} [TopologicalSpace X] {V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) (t : ORI 0 1) :
    ((reversedChart ψ t : {x : X // x ∈ V}) : X) = (ψ (intervalReflection (0 : ℝ) 1 t) : X) := by
  rfl

/-- **Reversed shape**: in the reversed chart the overlap is the mirror
interval `(1−d, 1−c)`. -/
theorem coordRealSet_reversedShape {X : Type*} [TopologicalSpace X] {V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) (U : Set X)
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hB : coordRealSet ψ U = Set.Ioo c d) :
    coordRealSet (reversedChart ψ) U = Set.Ioo (1 - d) (1 - c) := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨t, htU, htv⟩
    let s : ORI 0 1 := intervalReflection (0 : ℝ) 1 t
    have hsψU : (ψ s : X) ∈ U := by
      have hψt : ((reversedChart ψ t : {x : X // x ∈ V}) : X) = (ψ s : X) := by
        dsimp [s]
        exact reversedChart_apply_val ψ t
      rw [← hψt]
      exact htU
    have hmem : (s : ℝ) ∈ coordRealSet ψ U := by
      have hiff := coord_mem_iff_mem_coordRealSet (φ := ψ) (V := U) (r := (s : ℝ)) s.2
      have hψs : (ψ ⟨(s : ℝ), s.2⟩ : X) ∈ U := by
        have hs_eq : (⟨(s : ℝ), s.2⟩ : ORI 0 1) = s := by apply Subtype.ext; rfl
        rwa [hs_eq]
      exact hiff.mp hψs
    have hcd' : (s : ℝ) ∈ Set.Ioo c d := by simpa [hB] using hmem
    have hval : (s : ℝ) = 1 - (t : ℝ) := by
      dsimp [s]
      rw [intervalReflection_apply]
      ring
    rcases hcd' with ⟨hcs, hsd⟩
    constructor <;> linarith
  · intro hr
    rcases hr with ⟨hlo, hhi⟩
    have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · have h1d : 0 ≤ 1 - d := by linarith
        linarith
      · have h1c : 1 - c ≤ 1 := by linarith
        linarith
    let t : ORI 0 1 := ⟨r, hr01⟩
    have hmem' : (ψ (intervalReflection (0 : ℝ) 1 t) : X) ∈ U := by
      let s : ORI 0 1 := intervalReflection (0 : ℝ) 1 t
      have hs01 : (s : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := s.2
      have hiff := coord_mem_iff_mem_coordRealSet (φ := ψ) (V := U) (r := (s : ℝ)) hs01
      have hsval : (s : ℝ) = 1 - r := by
        dsimp [s, t]
        rw [intervalReflection_apply]
        ring
      have hscd : (s : ℝ) ∈ Set.Ioo c d := by
        rw [hsval]
        constructor <;> linarith
      have hψs : (ψ ⟨(s : ℝ), hs01⟩ : X) ∈ U := hiff.mpr (by simpa [hB] using hscd)
      have hs_eq : (⟨(s : ℝ), hs01⟩ : ORI 0 1) = s := by apply Subtype.ext; rfl
      change (ψ s : X) ∈ U
      rw [← hs_eq]
      exact hψs
    refine ⟨t, ?_, rfl⟩
    -- goal: t ∈ {u | (reversedChart ψ u : X) ∈ U}; reduce and rewrite
    change ((reversedChart ψ t : {x : X // x ∈ V}) : X) ∈ U
    rw [reversedChart_apply_val ψ t]
    exact hmem'

/-- **Value identity for the reversed chart**: the coordinate of the new
transition at `t` equals the old transition coordinate at the reflected
parameter `reflectCoord c d t` (`s ↦ 1 − s`). -/
theorem transitionHomeo_reversedCoord {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}) :
    ((transitionHomeo φ (reversedChart ψ) hA
        (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
        (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
        (show 1 - c ≤ 1 by linarith) t : {x : ℝ // x ∈ Ioo a b}) : ℝ) =
    ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
        (reflectCoord c d t) : {x : ℝ // x ∈ Ioo a b}) : ℝ) := by
  let ψ' : ORI 0 1 ≃ₜ {x : X // x ∈ V} := reversedChart ψ
  let hB' : coordRealSet ψ' U = Set.Ioo (1 - d) (1 - c) :=
    coordRealSet_reversedShape ψ U hc0 hcd hd1 hB
  let hc'0 : 0 ≤ 1 - d := by linarith
  let hc'd' : 1 - d < 1 - c := by linarith
  let hd'1 : 1 - c ≤ 1 := by linarith
  let T' := transitionHomeo φ ψ' hA hB' ha0 hab hb1 hc'0 hc'd' hd'1
  let g := transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  let s : {x : ℝ // x ∈ Ioo c d} := reflectCoord c d t
  rcases t.2 with ⟨htlo, hthi⟩
  have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hsval : (s : ℝ) = 1 - (t : ℝ) := by
    dsimp [s]
    rw [reflectCoord_val]
  have hs01 : (s : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    rw [hsval]
    constructor <;> linarith
  have hψ'U : (ψ' ⟨(t : ℝ), ht01⟩ : X) ∈ U := by
    have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ') (r := (t : ℝ)) ht01
    exact hiff.mpr (by simpa [hB'] using t.2)
  have hψU : (ψ ⟨(s : ℝ), hs01⟩ : X) ∈ U := by
    have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := (s : ℝ)) hs01
    exact hiff.mpr (by simpa [hB] using s.2)
  have hrefleq : (intervalReflection (0 : ℝ) 1 ⟨(t : ℝ), ht01⟩ : ORI 0 1) = ⟨(s : ℝ), hs01⟩ := by
    apply Subtype.ext
    rw [intervalReflection_apply]
    rw [hsval]
    ring
  have hψeq : (ψ (intervalReflection (0 : ℝ) 1 ⟨(t : ℝ), ht01⟩) : X) = (ψ ⟨(s : ℝ), hs01⟩ : X) := by
    exact congrArg (fun z : ORI 0 1 => (ψ z : X)) hrefleq
  have hXeq : (ψ' ⟨(t : ℝ), ht01⟩ : X) = (ψ ⟨(s : ℝ), hs01⟩ : X) := by
    dsimp [ψ']
    calc
      ((reversedChart ψ ⟨(t : ℝ), ht01⟩ : {x : X // x ∈ V}) : X)
          = (ψ (intervalReflection (0 : ℝ) 1 ⟨(t : ℝ), ht01⟩) : X) :=
            reversedChart_apply_val ψ ⟨(t : ℝ), ht01⟩
      _ = (ψ ⟨(s : ℝ), hs01⟩ : X) := hψeq
  have hArg : (⟨(ψ' ⟨(t : ℝ), ht01⟩ : X), hψ'U⟩ : {x : X // x ∈ U}) =
      ⟨(ψ ⟨(s : ℝ), hs01⟩ : X), hψU⟩ := by
    apply Subtype.ext
    exact hXeq
  have hL := transitionHomeo_coord φ ψ' hA hB' ha0 hab hb1 hc'0 hc'd' hd'1 t ht01 hψ'U
  have hR := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 s hs01 hψU
  dsimp [T', g, ψ'] at hL hR ⊢
  rw [hL, hR]
  exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : ORI 0 1) : ℝ)) hArg

/-- **S181 chart-orientation lemma**: reversing the orientation of the
`V`-chart (composing with the coordinate reflection `u ↦ 1 − u`) turns a
DECREASING transition into an INCREASING one — the new transition has the
left end of the reflected domain near `a` and the right end near `b`.  Hence
after the reversal the consistent orientation (`TransitionIncreasing` of
S178) holds, and `ends_of_at_least_one_chart_of_increasing` applies. -/
theorem transitionDecreasing_reversed_increasing {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hdec : TransitionDecreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) :
    TransitionIncreasing φ (reversedChart ψ) hA
      (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
      (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
      (show 1 - c ≤ 1 by linarith) := by
  rcases increasing_ends_after_reflection hab hcd
      (transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1) hdec with ⟨incL, incR⟩
  constructor
  · intro ε hε
    rcases incL ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hid := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t
    rw [hid]
    exact hδ t ht
  · intro ε hε
    rcases incR ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hid := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t
    rw [hid]
    exact hδ t ht



/-- **Orientation dichotomy of the transition**: the transition coordinate
map of any two interval charts is strictly monotone or strictly antitone
(S165 `intervalHomeo_coord_strictMono_or_anti`), and each branch realises
the corresponding orientation bundle (S179 `increasing_of_strictMono`,
S180 `decreasing_of_strictAnti`). -/
theorem transition_increasing_or_decreasing {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) :
    TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 ∨
    TransitionDecreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 := by
  let g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd g with hm | ha
  · left
    exact increasing_of_strictMono φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hm
  · right
    exact decreasing_of_strictAnti φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 ha

/-- **Orientation normalization (S181 packaging)**: for any two interval
charts, either the transition is already increasing, or after reversing the
orientation of the `V`-chart the transition is increasing.  Hence the
consistent-orientation hypothesis (`TransitionIncreasing`) costs nothing —
one chart orientation can always be chosen to realise it. -/
theorem exists_increasing_orientation {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1) :
    TransitionIncreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 ∨
    TransitionIncreasing φ (reversedChart ψ) hA
      (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
      (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
      (show 1 - c ≤ 1 by linarith) := by
  rcases transition_increasing_or_decreasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 with hinc | hdec
  · exact Or.inl hinc
  · exact Or.inr (transitionDecreasing_reversed_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hdec)
end LeanEval.KnotTheory.Quadrisecant
