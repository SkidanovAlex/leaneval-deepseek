import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right
import Submission.Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top
import Submission.Commons.Topology.Homeomorph.open_interval_affine

set_option linter.ambiguousOpen false

/-!
# Commons promotion: two open arcs with connected overlap glue to an open interval

This module promotes the verified generic two-arc gluing engine (the S153--S183
real-coordinate/chart machinery, developed in the workspace root) into the
shared Commons.  All content is pure Mathlib + commons; nothing is
problem-specific.  The engine is bundled under the unique sub-namespace
`Commons.Topology.OneManifold.ArcGlue` to avoid name clashes with other
Commons modules, and the headline theorem is:

`union_two_open_arcs_connected_overlap_interval`: in a Hausdorff space `X`,
two OPEN arcs `U V` (each homeomorphic to the open unit interval) whose
overlap `U ∩ V` is CONNECTED glue to an open arc: `U ∪ V` is homeomorphic to
`(0,1)`.

Everything below is verified (no primitives, no `placeholder_`).
-/

open Set
open scoped Topology

noncomputable section

namespace Commons.Topology.OneManifold.ArcGlue

/-!
# S153 — generic engine for the interval/circle classification of the
trisecant-set components: topological 1-manifolds and their countable
open-arc covers (PURE Mathlib; nothing problem-specific)

`ComponentChart.lean` (S152) established that the connected components of
the trisecant set `O` are topological 1-manifolds: at every point an open
neighbourhood homeomorphic to an open real interval, Hausdorff, second
countable.  The classification theorem those components need
("a connected topological 1-manifold without boundary is homeomorphic to
an open interval or to a circle") is generic topology; this module starts
its engine on the generic side (and will be promotable to the commons as
is):

1. **`OpenRealInterval lo hi`** — the open real interval `(lo,hi)` as a
   type (`{t : ℝ // t ∈ Set.Ioo lo hi}`, definitionally the same as the
   O-chart interval `ChartInterval` of the Torus modules);
2. **`LocallyIntervalChart X`** — every point has an open neighbourhood
   homeomorphic to an open real interval (the local model of a
   1-manifold);
3. **`IsOneManifold X`** — Hausdorff + second countable + locally
   interval-charted (a topological 1-manifold without boundary);
4. **`countable_open_arc_cover`** — the existence half of the exhaustion
   engine: every 1-manifold is covered by countably many open arcs
   (`∃ A : ℕ → Set X`, each `A n` open and homeomorphic to an open real
   interval, `⋃ n, A n = univ`).  Proof: choose an arc chart at each
   point (`Classical.choose`), get a countable subcover from
   second-countability (`eq_open_union_nat`, second countable ⇒
   hereditarily Lindelöf), and read the arc property back off the chart
   choice.  (Note: this cover is NOT nested — a nested exhaustion exists
   exactly on the interval side of the dichotomy; the circle side is
   detected by the compactness dichotomy, cf. the ROADMAP S153 design
   entry.)

The dichotomy itself (`X` connected ⇒ `X ≃ₜ` open interval or `X ≃ₜ`
circle) is the next engine stage: it consumes this cover plus the
overlap-walk/order gluing machinery (ConnectedWalk and the real-interval
analysis of `IsPreconnected.mem_intervals`).  A real-interval support
fact of the gluing core is included: **`union_Ioo_of_overlap`** — the
union of two open real intervals with nonempty intersection is an open
real interval (`(min a c, max b d)`), the coordinate model of two facing
end-overlapping interval charts gluing to an interval (ROADMAP S154).
Everything here is elementary and verified (no primitives, no `placeholder_`).
-/

/-- The open real interval `(lo,hi)` as a type.  (Definitionally the same
type as the chart interval `ChartInterval lo hi` of the trisecant chart
modules.) -/
abbrev OpenRealInterval (lo hi : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo lo hi}

/-- **Locally interval-charted**: every point has an open neighbourhood
homeomorphic to an open real interval — the local model of a
1-dimensional manifold. -/
def LocallyIntervalChart (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ lo hi : ℝ, Nonempty (OpenRealInterval lo hi ≃ₜ U)

/-- **Topological 1-manifold without boundary**: Hausdorff, second
countable, and locally interval-charted.  (The O-chart components of S152
are instances; the classification "connected ⇒ open interval or circle"
is the next engine stage.) -/
def IsOneManifold (X : Type*) [TopologicalSpace X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ LocallyIntervalChart X

/-- **Countable open-arc cover existence.**  Every topological 1-manifold
(Hausdorff, second countable, locally interval-charted) is covered by
countably many open sets each homeomorphic to an open real interval.
Proof: choose an arc chart at each point; second countability gives the
countable subcover (`eq_open_union_nat` through the hereditarily Lindelöf
instance). -/
theorem countable_open_arc_cover {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] (hLoc : LocallyIntervalChart X) :
    ∃ A : ℕ → Set X,
      (∀ n, IsOpen (A n)) ∧
      (∀ n, ∃ lo hi : ℝ, Nonempty (OpenRealInterval lo hi ≃ₜ A n)) ∧
      (⋃ n, A n = univ) := by
  classical
  let U : X → Set X := fun x => Classical.choose (hLoc x)
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    exact (Classical.choose_spec (hLoc x)).1
  have hxU : ∀ x, x ∈ U x := by
    intro x
    exact (Classical.choose_spec (hLoc x)).2.1
  have hUarc : ∀ x, ∃ lo hi : ℝ, Nonempty (OpenRealInterval lo hi ≃ₜ U x) := by
    intro x
    exact (Classical.choose_spec (hLoc x)).2.2
  rcases eq_open_union_nat (U := U) hUopen with ⟨k, hk⟩
  let A : ℕ → Set X := fun n => U (k n)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    exact hUopen (k n)
  · intro n
    exact hUarc (k n)
  · -- union A = univ
    have hcov : ⋃ x : X, U x = univ := by
      ext x
      constructor
      · intro hx
        exact trivial
      · intro _
        exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
    ext x
    constructor
    · intro hx
      exact trivial
    · intro _
      have hxcover : x ∈ ⋃ x : X, U x := Set.mem_iUnion.mpr ⟨x, hxU x⟩
      have hxsub : x ∈ ⋃ n, U (k n) := by
        rw [hk]
        exact hxcover
      simpa [A] using hxsub

/-! ## Real-interval support facts of the two-chart gluing core -/

/-- The union of two open real intervals with nonempty intersection is an
open real interval (`(min a c, max b d)`): the coordinate model of two
facing end-overlapping interval charts glues to an interval. -/
lemma union_Ioo_of_overlap {a b c d : ℝ}
    (hint : (Set.Ioo a b ∩ Set.Ioo c d).Nonempty) :
    ∃ lo hi : ℝ, Set.Ioo a b ∪ Set.Ioo c d = Set.Ioo lo hi := by
  let lo := min a c
  let hi := max b d
  refine ⟨lo, hi, ?_⟩
  rcases hint with ⟨x, hx1, hx2⟩
  have had : a < d := lt_trans hx1.1 hx2.2
  have hcb : c < b := lt_trans hx2.1 hx1.2
  ext y
  constructor
  · intro hy
    rcases hy with hy1 | hy2
    · constructor
      · dsimp [lo]; exact lt_of_le_of_lt (min_le_left a c) hy1.1
      · dsimp [hi]; exact lt_of_lt_of_le hy1.2 (le_max_left b d)
    · constructor
      · dsimp [lo]; exact lt_of_le_of_lt (min_le_right a c) hy2.1
      · dsimp [hi]; exact lt_of_lt_of_le hy2.2 (le_max_right b d)
  · intro hy
    rcases hy with ⟨hylo, hyhi⟩
    have hylo' : min a c < y := hylo
    have hyhi' : y < max b d := hyhi
    by_cases hya : a < y
    · by_cases hyb : y < b
      · exact Or.inl ⟨hya, hyb⟩
      · right
        have hyge : b ≤ y := le_of_not_gt hyb
        have hc : c < y := lt_of_lt_of_le hcb hyge
        have hyd : ¬ d ≤ y := by
          intro hdy
          have hmaxle : max b d ≤ y := max_le hyge hdy
          linarith
        exact ⟨hc, lt_of_not_ge hyd⟩
    · right
      have hyale : y ≤ a := le_of_not_gt hya
      have hc : c < y := by
        by_contra hyc
        have hycle : y ≤ c := le_of_not_gt hyc
        have hylemin : y ≤ min a c := le_min hyale hycle
        linarith
      by_cases hdb : d ≤ b
      · have hmaxb : max b d = b := max_eq_left hdb
        have hyb : y < b := by simpa [hi, hmaxb] using hyhi'
        have hyd : y < d := by linarith
        exact ⟨hc, hyd⟩
      · have hbd : b < d := lt_of_not_ge hdb
        have hyd : y < d := by simpa [hi, max_eq_right (le_of_lt hbd)] using hyhi'
        exact ⟨hc, hyd⟩

end Commons.Topology.OneManifold.ArcGlue


open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# S162 — the real-interval shape foundation of the connected-1-manifold
dichotomy, slice (b2)/(d) at the real-coordinate level

`OneManifold.lean` (S153) fixed the generic 1-manifold vocabulary and the
dichotomy target `connected_oneManifold_dichotomy` (every connected
Hausdorff second-countable topological 1-manifold is an open real interval
or a circle).  The S154–S161 engine proved the conditional interval-chart
chain machinery (`TwoChartGlue.lean`); this module supplies the
real-coordinate facts that the dichotomy's interval-side assembly consumes,
in PURE-Mathlib form (plus the commons affine-interval homeo L30):

1. **the classification** `open_preconnected_nonempty_ℝ_shape`: a nonempty
   open connected subset of ℝ is an open bounded interval `(a,b)`, an
   upper half-line `(a,∞)`, a lower half-line `(−∞,b)`, or all of ℝ.
   Proof: `IsPreconnected.mem_intervals` (the ten canonical interval
   shapes) + openness eliminates the closed/half-closed members (an open
   set can contain neither its `sSup` nor its `sInf` — the two
   ε-ball endpoint lemmas `isOpen_not_sup_mem` / `isOpen_not_inf_mem`
   plus the closed-shape contradiction lemmas `isOpen_nonempty_not_Icc`
   etc.);
2. **the homeomorphisms to the open unit interval** `OpenRealInterval 0
   1`: bounded `(a,b)` via the commons affine homeo (L30); half-lines via
   translation/reflection to `(0,∞)` and the rational model homeo
   `x ↦ x/(1+x)` (`homeo_Ioi_zero_openUnit`, inverse `y ↦ y/(1−y)`,
   both directions `Continuous.div₀`); `ℝ ≃ (0,∞)` via
   `Real.expOrderIso.toHomeomorph` (subtype `OrderTopology` instances are
   automatic through `orderTopology_of_ordConnected`);
3. **the headline** `open_connected_ℝ_homeo_openUnit`: every nonempty
   open connected subset of ℝ is homeomorphic to `(0,1)` (classification
   + the reassociation `subtypeSetEqHomeo` + the shape homeos);
4. **the union theorem** `open_connected_ℝ_union_homeo_openUnit`: the
   union of two nonempty open connected subsets of ℝ with nonempty
   intersection is again homeomorphic to `(0,1)` (open + preconnected via
   `IsPreconnected.union` + the headline) — the coordinate model of the
   two-arc gluing (slice b2/d: two arcs with connected overlap in the
   real line union to an arc);
5. **the compactness marker** `exists_eq_univ_of_compact_nested_union`:
   if `univ` is compact and the open sets `U n` are nested with union
   `univ`, then some `U k = univ` (compactness: finite subcover absorbed
   by the largest member `t.sup id` of the nested family) — the
   interval-side marker that a compact ambient (the circle side) can
   never be exhausted by proper open arcs;
6. **the non-compactness hinge** `not_compactSpace_openUnit` — the model
   arc `(0,1)` is NOT compact (the open cover by `U n = {x | x <
   1 − 1/(n+2)}` has no finite subcover: the largest member of a finite
   subcover misses `1 − 1/D`, `D = 2(k+2)`) and the corollary
   `not_homeo_compact_openUnit` — a compact space is never homeomorphic
   to `(0,1)` (via `Homeomorph.compactSpace`).  Together with (5) this
   pins the dichotomy: the interval side is exactly the non-compact
   side; a compact connected 1-manifold (component) can never carry an
   interval chart of its whole space.

Everything here is verified (no primitives, no `placeholder_`); the module is pure
Mathlib plus the commons affine fact, so it is promotable to the commons
as-is.
-/

noncomputable section

namespace Commons.Topology.OneManifold.ArcGlue

/-! S162 scratch: real-interval shape facts -/

/-- An open subset of ℝ containing `m`, all of whose points are `≤ m`, is impossible. -/
lemma isOpen_not_sup_mem {S : Set ℝ} (hS : IsOpen S) {m : ℝ} (hm : m ∈ S)
    (hsu : ∀ x ∈ S, x ≤ m) : False := by
  rcases Metric.isOpen_iff.mp hS m hm with ⟨ε, hε, hball⟩
  let y : ℝ := m + ε / 2
  have hyS : y ∈ S := hball (by
    dsimp [y]
    rw [Metric.mem_ball, Real.dist_eq]
    have hε2 : 0 < ε / 2 := by positivity
    rw [abs_of_pos (by linarith)]
    linarith)
  have : m < y := by dsimp [y]; linarith
  exact (not_le_of_gt this) (hsu y hyS)

/-- An open subset of ℝ containing `m`, all of whose points are `≥ m`, is impossible. -/
lemma isOpen_not_inf_mem {S : Set ℝ} (hS : IsOpen S) {m : ℝ} (hm : m ∈ S)
    (hin : ∀ x ∈ S, m ≤ x) : False := by
  rcases Metric.isOpen_iff.mp hS m hm with ⟨ε, hε, hball⟩
  let y : ℝ := m - ε / 2
  have hyS : y ∈ S := hball (by
    dsimp [y]
    rw [Metric.mem_ball, Real.dist_eq]
    have hyneg : y - m < 0 := by dsimp [y]; linarith
    rw [abs_of_neg hyneg]
    dsimp [y]
    linarith)
  have : y < m := by dsimp [y]; linarith
  exact (not_le_of_gt this) (hin y hyS)

lemma isOpen_nonempty_not_Icc {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Icc a b) : False := by
  by_cases hab : a ≤ b
  · have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have hbS : b ∈ S := by simpa [h] using hbI
    exact isOpen_not_sup_mem hS hbS (by
      intro x hx
      have hx' : x ∈ Icc a b := by simpa [h] using hx
      exact hx'.2)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Icc a b := by simpa [h] using hx
        have hb : b < a := lt_of_not_ge hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ico {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Ico a b) : False := by
  by_cases hab : a < b
  · have haI : a ∈ Ico a b := ⟨le_rfl, hab⟩
    have haS : a ∈ S := by simpa [h] using haI
    exact isOpen_not_inf_mem hS haS (by
      intro x hx
      have hx' : x ∈ Ico a b := by simpa [h] using hx
      exact hx'.1)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Ico a b := by simpa [h] using hx
        have hb : b ≤ a := le_of_not_gt hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ioc {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) {a b : ℝ}
    (h : S = Ioc a b) : False := by
  by_cases hab : a < b
  · have hbI : b ∈ Ioc a b := ⟨hab, le_rfl⟩
    have hbS : b ∈ S := by simpa [h] using hbI
    exact isOpen_not_sup_mem hS hbS (by
      intro x hx
      have hx' : x ∈ Ioc a b := by simpa [h] using hx
      exact hx'.2)
  · have : S = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Ioc a b := by simpa [h] using hx
        have hb : b ≤ a := le_of_not_gt hab
        rcases hx' with ⟨h1, h2⟩
        linarith
      · intro hx
        simpa using hx
    rw [this] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

lemma isOpen_nonempty_not_Ici {S : Set ℝ} (hS : IsOpen S) (_hne : S.Nonempty) {a : ℝ}
    (h : S = Ici a) : False := by
  have haI : a ∈ Ici a := by simpa using (le_rfl : a ≤ a)
  have haS : a ∈ S := by simpa [h] using haI
  exact isOpen_not_inf_mem hS haS (by
    intro x hx
    have hx' : x ∈ Ici a := by simpa [h] using hx
    exact hx')

lemma isOpen_nonempty_not_Iic {S : Set ℝ} (hS : IsOpen S) (_hne : S.Nonempty) {b : ℝ}
    (h : S = Iic b) : False := by
  have hbI : b ∈ Iic b := by simpa using (le_rfl : b ≤ b)
  have hbS : b ∈ S := by simpa [h] using hbI
  exact isOpen_not_sup_mem hS hbS (by
    intro x hx
    have hx' : x ∈ Iic b := by simpa [h] using hx
    exact hx')

/-- **Classification**: a nonempty open connected subset of ℝ is an open interval
`(a,b)`, an upper half-line `(a,∞)`, a lower half-line `(−∞,b)`, or all of ℝ. -/
theorem open_preconnected_nonempty_ℝ_shape {S : Set ℝ} (hS : IsOpen S)
    (hpc : IsPreconnected S) (hne : S.Nonempty) :
    (∃ a b : ℝ, S = Ioo a b) ∨ (∃ a : ℝ, S = Ioi a) ∨ (∃ a : ℝ, S = Iio a) ∨ S = univ := by
  rcases hpc.mem_intervals with h | h | h | h | h | h | h | h | h | h
  · exact False.elim (isOpen_nonempty_not_Icc hS hne h)
  · exact False.elim (isOpen_nonempty_not_Ico hS hne h)
  · exact False.elim (isOpen_nonempty_not_Ioc hS hne h)
  · left
    exact ⟨sInf S, sSup S, h⟩
  · exact False.elim (isOpen_nonempty_not_Ici hS hne h)
  · right; left
    exact ⟨sInf S, h⟩
  · exact False.elim (isOpen_nonempty_not_Iic hS hne h)
  · right; right; left
    exact ⟨sSup S, h⟩
  · right; right; right
    exact h
  · exfalso
    rw [h] at hne
    exact (Set.not_nonempty_empty (α := ℝ) hne)

/-! ## Homeomorphisms of the canonical shapes to the open unit interval -/

/-- Rational homeo `(0,∞) ≃ (0,1)`: `x ↦ x/(1+x)`, inverse `y ↦ y/(1−y)`. -/
theorem homeo_Ioi_zero_openUnit :
    Nonempty ({x : ℝ // x ∈ Set.Ioi (0 : ℝ)} ≃ₜ OpenRealInterval 0 1) := by
  let S : Type := {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}
  let T : Type := OpenRealInterval 0 1
  let F : S → T := fun x => ⟨x.1 / (1 + x.1), by
    have hx : 0 < x.1 := x.2
    have hden : 0 < 1 + x.1 := by linarith
    constructor
    · exact div_pos hx hden
    · rw [div_lt_one hden]; linarith⟩
  let G : T → S := fun y => ⟨y.1 / (1 - y.1), by
    have hy0 : 0 < y.1 := y.2.1
    have hden : 0 < 1 - y.1 := by linarith [y.2.2]
    exact div_pos hy0 hden⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    have hden0 : (1 : ℝ) + x.1 ≠ 0 := by
      have hx : 0 < x.1 := x.2
      have hpos : 0 < 1 + x.1 := by linarith
      exact ne_of_gt hpos
    field_simp [hden0]
    ring
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    dsimp [F, G]
    have hd0 : (1 : ℝ) - y.1 ≠ 0 := by have hy1 : y.1 < 1 := y.2.2; linarith
    have hd1 : 1 + y.1 / (1 - y.1) ≠ 0 := by
      have h : 1 + y.1 / (1 - y.1) = (1 : ℝ) / (1 - y.1) := by
        field_simp [hd0]
        ring
      rw [h]
      exact one_div_ne_zero hd0
    field_simp [hd0, hd1]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.div₀ continuous_subtype_val (by fun_prop)
      (by intro x; have hx : 0 < (x : ℝ) := x.2; positivity)
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.div₀ continuous_subtype_val (by fun_prop)
      (by intro y; have hy1 : (y : ℝ) < 1 := y.2.2; linarith)
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact ⟨Homeomorph.mk e hFc hGc⟩

/-- `exp : ℝ ≃ₜ (0,∞)`. -/
theorem homeo_real_Ioi_zero : Nonempty (ℝ ≃ₜ {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}) := by
  exact ⟨Real.expOrderIso.toHomeomorph⟩

/-- The translation homeo `(a,∞) ≃ (0,∞)`: `x ↦ x − a`. -/
theorem homeo_Ioi_translation (a : ℝ) :
    Nonempty ({x : ℝ // x ∈ Set.Ioi a} ≃ₜ {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}) := by
  let S : Type := {x : ℝ // x ∈ Set.Ioi a}
  let T : Type := {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}
  let F : S → T := fun x => ⟨x.1 - a, by
    have hx : a < x.1 := x.2
    rw [Set.mem_Ioi]
    linarith⟩
  let G : T → S := fun x => ⟨x.1 + a, by
    have hx : 0 < x.1 := x.2
    rw [Set.mem_Ioi]
    linarith⟩
  have hFG : Function.LeftInverse G F := by
    intro x; apply Subtype.ext; dsimp [F, G]; ring
  have hGF : Function.RightInverse G F := by
    intro y; apply Subtype.ext; dsimp [F, G]; ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.sub continuous_const
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.add continuous_const
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact ⟨Homeomorph.mk e hFc hGc⟩

/-- The reflection homeo `(−∞,a) ≃ (0,∞)`: `x ↦ a − x`. -/
theorem homeo_Iio_reflection (a : ℝ) :
    Nonempty ({x : ℝ // x ∈ Set.Iio a} ≃ₜ {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}) := by
  let S : Type := {x : ℝ // x ∈ Set.Iio a}
  let T : Type := {x : ℝ // x ∈ Set.Ioi (0 : ℝ)}
  let F : S → T := fun x => ⟨a - x.1, by
    have hx : x.1 < a := x.2
    rw [Set.mem_Ioi]
    linarith⟩
  let G : T → S := fun x => ⟨a - x.1, by
    have hx : 0 < x.1 := x.2
    rw [Set.mem_Iio]
    linarith⟩
  have hFG : Function.LeftInverse G F := by
    intro x; apply Subtype.ext; dsimp [F, G]; ring
  have hGF : Function.RightInverse G F := by
    intro y; apply Subtype.ext; dsimp [F, G]; ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact ⟨Homeomorph.mk e hFc hGc⟩

/-- Reassociation homeo for equal sets: `{x // x ∈ S} ≃ₜ {x // x ∈ T}` when `S = T`
(identity on values). -/
noncomputable def subtypeSetEqHomeo {S T : Set ℝ} (h : S = T) : {x : ℝ // x ∈ S} ≃ₜ {x : ℝ // x ∈ T} := by
  let e : {x : ℝ // x ∈ S} ≃ {x : ℝ // x ∈ T} :=
    { toFun := fun x => ⟨x.1, by simpa [h] using x.2⟩,
      invFun := fun y => ⟨y.1, by simpa [← h] using y.2⟩,
      left_inv := by intro x; apply Subtype.ext; rfl,
      right_inv := by intro y; apply Subtype.ext; rfl }
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val

/-- `{x // x ∈ univ} ≃ₜ ℝ`. -/
noncomputable def homeo_subtype_univ : {x : ℝ // x ∈ (univ : Set ℝ)} ≃ₜ ℝ := by
  let e : {x : ℝ // x ∈ (univ : Set ℝ)} ≃ ℝ :=
    { toFun := fun x => x.1,
      invFun := fun x => ⟨x, trivial⟩,
      left_inv := by intro x; rfl,
      right_inv := by intro x; rfl }
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    exact continuous_subtype_val
  · dsimp [e]
    refine Continuous.subtype_mk continuous_id (by intro x; trivial)

/-- Any nonempty open bounded interval is homeomorphic to `(0,1)`. -/
theorem homeo_Ioo_openUnit (a b : ℝ) (hab : a < b) :
    Nonempty ({x : ℝ // x ∈ Set.Ioo a b} ≃ₜ OpenRealInterval 0 1) := by
  exact Commons.Topology.Homeomorph.open_interval_affine hab (by norm_num)

/-- Any upper half-line `(a,∞)` is homeomorphic to `(0,1)`. -/
theorem homeo_Ioi_openUnit (a : ℝ) : Nonempty ({x : ℝ // x ∈ Set.Ioi a} ≃ₜ OpenRealInterval 0 1) := by
  rcases homeo_Ioi_translation a with ⟨e1⟩
  rcases homeo_Ioi_zero_openUnit with ⟨e2⟩
  exact ⟨e1.trans e2⟩

/-- Any lower half-line `(−∞,b)` is homeomorphic to `(0,1)`. -/
theorem homeo_Iio_openUnit (b : ℝ) : Nonempty ({x : ℝ // x ∈ Set.Iio b} ≃ₜ OpenRealInterval 0 1) := by
  rcases homeo_Iio_reflection b with ⟨e1⟩
  rcases homeo_Ioi_zero_openUnit with ⟨e2⟩
  exact ⟨e1.trans e2⟩

/-- ℝ is homeomorphic to `(0,1)`. -/
theorem homeo_real_openUnit : Nonempty (ℝ ≃ₜ OpenRealInterval 0 1) := by
  rcases homeo_real_Ioi_zero with ⟨e1⟩
  rcases homeo_Ioi_zero_openUnit with ⟨e2⟩
  exact ⟨e1.trans e2⟩

/-- **Headline**: every nonempty open connected subset of ℝ is homeomorphic
to the open unit interval `(0,1)`. -/
theorem open_connected_ℝ_homeo_openUnit {S : Set ℝ} (hS : IsOpen S)
    (hpc : IsPreconnected S) (hne : S.Nonempty) :
    Nonempty ({x : ℝ // x ∈ S} ≃ₜ OpenRealInterval 0 1) := by
  rcases open_preconnected_nonempty_ℝ_shape hS hpc hne with h | h | h | h
  · rcases h with ⟨a, b, h⟩
    have hab : a < b := by
      rcases hne with ⟨x, hx⟩
      have hx' : x ∈ Ioo a b := by simpa [h] using hx
      exact hx'.1.trans hx'.2
    rcases homeo_Ioo_openUnit a b hab with ⟨e⟩
    exact ⟨(subtypeSetEqHomeo h).trans e⟩
  · rcases h with ⟨a, h⟩
    rcases homeo_Ioi_openUnit a with ⟨e⟩
    exact ⟨(subtypeSetEqHomeo h).trans e⟩
  · rcases h with ⟨a, h⟩
    rcases homeo_Iio_openUnit a with ⟨e⟩
    exact ⟨(subtypeSetEqHomeo h).trans e⟩
  · rcases homeo_real_openUnit with ⟨e⟩
    exact ⟨(subtypeSetEqHomeo h).trans (homeo_subtype_univ.trans e)⟩

/-- **The union theorem**: the union of two nonempty open connected subsets of ℝ
with nonempty intersection is again homeomorphic to `(0,1)`. -/
theorem open_connected_ℝ_union_homeo_openUnit {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B)
    (hApc : IsPreconnected A) (hBpc : IsPreconnected B)
    (hint : (A ∩ B).Nonempty) :
    Nonempty ({x : ℝ // x ∈ A ∪ B} ≃ₜ OpenRealInterval 0 1) := by
  have hopen : IsOpen (A ∪ B) := hA.union hB
  rcases hint with ⟨x, hxA, hxB⟩
  have hpc : IsPreconnected (A ∪ B) := IsPreconnected.union x hxA hxB hApc hBpc
  have hne : (A ∪ B).Nonempty := ⟨x, Or.inl hxA⟩
  exact open_connected_ℝ_homeo_openUnit hopen hpc hne

/-- **Compactness marker (d-slice)**: if `univ` is compact and the open sets
`U n` are nested with union `univ`, then some `U k = univ`.  (An open arc
`≃ (0,1)` is never compact, so a compact ambient cannot be exhausted by
proper open arcs — the interval side of the dichotomy is non-compact.) -/
theorem exists_eq_univ_of_compact_nested_union {X : Type*} [TopologicalSpace X]
    (hC : IsCompact (univ : Set X)) (hneX : (univ : Set X).Nonempty)
    {U : ℕ → Set X} (hopen : ∀ n, IsOpen (U n))
    (hnest : ∀ n, U n ⊆ U (n + 1)) (hcover : (⋃ n, U n) = univ) : ∃ k : ℕ, U k = univ := by
  classical
  have hsub : (univ : Set X) ⊆ ⋃ n, U n := by rw [hcover]
  rcases hC.elim_finite_subcover U hopen hsub with ⟨t, ht⟩
  have hmono : Monotone U := monotone_nat_of_le_succ (fun n => hnest n)
  by_cases htempty : t = ∅
  · exfalso
    rcases hneX with ⟨x, _⟩
    have hxU : x ∈ ⋃ i ∈ (t : Set ℕ), U i := ht (by trivial : x ∈ (univ : Set X))
    rw [htempty] at hxU
    simp at hxU
  · let kmax : ℕ := t.sup id
    refine ⟨kmax, ?_⟩
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxU : x ∈ ⋃ i ∈ (t : Set ℕ), U i := ht (by trivial : x ∈ (univ : Set X))
    rcases (Set.mem_iUnion₂.mp hxU) with ⟨i, hit, hxi⟩
    have hitf : i ∈ t := by simpa using hit
    have hile : i ≤ kmax := by
      dsimp [kmax]
      exact Finset.le_sup (s := t) (f := id) hitf
    exact hmono hile hxi

/-- **Non-compactness of the model arc**: the open unit interval
`(0,1)` (as a subtype) is NOT compact.  Proof: the open cover by the
sub-intervals `U n = {x | x < 1 − 1/(n+2)}` has no finite subcover —
any finite subcover is absorbed by its largest member `t.sup id`, which
misses the point `1 − 1/D` for `D = 2(k+2)` (each `U i` with `i ≤ k`
excludes it).  This is the dichotomy hinge: a compact (circle) ambient
can never be charted to the model arc, so the interval side of the
classification is exactly the non-compact side. -/
theorem not_compactSpace_openUnit : ¬ CompactSpace (OpenRealInterval 0 1) := by
  intro hC
  let X := OpenRealInterval 0 1
  let U : ℕ → Set X := fun n => {x : X | (x : ℝ) < 1 - 1 / (n + 2 : ℝ)}
  have hopen : ∀ n, IsOpen (U n) := by
    intro n
    have hpre : U n = (fun x : X => (x : ℝ)) ⁻¹' (Iio (1 - 1 / (n + 2 : ℝ))) := by
      ext x; rfl
    rw [hpre]
    exact isOpen_Iio.preimage continuous_subtype_val
  have hcov : (univ : Set X) ⊆ ⋃ n, U n := by
    intro x hx
    have hx1 : (x : ℝ) < 1 := x.2.2
    have hpos : 0 < 1 - (x : ℝ) := by linarith
    rcases exists_nat_gt (1 / (1 - (x : ℝ))) with ⟨m, hm⟩
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    dsimp [U]
    have hpos2 : 0 < (m + 2 : ℝ) := by positivity
    have hI0 : 1 < (m + 2 : ℝ) * (1 - (x : ℝ)) := by
      have hm' : 1 / (1 - (x : ℝ)) < (m + 2 : ℝ) := lt_of_lt_of_le hm (by
        exact_mod_cast (by omega : m ≤ m + 2))
      exact (div_lt_iff₀ hpos).mp hm'
    have hI : 1 / (m + 2 : ℝ) < 1 - (x : ℝ) := by
      rw [div_lt_iff₀ hpos2]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hI0
    linarith
  rcases (IsCompact.elim_finite_subcover hC.isCompact_univ U hopen hcov) with ⟨t, ht⟩
  let w : X := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  by_cases htempty : t = ∅
  · exfalso
    have hw : w ∈ ⋃ i ∈ t, U i := ht (by trivial : w ∈ (univ : Set X))
    rw [htempty] at hw
    simp at hw
  · let kmax : ℕ := t.sup id
    let D : ℝ := (2 : ℝ) * ((kmax : ℝ) + 2)
    let x₀ : X := ⟨1 - 1 / D, by
      have hDpos : 0 < D := by
        dsimp [D]
        positivity
      constructor
      · have : 1 / D < 1 := by
          rw [div_lt_one hDpos]
          have hkge0 : 0 ≤ (kmax : ℝ) := by positivity
          dsimp [D]
          nlinarith
        linarith
      · have : 0 < 1 / D := div_pos zero_lt_one hDpos
        linarith⟩
    have hxU : x₀ ∈ ⋃ i ∈ t, U i := ht (by trivial : x₀ ∈ (univ : Set X))
    rcases (Set.mem_iUnion₂.mp hxU) with ⟨i, hit, hxi⟩
    have hile : i ≤ kmax := by
      dsimp [kmax]
      have hitf : i ∈ t := by simpa using hit
      exact Finset.le_sup (s := t) (f := id) hitf
    have hDle : (i : ℝ) + 2 ≤ D := by
      dsimp [D]
      have hc : (i : ℝ) ≤ (kmax : ℝ) := by exact_mod_cast hile
      linarith
    have hnot : ¬ x₀ ∈ U i := by
      intro hi
      dsimp [U, x₀] at hi
      have hDpos : 0 < D := by dsimp [D]; positivity
      have hposi : 0 < (i + 2 : ℝ) := by positivity
      have hlim : 1 / D ≤ 1 / (i + 2 : ℝ) := by
        rw [div_le_div_iff₀ hDpos hposi]
        simpa using hDle
      linarith
    exact False.elim (hnot hxi)

/-- A compact space cannot be homeomorphic to the open unit interval. -/
theorem not_homeo_compact_openUnit {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    ¬ Nonempty (X ≃ₜ OpenRealInterval 0 1) := by
  rintro ⟨e⟩
  exact not_compactSpace_openUnit (Homeomorph.compactSpace e)

end Commons.Topology.OneManifold.ArcGlue


open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-!
# S165 — end correspondence for homeomorphisms of open intervals (module
Submission/IntervalHomeoEnds.lean)

The first sub-lemma of the facing-normalization theorem (ROADMAP S163/S164,
step (3)(i)): a homeomorphism between open real intervals is strictly
monotone, and it maps the ends of the interval to ends.  Content (namespace
Commons.Topology.OneManifold.ArcGlue; PURE Mathlib):

1. **`intervalHomeoTotal`** — totalize the coordinate map of an interval
   homeo `e : (c,d) ≃ₜ (a,b)` (agreeing with `e` on `(c,d)`, arbitrary
   outside), with the value lemma `intervalHomeoTotal_eq`;
2. **`intervalHomeoTotal_contOn_injOn`** — the totalized map is continuous
   on `(c,d)` (restriction equals `val ∘ e`, via
   `continuousOn_iff_continuous_domRestrict`) and injective there;
3. **`intervalHomeo_coord_strictMono_or_anti`** — a homeo between open
   intervals of ℝ is strictly increasing or strictly decreasing (the
   monotonicity of continuous injective maps:
   `ContinuousOn.strictMonoOn_of_injOn_Ioo` of Mathlib);
4. **`intervalReflection`** (the order-reversing reflection `t ↦ c+d−t`,
   with `intervalReflection_apply` / `intervalReflection_involutive`);
5. **`intervalHomeo_left_end_reaches_endpoint`** — end correspondence at
   the LEFT end: as `t → c⁺`, `(e t : ℝ)` is eventually below `a + ε`
   (increasing case) or above `b − ε` (decreasing case) — i.e. the left
   end of the domain goes to the left or the right end of the range.
   Proof: surjectivity (`e.symm` hits the point `a+ε` / `b−ε`) +
   strict monotonicity + the trivial large-ε bound;
6. **`intervalHomeo_right_end_reaches_endpoint`** — the RIGHT-end
   analogue, derived from the left-end theorem by pre-composing with the
   reflection homeo.

These are the model-level inputs of the seam-inseparability argument
(step (3)(ii) of the S164 record): when both charts have a strict seam at
the same end of the overlap, the corresponding one-sided approach of the
transition homeo makes the two seam points inseparable.  Everything here
is verified (no primitives, no `placeholder_`).
-/
open Set
open scoped Topology

noncomputable section
namespace Commons.Topology.OneManifold.ArcGlue

/-- Totalize the coordinate map of an interval homeo: agrees with `e` on `(c,d)`. -/
noncomputable def intervalHomeoTotal {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) : ℝ → ℝ :=
  fun r => if h : r ∈ Ioo c d then (e ⟨r, h⟩ : ℝ) else a

theorem intervalHomeoTotal_eq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) {r : ℝ} (hr : r ∈ Ioo c d) :
    intervalHomeoTotal hab hcd e r = (e ⟨r, hr⟩ : ℝ) := by
  simp [intervalHomeoTotal, hr]

/-- The totalized coordinate map is continuous on `(c,d)` and injective there. -/
theorem intervalHomeoTotal_contOn_injOn {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    ContinuousOn (intervalHomeoTotal hab hcd e) (Ioo c d) ∧
      InjOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
  have hcont : ContinuousOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hpt : (Ioo c d).domRestrict (intervalHomeoTotal hab hcd e) =
        (fun x : {x : ℝ // x ∈ Ioo c d} => (e x : ℝ)) := by
      funext x
      dsimp [Set.domRestrict, intervalHomeoTotal]
      simp [x.2]
    rw [hpt]
    exact Continuous.subtype_val e.continuous
  have hinj : InjOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
    intro x hx y hy hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e hx
    have hy1 := intervalHomeoTotal_eq hab hcd e hy
    have heq : (e ⟨x, hx⟩ : ℝ) = (e ⟨y, hy⟩ : ℝ) := by
      rw [← hx1, ← hy1]
      exact hxy
    have heqJ : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      exact heq
    have : (⟨x, hx⟩ : {r : ℝ // r ∈ Ioo c d}) = ⟨y, hy⟩ := e.injective heqJ
    exact congrArg Subtype.val this
  exact ⟨hcont, hinj⟩

/-- A homeo between open intervals of ℝ is strictly monotone or antitone (the
coordinate map, increasing or decreasing). -/
theorem intervalHomeo_coord_strictMono_or_anti {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    StrictMono (fun x : ({x : ℝ // x ∈ Ioo c d}) => (e x : ℝ)) ∨
    StrictAnti (fun x : ({x : ℝ // x ∈ Ioo c d}) => (e x : ℝ)) := by
  have hci := intervalHomeoTotal_contOn_injOn hab hcd e
  have hma : StrictMonoOn (intervalHomeoTotal hab hcd e) (Ioo c d) ∨
      StrictAntiOn (intervalHomeoTotal hab hcd e) (Ioo c d) :=
    ContinuousOn.strictMonoOn_of_injOn_Ioo hcd hci.1 hci.2
  rcases hma with hm | ha
  · left
    intro x y hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e x.2
    have hy1 := intervalHomeoTotal_eq hab hcd e y.2
    have hlt := hm x.2 y.2 hxy
    rw [hx1, hy1] at hlt
    exact hlt
  · right
    intro x y hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e x.2
    have hy1 := intervalHomeoTotal_eq hab hcd e y.2
    have hlt := ha x.2 y.2 hxy
    rw [hx1, hy1] at hlt
    exact hlt


/-- **End correspondence (left end)**: a homeo between open intervals maps the
left end of the domain to the left end of the range (strictly increasing case)
or to the right end (strictly decreasing case).  Formally: as `t → c⁺`, the
coordinate `(e t : ℝ)` is eventually below `a + ε` (increasing) or above
`b − ε` (decreasing). -/
theorem intervalHomeo_left_end_reaches_endpoint {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, (t : ℝ) < c + δ → (e t : ℝ) < a + ε) ∨
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, (t : ℝ) < c + δ → b - ε < (e t : ℝ)) := by
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd e with hm | ha
  · left
    intro ε hε
    by_cases hge : b - a ≤ ε
    · refine ⟨d - c, sub_pos.mpr hcd, ?_⟩
      intro t ht
      have hltb : (e t : ℝ) < b := (e t).2.2
      have hbe : b ≤ a + ε := by linarith
      linarith
    · have hlt : a + ε < b := by linarith
      let y : {x : ℝ // x ∈ Ioo a b} := ⟨a + ε, ⟨by linarith, hlt⟩⟩
      let t₀ : {x : ℝ // x ∈ Ioo c d} := e.symm y
      refine ⟨(t₀ : ℝ) - c, ?_, ?_⟩
      · have hc : c < (t₀ : ℝ) := t₀.2.1
        linarith
      · intro t ht
        have htlt : (t : ℝ) < (t₀ : ℝ) := by
          dsimp [t₀]
          linarith
        have hmono : (e t : ℝ) < (e t₀ : ℝ) := hm htlt
        have heq : (e t₀ : ℝ) = a + ε := by
          dsimp [t₀, y]
          exact congrArg (fun z : {x : ℝ // x ∈ Ioo a b} => (z : ℝ)) (e.apply_symm_apply y)
        rw [heq] at hmono
        exact hmono
  · right
    intro ε hε
    by_cases hge : b - a ≤ ε
    · refine ⟨d - c, sub_pos.mpr hcd, ?_⟩
      intro t ht
      have hgta : a < (e t : ℝ) := (e t).2.1
      have hbe : b - ε ≤ a := by linarith
      linarith
    · have hlt : a < b - ε := by linarith
      let y : {x : ℝ // x ∈ Ioo a b} := ⟨b - ε, ⟨hlt, by linarith⟩⟩
      let t₀ : {x : ℝ // x ∈ Ioo c d} := e.symm y
      refine ⟨(t₀ : ℝ) - c, ?_, ?_⟩
      · have hc : c < (t₀ : ℝ) := t₀.2.1
        linarith
      · intro t ht
        have htlt : (t : ℝ) < (t₀ : ℝ) := by
          dsimp [t₀]
          linarith
        have hanti : (e t₀ : ℝ) < (e t : ℝ) := ha htlt
        have heq : (e t₀ : ℝ) = b - ε := by
          dsimp [t₀, y]
          exact congrArg (fun z : {x : ℝ // x ∈ Ioo a b} => (z : ℝ)) (e.apply_symm_apply y)
        rw [heq] at hanti
        exact hanti

/-- The order-reversing reflection of the interval `(c,d)`. -/
noncomputable def intervalReflection (c d : ℝ) : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ
    ({x : ℝ // x ∈ Ioo c d}) := by
  let I := {x : ℝ // x ∈ Ioo c d}
  let F : I → I := fun x => ⟨c + d - (x : ℝ), by
    rcases x.2 with ⟨h1, h2⟩
    constructor <;> linarith⟩
  let G : I → I := fun x => ⟨c + d - (x : ℝ), by
    rcases x.2 with ⟨h1, h2⟩
    constructor <;> linarith⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  let e : I ≃ I := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

theorem intervalReflection_apply (c d : ℝ) (t : {x : ℝ // x ∈ Ioo c d}) :
    ((intervalReflection c d t) : ℝ) = c + d - (t : ℝ) := by
  rfl

theorem intervalReflection_involutive (c d : ℝ) (t : {x : ℝ // x ∈ Ioo c d}) :
    intervalReflection c d (intervalReflection c d t) = t := by
  apply (intervalReflection c d).injective
  apply Subtype.ext
  simp [intervalReflection_apply]

/-- **End correspondence (right end)**: as `t → d⁻`, the coordinate `(e t : ℝ)`
is eventually above `b − ε` (strictly increasing case) or below `a + ε`
(strictly decreasing case). -/
theorem intervalHomeo_right_end_reaches_endpoint {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, d - δ < (t : ℝ) → b - ε < (e t : ℝ)) ∨
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, d - δ < (t : ℝ) → (e t : ℝ) < a + ε) := by
  let ρ : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo c d}) := intervalReflection c d
  let eρ : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) := ρ.trans e
  rcases intervalHomeo_left_end_reaches_endpoint hab hcd eρ with hl | hr
  · right
    intro ε hε
    rcases hl ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hρt : ((ρ t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      have ht' : d - δ < (t : ℝ) := ht
      rw [intervalReflection_apply c d t]
      linarith
    have hval := hδ (ρ t) hρt
    have heq : (eρ (ρ t) : ℝ) = (e t : ℝ) := by
      have hρρ : ρ (ρ t) = t := intervalReflection_involutive c d t
      dsimp [eρ]
      rw [hρρ]
    rwa [heq] at hval
  · left
    intro ε hε
    rcases hr ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hρt : ((ρ t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      rw [intervalReflection_apply c d t]
      linarith
    have hval := hδ (ρ t) hρt
    have heq : (eρ (ρ t) : ℝ) = (e t : ℝ) := by
      have hρρ : ρ (ρ t) = t := intervalReflection_involutive c d t
      dsimp [eρ]
      rw [hρρ]
    rwa [heq] at hval

/-- **Chart-orientation flip, coordinate level (S181)**: reflect the DOMAIN
coordinate of an interval homeo about the midpoint of `(0,1)`.  The
order-reversing map `s ↦ 1 − s` sends `(1−d, 1−c)`-coordinates to
`(c,d)`-coordinates (`reflectCoord`), and composing a DECREASING interval
homeo `e : (c,d) ≃ₜ (a,b)` (left end → `b`, right end → `a`) with it
produces a map with the INCREASING end behavior (new left end `(1−d)⁺` →
`a`, new right end `(1−c)⁻` → `b`).  This is the pure-coordinate core of
the S181 chart-orientation lemma: reversing a chart's orientation (its
coordinate reflection) turns a `TransitionDecreasing` transition into a
`TransitionIncreasing` one.

`reflectCoord` reflects the coordinate of an interval-type point:
`(1−d, 1−c)`-coordinates map to `(c,d)`-coordinates by `s ↦ 1 − s`. -/
noncomputable def reflectCoord (c d : ℝ) (t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}) :
    {x : ℝ // x ∈ Ioo c d} := by
  have h1 : 1 - d < (t : ℝ) := t.2.1
  have h2 : (t : ℝ) < 1 - c := t.2.2
  refine ⟨1 - (t : ℝ), ?_⟩
  constructor
  · linarith
  · linarith

/-- Value lemma for `reflectCoord`. -/
theorem reflectCoord_val (c d : ℝ) (t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}) :
    ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) = 1 - (t : ℝ) := by
  rfl

/-- **Coordinate core of the orientation flip**: a homeo `e : (c,d) ≃ₜ (a,b)`
with the DECREASING end behavior becomes INCREASING after precomposition
with `reflectCoord c d` — left end `(1−d)⁺` maps near `a`, right end
`(1−c)⁻` maps near `b`. -/
theorem increasing_ends_after_reflection {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}))
    (hdec : (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {x : ℝ // x ∈ Ioo c d}, (s : ℝ) < c + δ → b - ε < (e s : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {x : ℝ // x ∈ Ioo c d}, d - δ < (s : ℝ) → (e s : ℝ) < a + ε)) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}, (t : ℝ) < (1 - d) + δ →
          (e (reflectCoord c d t) : ℝ) < a + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}, (1 - c) - δ < (t : ℝ) →
          b - ε < (e (reflectCoord c d t) : ℝ)) := by
  constructor
  · intro ε hε
    rcases hdec.2 ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hs : d - δ < ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) := by
      rw [reflectCoord_val]
      linarith
    exact hδ (reflectCoord c d t) hs
  · intro ε hε
    rcases hdec.1 ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hs : ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      rw [reflectCoord_val]
      linarith
    exact hδ (reflectCoord c d t) hs
end Commons.Topology.OneManifold.ArcGlue



open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/-!
# S163 — the ambient two-arc theorem, slice (a): the coordinate
transport of the overlap along the arc charts (module
Submission/AmbientTwoArc.lean)

`RealIntervalShape.lean` (S162) supplied the real-line model: every
nonempty open connected subset of ℝ is homeomorphic to `(0,1)`, and the
union of two such sets with nonempty intersection is again one (the
coordinate two-arc union).  This module lifts the FIRST half of the
model to an ambient space `X`: given an open arc `U ⊆ X` with chart
`φ : (0,1) ≃ₜ {x // x ∈ U}` and any open set `V`, the overlap
`W = U ∩ V` transports to the chart as `A = {t ∈ (0,1) | φ t ∈ V}`, and
— when `W` is connected — `A` is again an open arc `A ≃ₜ (0,1)`
(**`overlap_pullback_arc`**).  The symmetric pullback `B` for the second
chart is the same theorem with `U,V` interchanged, and the two pullbacks
are identified by the canonical homeo `B ≃ₜ A` (both ≃ₜ
`{x // x ∈ U ∩ V}`).

Together these are exactly the "transporting the coordinates along the
overlapping chart" subgoals of the ambient two-arc theorem (ROADMAP
S153 slice (b2) / S162 STATUS slice (a)).  The ambient two-arc theorem
itself — for `X` Hausdorff + locally-interval-charted (a topological
1-manifold), `U,V` open arcs with `φ,ψ` charts and `U∩V` connected, the
union `U∪V ≃ₜ (0,1)` — assembles from this module by the four-step
outline recorded in the ROADMAP S163 entry: (1) pull both overlaps back
to the charts (this module, DONE); (2) classify the pullbacks as open
intervals `(a,b) ⊆ (0,1)` (RealIntervalShape, DONE); (3) the
facing-normalization: in a Hausdorff locally-interval ambient only the
facing/containment end-arrangements occur (branch-point exclusion at
seam points; the ROADMAP S154 correction — still OPEN, recorded as
lemma `facing_overlap_after_restriction`); (4) apply the ordered
two-chart gluing `two_chart_glue_homeo` (TwoChartGlue S157, DONE).  The
containment case `V ⊆ U` is fully proved here
(**`two_arc_contained`**).  Everything in this module is verified (no
primitives, no `placeholder_`).
-/

noncomputable section

namespace Commons.Topology.OneManifold.ArcGlue

/-- Coordinate transport of the overlap along a chart: for a chart
`φ : (0,1) ≃ₜ {x // x ∈ U}`, the pullback of `V` to the chart
`{t // (φ t : X) ∈ V}` is homeomorphic (via `φ`) to `{x : X // x ∈ U ∩ V}`. -/
noncomputable def overlapPullbackHomeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    ({t : OpenRealInterval 0 1 // (φ t : X) ∈ V}) ≃ₜ {x : X // x ∈ U ∩ V} := by
  let A := {t : OpenRealInterval 0 1 // (φ t : X) ∈ V}
  let W := {x : X // x ∈ U ∩ V}
  let F : A → W := fun t => ⟨(φ t : X), ⟨(φ t).2, t.2⟩⟩
  let G : W → A := fun w => ⟨φ.symm ⟨(w : X), (w.2).1⟩, by
    have hx : (φ (φ.symm ⟨(w : X), (w.2).1⟩) : X) = (w : X) := by
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
        (φ.apply_symm_apply ⟨(w : X), (w.2).1⟩)
    rw [hx]
    exact w.2.2⟩
  have hFG : Function.LeftInverse G F := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ)) (φ.symm_apply_apply t)
    simpa [F, G] using h
  have hGF : Function.RightInverse G F := by
    intro w
    apply Subtype.ext
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
      (φ.apply_symm_apply ⟨(w : X), (w.2).1⟩)
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_val (φ.continuous.comp continuous_subtype_val)
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact φ.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val (by intro w; exact w.2.1))
  let e : A ≃ W := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- Restricting a homeomorphism to a subset gives a homeomorphism onto the
image: `↑A ≃ₜ ↑(e '' A)`. -/
noncomputable def homeoRestrictImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : ({x : X // x ∈ A}) ≃ₜ ({y : Y // y ∈ e '' A}) := by
  let S := {x : X // x ∈ A}
  let T := {y : Y // y ∈ e '' A}
  let F : S → T := fun x => ⟨e x.1, by
    refine ⟨x.1, x.2, ?_⟩
    rfl⟩
  let G : T → S := fun y => ⟨e.symm y.1, by
    rcases y.2 with ⟨x, hxA, hx⟩
    have heq : e.symm y.1 = x := by
      apply e.injective
      rw [e.apply_symm_apply, hx]
    rwa [heq]⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    exact e.symm_apply_apply x.1
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    dsimp [F, G]
    exact e.apply_symm_apply y.1
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact e.continuous.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact e.symm.continuous.comp continuous_subtype_val
  let ee : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk ee hFc hGc

/-- The pullback of an open set `V` to the chart domain is open in `(0,1)`. -/
theorem overlapPullback_isOpen {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V) :
    IsOpen {t : OpenRealInterval 0 1 | (φ t : X) ∈ V} := by
  have hAt' : {t : OpenRealInterval 0 1 | (φ t : X) ∈ V} =
      (fun t : OpenRealInterval 0 1 => (φ t : X)) ⁻¹' V := by
    ext t; rfl
  rw [hAt']
  exact hV.preimage (Continuous.subtype_val φ.continuous)

/-- **Coordinate-transport arc theorem**: if the overlap `U ∩ V` of an open
set `V` with the open arc `U` is connected (as a subspace of `X`), then the
pullback of `V` to the chart of `U` is again an open arc:
`{t ∈ (0,1) | φ t ∈ V} ≃ₜ (0,1)`.  Proof: transport the overlap to the chart
(`overlapPullbackHomeo`), view the chart inside the real line through a chart
`ℝ ≃ₜ (0,1)` (`homeoRestrictImage` + the classification
`open_connected_ℝ_homeo_openUnit` of RealIntervalShape S162). -/
theorem overlap_pullback_arc {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V)
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    Nonempty ({t : OpenRealInterval 0 1 // (φ t : X) ∈ V} ≃ₜ OpenRealInterval 0 1) := by
  let A := {t : OpenRealInterval 0 1 // (φ t : X) ∈ V}
  let At : Set (OpenRealInterval 0 1) := {t : OpenRealInterval 0 1 | (φ t : X) ∈ V}
  have hAhomeo : A ≃ₜ {x : X // x ∈ U ∩ V} := by
    dsimp [A]
    exact overlapPullbackHomeo φ
  have hAconn : ConnectedSpace A := (hAhomeo.symm.connectedSpace_iff).mp hconn
  haveI : ConnectedSpace A := hAconn
  rcases homeo_real_openUnit with ⟨eR⟩
  let F : A → ℝ := fun a => (eR.symm (a : OpenRealInterval 0 1) : ℝ)
  have hFcont : Continuous F := by
    dsimp [F]
    exact eR.symm.continuous.comp continuous_subtype_val
  let S : Set ℝ := Set.range F
  have hSpreim : S = eR.toFun ⁻¹' At := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      dsimp [At]
      have he : eR (eR.symm (a : OpenRealInterval 0 1)) = (a : OpenRealInterval 0 1) :=
        eR.apply_symm_apply (a : OpenRealInterval 0 1)
      rw [he]
      exact a.2
    · intro hy
      dsimp [At] at hy
      refine ⟨⟨eR y, hy⟩, ?_⟩
      exact eR.symm_apply_apply y
  have hSopen : IsOpen S := by
    rw [hSpreim]
    exact (overlapPullback_isOpen φ hV).preimage eR.continuous
  have hSconn : IsConnected S := by
    have hSuniv : S = F '' (univ : Set A) := by
      ext y; simp [S]
    rw [hSuniv]
    exact IsConnected.image (isConnected_univ (α := A)) F hFcont.continuousOn
  rcases open_connected_ℝ_homeo_openUnit hSopen hSconn.2 hSconn.1 with ⟨e2⟩
  have himg : (eR.symm) '' At = S := by
    apply Eq.trans _ hSpreim.symm
    ext y
    constructor
    · rintro ⟨t, ht, hty⟩
      dsimp [At]
      have he : eR (eR.symm t) = eR y := congrArg eR hty
      have ht' : t = eR y := by simpa using he
      rw [← ht']
      exact ht
    · intro hy
      dsimp [At] at hy
      refine ⟨eR y, hy, ?_⟩
      exact eR.symm_apply_apply y
  let hr : A ≃ₜ ({x : ℝ // x ∈ S}) := by
    dsimp [A, At]
    exact (homeoRestrictImage (eR.symm) At).trans (Homeomorph.setCongr himg)
  exact ⟨hr.trans e2⟩

/-- Reassociation homeo for equal sets of an ambient type `X` (identity on
values). -/
noncomputable def setEqSubtypeHomeoX {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s = t) :
    ({x : X // x ∈ s}) ≃ₜ ({x : X // x ∈ t}) := by
  let e : ({x : X // x ∈ s}) ≃ ({x : X // x ∈ t}) :=
    { toFun := fun x => ⟨x.1, by simpa [h] using x.2⟩,
      invFun := fun y => ⟨y.1, by simpa [← h] using y.2⟩,
      left_inv := by intro x; apply Subtype.ext; rfl,
      right_inv := by intro y; apply Subtype.ext; rfl }
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val

/-- **The ambient two-arc theorem, containment case**: if `V ⊆ U` (the second
arc lies inside the first) then the union `U ∪ V = U` is an arc.  (Together
with the engine's `two_chart_glue_homeo` and the facing-normalization lemma
to come this covers the ambient two-arc theorem of slice (a).) -/
theorem two_arc_contained {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hVU : V ⊆ U) (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  have h : U ∪ V = U := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx
      · exact hVU hx
    · intro hx
      exact Or.inl hx
  exact ⟨(setEqSubtypeHomeoX h).trans φ.symm⟩

/-- For an open set `N₀ : Set X`, the points of the subspace
`M := {x // x ∈ U ∪ V}` lying in `N₀` reassociate homeomorphically with
`{x // x ∈ N₀}` (identity on values). -/
noncomputable def subspaceOverlapReassoc {X : Type*} [TopologicalSpace X] {U V N₀ : Set X}
    (hN₀ : N₀ ⊆ U ∪ V) :
    ({m : {x : X // x ∈ U ∪ V} // (m : X) ∈ N₀}) ≃ₜ ({x : X // x ∈ N₀}) := by
  let M := {x : X // x ∈ U ∪ V}
  let S := {m : M // (m : X) ∈ N₀}
  let T := {x : X // x ∈ N₀}
  let F : S → T := fun m => ⟨((m : M) : X), m.2⟩
  let G : T → S := fun x => ⟨⟨(x : X), hN₀ x.2⟩, x.2⟩
  have hFG : Function.LeftInverse G F := by
    intro m
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    rfl
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact hN₀ x.2)
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- **The union of two open arcs is locally interval-charted**: every point of
`{x // x ∈ U ∪ V}` (where `U`, `V` are open arcs of a Hausdorff ambient `X`)
has an open neighbourhood homeomorphic to an open real interval — for `x ∈ U`
take (the subspace part of) `U` itself, which is open in the union and carries
the `U`-chart. -/
theorem two_arc_union_locallyInterval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    LocallyIntervalChart {x : X // x ∈ U ∪ V} := by
  let M := {x : X // x ∈ U ∪ V}
  intro x
  by_cases hxU : (x : X) ∈ U
  · -- x ∈ U: use U as the neighbourhood
    refine ⟨{m : M | (m : X) ∈ U}, ?_, ?_, 0, 1, ?_⟩
    · have hpre : {m : M | (m : X) ∈ U} = (fun m : M => (m : X)) ⁻¹' U := by
        ext m; rfl
      rw [hpre]
      exact hUopen.preimage continuous_subtype_val
    · exact hxU
    · have hsub : U ⊆ U ∪ V := by intro x hx; exact Or.inl hx
      refine ⟨φ.trans (subspaceOverlapReassoc (U := U) (V := V) (N₀ := U) hsub).symm⟩
  · -- x ∈ V (x ∉ U): from x.2
    have hxV : (x : X) ∈ V := by
      rcases x.2 with h | h
      · exact False.elim (hxU h)
      · exact h
    refine ⟨{m : M | (m : X) ∈ V}, ?_, ?_, 0, 1, ?_⟩
    · have hpre : {m : M | (m : X) ∈ V} = (fun m : M => (m : X)) ⁻¹' V := by
        ext m; rfl
      rw [hpre]
      exact hVopen.preimage continuous_subtype_val
    · exact hxV
    · have hsub : V ⊆ U ∪ V := by intro x hx; exact Or.inr hx
      refine ⟨ψ.trans (subspaceOverlapReassoc (U := U) (V := V) (N₀ := V) hsub).symm⟩

/-- **The union of two open arcs of a Hausdorff second-countable ambient is a
topological 1-manifold** (`IsOneManifold` of OneManifold S153) — no
connectedness of the overlap is needed.  This is the dichotomy's local input
for the ambient two-arc theorem (slice (a)). -/
theorem two_arc_union_isOneManifold {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    IsOneManifold {x : X // x ∈ U ∪ V} := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact two_arc_union_locallyInterval (U := U) (V := V) hUopen hVopen φ ψ
end Commons.Topology.OneManifold.ArcGlue

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# S154–S155 — the ordered two-chart gluing core (the engine's atomic
step): facing end-overlap charts of a Hausdorff-type space glue to an
open interval

`OneManifold.lean` (S153) fixed the generic engine vocabulary; this
module is the gluing core ROADMAP S154/S155: two open-interval charts
whose overlap is the RIGHT end of one chart and the LEFT end of the
other (the *facing* configuration; only orientation-preserving
transitions are Hausdorff-compatible — ROADMAP S154) glue to an open
interval.  Charts are normalised to `(0,1)` (`OpenRealInterval 0 1`);
general chart intervals are reached by pre-normalising with the affine
homeo `Commons.Topology.Homeomorph.open_interval_affine` (L30).

1. **the transition coordinate** `T hu1 φ ψ hUend hv` — the U-chart
   coordinate of the overlap point `ψ v` (`v ∈ (0,u)`); with
   `T_mem` (values in `(s,1)`) and `T_range` (surjectivity onto
   `(s,1)`: the overlap `ψ((0,u)) = φ((s,1))` in coordinates);
2. **the real-function form** `Tfun` (0 off `(0,u)`; its `if`-condition
   is written `0 < v ∧ v < u` — the membership form does NOT match
   `dif_pos`), with `Tfun_eq`, `Tfun_range`, `Tfun_strictMonoOn`;
3. **the endpoint-limit** `T_endpoint_right` (S154 (P1)): under the
   orientation-preserving hypothesis `hinc`, `T v → 1` as `v → u⁻`
   (invoking the fleet fact
   `Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right`,
   L31), plus the upper bound `T_lt_one`;
4. **the seam function** `Gfun` (S155): `Gfun v = T v` on `(0,u)`,
   `v + 1 − u` elsewhere — the V-side coordinate formula — with
   `G_at_u` (`G u = 1`) and **`G_continuousAt`** (continuous at `u`):
   left side controlled by `T_endpoint_right` + `T_lt_one`, right side
   affine.

S156/S157: the global map **`twoChartF hu1 φ ψ hUend hUV : X →
OpenRealInterval 0 (2 − u)`** (U-coordinate on `U`, ψ⁻¹-coordinate +
`1 − u` on `V∖U`) with value lemmas and **bijectivity**
(`twoChartF_surjective`/`injective`/`bijective`), and its **continuity**:
`Tfun_continuousOn (0,u)` (a), `Gfun_continuousOn` on `(0,u)`, `(u,1)`
and `(0,1)` (b), `twoChartF_comp_ψ_val` (`F(ψ t) = Gfun t`),
`twoChartF_continuousOn_U`/`_V`, the open-cover glue
`continuous_of_continuousOn_open_cover`, and **`twoChartF_continuous`**
(c)/(d).  NEXT: the continuous inverse (S157 (f): the inverse **`twoChartG hs0 hu φ ψ : OpenRealInterval 0
(2 − u) → X`** (piecewise: `y < 1 ↦ φ⟨y⟩`, `y ≥ 1 ↦ ψ⟨y − 1 + u⟩`)
with value lemmas `twoChartG_apply_lt_one`/`twoChartG_apply_ge_one`,
continuity on the two open pieces
`twoChartG_continuousOn_left`/`twoChartG_continuousOn_right`, and the
**seam identity `φ_eq_ψ_Sfun`** (an overlap point with U-coordinate
`y ∈ (s,1)` is `ψ⟨Sfun y⟩`) and the real-parameter seam convergence
lemmas **`twoChartG_left_converge`** (any neighbourhood `N` of `ψ⟨u⟩`
contains `φ⟨y⟩ = ψ⟨Sfun y⟩` eventually as `y → 1⁻`, via the `ψ`-pullback
metric ball + `Sfun_endpoint_top` + `Sfun_lt_u`) and
**`twoChartG_right_converge`** (`twoChartG⟨y⟩ = ψ⟨y − 1 + u⟩ → ψ⟨u⟩` as
`y → 1⁺`).  S157 (f) step 3 (done): **`twoChartG_continuousAt_seam`**
(ε-ball proof at `⟨1, ·⟩`: `δ := min δₗ (min δᵣ (1 − s))`; values with
`val < 1` are `φ⟨val⟩ ∈ N` by the left convergence (with `val > s` from
`ε ≤ 1 − s`), `val = 1` is `ψ⟨u⟩ ∈ N` by `mem_of_mem_nhds`, `val > 1`
by the right convergence; subtype distances reduced via the helper
`dist_subtype_val` (subtype distance is induced — `change`-free after
`Metric.mem_ball` + this rfl lemma)) and **`twoChartG_continuous`**
(three-piece pointwise: `lt_trichotomy` on the value; the two open
pieces via `ContinuousOn.continuousAt` at the open preimages
`val⁻¹(Iio 1)`/`val⁻¹(Ioi 1)`; the middle by
`twoChartG_continuousAt_seam`).  STEP 4 (done): the inverse identities
**`twoChartG_comp_twoChartF`** / **`twoChartF_comp_twoChartG`** and the
**two-chart gluing theorem `two_chart_glue_homeo`**: facing end-overlap
charts (open `U V`, `0 < s < 1`, `0 < u < 1`, overlap `(s,1)`/`(0,u)`
in coordinates, `hinc` orientation-preserving, `U ∪ V = univ`) glue to
`Nonempty (X ≃ₜ OpenRealInterval 0 (2 - u))` — `Homeomorph.mk` of the
`Equiv` of `twoChartF`/`twoChartG` with the two continuities.
(ROADMAP S154 (P2)/(P3) finish: the engine's atomic gluing step is
fully verified.)  S158: **`range_chain_union_interval`** (the
coordinate model: finite chains of overlapping real intervals have
interval unions), **`unionSubtypeHomeo`** (the generalized subset
reassociation), and **`single_junction_extension`** — the
chain-induction step: open `U V` of an ambient space with facing
terminal-overlap charts `η ψ` glue to
`Nonempty ({z : Y // z ∈ U ∪ V} ≃ₜ OpenRealInterval 0 (2 - u))`, via
`two_chart_glue_homeo` on the union-subtype with transported overlap
equivalences `hVend'`/`hUend'` and the (computational) `Tfun`
invariance under reassociation (`dsimp [T, η', ψ', reassocU, reassocV,
unionSubtypeHomeo]`).  S159: **`prefix_two_charts_interval`** — the
base+first-step of the chain induction: two open traces `T₀ T₁` with
facing terminal-overlap interval charts glue to
`Nonempty ({z : Y // z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1)`
(`single_junction_extension` + the affine `norm01` back to `(0,1)`),
and the abstract **`chain_step`** — `T : ℕ → Set Y`, prefix-up-to-`k`
interval chart `κk`, new trace `T (k+1)` attaching along a facing
terminal overlap (`hVend`/`hUend`/`hinc` stated against `κk`):
`Nonempty (ORI 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ range (k+2), T j})` —
via `single_junction_extension` + `norm01` + the set-equality
reassociation `setEqSubtypeHomeo` and the union split
`union_range_succ`.  Everything here is verified (no primitives, no
`placeholder_`).

S160: the **finite-chain prefix interval theorem** — the induction
harness over the chain: `prefix_open` (each prefix union
`⋃ j ∈ range (k+1), T j` is open — finite union of open traces),
`prefix_zero_interval` (base: single trace `T 0` is the `(0+1)`-prefix),
`chain_step_open` (the abstract `chain_step` with `hUopen` derived from
per-trace openness), and **`finite_prefix_interval`** — given interval
charts `η j` of every trace and, at every level `k`, the facing
terminal-overlap data (`hdata`) stated against the current prefix
homeo `κk` (the overlap of `T (k+1)` with the prefix is the right end
`(s,1)` of `κk` and the left end `(0,u)` of `ηnew`, with the
`hinc` monotone transition), every prefix union
`⋃ j ∈ range (k+1), T j` is an open real interval chart
(`Nonempty (ORI 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ range (k+1), T j})`), by
transfinite-style induction: zero via `prefix_zero_interval`, succ via
`chain_step_open`.  This is the *chain-induction harness* of the
S147-T sweep: it reduces the sweep to (a) supplying the per-trace
interval charts `η`, and (b) proving `hdata` — the automatic
re-supply of facing terminal-overlap data as the prefix homeo
changes.  Where (b) wraps (the union covers the whole component / the
chain closes on itself), the interval model is replaced by the
compact circle side of the dichotomy (ROADMAP S152 analysis).

S161: the **interval-side growth atom and the wrap contradiction** —
`prefix_proper_growth` (if the new trace is an interval chart whose
overlap with the `k`-prefix is the left terminal interval `(0,u)`, `u < 1`,
then the new trace contains a point outside the prefix: every
facing-terminal chain step strictly grows the prefix union) and
`chain_data_fails_at_full_prefix` (the facing-terminal data with `u < 1`
cannot be supplied at a level whose prefix already equals the whole space
— the precise sense in which a compact/circle component is NOT chainable:
at the absorbing level the new trace must attach at both ends / wrap).
These are the two dichotomy markers the S147-T sweep reduces to on the
interval side: an infinite facing-terminal chain is the certificate of the
non-compact (interval) side, and its failure at full prefix is the wrap.
-/

open Commons.Topology.OneManifold.ArcGlue
open Set
open scoped Real Topology

noncomputable section

namespace Commons.Topology.OneManifold.ArcGlue

variable {X : Type*} [TopologicalSpace X]

/-- `v ∈ (0,u)` embedded into `(0,1)` (needs `u ≤ 1`). -/
theorem emb01 {u : ℝ} (hu1 : u ≤ 1) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) u) : v ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨hv.1, lt_of_lt_of_le hv.2 hu1⟩

/-- The U-chart coordinate of the point `ψ v` (transition; `v ∈ (0,u)`). -/
noncomputable def T {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) : ℝ :=
  ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩ : OpenRealInterval 0 1) : ℝ)

/-- `T` is monotone-or-antitone free; `T v ∈ (s,1)` and `T` ranges over all of `(s,1)`. -/
lemma T_mem {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    T hu1 φ ψ hUend hv ∈ Set.Ioo s 1 := by
  dsimp [T]
  have hpV : ((ψ ⟨v, emb01 hu1 hv⟩) : X) ∈ V :=
    (ψ ⟨v, emb01 hu1 hv⟩ : {x : X // x ∈ V}).2
  have hpU : ((ψ ⟨v, emb01 hu1 hv⟩) : X) ∈ U :=
    (hUend ⟨v, emb01 hu1 hv⟩).mpr hv
  have hφφ : (φ (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩) : X) = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
      (φ.apply_symm_apply ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩)
  exact (hVend (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩)).1 (by simpa [hφφ] using hpV)

/-- Surjectivity of the transition coordinate: every `y ∈ (s,1)` is the
U-coordinate of the overlap point `ψ v` for some `v ∈ (0,u)`; conversely
every such value lies in `(s,1)` (`T_mem`). -/
lemma T_range {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ∀ y : ℝ, y ∈ Set.Ioo s 1 ↔ ∃ v : ℝ, ∃ hv : v ∈ Set.Ioo 0 u, T hu1 φ ψ hUend hv = y := by
  intro y
  constructor
  · intro hy
    have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hs hy.1, hy.2⟩
    let p : X := (φ ⟨y, hy01⟩ : X)
    have hpU : p ∈ U := (φ ⟨y, hy01⟩ : {x : X // x ∈ U}).2
    have hpV : p ∈ V := (hVend ⟨y, hy01⟩).2 hy
    let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hpV⟩
    have hwU : (w : ℝ) ∈ Set.Ioo (0 : ℝ) u := by
      have hψwU : ((ψ w : X) ∈ U) := by
        have heq : (ψ w : X) = p := by
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨p, hpV⟩)
        simpa [heq] using hpU
      exact (hUend w).1 hψwU
    refine ⟨(w : ℝ), hwU, ?_⟩
    dsimp [T]
    have hwψ : (⟨(w : ℝ), emb01 hu1 hwU⟩ : OpenRealInterval 0 1) = w := by
      apply Subtype.ext
      rfl
    have hp' : ((ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) ∈ U) := by
      simpa [hwψ] using (hUend w).mpr hwU
    have hψp : (ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) = p := by
      rw [hwψ]
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨p, hpV⟩)
    have harg : (⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X), hp'⟩ : {x : X // x ∈ U}) = φ ⟨y, hy01⟩ := by
      apply Subtype.ext
      exact hψp
    calc
      ((φ.symm ⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X), hp'⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨y, hy01⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨y, hy01⟩ : OpenRealInterval 0 1) : ℝ) := by
            rw [φ.symm_apply_apply]
  · intro hv_exists
    rcases hv_exists with ⟨v, hv, hvy⟩
    rw [← hvy]
    exact T_mem hs hu hu1 φ ψ hVend hUend hv

/-! ## Endpoint-limit of the transition (S154 (P1), via L31) -/

/-- The transition as a total real function (0 off its domain). -/
noncomputable def Tfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (v : ℝ) : ℝ :=
  if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else 0

/-- `Tfun` agrees with `T` on the domain. -/
lemma Tfun_eq {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Tfun hu1 φ ψ hUend v = T hu1 φ ψ hUend hv := by
  change (if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else 0) = T hu1 φ ψ hUend hv
  rw [dif_pos ⟨hv.1, hv.2⟩]

/-- `Tfun '' (0,u) = (s,1)`: the real-function form of `T_range`. -/
lemma Tfun_range {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Tfun hu1 φ ψ hUend '' Set.Ioo 0 u = Set.Ioo s 1 := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨v, hv, hvy⟩
    have hTeq : T hu1 φ ψ hUend hv = y := by
      rw [← Tfun_eq hu1 φ ψ hUend hv]
      exact hvy
    exact (T_range hs hu hu1 φ ψ hVend hUend y).2 ⟨v, hv, hTeq⟩
  · intro hy
    rcases (T_range hs hu hu1 φ ψ hVend hUend y).1 hy with ⟨v, hv, hTeq⟩
    refine ⟨v, hv, ?_⟩
    rw [Tfun_eq hu1 φ ψ hUend hv]
    exact hTeq

/-- Strict monotonicity of the real transition function from the
`hinc` (orientation-preserving) hypothesis. -/
lemma Tfun_strictMonoOn {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    StrictMonoOn (Tfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  intro v₁ hv₁ v₂ hv₂ hvlt
  exact hinc hv₁ hv₂ hvlt

/-- **Endpoint-limit of the transition (S154 (P1))**: under the
orientation-preserving hypothesis, the U-coordinate `T v` of the overlap
point `ψ v` approaches `1` as `v` approaches `u` from below.  (Invokes the
fleet fact `Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right`
on the total function `Tfun`.) -/
lemma T_endpoint_right {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v : ℝ, ∀ hv : v ∈ Set.Ioo 0 u, u - δ < v → 1 - ε < T hu1 φ ψ hUend hv := by
  intro ε hε
  rcases Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right hu
      (Tfun_strictMonoOn hu1 φ ψ hUend hinc)
      (Tfun_range hs hu hu1 φ ψ hVend hUend) ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro v hv huδ
  have hvT : 1 - ε < Tfun hu1 φ ψ hUend v := hδ v hv huδ
  rw [← Tfun_eq hu1 φ ψ hUend hv]
  exact hvT

/-- Upper bound: `T v < 1` on the domain (values live in `(s,1)`). -/
lemma T_lt_one {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    T hu1 φ ψ hUend hv < 1 := by
  exact (T_mem hs hu hu1 φ ψ hVend hUend hv).2

/-! ## The seam function `Gfun` and its continuity at `u` (S155) -/

/-- **The seam real function**: on the overlap coordinates `(0,u)` it is
the transition `T`; on the rest it is the affine `v + 1 − u` (the V-tail
formula).  At `v = u` the two formulas both give `1`. -/
noncomputable def Gfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (v : ℝ) : ℝ :=
  if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else v + 1 - u

/-- The seam value: `G u = 1` (the affine branch at `v = u`). -/
lemma G_at_u {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Gfun hu1 φ ψ hUend u = 1 := by
  dsimp [Gfun]
  have hnot : ¬ (0 < u ∧ u < u) := by intro h; linarith
  rw [dif_neg hnot]
  ring

/-- **Seam continuity (S155)**: `Gfun` is continuous at `u` with value
`1`.  Left side: the transition `T v` tends to `1` as `v → u⁻`
(`T_endpoint_right`, the lower bound) and stays below `1`
(`T_lt_one`); right side: `v + 1 − u` is linear, equal to `1` at `u`;
the ε-δ glue at `u` combines the two. -/
lemma G_continuousAt {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ContinuousAt (Gfun hu1 φ ψ hUend) u := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  rcases T_endpoint_right hs hu hu1 φ ψ hVend hUend hinc ε hε with ⟨δ₁, hδ₁pos, hδ₁⟩
  let δ := min δ₁ (min ε u)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₁pos (lt_min hε hu)
  have hδ₁le : δ ≤ δ₁ := by
    dsimp [δ]
    exact min_le_left δ₁ (min ε u)
  have hδu : δ ≤ u := by
    dsimp [δ]
    exact le_trans (min_le_right δ₁ (min ε u)) (min_le_right ε u)
  have hδε : δ ≤ ε := by
    dsimp [δ]
    exact le_trans (min_le_right δ₁ (min ε u)) (min_le_left ε u)
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  have hy' : |y - u| < δ := by
    simpa [Real.dist_eq] using hy
  have hyu' : -(δ) < y - u := (abs_lt.mp hy').1
  have hGu : Gfun hu1 φ ψ hUend u = 1 := G_at_u hu1 φ ψ hUend
  by_cases hyu : u ≤ y
  · -- y ≥ u: affine branch
    have hnot : ¬ (0 < y ∧ y < u) := by intro h; linarith
    have hG : Gfun hu1 φ ψ hUend y = y + 1 - u := by
      dsimp [Gfun]
      rw [dif_neg hnot]
    rw [hG, hGu]
    have habs : |(y + 1 - u) - 1| < ε := by
      have hcalc : (y + 1 - u) - 1 = y - u := by ring
      rw [hcalc]
      exact lt_of_lt_of_le hy' hδε
    rw [Real.dist_eq]
    exact habs
  · -- y < u: transition branch (y ∈ (0,u) since |y−u| < δ ≤ u)
    have hylt : y < u := lt_of_not_ge hyu
    have hy0 : 0 < y := by
      have : y - u > -δ := hyu'
      have : y > u - δ := by linarith
      linarith [hδu]
    have hG : Gfun hu1 φ ψ hUend y = T hu1 φ ψ hUend ⟨hy0, hylt⟩ := by
      dsimp [Gfun]
      rw [dif_pos ⟨hy0, hylt⟩]
    have huδy : u - δ₁ < y := by
      have h1 : -δ < y - u := (abs_lt.mp hy').1
      have h2 : -δ₁ ≤ -δ := by linarith
      linarith
    have hlow : 1 - ε < T hu1 φ ψ hUend ⟨hy0, hylt⟩ := hδ₁ y ⟨hy0, hylt⟩ huδy
    have hup : T hu1 φ ψ hUend ⟨hy0, hylt⟩ < 1 + ε := by
      have hlt1 : T hu1 φ ψ hUend ⟨hy0, hylt⟩ < 1 := T_lt_one hs hu hu1 φ ψ hVend hUend ⟨hy0, hylt⟩
      linarith
    rw [hG, hGu]
    have habs : |(T hu1 φ ψ hUend ⟨hy0, hylt⟩) - 1| < ε := by
      rw [abs_lt]
      constructor <;> linarith
    rw [Real.dist_eq]
    exact habs

/-! ## The global map `twoChartF` and its bijectivity (S156) -/

/-- Outside `U`, a point lies in `V` (the two charts cover `X`). -/
theorem memV_of_not_memU {U V : Set X} (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) : x ∈ V := by
  have hx : x ∈ (U ∪ V : Set X) := by simpa [hUV]
  exact hx.elim (fun h => (hxU h).elim) id

/-- **The global coordinate map** `F : X → OpenRealInterval 0 (2 − u)`:
the U-chart coordinate on `U`; on `V ∖ U` the V-chart coordinate shifted
by `1 − u` (so the free V-tail `(u,1)` maps onto `(1, 2−u)` and the seam
point `ψ(u)` maps to `1`). -/
noncomputable def twoChartF {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (x : X) : OpenRealInterval 0 (2 - u) := by
  classical
  by_cases hxU : x ∈ U
  · let c : OpenRealInterval 0 1 := φ.symm ⟨x, hxU⟩
    exact ⟨(c : ℝ), by
      have h1le : 1 ≤ 2 - u := by linarith
      exact ⟨c.2.1, lt_of_lt_of_le c.2.2 h1le⟩⟩
  · let v : OpenRealInterval 0 1 := ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩
    exact ⟨(v : ℝ) + 1 - u, by
      have hvnot : ¬ (v : ℝ) ∈ Set.Ioo 0 u := by
        intro hvu
        have hψx : (ψ v : X) = x := by
          dsimp [v]
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
            (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)
        have hxU' : x ∈ U := by
          simpa [hψx] using ((hUend v).mpr hvu)
        exact hxU hxU'
      have hvu : u ≤ (v : ℝ) := by
        by_contra hvul
        have hvltu : (v : ℝ) < u := lt_of_not_ge hvul
        exact hvnot ⟨v.2.1, hvltu⟩
      constructor
      · have hge1 : 1 ≤ (v : ℝ) + 1 - u := by linarith
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hge1
      · have hlt : (v : ℝ) + 1 - u < 2 - u := by linarith [v.2.2]
        exact hlt⟩

/-- Value on `U`: the U-chart coordinate. -/
lemma twoChartF_val_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∈ U) :
    ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) =
      ((φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1) : ℝ) := by
  dsimp [twoChartF]
  rw [dif_pos hxU]

/-- Value outside `U` (on the free V-tail): the V-chart coordinate shifted. -/
lemma twoChartF_val_not_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) :
    ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) =
      ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u := by
  dsimp [twoChartF]
  rw [dif_neg hxU]

/-- The V-coordinate of a point outside `U` is at least `u` (it lies on
the free V-tail, not in the overlap `(0,u)`). -/
lemma coord_ge_u_of_not_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) :
    u ≤ ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) := by
  let v : OpenRealInterval 0 1 := ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩
  have hvnot : ¬ (v : ℝ) ∈ Set.Ioo 0 u := by
    intro hvu
    have hψx : (ψ v : X) = x := by
      dsimp [v]
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
        (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)
    have hxU' : x ∈ U := by
      simpa [hψx] using ((hUend v).mpr hvu)
    exact hxU hxU'
  by_contra hvul
  have hvltu : (v : ℝ) < u := lt_of_not_ge hvul
  exact hvnot ⟨v.2.1, hvltu⟩

/-- **Surjectivity of the global map.**  `y < 1`: preimage `φ⟨y⟩ ∈ U`;
`y ≥ 1`: preimage `ψ⟨y − 1 + u⟩` on the free V-tail. -/
lemma twoChartF_surjective {U V : Set X} {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Surjective (twoChartF hu1 φ ψ hUend hUV) := by
  intro y
  by_cases hy1 : (y : ℝ) < 1
  · let x : X := (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X)
    refine ⟨x, ?_⟩
    have hxU : x ∈ U := (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : {x : X // x ∈ U}).2
    apply Subtype.ext
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV hxU]
    have hφinv : (φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) =
        ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ :=
      φ.symm_apply_apply ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩
    have harg : (⟨x, hxU⟩ : {x : X // x ∈ U}) = φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ := by
      apply Subtype.ext
      dsimp [x]
    calc
      ((φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : OpenRealInterval 0 1) : ℝ) := by
            simpa using congrArg (fun t : OpenRealInterval 0 1 => (t : ℝ)) hφinv
      _ = (y : ℝ) := rfl
  · have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
    let w : ℝ := (y : ℝ) - 1 + u
    have hw0 : 0 < w := by dsimp [w]; linarith [hyge, hu]
    have hw1 : w < 1 := by dsimp [w]; linarith [y.2.2]
    have hwnot : ¬ w ∈ Set.Ioo 0 u := by
      intro hw
      have hwltu : w < u := hw.2
      dsimp [w] at hwltu
      linarith
    let x : X := (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X)
    refine ⟨x, ?_⟩
    have hxnotU : x ∉ U := by
      intro hxU
      exact hwnot ((hUend ⟨w, ⟨hw0, hw1⟩⟩).1 hxU)
    apply Subtype.ext
    have hψinv : (ψ.symm (ψ ⟨w, ⟨hw0, hw1⟩⟩) : OpenRealInterval 0 1) = ⟨w, ⟨hw0, hw1⟩⟩ :=
      ψ.symm_apply_apply ⟨w, ⟨hw0, hw1⟩⟩
    have hval : ((ψ.symm ⟨x, memV_of_not_memU hUV hxnotU⟩ : OpenRealInterval 0 1) : ℝ) = w := by
      -- ψ.symm of ψ⟨w⟩ with a different membership: apply_symm_apply on the exact element
      have hx : x = (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X) := rfl
      have harg : (⟨x, memV_of_not_memU hUV hxnotU⟩ : {x : X // x ∈ V}) =
          ψ ⟨w, ⟨hw0, hw1⟩⟩ := by
        apply Subtype.ext
        exact hx
      calc
        ((ψ.symm ⟨x, memV_of_not_memU hUV hxnotU⟩ : OpenRealInterval 0 1) : ℝ)
            = ((ψ.symm (ψ ⟨w, ⟨hw0, hw1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
              exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg
        _ = w := by
              simpa using congrArg (fun t : OpenRealInterval 0 1 => (t : ℝ)) hψinv
    calc
      ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) = w + 1 - u := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxnotU]
        rw [hval]
      _ = (y : ℝ) := by dsimp [w]; ring

/-- **Injectivity of the global map**: the two image regions `(0,1)`
(U-part) and `[1, 2−u)` (V-tail) are disjoint, and within each region the
chart coordinate map is injective. -/
lemma twoChartF_injective {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Injective (twoChartF hu1 φ ψ hUend hUV) := by
  intro x₁ x₂ hEq
  by_cases h1 : x₁ ∈ U
  · by_cases h2 : x₂ ∈ U
    · have hc₁ : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) : ℝ) :=
        twoChartF_val_memU hu1 φ ψ hUend hUV h1
      have hc₂ : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1) : ℝ) :=
        twoChartF_val_memU hu1 φ ψ hUend hUV h2
      have hcoord : (φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) = φ.symm ⟨x₂, h2⟩ := by
        apply Subtype.ext
        have hval : ((φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) : ℝ) =
            ((φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa [hc₁, hc₂] using congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
        exact hval
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) ((φ.symm.injective) hcoord)
    · have hval₁lt : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := by
        rw [twoChartF_val_memU hu1 φ ψ hUend hUV h1]
        exact (φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1).2.2
      have hval₂ge : 1 ≤ ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV h2]
        have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV h2
        linarith
      have heqv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
        congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
      linarith
  · by_cases h2 : x₂ ∈ U
    · have hval₁ge : 1 ≤ ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV h1]
        have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV h1
        linarith
      have hval₂lt : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := by
        rw [twoChartF_val_memU hu1 φ ψ hUend hUV h2]
        exact (φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1).2.2
      have heqv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
        congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
      linarith
    · have hc₁ : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u :=
        twoChartF_val_not_memU hu1 φ ψ hUend hUV h1
      have hc₂ : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u :=
        twoChartF_val_not_memU hu1 φ ψ hUend hUV h2
      have hcoord : (ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) =
          ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ := by
        apply Subtype.ext
        have hval : ((ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) : ℝ) =
            ((ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ : OpenRealInterval 0 1) : ℝ) := by
          have hvv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
              ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
            congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
          linarith
        exact hval
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) ((ψ.symm.injective) hcoord)

/-- **Bijectivity of the global map.** -/
lemma twoChartF_bijective {U V : Set X} {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Bijective (twoChartF hu1 φ ψ hUend hUV) := by
  exact ⟨twoChartF_injective hu1 φ ψ hUend hUV, twoChartF_surjective hu hu1 φ ψ hUend hUV⟩

/-! ## Continuity of the transition function on its domain (S157 (a)) -/

/-- `Tfun` is continuous on its domain `(0,u)`: there it is the
coordinate composition `val ∘ φ.symm ∘ ψ ∘ emb`, continuous by the
chart homeos. -/
lemma Tfun_continuousOn {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Tfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g : {x : ℝ // x ∈ Set.Ioo 0 u} → ℝ := fun v =>
    ((φ.symm ⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
        : OpenRealInterval 0 1) : ℝ)
  have hg : Continuous g := by
    dsimp [g]
    have h1 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (⟨(v : ℝ), emb01 hu1 v.2⟩ : OpenRealInterval 0 1)) := by
      exact Continuous.subtype_mk continuous_subtype_val (fun v => emb01 hu1 v.2)
    have hψ : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X)) := by
      exact continuous_subtype_val.comp (ψ.continuous.comp h1)
    have h2 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
          : {x : X // x ∈ U})) := by
      exact Continuous.subtype_mk hψ (fun v => (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2)
    have h3 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (φ.symm ⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
          : OpenRealInterval 0 1)) := by
      exact φ.symm.continuous.comp h2
    exact continuous_subtype_val.comp h3
  have hcongr : (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} => Tfun hu1 φ ψ hUend (v : ℝ)) = g := by
    funext v
    dsimp [g]
    rw [Tfun_eq hu1 φ ψ hUend v.2]
    dsimp [T]
  change Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} => Tfun hu1 φ ψ hUend (v : ℝ))
  rw [hcongr]
  exact hg

/-! ## Continuity of the seam function on the unit interval (S157 (b)) -/

/-- `Gfun` equals the transition `T` on the overlap domain. -/
lemma Gfun_eq_Tfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Gfun hu1 φ ψ hUend v = T hu1 φ ψ hUend hv := by
  dsimp [Gfun]
  rw [dif_pos ⟨hv.1, hv.2⟩]

/-- `Gfun` is continuous on the overlap domain `(0,u)` (it equals `Tfun`
there, continuous by (a)). -/
lemma Gfun_continuousOn_domain {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  apply ContinuousOn.congr (Tfun_continuousOn hu1 φ ψ hUend)
  intro v hv
  rw [Gfun_eq_Tfun hu1 φ ψ hUend hv, Tfun_eq hu1 φ ψ hUend hv]

/-- `Gfun` is continuous on the free V-tail `(u,1)` (it is the affine map
`v ↦ v + 1 − u` there). -/
lemma Gfun_continuousOn_tail {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo u 1) := by
  have haff : ContinuousOn (fun v : ℝ => v + 1 - u) (Set.Ioo u 1) := by fun_prop
  apply ContinuousOn.congr haff
  intro v hv
  dsimp [Gfun]
  have hnot : ¬ (0 < v ∧ v < u) := by intro h; linarith [hv.1]
  rw [dif_neg hnot]

/-- `Gfun` is continuous on the whole unit interval `(0,1)`: the three
pieces `(0,u)` (domain), `{u}` (seam, by `G_continuousAt`) and `(u,1)`
(tail). -/
lemma Gfun_continuousOn_unit {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo 0 1) := by
  rw [IsOpen.continuousOn_iff isOpen_Ioo]
  intro v hv
  rcases lt_trichotomy v u with hlt | heq | hgt
  · exact ContinuousOn.continuousAt (Gfun_continuousOn_domain hu1 φ ψ hUend)
      (isOpen_Ioo.mem_nhds ⟨hv.1, hlt⟩)
  · subst heq
    exact G_continuousAt hs hu hu1 φ ψ hVend hUend hinc
  · exact ContinuousOn.continuousAt (Gfun_continuousOn_tail hu1 φ ψ hUend)
      (isOpen_Ioo.mem_nhds ⟨hgt, hv.2⟩)

/-! ## Continuity of the global map (S157 (c)/(d)) -/

/-- Along the V-chart, the global map reads as the seam function:
`F (ψ t) = Gfun (t : ℝ)` (as real values). -/
lemma twoChartF_comp_ψ_val {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {t : OpenRealInterval 0 1} :
    ((twoChartF hu1 φ ψ hUend hUV (ψ t : X) : OpenRealInterval 0 (2 - u)) : ℝ) =
      Gfun hu1 φ ψ hUend (t : ℝ) := by
  by_cases ht : (t : ℝ) < u
  · -- t ∈ (0,u): ψ t ∈ U; both sides are the U-coordinate of ψ t = T t
    have htmem : (t : ℝ) ∈ Set.Ioo 0 u := ⟨t.2.1, ht⟩
    have hψU : ((ψ t : X) ∈ U) := (hUend t).mpr htmem
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV hψU]
    have hG : Gfun hu1 φ ψ hUend (t : ℝ) = T hu1 φ ψ hUend htmem := Gfun_eq_Tfun hu1 φ ψ hUend htmem
    rw [hG]
    dsimp [T]
  · -- t ≥ u: ψ t ∉ U; both sides are ψ⁻¹-coordinate of ψ t + 1 − u = t + 1 − u
    have htge : u ≤ (t : ℝ) := le_of_not_gt ht
    have hψnotU : ((ψ t : X) ∉ U) := by
      intro hU
      have htt : (t : ℝ) ∈ Set.Ioo 0 u := (hUend t).1 hU
      exact (not_lt_of_ge htge) htt.2
    rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hψnotU]
    have hψinv : ((ψ.symm ⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : OpenRealInterval 0 1) : ℝ) = (t : ℝ) := by
      have harg : (⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : {x : X // x ∈ V}) = ψ t := by
        apply Subtype.ext
        rfl
      calc
        ((ψ.symm ⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : OpenRealInterval 0 1) : ℝ)
            = ((ψ.symm (ψ t) : OpenRealInterval 0 1) : ℝ) := by
              exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg
        _ = (t : ℝ) := by
              simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ)) (ψ.symm_apply_apply t)
    rw [hψinv]
    dsimp [Gfun]
    have hnot : ¬ (0 < (t : ℝ) ∧ (t : ℝ) < u) := by intro h; linarith
    rw [dif_neg hnot]

/-- `F` is continuous on the open chart `U`: there it is the U-chart
coordinate (a chart homeo). -/
lemma twoChartF_continuousOn_U {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : ContinuousOn (twoChartF hu1 φ ψ hUend hUV) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : X // x ∈ U} => twoChartF hu1 φ ψ hUend hUV (x : X))
  have hval : Continuous (fun x : {x : X // x ∈ U} =>
      ((twoChartF hu1 φ ψ hUend hUV (x : X) : OpenRealInterval 0 (2 - u)) : ℝ)) := by
    have hclean : Continuous (fun x : {x : X // x ∈ U} => ((φ.symm ⟨(x : X), x.2⟩ : OpenRealInterval 0 1) : ℝ)) := by
      exact continuous_subtype_val.comp φ.symm.continuous
    apply Continuous.congr hclean
    intro x
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV x.2]
  exact Continuous.subtype_mk hval (fun x => (twoChartF hu1 φ ψ hUend hUV (x : X)).2)

/-- `F` is continuous on the open chart `V`: along `ψ` it reads as the
seam function `Gfun`, continuous on the unit interval by (b). -/
lemma twoChartF_continuousOn_V {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂)
    (hUV : U ∪ V = univ) : ContinuousOn (twoChartF hu1 φ ψ hUend hUV) V := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : X // x ∈ V} => twoChartF hu1 φ ψ hUend hUV (x : X))
  -- V ≃ (0,1) via ψ: pull back to the unit interval
  let g : OpenRealInterval 0 1 → OpenRealInterval 0 (2 - u) := fun t =>
    twoChartF hu1 φ ψ hUend hUV (ψ t : X)
  have hg : Continuous g := by
    dsimp [g]
    refine Continuous.subtype_mk ?_ (fun t => (twoChartF hu1 φ ψ hUend hUV (ψ t : X)).2)
    have hGcont : Continuous (fun t : OpenRealInterval 0 1 => Gfun hu1 φ ψ hUend (t : ℝ)) := by
      -- from Gfun_continuousOn_unit via the domRestrict direction
      have h1 := (Gfun_continuousOn_unit hs hu hu1 φ ψ hVend hUend hinc)
      rw [continuousOn_iff_continuous_domRestrict] at h1
      exact h1
    apply Continuous.congr hGcont
    intro t
    exact (twoChartF_comp_ψ_val hu1 φ ψ hUend hUV).symm
  -- V-restriction = g ∘ (the map back from V to the interval) ∘?
  -- for x : V: x = ψ(ψ⁻¹ x): twoChartF x = g (ψ⁻¹-based): express x ↦ F x = g (fun via ψ.symm)
  have hback : Continuous (fun x : {x : X // x ∈ V} =>
      (ψ.symm ⟨(x : X), x.2⟩ : OpenRealInterval 0 1)) := by
    exact ψ.symm.continuous
  -- F on V = g ∘ ψ⁻¹∘(embedding)? we need: (fun x : V => twoChartF .. (x : X)) = (g ∘ fun x : V => ψ.symm ⟨x, x.2⟩)
  have hEq : (fun x : {x : X // x ∈ V} => twoChartF hu1 φ ψ hUend hUV (x : X)) =
      (fun x : {x : X // x ∈ V} => g (ψ.symm ⟨(x : X), x.2⟩)) := by
    funext x
    dsimp [g]
    congr 1
    -- (ψ (ψ.symm ⟨x, x.2⟩) : X) = (x : X)
    have hψψ : (ψ (ψ.symm ⟨(x : X), x.2⟩) : X) = (x : X) := by
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨(x : X), x.2⟩)
    exact hψψ.symm
  rw [hEq]
  exact hg.comp hback

/-- Open-cover glue: continuous on two open sets covering the space. -/
lemma continuous_of_continuousOn_open_cover {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {f : X → Y} (hUc : ContinuousOn f U) (hVc : ContinuousOn f V) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · exact ContinuousOn.continuousAt hUc (hU.mem_nhds hxU)
  · exact ContinuousOn.continuousAt hVc (hV.mem_nhds (memV_of_not_memU hUV hxU))

/-- **Continuity of the global map** (S157 (d)): `twoChartF` is
continuous — on `U` the U-coordinate, on `V` the seam function pulled
back along `ψ`, glued by the open cover `U ∪ V = univ`. -/
lemma twoChartF_continuous {U V : Set X} {s u : ℝ} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂)
    (hUV : U ∪ V = univ) : Continuous (twoChartF hu1 φ ψ hUend hUV) := by
  exact continuous_of_continuousOn_open_cover hUopen hVopen hUV
    (twoChartF_continuousOn_U hu1 φ ψ hUend hUV)
    (twoChartF_continuousOn_V hs hu hu1 φ ψ hVend hUend hinc hUV)

/-! ## The inverse transition `Sfun` and its endpoint limit (S157 (e)) -/

/-- `y ∈ (s,1)` embedded into `(0,1)` (needs `0 < s`). -/
theorem embS {s : ℝ} (hs0 : 0 < s) {y : ℝ} (hy : y ∈ Set.Ioo s 1) : y ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨lt_trans hs0 hy.1, hy.2⟩

/-- The V-chart coordinate of an overlap point with U-coordinate `y` (the
inverse transition; `y ∈ (s,1)`, value in `(0,u)`), as a total real
function (0 off its domain). -/
noncomputable def Sfun {U V : Set X} {s : ℝ} (hs0 : 0 < s)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Ioo s 1 then
    ((ψ.symm ⟨(φ ⟨y, embS hs0 hy⟩ : X), (hVend ⟨y, embS hs0 hy⟩).mpr hy⟩
        : OpenRealInterval 0 1) : ℝ)
  else 0

/-- The overlap value of `Sfun` lies in `(0,u)`: V-coordinates of overlap
points lie in the V-overlap. -/
lemma Sfun_mem {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Sfun hs0 φ ψ hVend y ∈ Set.Ioo 0 u := by
  dsimp [Sfun]
  have hφV : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ V) := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let w : OpenRealInterval 0 1 := ψ.symm ⟨(φ ⟨y, embS hs0 hy⟩ : X), hφV⟩
  have hwU : (w : ℝ) ∈ Set.Ioo 0 u := by
    have hψwU : ((ψ w : X) ∈ U) := by
      have heq : (ψ w : X) = (φ ⟨y, embS hs0 hy⟩ : X) := by
        dsimp [w]
        exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
          (ψ.apply_symm_apply ⟨(φ ⟨y, embS hs0 hy⟩ : X), hφV⟩)
      have hφU : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ U) :=
        (φ ⟨y, embS hs0 hy⟩ : {x : X // x ∈ U}).2
      simpa [heq] using hφU
    exact (hUend w).1 hψwU
  rw [dif_pos hy]
  exact hwU

/-- `Tfun (Sfun y) = y` for overlap U-coordinates: the two transitions
are mutual inverses on the overlap. -/
lemma Tfun_of_Sfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y) = y := by
  -- Sfun y = w = V-coordinate of p := φ⟨y⟩; Tfun w = U-coordinate of ψ⟨w⟩ = p = y
  dsimp [Sfun]
  have hφV : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ V) := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let p : X := (φ ⟨y, embS hs0 hy⟩ : X)
  let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hφV⟩
  have hwU : (w : ℝ) ∈ Set.Ioo 0 u := by
    have hψwU : ((ψ w : X) ∈ U) := by
      have heq : (ψ w : X) = p := by
        dsimp [w]
        exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
          (ψ.apply_symm_apply ⟨p, hφV⟩)
      have hφU : p ∈ U := (φ ⟨y, embS hs0 hy⟩ : {x : X // x ∈ U}).2
      simpa [heq] using hφU
    exact (hUend w).1 hψwU
  rw [dif_pos hy]
  change Tfun hu1 φ ψ hUend (w : ℝ) = y
  -- Tfun (w:ℝ) = T-coord(w) = U-coordinate of ψ⟨w⟩; ψ⟨w⟩ = p = φ⟨y⟩; U-coordinate = y
  have hψp : (ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) = p := by
    have hwψ : (⟨(w : ℝ), emb01 hu1 hwU⟩ : OpenRealInterval 0 1) = w := by
      apply Subtype.ext
      rfl
    rw [hwψ]
    dsimp [w]
    exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
      (ψ.apply_symm_apply ⟨p, hφV⟩)
  have hφp : (φ ⟨y, embS hs0 hy⟩ : X) = p := rfl
  have hφarg : (⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X),
      (hUend ⟨(w : ℝ), emb01 hu1 hwU⟩).mpr hwU⟩ : {x : X // x ∈ U}) = φ ⟨y, embS hs0 hy⟩ := by
    apply Subtype.ext
    exact hψp
  rw [Tfun_eq hu1 φ ψ hUend hwU]
  dsimp [T]
  calc
    ((φ.symm ⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X),
        (hUend ⟨(w : ℝ), emb01 hu1 hwU⟩).mpr hwU⟩ : OpenRealInterval 0 1) : ℝ)
        = ((φ.symm (φ ⟨y, embS hs0 hy⟩) : OpenRealInterval 0 1) : ℝ) := by
          exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) hφarg
    _ = ((⟨y, embS hs0 hy⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
            (φ.symm_apply_apply ⟨y, embS hs0 hy⟩)
    _ = y := rfl

/-- `Sfun (T v) = v` for overlap V-coordinates: the other direction of
the mutual-inverse identity. -/
lemma Sfun_of_Tfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Sfun hs0 φ ψ hVend (T hu1 φ ψ hUend hv) = v := by
  have hy : T hu1 φ ψ hUend hv ∈ Set.Ioo s 1 := T_mem hs0 hu hu1 φ ψ hVend hUend hv
  dsimp [Sfun]
  rw [dif_pos hy]
  -- y := T hv is the U-coordinate of ψ⟨v⟩: the point φ⟨y⟩ equals ψ⟨v⟩,
  -- hence its V-coordinate is v.
  let p : X := (φ ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : X)
  have hφV : p ∈ V := (hVend ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩).mpr hy
  have hpψ : p = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
    -- y = U-coordinate of ψ⟨v⟩: T hu1 φ ψ hUend hv = U-coord(ψ⟨v⟩): so φ⟨y⟩ = ψ⟨v⟩
    have hyeq : ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩
        : OpenRealInterval 0 1) : ℝ) = T hu1 φ ψ hUend hv := rfl
    dsimp [p]
    -- φ applied to the ORI element ⟨T hv, embS⟩ equals ψ⟨v⟩:
    -- φ⟨U-coord⟩ of a point returns the point.
    have harg : (⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : OpenRealInterval 0 1) =
        φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩ := by
      apply Subtype.ext
      exact hyeq
    calc
      (φ ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : X)
          = (φ (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (φ z : X)) harg
      _ = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
            exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
              (φ.apply_symm_apply ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩)
  have hφarg : (⟨p, hφV⟩ : {x : X // x ∈ V}) = ψ ⟨v, emb01 hu1 hv⟩ := by
    apply Subtype.ext
    exact hpψ
  calc
    ((ψ.symm ⟨p, hφV⟩ : OpenRealInterval 0 1) : ℝ)
        = ((ψ.symm (ψ ⟨v, emb01 hu1 hv⟩) : OpenRealInterval 0 1) : ℝ) := by
          exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) hφarg
    _ = ((⟨v, emb01 hu1 hv⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
            (ψ.symm_apply_apply ⟨v, emb01 hu1 hv⟩)
    _ = v := rfl

/-- Range of `Sfun`: the V-coordinates of overlap points cover `(0,u)`.
(One direction: values lie in `(0,u)` by `Sfun_mem`; the other: every
`w ∈ (0,u)` is the V-coordinate of `ψ⟨w⟩`, whose U-coordinate is
`T hu1 φ ψ hUend ⟨w.1, w.2⟩`.) -/
lemma Sfun_range {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Sfun hs0 φ ψ hVend '' Set.Ioo s 1 = Set.Ioo 0 u := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨y, hy, hwy⟩
    have hwm : Sfun hs0 φ ψ hVend y ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy
    rwa [hwy] at hwm
  · intro hw
    exact ⟨T hu1 φ ψ hUend hw,
      T_mem hs0 hu hu1 φ ψ hVend hUend hw,
      Sfun_of_Tfun hs0 hu hu1 φ ψ hVend hUend hw⟩

/-- `Sfun` is strictly increasing on its domain `(s,1)`: it is the
inverse of the increasing `Tfun` (identity `Tfun (Sfun y) = y` + `hinc`). -/
lemma Sfun_strictMonoOn {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    StrictMonoOn (Sfun hs0 φ ψ hVend) (Set.Ioo s 1) := by
  intro y₁ hy₁ y₂ hy₂ hylt
  have hTmono := Tfun_strictMonoOn hu1 φ ψ hUend hinc
  have h1 : Sfun hs0 φ ψ hVend y₁ ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy₁
  have h2 : Sfun hs0 φ ψ hVend y₂ ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy₂
  by_contra hnot
  have hle : Sfun hs0 φ ψ hVend y₂ ≤ Sfun hs0 φ ψ hVend y₁ := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hTs : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) <
        Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) := hTmono h2 h1 hlt
    have hTs1 : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) = y₂ :=
      Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₂
    have hTs2 : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) = y₁ :=
      Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₁
    rw [hTs1, hTs2] at hTs
    exact (not_lt_of_ge (le_of_lt hylt)) hTs
  · have hTeq : y₂ = y₁ := by
      calc
        y₂ = Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) :=
          (Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₂).symm
        _ = Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) := by rw [heq]
        _ = y₁ := Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₁
    exact (ne_of_lt hylt) hTeq.symm

/-- **Endpoint-limit of the inverse transition (S157 (e))**: as the
U-coordinate `y` of an overlap point approaches `1` from below, its
V-coordinate `Sfun y` approaches `u` (the top of the V-overlap).
Invokes the fleet mirror of L31
(`Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top`) on the
strictly increasing surjection `Sfun`. -/
lemma Sfun_endpoint_top {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ∈ Set.Ioo s 1 → 1 - δ < y → u - ε < Sfun hs0 φ ψ hVend y := by
  exact Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top hs1
    (Sfun_strictMonoOn hs0 hu hu1 φ ψ hVend hUend hinc)
    (Sfun_range hs0 hu hu1 φ ψ hVend hUend)

/-- Upper bound: `Sfun y < u` on its domain (values live in `(0,u)`). -/
lemma Sfun_lt_u {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Sfun hs0 φ ψ hVend y < u := by
  exact (Sfun_mem hs0 hu1 φ ψ hVend hUend hy).2

/-! ## The inverse map `twoChartG` and its continuity (S157 (f)) -/

/-- **The inverse of the global map**: `y < 1` is the U-coordinate of a
point of `U` (`φ⟨y⟩`); `y ≥ 1` is the affine-shifted V-coordinate of a
point of the free V-tail (`ψ⟨y − 1 + u⟩`). -/
noncomputable def twoChartG {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (y : OpenRealInterval 0 (2 - u)) : X := by
  classical
  by_cases hy1 : (y : ℝ) < 1
  · exact (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X)
  · have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
    let w : ℝ := (y : ℝ) - 1 + u
    have hw0 : 0 < w := by dsimp [w]; linarith [hyge, hu]
    have hw1 : w < 1 := by dsimp [w]; linarith [y.2.2]
    exact (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X)

/-- Value of `twoChartG` for `y < 1`: the U-chart point `φ⟨y⟩`. -/
lemma twoChartG_apply_lt_one {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {y : OpenRealInterval 0 (2 - u)} (hy1 : (y : ℝ) < 1) :
    twoChartG hs0 hu φ ψ y = (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X) := by
  dsimp [twoChartG]
  rw [dif_pos hy1]

/-- Value of `twoChartG` for `y ≥ 1`: the V-tail point
`ψ⟨y − 1 + u⟩` (whose parameter lies in `[u,1)`). -/
lemma twoChartG_apply_ge_one {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {y : OpenRealInterval 0 (2 - u)} (hy1 : ¬ (y : ℝ) < 1) :
    twoChartG hs0 hu φ ψ y = (ψ ⟨(y : ℝ) - 1 + u, ⟨by
      have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
      have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hyge, hu]
      exact hw0, by
      have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
      exact hw1⟩⟩ : X) := by
  dsimp [twoChartG]
  rw [dif_neg hy1]

/-- `twoChartG` is continuous on the open piece `{y | (y : ℝ) < 1}`:
there it is `φ` applied to the coordinate. -/
lemma twoChartG_continuousOn_left {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ContinuousOn (twoChartG hs0 hu φ ψ)
      {y : OpenRealInterval 0 (2 - u) | (y : ℝ) < 1} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (OpenRealInterval 0 (2 - u)) := {y | (y : ℝ) < 1}
  change Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
    twoChartG hs0 hu φ ψ (a : OpenRealInterval 0 (2 - u)))
  have hf : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      ((a : OpenRealInterval 0 (2 - u)) : ℝ)) := by
    fun_prop
  have hc : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (⟨((a : OpenRealInterval 0 (2 - u)) : ℝ),
        ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩⟩ : OpenRealInterval 0 1)) := by
    exact Continuous.subtype_mk hf
      (fun a => ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩)
  have hφX : Continuous (fun z : OpenRealInterval 0 1 => (φ z : X)) := by
    exact continuous_subtype_val.comp φ.continuous
  have hclean : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (φ ⟨((a : OpenRealInterval 0 (2 - u)) : ℝ),
        ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩⟩ : X)) :=
    hφX.comp hc
  apply Continuous.congr hclean
  intro a
  exact (twoChartG_apply_lt_one hs0 hu φ ψ a.2).symm

lemma twoChartG_continuousOn_right {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ContinuousOn (twoChartG hs0 hu φ ψ)
      {y : OpenRealInterval 0 (2 - u) | 1 < (y : ℝ)} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (OpenRealInterval 0 (2 - u)) := {y | 1 < (y : ℝ)}
  change Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
    twoChartG hs0 hu φ ψ (a : OpenRealInterval 0 (2 - u)))
  have hc : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (⟨((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u,
          ⟨by
            have hyge : 1 ≤ ((a : OpenRealInterval 0 (2 - u)) : ℝ) := le_of_lt a.2
            have hw0 : 0 < ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u := by linarith [hyge, hu]
            exact hw0, by
            have hw1 : ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u < 1 := by
              linarith [(a : OpenRealInterval 0 (2 - u)).2.2]
            exact hw1⟩⟩ : OpenRealInterval 0 1)) := by
    apply Continuous.subtype_mk
    fun_prop
  have hψ : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (ψ ⟨((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u,
        ⟨by
          have hyge : 1 ≤ ((a : OpenRealInterval 0 (2 - u)) : ℝ) := le_of_lt a.2
          have hw0 : 0 < ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u := by linarith [hyge, hu]
          exact hw0, by
          have hw1 : ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u < 1 := by
            linarith [(a : OpenRealInterval 0 (2 - u)).2.2]
          exact hw1⟩⟩ : X)) := by
    exact continuous_subtype_val.comp (ψ.continuous.comp hc)
  apply Continuous.congr hψ
  intro a
  have hge : ¬ ((a : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := not_lt_of_gt a.2
  rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]

/-! ## The seam identity and continuity of `twoChartG` at `y = 1` -/

/-- **Seam identity**: an overlap point with U-coordinate `y ∈ (s,1)` is
`ψ⟨Sfun y⟩` (its V-coordinate is `Sfun y`). -/
lemma φ_eq_ψ_Sfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X)
      = (φ ⟨y, embS hs0 hy⟩ : X) := by
  let p : X := (φ ⟨y, embS hs0 hy⟩ : X)
  have hφV : p ∈ V := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hφV⟩
  have hS : Sfun hs0 φ ψ hVend y = (w : ℝ) := by
    dsimp [Sfun, w]
    rw [dif_pos hy]
  have harg : (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) = w := by
    apply Subtype.ext
    exact hS
  calc
    (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X)
        = (ψ w : X) := by
          exact congrArg (fun z : OpenRealInterval 0 1 => (ψ z : X)) harg
    _ = p := by
          dsimp [w]
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
            (ψ.apply_symm_apply ⟨p, hφV⟩)
    _ = (φ ⟨y, embS hs0 hy⟩ : X) := rfl

/-! ## Seam convergence of `twoChartG` at `y = 1` (S157 (f) step 2) -/

/-- **Left convergence at the seam**: for any neighbourhood `N` of
`ψ⟨u⟩`, the left-hand values `φ⟨y⟩ = ψ⟨Sfun y⟩` (overlap U-coordinates
`y ∈ (s,1)` sufficiently close to `1` from below) lie in `N`.  Proof:
pull `N` back under the homeo `ψ` to a real neighbourhood of `u`
(metric ball of radius `η`); `Sfun_endpoint_top` + `Sfun_lt_u` give
`|Sfun y − u| < η` eventually; the seam identity `φ_eq_ψ_Sfun`
identifies `ψ⟨Sfun y⟩` with `φ⟨y⟩`. -/
lemma twoChartG_left_converge {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂) :
    ∀ N : Set X, N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ, ∀ hy : y ∈ Set.Ioo s 1, 1 - δ < y →
          ((φ ⟨y, embS hs0 hy⟩ : X) ∈ N) := by
  intro N hN
  let hu1 : u ≤ 1 := le_of_lt hu1s
  have hm : Continuous (fun t : OpenRealInterval 0 1 => (ψ t : X)) :=
    continuous_subtype_val.comp ψ.continuous
  have hpre : (fun t : OpenRealInterval 0 1 => (ψ t : X)) ⁻¹' N ∈ 𝓝 ⟨u, ⟨hu, hu1s⟩⟩ :=
    hm.continuousAt.preimage_mem_nhds hN
  rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hηpos, hball⟩
  have hballN : ∀ t : OpenRealInterval 0 1,
      dist t ⟨u, ⟨hu, hu1s⟩⟩ < η → (ψ t : X) ∈ N := by
    intro t ht
    exact hball (by simpa [Metric.mem_ball] using ht)
  rcases Sfun_endpoint_top hs0 hs1 hu hu1 φ ψ hVend hUend hinc η hηpos with ⟨δ₁, hδ₁pos, hδ₁⟩
  let δ : ℝ := min δ₁ (1 - s)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₁pos (sub_pos.mpr hs1)
  refine ⟨δ, hδpos, ?_⟩
  intro y hy hyδ
  have hyδ₁ : 1 - δ₁ < y := by
    have hδ₁le : δ ≤ δ₁ := by dsimp [δ]; exact min_le_left δ₁ (1 - s)
    linarith
  have hlow : u - η < Sfun hs0 φ ψ hVend y := hδ₁ y hy hyδ₁
  have hup : Sfun hs0 φ ψ hVend y < u := Sfun_lt_u hs0 hu1 φ ψ hVend hUend hy
  have hSnear : dist (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) (⟨u, ⟨hu, hu1s⟩⟩ : OpenRealInterval 0 1) < η := by
    have habs : |Sfun hs0 φ ψ hVend y - u| < η := by
      rw [abs_lt]
      constructor <;> linarith
    change dist (Sfun hs0 φ ψ hVend y) u < η
    rw [Real.dist_eq]
    exact habs
  have hψin : (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X) ∈ N :=
    hballN (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) hSnear
  have hid := φ_eq_ψ_Sfun hs0 hu hu1 φ ψ hVend hUend hy
  rwa [hid] at hψin

/-- **Right convergence at the seam**: `twoChartG⟨y⟩ = ψ⟨y − 1 + u⟩ →
ψ⟨u⟩` as `y → 1⁺` (affine reparametrisation of the continuous `ψ`). -/
lemma twoChartG_right_converge {U V : Set X} {s u : ℝ} (hs0 : 0 < s)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ∀ N : Set X, N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : OpenRealInterval 0 (2 - u), 1 < (y : ℝ) → (y : ℝ) - 1 < δ →
          (twoChartG hs0 hu φ ψ y ∈ N) := by
  intro N hN
  let hu1 : u ≤ 1 := le_of_lt hu1s
  have hm : Continuous (fun t : OpenRealInterval 0 1 => (ψ t : X)) :=
    continuous_subtype_val.comp ψ.continuous
  have hpre : (fun t : OpenRealInterval 0 1 => (ψ t : X)) ⁻¹' N ∈ 𝓝 ⟨u, ⟨hu, hu1s⟩⟩ :=
    hm.continuousAt.preimage_mem_nhds hN
  rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hηpos, hball⟩
  have hballN : ∀ t : OpenRealInterval 0 1,
      dist t ⟨u, ⟨hu, hu1s⟩⟩ < η → (ψ t : X) ∈ N := by
    intro t ht
    exact hball (by simpa [Metric.mem_ball] using ht)
  refine ⟨η, hηpos, ?_⟩
  intro y hygt hyη
  have hge : ¬ (y : ℝ) < 1 := not_lt_of_gt hygt
  rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]
  have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hu, hygt]
  have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
  have hnear : dist (⟨(y : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1)
      (⟨u, ⟨hu, hu1s⟩⟩ : OpenRealInterval 0 1) < η := by
    have habs : |((y : ℝ) - 1 + u) - u| < η := by
      rw [abs_lt]
      constructor <;> linarith
    change dist ((y : ℝ) - 1 + u) u < η
    rw [Real.dist_eq]
    exact habs
  exact hballN (⟨(y : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1) hnear

/-- Subtype distance is the induced distance on values. -/
lemma dist_subtype_val {α : Type*} [PseudoMetricSpace α] (p : α → Prop)
    (x y : {a : α // p a}) : dist x y = dist (x : α) (y : α) := rfl

/-! ## Seam continuity of `twoChartG` and the full continuity (S157 (f) step 3) -/

/-- Continuity of `twoChartG` at the seam point `⟨1, ·⟩`: left values
`φ⟨y⟩ = ψ⟨Sfun y⟩ → ψ⟨u⟩` (`twoChartG_left_converge`), right values
`ψ⟨y − 1 + u⟩ → ψ⟨u⟩` (`twoChartG_right_converge`). -/
lemma twoChartG_continuousAt_seam {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂)
    {hm : 1 ∈ Set.Ioo 0 (2 - u)} :
    ContinuousAt (twoChartG hs0 hu φ ψ) ⟨1, hm⟩ := by
  have hval0 : twoChartG hs0 hu φ ψ ⟨1, hm⟩ = (ψ ⟨u, ⟨hu, hu1s⟩⟩ : X) := by
    have hge : ¬ (1 : ℝ) < 1 := by norm_num
    rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]
    congr 1
    apply Subtype.ext
    ring_nf
  rw [continuousAt_def]
  intro N hN
  have hN' : N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) := by
    simpa [hval0] using hN
  rcases twoChartG_left_converge hs0 hs1 hu hu1s φ ψ hVend hUend hinc N hN' with ⟨δₗ, hδₗpos, hδₗ⟩
  rcases twoChartG_right_converge hs0 hu hu1s φ ψ N hN' with ⟨δᵣ, hδᵣpos, hδᵣ⟩
  let ε : ℝ := min δₗ (min δᵣ (1 - s))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδₗpos (lt_min hδᵣpos (sub_pos.mpr hs1))
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hεpos, ?_⟩
  intro z hz
  have hzabs : |(z : ℝ) - 1| < ε := by
    have hz1 : dist (z : ℝ) 1 < ε := by
      rw [Metric.mem_ball] at hz
      rw [dist_subtype_val] at hz
      simpa using hz
    rwa [Real.dist_eq] at hz1
  by_cases hzlt : (z : ℝ) < 1
  · have hval_gt_s : s < (z : ℝ) := by
      have h1 : 1 - ε < (z : ℝ) := by linarith [(abs_lt.mp hzabs).1]
      have hεs : ε ≤ 1 - s := by
        dsimp [ε]
        exact le_trans (min_le_right δₗ (min δᵣ (1 - s))) (min_le_right δᵣ (1 - s))
      linarith
    have hvalmem : (z : ℝ) ∈ Set.Ioo s 1 := ⟨hval_gt_s, hzlt⟩
    have hzδl : 1 - δₗ < (z : ℝ) := by
      have h1 : 1 - ε < (z : ℝ) := by linarith [(abs_lt.mp hzabs).1]
      have hεδl : ε ≤ δₗ := by
        dsimp [ε]
        exact min_le_left δₗ (min δᵣ (1 - s))
      linarith
    have hφin : (φ ⟨(z : ℝ), embS hs0 hvalmem⟩ : X) ∈ N := hδₗ (z : ℝ) hvalmem hzδl
    have hval2 : twoChartG hs0 hu φ ψ z = (φ ⟨(z : ℝ), embS hs0 hvalmem⟩ : X) := by
      rw [twoChartG_apply_lt_one hs0 hu φ ψ hzlt]
    rwa [← hval2] at hφin
  · by_cases hzeq : (z : ℝ) = 1
    · have hzdef : z = ⟨1, hm⟩ := by
        apply Subtype.ext
        exact hzeq
      rw [hzdef]
      change twoChartG hs0 hu φ ψ ⟨1, hm⟩ ∈ N
      rw [hval0]
      exact mem_of_mem_nhds hN'
    · have hgt1 : 1 < (z : ℝ) := lt_of_le_of_ne (le_of_not_gt hzlt) (by intro h; exact hzeq h.symm)
      have hzδr : (z : ℝ) - 1 < δᵣ := by
        have hεδr : ε ≤ δᵣ := by
          dsimp [ε]
          exact le_trans (min_le_right δₗ (min δᵣ (1 - s))) (min_le_left δᵣ (1 - s))
        linarith [(abs_lt.mp hzabs).2, hεδr]
      exact hδᵣ z hgt1 hzδr

/-- **`twoChartG` is continuous** (three pieces: the two open pieces and
the seam point, glued by the convergence lemmas). -/
lemma twoChartG_continuous {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂) :
    Continuous (twoChartG hs0 hu φ ψ) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy (y : ℝ) 1 with hlt | heq | hgt
  · exact ContinuousOn.continuousAt (twoChartG_continuousOn_left hs0 hu φ ψ)
      (by
        have hp : (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) ⁻¹' (Set.Iio 1) ∈ 𝓝 y :=
          (continuous_subtype_val.continuousAt).preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
        simpa [Set.preimage, Set.Iio] using hp)
  · have hmem : 1 ∈ Set.Ioo 0 (2 - u) := by simpa [heq] using y.2
    have hydef : y = ⟨1, hmem⟩ := by
      apply Subtype.ext
      exact heq
    rw [hydef]
    exact twoChartG_continuousAt_seam hs0 hs1 hu hu1s φ ψ hVend hUend hinc (hm := hmem)
  · exact ContinuousOn.continuousAt (twoChartG_continuousOn_right hs0 hu φ ψ)
      (by
        have hp : (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) ⁻¹' (Set.Ioi 1) ∈ 𝓝 y :=
          (continuous_subtype_val.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
        simpa [Set.preimage, Set.Ioi] using hp)

/-! ## The two-chart gluing theorem (S157 (f) step 4) -/

/-- `twoChartG` is the left inverse of `twoChartF`. -/
lemma twoChartG_comp_twoChartF {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (x : X) :
    twoChartG hs0 hu φ ψ (twoChartF hu1 φ ψ hUend hUV x) = x := by
  by_cases hxU : x ∈ U
  · let Fx : OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV x
    have hFx : (Fx : ℝ) < 1 := by
      dsimp [Fx]
      rw [twoChartF_val_memU hu1 φ ψ hUend hUV hxU]
      exact (φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1).2.2
    dsimp [twoChartG]
    rw [dif_pos hFx]
    have harg : (⟨(Fx : ℝ), ⟨Fx.2.1, hFx⟩⟩ : OpenRealInterval 0 1) = φ.symm ⟨x, hxU⟩ := by
      apply Subtype.ext
      dsimp [Fx]
      exact twoChartF_val_memU hu1 φ ψ hUend hUV hxU
    calc
      (φ ⟨(Fx : ℝ), ⟨Fx.2.1, hFx⟩⟩ : X)
          = (φ (φ.symm ⟨x, hxU⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (φ z : X)) harg
      _ = x := by
            exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨x, hxU⟩)
  · let Fx : OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV x
    have hge : ¬ (Fx : ℝ) < 1 := by
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV hxU
      exact not_lt_of_ge (by linarith)
    dsimp [twoChartG]
    rw [dif_neg hge]
    have hw0 : 0 < (Fx : ℝ) - 1 + u := by
      have hv0 : 0 < ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) :=
        (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1).2.1
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      nlinarith
    have hw1 : (Fx : ℝ) - 1 + u < 1 := by
      have hv1 : ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) < 1 :=
        (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1).2.2
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      nlinarith
    have harg : (⟨(Fx : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1) =
        ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ := by
      apply Subtype.ext
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      ring
    calc
      (ψ ⟨(Fx : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : X)
          = (ψ (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (ψ z : X)) harg
      _ = x := by
            exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
              (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)

/-- `twoChartF` is the right inverse of `twoChartG`. -/
lemma twoChartF_comp_twoChartG {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (y : OpenRealInterval 0 (2 - u)) :
    twoChartF hu1 φ ψ hUend hUV (twoChartG hs0 hu φ ψ y) = y := by
  apply Subtype.ext
  by_cases hy1 : (y : ℝ) < 1
  · have hGy : twoChartG hs0 hu φ ψ y = (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X) :=
      twoChartG_apply_lt_one hs0 hu φ ψ hy1
    have hGU : twoChartG hs0 hu φ ψ y ∈ U := by
      rw [hGy]
      exact (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : {x : X // x ∈ U}).2
    dsimp [twoChartF]
    rw [dif_pos hGU]
    have harg : (⟨twoChartG hs0 hu φ ψ y, hGU⟩ : {x : X // x ∈ U}) = φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ := by
      apply Subtype.ext
      exact hGy
    calc
      ((φ.symm ⟨twoChartG hs0 hu φ ψ y, hGU⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : OpenRealInterval 0 1) : ℝ) := by
            simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
              (φ.symm_apply_apply ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩)
      _ = (y : ℝ) := rfl
  · have hGy : twoChartG hs0 hu φ ψ y = (ψ ⟨(y : ℝ) - 1 + u, ⟨by
        have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
        have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
        exact hw0, by
        have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
        exact hw1⟩⟩ : X) := twoChartG_apply_ge_one hs0 hu φ ψ hy1
    have hnotGU : twoChartG hs0 hu φ ψ y ∉ U := by
      rw [hGy]
      intro hU
      have hwu : (y : ℝ) - 1 + u ∈ Set.Ioo 0 u := by
        exact (hUend ⟨(y : ℝ) - 1 + u, ⟨by
          have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
          have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
          exact hw0, by
          have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
          exact hw1⟩⟩).1 hU
      have hgeu : u ≤ (y : ℝ) - 1 + u := by linarith [le_of_not_gt hy1]
      exact (not_lt_of_ge hgeu) hwu.2
    dsimp [twoChartF]
    rw [dif_neg hnotGU]
    have harg : (⟨twoChartG hs0 hu φ ψ y, memV_of_not_memU hUV hnotGU⟩ : {x : X // x ∈ V}) =
        ψ ⟨(y : ℝ) - 1 + u, ⟨by
          have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
          have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
          exact hw0, by
          have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
          exact hw1⟩⟩ := by
      apply Subtype.ext
      exact hGy
    calc
      ((ψ.symm ⟨twoChartG hs0 hu φ ψ y, memV_of_not_memU hUV hnotGU⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u
          = ((ψ.symm (ψ ⟨(y : ℝ) - 1 + u, ⟨by
              have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
              have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
              exact hw0, by
              have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
              exact hw1⟩⟩) : OpenRealInterval 0 1) : ℝ) + 1 - u := by
              exact congrArg (fun r : ℝ => r + 1 - u)
                (congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg)
      _ = ((⟨(y : ℝ) - 1 + u, ⟨by
              have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
              have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
              exact hw0, by
              have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
              exact hw1⟩⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u := by
              simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
                (ψ.symm_apply_apply ⟨(y : ℝ) - 1 + u, ⟨by
                  have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
                  have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
                  exact hw0, by
                  have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
                  exact hw1⟩⟩)
      _ = (y : ℝ) := by ring_nf

/-- **The two-chart gluing theorem**: two open-interval charts of a space
whose overlap is the right end of one and the left end of the other
(facing, orientation-preserving) cover a space homeomorphic to an open
real interval.  `twoChartF` and `twoChartG` are mutual inverses
(`twoChartF_comp_twoChartG`, `twoChartG_comp_twoChartF`), both
continuous (`twoChartF_continuous`, `twoChartG_continuous`). -/
theorem two_chart_glue_homeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂)
    (hUV : U ∪ V = univ) :
    Nonempty (X ≃ₜ OpenRealInterval 0 (2 - u)) := by
  let hu1 : u ≤ 1 := le_of_lt hu1s
  let F : X → OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV
  let G : OpenRealInterval 0 (2 - u) → X := twoChartG hs0 hu φ ψ
  have hcF : Continuous F := by
    dsimp [F]
    exact twoChartF_continuous hUopen hVopen hs0 hu hu1 φ ψ hVend hUend hinc hUV
  have hcG : Continuous G := by
    dsimp [G]
    exact twoChartG_continuous hs0 hs1 hu hu1s φ ψ hVend hUend hinc
  let e : X ≃ OpenRealInterval 0 (2 - u) := ⟨F, G,
    (fun x => by
      dsimp [F, G]
      exact twoChartG_comp_twoChartF hs0 hu hu1 φ ψ hUend hUV x),
    (fun y => by
      dsimp [F, G]
      exact twoChartF_comp_twoChartG hs0 hu hu1 φ ψ hUend hUV y)⟩
  exact ⟨Homeomorph.mk e (by simpa [e] using hcF) (by simpa [e] using hcG)⟩

/-! ## Finite chains of real intervals (S158: coordinate model of the
sweep) -/

/-- A finite chain of open real intervals with consecutive overlaps has
an open-interval union: the coordinate model of the interval side of the
sweep (on `ℝ` there is no wrapping, so consecutive overlaps suffice). -/
theorem range_chain_union_interval (n : ℕ) (I : ℕ → Set ℝ)
    (hI : ∀ j, j < n + 1 → ∃ a b : ℝ, I j = Set.Ioo a b)
    (hchain : ∀ j, j < n → (I j ∩ I (j + 1)).Nonempty) :
    ∃ a b : ℝ, (⋃ j ∈ Finset.range (n + 1), I j) = Set.Ioo a b := by
  induction n with
  | zero =>
      rcases hI 0 (by omega) with ⟨a, b, hI0⟩
      refine ⟨a, b, ?_⟩
      simp [Finset.range_one, hI0]
  | succ n ih =>
      have hIn : ∀ j, j < n + 1 → ∃ a b : ℝ, I j = Set.Ioo a b := by
        intro j hj
        exact hI j (by omega)
      have hch : ∀ j, j < n → (I j ∩ I (j + 1)).Nonempty := by
        intro j hj
        exact hchain j (by omega)
      rcases ih hIn hch with ⟨lo, hi, hU⟩
      rcases hI (n + 1) (by omega) with ⟨a, b, hI1⟩
      have hmemIn : I n ⊆ (⋃ j ∈ Finset.range (n + 1), I j) := by
        intro x hx
        exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega), hx⟩
      have hov : (Set.Ioo lo hi ∩ Set.Ioo a b).Nonempty := by
        rcases hchain n (by omega) with ⟨x, hx1, hx2⟩
        have hxU : x ∈ Set.Ioo lo hi := by
          rw [← hU]
          exact hmemIn hx1
        have hx2' : x ∈ Set.Ioo a b := by
          rwa [hI1] at hx2
        exact ⟨x, hxU, hx2'⟩
      rcases union_Ioo_of_overlap hov with ⟨l, h, hUunion⟩
      refine ⟨l, h, ?_⟩
      calc
        (⋃ j ∈ Finset.range (n + 2), I j)
            = (⋃ j ∈ Finset.range (n + 1), I j) ∪ I (n + 1) := by
              ext x
              constructor
              · intro hx
                rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
                have hjlt : j < n + 2 := Finset.mem_range.mp hj
                by_cases hjn : j < n + 1
                · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, hxj⟩)
                · have hj' : j = n + 1 := by omega
                  exact Or.inr (by simpa [hj'] using hxj)
              · intro hx
                rcases hx with hx1 | hx2
                · rcases Set.mem_iUnion₂.mp hx1 with ⟨j, hj, hxj⟩
                  have hjlt : j < n + 1 := Finset.mem_range.mp hj
                  exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hxj⟩
                · exact Set.mem_iUnion₂.mpr ⟨n + 1, Finset.mem_range.mpr (by omega), hx2⟩
        _ = Set.Ioo l h := by
              rw [hU, hI1]
              exact hUunion

/-! ## The single-junction extension lemma (S158) -/

/-- **Subset reassociation homeo**: a subset `U ⊆ W` read as a subtype
of the ambient space and as a subtype of the `W`-subtype are the same
topological space (the identity on values).  (Generalises the
union-subtype reassociation: both chart reassociations of the
single-junction extension use one instance with `W := U ∪ V` and the
two inclusions `U ⊆ U∪V`, `V ⊆ U∪V`.) -/
noncomputable def unionSubtypeHomeo {Y : Type*} [TopologicalSpace Y] {U W : Set Y}
    (hsub : U ⊆ W) : {y : Y // y ∈ U} ≃ₜ
      {z : {x : Y // x ∈ W} // (z : Y) ∈ U} where
  toFun := fun y => ⟨⟨(y : Y), hsub y.2⟩, y.2⟩
  invFun := fun z => ⟨((z : {x : Y // x ∈ W}) : Y), z.2⟩
  left_inv := by intro y; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## The single-junction extension lemma (S158) -/

theorem single_junction_extension {Y : Type*} [TopologicalSpace Y] {U V : Set Y}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (η : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((η t) : Y) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : Y) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) η ψ hUend v₁ < Tfun (le_of_lt hu1s) η ψ hUend v₂) :
    Nonempty ({z : Y // z ∈ U ∪ V} ≃ₜ OpenRealInterval 0 (2 - u)) := by
  let hu1 : u ≤ 1 := le_of_lt hu1s
  let X := {z : Y // z ∈ U ∪ V}
  let U' : Set X := {z : X | (z : Y) ∈ U}
  let V' : Set X := {z : X | (z : Y) ∈ V}
  have hU'open : IsOpen U' := by
    dsimp [U']
    exact hUopen.preimage continuous_subtype_val
  have hV'open : IsOpen V' := by
    dsimp [V']
    exact hVopen.preimage continuous_subtype_val
  have hUV' : U' ∪ V' = univ := by
    ext z
    constructor
    · intro hz; exact trivial
    · intro hz
      rcases z.2 with hU | hV
      · exact Or.inl (by simpa [U'] using hU)
      · exact Or.inr (by simpa [V'] using hV)
  let reassocU : {y : Y // y ∈ U} ≃ₜ {z : {x : Y // x ∈ U ∪ V} // (z : Y) ∈ U} :=
    unionSubtypeHomeo (U := U) (W := U ∪ V) (by intro y hy; exact Or.inl hy)
  let reassocV : {y : Y // y ∈ V} ≃ₜ {z : {x : Y // x ∈ U ∪ V} // (z : Y) ∈ V} :=
    unionSubtypeHomeo (U := V) (W := U ∪ V) (by intro y hy; exact Or.inr hy)
  let η' : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U'} := η.trans reassocU
  let ψ' : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V'} := ψ.trans reassocV
  have hxU : ∀ t : OpenRealInterval 0 1,
      (((η' t : {x : X // x ∈ U'}) : X) : Y) = ((η t : {y : Y // y ∈ U}) : Y) := by
    intro t
    dsimp [η', reassocU]
    rfl
  have hxV : ∀ t : OpenRealInterval 0 1,
      (((ψ' t : {x : X // x ∈ V'}) : X) : Y) = ((ψ t : {y : Y // y ∈ V}) : Y) := by
    intro t
    dsimp [ψ', reassocV]
    rfl
  have hVend' : ∀ t : OpenRealInterval 0 1, ((η' t : {x : X // x ∈ U'}) : X) ∈ V' ↔
      (t : ℝ) ∈ Set.Ioo s 1 := by
    intro t
    constructor
    · intro ht
      have hval : (((η' t : {x : X // x ∈ U'}) : X) : Y) ∈ V := by
        simpa [V'] using ht
      have hyt : ((η t : {y : Y // y ∈ U}) : Y) ∈ V := by
        simpa [hxU t] using hval
      exact (hVend t).1 hyt
    · intro hyt
      have hval : (((η' t : {x : X // x ∈ U'}) : X) : Y) ∈ V := by
        simpa [hxU t] using ((hVend t).2 hyt)
      simpa [V'] using hval
  have hUend' : ∀ t : OpenRealInterval 0 1, ((ψ' t : {x : X // x ∈ V'}) : X) ∈ U' ↔
      (t : ℝ) ∈ Set.Ioo 0 u := by
    intro t
    constructor
    · intro ht
      have hval : (((ψ' t : {x : X // x ∈ V'}) : X) : Y) ∈ U := by
        simpa [U'] using ht
      have hyt : ((ψ t : {y : Y // y ∈ V}) : Y) ∈ U := by
        simpa [hxV t] using hval
      exact (hUend t).1 hyt
    · intro hyt
      have hval : (((ψ' t : {x : X // x ∈ V'}) : X) : Y) ∈ U := by
        simpa [hxV t] using ((hUend t).2 hyt)
      simpa [U'] using hval
  -- invariance of the transition coordinate under reassociation:
  have hTfun : ∀ {v : ℝ} (hv : v ∈ Set.Ioo 0 u),
      Tfun hu1 η' ψ' hUend' v = Tfun hu1 η ψ hUend v := by
    intro v hv
    rw [Tfun_eq hu1 η' ψ' hUend' hv, Tfun_eq hu1 η ψ hUend hv]
    dsimp [T, η', ψ', reassocU, reassocV, unionSubtypeHomeo]

  have hinc' : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
      Tfun (le_of_lt hu1s) η' ψ' hUend' v₁ < Tfun (le_of_lt hu1s) η' ψ' hUend' v₂ := by
    intro v₁ v₂ hv₁ hv₂ hvlt
    have h1 := hinc hv₁ hv₂ hvlt
    -- rewrite Tfun η' ψ' hUend' → Tfun η ψ hUend on both sides via hTfun
    rwa [hTfun hv₁, hTfun hv₂]
  exact two_chart_glue_homeo hU'open hV'open hs0 hs1 hu hu1s η' ψ' hVend' hUend' hinc' hUV'

/-! ## The prefix-union step (S159) -/

-- normalization: (0, 2-u) ≃ (0,1) via L30 (affine)
lemma norm01 {u : ℝ} (hu1s : u < 1) : Nonempty (OpenRealInterval 0 (2 - u) ≃ₜ OpenRealInterval 0 1) := by
  have hpos : 0 < 2 - u := by linarith
  exact Commons.Topology.Homeomorph.open_interval_affine hpos (by norm_num)

/-- **S159 base+first-step**: two open traces `T₀ T₁` of an ambient
space with interval charts `η₀ η₁` whose overlap is the facing terminal
pair (right end `(s,1)` of `T₀`, left end `(0,u)` of `T₁` in
coordinates, monotone transition) glue to a single interval chart of the
prefix union: `{z | z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1`. -/
theorem prefix_two_charts_interval {Y : Type*} [TopologicalSpace Y]
    (T₀ T₁ : Set Y) (hT₀open : IsOpen T₀) (hT₁open : IsOpen T₁)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (η₀ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T₀})
    (η₁ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T₁})
    (hVend : ∀ t : OpenRealInterval 0 1, ((η₀ t) : Y) ∈ T₁ ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((η₁ t) : Y) ∈ T₀ ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) η₀ η₁ hUend v₁ < Tfun (le_of_lt hu1s) η₀ η₁ hUend v₂) :
    Nonempty ({z : Y // z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1) := by
  rcases single_junction_extension (U := T₀) (V := T₁) hT₀open hT₁open hs0 hs1 hu hu1s
      η₀ η₁ hVend hUend hinc with ⟨hmid⟩
  rcases norm01 (u := u) hu1s with ⟨hnorm⟩
  exact ⟨hmid.trans hnorm⟩

/-! ## The abstract chain step (S159) -/

/-- Reassociation along a set equality. -/
noncomputable def setEqSubtypeHomeo {Y : Type*} [TopologicalSpace Y] {s t : Set Y} (h : s = t) :
    {z : Y // z ∈ s} ≃ₜ {z : Y // z ∈ t} where
  toFun := fun z => ⟨(z : Y), by rw [← h]; exact z.2⟩
  invFun := fun z => ⟨(z : Y), by rw [h]; exact z.2⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- range (k+2) splits into range (k+1) and {k+1}. -/
lemma union_range_succ {Y : Type*} (T : ℕ → Set Y) (k : ℕ) :
    (⋃ j ∈ Finset.range (k + 2), T j) =
      (⋃ j ∈ Finset.range (k + 1), T j) ∪ T (k + 1) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
    have hjlt : j < k + 2 := Finset.mem_range.mp hj
    by_cases hjn : j < k + 1
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, hxj⟩)
    · have hj' : j = k + 1 := by omega
      exact Or.inr (by simpa [hj'] using hxj)
  · intro hx
    rcases hx with hx1 | hx2
    · rcases Set.mem_iUnion₂.mp hx1 with ⟨j, hj, hxj⟩
      have hjlt : j < k + 1 := Finset.mem_range.mp hj
      exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hxj⟩
    · exact Set.mem_iUnion₂.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), hx2⟩

/-- **The abstract chain step (S159)**: the prefix union up to `k` is an
interval chart `κk`; the new trace `T (k+1)` attaches along a facing
terminal overlap (right end `(s,1)` of the prefix in `κk` coordinates,
left end `(0,u)` of the new chart, monotone transition).  Then the
prefix up to `k+1` is an interval chart. -/
theorem chain_step {Y : Type*} [TopologicalSpace Y] (T : ℕ → Set Y) (k : ℕ)
    (hUopen : IsOpen (⋃ j ∈ Finset.range (k + 1), T j))
    (hnewopen : IsOpen (T (k + 1)))
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hVend : ∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) κk ηnew hUend v₁ < Tfun (le_of_lt hu1s) κk ηnew hUend v₂) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 2), T j}) := by
  let U : Set Y := ⋃ j ∈ Finset.range (k + 1), T j
  let V : Set Y := T (k + 1)
  rcases single_junction_extension (U := U) (V := V) hUopen hnewopen hs0 hs1 hu hu1s
      κk ηnew hVend hUend hinc with ⟨hmid⟩
  -- hmid : {z // z ∈ U ∪ V} ≃ₜ ORI 0 (2-u)
  have hnorm : Nonempty (OpenRealInterval 0 (2 - u) ≃ₜ OpenRealInterval 0 1) := by
    have hpos : 0 < 2 - u := by linarith
    exact Commons.Topology.Homeomorph.open_interval_affine hpos (by norm_num)
  rcases hnorm with ⟨hN⟩
  -- reassociate {z//z∈U∪V} to {z//z∈⋃range(k+2)} via the union-split equality
  have hsplit : (U ∪ V : Set Y) = (⋃ j ∈ Finset.range (k + 2), T j) := by
    dsimp [U, V]
    exact (union_range_succ T k).symm
  exact ⟨hN.symm.trans (hmid.symm.trans (setEqSubtypeHomeo hsplit))⟩

variable {Y : Type*} [TopologicalSpace Y]

/-- The prefix union `⋃ j ∈ range (k+1), T j` is open (finite union of
open traces). -/
lemma prefix_open (T : ℕ → Set Y) (hopen : ∀ j, IsOpen (T j)) (k : ℕ) :
    IsOpen (⋃ j ∈ Finset.range (k + 1), T j) := by
  induction k with
  | zero =>
      -- range 1 = {0}
      rw [show Finset.range (0 + 1) = {0} by simp]
      simp [hopen 0]
  | succ k ih =>
      rw [union_range_succ]
      exact ih.union (hopen (k + 1))

/-- Base case `k = 0`: the single trace `T 0` (chart `η 0`) is the
`(0+1)`-prefix interval. -/
theorem prefix_zero_interval (T : ℕ → Set Y)
    (η0 : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T 0}) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (0 + 1), T j}) := by
  have hsplit : (⋃ j ∈ Finset.range (0 + 1), T j) = T 0 := by
    simp [Finset.range_one]
  exact ⟨η0.trans (setEqSubtypeHomeo (hsplit.symm))⟩

/-- The chain step with prefix-openness derived from the per-trace
openness. -/
theorem chain_step_open (T : ℕ → Set Y) (k : ℕ) (hopen : ∀ j, IsOpen (T j))
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hVend : ∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) κk ηnew hUend v₁ < Tfun (le_of_lt hu1s) κk ηnew hUend v₂) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 2), T j}) :=
  chain_step T k (prefix_open T hopen k) (hopen (k + 1)) hs0 hs1 hu hu1s κk ηnew hVend hUend hinc

/-- **The finite-chain interval theorem (S160)**: given interval charts
of every trace and, at each level, the facing terminal-overlap data
stated against the current prefix homeo, every prefix union
`⋃ j ∈ range (k+1), T j` is an open real interval chart. -/
theorem finite_prefix_interval (T : ℕ → Set Y) (hopen : ∀ j, IsOpen (T j))
    (η : ∀ j, OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T j})
    (hdata : ∀ k : ℕ,
        ∀ κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j},
          ∃ s u : ℝ, ∃ hs0 : 0 < s, ∃ hs1 : s < 1, ∃ hu : 0 < u, ∃ hu1s : u < 1,
            ∃ ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)},
            ∃ hUend : (∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
                  (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u),
              (∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1) ∧
              (∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
                  Tfun (u := u) (le_of_lt hu1s) κk ηnew hUend v₁ <
                  Tfun (u := u) (le_of_lt hu1s) κk ηnew hUend v₂)) :
    ∀ k : ℕ, Nonempty (OpenRealInterval 0 1 ≃ₜ
      {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j}) := by
  intro k
  induction k with
  | zero =>
      exact prefix_zero_interval T (η 0)
  | succ k ih =>
      classical
      rcases ih with ⟨κk⟩
      rcases hdata k κk with ⟨s, u, hs0, hs1, hu, hu1s, ηnew, hU, hV, hinc⟩
      exact chain_step_open T k hopen hs0 hs1 hu hu1s κk ηnew hV hU hinc


/-- The interval-side growth atom (S161): if the new trace `T (k+1)` is
an interval chart whose overlap with the prefix
`⋃ j ∈ range (k+1), T j` is the LEFT terminal interval `(0,u)` of the
new chart with `u < 1`, then the new trace contains a point outside the
prefix — every facing-terminal chain step strictly grows the prefix
union.  This is the wrap/dichotomy marker: inside a compact ambient
(where some prefix already equals the whole space by open-cover
compactness) the facing-terminal chain data can never hold indefinitely,
so an infinite interval chain is the certificate of the NON-compact
(interval) side. -/
lemma prefix_proper_growth {Y : Type*} [TopologicalSpace Y] (T : ℕ → Set Y) (k : ℕ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ∃ x : Y, x ∈ T (k + 1) ∧ x ∉ ⋃ j ∈ Finset.range (k + 1), T j := by
  let tv : ℝ := (1 + u) / 2
  have htv0 : 0 < tv := by dsimp [tv]; linarith
  have htv1 : tv < 1 := by dsimp [tv]; linarith
  have htvu : u < tv := by dsimp [tv]; linarith
  let z : {y : Y // y ∈ T (k + 1)} := ηnew ⟨tv, ⟨htv0, htv1⟩⟩
  refine ⟨(z : Y), ?mem, ?notin⟩
  · exact z.2
  · intro hx
    have htu : (tv : ℝ) ∈ Set.Ioo (0 : ℝ) u := (hUend ⟨tv, ⟨htv0, htv1⟩⟩).mp hx
    exact (not_lt_of_ge (le_of_lt htu.2)) htvu

/-- The compact wrap contradiction (S161): the facing-terminal chain
data (`hUend` with `u < 1`) cannot be supplied at a level `k` whose
prefix already covers the whole space — the prefix being full makes the
growth atom impossible (`prefix_proper_growth` finds a point of
`T (k+1)` outside the prefix, yet `T (k+1) ⊆ univ = prefix`).  This is
the precise sense in which a compact (circle) component is NOT
chainable: at the level where the prefixes absorb the space, the
facing-terminal assumption must fail — the new trace must attach at
both ends (wrap) instead. -/
lemma chain_data_fails_at_full_prefix {Y : Type*} [TopologicalSpace Y]
    (T : ℕ → Set Y) (k : ℕ)
    (hfull : (⋃ j ∈ Finset.range (k + 1), T j) = Set.univ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u) : False := by
  rcases prefix_proper_growth T k hu0 hu1 ηnew hUend with ⟨x, _hxT, hxP⟩
  have hxP' : x ∈ ⋃ j ∈ Finset.range (k + 1), T j := by
    rw [hfull]
    trivial
  exact hxP hxP'

end Commons.Topology.OneManifold.ArcGlue


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
overlap points).  Everything in this module is verified (no primitives, no
`placeholder_`).
-/
open Set
open scoped Topology

noncomputable section
namespace Commons.Topology.OneManifold.ArcGlue

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

Everything here is verified (no primitives, no `placeholder_`).
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
end Commons.Topology.OneManifold.ArcGlue


open Set
open scoped Topology
open Commons.Topology.OneManifold.ArcGlue

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

noncomputable section
namespace Commons.Topology.OneManifold.ArcGlue

/-!
# S182 — the ambient two-arc theorem (module Submission/TwoArcUnion.lean)

The four-pairing end assembly of the facing-normalization program
(ROADMAP S182; AmbientTwoArc four-step outline step (3)+(4)): in a
HAUSDORFF space, TWO OPEN ARCS with CONNECTED OVERLAP GLUE TO AN OPEN
INTERVAL.  Content (namespace Commons.Topology.OneManifold.ArcGlue;
placeholder_-free, warning-free):

1. **Containment detection from the overlap shapes**:
   `subset_of_coordShape_all` — if the `V`-part of the `U`-chart is the
   whole interval `(0,1)` (shape `(a,b)` with `a = 0`, `b = 1`) then
   `U ⊆ V`; `subset_of_coordShape_all_symm` — the mirror `V ⊆ U`;
2. **`endIff_of_shape`** — the overlap-shape read off as the terminal
   membership iff `(ψ t : X) ∈ U ↔ (t : ℝ) ∈ Ioo lo hi` (the engine's
   `hVend`/`hUend` data, from `coord_mem_iff_mem_coordRealSet`);
3. **`Tfun_eq_transitionHomeo_coord`** — the engine's real transition
   `Tfun` agrees pointwise with the `transitionHomeo` coordinate value on
   the overlap domain (via `transitionHomeo_coord` S169);
4. **`two_arc_union_straight_facing`** (from shape data + `Tfun`-monotone
   `hinc`) and **`two_arc_union_straight_facing_of_strictMono`** (same,
   driven by `StrictMono` of the transition coordinate map through (3));
5. **`reversedChart_symm_apply_val` / `reversedChart_symm_coord_val`** —
   the symm of a reversed chart is the reflected `φ.symm` (coordinate
   `1 −` value); **`two_arc_union_mirror_facing_of_strictMono`** — the
   MIRROR configuration (overlap `(0,b)` LEFT-terminal in `U`, `(c,1)`
   RIGHT-terminal in `V`) glues too: reverse BOTH chart orientations
   (`(1−b,1)` / `(0,1−c)`), the doubly-reversed transition stays strictly
   increasing (`t ↦ 1 − g(1−t)`, direct coordinate computation through
   `transitionHomeo_coord` + the symm value lemma), then (4) applies;
6. **`two_open_arcs_union_of_shapes_inc`** — THE four-pairing theorem
   under the increasing orientation: shapes `(a,b)`, `(c,d)` with
   `[T2Space X]` and `StrictMono` transition.  `TransitionIncreasing`
   (S179) + `ends_of_at_least_one_chart_of_increasing` (S178) give
   `(a = 0 ∨ c = 0) ∧ (b = 1 ∨ d = 1)`; the four corners are containment
   (`a=0,b=1` ⟹ `U ⊆ V`; `c=0,d=1` ⟹ `V ⊆ U`), straight gluing
   (`c=0,b=1`) and mirror gluing (`a=0,d=1`); degenerate sub-corners
   collapse into the containments;
7. **`two_open_arcs_union_is_openInterval`** — THE ambient two-arc
   theorem: `[T2Space X]`, open `U V` with interval charts `φ ψ`, overlap
   `U ∩ V` connected ⟹ `Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ
   OpenRealInterval 0 1)`.  Orientation normalization: the transition
   monotone dichotomy (S165) — `StrictMono` applies (6) directly,
   `StrictAnti` reverses the `V`-chart (S181 `coordRealSet_reversedShape`
   + `transitionHomeo_reversedCoord`, the reversed transition
   `StrictMono` by the pointwise value identity) and applies (6) to the
   reversed pair.

This closes the gap recorded in ROADMAP S164/S177/S181: the consistent
orientation is always realisable (S181), the seam contradictions are
packaged (S178), and the end-covered lattice glues (this module) — the
union of two overlapping arcs of a Hausdorff space is an arc.  The
one-dimensional sweep (OneManifold / chain machinery) consumes this at
the two-trace base step.
-/
/-- If the `V`-part of the `U`-chart is the whole open interval `(0,1)`
then every point of `U` lies in `V` (`U ⊆ V`). -/
theorem subset_of_coordShape_all {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (ha0' : a = 0) (hb1' : b = 1) : U ⊆ V := by
  intro x hx
  let xu : {x : X // x ∈ U} := ⟨x, hx⟩
  let t : ORI 0 1 := φ.symm xu
  have htv : (φ t : X) = x := by
    dsimp [t, xu]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨x, hx⟩)
  have hiff := coord_mem_iff_mem_coordRealSet (φ := φ) (V := V) (r := (t : ℝ)) t.2
  have htV : (t : ℝ) ∈ coordRealSet φ V := by
    rw [hA, ha0', hb1']
    exact t.2
  have hφtV : (φ ⟨(t : ℝ), t.2⟩ : X) ∈ V := hiff.mpr htV
  have ht_eq : (⟨(t : ℝ), t.2⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
  have hφtV' : (φ t : X) ∈ V := by
    rwa [ht_eq] at hφtV
  rw [← htv]
  exact hφtV'

/-- The mirror: if the `U`-part of the `V`-chart is the whole interval then
`V ⊆ U`. -/
theorem subset_of_coordShape_all_symm {X : Type*} [TopologicalSpace X] {U V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) {c d : ℝ}
    (hB : coordRealSet ψ U = Set.Ioo c d) (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hc0' : c = 0) (hd1' : d = 1) : V ⊆ U := by
  -- instantiate the previous lemma with U↔V, φ↔ψ, and the tested set V↔U
  have h := subset_of_coordShape_all (U := V) (V := U) ψ hB hc0 hcd hd1 hc0' hd1'
  simpa [inter_comm, Set.subset_def] using h


/-- The terminal-overlap membership iff, read off the overlap shape: for a
chart `ψ` of `V` whose `U`-part has shape `(lo,hi)`, `(ψ t : X) ∈ U` iff
`(t : ℝ) ∈ Ioo lo hi` (exactly the `hUend`/`hVend` data of the glue
engine). -/
theorem endIff_of_shape {X : Type*} [TopologicalSpace X] {V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) (U : Set X)
    {lo hi : ℝ} (hB : coordRealSet ψ U = Set.Ioo lo hi) :
    ∀ t : ORI 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo lo hi := by
  intro t
  have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := t.2
  have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := (t : ℝ)) ht01
  constructor
  · intro hψtU
    have ht_eq : (⟨(t : ℝ), ht01⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
    have h' : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := by simpa [ht_eq] using hψtU
    have hin : (t : ℝ) ∈ coordRealSet ψ U := hiff.mp h'
    simpa [hB] using hin
  · intro ht
    have h' : (t : ℝ) ∈ coordRealSet ψ U := by simpa [hB] using ht
    have h'' : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := hiff.mpr h'
    have ht_eq : (⟨(t : ℝ), ht01⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
    simpa [ht_eq] using h''

/-- **S182 (straight-facing two-arc union)**: two open arcs `U V` whose
overlap is the right-terminal strip `(a,1)` of the `U`-chart and the
left-terminal strip `(0,d)` of the `V`-chart (monotone increasing
transition) glue to an open interval — the engine step
`prefix_two_charts_interval` (S159) driven by shape data. -/
theorem two_arc_union_straight_facing {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 d → v₂ ∈ Set.Ioo 0 d → v₁ < v₂ →
        Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v₁ <
        Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v₂) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  exact prefix_two_charts_interval (Y := X) (T₀ := U) (T₁ := V) hUopen hVopen ha0 ha1 hd0 hd1
    φ ψ (endIff_of_shape φ V hA) (endIff_of_shape ψ U hB) hinc



/-- The engine's transition function `Tfun` agrees pointwise with the
coordinate value of `transitionHomeo` on the overlap domain `(0,d)`. -/
lemma Tfun_eq_transitionHomeo_coord {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 d) :
    Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v =
      ((transitionHomeo φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
        le_rfl hd0 (le_of_lt hd1) ⟨v, hv⟩ : {x : ℝ // x ∈ Ioo a 1}) : ℝ) := by
  have hu1 : d ≤ 1 := le_of_lt hd1
  let hUend := endIff_of_shape ψ U hB
  rw [Tfun_eq hu1 φ ψ hUend hv]
  dsimp [T, hUend]
  -- v ∈ (0,1) needed
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_trans hv.2 hd1⟩
  have hψU : (ψ ⟨v, hv01⟩ : X) ∈ U := (endIff_of_shape ψ U hB ⟨v, hv01⟩).mpr (by
    have hvv : v ∈ Ioo 0 d := hv
    simpa using hvv)
  have hg := transitionHomeo_coord φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
    le_rfl hd0 (le_of_lt hd1) ⟨v, hv⟩ hv01 hψU
  -- hg : (transitionHomeo ... ⟨v,hv⟩ : ℝ) = (φ.symm ⟨(ψ ⟨v, hv01⟩ : X), hψU⟩ : ORI) : ℝ
  -- goal: ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (endIff hUend...).mpr hv⟩) : ORI) : ℝ = that RHS
  -- after dsimp [T], goal is: ((φ.symm (⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hmem⟩ : {x//x∈U})) : ORI) : ℝ = (hg RHS?)
  -- Actually goal after Tfun_eq + dsimp [T]: LHS = RHS from hg (orientation reversed).
  exact hg.symm



/-- **Straight-facing union from `StrictMono`**: with the overlap the
right-terminal strip `(a,1)` of the `U`-chart and the left-terminal strip
`(0,d)` of the `V`-chart and a strictly increasing transition coordinate
map, `U ∪ V` is an open interval.  (This is `two_arc_union_straight_facing`
driven by `StrictMono` through the pointwise identity
`Tfun_eq_transitionHomeo_coord`.) -/
lemma two_arc_union_straight_facing_of_strictMono {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo 0 d} =>
        ((transitionHomeo φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
          le_rfl hd0 (le_of_lt hd1) x : {x : ℝ // x ∈ Ioo a 1}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  refine two_arc_union_straight_facing hUopen hVopen ha0 ha1 hd0 hd1 φ ψ hA hB ?_
  intro v₁ v₂ hv₁ hv₂ hvlt
  rw [Tfun_eq_transitionHomeo_coord φ ψ ha0 ha1 hd0 hd1 hA hB hv₁,
      Tfun_eq_transitionHomeo_coord φ ψ ha0 ha1 hd0 hd1 hA hB hv₂]
  exact hmono (a := ⟨v₁, hv₁⟩) (b := ⟨v₂, hv₂⟩) hvlt



/-- **First-chart reversal value identity**: reversing the orientation of
the FIRST chart (`φ` ↦ `reversedChart φ`) reflects the transition values
about `1/2` — the new transition at `t` has coordinate `1 −` the old
coordinate, for `t` in the (unchanged) second-chart overlap `(c,d)`. -/
theorem transitionHomeo_firstReversedCoord {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (t : {x : ℝ // x ∈ Ioo c d}) :
    ((transitionHomeo (reversedChart φ) ψ
        (coordRealSet_reversedShape φ V ha0 hab hb1 hA) hB
        (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 - a by linarith)
        (show 1 - a ≤ 1 by linarith) hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo (1 - b) (1 - a)}) : ℝ)
      = 1 - ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo a b}) : ℝ) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  let hA' : coordRealSet φ' V = Set.Ioo (1 - b) (1 - a) :=
    coordRealSet_reversedShape φ V ha0 hab hb1 hA
  let hb'0 : 0 ≤ 1 - b := by linarith
  let hb'a : 1 - b < 1 - a := by linarith
  let ha'1 : 1 - a ≤ 1 := by linarith
  -- coordinates
  rcases t.2 with ⟨htc, htd⟩
  have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith
  have hψU : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := by
    have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := (t : ℝ)) ht01
    exact hiff.mpr (by simpa [hB] using t.2)
  have hL := transitionHomeo_coord φ' ψ hA' hB hb'0 hb'a ha'1 hc0 hcd hd1 t ht01 hψU
  have hR := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t ht01 hψU
  -- LHS = (φ'.symm ⟨(ψ⟨t⟩:X), hψU⟩ : ORI) : ℝ ; RHS-side: 1 - (φ.symm ⟨…⟩ : ORI) : ℝ
  -- φ' = φ ∘ refl, so φ'.symm z = refl (φ.symm z); value 1 - value
  have hφ' : ∀ z : {x : X // x ∈ U},
      ((φ'.symm z : ORI 0 1) : ℝ) = 1 - ((φ.symm z : ORI 0 1) : ℝ) := by
    intro z
    have hsymm : (φ'.symm z : ORI 0 1) = intervalReflection (0 : ℝ) 1 (φ.symm z) := by
      -- φ'.symm z is the unique point whose φ'-image is z; reflection∘φ.symm has image z
      apply (φ').injective
      have h1 : φ' (φ'.symm z) = z := φ'.apply_symm_apply z
      have h2 : φ' (intervalReflection (0 : ℝ) 1 (φ.symm z)) = z := by
        -- φ' = φ ∘ refl ; refl involutive
        have href : intervalReflection (0 : ℝ) 1 (intervalReflection (0 : ℝ) 1 (φ.symm z))
            = φ.symm z := intervalReflection_involutive (0 : ℝ) 1 (φ.symm z)
        dsimp [φ']
        dsimp [reversedChart]
        rw [href]
        -- (intervalReflection 0 1).trans φ applied to x is φ(refl x)?? compute:
        exact congrArg (fun w : {x : X // x ∈ U} => w) (φ.apply_symm_apply z)
      simpa [h1] using h2.symm ▸ h1
    rw [hsymm]
    rw [intervalReflection_apply]
    ring
  have hL' : ((transitionHomeo φ' ψ hA' hB hb'0 hb'a ha'1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo (1-b) (1-a)}) : ℝ)
      = 1 - ((φ.symm ⟨(ψ ⟨(t : ℝ), ht01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    rw [hL]
    dsimp [φ'] at hφ' ⊢
    rw [hφ']
  have hR' : ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo a b}) : ℝ)
      = ((φ.symm ⟨(ψ ⟨(t : ℝ), ht01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := hR
  -- goal: (T(φ',ψ) t : ℝ) = 1 - (T(φ,ψ) t : ℝ)
  rw [hL', hR']





/-- **Symm of the reversed chart**: `(reversedChart φ).symm` is the
reflection of `φ.symm` (the reflection homeo is its own inverse). -/
theorem reversedChart_symm_apply_val {X : Type*} [TopologicalSpace X] {U : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (z : {x : X // x ∈ U}) :
    ((reversedChart φ).symm z : ORI 0 1) = intervalReflection (0 : ℝ) 1 (φ.symm z) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  have h1 : φ' (φ'.symm z) = z := φ'.apply_symm_apply z
  have h2 : φ' (intervalReflection (0 : ℝ) 1 (φ.symm z)) = z := by
    have href : intervalReflection (0 : ℝ) 1 (intervalReflection (0 : ℝ) 1 (φ.symm z))
        = φ.symm z := intervalReflection_involutive (0 : ℝ) 1 (φ.symm z)
    dsimp [φ']
    dsimp [reversedChart]
    rw [href]
    exact congrArg (fun w : {x : X // x ∈ U} => w) (φ.apply_symm_apply z)
  have h3 : φ'.symm z = intervalReflection (0 : ℝ) 1 (φ.symm z) :=
    (φ'.injective (by simpa [h1] using h2.symm ▸ h1))
  exact congrArg (fun w : ORI 0 1 => (w : ORI 0 1)) h3

/-- Coordinate value of the symm: `((reversedChart φ).symm z : ℝ) = 1 −
`((φ.symm z) : ℝ)`. -/
theorem reversedChart_symm_coord_val {X : Type*} [TopologicalSpace X] {U : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (z : {x : X // x ∈ U}) :
    (((reversedChart φ).symm z : ORI 0 1) : ℝ) = 1 - ((φ.symm z : ORI 0 1) : ℝ) := by
  rw [reversedChart_symm_apply_val φ z]
  rw [intervalReflection_apply]
  ring

/-- **S182 (mirror-facing two-arc union)**: two open arcs whose overlap is
the LEFT-terminal strip `(0,b)` of the `U`-chart and the RIGHT-terminal
strip `(c,1)` of the `V`-chart (strictly increasing transition) glue to an
open interval.  Proof: reverse BOTH chart orientations — the overlap becomes
the straight-facing configuration (`(1−b,1)` right-terminal in the reversed
`U`-chart, `(0,1−c)` left-terminal in the reversed `V`-chart) of
`two_arc_union_straight_facing_of_strictMono`, and the doubly-reversed
transition is strictly increasing (`t ↦ 1 − g(1 − t)`). -/
lemma two_arc_union_mirror_facing_of_strictMono {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {b c : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo 0 b) (hB : coordRealSet ψ U = Set.Ioo c 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c 1} =>
        ((transitionHomeo φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
           x : {x : ℝ // x ∈ Ioo 0 b}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  let ψ' : ORI 0 1 ≃ₜ {x : X // x ∈ V} := reversedChart ψ
  let hA' : coordRealSet φ' V = Set.Ioo (1 - b) 1 := by
    dsimp [φ']
    simpa using coordRealSet_reversedShape φ V (c := 0) (d := b)
      (show 0 ≤ 0 from le_rfl) hb0 (le_of_lt hb1) hA
  let hB' : coordRealSet ψ' U = Set.Ioo 0 (1 - c) := by
    dsimp [ψ']
    simpa using coordRealSet_reversedShape ψ U (c := c) (d := 1)
      (le_of_lt hc0) hc1 (show 1 ≤ 1 from le_rfl) hB
  have hval2 : ∀ t : {x : ℝ // x ∈ Ioo 0 (1 - c)},
      ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)
        = 1 - ((transitionHomeo φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
            ⟨1 - (t : ℝ), (by rcases t.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
              : {x : ℝ // x ∈ Ioo 0 b}) : ℝ) := by
    intro t
    rcases t.2 with ⟨ht0, htc⟩
    have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hs01 : 1 - (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hsc1 : 1 - (t : ℝ) ∈ Ioo c 1 := by constructor <;> linarith
    have hψ'U : (ψ' ⟨(t : ℝ), ht01⟩ : X) ∈ U := by
      have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ') (r := (t : ℝ)) ht01
      exact hiff.mpr (by simpa [hB'] using t.2)
    have hψU : (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) ∈ U := by
      have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := 1 - (t : ℝ)) hs01
      exact hiff.mpr (by simpa [hB] using hsc1)
    have hXval : (ψ' ⟨(t : ℝ), ht01⟩ : X) = (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) := by
      dsimp [ψ']
      calc
        ((reversedChart ψ ⟨(t : ℝ), ht01⟩ : {x : X // x ∈ V}) : X)
            = (ψ (intervalReflection (0 : ℝ) 1 ⟨(t : ℝ), ht01⟩) : X) :=
              reversedChart_apply_val ψ ⟨(t : ℝ), ht01⟩
        _ = (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) := by
              exact congrArg (fun w : ORI 0 1 => (ψ w : X)) (by
                apply Subtype.ext
                rw [intervalReflection_apply]
                ring)
    have hArg : (⟨(ψ' ⟨(t : ℝ), ht01⟩ : X), hψ'U⟩ : {x : X // x ∈ U}) =
        ⟨(ψ ⟨(1 - (t : ℝ)), hs01⟩ : X), hψU⟩ := by
      apply Subtype.ext
      exact hXval
    have hL := transitionHomeo_coord φ' ψ' hA' hB'
      (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
      le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith) t ht01 hψ'U
    have hR := transitionHomeo_coord φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
      ⟨1 - (t : ℝ), hsc1⟩ hs01 hψU
    rw [hL, hR]
    dsimp [φ']
    rw [reversedChart_symm_coord_val φ ⟨(ψ' ⟨(t : ℝ), ht01⟩ : X), hψ'U⟩]
    exact congrArg (fun w : {x : X // x ∈ U} => (1 - ((φ.symm w : ORI 0 1) : ℝ))) hArg
  have hmono' : StrictMono (fun t : {x : ℝ // x ∈ Ioo 0 (1 - c)} =>
      ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)) := by
    intro t₁ t₂ hlt
    have hltv : (t₁ : ℝ) < (t₂ : ℝ) := hlt
    have h₁ := hval2 t₁
    have h₂ := hval2 t₂
    change ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t₁ : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ) <
        ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t₂ : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)
    rw [h₁, h₂]
    have hrc : ((⟨1 - (t₂ : ℝ), (by rcases t₂.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
        : {x : ℝ // x ∈ Ioo c 1}) : ℝ) <
        ((⟨1 - (t₁ : ℝ), (by rcases t₁.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
        : {x : ℝ // x ∈ Ioo c 1}) : ℝ) := by
      change 1 - (t₂ : ℝ) < 1 - (t₁ : ℝ)
      linarith
    have hg := hmono (a := ⟨1 - (t₂ : ℝ), (by rcases t₂.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩)
      (b := ⟨1 - (t₁ : ℝ), (by rcases t₁.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩) hrc
    linarith
  exact two_arc_union_straight_facing_of_strictMono (X := X) hUopen hVopen
    (a := 1 - b) (d := 1 - c)
    (show 0 < 1 - b by linarith) (show 1 - b < 1 by linarith)
    (show 0 < 1 - c by linarith) (show 1 - c < 1 by linarith)
    φ' ψ' hA' hB' (by simpa [φ', ψ', hA', hB'] using hmono')



/-- **S182 (the two-arc union theorem — increasing orientation)**: two open
arcs `U V` of a Hausdorff ambient, whose overlap `U ∩ V` has the interval
shapes `(a,b)` in the `U`-chart and `(c,d)` in the `V`-chart, with a
strictly increasing transition coordinate map, glue to an open interval.
Proof (the four-pairing end assembly): under `[T2Space X]` the increasing
orientation forbids a strict seam pair at either overlap end
(`ends_of_at_least_one_chart_of_increasing`, S178), so each overlap end is
an end of at least one chart: `(a = 0 ∨ c = 0) ∧ (b = 1 ∨ d = 1)`.  The
four corners give containment (`a = 0 ∧ b = 1` ⟹ `U ⊆ V`;
`c = 0 ∧ d = 1` ⟹ `V ⊆ U`), the straight facing gluing
(`c = 0 ∧ b = 1`; `two_arc_union_straight_facing_of_strictMono`), and the
mirror facing gluing (`a = 0 ∧ d = 1`;
`two_arc_union_mirror_facing_of_strictMono`, reversing both chart
orientations); degenerate sub-corners collapse into the containments. -/
theorem two_open_arcs_union_of_shapes_inc {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x : {x : ℝ // x ∈ Ioo a b}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  classical
  have hinc := increasing_of_strictMono φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
  have hends := ends_of_at_least_one_chart_of_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc
  have hlef : a = 0 ∨ c = 0 := by
    by_cases ha0s : a = 0
    · exact Or.inl ha0s
    · right
      have hapos : 0 < a := lt_of_le_of_ne ha0 (fun hz => ha0s hz.symm)
      have hnotc : ¬ 0 < c := fun hcpos => hends.1 ⟨hapos, hcpos⟩
      exact le_antisymm (le_of_not_gt hnotc) hc0
  have hrig : b = 1 ∨ d = 1 := by
    by_cases hb1s : b = 1
    · exact Or.inl hb1s
    · right
      have hblt : b < 1 := lt_of_le_of_ne hb1 hb1s
      have hnotd : ¬ d < 1 := fun hdlt => hends.2 ⟨hblt, hdlt⟩
      exact le_antisymm hd1 (le_of_not_gt hnotd)
  rcases hlef with ha0s | hc0s
  · rcases hrig with hb1s | hd1s
    · -- a = 0, b = 1 : U ⊆ V (containment)
      have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 ha0s hb1s
      rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
      exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
    · -- a = 0, d = 1 : mirror (degenerate corners collapse to containment)
      subst a
      subst d
      by_cases hb1eq : b = 1
      · have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 rfl hb1eq
        rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
        exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
      · have hblt : b < 1 := lt_of_le_of_ne hb1 hb1eq
        by_cases hc0eq : c = 0
        · have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 hc0eq rfl
          exact two_arc_contained hVU φ
        · have hcpos : 0 < c := lt_of_le_of_ne hc0 (fun hz => hc0eq hz.symm)
          exact two_arc_union_mirror_facing_of_strictMono (X := X) hUopen hVopen
            hab hblt hcpos hcd φ ψ hA hB hmono
  · rcases hrig with hb1s | hd1s
    · -- c = 0, b = 1 : straight (degenerate corners collapse to containment)
      subst b
      subst c
      by_cases ha0eq : a = 0
      · have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 ha0eq rfl
        rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
        exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
      · have hapos : 0 < a := lt_of_le_of_ne ha0 (fun hz => ha0eq hz.symm)
        by_cases hd1eq : d = 1
        · have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 rfl hd1eq
          exact two_arc_contained hVU φ
        · have hdlt : d < 1 := lt_of_le_of_ne hd1 hd1eq
          exact two_arc_union_straight_facing_of_strictMono (X := X) hUopen hVopen
            hapos hab hcd hdlt φ ψ hA hB hmono
    · -- c = 0, d = 1 : V ⊆ U (containment)
      have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 hc0s hd1s
      exact two_arc_contained hVU φ



/-- **S182 (the ambient two-arc theorem)**: in a Hausdorff space, two open
arcs `U V` (with interval charts `φ ψ`) whose overlap `U ∩ V` is connected
glue to a single open interval — `{x : X // x ∈ U ∪ V} ≃ₜ (0,1)`.  Proof:
classify the two overlap shapes `(a,b)`, `(c,d)`; take the transition
monotone dichotomy (S165): under `StrictMono` apply
`two_open_arcs_union_of_shapes_inc` directly, under `StrictAnti` reverse
the `V`-chart orientation (S181) — the reversed transition is `StrictMono`
(`transitionHomeo_reversedCoord` value identity) and the reversed pair has
shapes `(a,b)`, `(1−d,1−c)` (`coordRealSet_reversedShape`) — then apply
the same theorem to the reversed pair. -/
theorem two_open_arcs_union_is_openInterval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  -- V-side overlap connectedness
  have hconn' : ConnectedSpace {x : X // x ∈ V ∩ U} := by
    let e : {x : X // x ∈ V ∩ U} ≃ₜ {x : X // x ∈ U ∩ V} :=
      setEqSubtypeHomeoX (Set.inter_comm V U)
    exact (e.connectedSpace_iff).mpr hconn
  rcases overlap_coord_shape φ hVopen hconn with ⟨a, b, ha0, hab, hb1, hA⟩
  rcases overlap_coord_shape ψ hUopen hconn' with ⟨c, d, hc0, hcd, hd1, hB⟩
  let g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd g with hmono | hanti
  · exact two_open_arcs_union_of_shapes_inc hUopen hVopen φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
  · -- reverse the V-chart: the reversed transition is strictly increasing
    have hmono' : StrictMono (fun x : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)} =>
        ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x : {x : ℝ // x ∈ Ioo a b}) : ℝ)) := by
      intro x₁ x₂ hlt
      have hltv : (x₁ : ℝ) < (x₂ : ℝ) := hlt
      have h₁ := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x₁
      have h₂ := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x₂
      change ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x₁ : {x : ℝ // x ∈ Ioo a b}) : ℝ) <
        ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x₂ : {x : ℝ // x ∈ Ioo a b}) : ℝ)
      rw [h₁, h₂]
      have hrc : ((reflectCoord c d x₂ : {x : ℝ // x ∈ Ioo c d}) : ℝ) <
          ((reflectCoord c d x₁ : {x : ℝ // x ∈ Ioo c d}) : ℝ) := by
        rw [reflectCoord_val, reflectCoord_val]
        linarith
      have hg := hanti (a := reflectCoord c d x₂) (b := reflectCoord c d x₁) hrc
      linarith
    exact two_open_arcs_union_of_shapes_inc hUopen hVopen φ (reversedChart ψ) hA
      (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
      (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
      (show 1 - c ≤ 1 by linarith) hmono'


/-! ## S183 — the finite-chain union theorem (induction over the two-arc gluing)

The chain-level statement the S182 two-arc theorem feeds: a finite chain
of open arcs of a Hausdorff space whose every PREFIX meets the next trace
in a connected overlap glues to one open interval.  The induction carries
the explicit prefix homeomorphism (each step consumes the previous
prefix's interval chart).  (Successive-overlap-only hypotheses are NOT
sufficient — a wrapping trace can touch the prefix in two components;
prefix-overlap connectivity must come from the walk/O-chart geometry.)
-/

/-- **S183 (finite-chain union, induction statement)**: in a Hausdorff
space, a finite chain of open arcs — each trace `T k` (`k ≤ n`) open with
an interval chart, every prefix `P k := ⋃ j ∈ range (k+1), T j` meeting
the next trace `T (k+1)` in a CONNECTED (hence nonempty) overlap — glues
to a single open interval: the full prefix `P n` carries an interval
chart.  The induction carries the explicit homeomorphism (not merely
interval-ness), because the two-arc theorem's next step consumes the
prefix's interval chart as an input.

HYPOTHESES ARE PREFIX-OVERLAP (not merely successive-overlap): the
`(k ↦ k+1)` gluing applies the ambient two-arc theorem
(`two_open_arcs_union_is_openInterval`, S182) to the pair
`(P k, T (k+1))`, which requires `P k ∩ T (k+1)` connected.  NOTE
(honest): connectedness of the *successive* overlaps `T k ∩ T (k+1)`
alone does NOT suffice — a later trace may touch the interior of the
prefix in a second component (e.g. arcs of a circle wrapping past a
meridian), which disconnects `P k ∩ T (k+1)`; the walk/O-chart geometry
must supply prefix-overlap connectivity. -/
theorem finite_chain_union_interval {X : Type*} [TopologicalSpace X] [T2Space X]
    (T : ℕ → Set X) (n : ℕ)
    (hopen : ∀ k, k ≤ n → IsOpen (T k))
    (hchart : ∀ k, k ≤ n → Nonempty (ORI 0 1 ≃ₜ {x : X // x ∈ T k}))
    (hconn : ∀ k, k < n →
      ConnectedSpace {x : X // x ∈ (⋃ j ∈ Finset.range (k+1), T j) ∩ T (k+1)}) :
    Nonempty ({x : X // x ∈ ⋃ j ∈ Finset.range (n+1), T j} ≃ₜ OpenRealInterval 0 1) := by
  classical
  induction n with
  | zero =>
      have hset : (⋃ j ∈ Finset.range (1), T j) = T 0 := by
        ext x
        simp [Finset.range_one]
      rcases hchart 0 (by omega) with ⟨e⟩
      exact ⟨(setEqSubtypeHomeoX hset).trans e.symm⟩
  | succ n ih =>
      -- prefix-openness at level n (finite union of open traces, j ≤ n)
      have hpref_open : IsOpen (⋃ j ∈ Finset.range (n + 1), T j) := by
        -- induction on the trace count m, showing prefix m open for m ≤ n+1
        have hgo : ∀ m : ℕ, m ≤ n + 1 → IsOpen (⋃ j ∈ Finset.range (m + 1), T j) := by
          intro m
          induction m with
          | zero =>
              intro hm
              have hset0 : (⋃ j ∈ Finset.range (1), T j) = T 0 := by
                ext x
                simp [Finset.range_one]
              rw [hset0]
              exact hopen 0 (by omega)
          | succ m ih' =>
              intro hm
              rw [union_range_succ T m]
              exact (ih' (by omega)).union (hopen (m + 1) (by omega))
        exact hgo n (by omega)
      -- induction hypothesis: the prefix of the first n+1 traces is an arc
      have hP := ih (fun k hk => hopen k (by omega)) (fun k hk => hchart k (by omega))
        (fun k hk => hconn k (by omega))
      rcases hP with ⟨eP⟩
      rcases hchart (n + 1) (by omega) with ⟨eT⟩
      have hov : ConnectedSpace
          {x : X // x ∈ (⋃ j ∈ Finset.range (n+1), T j) ∩ T (n+1)} := hconn n (by omega)
      have htwo := two_open_arcs_union_is_openInterval
        (U := ⋃ j ∈ Finset.range (n+1), T j) (V := T (n+1))
        hpref_open (hopen (n + 1) (by omega)) eP.symm eT hov
      rcases htwo with ⟨eU⟩
      have hset : (⋃ j ∈ Finset.range (n + 2), T j) =
          (⋃ j ∈ Finset.range (n + 1), T j) ∪ T (n + 1) := union_range_succ T n
      have hfin : ({x : X // x ∈ ⋃ j ∈ Finset.range (n + 2), T j}) ≃ₜ
          ({x : X // x ∈ (⋃ j ∈ Finset.range (n+1), T j) ∪ T (n+1)}) :=
        setEqSubtypeHomeoX hset
      exact ⟨hfin.trans eU⟩
end Commons.Topology.OneManifold.ArcGlue


namespace Commons.Topology.OneManifold

open Commons.Topology.OneManifold.ArcGlue

/-- **Two open arcs with connected overlap glue to an open interval.**  In a
Hausdorff space `X`, let `U V : Set X` be OPEN sets each homeomorphic to the
open unit interval `(0,1)`, whose overlap `U ∩ V` is CONNECTED (as a
subspace).  Then `U ∪ V` is homeomorphic to the open unit interval.

This is the interval half of the two-open-arc classification (S182): the
orientation-normalization machinery (`exists_increasing_orientation`) and the
shape/end analysis of `ArcGlue` reduce every configuration to a containment
(`U ⊆ V` or `V ⊆ U`) or an increasing facing/gluing of the two charts, each
of which glues to an interval. -/
theorem union_two_open_arcs_connected_overlap_interval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (eU : Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ U))
    (eV : Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ V))
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ (U ∪ V : Set X)) := by
  rcases eU with ⟨φ⟩
  rcases eV with ⟨ψ⟩
  rcases ArcGlue.two_open_arcs_union_is_openInterval (X := X) (U := U) (V := V)
    hUopen hVopen φ ψ hconn with ⟨e⟩
  exact ⟨e.symm⟩

end Commons.Topology.OneManifold