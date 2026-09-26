import Mathlib

open Set
open scoped Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

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
Everything here is elementary and verified (no axioms, no `sorry`).
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

end LeanEval.KnotTheory.Quadrisecant
