import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.RealIntervals.open_preconnected_untrapped_unit_end_strip

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Analysis.RealIntervals

/-- If the connected component of `x` in an open set `S` is the open interval
`(a,b)`, then its left endpoint `a` does not belong to `S`.  Otherwise the
component could be enlarged with an open ball around `a`, contradicting
maximality of the connected component. -/
lemma left_endpoint_of_component_Ioo_not_mem {S : Set ℝ} (hSopen : IsOpen S) {x a b : ℝ}
    (hxS : x ∈ S) (hK : connectedComponentIn S x = Set.Ioo a b)
    (hxI : x ∈ Set.Ioo a b) : a ∉ S := by
  intro haS
  rcases Metric.isOpen_iff.mp hSopen a haS with ⟨δ, hδ0, hball⟩
  let K : Set ℝ := connectedComponentIn S x
  let T : Set ℝ := K ∪ Metric.ball a δ
  have hKsubS : K ⊆ S := connectedComponentIn_subset S x
  have hTsubS : T ⊆ S := by
    intro z hz
    rcases hz with hzK | hzB
    · exact hKsubS hzK
    · exact hball hzB
  have hxK : x ∈ K := by
    exact mem_connectedComponentIn hxS
  have hxT : x ∈ T := by
    left
    exact hxK
  have hKpc : IsPreconnected K := by
    simpa [K] using (isPreconnected_connectedComponentIn (x := x) (F := S))
  have hBpc : IsPreconnected (Metric.ball a δ) := Metric.isPreconnected_ball
  have hab : a < b := lt_trans (Set.mem_Ioo.mp hxI).1 (Set.mem_Ioo.mp hxI).2
  have hov : (K ∩ Metric.ball a δ).Nonempty := by
    let m : ℝ := min b (a + δ)
    let z : ℝ := (a + m) / 2
    have hma : a < m := by
      dsimp [m]
      exact lt_min hab (by linarith)
    have hz_a : a < z := by
      dsimp [z]
      linarith
    have hz_m : z < m := by
      dsimp [z]
      linarith
    have hz_b : z < b := lt_of_lt_of_le hz_m (min_le_left b (a + δ))
    have hz_lt : z < a + δ := lt_of_lt_of_le hz_m (min_le_right b (a + δ))
    have hzK : z ∈ K := by
      simpa [K, hK] using (show z ∈ Set.Ioo a b from ⟨hz_a, hz_b⟩)
    have hzB : z ∈ Metric.ball a δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hpos : 0 < z - a := by linarith
      rw [abs_of_pos hpos]
      linarith
    exact ⟨z, hzK, hzB⟩
  have hTpc : IsPreconnected T := by
    rcases hov with ⟨z, hzK, hzB⟩
    simpa [T] using (IsPreconnected.union z hzK hzB hKpc hBpc)
  have hTsubK : T ⊆ connectedComponentIn S x :=
    IsPreconnected.subset_connectedComponentIn hTpc hxT hTsubS
  have hmemT : a - δ / 2 ∈ T := by
    right
    rw [Metric.mem_ball, Real.dist_eq]
    have hneg : a - δ / 2 - a < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have hmemK : a - δ / 2 ∈ K := by
    exact hTsubK hmemT
  have hmemI : a - δ / 2 ∈ Set.Ioo a b := by
    simpa [K, hK] using hmemK
  have hgt : a < a - δ / 2 := (Set.mem_Ioo.mp hmemI).1
  linarith

/-- Symmetric statement for the right endpoint of a component which is an
open interval `(a,b)`. -/
lemma right_endpoint_of_component_Ioo_not_mem {S : Set ℝ} (hSopen : IsOpen S) {x a b : ℝ}
    (hxS : x ∈ S) (hK : connectedComponentIn S x = Set.Ioo a b)
    (hxI : x ∈ Set.Ioo a b) : b ∉ S := by
  intro hbS
  rcases Metric.isOpen_iff.mp hSopen b hbS with ⟨δ, hδ0, hball⟩
  let K : Set ℝ := connectedComponentIn S x
  let T : Set ℝ := K ∪ Metric.ball b δ
  have hKsubS : K ⊆ S := connectedComponentIn_subset S x
  have hTsubS : T ⊆ S := by
    intro z hz
    rcases hz with hzK | hzB
    · exact hKsubS hzK
    · exact hball hzB
  have hxK : x ∈ K := by
    exact mem_connectedComponentIn hxS
  have hxT : x ∈ T := by
    left
    exact hxK
  have hKpc : IsPreconnected K := by
    simpa [K] using (isPreconnected_connectedComponentIn (x := x) (F := S))
  have hBpc : IsPreconnected (Metric.ball b δ) := Metric.isPreconnected_ball
  have hab : a < b := lt_trans (Set.mem_Ioo.mp hxI).1 (Set.mem_Ioo.mp hxI).2
  have hov : (K ∩ Metric.ball b δ).Nonempty := by
    let m : ℝ := max a (b - δ)
    let z : ℝ := (m + b) / 2
    have hmb : m < b := by
      dsimp [m]
      exact max_lt hab (by linarith)
    have hz_m : m < z := by
      dsimp [z]
      linarith
    have hz_b : z < b := by
      dsimp [z]
      linarith
    have ha_z : a < z := by
      have ham : a ≤ m := by
        dsimp [m]
        exact le_max_left a (b - δ)
      exact lt_of_le_of_lt ham hz_m
    have hbg : b - δ < z := by
      have hmg : b - δ ≤ m := by
        dsimp [m]
        exact le_max_right a (b - δ)
      exact lt_of_le_of_lt hmg hz_m
    have hzK : z ∈ K := by
      simpa [K, hK] using (show z ∈ Set.Ioo a b from ⟨ha_z, hz_b⟩)
    have hzB : z ∈ Metric.ball b δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hneg : z - b < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    exact ⟨z, hzK, hzB⟩
  have hTpc : IsPreconnected T := by
    rcases hov with ⟨z, hzK, hzB⟩
    simpa [T] using (IsPreconnected.union z hzK hzB hKpc hBpc)
  have hTsubK : T ⊆ connectedComponentIn S x :=
    IsPreconnected.subset_connectedComponentIn hTpc hxT hTsubS
  have hmemT : b + δ / 2 ∈ T := by
    right
    rw [Metric.mem_ball, Real.dist_eq]
    have hpos : 0 < b + δ / 2 - b := by linarith
    rw [abs_of_pos hpos]
    linarith
  have hmemK : b + δ / 2 ∈ K := by
    exact hTsubK hmemT
  have hmemI : b + δ / 2 ∈ Set.Ioo a b := by
    simpa [K, hK] using hmemK
  have hlt : b + δ / 2 < b := (Set.mem_Ioo.mp hmemI).2
  linarith

/-- **Structural dichotomy for a connected component of an open subset of
`ℝ` that meets `(−∞, c)`**.  Under the hypothesis that no interval of the
form `(b, c)` (`0 ≤ b < c`) is entirely contained in `S`, the connected
component of a point `x ∈ S`, `x < c`, cannot be a closed interval, a ray
`(a, ∞)` or all of `ℝ`; it must be either a left ray `(−∞, b)` or an open
interval `(a, b)` with `b < c`.  (Components are open preconnected subsets
of ℝ; `IsPreconnected.mem_intervals` lists their ten possible shapes.) -/
lemma component_dichotomy {S : Set ℝ} (hSopen : IsOpen S) {c : ℝ} (hc0 : 0 < c)
    (hnoFull : ¬ ∃ b : ℝ, b < c ∧ 0 ≤ b ∧ Set.Ioo b c ⊆ S) {x : ℝ}
    (hxS : x ∈ S) (hxc : x < c) :
    (connectedComponentIn S x = Set.Iio (sSup (connectedComponentIn S x)) ∧
        sSup (connectedComponentIn S x) < c) ∨
      (connectedComponentIn S x =
          Set.Ioo (sInf (connectedComponentIn S x)) (sSup (connectedComponentIn S x)) ∧
        sSup (connectedComponentIn S x) < c) := by
  let C : Set ℝ := connectedComponentIn S x
  have hCsub : C ⊆ S := by
    simpa [C] using (connectedComponentIn_subset S x)
  have hxC : x ∈ C := by
    simpa [C] using (mem_connectedComponentIn hxS)
  have hCpc : IsPreconnected C := by
    simpa [C] using (isPreconnected_connectedComponentIn (x := x) (F := S))
  have hCopen : IsOpen C := by
    simpa [C] using (IsOpen.connectedComponentIn (F := S) (x := x) hSopen)
  have hCne : C.Nonempty := ⟨x, hxC⟩
  rcases hCpc.mem_intervals with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact False.elim (isOpen_nonempty_not_Icc hCopen hCne h1)
  · exact False.elim (isOpen_nonempty_not_Ico hCopen hCne h2)
  · exact False.elim (isOpen_nonempty_not_Ioc hCopen hCne h3)
  · -- `C = Ioo (sInf C) (sSup C)`: keep it, show the right end is below `c`.
    right
    refine ⟨h4, ?_⟩
    by_contra hnot
    have hle : c ≤ sSup C := le_of_not_gt hnot
    have hxI : x ∈ Set.Ioo (sInf C) (sSup C) := h4 ▸ hxC
    have hinfx : sInf C < x := (Set.mem_Ioo.mp hxI).1
    have hb0c : max (sInf C) 0 < c := max_lt (lt_trans hinfx hxc) hc0
    have hb0n : 0 ≤ max (sInf C) 0 := le_max_right (sInf C) 0
    have hsub : Set.Ioo (max (sInf C) 0) c ⊆ S := by
      intro z hz
      rcases Set.mem_Ioo.mp hz with ⟨hbz, hzc⟩
      have hzmem : z ∈ Set.Ioo (sInf C) (sSup C) :=
        ⟨lt_of_le_of_lt (le_max_left (sInf C) 0) hbz, lt_of_lt_of_le hzc hle⟩
      have hzC : z ∈ C := h4.symm ▸ hzmem
      exact hCsub hzC
    exact hnoFull ⟨max (sInf C) 0, hb0c, hb0n, hsub⟩
  · exact False.elim (isOpen_nonempty_not_Ici hCopen hCne h5)
  · -- `C = Ioi (sInf C)`: a right ray reaching down to `x < c` would
    -- contain `(b, c)` for some `b ≥ 0`.
    exfalso
    have hxI : x ∈ Set.Ioi (sInf C) := h6 ▸ hxC
    have hinfx : sInf C < x := Set.mem_Ioi.mp hxI
    have hb0c : max (sInf C) 0 < c := max_lt (lt_trans hinfx hxc) hc0
    have hb0n : 0 ≤ max (sInf C) 0 := le_max_right (sInf C) 0
    have hsub : Set.Ioo (max (sInf C) 0) c ⊆ S := by
      intro z hz
      rcases Set.mem_Ioo.mp hz with ⟨hbz, _⟩
      have hzC : z ∈ C := h6.symm ▸ (Set.mem_Ioi.mpr (lt_of_le_of_lt (le_max_left (sInf C) 0) hbz))
      exact hCsub hzC
    exact hnoFull ⟨max (sInf C) 0, hb0c, hb0n, hsub⟩
  · exact False.elim (isOpen_nonempty_not_Iic hCopen hCne h7)
  · -- `C = Iio (sSup C)`: keep it, show the right end is below `c`.
    left
    refine ⟨h8, ?_⟩
    by_contra hnot
    have hle : c ≤ sSup C := le_of_not_gt hnot
    have hsub : Set.Ioo 0 c ⊆ S := by
      intro z hz
      rcases Set.mem_Ioo.mp hz with ⟨_, hzc⟩
      have hzC : z ∈ C := h8.symm ▸ (Set.mem_Iio.mpr (lt_of_lt_of_le hzc hle))
      exact hCsub hzC
    exact hnoFull ⟨0, hc0, le_rfl, hsub⟩
  · -- `C = univ` would put the whole interval `(0,c)` inside `S`.
    exfalso
    have hsub : Set.Ioo 0 c ⊆ S := by
      intro z hz
      have hzC : z ∈ C := h9.symm ▸ trivial
      exact hCsub hzC
    exact hnoFull ⟨0, hc0, le_rfl, hsub⟩
  · -- `C = ∅` contradicts the nonemptiness of the component.
    exfalso
    rw [h10] at hCne
    exact (Set.not_nonempty_empty (α := ℝ) hCne)

/-- **Main statement**: an open subset `S` of `ℝ` whose points are dense in
every left neighbourhood of a positive point `c`, but which contains NO full
strip `(b, c)` (`0 ≤ b < c`), must contain an open interval `(a,b)` strictly
inside `(0,c)` whose endpoints are outside `S`.

Proof structure: connected components of `S` containing points below `c`
are, by `component_dichotomy`, left rays `(−∞, t)` or open intervals
`(a, t)` with `t < c`; a component is *good* when it is an interval
`(a, t)` with `0 < a`.  Only one component meeting `(c/2, c)` can fail to
be good, since every non-good such component contains the whole interval
`(0, c/2)` and distinct components are disjoint.  If there were no good
component, all points of `S ∩ (c/2, c)` would lie in that single non-good
component, whose right end lies strictly below `c`, contradicting density of
`S` below `c`.  A good component `(a,b)` (with `0 < a < b < c`) is then
entirely contained in `S`; its endpoints lie outside `S` by maximality of
the component (`left_endpoint_of_component_Ioo_not_mem`,
`right_endpoint_of_component_Ioo_not_mem`). -/
theorem exists_interior_interval_of_dense_no_full {S : Set ℝ} (hSopen : IsOpen S) {c : ℝ}
    (hc0 : 0 < c)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c - ε < x ∧ x < c)
    (hnoFull : ¬ ∃ b : ℝ, b < c ∧ 0 ≤ b ∧ Set.Ioo b c ⊆ S) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < c ∧ Set.Ioo a b ⊆ S ∧ a ∉ S ∧ b ∉ S := by
  let K : ℝ → Set ℝ := fun x => connectedComponentIn S x
  -- A point of `S` arbitrarily close to `c` from below, inside `(c/2, c)`.
  rcases hdense (c / 2) (by positivity) with ⟨x0, hx0S, hx0l, hx0c⟩
  have hx0mid : c / 2 < x0 := by linarith
  have hx00 : 0 < x0 := lt_trans (half_pos hc0) hx0mid
  -- There is a point of `S ∩ (c/2, c)` whose component is an interval
  -- `(a, b)` with positive left end.
  have hgood : ∃ x : ℝ, x ∈ S ∧ c / 2 < x ∧ x < c ∧
      0 < sInf (connectedComponentIn S x) ∧
      connectedComponentIn S x =
        Set.Ioo (sInf (connectedComponentIn S x)) (sSup (connectedComponentIn S x)) := by
    by_contra hno
    -- Every component that meets `S ∩ (c/2, c)` is a left ray `(−∞, t)`
    -- or an interval whose left end is `≤ 0`; in both cases it contains
    -- all of `(0, c/2)`.
    have hcontains : ∀ x : ℝ, x ∈ S → c / 2 < x → x < c →
        Set.Ioo 0 (c / 2) ⊆ connectedComponentIn S x := by
      intro x hxS hxmid hxc z hz
      rcases Set.mem_Ioo.mp hz with ⟨hz0, hzc2⟩
      have hxK : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
      rcases component_dichotomy hSopen hc0 hnoFull hxS hxc with hcase1 | hcase2
      · -- component is `Iio (sSup ...)`
        have hxsup : x < sSup (connectedComponentIn S x) := by
          have : x ∈ Set.Iio (sSup (connectedComponentIn S x)) := hcase1.1 ▸ hxK
          exact Set.mem_Iio.mp this
        rw [hcase1.1]
        exact Set.mem_Iio.mpr (lt_trans hzc2 (lt_trans hxmid hxsup))
      · -- component is `Ioo (sInf ...) (sSup ...)`; no-good gives `sInf ≤ 0`
        have hle0 : sInf (connectedComponentIn S x) ≤ 0 := by
          by_contra hgt
          have hgt0 : 0 < sInf (connectedComponentIn S x) := lt_of_not_ge hgt
          exact hno ⟨x, hxS, hxmid, hxc, hgt0, hcase2.1⟩
        have hxsup : x < sSup (connectedComponentIn S x) := by
          have : x ∈ Set.Ioo (sInf (connectedComponentIn S x)) (sSup (connectedComponentIn S x)) :=
            hcase2.1 ▸ hxK
          exact (Set.mem_Ioo.mp this).2
        rw [hcase2.1]
        exact ⟨lt_of_le_of_lt hle0 hz0, lt_trans hzc2 (lt_trans hxmid hxsup)⟩
    -- All components meeting `S ∩ (c/2, c)` coincide with that of `x0`
    -- (they all contain the shared point `c/4`).
    have hall : ∀ x : ℝ, x ∈ S → c / 2 < x → x < c →
        x ∈ connectedComponentIn S x0 := by
      intro x hxS hxmid hxc
      have hq4 : 0 < c / 4 ∧ c / 4 < c / 2 := by
        constructor <;> linarith
      have hzx : c / 4 ∈ connectedComponentIn S x :=
        hcontains x hxS hxmid hxc ⟨hq4.1, hq4.2⟩
      have hzx0 : c / 4 ∈ connectedComponentIn S x0 :=
        hcontains x0 hx0S hx0mid hx0c ⟨hq4.1, hq4.2⟩
      have heq1 : connectedComponentIn S x = connectedComponentIn S (c / 4) :=
        connectedComponentIn_eq (x := x) (y := c / 4) hzx
      have heq2 : connectedComponentIn S x0 = connectedComponentIn S (c / 4) :=
        connectedComponentIn_eq (x := x0) (y := c / 4) hzx0
      have hxK : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
      have hmid : x ∈ connectedComponentIn S (c / 4) := by
        simpa [heq1] using hxK
      simpa [heq2] using hmid
    -- The right end of the component of `x0` is strictly below `c`.
    have hsup0 : sSup (connectedComponentIn S x0) < c := by
      rcases component_dichotomy hSopen hc0 hnoFull hx0S hx0c with hcase1 | hcase2
      · exact hcase1.2
      · exact hcase2.2
    -- Density then forces a point of `S ∩ (c/2, c)` beyond that right end:
    -- take `ε := c − s` (where `s := sSup (component of x0)`, so `0 < ε`),
    -- the witness `y` lies above `s` and inside `(c/2, c)`.
    have hxK0 : x0 ∈ connectedComponentIn S x0 := mem_connectedComponentIn hx0S
    have hsup_gt : c / 2 < sSup (connectedComponentIn S x0) := by
      rcases component_dichotomy hSopen hc0 hnoFull hx0S hx0c with hcase1 | hcase2
      · have : x0 ∈ Set.Iio (sSup (connectedComponentIn S x0)) := hcase1.1 ▸ hxK0
        exact lt_trans hx0mid (Set.mem_Iio.mp this)
      · have : x0 ∈
            Set.Ioo (sInf (connectedComponentIn S x0)) (sSup (connectedComponentIn S x0)) :=
          hcase2.1 ▸ hxK0
        exact lt_trans hx0mid (Set.mem_Ioo.mp this).2
    rcases hdense (c - sSup (connectedComponentIn S x0)) (by linarith) with ⟨y, hyS, hyl, hyc⟩
    have hymid : c / 2 < y := by
      have hsy : sSup (connectedComponentIn S x0) < y := by linarith
      exact lt_trans hsup_gt hsy
    have hyK : y ∈ connectedComponentIn S x0 := hall y hyS hymid hyc
    have hysup : sSup (connectedComponentIn S x0) < y := by linarith
    have hylt : y < sSup (connectedComponentIn S x0) := by
      rcases component_dichotomy hSopen hc0 hnoFull hx0S hx0c with hcase1 | hcase2
      · have : y ∈ Set.Iio (sSup (connectedComponentIn S x0)) := hcase1.1 ▸ hyK
        exact Set.mem_Iio.mp this
      · have : y ∈
            Set.Ioo (sInf (connectedComponentIn S x0)) (sSup (connectedComponentIn S x0)) :=
          hcase2.1 ▸ hyK
        exact (Set.mem_Ioo.mp this).2
    linarith
  rcases hgood with ⟨x, hxS, hxmid, hxc, hxinf, hxIoo⟩
  let a : ℝ := sInf (connectedComponentIn S x)
  let b : ℝ := sSup (connectedComponentIn S x)
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [a] using hxinf
  · have hxK : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
    have hxI : x ∈ Set.Ioo a b := hxIoo ▸ hxK
    exact lt_trans (Set.mem_Ioo.mp hxI).1 (Set.mem_Ioo.mp hxI).2
  · rcases component_dichotomy hSopen hc0 hnoFull hxS hxc with hcase1 | hcase2
    · simpa [b] using hcase1.2
    · simpa [b] using hcase2.2
  · have hsub : Set.Ioo a b ⊆ connectedComponentIn S x := by
      intro z hz
      exact hxIoo.symm ▸ hz
    exact Set.Subset.trans hsub (connectedComponentIn_subset S x)
  · have hxK : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
    have hxI : x ∈ Set.Ioo a b := hxIoo ▸ hxK
    simpa [a] using left_endpoint_of_component_Ioo_not_mem hSopen hxS hxIoo hxI
  · have hxK : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
    have hxI : x ∈ Set.Ioo a b := hxIoo ▸ hxK
    simpa [b] using right_endpoint_of_component_Ioo_not_mem hSopen hxS hxIoo hxI

end Commons.Analysis.RealIntervals