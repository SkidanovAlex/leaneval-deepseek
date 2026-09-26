import Mathlib
import Submission.OneManifold
import Submission.Commons.Topology.Homeomorph.open_interval_affine

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

Everything here is verified (no axioms, no `sorry`); the module is pure
Mathlib plus the commons affine fact, so it is promotable to the commons
as-is.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

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

end LeanEval.KnotTheory.Quadrisecant
