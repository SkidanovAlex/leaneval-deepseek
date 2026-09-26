import Mathlib
import Submission.Commons.Topology.OneManifold.arc_extension_or_compact
import Submission.Commons.Topology.OneManifold.nested_open_arcs_union_is_open_arc
import Submission.Commons.Topology.OneManifold.oneManifold_dichotomy

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# Generic classification of connected non-compact topological 1-manifolds

A connected, Hausdorff, second-countable topological space in which every
point has an open neighbourhood homeomorphic to an open interval of `ℝ`
(a connected topological 1-manifold without boundary) is homeomorphic
either to the open unit interval `(0,1)` or is compact.  In particular a
connected *non-compact* one is homeomorphic to `(0,1)`.

This file develops the proof bottom-up as a sequence of generic lemmas.
-/

/-- The open real interval `(lo,hi)` as a type. -/
abbrev OpenRealInterval (lo hi : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo lo hi}

/-- Affine homeomorphism between two open real intervals. -/
theorem affine_Ioo_homeo (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    Nonempty (OpenRealInterval a b ≃ₜ OpenRealInterval c d) := by
  let S := OpenRealInterval a b
  let T := OpenRealInterval c d
  let F : S → T := fun x => ⟨c + (d - c) * (x.1 - a) / (b - a), by
    have hx : a < x.1 := x.2.1
    have hx2 : x.1 < b := x.2.2
    have hbma : 0 < b - a := by linarith
    have hdc : 0 < d - c := by linarith
    have hleft : c < c + (d - c) * (x.1 - a) / (b - a) := by
      have h1 : 0 < (d - c) * (x.1 - a) / (b - a) := by positivity
      linarith
    have hright : c + (d - c) * (x.1 - a) / (b - a) < d := by
      have hmain : (d - c) * (x.1 - a) / (b - a) < d - c := by
        rw [div_lt_iff₀ hbma]
        nlinarith
      linarith
    exact ⟨hleft, hright⟩⟩
  let G : T → S := fun y => ⟨a + (b - a) * (y.1 - c) / (d - c), by
    have hy : c < y.1 := y.2.1
    have hy2 : y.1 < d := y.2.2
    have hdcm : 0 < d - c := by linarith
    have hba : 0 < b - a := by linarith
    have hleft : a < a + (b - a) * (y.1 - c) / (d - c) := by
      have h1 : 0 < (b - a) * (y.1 - c) / (d - c) := by positivity
      linarith
    have hright : a + (b - a) * (y.1 - c) / (d - c) < b := by
      have hmain : (b - a) * (y.1 - c) / (d - c) < b - a := by
        rw [div_lt_iff₀ hdcm]
        nlinarith
      linarith
    exact ⟨hleft, hright⟩⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    have hbma : b - a ≠ 0 := by linarith
    have hdcm : d - c ≠ 0 := by linarith
    field_simp [hbma, hdcm]
    ring
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    dsimp [F, G]
    have hbma : b - a ≠ 0 := by linarith
    have hdcm : d - c ≠ 0 := by linarith
    field_simp [hbma, hdcm]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    fun_prop
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    fun_prop
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact ⟨Homeomorph.mk e hFc hGc⟩

/-- Any bounded open interval is homeomorphic to `(0,1)`. -/
theorem homeo_Ioo_openUnit (a b : ℝ) (hab : a < b) :
    Nonempty ({x : ℝ // x ∈ Set.Ioo a b} ≃ₜ OpenRealInterval 0 1) := by
  exact affine_Ioo_homeo a b 0 1 hab (by norm_num)

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




/-! ## Locally interval-charted spaces and countable open-arc covers -/

/-- **Locally interval-charted**: every point has an open neighbourhood
homeomorphic to an open real interval (the local model of a 1-manifold). -/
def LocallyIntervalChart (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U)

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
  · ext x
    constructor
    · intro hx
      exact trivial
    · intro _
      have hxcover : x ∈ ⋃ x : X, U x := Set.mem_iUnion.mpr ⟨x, hxU x⟩
      have hxsub : x ∈ ⋃ n, U (k n) := by
        rw [hk]
        exact hxcover
      simpa [A] using hxsub

/-- Every point of a locally interval-charted space lies in some open arc
homeomorphic to the open unit interval `(0,1)`. -/
theorem exists_openUnit_arc_chart {X : Type*} [TopologicalSpace X] [Nonempty X]
    (hLoc : LocallyIntervalChart X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ U) := by
  rcases hLoc x with ⟨U, hUopen, hxU, lo, hi, ⟨e⟩⟩
  -- (lo,hi) ≃ ORI 0 1 via affine homeo when lo < hi; else contradiction-free handling
  by_cases hlt : lo < hi
  · rcases homeo_Ioo_openUnit lo hi hlt with ⟨a⟩
    refine ⟨U, hUopen, hxU, ?_⟩
    exact ⟨a.symm.trans e⟩
  · have hlo : hi ≤ lo := le_of_not_gt hlt
    -- U is nonempty (contains x) but (lo,hi) empty: impossible
    exfalso
    rcases e.surjective ⟨x, hxU⟩ with ⟨t, _⟩
    have hx' : lo < (t : ℝ) := t.2.1
    have hy' : (t : ℝ) < hi := t.2.2
    linarith


/-- **Countable cover by open arcs homeomorphic to the open unit interval.**
Every locally interval-charted Hausdorff second-countable space is covered
by countably many open sets each `≃ₜ ORI 0 1`. -/
theorem countable_open_ORI_cover {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] (hLoc : LocallyIntervalChart X) :
    ∃ A : ℕ → Set X,
      (∀ n, IsOpen (A n)) ∧ (∀ n, Nonempty (OpenRealInterval 0 1 ≃ₜ A n)) ∧
      (⋃ n, A n = univ) := by
  classical
  let U : X → Set X := fun x => Classical.choose (exists_openUnit_arc_chart hLoc x)
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    exact (Classical.choose_spec (exists_openUnit_arc_chart hLoc x)).1
  have hxU : ∀ x, x ∈ U x := by
    intro x
    exact (Classical.choose_spec (exists_openUnit_arc_chart hLoc x)).2.1
  have hUarc : ∀ x, Nonempty (OpenRealInterval 0 1 ≃ₜ U x) := by
    intro x
    exact (Classical.choose_spec (exists_openUnit_arc_chart hLoc x)).2.2
  rcases eq_open_union_nat (U := U) hUopen with ⟨k, hk⟩
  let A : ℕ → Set X := fun n => U (k n)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    exact hUopen (k n)
  · intro n
    exact hUarc (k n)
  · ext x
    constructor
    · intro hx
      exact trivial
    · intro _
      have hcov : x ∈ ⋃ x : X, U x := Set.mem_iUnion.mpr ⟨x, hxU x⟩
      have hsub : x ∈ ⋃ n, U (k n) := by rw [hk]; exact hcov
      simpa [A] using hsub

/-- In a connected space a proper nonempty open set has a boundary point:
`P̄ ∖ P` is nonempty. -/
lemma boundary_point_nonempty_of_proper_open {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] (P : Set X) (hPopen : IsOpen P) (hPne : P.Nonempty)
    (hPproper : P ≠ Set.univ) : (closure P \ P).Nonempty := by
  by_contra h
  have hsub : closure P ⊆ P := by
    intro x hx
    by_contra hxP
    exact h ⟨x, hx, hxP⟩
  have hclosed : IsClosed P := by
    rw [← closure_eq_iff_isClosed]
    exact Set.Subset.antisymm hsub subset_closure
  have hclopen : IsClopen P := ⟨hclosed, hPopen⟩
  have hPuniv : P = Set.univ := IsClopen.eq_univ hclopen hPne
  exact hPproper hPuniv

/-! ## LAYER 1 OF THE END THEORY — terminal extension of an open-arc
prefix (fleet L49, PROVED — imported from the commons as
`Commons.Topology.OneManifold.arc_extension_or_compact`)

In a connected Hausdorff second-countable locally interval-charted space,
every proper open arc (an open set `≃ₜ (0,1)`) either extends to a
strictly larger open arc, or the whole ambient space is compact.  (The
one-dimensional boundary/end analysis of the interval-side
classification; under `¬ CompactSpace X` every proper open arc is
extendable.)
-/

/-! ## LAYER 2 OF THE END THEORY — nested open-arc unions are open arcs
(fleet L50, PROVED — imported from the commons as
`Commons.Topology.OneManifold.nested_open_arcs_union_is_open_arc`)

The union of a nested increasing sequence of open arcs (each open in `X`
and `≃ₜ (0,1)`) is again an open arc `≃ₜ (0,1)` — the chain upper bound
of the maximal-arc exhaustion.  Proof (commons): re-chart each level so
the charts agree literally; coordinate domains are nested open intervals,
interval homeomorphisms extend across the ends, and the pasted coordinate
map is a homeomorphism onto an open real interval.
-/

/-! ## LAYER 3 — the maximal-arc dichotomy (fleet L64, PROVED — imported
from the commons as `Commons.Topology.OneManifold.oneManifold_dichotomy`)

A connected Hausdorff second-countable locally interval-charted space is
homeomorphic to the open unit interval `(0,1)` or is compact.  (Proof:
maximal-arc exhaustion — the family of open arcs containing a base arc
has chain upper bounds by Layer 2 (nested open-arc unions are open arcs),
so Zorn gives a maximal open arc, which Layer 1 forces to be all of `X`
unless `X` is compact.)
-/

/-!
# The classification theorem

The main theorem: a connected Hausdorff second-countable topological
1-manifold without boundary which is not compact is homeomorphic to the
open unit interval `(0,1)`.
-/

theorem noncompact_connected_oneManifold_interval
    {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    (hconn : ConnectedSpace X) (hnc : ¬ CompactSpace X) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ X) := by
  -- Layer 3 dichotomy: X ≃ (0,1) or X compact; non-compactness chooses the
  -- interval side.  (One-line assembly of the layer lemmas.)
  rcases oneManifold_dichotomy (X := X) hLoc with h | hC
  · exact h
  · exact False.elim (hnc hC)

namespace WalkEngine

open List

namespace ConnectedWalk

variable {X : Type*} [TopologicalSpace X]

/-- adjacency of two covering sets: they overlap -/
def Adj (U : ℕ → Set X) (a b : ℕ) : Prop := (U a ∩ U b).Nonempty

/-- In a preconnected space the overlap graph of a countable open cover by
nonempty sets is connected. -/
lemma graph_connected [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n) :
    ∀ a b : ℕ, Relation.ReflTransGen (Adj U) a b := by
  have hpre : IsPreconnected (univ : Set X) := isPreconnected_univ
  intro a b
  by_contra hb
  let P : ℕ → Prop := fun n => Relation.ReflTransGen (Adj U) a n
  have haP : P a := by
    dsimp [P]
    exact Relation.ReflTransGen.refl
  let u : Set X := {x : X | ∃ m : {m : ℕ // P m}, x ∈ U (m : ℕ)}
  have hu_open : IsOpen u := by
    rw [show u = ⋃ m : {m : ℕ // P m}, U (m : ℕ) by
      ext x
      simp [u]]
    exact isOpen_iUnion (fun m : {m : ℕ // P m} => hU (m : ℕ))
  let v : Set X := {x : X | ∃ n : {n : ℕ // ¬ P n}, x ∈ U (n : ℕ)}
  have hv_open : IsOpen v := by
    rw [show v = ⋃ n : {n : ℕ // ¬ P n}, U (n : ℕ) by
      ext x
      simp [v]]
    exact isOpen_iUnion (fun n : {n : ℕ // ¬ P n} => hU (n : ℕ))
  have hcov : (Set.univ : Set X) ⊆ u ∪ v := by
    intro x hx
    rcases hcover x with ⟨n, hxn⟩
    by_cases hn : P n
    · exact Or.inl ⟨⟨n, hn⟩, hxn⟩
    · exact Or.inr ⟨⟨n, hn⟩, hxn⟩
  have hu_ne : (univ ∩ u).Nonempty := by
    rcases hUn a with ⟨xa, hxa⟩
    refine ⟨xa, ⟨trivial, ⟨⟨a, haP⟩, hxa⟩⟩⟩
  have hv_ne : (univ ∩ v).Nonempty := by
    have hbP : ¬ P b := by
      intro hbin
      exact hb hbin
    rcases hUn b with ⟨xb, hxb⟩
    refine ⟨xb, ⟨trivial, ⟨⟨b, hbP⟩, hxb⟩⟩⟩
  have hsep : (univ ∩ (u ∩ v)).Nonempty :=
    hpre u v hu_open hv_open hcov hu_ne hv_ne
  rcases hsep with ⟨x, hxmem⟩
  rcases hxmem.2.1 with ⟨m, hxm⟩
  rcases hxmem.2.2 with ⟨n, hxn⟩
  have hadj : Adj U (m : ℕ) (n : ℕ) := ⟨x, hxm, hxn⟩
  have hR : Relation.ReflTransGen (Adj U) a (n : ℕ) :=
    Relation.ReflTransGen.trans (m : {m : ℕ // P m}).2
      (Relation.ReflTransGen.single hadj)
  exact (n : {n : ℕ // ¬ P n}).2 hR

/-- A finite walk from `a` to `b`: a nonempty list whose head is `a`, last
is `b`, consecutive elements related by `R`. -/
structure Walk (R : ℕ → ℕ → Prop) (a b : ℕ) where
  l : List ℕ
  ne : l ≠ []
  chain : l.IsChain R
  head : l.head ne = a
  last : l.getLast ne = b

namespace Walk

/-- The last element of a list does not depend on the nonemptiness proof. -/
private lemma getLast_irrel {l : List ℕ} {h₁ h₂ : l ≠ []} :
    l.getLast h₁ = l.getLast h₂ := by
  congr 1

/-- Append a final step `b —R→ c` at the end of a walk. -/
def append_last {R : ℕ → ℕ → Prop} {a b c : ℕ} (w : Walk R a b) (hbc : R b c) :
    Walk R a c := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  refine ⟨l ++ [c], ?_, ?_, ?_, ?_⟩
  · have hlen : 0 < (l ++ [c]).length := by
      rw [length_append]
      have h0 : 0 < l.length := List.length_pos_of_ne_nil lne
      omega
    exact List.ne_nil_of_length_pos hlen
  · rw [isChain_append]
    constructor
    · exact lchain
    constructor
    · exact List.isChain_singleton c
    · intro x hx y hy
      obtain ⟨hnx, hxeq⟩ := mem_getLast?_eq_getLast hx
      rw [hxeq]
      rw [llast]
      have hyc : c = y := by simpa using hy
      rw [← hyc]
      exact hbc
  · cases l with
    | nil => exfalso; exact lne rfl
    | cons x xs => simpa [lhead]
  · simpa [getLast_irrel] using (getLast_append_singleton l (a := c))

/-- The tail of a nontrivial walk list is nonempty. -/
lemma tail_ne {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b) (hab : a ≠ b) :
    w.l.tail ≠ [] := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  intro ht
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      have hxs : xs = [] := by
        simpa using ht
      subst xs
      have hx : x = a := by simpa using lhead
      have hb : x = b := by simpa using llast
      exact hab (hx.symm.trans hb)

/-- The tail of a walk list ends at the target. -/
lemma tail_last {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b)
    (ht : w.l.tail ≠ []) : w.l.tail.getLast ht = b := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      -- l = x :: xs, w.l.tail = xs
      cases xs with
      | nil => exact (ht rfl).elim
      | cons y ys =>
          -- target: (y :: ys).getLast ht = b; llast: (x :: y :: ys).getLast lne = b
          simpa using llast

/-- The first element of the tail is related to the head. -/
lemma rel_head_tail {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b)
    (ht : w.l.tail ≠ []) : R a (w.l.tail.head ht) := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      have hxs : xs ≠ [] := by simpa using ht
      have hc := (isChain_cons.mp lchain).1
      have hmem : xs.head hxs ∈ xs.head? := by
        cases xs with
        | nil => exact (hxs rfl).elim
        | cons y ys => simp
      have hR : R x (xs.head hxs) := hc (xs.head hxs) hmem
      have hx : x = a := by simpa using lhead
      simpa [hx] using hR

end Walk

/-- Equal nonempty lists have equal last elements. -/
private lemma getLast_congr {l l' : List ℕ} (h : l = l') {h₁ : l ≠ []} {h₂ : l' ≠ []} :
    l.getLast h₁ = l'.getLast h₂ := by
  subst l'
  congr 1
/-- An element of the `head?` of a nonempty list equals its head. -/
private lemma head_mem_head_eq {l : List ℕ} (hl : l ≠ []) {y : ℕ} (hy : y ∈ l.head?) :
    y = l.head hl := by
  have h := head_of_mem_head? hy
  rw [← h]


/-- An RTC proof yields a finite walk (existence). -/
lemma exists_walk_of_rtc {R : ℕ → ℕ → Prop} {a b : ℕ}
    (h : Relation.ReflTransGen R a b) : Nonempty (Walk R a b) := by
  induction h with
  | refl =>
      refine ⟨{ l := [a], ne := by simp, chain := by simp, head := rfl, last := rfl }⟩
  | tail hstep hrest ih =>
      rcases ih with ⟨w⟩
      exact ⟨w.append_last hrest⟩

/-- The concrete walk extracted from an RTC proof (choice). -/
noncomputable def walkOf {R : ℕ → ℕ → Prop} {a b : ℕ}
    (h : Relation.ReflTransGen R a b) : Walk R a b :=
  Classical.choice (exists_walk_of_rtc h)

/-- The state of the round construction: the walk list built so far and
the current vertex. -/
structure RoundData where
  list : List ℕ
  cur : ℕ

/-- One round: walk from `r` to `r+1` along the (choice) finite walk of the
connected graph, appending all new vertices of that walk to the list. -/
noncomputable def nextRound (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (s : RoundData) (r : ℕ) :
    RoundData :=
  ⟨s.list ++ (walkOf (allR r (r + 1))).l.tail, r + 1⟩

/-- The rounds: `rounds r` is the walk list that has visited every vertex
`≤ r` (and possibly more), ending at the vertex `r`. -/
noncomputable def rounds (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) : ℕ → RoundData
  | 0 => ⟨[0], 0⟩
  | r + 1 => nextRound R allR (rounds R allR r) r

/-- After round `r` the current vertex is `r`. -/
lemma rounds_cur (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).cur = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [rounds, nextRound]

/-- The joint invariants of the rounds: nonempty list, chain of consecutive
overlaps, ending at `r`, containing every vertex `≤ r`. -/
private lemma rounds_ind (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    ∃ ne : (rounds R allR r).list ≠ [],
      (rounds R allR r).cur = r ∧ (rounds R allR r).list.IsChain R ∧
      (rounds R allR r).list.getLast ne = r ∧
      ∀ k : ℕ, k ≤ r → k ∈ (rounds R allR r).list := by
  induction r with
  | zero =>
      refine ⟨by simp [rounds], ?_, ?_, ?_, ?_⟩
      · rfl
      · exact List.isChain_singleton 0
      · simp [rounds]
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp [rounds]
  | succ r ih =>
      rcases ih with ⟨ne, hcur, hchain, hlast, hmem⟩
      let s : RoundData := rounds R allR r
      let w : Walk R r (r + 1) := walkOf (allR r (r + 1))
      have hne_w : r ≠ r + 1 := by omega
      have htail : w.l.tail ≠ [] := w.tail_ne hne_w
      have hnewlist : (rounds R allR (r + 1)).list = s.list ++ w.l.tail := by
        rfl
      -- nonempty
      have hne' : (rounds R allR (r + 1)).list ≠ [] := by
        rw [hnewlist]
        apply List.ne_nil_of_length_pos
        rw [length_append]
        have h0 : 0 < s.list.length := List.length_pos_of_ne_nil ne
        have h0' : 0 ≤ w.l.tail.length := Nat.zero_le _
        omega
      refine ⟨hne', ?_, ?_, ?_, ?_⟩
      · simp [rounds, nextRound]
      · -- IsChain of s.list ++ w.l.tail
        rw [hnewlist]
        have htailchain : w.l.tail.IsChain R := w.chain.tail
        apply IsChain.append hchain htailchain
        intro x hx y hy
        obtain ⟨hnx, hxeq⟩ := mem_getLast?_eq_getLast hx
        rw [hxeq]
        -- x = getLast s.list ne = r
        have hxr : s.list.getLast ne = r := by
          simpa [s, hcur] using hlast
        rw [hxr]
        -- y is the head of the tail, related to r
        have hyh : y = w.l.tail.head htail := head_mem_head_eq htail hy
        rw [hyh]
        exact w.rel_head_tail htail
      · -- last = r+1
        have hne_app : (s.list ++ w.l.tail) ≠ [] :=
          append_ne_nil_of_right_ne_nil s.list htail
        have hmain : (s.list ++ w.l.tail).getLast hne_app = r + 1 := by
          rw [getLast_append_of_right_ne_nil s.list w.l.tail htail]
          exact w.tail_last htail
        exact (getLast_congr hnewlist (h₁ := hne') (h₂ := hne_app)).trans hmain
      · intro k hk
        rw [hnewlist]
        rw [List.mem_append]
        by_cases hkr : k ≤ r
        · exact Or.inl (hmem k hkr)
        · have hk1 : k = r + 1 := by omega
          subst k
          apply Or.inr
          -- r+1 is the last element of the tail, hence in the tail
          have hlastmem : w.l.tail.getLast htail ∈ w.l.tail := List.getLast_mem htail
          rw [w.tail_last htail] at hlastmem
          exact hlastmem

/-- The rounds list is nonempty. -/
lemma rounds_ne (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list ≠ [] :=
  (rounds_ind R allR r).1

/-- The rounds list is a chain (consecutive vertices overlap-related). -/
lemma rounds_chain (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list.IsChain R :=
  (rounds_ind R allR r).2.2.1

/-- The rounds list ends at the current vertex `r`. -/
lemma rounds_last (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list.getLast (rounds_ne R allR r) = r :=
  (rounds_ind R allR r).2.2.2.1

/-- The rounds list contains every vertex `≤ r`. -/
lemma rounds_mem (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) {k : ℕ} (hk : k ≤ r) :
    k ∈ (rounds R allR r).list :=
  (rounds_ind R allR r).2.2.2.2 k hk

/-- The list after round `r + 1` extends the list after round `r` by the
(possibly trivial) tail of the walk from `r` to `r+1`. -/
lemma rounds_succ_list (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR (r + 1)).list =
      (rounds R allR r).list ++ (walkOf (allR r (r + 1))).l.tail := by
  rfl

/-- The length of the rounds list is at least `r + 1`. -/
lemma rounds_length_ge (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    r + 1 ≤ (rounds R allR r).list.length := by
  induction r with
  | zero => simp [rounds]
  | succ r ih =>
      rw [rounds_succ_list]
      rw [length_append]
      have htail : (walkOf (allR r (r + 1))).l.tail ≠ [] :=
        (walkOf (allR r (r + 1))).tail_ne (by omega)
      have h1 : 1 ≤ (walkOf (allR r (r + 1))).l.tail.length :=
        Nat.succ_le_of_lt (List.length_pos_of_ne_nil htail)
      omega



/-- Getting an element of an append inside the left list is the same as
getting it from the left list. -/
private lemma get_append_left (l₁ t : List ℕ) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ t).get ⟨i, by rw [length_append]; omega⟩ = l₁.get ⟨i, hi⟩ := by
  have hpre : l₁ <+: l₁ ++ t := ⟨t, rfl⟩
  simpa using (IsPrefix.getElem hpre hi).symm

/-- Equal lists have equal get-elements at the same index. -/
private lemma get_eq_of_list_eq {l₁ l₂ : List ℕ} (h : l₁ = l₂) (i : ℕ)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁.get ⟨i, h₁⟩ = l₂.get ⟨i, h₂⟩ := by
  subst l₂
  congr 1

/-- The rounds list of round `n` extends the rounds list of round `k` by a
suffix (for `k ≤ n`). -/
private lemma rounds_prefix_tail (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n : ℕ} (h : k ≤ n) :
    ∃ t : List ℕ, (rounds R allR n).list = (rounds R allR k).list ++ t := by
  induction n with
  | zero =>
      refine ⟨[], ?_⟩
      have : k = 0 := by omega
      subst k
      simp [rounds]
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rcases ih hkn with ⟨t, ht⟩
        refine ⟨t ++ (walkOf (allR n (n + 1))).l.tail, ?_⟩
        rw [rounds_succ_list]
        rw [ht]
        simp [List.append_assoc]
      · have hk : k = n + 1 := by omega
        subst k
        refine ⟨[], ?_⟩
        simp [rounds_succ_list]

/-- The walk: `walkPos n` is the vertex visited at time `n` — the element
at position `n` of the `n`-th round list. -/
noncomputable def walkPos (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (n : ℕ) : ℕ :=
  (rounds R allR n).list.get ⟨n,
    Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩

/-- The rounds list of `k` is a prefix of the rounds list of any later
round. -/
private lemma rounds_prefix (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n : ℕ} (h : k ≤ n) :
    (rounds R allR k).list <+: (rounds R allR n).list := by
  rcases rounds_prefix_tail R allR h with ⟨t, ht⟩
  exact ⟨t, ht.symm⟩

/-- Elements of a round list stay fixed in all later rounds. -/
private lemma rounds_fix (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n i : ℕ} (h : k ≤ n)
    (hi : i < (rounds R allR k).list.length)
    (hi2 : i < (rounds R allR n).list.length) :
    (rounds R allR k).list.get ⟨i, hi⟩ = (rounds R allR n).list.get ⟨i, hi2⟩ := by
  rcases rounds_prefix_tail R allR h with ⟨t, ht⟩
  -- ht : (rounds n).list = (rounds k).list ++ t ; first step: left get = append get
  have h1 : (rounds R allR k).list.get ⟨i, hi⟩ =
      ((rounds R allR k).list ++ t).get ⟨i, by rw [length_append]; omega⟩ := by
    have hg := get_append_left (rounds R allR k).list t i hi
    -- hg : append.get⟨i, by omega⟩ = left.get⟨i,hi⟩
    exact hg.symm
  have h2 : ((rounds R allR k).list ++ t).get ⟨i,
      by rw [length_append]; omega⟩ = (rounds R allR n).list.get ⟨i, hi2⟩ :=
    get_eq_of_list_eq ht.symm i (by rw [length_append]; omega) hi2
  exact h1.trans h2

/-- Consecutive walk positions are related: `walkPos` is an overlap walk. -/
lemma walkPos_adjacent (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (n : ℕ) :
    R (walkPos R allR n) (walkPos R allR (n + 1)) := by
  have hn1 : n < (rounds R allR (n + 1)).list.length := by
    have h := rounds_length_ge R allR (n + 1)
    omega
  have hn2 : n + 1 < (rounds R allR (n + 1)).list.length :=
    Nat.lt_of_succ_le (rounds_length_ge R allR (n + 1))
  have hchain : R ((rounds R allR (n + 1)).list.get ⟨n, hn1⟩)
      ((rounds R allR (n + 1)).list.get ⟨n + 1, hn2⟩) := by
    exact (rounds_chain R allR (n + 1)).getElem n hn2
  have hfix : (rounds R allR n).list.get
      ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩ =
      (rounds R allR (n + 1)).list.get ⟨n, hn1⟩ := by
    exact rounds_fix R allR (k := n) (n := n + 1) (by omega)
      (Nat.lt_of_succ_le (rounds_length_ge R allR n)) hn1
  dsimp [walkPos]
  change R ((rounds R allR n).list.get
      ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩)
    ((rounds R allR (n + 1)).list.get
      ⟨n + 1, Nat.lt_of_succ_le (rounds_length_ge R allR (n + 1))⟩)
  rw [hfix]
  exact hchain

/-- The walk visits every vertex. -/
lemma walkPos_surjective (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) :
    Function.Surjective (walkPos R allR) := by
  intro k
  have hk : k ∈ (rounds R allR k).list := rounds_mem R allR k (le_rfl)
  rcases List.mem_iff_get.mp hk with ⟨i, hi⟩
  let n : ℕ := i.1
  have hn_lt : n < (rounds R allR n).list.length :=
    Nat.lt_of_succ_le (rounds_length_ge R allR n)
  refine ⟨n, ?_⟩
  dsimp [walkPos]
  by_cases hkn : k ≤ n
  · have hfix := rounds_fix R allR (k := k) (n := n) hkn i.2 hn_lt
    calc
      (rounds R allR n).list.get ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩
          = (rounds R allR k).list.get ⟨n, i.2⟩ := hfix.symm
      _ = k := hi
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    have hfix := rounds_fix R allR (k := n) (n := k) (le_of_lt hnk) hn_lt i.2
    calc
      (rounds R allR n).list.get ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩
          = (rounds R allR k).list.get ⟨n, i.2⟩ := hfix
      _ = k := hi


/-- **Overlap-walk of a countable connected open cover.**  A preconnected
space with a countable open cover by nonempty open sets admits an infinite
walk `e` visiting every index (starting at `0`) whose consecutive sets
overlap.  This is the enumeration input of the ordering construction
(interval-chain exhaustion) of the component classification. -/
theorem exists_overlap_walk [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n) :
    ∃ e : ℕ → ℕ, e 0 = 0 ∧ (∀ n, (U (e n) ∩ U (e (n + 1))).Nonempty) ∧
      Function.Surjective e := by
  classical
  let allR : ∀ a b : ℕ, Relation.ReflTransGen (Adj U) a b :=
    graph_connected U hU hUn hcover
  refine ⟨walkPos (Adj U) allR, ?_, ?_, ?_⟩
  · dsimp [walkPos]
    simp [rounds]
  · intro n
    exact walkPos_adjacent (Adj U) allR n
  · exact walkPos_surjective (Adj U) allR


/-- Membership in an `Iio`-indexed biUnion. -/
private lemma mem_biUnion_Iio {X : Type*} {U : ℕ → Set X} {x : X} {n : ℕ} :
    (x ∈ ⋃ m ∈ Set.Iio n, U m) ↔ ∃ m, m < n ∧ x ∈ U m := by
  simp

/-- **Path-connected exhaustion from the walk (combined form).**  If the
sets of the cover are path-connected, there is an overlap walk `e`
(consecutive overlaps, surjective, `e 0 = 0`) such that the partial
unions `V n = ⋃_{m < n+1} U (e m)` are an increasing exhaustion of `X` by
open path-connected sets.  This is the interval-chain-exhaustion input
over a connected component of the trisecant set (whose chart traces are
path-connected, homeomorphic to open intervals): the walk and the
exhaustion unions are returned together, tied by the defining equality
`V n = ⋃ m ∈ Iio (n+1), U (e m)`. -/
theorem exists_pathConnected_open_exhaustion [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n)
    (hpc : ∀ n, IsPathConnected (U n)) :
    ∃ (e : ℕ → ℕ) (V : ℕ → Set X),
      e 0 = 0 ∧ Function.Surjective e ∧
      (∀ n, (U (e n) ∩ U (e (n + 1))).Nonempty) ∧
      (∀ n, IsOpen (V n)) ∧ (∀ n, IsPathConnected (V n)) ∧
      (∀ n, V n ⊆ V (n + 1)) ∧ (∀ x : X, ∃ n, x ∈ V n) ∧
      (∀ n, V n = ⋃ m ∈ Set.Iio (n + 1), U (e m)) := by
  classical
  rcases exists_overlap_walk U hU hUn hcover with ⟨e, e0, hadj, esurj⟩
  let V : ℕ → Set X := fun n => ⋃ m ∈ Set.Iio (n + 1), U (e m)
  have hVstep : ∀ n, V (n + 1) = V n ∪ U (e (n + 1)) := by
    intro n
    ext x
    change (x ∈ ⋃ m ∈ Set.Iio (n + 2), U (e m) ↔
      x ∈ (⋃ m ∈ Set.Iio (n + 1), U (e m)) ∪ U (e (n + 1)))
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    rw [Set.mem_union]
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    constructor
    · rintro ⟨m, hm, hx⟩
      have hmle : m ≤ n + 1 := by omega
      rcases Nat.lt_or_eq_of_le hmle with hmlt | hmeq
      · exact Or.inl ⟨m, hmlt, hx⟩
      · subst m
        exact Or.inr hx
    · rintro (⟨m, hm, hx⟩ | hx)
      · exact ⟨m, by omega, hx⟩
      · exact ⟨n + 1, by omega, hx⟩
  refine ⟨e, V, e0, esurj, hadj, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [V]
    exact isOpen_biUnion (fun m hm => hU (e m))
  · intro n
    induction n with
    | zero =>
        have hV0 : V 0 = U (e 0) := by
          ext x
          dsimp [V]
          rw [mem_biUnion_Iio (U := fun m => U (e m))]
          simp
        rw [hV0]
        exact hpc (e 0)
    | succ n ih =>
        rw [hVstep n]
        apply IsPathConnected.union ih (hpc (e (n + 1)))
        rcases hadj n with ⟨x, hxmem⟩
        refine ⟨x, ?_, hxmem.2⟩
        dsimp [V]
        rw [mem_biUnion_Iio (U := fun m => U (e m))]
        exact ⟨n, by omega, hxmem.1⟩
  · intro n x hx
    rw [hVstep n]
    exact Or.inl hx
  · intro x
    rcases hcover x with ⟨m, hxm⟩
    rcases esurj m with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    dsimp [V]
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    refine ⟨p, by omega, ?_⟩
    rw [hp]
    exact hxm
  · intro n
    rfl

end ConnectedWalk

end WalkEngine

end Commons.Topology.OneManifold
