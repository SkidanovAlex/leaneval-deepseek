/-
  WilC4 : the elementary definability input of the o-minimal monotonicity theorem.

  The graph `Y ⊆ ℝ²` of a `∅`-definable partial function is given; we show that the three
  *purely first-order* derived objects of `monoDefs` are definable over the same parameter set:

  * `MonoDom Y` — the domain, the projection of `Y` (one existential quantifier over the value);
  * `MonoLA Y`  — the relation `f x < f w` (reindex the variables, `<` is definable by
    `x ≤ y ↔ ∃ z, x + z * z = y` in `ℝ`, and existentially quantify the two values);
  * `MonoHA Y`  — the relation `f x > f w`, the same with the opposite comparison.

  The remaining definability inputs of `mono_real` (`MonoW`, `MonoLm`, …) are *not* of this
  purely logical kind: they quantify over *neighbourhoods* (`∃ ε > 0, ∀ z, |z - x| < ε → …`)
  and are handled separately.

  All the technical work is variable bookkeeping: `Set.Definable` lives on `Set (α → ℝ)` for a
  finite index type `α`, so a formula with two quantified *value* variables is written on
  `(Fin 2 ⊕ Fin 2) → ℝ` and the values are projected out with `Set.Definable.exists_of_finite`,
  which is exactly the semantic content of `∃ y y'`.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.finite_definable_singleton

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## Two reindexing helpers -/

/-- The relation `Y ⊆ ℝ²` pulled back along the "pair of coordinates" map `w ↦ ![w i, w j]`.
This is `Set.Definable.preimage_comp` for the index map `![i, j] : Fin 2 → α`, with the
composition `w ∘ ![i, j]` identified with `![w i, w j]`. -/
private lemma definable_pair_mem {A : Set ℝ} {Y : Set (Fin 2 → ℝ)} (hY : A.Definable LRc Y)
    {α : Type*} (i j : α) : A.Definable LRc {w : α → ℝ | ![w i, w j] ∈ Y} := by
  have h := hY.preimage_comp ![i, j]
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [show (![w i, w j] : Fin 2 → ℝ) = w ∘ ![i, j] from by funext k; fin_cases k <;> rfl]

/-- Coordinatewise `<` is `A`-definable in `ℝ` for every parameter set `A`: in a real closed
field `x ≤ y ↔ ∃ z, x + z * z = y` (`Work.WilC2.definable_le`), and `x < y ↔ x ≤ y ∧ ¬ y ≤ x`. -/
private lemma definable_lt_coord {A : Set ℝ} {α : Type*} (i j : α) :
    A.Definable LRc {v : α → ℝ | v i < v j} := by
  have h1 : A.Definable LRc {v : α → ℝ | v i ≤ v j} :=
    Work.WilC2.definable_le Work.WilC2.real_exists_sq i j
  have h2 : A.Definable LRc {v : α → ℝ | v j ≤ v i} :=
    Work.WilC2.definable_le Work.WilC2.real_exists_sq j i
  have h := h1.sdiff h2
  convert h using 1
  ext v
  simp only [Set.mem_sdiff, Set.mem_setOf_eq]
  exact lt_iff_le_not_ge

/-- The common shape of `MonoLA` and `MonoHA`: the relation "`v 0` and `v 1` are both in the
domain of `Y` and the value at `v 0` compares with the value at `v 1` according to the
`∅`-definable relation `R` on the pair of values".  It is definable as soon as `Y` and `R` are. -/
private lemma definable_value_pair {A : Set ℝ} {Y : Set (Fin 2 → ℝ)} (hY : A.Definable LRc Y)
    {R : Set (Fin 2 → ℝ)} (hR : A.Definable LRc R) :
    A.Definable LRc {v : Fin 2 → ℝ |
      ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![v 1, y'] ∈ Y ∧ ![y, y'] ∈ R} := by
  -- the two "the point `v 0`, resp. `v 1`, carries the value `y`, resp. `y'`" relations
  have h1 : A.Definable LRc
      {w : (Fin 2 ⊕ Fin 2) → ℝ | ![w (Sum.inl (0 : Fin 2)), w (Sum.inr (0 : Fin 2))] ∈ Y} :=
    definable_pair_mem hY (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2))
  have h2 : A.Definable LRc
      {w : (Fin 2 ⊕ Fin 2) → ℝ | ![w (Sum.inl (1 : Fin 2)), w (Sum.inr (1 : Fin 2))] ∈ Y} :=
    definable_pair_mem hY (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
  -- the comparison relation on the two value variables
  have h3 : A.Definable LRc
      {w : (Fin 2 ⊕ Fin 2) → ℝ | ![w (Sum.inr (0 : Fin 2)), w (Sum.inr (1 : Fin 2))] ∈ R} :=
    definable_pair_mem hR (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2))
  -- and now eliminate the two value variables
  have hproj := ((h1.inter h2).inter h3).exists_of_finite
  convert hproj using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨y, y', h1, h2, h3⟩
    exact ⟨![y, y'], ⟨by simpa using h1, by simpa using h2⟩, by simpa using h3⟩
  · rintro ⟨u, ⟨hu1, hu2⟩, hu3⟩
    exact ⟨u 0, u 1, hu1, hu2, hu3⟩

/-! ## The theorem -/

theorem monoDefinable_basic {Y : Set (Fin 2 → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoDom Y) ∧
      (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MonoLA Y) ∧
      (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MonoHA Y) := by
  -- `MonoDom Y = {x | ∃ y, (x, y) ∈ Y}`: the domain is the projection of `Y`
  have hDom : (∅ : Set ℝ).Definable₁ LRc (MonoDom Y) := by
    rw [Set.Definable₁]
    have h1 : (∅ : Set ℝ).Definable LRc
        {w : (Fin 1 ⊕ Fin 1) → ℝ | ![w (Sum.inl (0 : Fin 1)), w (Sum.inr (0 : Fin 1))] ∈ Y} :=
      definable_pair_mem hY (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1))
    have hproj := h1.exists_of_finite
    convert hproj using 1
    ext v
    simp only [Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr, mem_MonoDom]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨fun _ => y, by simpa using hy⟩
    · rintro ⟨u, hu⟩
      exact ⟨u 0, hu⟩
  have hLA : (∅ : Set ℝ).Definable LRc (MonoLA Y) := by
    have hR : (∅ : Set ℝ).Definable LRc {z : Fin 2 → ℝ | z 0 < z 1} :=
      definable_lt_coord (0 : Fin 2) (1 : Fin 2)
    have h := definable_value_pair hY hR
    have hset : MonoLA Y =
        {v : Fin 2 → ℝ | ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![v 1, y'] ∈ Y ∧
          ![y, y'] ∈ {z : Fin 2 → ℝ | z 0 < z 1}} := by
      ext v
      simp only [MonoLA, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, y', h1, h2, h3⟩
        exact ⟨y, y', h1, h2, by simpa using h3⟩
      · rintro ⟨y, y', h1, h2, h3⟩
        exact ⟨y, y', h1, h2, by simpa using h3⟩
    rw [hset]
    exact h
  have hHA : (∅ : Set ℝ).Definable LRc (MonoHA Y) := by
    have hR : (∅ : Set ℝ).Definable LRc {z : Fin 2 → ℝ | z 1 < z 0} :=
      definable_lt_coord (1 : Fin 2) (0 : Fin 2)
    have h := definable_value_pair hY hR
    have hset : MonoHA Y =
        {v : Fin 2 → ℝ | ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![v 1, y'] ∈ Y ∧
          ![y, y'] ∈ {z : Fin 2 → ℝ | z 1 < z 0}} := by
      ext v
      simp only [MonoHA, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, y', h1, h2, h3⟩
        exact ⟨y, y', h1, h2, by simpa using h3⟩
      · rintro ⟨y, y', h1, h2, h3⟩
        exact ⟨y, y', h1, h2, by simpa using h3⟩
    rw [hset]
    exact h
  exact ⟨hDom, hLA, hHA⟩

end Work.WilC4
