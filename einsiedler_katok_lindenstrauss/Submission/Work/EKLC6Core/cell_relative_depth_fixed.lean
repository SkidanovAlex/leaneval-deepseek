import Mathlib
import Submission.Work.EKLC6Core.cellW_depth_aux
import Submission.Work.EKLC6Core.ShallowRelDefs
import Submission.Work.EKLC6Core.InjRadius

/-!
# `Work.EKLC6Core.cell_relative_depth_fixed` — relative depth from relative thinness
(disjoint cells)

`Work.EKLC6Core.cell_relative_depth` as written is **false**: the relative-thinness hypothesis
bounds the measure of

`{y | ∀ k, y ∈ Q k → cellMargin Q k y < ε * injCap y}`,

which is the "**every** cell containing `y` has a small margin" condition.  When two cells
`Q k ≠ Q k'` overlap in a point `y`, only *one* of the two margins is constrained, while the
conclusion asks the ball `V (γ ^ n * injCap y) · y` to be inside **every** cell containing `y`.
So one can put a cell with a huge margin (the whole space, margin `2`) and a cell with margin
`0` (a singleton) into the same family: the thinness hypothesis is then vacuous
(`ε * injCap y ≤ ε / 2 < 2` for `ε ≤ 4`, so no point satisfies it), but the conclusion fails at
every `n`.

The missing hypothesis is *disjointness* of the cells.  With `∀ k l, k ≠ l → Disjoint (Q k) (Q l)`
a point `y` lies in at most one cell, so relative thinness does bound
`shallowRel Q ε`, and the standard Borel–Cantelli along the measure-preserving orbit gives
the conclusion — with **no** hypothesis on the geometry of `V` beyond `injCap` itself
(in particular no geometric decay of `injCap` along the orbit, unlike
`Work.EKLC6Core.cellW_depth_of_relthin`): this is the point of the *relative* formulation.

## Main results

Two ways of repairing it, both proved here:

* keep the `∀ k`-form of `hthin` and **assume the cells are pairwise disjoint**
  (`shallowRel_subset_cellMargin_of_disjoint`, `cell_relative_depth_of_disjoint`); or
* keep overlapping cells and state `hthin` in the **`∃`-form** ("some containing cell is thin",
  `shallowRel_subset_exists_cellMargin`, `cell_relative_depth_of_exists_thin`) — this is the form
  in which `hthin` is actually derived in practice, since a shallow point `y` is witnessed by a
  single cell.

A formal counterexample to the statement as requested is in
`Submission.Work.EKLC6Core.cell_relative_depth_refutation`.
-/

namespace Work.EKLC6Core

open Work.EKLContract MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

/-- **The pointwise reduction.**  For a *disjoint* cell family, the relatively `ε`-shallow set
is contained in the set of points every cell of which has `(ε')`-small relative margin, for any
`ε' > ε`.

Indeed, if `y` is shallow with witness cell `k`, then the margin of `k` at `y` is `≤ ε * injCap y`
(otherwise the `ε * injCap y`-ball around `y` would be inside `Q k`); and disjointness forces
every cell containing `y` to be `Q k`. -/
theorem shallowRel_subset_cellMargin_of_disjoint {Q : ℕ → Set X3}
    (hdisj : ∀ k l : ℕ, k ≠ l → Disjoint (Q k) (Q l)) {ε ε' : ℝ} (hε : 0 ≤ ε) (hlt : ε < ε') :
    shallowRel Q ε ⊆ {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < ε' * injCap y} := by
  rintro y ⟨k, hk, v, hv, hvy⟩
  have hcap : 0 < injCap y := injCap_pos y
  have hle : cellMargin Q k y ≤ ε * injCap y := by
    by_contra hcon
    push_neg at hcon
    exact hvy (cellMargin_property hcon (mul_nonneg hε (le_of_lt hcap)) v hv)
  intro k' hk'
  have hk'k : k' = k := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj k' k hne) hk' hk
  subst hk'k
  exact lt_of_le_of_lt hle (by nlinarith [hlt, hcap])

/-- **Relative depth of the orbit points, for disjoint cells.**  Under the relative-thinness
hypothesis (and disjointness of the cells), for `μ`-a.e. `x` the orbit points
`aDiag t ^[n] · x`, as soon as they lie in a cell `Q k`, are `γ ^ n`-deep inside it *relative to
their own injectivity radius*: the whole ball `V (γ ^ n * injCap y) · y` stays in `Q k`. -/
theorem cell_relative_depth_of_disjoint
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {Q : ℕ → Set X3} (hdisj : ∀ k l : ℕ, k ≠ l → Disjoint (Q k) (Q l))
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hthin : ∀ ε : ℝ, 0 < ε → μ {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < ε * injCap y}
      ≤ ENNReal.ofReal (C * ε ^ α))
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
      (((fun y : X3 => aDiag t • y)^[n]) x) ∈ Q k →
      ∀ v : SL3,
        v ∈ V (γ ^ n * injCap (((fun y : X3 => aDiag t • y)^[n]) x)) →
        v • (((fun y : X3 => aDiag t • y)^[n]) x) ∈ Q k := by
  classical
  have hγnn : 0 ≤ γ := le_of_lt hγ0
  have h2α : (0 : ℝ) ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  have hγα0 : 0 ≤ γ ^ α := Real.rpow_nonneg hγnn α
  have hγα1 : γ ^ α < 1 := Real.rpow_lt_one hγnn hγ1 hα
  set A : ℕ → Set X3 := fun n => ((fun y : X3 => aDiag t • y)^[n]) ⁻¹'
    {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < (2 * γ ^ n) * injCap y} with hA
  have hsub : ∀ n : ℕ, shallowRel Q (γ ^ n)
      ⊆ {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < (2 * γ ^ n) * injCap y} := by
    intro n
    refine shallowRel_subset_cellMargin_of_disjoint hdisj (pow_nonneg hγnn n) ?_
    have := pow_pos hγ0 n
    linarith
  have hbound : ∀ n : ℕ, μ (A n)
      ≤ ENNReal.ofReal ((C * (2 : ℝ) ^ α) * (γ ^ α) ^ n) := by
    intro n
    have hε : 0 < 2 * γ ^ n := by positivity
    have h2 : (2 * γ ^ n) ^ α = (2 : ℝ) ^ α * (γ ^ α) ^ n := by
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hγnn n), ← Real.rpow_natCast γ n,
        ← Real.rpow_mul hγnn (n : ℝ) α, mul_comm (n : ℝ) α, Real.rpow_mul hγnn α (n : ℝ),
        Real.rpow_natCast]
    refine le_trans ((hmp.iterate n).measure_preimage_le
      {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < (2 * γ ^ n) * injCap y}) ?_
    refine le_trans (hthin (2 * γ ^ n) hε) ?_
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [h2]
    ring
  have hnull : μ (⋂ N : ℕ, ⋃ n ≥ N, A n) = 0 :=
    geometric_borel_cantelli μ A (mul_nonneg (le_of_lt hC) h2α) hγα0 hγα1 hbound
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  rw [Filter.not_eventually, Filter.frequently_atTop] at hx
  refine Set.mem_iInter.mpr fun N => ?_
  obtain ⟨n, hnN, hn⟩ := hx N
  refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hnN, ?_⟩⟩
  show (((fun y : X3 => aDiag t • y)^[n]) x) ∈
    {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < (2 * γ ^ n) * injCap y}
  have hsh : (((fun y : X3 => aDiag t • y)^[n]) x) ∈ shallowRel Q (γ ^ n) := by
    by_contra hc
    exact hn ((not_shallowRel_iff).mp hc)
  exact hsub n hsh


/-- **The pointwise reduction, `∃`-form.**  If *some* cell containing `y` is `ε`-thin at `y`, then
`y` is *not* deeply inside all of its cells: `shallowRel Q ε` is contained in the set of points
having a containing cell whose relative margin is `< ε'` (any `ε' > ε`).

No disjointness is needed here — this is the `∃`-version of the thinness condition, and it is what
makes the statement true also for overlapping families. -/
theorem shallowRel_subset_exists_cellMargin {Q : ℕ → Set X3} {ε ε' : ℝ} (hε : 0 ≤ ε)
    (hlt : ε < ε') :
    shallowRel Q ε ⊆ {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < ε' * injCap y} := by
  rintro y ⟨k, hk, v, hv, hvy⟩
  refine ⟨k, hk, ?_⟩
  have hcap : 0 < injCap y := injCap_pos y
  have hle : cellMargin Q k y ≤ ε * injCap y := by
    by_contra hcon
    push_neg at hcon
    exact hvy (cellMargin_property hcon (mul_nonneg hε (le_of_lt hcap)) v hv)
  exact lt_of_le_of_lt hle (by nlinarith [hlt, hcap])

/-- **Relative depth of the orbit points, `∃`-form of thinness.**  The conclusion of
`Work.EKLC6Core.cell_relative_depth` holds as soon as relative thinness is assumed in the
`∃`-form: the measure of the points having *some* containing cell of relative margin `< ε` is
`≤ C ε ^ α`.  No disjointness and no geometric hypothesis on `injCap` along the orbit is needed. -/
theorem cell_relative_depth_of_exists_thin
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {Q : ℕ → Set X3}
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hthin : ∀ ε : ℝ, 0 < ε → μ {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < ε * injCap y}
      ≤ ENNReal.ofReal (C * ε ^ α))
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
      (((fun y : X3 => aDiag t • y)^[n]) x) ∈ Q k →
      ∀ v : SL3,
        v ∈ V (γ ^ n * injCap (((fun y : X3 => aDiag t • y)^[n]) x)) →
        v • (((fun y : X3 => aDiag t • y)^[n]) x) ∈ Q k := by
  classical
  have hγnn : 0 ≤ γ := le_of_lt hγ0
  have h2α : (0 : ℝ) ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  have hγα0 : 0 ≤ γ ^ α := Real.rpow_nonneg hγnn α
  have hγα1 : γ ^ α < 1 := Real.rpow_lt_one hγnn hγ1 hα
  set A : ℕ → Set X3 := fun n => ((fun y : X3 => aDiag t • y)^[n]) ⁻¹'
    {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < (2 * γ ^ n) * injCap y} with hA
  have hsub : ∀ n : ℕ, shallowRel Q (γ ^ n)
      ⊆ {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < (2 * γ ^ n) * injCap y} := by
    intro n
    refine shallowRel_subset_exists_cellMargin (pow_nonneg hγnn n) ?_
    have := pow_pos hγ0 n
    linarith
  have hbound : ∀ n : ℕ, μ (A n)
      ≤ ENNReal.ofReal ((C * (2 : ℝ) ^ α) * (γ ^ α) ^ n) := by
    intro n
    have hε : 0 < 2 * γ ^ n := by positivity
    have h2 : (2 * γ ^ n) ^ α = (2 : ℝ) ^ α * (γ ^ α) ^ n := by
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hγnn n), ← Real.rpow_natCast γ n,
        ← Real.rpow_mul hγnn (n : ℝ) α, mul_comm (n : ℝ) α, Real.rpow_mul hγnn α (n : ℝ),
        Real.rpow_natCast]
    refine le_trans ((hmp.iterate n).measure_preimage_le
      {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < (2 * γ ^ n) * injCap y}) ?_
    refine le_trans (hthin (2 * γ ^ n) hε) ?_
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [h2]
    ring
  have hnull : μ (⋂ N : ℕ, ⋃ n ≥ N, A n) = 0 :=
    geometric_borel_cantelli μ A (mul_nonneg (le_of_lt hC) h2α) hγα0 hγα1 hbound
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  rw [Filter.not_eventually, Filter.frequently_atTop] at hx
  refine Set.mem_iInter.mpr fun N => ?_
  obtain ⟨n, hnN, hn⟩ := hx N
  refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hnN, ?_⟩⟩
  show (((fun y : X3 => aDiag t • y)^[n]) x) ∈
    {y : X3 | ∃ k, y ∈ Q k ∧ cellMargin Q k y < (2 * γ ^ n) * injCap y}
  have hsh : (((fun y : X3 => aDiag t • y)^[n]) x) ∈ shallowRel Q (γ ^ n) := by
    by_contra hc
    exact hn ((not_shallowRel_iff).mp hc)
  exact hsub n hsh

end

end Work.EKLC6Core
