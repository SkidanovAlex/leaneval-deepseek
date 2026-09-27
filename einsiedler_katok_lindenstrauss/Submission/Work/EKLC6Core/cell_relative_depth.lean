import Mathlib
import Submission.Work.EKLC6Core.cellW_depth_aux
import Submission.Work.EKLC6Core.ShallowRelDefs
import Submission.Work.EKLC6Core.InjRadius

/-!
# `Work.EKLC6Core.cell_relative_depth` — relative depth of the orbit points

For a cell family `Q : ℕ → Set X₃` that is *pairwise disjoint* and *relatively thin* — meaning
that for every `ε > 0` the set of points all of whose containing cells have relative margin
`< ε * injCap` has measure `≤ C ε ^ α` — the orbit points of the `aDiag t`-flow that land in a
cell are, for `μ`-a.e. `x` and all sufficiently large `n`, `γ ^ n`-*deep* inside that cell
*relative to their own injectivity radius*: the whole `V`-ball `V (γ ^ n * injCap y) · y` stays
in the cell.

The proof is the standard Borel–Cantelli argument along a measure-preserving orbit.  Two facts
are used:
* the pointwise reduction `shallowRel_cellMargin_subset_crd`: for a *disjoint* cell family, the
  relatively shallow set is contained in the set of points each of whose cells has small relative
  margin (this is where disjointness enters — a shallow point is witnessed by one cell `Q k`, and
  every other cell through the point must coincide with `Q k`);
* `geometric_borel_cantelli`, applied to the geometric sequence of relative scales
  `γ ^ n = (γ ^ α) ^ n`, `γ ^ α < 1`.

No geometric hypothesis on `injCap` along the orbit is required; this is the point of the
*relative* formulation.
-/

namespace Work.EKLC6Core

open Work.EKLContract MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

/-- **Pointwise reduction.**  For a *disjoint* cell family, the relatively `ε`-shallow set is
contained in the set of points every containing cell of which has relative margin `< ε'`, for any
`ε' > ε`.

Indeed, if `y` is shallow with witness cell `k`, then the margin of `k` at `y` is `≤ ε * injCap y`
(otherwise the `ε * injCap y`-ball around `y` would be inside `Q k`); and disjointness forces
every cell containing `y` to coincide with `Q k`. -/
theorem shallowRel_cellMargin_subset_crd {Q : ℕ → Set X3}
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
theorem cell_relative_depth {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Q : ℕ → Set Work.EKLContract.X3} (hdisj : ∀ k l : ℕ, k ≠ l → Disjoint (Q k) (Q l))
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hthin : ∀ ε : ℝ, 0 < ε → μ {y : Work.EKLContract.X3 |
        ∀ k, y ∈ Q k → Work.EKLC6Core.cellMargin Q k y < ε * Work.EKLC6Core.injCap y}
      ≤ ENNReal.ofReal (C * ε ^ α))
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
      (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ Q k →
      ∀ v : Work.EKLContract.SL3,
        v ∈ Work.EKLContract.V (γ ^ n *
          Work.EKLC6Core.injCap (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x)) →
        v • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ Q k := by
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
    refine shallowRel_cellMargin_subset_crd hdisj (pow_nonneg hγnn n) ?_
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

end

end Work.EKLC6Core
