/-
# Mass transference in `ℝ`, `k = 1`, `f(r) = r ^ d`: basic objects

This file sets up the notation for the Beresnevich–Velani mass transference
principle in `ℝ` (`k = 1`) for the power dimension function `f(r) = r ^ d`,
`0 < d < 1`, for a family indexed by `ℕ`.

* `Iv x r` is the closed interval with centre `x` and radius `r`;
* `Fsm c ρ i = Iv (c i) (ρ i)` is the `i`-th "small" interval;
* `Fenl d c ρ i = Iv (c i) ((ρ i) ^ d)` is the `i`-th "enlarged" interval;
* `LSsm c ρ`, `LSenl d c ρ` are the corresponding limsup sets, restricted to
  positive radii (the form in which the full measure hypothesis is used in the
  construction);
* `LSsm' c ρ`, `LSenl' d c ρ` are the limsup sets over *all* radii; `LSsm'` is
  the set appearing in the conclusion of the main theorem.

Main results of the file:

* `full_measure_pos` : the full measure hypothesis for the enlarged intervals
  transfers from "all radii" to "positive radii" (the zero-radius indices can
  only contribute a countable set);
* `eventually_small`, `infinite_fresh` : the "radii tend to `0`" hypothesis
  `hρfin` says that for every `ε > 0` all but finitely many indices satisfy
  `ρ i < ε`, which gives the supply of fresh indices used in the construction.
-/
import Mathlib

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt

/-- The closed interval with centre `x` and radius `r`. -/
def Iv (x r : ℝ) : Set ℝ := Set.Icc (x - r) (x + r)

/-- The `i`-th "small" interval `B(c i, ρ i)`. -/
def Fsm (c ρ : ℕ → ℝ) (i : ℕ) : Set ℝ := Iv (c i) (ρ i)

/-- The `i`-th "enlarged" interval `B(c i, (ρ i) ^ d)`. -/
def Fenl (d : ℝ) (c ρ : ℕ → ℝ) (i : ℕ) : Set ℝ := Iv (c i) ((ρ i) ^ d)

/-- The limsup set of the enlarged intervals, over indices with positive radius. -/
def LSenl (d : ℝ) (c ρ : ℕ → ℝ) : Set ℝ :=
  {z : ℝ | {i : ℕ | 0 < ρ i ∧ |z - c i| ≤ (ρ i) ^ d}.Infinite}

/-- The limsup set of the enlarged intervals, over all indices. -/
def LSenl' (d : ℝ) (c ρ : ℕ → ℝ) : Set ℝ :=
  {z : ℝ | {i : ℕ | |z - c i| ≤ (ρ i) ^ d}.Infinite}

/-- The limsup set of the small intervals, over indices with positive radius. -/
def LSsm (c ρ : ℕ → ℝ) : Set ℝ :=
  {z : ℝ | {i : ℕ | 0 < ρ i ∧ |z - c i| ≤ ρ i}.Infinite}

/-- The limsup set of the small intervals, over all indices. -/
def LSsm' (c ρ : ℕ → ℝ) : Set ℝ :=
  {z : ℝ | {i : ℕ | |z - c i| ≤ ρ i}.Infinite}

/-! ### The interval `Iv x r` -/

lemma mem_Iv {x r z : ℝ} : z ∈ Iv x r ↔ |z - x| ≤ r := by
  simp only [Iv, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

lemma Iv_nonempty {x r : ℝ} (hr : 0 ≤ r) : (Iv x r).Nonempty :=
  ⟨x, by rw [mem_Iv]; simpa using hr⟩

lemma isClosed_Iv (x r : ℝ) : IsClosed (Iv x r) := isClosed_Icc

lemma isCompact_Iv (x r : ℝ) : IsCompact (Iv x r) := isCompact_Icc

/-- `Iv` is monotone in the radius. -/
lemma Iv_mono {x : ℝ} {r s : ℝ} (h : r ≤ s) : Iv x r ⊆ Iv x s := by
  intro z hz
  rw [mem_Iv] at hz ⊢
  exact hz.trans h

/-- Inclusion of intervals, in terms of the centres and radii. -/
lemma Iv_subset_Iv {x y r s : ℝ} (h : |x - y| + r ≤ s) : Iv x r ⊆ Iv y s := by
  intro z hz
  rw [mem_Iv] at hz ⊢
  calc |z - y| = |(z - x) + (x - y)| := by ring_nf
    _ ≤ |z - x| + |x - y| := abs_add_le _ _
    _ ≤ r + |x - y| := by linarith
    _ = |x - y| + r := by ring
    _ ≤ s := h

/-- Two intervals with nonnegative radii `r`, `s` are disjoint iff the distance of their
centres exceeds `r + s`. -/
lemma disjoint_Iv_iff {x y r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Disjoint (Iv x r) (Iv y s) ↔ r + s < |x - y| := by
  rw [Set.disjoint_left]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hxy : |x - y| ≤ r + s := hle
    have h1 : x - r ≤ y + s := by linarith [le_abs_self (x - y), neg_abs_le (x - y)]
    have h2 : y - s ≤ x + r := by linarith [le_abs_self (x - y), neg_abs_le (x - y)]
    have hz1 : min (x + r) (y + s) ∈ Iv x r := by
      rw [Iv, Set.mem_Icc]
      exact ⟨le_min (by linarith) h1, min_le_left _ _⟩
    have hz2 : min (x + r) (y + s) ∈ Iv y s := by
      rw [Iv, Set.mem_Icc]
      exact ⟨le_min h2 (by linarith), min_le_right _ _⟩
    exact h hz1 hz2
  · intro h z hz1 hz2
    rw [mem_Iv] at hz1 hz2
    have hxz : |x - z| ≤ r := by rw [abs_sub_comm x z]; exact hz1
    have h' : |x - y| ≤ |x - z| + |z - y| := by
      calc |x - y| = |(x - z) + (z - y)| := by ring_nf
        _ ≤ |x - z| + |z - y| := abs_add_le _ _
    linarith

/-- The Lebesgue measure of `Iv x r` is `2 r`. -/
lemma volume_Iv (x r : ℝ) (hr : 0 ≤ r) : volume (Iv x r) = ENNReal.ofReal (2 * r) := by
  rw [Iv, Real.volume_Icc]
  congr 1
  ring

/-- The `1`-dimensional Hausdorff measure is Lebesgue measure, so the same formula holds. -/
lemma hausdorffMeasure_one_Iv (x r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.Measure.hausdorffMeasure 1 (Iv x r) = ENNReal.ofReal (2 * r) := by
  rw [MeasureTheory.hausdorffMeasure_real]
  exact volume_Iv x r hr

/-- The (e)metric diameter of `Iv x r` is `2 r`. -/
lemma ediam_Iv (x r : ℝ) (hr : 0 ≤ r) : ediam (Iv x r) = ENNReal.ofReal (2 * r) := by
  refine le_antisymm ?_ ?_
  · refine ediam_le_of_forall_dist_le ?_
    intro a ha b hb
    rw [mem_Iv] at ha hb
    rw [abs_le] at ha hb
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · have hmem1 : x - r ∈ Iv x r := by rw [mem_Iv, abs_le]; constructor <;> linarith
    have hmem2 : x + r ∈ Iv x r := by rw [mem_Iv, abs_le]; constructor <;> linarith
    have h := edist_le_ediam_of_mem hmem1 hmem2
    rw [edist_dist, Real.dist_eq] at h
    have h2 : |x - r - (x + r)| = 2 * r := by
      rw [show x - r - (x + r) = -(2 * r) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [h2] at h
    exact h

/-! ### `hρfin` and its consequences -/

section Hρfin

variable {ρ : ℕ → ℝ}

/-- `hρfin` implies that all but finitely many indices have radius `< ε`. -/
lemma eventually_small (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (ε : ℝ) (hε : 0 < ε) : ∃ G : ℕ, ∀ i, G ≤ i → ρ i < ε := by
  let T : Finset ℕ := (hρfin ε hε).toFinset
  refine ⟨T.sup id + 1, fun i hi => ?_⟩
  by_contra h
  rw [not_lt] at h
  have hiT : i ∈ T := by rw [Set.Finite.mem_toFinset]; exact h
  have : i ≤ T.sup id := Finset.le_sup (f := id) hiT
  omega

/-- Infinitely many indices have radius `< ε`. -/
lemma infinite_lt_of_hρfin (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (ε : ℝ) (hε : 0 < ε) : {i : ℕ | ρ i < ε}.Infinite :=
  (Set.Finite.infinite_compl (hρfin ε hε)).mono (by intro i hi; simpa using hi)

/-- **The covering property of the enlarged limsup set at arbitrarily small scales.**
If `z` lies in the enlarged limsup set (over positive radii), then for every `ε > 0` and
every finite set `T` of indices there is a *fresh* index `i ∉ T` with `0 < ρ i < ε` whose
enlarged interval contains `z`.  This is the statement used to cover the "good" part of an
interval in the construction. -/
lemma exists_fresh_of_mem_LSenl {d : ℝ} {c ρ : ℕ → ℝ}
    (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    {ε : ℝ} (hε : 0 < ε) {z : ℝ} (hz : z ∈ LSenl d c ρ) (T : Finset ℕ) :
    ∃ i, i ∉ T ∧ 0 < ρ i ∧ ρ i < ε ∧ |z - c i| ≤ (ρ i) ^ d := by
  have h3 : ({i : ℕ | 0 < ρ i ∧ |z - c i| ≤ (ρ i) ^ d} \
      ({i : ℕ | ε ≤ ρ i} ∪ (T : Set ℕ))).Infinite :=
    hz.sdiff ((hρfin ε hε).union T.finite_toSet)
  obtain ⟨i, hi⟩ := h3.nonempty
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_union] at hi
  obtain ⟨⟨hpos, hcov⟩, hnot⟩ := hi
  push_neg at hnot
  exact ⟨i, hnot.2, hpos, hnot.1, hcov⟩

end Hρfin

/-! ### The full measure hypothesis -/

section FullMeasure

variable (c ρ : ℕ → ℝ)

/-- The set of points `z` such that infinitely many indices with `ρ i = 0` are centred
exactly at `z` is countable. -/
lemma countable_zero_radius :
    ({z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite}).Countable := by
  have hT : ({i : ℕ | ρ i = 0} : Set ℕ).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  refine Set.Countable.mono ?_ (hT.image c)
  intro z hz
  obtain ⟨i, hi⟩ := hz.nonempty
  exact ⟨i, hi.1, hi.2⟩

/-- Every point of the enlarged limsup set either lies in the enlarged limsup set over
positive radii, or belongs to the countable exceptional set above. -/
lemma LSenl'_subset {d : ℝ} (hd0 : 0 < d) (hρ : ∀ i, 0 ≤ ρ i) :
    LSenl' d c ρ ⊆ LSenl d c ρ ∪ {z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite} := by
  intro z hz
  by_cases hfin : ({i : ℕ | 0 < ρ i ∧ |z - c i| ≤ (ρ i) ^ d} : Set ℕ).Finite
  · right
    have h2 : ({i : ℕ | |z - c i| ≤ (ρ i) ^ d} \
        {i : ℕ | 0 < ρ i ∧ |z - c i| ≤ (ρ i) ^ d}).Infinite := hz.diff hfin
    refine h2.mono ?_
    intro i hi
    simp only [Set.mem_setOf_eq, Set.mem_diff] at hi ⊢
    obtain ⟨hi1, hi2⟩ := hi
    have hρ0 : ρ i = 0 := by
      by_contra h
      exact hi2 ⟨lt_of_le_of_ne (hρ i) (Ne.symm h), hi1⟩
    refine ⟨hρ0, ?_⟩
    have h0 : (ρ i) ^ d = 0 := by rw [hρ0, Real.zero_rpow (ne_of_gt hd0)]
    rw [h0] at hi1
    have : z - c i = 0 := abs_nonpos_iff.mp hi1
    linarith
  · left
    exact hfin

/-- **Transfer of the full measure hypothesis to positive radii.**  If the limsup set of
the enlarged intervals has full `1`-dimensional Hausdorff measure on every subinterval of
`[0,1]` (over all radii), the same holds for the enlarged intervals with positive radius. -/
lemma full_measure_pos {d : ℝ} (hd0 : 0 < d) (hρ : ∀ i, 0 ≤ ρ i)
    (hfull : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ LSenl' d c ρ) = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)) :
    ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ LSenl d c ρ) = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y) := by
  intro x y hx hy
  have hsub := LSenl'_subset c ρ hd0 hρ
  have h1 : Set.Icc x y ∩ LSenl' d c ρ ⊆
      (Set.Icc x y ∩ LSenl d c ρ) ∪ {z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite} := by
    rintro z ⟨hz1, hz2⟩
    rcases hsub hz2 with h | h
    · exact Or.inl ⟨hz1, h⟩
    · exact Or.inr h
  have hnull : MeasureTheory.Measure.hausdorffMeasure 1
      ({z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite}) = 0 := by
    rw [MeasureTheory.hausdorffMeasure_real]
    exact (countable_zero_radius c ρ).measure_zero volume
  have hle : MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩ LSenl d c ρ) := by
    rw [← hfull x y hx hy]
    calc MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩ LSenl' d c ρ)
        ≤ MeasureTheory.Measure.hausdorffMeasure 1 ((Set.Icc x y ∩ LSenl d c ρ) ∪
            {z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite}) := measure_mono h1
      _ ≤ MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩ LSenl d c ρ)
            + MeasureTheory.Measure.hausdorffMeasure 1
              ({z : ℝ | {i : ℕ | ρ i = 0 ∧ c i = z}.Infinite}) := measure_union_le _ _
      _ = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩ LSenl d c ρ) := by rw [hnull, add_zero]
  have hle2 : MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y ∩ LSenl d c ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y) := measure_mono (Set.inter_subset_left)
  exact le_antisymm hle2 hle

end FullMeasure


/-- **Thickening a finite union of intervals.**  The `δ`-neighbourhood of a finite union of
closed intervals is contained in the union of the intervals enlarged by `δ`, so its measure
is at most `∑ 2 (r i + δ)`. -/
lemma measure_thickening_biUnion_Iv_le {c ρ : ℕ → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (s : Finset ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (Metric.thickening δ (⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i)))
      ≤ ENNReal.ofReal (∑ i ∈ s, 2 * (4 * ρ i + δ)) := by
  have hsub : Metric.thickening δ (⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i)) ⊆
      ⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i + δ) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp hx
    simp only [Set.mem_iUnion] at hy ⊢
    obtain ⟨i, his, hyi⟩ := hy
    refine ⟨i, his, ?_⟩
    rw [mem_Iv] at hyi ⊢
    have hdist : dist x y < δ := hxy
    rw [Real.dist_eq] at hdist
    calc |x - c i| = |(x - y) + (y - c i)| := by ring_nf
      _ ≤ |x - y| + |y - c i| := abs_add_le _ _
      _ ≤ δ + 4 * ρ i := by linarith [abs_sub_comm x y]
      _ = 4 * ρ i + δ := by ring
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le s
    (fun i => Iv (c i) (4 * ρ i + δ))) (le_of_eq ?_))
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hρ i; positivity)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hausdorffMeasure_one_Iv _ _ (by have := hρ i; linarith)]

end Work.MassTransferenceAlt
