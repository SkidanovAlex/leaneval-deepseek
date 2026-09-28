import Mathlib
import Submission.Work.HP.HP2.SepGridDefs

namespace Work.HP.HP2

open MeasureTheory

/-- The half-open grid cells `hpGrid h j = [j*h-1, (j+1)*h-1)` for `j < ⌈2/h⌉₊ + 1`
cover the interval `[-1,1]`. -/
lemma hp_grid_cover {h : ℝ} (hh : 0 < h) {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    ∃ j : ℕ, j < ⌈2 / h⌉₊ + 1 ∧ x ∈ hpGrid h j := by
  have hx0 : 0 ≤ x + 1 := by linarith [hx.1]
  have hx2 : x + 1 ≤ 2 := by linarith [hx.2]
  have hd0 : 0 ≤ (x + 1) / h := div_nonneg hx0 hh.le
  refine ⟨⌊(x + 1) / h⌋₊, ?_, ?_⟩
  · have h1 : ((⌊(x + 1) / h⌋₊ : ℕ) : ℝ) ≤ (x + 1) / h := Nat.floor_le hd0
    have h2 : (x + 1) / h ≤ 2 / h := div_le_div_of_nonneg_right hx2 hh.le
    have h3 : ((⌊(x + 1) / h⌋₊ : ℕ) : ℝ) ≤ ((⌈2 / h⌉₊ : ℕ) : ℝ) :=
      le_trans (le_trans h1 h2) (Nat.le_ceil _)
    exact Nat.lt_succ_of_le (Nat.cast_le.mp h3)
  · rw [hpGrid, Set.mem_Ico]
    constructor
    · have h1 : ((⌊(x + 1) / h⌋₊ : ℕ) : ℝ) ≤ (x + 1) / h := Nat.floor_le hd0
      have h2 := mul_le_mul_of_nonneg_right h1 hh.le
      rw [div_mul_cancel₀ _ (ne_of_gt hh)] at h2
      linarith
    · have h1 : (x + 1) / h < ((⌊(x + 1) / h⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 := mul_lt_mul_of_pos_right h1 hh
      rw [div_mul_cancel₀ _ (ne_of_gt hh)] at h2
      linarith

/-- From a finset of natural numbers with at least `2*n` elements one can select `n` elements
whose consecutive selected values differ by at least `2`. -/
lemma finset_gap_two_selection (S : Finset ℕ) (n : ℕ) (hcard : 2 * n ≤ S.card) :
    ∃ j : Fin n → ℕ, (∀ t, j t ∈ S) ∧ ∀ t u : Fin n, t < u → j t + 2 ≤ j u := by
  classical
  have hlt : ∀ t : Fin n, 2 * (t : ℕ) < S.card := by
    intro t
    have := t.isLt
    omega
  let e := S.orderIsoOfFin rfl
  refine ⟨fun t => (e ⟨2 * (t : ℕ), hlt t⟩).val, ?_, ?_⟩
  · intro t
    exact (e ⟨2 * (t : ℕ), hlt t⟩).property
  · intro t u htu
    have h1 : 2 * (t : ℕ) < 2 * (u : ℕ) := by
      have : (t : ℕ) < (u : ℕ) := htu
      omega
    have hmid : 2 * (t : ℕ) + 1 < S.card := by
      have := u.isLt
      omega
    have hi1 : (⟨2 * (t : ℕ), hlt t⟩ : Fin S.card) < ⟨2 * (t : ℕ) + 1, hmid⟩ := by
      simp only [Fin.mk_lt_mk]; omega
    have hi2 : (⟨2 * (t : ℕ) + 1, hmid⟩ : Fin S.card) < ⟨2 * (u : ℕ), hlt u⟩ := by
      simp only [Fin.mk_lt_mk]; omega
    have hm1 : e ⟨2 * (t : ℕ), hlt t⟩ < e ⟨2 * (t : ℕ) + 1, hmid⟩ := e.strictMono hi1
    have hm2 : e ⟨2 * (t : ℕ) + 1, hmid⟩ < e ⟨2 * (u : ℕ), hlt u⟩ := e.strictMono hi2
    have hv1 : (e ⟨2 * (t : ℕ), hlt t⟩).val < (e ⟨2 * (t : ℕ) + 1, hmid⟩).val := hm1
    have hv2 : (e ⟨2 * (t : ℕ) + 1, hmid⟩).val < (e ⟨2 * (u : ℕ), hlt u⟩).val := hm2
    show (e ⟨2 * (t : ℕ), hlt t⟩).val + 2 ≤ (e ⟨2 * (u : ℕ), hlt u⟩).val
    omega

/-- **Pigeonhole bound on the grid.** If `E ⊆ [-1,1]` is measurable with
`(volume E).toReal ≥ 2*n*h` then there is a set `S` of at least `2*n` grid indices, all
smaller than `Nat.ceil (2/h) + 1`, each of whose cells `hpGrid h j` meets `E`. -/
lemma hp_grid_card_bound (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Set.Icc (-1:ℝ) 1)
    (n : ℕ) {h : ℝ} (hh : 0 < h) (hvol : 2 * (n : ℝ) * h ≤ (MeasureTheory.volume E).toReal) :
    ∃ S : Finset ℕ, (∀ j ∈ S, j < ⌈2 / h⌉₊ + 1 ∧ (E ∩ hpGrid h j).Nonempty) ∧
      2 * n ≤ S.card := by
  classical
  set S : Finset ℕ := (Finset.range (⌈2 / h⌉₊ + 1)).filter
    (fun j => (E ∩ hpGrid h j).Nonempty) with hS
  have hSprop : ∀ j, j ∈ S ↔ j < ⌈2 / h⌉₊ + 1 ∧ (E ∩ hpGrid h j).Nonempty := by
    intro j
    rw [hS]
    simp [Finset.mem_filter, Finset.mem_range]
  refine ⟨S, fun j hj => (hSprop j).mp hj, ?_⟩
  have hEeq : E = ⋃ j ∈ Finset.range (⌈2 / h⌉₊ + 1), (E ∩ hpGrid h j) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, hjN, hxj⟩ := hp_grid_cover hh (hsub hx)
      exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjN, hx, hxj⟩
    · intro x hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨j, _, hx'⟩ := hx
      exact hx'.1
  have hmeas : ∀ j, MeasurableSet (E ∩ hpGrid h j) := fun j => hE.inter (measurableSet_hpGrid h j)
  have hdisj : (↑(Finset.range (⌈2 / h⌉₊ + 1)) : Set ℕ).PairwiseDisjoint
      (fun j => E ∩ hpGrid h j) := by
    intro a _ b _ hab
    exact (hpGrid_disjoint hh.le hab).mono Set.inter_subset_right Set.inter_subset_right
  have hvol_eq : volume E = ∑ j ∈ Finset.range (⌈2 / h⌉₊ + 1), volume (E ∩ hpGrid h j) := by
    conv_lhs => rw [hEeq]
    rw [measure_biUnion_finset hdisj (fun j _ => hmeas j)]
  have hne : ∀ j ∈ Finset.range (⌈2 / h⌉₊ + 1), volume (E ∩ hpGrid h j) ≠ ⊤ := by
    intro j _
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
      calc volume (E ∩ hpGrid h j) ≤ volume (hpGrid h j) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal h := volume_hpGrid h j)
  have htoReal : (volume E).toReal
      = ∑ j ∈ Finset.range (⌈2 / h⌉₊ + 1), (volume (E ∩ hpGrid h j)).toReal := by
    rw [hvol_eq, ENNReal.toReal_sum hne]
  have hterm : ∀ j ∈ S, (volume (E ∩ hpGrid h j)).toReal ≤ h := by
    intro j _
    calc (volume (E ∩ hpGrid h j)).toReal ≤ (ENNReal.ofReal h).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (by
            calc volume (E ∩ hpGrid h j) ≤ volume (hpGrid h j) := measure_mono Set.inter_subset_right
              _ = ENNReal.ofReal h := volume_hpGrid h j)
      _ = h := ENNReal.toReal_ofReal hh.le
  have hsum_eq : ∑ j ∈ Finset.range (⌈2 / h⌉₊ + 1), (volume (E ∩ hpGrid h j)).toReal
      = ∑ j ∈ S, (volume (E ∩ hpGrid h j)).toReal := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      exact Finset.mem_range.mpr ((hSprop x).mp hx).1
    · intro x hx hxS
      have hnot : ¬ (E ∩ hpGrid h x).Nonempty := fun hne' =>
        hxS ((hSprop x).mpr ⟨Finset.mem_range.mp hx, hne'⟩)
      have hempty : E ∩ hpGrid h x = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
      simp [hempty]
  have hbound : (volume E).toReal ≤ (S.card : ℝ) * h := by
    calc (volume E).toReal
        = ∑ j ∈ Finset.range (⌈2 / h⌉₊ + 1), (volume (E ∩ hpGrid h j)).toReal := htoReal
      _ = ∑ j ∈ S, (volume (E ∩ hpGrid h j)).toReal := hsum_eq
      _ ≤ ∑ j ∈ S, h := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * h := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : 2 * (n : ℝ) ≤ (S.card : ℝ) :=
    le_of_mul_le_mul_right (le_trans hvol hbound) hh
  exact_mod_cast h2

/-- **Separation from measure.** A measurable set `E ⊆ [-1,1]` of measure at least `2*n*h`
contains `n` points that are pairwise at distance at least `h`.

Route (uniform grid + pigeonhole).  Let `N := ⌈2/h⌉₊ + 1 > 2/h` and, for `j : ℕ`, let
`I j := Set.Ico ((j:ℝ)*h - 1) (((j:ℝ)+1)*h - 1)`.  The `I j` are pairwise disjoint and
`[-1,1] ⊆ ⋃_{j<N} I j`.  So `E = ⋃_{j<N} (E ∩ I j)` is a disjoint union of measurable sets, whence
`(volume E).toReal = ∑_{j<N} (volume (E ∩ I j)).toReal`.  Only `k := #{j < N | (E ∩ I j).Nonempty}`
of the terms are nonzero, each of volume at most `h` (the volume of `I j`), so
`(volume E).toReal ≤ k * h`; combined with the hypothesis this gives `k ≥ 2n` (both sides natural
numbers).  List the elements of `{j < N | (E ∩ I j).Nonempty}` in increasing order via
`Finset.orderEmbOfFin` as `j : Fin k → ℕ`, choose `x t ∈ E ∩ I (j (2*t))` for `t : Fin n`
(well posed since `2*(n-1) < k`), and observe that for `t < t'` the order embedding gives
`j (2*t') ≥ j (2*t) + 2`, so the two points lie in intervals with at least one interval of length
`h` strictly between them; hence `h ≤ |x t - x t'|`. -/
theorem measure_separated_points {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Set.Icc (-1:ℝ) 1)
    (n : ℕ) {h : ℝ} (hh : 0 < h) (hvol : 2 * (n : ℝ) * h ≤ (MeasureTheory.volume E).toReal) :
    ∃ x : Fin n → ℝ, (∀ i, x i ∈ E) ∧ ∀ i j, i ≠ j → h ≤ |x i - x j| := by
  classical
  obtain ⟨S, hSbound, hScard⟩ := hp_grid_card_bound E hE hsub n hh hvol
  obtain ⟨j, hjS, hjgap⟩ := finset_gap_two_selection S n hScard
  have hne : ∀ t : Fin n, (E ∩ hpGrid h (j t)).Nonempty := fun t => (hSbound (j t) (hjS t)).2
  choose x hx using hne
  refine ⟨x, fun t => (hx t).1, fun i k hik => ?_⟩
  rcases lt_or_gt_of_ne hik with h | h
  · exact hpGrid_abs_sub_ge hh.le (hjgap i k h) (hx i).2 (hx k).2
  · rw [abs_sub_comm]
    exact hpGrid_abs_sub_ge hh.le (hjgap k i h) (hx k).2 (hx i).2

end Work.HP.HP2
