import Mathlib
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid

/-!
# The centred maximal function is controlled by two dyadic maximal functions

The classical two-grid transfer: the centred Hardy--Littlewood maximal function over *all*
intervals is dominated, pointwise, by `4` times the sum of the dyadic maximal function of the
standard grid and of the grid shifted by half a cell,

`hlMax φ x ≤ 4 · (dyMax φ x + dyMaxShift (1/2) φ x)`.

The proof is the standard one.  Let `I = [a,b] ∋ x` have length `L = b - a` and let `H = 2^N`
satisfy `H ≤ 4L` and `2L < H`.  The interval `[x-L, x+L]` containing `I` is too short to meet
three dyadic cells of length `H`, so `I` meets the cell `C` of `x` and at most one of its two
neighbours; if the right (resp. left) neighbour is met, then `x` lies in the right (resp. left)
half-shifted cell `C'` of the same level and `I ⊆ C ∪ C'` (this is where the shift by half a cell
enters).  Each of the two cells has length `H`, so

`∫_I φ ≤ H·dyMax φ x + H·dyMaxShift (1/2) φ x`,

and dividing by `L` with `H ≤ 4L` gives the claim.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-! ### Rewriting the dyadic cells as half-open intervals with an explicit left endpoint -/

private lemma dyCell_eq_Ico (N K : ℤ) :
    dyCell N K =
      Set.Ico ((K : ℝ) * (2 : ℝ) ^ N) (((K : ℝ) * (2 : ℝ) ^ N) + (2 : ℝ) ^ N) := by
  unfold dyCell
  rw [add_mul, one_mul]

private lemma dyCellShift_half_eq_Ico (N K : ℤ) :
    dyCellShift (1 / 2) N K =
      Set.Ico (((K : ℝ) * (2 : ℝ) ^ N) + (1 / 2) * (2 : ℝ) ^ N)
        (((K : ℝ) * (2 : ℝ) ^ N) + (3 / 2) * (2 : ℝ) ^ N) := by
  unfold dyCellShift
  have h1 : (((K : ℝ) + 1 / 2) + 1) = ((K : ℝ) + 3 / 2) := by ring
  rw [h1, add_mul, add_mul]

private lemma dyCellShift_half_eq_Ico_prev (N K : ℤ) :
    dyCellShift (1 / 2) N (K - 1) =
      Set.Ico (((K : ℝ) * (2 : ℝ) ^ N) - (1 / 2) * (2 : ℝ) ^ N)
        (((K : ℝ) * (2 : ℝ) ^ N) + (1 / 2) * (2 : ℝ) ^ N) := by
  unfold dyCellShift
  have h1 : ((((K - 1 : ℤ)) : ℝ) + 1 / 2 + 1) = (((K - 1 : ℤ)) : ℝ) + 3 / 2 := by ring
  rw [h1, add_mul, add_mul]
  congr 1
  · rw [show (((K - 1 : ℤ)) : ℝ) = (K : ℝ) - 1 by push_cast; ring, sub_mul, one_mul]
    ring
  · rw [show (((K - 1 : ℤ)) : ℝ) = (K : ℝ) - 1 by push_cast; ring, sub_mul, one_mul]
    ring

/-! ### The two elementary interval covers -/

private lemma Ico_union_right (p H : ℝ) (hH : 0 < H) :
    Set.Ico p (p + (3 / 2) * H) ⊆
      Set.Ico p (p + H) ∪ Set.Ico (p + (1 / 2) * H) (p + (3 / 2) * H) := by
  intro y hy
  rcases lt_or_ge y (p + H) with h | h
  · exact Or.inl ⟨hy.1, h⟩
  · exact Or.inr ⟨by linarith, hy.2⟩

private lemma Ico_union_left (p H : ℝ) (hH : 0 < H) :
    Set.Ico (p - (1 / 2) * H) (p + H) ⊆
      Set.Ico p (p + H) ∪ Set.Ico (p - (1 / 2) * H) (p + (1 / 2) * H) := by
  intro y hy
  rcases lt_or_ge y p with h | h
  · exact Or.inr ⟨hy.1, by linarith⟩
  · exact Or.inl ⟨h, hy.2⟩

/-! ### The geometric covering lemmas

`p` is the left endpoint of the dyadic cell of level `N` containing `x` and `H = 2^N` its length.
The hypotheses below are exactly `2 (b - a) < H` together with the position of `b` relative to the
right endpoint `p + H` of the cell of `x`. -/

/-- If `[a,b]` reaches the right endpoint of the cell of `x`, then `x` lies in the half-shifted
cell `[p + H/2, p + 3H/2)` and `[a,b]` is covered by the cell of `x` and that shifted cell. -/
private lemma cover_right {p H a b x : ℝ} (hH : 0 < H)
    (hx : x ∈ Set.Ico p (p + H)) (hax : a ≤ x) (hxb : x ≤ b)
    (hpb : p + H ≤ b) (h2L : 2 * (b - a) < H) :
    x ∈ Set.Ico (p + (1 / 2) * H) (p + (3 / 2) * H) ∧
      Set.Icc a b ⊆ Set.Ico p (p + H) ∪ Set.Ico (p + (1 / 2) * H) (p + (3 / 2) * H) := by
  have hx1 : p ≤ x := hx.1
  have hx2 : x < p + H := hx.2
  have ha_gt : p + (1 / 2) * H < a := by linarith
  have hb_lt : b < p + (3 / 2) * H := by linarith
  constructor
  · exact ⟨by linarith, by linarith⟩
  · intro y hy
    have hy' : y ∈ Set.Ico p (p + (3 / 2) * H) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact Ico_union_right p H hH hy'

/-- If `[a,b]` keeps strictly to the left of the right endpoint of the cell of `x` but starts
strictly to the left of that cell, then `x` lies in the half-shifted cell `[p - H/2, p + H/2)` of
the previous index and `[a,b]` is covered by the cell of `x` and that shifted cell. -/
private lemma cover_left {p H a b x : ℝ} (hH : 0 < H)
    (hx : x ∈ Set.Ico p (p + H)) (hax : a ≤ x) (hxb : x ≤ b)
    (hbl : b < p + H) (hal : a < p) (h2L : 2 * (b - a) < H) :
    x ∈ Set.Ico (p - (1 / 2) * H) (p + (1 / 2) * H) ∧
      Set.Icc a b ⊆ Set.Ico p (p + H) ∪ Set.Ico (p - (1 / 2) * H) (p + (1 / 2) * H) := by
  have hx1 : p ≤ x := hx.1
  have hx2 : x < p + H := hx.2
  have hb_lt : b < p + (1 / 2) * H := by linarith
  have ha_gt : p - (1 / 2) * H < a := by linarith
  constructor
  · exact ⟨by linarith, by linarith⟩
  · intro y hy
    have hy' : y ∈ Set.Ico (p - (1 / 2) * H) (p + H) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact Ico_union_left p H hH hy'

/-! ### The two integral bounds attached to a cell -/

private lemma lintegral_dyCell_le (φ : ℝ → ℝ≥0∞) (x : ℝ) (N K : ℤ) (hx : x ∈ dyCell N K) :
    ∫⁻ y in dyCell N K, φ y ≤ ENNReal.ofReal ((2 : ℝ) ^ N) * dyMax φ x := by
  have h1 : ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) * ∫⁻ y in dyCell N K, φ y ≤ dyMax φ x := by
    unfold dyMax
    exact le_iSup_of_le N (le_iSup_of_le K (le_iSup_of_le hx le_rfl))
  calc ∫⁻ y in dyCell N K, φ y
      = ENNReal.ofReal ((2 : ℝ) ^ N) *
          (ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) * ∫⁻ y in dyCell N K, φ y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (zpow_two_pos N)),
          mul_inv_cancel₀ (ne_of_gt (zpow_two_pos N)), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ N) * dyMax φ x := mul_le_mul_right h1 _

private lemma lintegral_dyCellShift_le (φ : ℝ → ℝ≥0∞) (x : ℝ) (N K : ℤ)
    (hx : x ∈ dyCellShift (1 / 2) N K) :
    ∫⁻ y in dyCellShift (1 / 2) N K, φ y ≤
      ENNReal.ofReal ((2 : ℝ) ^ N) * dyMaxShift (1 / 2) φ x := by
  have h1 : ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) * ∫⁻ y in dyCellShift (1 / 2) N K, φ y
      ≤ dyMaxShift (1 / 2) φ x := by
    unfold dyMaxShift
    exact le_iSup_of_le N (le_iSup_of_le K (le_iSup_of_le hx le_rfl))
  calc ∫⁻ y in dyCellShift (1 / 2) N K, φ y
      = ENNReal.ofReal ((2 : ℝ) ^ N) *
          (ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) * ∫⁻ y in dyCellShift (1 / 2) N K, φ y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (zpow_two_pos N)),
          mul_inv_cancel₀ (ne_of_gt (zpow_two_pos N)), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ N) * dyMaxShift (1 / 2) φ x := mul_le_mul_right h1 _

/-- The final weight computation: a factor `H` in front of a maximal bound costs only `H/L ≤ 4`. -/
private lemma weight_le (L H : ℝ) (hL : 0 < L) (hH : H ≤ 4 * L) (X : ℝ≥0∞) :
    ENNReal.ofReal L⁻¹ * (ENNReal.ofReal H * X) ≤ 4 * X := by
  have hHL : L⁻¹ * H ≤ 4 := by
    rw [inv_mul_le_iff₀ hL]
    linarith
  calc ENNReal.ofReal L⁻¹ * (ENNReal.ofReal H * X)
      = ENNReal.ofReal (L⁻¹ * H) * X := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le)]
    _ ≤ ENNReal.ofReal (4 : ℝ) * X := mul_le_mul_left (ENNReal.ofReal_le_ofReal hHL) X
    _ = 4 * X := by rw [ENNReal.ofReal_ofNat]

/-! ### The theorem -/

theorem hlMaxTwoDyadic (φ : ℝ → ENNReal) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax φ x ≤ 4 * (Work.BourgainPlan.Maximal.dyMax φ x + Work.BourgainPlan.Maximal.dyMaxShift (1 / 2) φ x) := by
  rw [hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  obtain ⟨hax, hxb⟩ := hab
  rcases eq_or_lt_of_le (sub_nonneg.mpr (hax.trans hxb)) with hL0 | hLpos
  · -- degenerate interval
    rw [← hL0, inv_zero, ENNReal.ofReal_zero, zero_mul]
    simp
  obtain ⟨N, hNle, hNlt⟩ := exists_level (b - a) hLpos
  have hHpos : 0 < (2 : ℝ) ^ N := zpow_two_pos N
  have h2L : 2 * (b - a) < (2 : ℝ) ^ N := by
    have h2 : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    linarith
  have h4L : (2 : ℝ) ^ N ≤ 4 * (b - a) := hNle
  have hxIco : x ∈ Set.Ico ((dyIdx N x : ℝ) * (2 : ℝ) ^ N)
      (((dyIdx N x : ℝ) * (2 : ℝ) ^ N) + (2 : ℝ) ^ N) := by
    rw [← dyCell_eq_Ico]
    exact dyIdx_mem N x
  -- once the covering by the cell of `x` and a shifted cell is known, the estimate is formal
  have key : ∀ (k : ℤ), x ∈ dyCellShift (1 / 2) N k →
      Set.Icc a b ⊆ dyCell N (dyIdx N x) ∪ dyCellShift (1 / 2) N k →
      ∫⁻ y in Set.Icc a b, φ y ≤
        ENNReal.ofReal ((2 : ℝ) ^ N) * (dyMax φ x + dyMaxShift (1 / 2) φ x) := by
    intro k hxk hsub
    have h1 : ∫⁻ y in Set.Icc a b, φ y ≤
        (∫⁻ y in dyCell N (dyIdx N x), φ y) + (∫⁻ y in dyCellShift (1 / 2) N k, φ y) :=
      le_trans (lintegral_mono_set hsub) (lintegral_union_le (μ := volume) φ _ _)
    have h2 : ∫⁻ y in dyCell N (dyIdx N x), φ y ≤ ENNReal.ofReal ((2 : ℝ) ^ N) * dyMax φ x :=
      lintegral_dyCell_le φ x N (dyIdx N x) (dyIdx_mem N x)
    have h3 : ∫⁻ y in dyCellShift (1 / 2) N k, φ y ≤
        ENNReal.ofReal ((2 : ℝ) ^ N) * dyMaxShift (1 / 2) φ x :=
      lintegral_dyCellShift_le φ x N k hxk
    rw [mul_add]
    exact le_trans h1 (add_le_add h2 h3)
  rcases lt_or_ge b (((dyIdx N x : ℝ) + 1) * (2 : ℝ) ^ N) with hbl | hbr
  · -- `b` is strictly inside the cell of `x`
    rw [add_mul, one_mul] at hbl
    rcases lt_or_ge a ((dyIdx N x : ℝ) * (2 : ℝ) ^ N) with hal | har
    · -- `a` is strictly outside the cell of `x` on the left: the previous shifted cell
      obtain ⟨hxc', hsub⟩ := cover_left hHpos hxIco hax hxb hbl hal h2L
      have hxk : x ∈ dyCellShift (1 / 2) N (dyIdx N x - 1) := by
        rw [dyCellShift_half_eq_Ico_prev]
        exact hxc'
      have hsub' : Set.Icc a b ⊆
          dyCell N (dyIdx N x) ∪ dyCellShift (1 / 2) N (dyIdx N x - 1) := by
        rw [dyCell_eq_Ico, dyCellShift_half_eq_Ico_prev]
        exact hsub
      exact le_trans (mul_le_mul_right (key (dyIdx N x - 1) hxk hsub') _)
        (weight_le (b - a) ((2 : ℝ) ^ N) hLpos h4L _)
    · -- `[a,b]` lies inside the cell of `x`: only the dyadic term is needed
      have hsub : Set.Icc a b ⊆ dyCell N (dyIdx N x) := by
        rw [dyCell_eq_Ico]
        intro y hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hle : ∫⁻ y in Set.Icc a b, φ y ≤ ENNReal.ofReal ((2 : ℝ) ^ N) * dyMax φ x :=
        le_trans (lintegral_mono_set hsub)
          (lintegral_dyCell_le φ x N (dyIdx N x) (dyIdx_mem N x))
      have hle' : ∫⁻ y in Set.Icc a b, φ y ≤
          ENNReal.ofReal ((2 : ℝ) ^ N) * (dyMax φ x + dyMaxShift (1 / 2) φ x) := by
        rw [mul_add]
        exact le_trans hle (le_add_right le_rfl)
      exact le_trans (mul_le_mul_right hle' _)
        (weight_le (b - a) ((2 : ℝ) ^ N) hLpos h4L _)
  · -- `b` reaches the right endpoint of the cell of `x`: the right half-shifted cell
    have hbr' : (dyIdx N x : ℝ) * (2 : ℝ) ^ N + (2 : ℝ) ^ N ≤ b := by
      rw [add_mul, one_mul] at hbr
      exact hbr
    obtain ⟨hxc', hsub⟩ := cover_right hHpos hxIco hax hxb hbr' h2L
    have hxk : x ∈ dyCellShift (1 / 2) N (dyIdx N x) := by
      rw [dyCellShift_half_eq_Ico]
      exact hxc'
    have hsub' : Set.Icc a b ⊆ dyCell N (dyIdx N x) ∪ dyCellShift (1 / 2) N (dyIdx N x) := by
      rw [dyCell_eq_Ico, dyCellShift_half_eq_Ico]
      exact hsub
    exact le_trans (mul_le_mul_right (key (dyIdx N x) hxk hsub') _)
      (weight_le (b - a) ((2 : ℝ) ^ N) hLpos h4L _)

end Work.BourgainPlan.Maximal
