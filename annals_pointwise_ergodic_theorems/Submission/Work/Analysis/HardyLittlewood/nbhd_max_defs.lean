import Mathlib
import Submission.Work.Analysis.HardyLittlewood.dyadic_max_defs

/-!
# The "neighbourhood" maximal function on the dyadic grid of `ℤ`

For `φ : ℤ → ℝ≥0∞` and `x : ℤ`, `nbhdMax φ x` is the supremum over all scales `s` of the average
of `φ` over the union of the dyadic block of `x` (standard grid) at scale `s` with its two
neighbouring blocks.

That interval contains `x`, so `nbhdMax φ x ≤ dMaxENN φ x`.  Every dyadic block whose average is
used by one of the shifted dyadic maximal functions `dyadMax ε` is contained in such an interval
(or, for `ε = true`, in one of scale one smaller), whence `dyadMax ε ≤ 3 nbhdMax`.  Finally the
super-level sets of `nbhdMax` are unions of triples of dyadic blocks, which makes them accessible
to the maximal-bad-block (Calderón–Zygmund) argument.
-/

namespace Work.Analysis.HardyLittlewood

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-! ### Dyadic cells of the standard grid -/

/-- The dyadic block of the standard grid at scale `s` containing the point `y`. -/
def dyadCell (s : ℕ) (y : ℤ) : Finset ℤ :=
  Finset.Icc (blk false s y) (blk false s y + (2 : ℤ) ^ s - 1)

/-- The interval consisting of the dyadic block of `x` at scale `s` and its two neighbours. -/
def nbhdIcc (s : ℕ) (x : ℤ) : Finset ℤ :=
  Finset.Icc (blk false s x - (2 : ℤ) ^ s) (blk false s x + 2 * (2 : ℤ) ^ s - 1)

lemma blk_false_eq (s : ℕ) (y : ℤ) : blk false s y = (2 : ℤ) ^ s * (y / (2 : ℤ) ^ s) := by
  unfold blk
  simp

lemma card_dyadCell (s : ℕ) (y : ℤ) : (dyadCell s y).card = 2 ^ s := by
  rw [dyadCell, Int.card_Icc]
  rw [show (blk false s y + (2 : ℤ) ^ s - 1 + 1 - blk false s y) = ((2 ^ s : ℕ) : ℤ) by
    rw [show blk false s y + (2 : ℤ) ^ s - 1 + 1 - blk false s y = (2 : ℤ) ^ s by ring]
    push_cast; ring]
  rw [Int.toNat_natCast]

/-- A finer cell is contained in a coarser one through the same point. -/
lemma dyadCell_subset_self {s S : ℕ} (h : s ≤ S) (y : ℤ) : dyadCell s y ⊆ dyadCell S y := by
  have hps : (0 : ℤ) < (2 : ℤ) ^ s := by positivity
  have hdvd : (2 : ℤ) ^ s ∣ (2 : ℤ) ^ S :=
    ⟨(2 : ℤ) ^ (S - s), by rw [← pow_add]; congr 1; omega⟩
  have hpow : (2 : ℤ) ^ s * (2 : ℤ) ^ (S - s) = (2 : ℤ) ^ S := by
    rw [← pow_add]; congr 1; omega
  have hy1 := Int.mul_ediv_add_emod y ((2 : ℤ) ^ s)
  have hy2 := Int.mul_ediv_add_emod y ((2 : ℤ) ^ S)
  obtain ⟨c, hc⟩ : ∃ c : ℤ, y % (2 : ℤ) ^ S = (2 : ℤ) ^ s * c + y % (2 : ℤ) ^ s := by
    refine ⟨(y % (2 : ℤ) ^ S) / (2 : ℤ) ^ s, ?_⟩
    have hh := Int.mul_ediv_add_emod (y % (2 : ℤ) ^ S) ((2 : ℤ) ^ s)
    rw [Int.emod_emod_of_dvd y hdvd] at hh
    linarith
  have hc0 : 0 ≤ c := by
    have h1 : y % (2 : ℤ) ^ s < (2 : ℤ) ^ s := Int.emod_lt_of_pos _ hps
    have h2 : 0 ≤ y % (2 : ℤ) ^ S :=
      Int.emod_nonneg y (ne_of_gt (by positivity : (0 : ℤ) < (2 : ℤ) ^ S))
    have h3 : -(2 : ℤ) ^ s < (2 : ℤ) ^ s * c := by linarith
    by_contra hc
    push_neg at hc
    have hc' : c ≤ -1 := by omega
    have h4 : (2 : ℤ) ^ s * c ≤ (2 : ℤ) ^ s * (-1) := mul_le_mul_of_nonneg_left hc' hps.le
    linarith
  have hc1 : c ≤ (2 : ℤ) ^ (S - s) - 1 := by
    have hlt : y % (2 : ℤ) ^ S < (2 : ℤ) ^ S := Int.emod_lt_of_pos _ (by positivity)
    have hnn : 0 ≤ y % (2 : ℤ) ^ s := Int.emod_nonneg y (ne_of_gt hps)
    have hm : (2 : ℤ) ^ s * c < (2 : ℤ) ^ s * (2 : ℤ) ^ (S - s) := by nlinarith [hpow]
    have := lt_of_mul_lt_mul_left hm hps.le
    omega
  intro z hz
  rw [dyadCell, Finset.mem_Icc] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  have e1 : blk false s y = y - y % (2 : ℤ) ^ s := by rw [blk_false_eq]; linarith
  have e2 : blk false S y = y - y % (2 : ℤ) ^ S := by rw [blk_false_eq]; linarith
  rw [e1] at hz1 hz2
  rw [e2, hc]
  have ht : 0 ≤ (2 : ℤ) ^ s * c := mul_nonneg hps.le hc0
  have ht2 : (2 : ℤ) ^ s * c ≤ (2 : ℤ) ^ S - (2 : ℤ) ^ s := by
    have h4 := mul_le_mul_of_nonneg_left hc1 hps.le
    nlinarith [h4, hpow]
  constructor <;> linarith

/-! ### Elementary facts about the maximal function -/

/-- The average of `φ` over a dyadic cell. -/
def cellAvg (s : ℕ) (y : ℤ) (φ : ℤ → ENNReal) : ENNReal :=
  (((2 : ℕ) ^ s : ℝ≥0∞))⁻¹ * ∑ z ∈ dyadCell s y, φ z

/-- The "neighbour maximal": the average of `φ` over the `nbhdIcc`-interval, supremised over
the scale. -/
def nbhdMax (φ : ℤ → ENNReal) (x : ℤ) : ENNReal :=
  ⨆ s : ℕ, (((3 * 2 ^ s : ℕ)) : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y

lemma two_pow_ne_zero (s : ℕ) : ((2 : ℝ≥0∞) ^ s) ≠ 0 := by simp
lemma two_pow_ne_top (s : ℕ) : ((2 : ℝ≥0∞) ^ s) ≠ ⊤ := by simp

/-- `N⁻¹ * (N * t) = t` for a finite nonzero `N`. -/
lemma inv_mul_mul_self (N : ENNReal) (hN0 : N ≠ 0) (hN : N ≠ ⊤) (t : ENNReal) :
    N⁻¹ * (N * t) = t := by
  calc N⁻¹ * (N * t) = (N⁻¹ * N) * t := (mul_assoc _ _ _).symm
    _ = 1 * t := by rw [ENNReal.inv_mul_cancel hN0 hN]
    _ = t := one_mul t

/-- `N⁻¹ ≤ 3 * (3 * N)⁻¹`. -/
lemma inv_le_three_mul_inv (N : ENNReal) (hN0 : N ≠ 0) (hN : N ≠ ⊤) :
    N⁻¹ ≤ 3 * ((3 * N)⁻¹) := by
  have h3 : ((3 : ENNReal) * N)⁻¹ = (3 : ENNReal)⁻¹ * N⁻¹ :=
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
  rw [h3, show 3 * ((3 : ENNReal)⁻¹ * N⁻¹) = (3 * (3 : ENNReal)⁻¹) * N⁻¹ by ring,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The cardinality of `nbhdIcc`. -/
lemma card_nbhdIcc (s : ℕ) (x : ℤ) : (nbhdIcc s x).card = 3 * 2 ^ s := by
  rw [nbhdIcc, Int.card_Icc]
  rw [show (blk false s x + 2 * (2 : ℤ) ^ s - 1 + 1 - (blk false s x - (2 : ℤ) ^ s))
      = ((3 * 2 ^ s : ℕ) : ℤ) by push_cast; ring]
  rw [Int.toNat_natCast]

lemma card_nbhdIcc_cast (s : ℕ) (x : ℤ) :
    (((nbhdIcc s x).card : ℕ) : ENNReal) = (((3 * 2 ^ s : ℕ)) : ENNReal) := by
  rw [card_nbhdIcc]

/-- The `nbhdIcc`-interval contains the point. -/
lemma mem_nbhdIcc_self (s : ℕ) (x : ℤ) : x ∈ nbhdIcc s x := by
  have hs : (1 : ℤ) ≤ (2 : ℤ) ^ s := by
    have := Nat.one_le_two_pow (n := s); exact_mod_cast this
  have h1 := blk_le_self false s x
  have h2 := self_lt_blk_add false s x
  rw [nbhdIcc, Finset.mem_Icc]
  constructor <;> nlinarith

/-- Every dyadic cell of the triple is contained in the `nbhdIcc`-interval. -/
lemma cell_subset_nbhdIcc (s : ℕ) (x : ℤ) {j : ℤ}
    (hj : blk false s j = blk false s x ∨ blk false s j = blk false s x - (2 : ℤ) ^ s
      ∨ blk false s j = blk false s x + (2 : ℤ) ^ s) :
    dyadCell s j ⊆ nbhdIcc s x := by
  intro z hz
  rw [dyadCell, Finset.mem_Icc] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [nbhdIcc, Finset.mem_Icc]
  have hs : (1 : ℤ) ≤ (2 : ℤ) ^ s := by
    have := Nat.one_le_two_pow (n := s); exact_mod_cast this
  rcases hj with h | h | h <;> rw [h] at hz1 hz2 <;> constructor <;> nlinarith

/-- Each cell average over a point of the triple is at most `3 * nbhdMax`. -/
lemma cellAvg_le_three_nbhdMax (φ : ℤ → ENNReal) (x : ℤ) (s : ℕ) {j : ℤ}
    (hj : blk false s j = blk false s x ∨ blk false s j = blk false s x - (2 : ℤ) ^ s
      ∨ blk false s j = blk false s x + (2 : ℤ) ^ s) :
    cellAvg s j φ ≤ 3 * nbhdMax φ x := by
  have hsum : ∑ z ∈ dyadCell s j, φ z ≤ ∑ y ∈ nbhdIcc s x, φ y :=
    Finset.sum_le_sum_of_subset_of_nonneg (cell_subset_nbhdIcc s x hj) (fun _ _ _ => bot_le)
  have hN0 := two_pow_ne_zero s
  have hNt := two_pow_ne_top s
  have hcast : ((3 * 2 ^ s : ℕ) : ℝ≥0∞) = 3 * ((2 : ℝ≥0∞) ^ s) := by push_cast; ring
  have hineq : ((2 : ℝ≥0∞) ^ s)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y
      ≤ 3 * ((((3 * 2 ^ s : ℕ)) : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y) := by
    rw [hcast]
    calc ((2 : ℝ≥0∞) ^ s)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y
        ≤ (3 * ((3 * ((2 : ℝ≥0∞) ^ s))⁻¹)) * ∑ y ∈ nbhdIcc s x, φ y :=
          mul_le_mul_of_nonneg_right (inv_le_three_mul_inv _ hN0 hNt) bot_le
      _ = 3 * ((3 * ((2 : ℝ≥0∞) ^ s))⁻¹ * ∑ y ∈ nbhdIcc s x, φ y) := by ring
  calc cellAvg s j φ
      = ((2 : ℝ≥0∞) ^ s)⁻¹ * ∑ z ∈ dyadCell s j, φ z := rfl
    _ ≤ ((2 : ℝ≥0∞) ^ s)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y :=
        mul_le_mul_of_nonneg_left hsum bot_le
    _ ≤ 3 * ((((3 * 2 ^ s : ℕ)) : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc s x, φ y) := hineq
    _ ≤ 3 * nbhdMax φ x := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        unfold nbhdMax
        exact le_iSup (fun s : ℕ => ((((3 * 2 ^ s : ℕ)) : ℝ≥0∞))⁻¹ *
          ∑ y ∈ nbhdIcc s x, φ y) s

/-- `cellAvg` is monotone. -/
lemma cellAvg_mono {φ ψ : ℤ → ENNReal} (h : ∀ y, φ y ≤ ψ y) (s : ℕ) (k : ℤ) :
    cellAvg s k φ ≤ cellAvg s k ψ := by
  unfold cellAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => h y) bot_le

/-- `cellAvg` of a constant function. -/
lemma cellAvg_const (s : ℕ) (k : ℤ) (a : ENNReal) :
    cellAvg s k (fun _ : ℤ => a) = a := by
  have hcast : ((2 ^ s : ℕ) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ s) := by push_cast; ring
  unfold cellAvg
  calc ((2 : ℝ≥0∞) ^ s)⁻¹ * ∑ z ∈ dyadCell s k, (fun _ : ℤ => a) z
      = ((2 : ℝ≥0∞) ^ s)⁻¹ * (((2 ^ s : ℕ) : ℝ≥0∞) * a) := by
        rw [Finset.sum_const, card_dyadCell s k, nsmul_eq_mul]
    _ = ((2 : ℝ≥0∞) ^ s)⁻¹ * (((2 : ℝ≥0∞) ^ s) * a) := by rw [hcast]
    _ = a := inv_mul_mul_self _ (two_pow_ne_zero s) (two_pow_ne_top s) a

/-- `nbhdMax` is monotone. -/
lemma nbhdMax_mono {φ ψ : ℤ → ENNReal} (h : ∀ y, φ y ≤ ψ y) (x : ℤ) :
    nbhdMax φ x ≤ nbhdMax ψ x := by
  unfold nbhdMax
  refine iSup_le fun s => ?_
  refine le_iSup_of_le s ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => h y) bot_le

/-- `nbhdMax` is subadditive. -/
lemma nbhdMax_add_le (φ ψ : ℤ → ENNReal) (x : ℤ) :
    nbhdMax (φ + ψ) x ≤ nbhdMax φ x + nbhdMax ψ x := by
  unfold nbhdMax
  refine iSup_le fun s => ?_
  rw [show ∑ y ∈ nbhdIcc s x, (φ + ψ) y
        = ∑ y ∈ nbhdIcc s x, φ y + ∑ y ∈ nbhdIcc s x, ψ y from by
      simp only [Pi.add_apply, Finset.sum_add_distrib], mul_add]
  exact add_le_add
    (le_iSup (fun t : ℕ => ((((3 * 2 ^ t : ℕ)) : ℝ≥0∞))⁻¹ * ∑ y ∈ nbhdIcc t x, φ y) s)
    (le_iSup (fun t : ℕ => ((((3 * 2 ^ t : ℕ)) : ℝ≥0∞))⁻¹ * ∑ y ∈ nbhdIcc t x, ψ y) s)

/-- `nbhdMax` of a constant is at most that constant. -/
lemma nbhdMax_const_le (a : ENNReal) (x : ℤ) : nbhdMax (fun _ : ℤ => a) x ≤ a := by
  unfold nbhdMax
  refine iSup_le fun s => ?_
  rw [Finset.sum_const, card_nbhdIcc s x, nsmul_eq_mul]
  exact (inv_mul_mul_self (((3 * 2 ^ s : ℕ)) : ℝ≥0∞) (by simp)
    (ENNReal.natCast_ne_top _) a).le

/-- The value of `φ` at a point is at most `3 * nbhdMax φ` there. -/
lemma le_three_nbhdMax_self (φ : ℤ → ENNReal) (x : ℤ) : φ x ≤ 3 * nbhdMax φ x := by
  have hmem : x ∈ nbhdIcc 0 x := mem_nbhdIcc_self 0 x
  have hsum : φ x ≤ ∑ y ∈ nbhdIcc 0 x, φ y :=
    Finset.single_le_sum (fun _ _ => bot_le) hmem
  have h1 : (3 : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc 0 x, φ y ≤ nbhdMax φ x := by
    have := le_iSup (fun s : ℕ => ((((3 * 2 ^ s : ℕ)) : ℝ≥0∞))⁻¹ *
      ∑ y ∈ nbhdIcc s x, φ y) 0
    rw [show (((3 * 2 ^ 0 : ℕ)) : ℝ≥0∞)⁻¹ = (3 : ℝ≥0∞)⁻¹ by norm_num] at this
    exact this
  calc φ x ≤ ∑ y ∈ nbhdIcc 0 x, φ y := hsum
    _ = 3 * ((3 : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc 0 x, φ y) := by
        rw [show 3 * ((3 : ℝ≥0∞)⁻¹ * ∑ y ∈ nbhdIcc 0 x, φ y)
            = (3 * (3 : ℝ≥0∞)⁻¹) * ∑ y ∈ nbhdIcc 0 x, φ y by ring,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 3 * nbhdMax φ x := mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- `dMaxENN` written as an iterated supremum. -/
lemma dMaxENN_eq_iSup (w : ℤ → ENNReal) (x : ℤ) :
    dMaxENN w x = ⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
      ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, w k := by
  rw [dMaxENN, iSup_subtype, iSup_prod]

/-- The neighbour maximal function is dominated by the interval maximal function. -/
lemma nbhdMax_le_dMaxENN (φ : ℤ → ENNReal) (x : ℤ) : nbhdMax φ x ≤ dMaxENN φ x := by
  unfold nbhdMax
  refine iSup_le fun s => ?_
  have hmem : blk false s x - (2 : ℤ) ^ s ≤ x
      ∧ x ≤ blk false s x + 2 * (2 : ℤ) ^ s - 1 := by
    have h1 := blk_le_self false s x
    have h2 := self_lt_blk_add false s x
    constructor <;> nlinarith
  have hcard : ((blk false s x + 2 * (2 : ℤ) ^ s - 1
      - (blk false s x - (2 : ℤ) ^ s) + 1).toNat : ℝ≥0∞) = (((3 * 2 ^ s : ℕ)) : ℝ≥0∞) := by
    have h1 : blk false s x + 2 * (2 : ℤ) ^ s - 1 - (blk false s x - (2 : ℤ) ^ s) + 1
        = ((3 * 2 ^ s : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
  calc ((((3 * 2 ^ s : ℕ)) : ℝ≥0∞))⁻¹ * ∑ y ∈ nbhdIcc s x, φ y
      = ((blk false s x + 2 * (2 : ℤ) ^ s - 1
          - (blk false s x - (2 : ℤ) ^ s) + 1).toNat : ℝ≥0∞)⁻¹
          * ∑ y ∈ nbhdIcc s x, φ y := by rw [hcard]
    _ ≤ dMaxENN φ x :=
        le_dMaxENN_of_interval φ x (a := blk false s x - (2 : ℤ) ^ s)
          (b := blk false s x + 2 * (2 : ℤ) ^ s - 1) hmem

/-- The block of the shifted grid `true` at scale `m ≥ 1` lies in the `nbhdIcc`-interval of the
point at scale `m - 1`. -/
lemma blk_true_subset_nbhdIcc {m : ℕ} (hm : 1 ≤ m) (x : ℤ) :
    Finset.Icc (blk true m x) (blk true m x + (2 : ℤ) ^ m - 1) ⊆ nbhdIcc (m - 1) x := by
  set D : ℤ := (2 : ℤ) ^ (m - 1) with hDef
  have hD : 0 < D := by rw [hDef]; positivity
  have hpow : (2 : ℤ) ^ m = 2 * D := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ, hDef]; ring
  have hb : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := hpow
  set q : ℤ := (x - D) / (2 : ℤ) ^ m with hq
  set r : ℤ := (x - D) % (2 : ℤ) ^ m with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ (by positivity)
  have hrt : r < (2 : ℤ) ^ m := by rw [hr]; exact Int.emod_lt_of_pos _ (by positivity)
  have hxD : x = D + (2 : ℤ) ^ m * q + r := by
    have h := Int.mul_ediv_add_emod (x - D) ((2 : ℤ) ^ m)
    rw [← hr, ← hq] at h
    linarith
  have hblk : blk true m x = D * (2 * q + 1) := by
    have hform : blk true m x = 2 ^ (m - 1) + 2 ^ m * ((x - 2 ^ (m - 1)) / 2 ^ m) := by
      unfold blk; rw [if_pos rfl]
    rw [hform, ← hDef, hq.symm, hpow]
    show D + 2 * D * q = D * (2 * q + 1)
    ring
  have hxblk : blk false (m - 1) x = D * (x / D) := by
    rw [blk_false_eq, hDef]
  -- x / D ∈ {2q + 1, 2q + 2}
  have hk : x / D = 2 * q + 1 + r / D := by
    conv_lhs => rw [hxD]
    rw [show D + (2 : ℤ) ^ m * q + r = r + D * (2 * q + 1) by rw [hpow]; ring]
    rw [Int.add_mul_ediv_left r (2 * q + 1) (ne_of_gt hD)]
    ring
  have hrdiv : r / D = 0 ∨ r / D = 1 := by
    rcases lt_or_ge r D with h | h
    · left; exact Int.ediv_eq_zero_of_lt hr0 h
    · right
      have h3 : r / D = ((r - D) + D * 1) / D := by ring_nf
      rw [h3, Int.add_mul_ediv_left (r - D) 1 (ne_of_gt hD)]
      have h4 : (r - D) / D = 0 := Int.ediv_eq_zero_of_lt (by linarith) (by linarith)
      rw [h4]; ring
  intro y hy
  rw [Finset.mem_Icc] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [nbhdIcc, Finset.mem_Icc]
  rw [hxblk]
  rw [hblk] at hy1 hy2
  have hq' : x / D = 2 * q + 1 ∨ x / D = 2 * q + 2 := by
    rcases hrdiv with h | h
    · exact Or.inl (by rw [hk, h]; ring)
    · exact Or.inr (by rw [hk, h]; ring)
  rcases hq' with hq' | hq' <;> rw [hq'] <;> constructor <;> nlinarith [hD]

/-! ### The scalar `ℓʳ` bounds -/

/-- **Scalar `ℓʳ` bound for the interval maximal function**. -/
lemma dMaxENN_lintegral_rpow_le {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℤ → ENNReal, (∀ k, u k ≠ ⊤) →
      ∫⁻ x : ℤ, (dMaxENN u x) ^ r ∂(Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℤ, u x ^ r ∂(Measure.count : Measure ℤ) := by
  obtain ⟨C, hC, hb⟩ := Commons.Analysis.HardyLittlewood.discrete_maximal_lp hr
  refine ⟨C, hC, fun u hu => ?_⟩
  set U : ℤ → ℝ := fun k => (u k).toReal with hU
  have hnorm : ∀ k, ‖U k‖ₑ = u k := by
    intro k
    simp only [Real.enorm_eq_ofReal_abs, hU]
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hu k)]
  have hfun : ∀ x, dMaxENN u x
      = ⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
          ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖U k‖ₑ := by
    intro x
    rw [dMaxENN_eq_iSup]
    apply iSup_congr; intro a
    apply iSup_congr; intro b
    apply iSup_congr; intro hab
    congr 1
    exact Finset.sum_congr rfl fun k _ => (hnorm k).symm
  calc ∫⁻ x : ℤ, (dMaxENN u x) ^ r ∂(Measure.count : Measure ℤ)
      = ∫⁻ x : ℤ, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
          ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖U k‖ₑ) ^ r
          ∂(Measure.count : Measure ℤ) := by
        apply lintegral_congr; intro x; rw [hfun x]
    _ ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℤ, ‖U x‖ₑ ^ r ∂(Measure.count : Measure ℤ) :=
        hb U
    _ = ENNReal.ofReal (C ^ r) * ∫⁻ x : ℤ, u x ^ r ∂(Measure.count : Measure ℤ) := by
        congr 1
        apply lintegral_congr; intro x
        rw [hnorm x]

/-- The neighbour maximal function satisfies the scalar `ℓʳ` bound for `r > 1`. -/
lemma nbhdMax_lintegral_rpow_le {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : ℤ → ENNReal, (∀ k, φ k ≠ ⊤) →
      ∫⁻ x : ℤ, (nbhdMax φ x) ^ r ∂(Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℤ, φ x ^ r ∂(Measure.count : Measure ℤ) := by
  obtain ⟨C, hC, h⟩ := dMaxENN_lintegral_rpow_le hr
  refine ⟨3 * C, by positivity, fun φ hφ => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (lt_trans zero_lt_one hr)
  calc ∫⁻ x : ℤ, (nbhdMax φ x) ^ r ∂(Measure.count : Measure ℤ)
      ≤ ∫⁻ x : ℤ, (3 * dMaxENN φ x) ^ r ∂(Measure.count : Measure ℤ) := by
        refine lintegral_mono fun x => ?_
        refine ENNReal.rpow_le_rpow ?_ hr0
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
        calc nbhdMax φ x ≤ dMaxENN φ x := nbhdMax_le_dMaxENN φ x
          _ ≤ ENNReal.ofReal 3 * dMaxENN φ x := le_mul_of_one_le_left' (by norm_num)
    _ = ENNReal.ofReal (3 ^ r) * ∫⁻ x : ℤ, (dMaxENN φ x) ^ r ∂(Measure.count : Measure ℤ) := by
        rw [show (fun x : ℤ => (3 * dMaxENN φ x) ^ r)
            = fun x : ℤ => (ENNReal.ofReal (3 : ℝ)) ^ r * (dMaxENN φ x) ^ r by
          funext x
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
            ENNReal.mul_rpow_of_nonneg _ _ hr0]]
        rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 3) hr0]
        exact lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ ENNReal.ofReal (3 ^ r) * (ENNReal.ofReal (C ^ r)
          * ∫⁻ x : ℤ, φ x ^ r ∂(Measure.count : Measure ℤ)) :=
        mul_le_mul_of_nonneg_left (h φ hφ) bot_le
    _ = ENNReal.ofReal ((3 * C) ^ r) * ∫⁻ x : ℤ, φ x ^ r ∂(Measure.count : Measure ℤ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 ^ r),
          ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hC.le]

end

end Work.Analysis.HardyLittlewood
