import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Commons.Analysis.Summation

/-! ## `xm`: the affine denominators `3m + j` -/

/-- `3m + j` as a real number. -/
def xm (m j : ℕ) : ℝ := (((3 * m + j : ℕ) : ℝ))

lemma xm_eq (m j : ℕ) : xm m j = 3 * (m : ℝ) + (j : ℝ) := by
  unfold xm
  norm_num

lemma xm_succ (m j : ℕ) : xm (m + 1) j = xm m (j + 3) := by
  unfold xm
  congr 1
  omega

lemma xm_pos {m j : ℕ} (hj : 0 < j) : 0 < xm m j := by
  unfold xm
  exact_mod_cast (by omega : 0 < 3 * m + j)

lemma xm_ne_zero {m j : ℕ} (hj : 0 < j) : xm m j ≠ 0 := ne_of_gt (xm_pos hj)

lemma xm_ge_succ {m j : ℕ} (hj : 1 ≤ j) : (m : ℝ) + 1 ≤ xm m j := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  rw [xm_eq]
  nlinarith

/-! ## The summand `Tm` -/

def Tm (m : ℕ) : ℝ :=
  ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) / 2) * 9 *
    ((3 / ((((3 * m + 2 : ℕ) : ℝ) * ((3 * m + 5 : ℕ) : ℝ)))) ^ 2
      - 3 * (3 / ((((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 6 : ℕ) : ℝ)))) ^ 2
      + 3 * (3 / ((((3 * m + 4 : ℕ) : ℝ) * ((3 * m + 7 : ℕ) : ℝ)))) ^ 2
      - (3 / ((((3 * m + 5 : ℕ) : ℝ) * ((3 * m + 8 : ℕ) : ℝ)))) ^ 2))

/-- Pointwise partial-fraction decomposition of the summand. -/
lemma tm_decomp (m : ℕ) :
    Tm m =
      (2 : ℝ) / (xm m 2)^2 - 3 / (xm m 4)^2 + 6 / (xm m 7)^2 - 5 / (xm m 8)^2
        + (7/6 : ℝ) * (1 / xm m 2 - 1 / xm m 5)
        - (1/6 : ℝ) * (1 / xm m 5 - 1 / xm m 8)
        - (9/2 : ℝ) * (1 / xm m 3 - 1 / xm m 6)
        + (7/2 : ℝ) * (1 / xm m 4 - 1 / xm m 7) := by
  have h2 : (3 * (m : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (3 * (m : ℝ) + 3) ≠ 0 := by positivity
  have h4 : (3 * (m : ℝ) + 4) ≠ 0 := by positivity
  have h5 : (3 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h6 : (3 * (m : ℝ) + 6) ≠ 0 := by positivity
  have h7 : (3 * (m : ℝ) + 7) ≠ 0 := by positivity
  have h8 : (3 * (m : ℝ) + 8) ≠ 0 := by positivity
  unfold Tm
  norm_num
  simp_rw [xm_eq]
  field_simp [h2, h3, h4, h5, h6, h7, h8]
  ring

/-- The summand is positive. -/
lemma tm_pos (m : ℕ) : 0 < Tm m := by
  -- reduced numerator/denominator (both positive for m ≥ 0)
  let N : ℝ :=
    12 * (3645 * (m : ℝ) ^ 6 + 36450 * (m : ℝ) ^ 5 + 148473 * (m : ℝ) ^ 4
      + 314820 * (m : ℝ) ^ 3 + 365724 * (m : ℝ) ^ 2 + 220080 * (m : ℝ) + 53408)
  let D : ℝ :=
    ((m : ℝ) + 1) * ((m : ℝ) + 2) * (3 * (m : ℝ) + 2) ^ 2 * (3 * (m : ℝ) + 4) ^ 2
      * (3 * (m : ℝ) + 5) * (3 * (m : ℝ) + 7) ^ 2 * (3 * (m : ℝ) + 8) ^ 2
  have h2 : (3 * (m : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (3 * (m : ℝ) + 3) ≠ 0 := by positivity
  have h4 : (3 * (m : ℝ) + 4) ≠ 0 := by positivity
  have h5 : (3 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h6 : (3 * (m : ℝ) + 6) ≠ 0 := by positivity
  have h7 : (3 * (m : ℝ) + 7) ≠ 0 := by positivity
  have h8 : (3 * (m : ℝ) + 8) ≠ 0 := by positivity
  have hDne : D ≠ 0 := by
    dsimp [D]
    positivity
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hmul : Tm m * D = N := by
    dsimp [N, D]
    unfold Tm
    norm_num
    field_simp [h2, h3, h4, h5, h6, h7, h8]
    ring
  have h : Tm m = N / D := by
    rw [eq_div_iff hDne]
    exact hmul
  rw [h]
  exact div_pos hNpos hDpos

/-! ## The two basic ζ-type series `f1`, `f2` -/

def f1 (k : ℕ) : ℝ := (1 : ℝ) / (xm k 1)^2
def f2 (k : ℕ) : ℝ := (1 : ℝ) / (xm k 2)^2

def A : ℝ := ∑' k : ℕ, f1 k
def B : ℝ := ∑' k : ℕ, f2 k

def Asum (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, f1 k
def Bsum (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, f2 k

/-! ## Summability of `f1`, `f2` and their partial sums -/

lemma summable_one_div_succ_sq : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)^2) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (k := 1)).mpr hs
  exact hshift.congr (by intro k; congr 1; norm_num)

lemma f1_le_succ_sq (k : ℕ) : f1 k ≤ (1 : ℝ) / ((k : ℝ) + 1)^2 := by
  have hx : 0 < xm k 1 := xm_pos (by norm_num)
  have hn : 0 < (k : ℝ) + 1 := by positivity
  have hge : (k : ℝ) + 1 ≤ xm k 1 := xm_ge_succ (j := 1) (by norm_num)
  have hge2 : ((k : ℝ) + 1)^2 ≤ (xm k 1)^2 := by nlinarith
  unfold f1
  exact one_div_le_one_div_of_le (by positivity : 0 < ((k : ℝ) + 1)^2) hge2

lemma f2_le_succ_sq (k : ℕ) : f2 k ≤ (1 : ℝ) / ((k : ℝ) + 1)^2 := by
  have hx : 0 < xm k 2 := xm_pos (by norm_num)
  have hn : 0 < (k : ℝ) + 1 := by positivity
  have hge : (k : ℝ) + 1 ≤ xm k 2 := xm_ge_succ (j := 2) (by norm_num)
  have hge2 : ((k : ℝ) + 1)^2 ≤ (xm k 2)^2 := by nlinarith
  unfold f2
  exact one_div_le_one_div_of_le (by positivity : 0 < ((k : ℝ) + 1)^2) hge2

lemma summable_f1 : Summable f1 := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_one_div_succ_sq
  · unfold f1
    positivity
  · exact f1_le_succ_sq k

lemma summable_f2 : Summable f2 := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_one_div_succ_sq
  · unfold f2
    positivity
  · exact f2_le_succ_sq k

lemma hasSum_f1 : HasSum f1 A := by
  simpa [A] using summable_f1.hasSum

lemma hasSum_f2 : HasSum f2 B := by
  simpa [B] using summable_f2.hasSum

lemma tendsto_Asum : Tendsto Asum atTop (𝓝 A) := by
  change Tendsto (fun n : ℕ => Asum n) atTop (𝓝 A)
  simpa [Asum] using hasSum_f1.tendsto_sum_nat

lemma tendsto_Bsum : Tendsto Bsum atTop (𝓝 B) := by
  change Tendsto (fun n : ℕ => Bsum n) atTop (𝓝 B)
  simpa [Bsum] using hasSum_f2.tendsto_sum_nat

/-! ## Limits of the `1/xm` tails -/

lemma tendsto_inv_xm_zero {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun m : ℕ => (1 : ℝ) / xm m j) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
  · exact tendsto_const_nhds
  · have hbig : Tendsto (fun m : ℕ => ((m : ℝ) + 1 : ℝ)) atTop atTop := by
      apply tendsto_atTop_mono' (l := atTop) (f₁ := fun m : ℕ => (m : ℝ))
        (f₂ := fun m : ℕ => (m : ℝ) + 1)
      · filter_upwards with m
        linarith
      · exact tendsto_natCast_atTop_atTop (R := ℝ)
    simpa using hbig.inv_tendsto_atTop
  · intro m
    unfold xm
    positivity
  · intro m
    have hmm : 0 < (m : ℝ) + 1 := by positivity
    have hx : 0 < xm m j := xm_pos (by omega)
    have hd : (m : ℝ) + 1 ≤ xm m j := xm_ge_succ hj
    have hle : (1 : ℝ) / xm m j ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hmm hd
    simpa using hle


/-! ## Finite range sums of the summand: induction route -/

/-- Partial sums of the inverse-square pieces. -/
def Ss (j M : ℕ) : ℝ := ∑ m ∈ Finset.range M, (1 : ℝ) / (xm m j) ^ 2

/-- Closed form for `∑_{m < M} Tm m` (via the pointwise decomposition). -/
def RangeExpr (M : ℕ) : ℝ :=
  2 * Ss 2 M - 3 * Ss 4 M + 6 * Ss 7 M - 5 * Ss 8 M
    + (7/6 : ℝ) * (1 / xm 0 2 - 1 / xm M 2)
    - (1/6 : ℝ) * (1 / xm 1 2 - 1 / xm (M + 1) 2)
    - (9/2 : ℝ) * (1 / xm 0 3 - 1 / xm M 3)
    + (7/2 : ℝ) * (1 / xm 0 4 - 1 / xm M 4)

lemma xm_succ5 (m : ℕ) : xm (m + 1) 2 = xm m 5 := by
  have h : (3 * (m + 1) + 2 : ℕ) = 3 * m + 5 := by omega
  unfold xm
  rw [h]

lemma xm_succ8 (m : ℕ) : xm (m + 2) 2 = xm m 8 := by
  have h : (3 * (m + 2) + 2 : ℕ) = 3 * m + 8 := by omega
  unfold xm
  rw [h]

lemma xm_succ6 (m : ℕ) : xm (m + 1) 3 = xm m 6 := by
  have h : (3 * (m + 1) + 3 : ℕ) = 3 * m + 6 := by omega
  unfold xm
  rw [h]

lemma xm_succ7 (m : ℕ) : xm (m + 1) 4 = xm m 7 := by
  have h : (3 * (m + 1) + 4 : ℕ) = 3 * m + 7 := by omega
  unfold xm
  rw [h]

lemma ss_succ (j M : ℕ) : Ss j (M + 1) = Ss j M + (1 : ℝ) / (xm M j) ^ 2 := by
  unfold Ss
  rw [Finset.sum_range_succ]

lemma range_tm_step (M : ℕ) : RangeExpr (M + 1) - RangeExpr M = Tm M := by
  have h : (1 : ℝ) / xm (M + 1) 2 = 1 / xm M 5 := by rw [xm_succ5]
  have h8 : (1 : ℝ) / xm (M + 2) 2 = 1 / xm M 8 := by rw [xm_succ8]
  have h6 : (1 : ℝ) / xm (M + 1) 3 = 1 / xm M 6 := by rw [xm_succ6]
  have h7 : (1 : ℝ) / xm (M + 1) 4 = 1 / xm M 7 := by rw [xm_succ7]
  unfold RangeExpr
  rw [ss_succ 2 M, ss_succ 4 M, ss_succ 7 M, ss_succ 8 M]
  rw [h, h8, h6, h7]
  -- difference of the two range expressions telescopes: rewrite into tm_decomp RHS
  rw [tm_decomp]
  ring

lemma range_tm_eq (M : ℕ) : (∑ m ∈ Finset.range M, Tm m) = RangeExpr M := by
  induction M with
  | zero =>
      simp [RangeExpr]
      -- all Ss j 0 = 0
      simp [Ss]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      -- goal: RangeExpr M + Tm M = RangeExpr (M+1)
      have hstep := range_tm_step M
      linarith

/-! ## Reindexing identities between `Ss` and `Asum`/`Bsum` -/

lemma xm_succ1_four (m : ℕ) : xm (m + 1) 1 = xm m 4 := by
  have h : (3 * (m + 1) + 1 : ℕ) = 3 * m + 4 := by omega
  unfold xm
  rw [h]

lemma xm_succ1_seven (m : ℕ) : xm (m + 2) 1 = xm m 7 := by
  have h : (3 * (m + 2) + 1 : ℕ) = 3 * m + 7 := by omega
  unfold xm
  rw [h]

lemma xm_succ2_eight (m : ℕ) : xm (m + 2) 2 = xm m 8 := by
  have h : (3 * (m + 2) + 2 : ℕ) = 3 * m + 8 := by omega
  unfold xm
  rw [h]

lemma ss2_eq (M : ℕ) : Ss 2 M = Bsum M := by
  unfold Ss Bsum
  rfl

lemma ss4_eq (M : ℕ) : Ss 4 M = Asum (M + 1) - 1 := by
  calc
    Ss 4 M = ∑ m ∈ Finset.range M, f1 (m + 1) := by
      unfold Ss
      apply Finset.sum_congr rfl
      intro m hm
      unfold f1
      rw [xm_succ1_four]
    _ = Asum (M + 1) - 1 := by
      have hsum := Finset.sum_range_succ' f1 M
      have hM : (∑ k ∈ Finset.range M, f1 (k + 1)) =
          (∑ k ∈ Finset.range (M + 1), f1 k) - f1 0 := by
        rw [hsum]
        ring
      have h0 : f1 0 = 1 := by norm_num [f1, xm]
      unfold Asum
      calc
        (∑ k ∈ Finset.range M, f1 (k + 1)) = (∑ k ∈ Finset.range (M + 1), f1 k) - f1 0 := hM
        _ = (∑ k ∈ Finset.range (M + 1), f1 k) - 1 := by rw [h0]

lemma ss7_eq (M : ℕ) : Ss 7 M = Asum (M + 2) - 1 - 1 / 16 := by
  calc
    Ss 7 M = ∑ m ∈ Finset.range M, f1 (m + 2) := by
      unfold Ss
      apply Finset.sum_congr rfl
      intro m hm
      unfold f1
      rw [xm_succ1_seven]
    _ = Asum (M + 2) - 1 - 1 / 16 := by
      have hsum1 := Finset.sum_range_succ' f1 (M + 1)
      have hsum2 := Finset.sum_range_succ' (fun k : ℕ => f1 (k + 1)) M
      have h0 : f1 0 = 1 := by norm_num [f1, xm]
      have h1 : f1 1 = 1 / 16 := by norm_num [f1, xm]
      unfold Asum
      calc
        (∑ m ∈ Finset.range M, f1 (m + 2))
            = (∑ k ∈ Finset.range (M + 2), f1 k) - f1 0 - f1 1 := by
              -- from hsum1 & hsum2
              rw [hsum1]
              rw [hsum2]
              ring
        _ = (∑ k ∈ Finset.range (M + 2), f1 k) - 1 - 1 / 16 := by rw [h0, h1]

lemma ss8_eq (M : ℕ) : Ss 8 M = Bsum (M + 2) - 1 / 4 - 1 / 25 := by
  calc
    Ss 8 M = ∑ m ∈ Finset.range M, f2 (m + 2) := by
      unfold Ss
      apply Finset.sum_congr rfl
      intro m hm
      unfold f2
      rw [xm_succ2_eight]
    _ = Bsum (M + 2) - 1 / 4 - 1 / 25 := by
      have hsum1 := Finset.sum_range_succ' f2 (M + 1)
      have hsum2 := Finset.sum_range_succ' (fun k : ℕ => f2 (k + 1)) M
      have h0 : f2 0 = 1 / 4 := by norm_num [f2, xm]
      have h1 : f2 1 = 1 / 25 := by norm_num [f2, xm]
      unfold Bsum
      calc
        (∑ m ∈ Finset.range M, f2 (m + 2))
            = (∑ k ∈ Finset.range (M + 2), f2 k) - f2 0 - f2 1 := by
              rw [hsum1]
              rw [hsum2]
              ring
        _ = (∑ k ∈ Finset.range (M + 2), f2 k) - 1 / 4 - 1 / 25 := by rw [h0, h1]

/-! ## The limit of the range expression -/

/-- Tails that vanish at infinity. -/
def E (M : ℕ) : ℝ :=
  2 * (Bsum M - B) - 3 * (Asum (M + 1) - A) + 6 * (Asum (M + 2) - A)
    - 5 * (Bsum (M + 2) - B)
    - (7/6 : ℝ) * (1 / xm M 2) + (1/6 : ℝ) * (1 / xm (M + 1) 2)
    + (9/2 : ℝ) * (1 / xm M 3) - (7/2 : ℝ) * (1 / xm M 4)

lemma range_expr_eq (M : ℕ) : RangeExpr M = (3 * A - 3 * B - 2) + E M := by
  unfold RangeExpr E
  rw [ss2_eq M, ss4_eq M, ss7_eq M, ss8_eq M]
  norm_num [xm]
  ring

lemma tendsto_tail2 : Tendsto (fun M : ℕ => (1 : ℝ) / xm (M + 1) 2) atTop (𝓝 0) := by
  have hrew : (fun M : ℕ => (1 : ℝ) / xm (M + 1) 2) = (fun M : ℕ => (1 : ℝ) / xm M 5) := by
    funext M
    rw [xm_succ5]
  rw [hrew]
  exact tendsto_inv_xm_zero (j := 5) (by norm_num)

lemma tendsto_E : Tendsto E atTop (𝓝 0) := by
  have hA1 : Tendsto (fun M : ℕ => Asum (M + 1) - A) atTop (𝓝 0) := by
    have h := tendsto_Asum.comp (tendsto_add_atTop_nat 1)
    simpa using h.sub_const A
  have hA2 : Tendsto (fun M : ℕ => Asum (M + 2) - A) atTop (𝓝 0) := by
    have h := tendsto_Asum.comp (tendsto_add_atTop_nat 2)
    simpa using h.sub_const A
  have hB0 : Tendsto (fun M : ℕ => Bsum M - B) atTop (𝓝 0) := by
    simpa using tendsto_Bsum.sub_const B
  have hB2 : Tendsto (fun M : ℕ => Bsum (M + 2) - B) atTop (𝓝 0) := by
    have h := tendsto_Bsum.comp (tendsto_add_atTop_nat 2)
    simpa using h.sub_const B
  have ht2 : Tendsto (fun M : ℕ => (1 : ℝ) / xm M 2) atTop (𝓝 0) :=
    tendsto_inv_xm_zero (j := 2) (by norm_num)
  have ht3 : Tendsto (fun M : ℕ => (1 : ℝ) / xm M 3) atTop (𝓝 0) :=
    tendsto_inv_xm_zero (j := 3) (by norm_num)
  have ht4 : Tendsto (fun M : ℕ => (1 : ℝ) / xm M 4) atTop (𝓝 0) :=
    tendsto_inv_xm_zero (j := 4) (by norm_num)
  have ht5 : Tendsto (fun M : ℕ => (1 : ℝ) / xm (M + 1) 2) atTop (𝓝 0) := tendsto_tail2
  have h1 : Tendsto (fun M : ℕ => 2 * (Bsum M - B)) atTop (𝓝 0) := by
    simpa using hB0.const_mul 2
  have h2 : Tendsto (fun M : ℕ => (-3) * (Asum (M + 1) - A)) atTop (𝓝 0) := by
    simpa using hA1.const_mul (-3)
  have h3 : Tendsto (fun M : ℕ => 6 * (Asum (M + 2) - A)) atTop (𝓝 0) := by
    simpa using hA2.const_mul 6
  have h4 : Tendsto (fun M : ℕ => (-5) * (Bsum (M + 2) - B)) atTop (𝓝 0) := by
    simpa using hB2.const_mul (-5)
  have h5 : Tendsto (fun M : ℕ => (-(7/6 : ℝ)) * (1 / xm M 2)) atTop (𝓝 0) := by
    simpa using ht2.const_mul (-(7/6 : ℝ))
  have h6 : Tendsto (fun M : ℕ => (1/6 : ℝ) * (1 / xm (M + 1) 2)) atTop (𝓝 0) := by
    simpa using ht5.const_mul (1/6 : ℝ)
  have h7 : Tendsto (fun M : ℕ => (9/2 : ℝ) * (1 / xm M 3)) atTop (𝓝 0) := by
    simpa using ht3.const_mul (9/2 : ℝ)
  have h8 : Tendsto (fun M : ℕ => (-(7/2 : ℝ)) * (1 / xm M 4)) atTop (𝓝 0) := by
    simpa using ht4.const_mul (-(7/2 : ℝ))
  have hEq : (fun M : ℕ => E M) =
      (fun M : ℕ =>
        2 * (Bsum M - B) + (-3) * (Asum (M + 1) - A) + 6 * (Asum (M + 2) - A)
          + (-5) * (Bsum (M + 2) - B) + (-(7/6 : ℝ)) * (1 / xm M 2)
          + (1/6 : ℝ) * (1 / xm (M + 1) 2) + (9/2 : ℝ) * (1 / xm M 3)
          + (-(7/2 : ℝ)) * (1 / xm M 4)) := by
    funext M
    unfold E
    ring
  change Tendsto (fun M : ℕ => E M) atTop (𝓝 0)
  rw [hEq]
  have h12 := h1.add h2
  have h123 := h12.add h3
  have h1234 := h123.add h4
  have h12345 := h1234.add h5
  have h123456 := h12345.add h6
  have h1234567 := h123456.add h7
  have hAll := h1234567.add h8
  simpa using hAll

lemma tendsto_partial_Tm :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, Tm m) atTop (𝓝 (3 * A - 3 * B - 2)) := by
  have h : (fun M : ℕ => ∑ m ∈ Finset.range M, Tm m) = (fun M : ℕ => (3 * A - 3 * B - 2) + E M) := by
    funext M
    rw [range_tm_eq M, range_expr_eq M]
  rw [h]
  have hc : Tendsto (fun _ : ℕ => (3 * A - 3 * B - 2 : ℝ)) atTop (𝓝 (3 * A - 3 * B - 2)) :=
    tendsto_const_nhds
  simpa using hc.add tendsto_E

lemma hasSum_Tm : HasSum Tm (3 * A - 3 * B - 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i : ℕ => le_of_lt (tm_pos i))]
  exact tendsto_partial_Tm

/-! ## The right-hand side series -/

def Rk (k : ℕ) : ℝ := (1 : ℝ) / (xm k 1)^2 - (1 : ℝ) / (xm k 2)^2

lemma hasSum_Rk : HasSum Rk (A - B) := by
  have hsub := hasSum_f1.sub hasSum_f2
  rw [show Rk = fun b : ℕ => f1 b - f2 b by funext b; rfl]
  exact hsub

lemma tsum_Rk : (∑' k : ℕ, Rk k) = A - B := hasSum_Rk.tsum_eq

/-! ## Final assembly -/

theorem sum_cintegralOne_core :
    (∑' m : ℕ,
        (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) / 2) * 9 *
          ((3 / ((((3 * m + 2 : ℕ) : ℝ) * ((3 * m + 5 : ℕ) : ℝ)))) ^ 2
            - 3 * (3 / ((((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 6 : ℕ) : ℝ)))) ^ 2
            + 3 * (3 / ((((3 * m + 4 : ℕ) : ℝ) * ((3 * m + 7 : ℕ) : ℝ)))) ^ 2
            - (3 / ((((3 * m + 5 : ℕ) : ℝ) * ((3 * m + 8 : ℕ) : ℝ)))) ^ 2)) =
      3 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 2 := by
  have hL : (∑' m : ℕ, Tm m) = 3 * A - 3 * B - 2 := hasSum_Tm.tsum_eq
  have hR : (∑' k : ℕ, Rk k) = A - B := tsum_Rk
  have hMain : (∑' m : ℕ, Tm m) = 3 * (∑' k : ℕ, Rk k) - 2 := by
    rw [hL, hR]
    ring
  simpa [Tm, Rk, xm] using hMain

end Commons.Analysis.Summation