import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.card_shell_boxZ_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.far_tail_le` — the far tail of the box-mode lattice sum

For `ℓ ≥ 1` and `0 ≤ R`, the sum of `exp(-(ℓ‖m‖ - 2R)²/4)` over the *far* lattice points
`m ∈ ℤ³ \ {0}` with `ℓ‖m‖ ≥ 2R + √6` is bounded by `1000 (1+R)³`.

Strategy (the one of `Work.BoseRowsFS.sum_exp_div_norm_sq_le`): bound every finite
partial sum, group the lattice points into the max-norm shells `{maxNat = k}`
(at most `26 k²` points, `Work.BoseRowsFS.card_shell_boxZ_le`), and sum the majorant.
On the far set the exponent is

`ℓ‖m‖ - 2R = √6 + ℓ(‖m‖ - T)`,  `T := (2R + √6)/ℓ`,

so `exp(-(ℓ‖m‖-2R)²/4) ≤ e^{-3/2} · exp(-(‖m‖-T)²/4)`, and on the shell `maxNat m = k`
the right-hand side is at most `e^{-3/2} · exp(-(max 0 (k-T))²/4)`.  Splitting the shells
at `K = ⌈T⌉` (below: the majorant is at most `1`; above: geometric) reduces everything to
the two numerical bounds `∑_j e^{-j²/4} ≤ 3` and `∑_j j²e^{-j²/4} ≤ 8`, and to the
arithmetic endgame `(26/12)K³ + 39K² + 104 ≤ 1000(1+R)³` for `0 ≤ K ≤ 3.45(1+R)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-! ## 1. Numerical bounds for `Real.exp` -/

/-- `exp (-3/2) ≤ 1/4`. -/
private lemma exp_neg_three_halves_le : Real.exp (-(3 / 2 : ℝ)) ≤ 1 / 4 := by
  have h1 : (1 : ℝ) + 1 / 2 ≤ Real.exp (1 / 2) := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  have h4 : (4 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    rw [h3]
    nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_pos 1]
  rw [Real.exp_neg]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h4

/-- `exp (-1) ≤ 1/2`. -/
private lemma exp_neg_one_le_half : Real.exp (-(1 : ℝ)) ≤ 1 / 2 :=
  le_of_lt Real.exp_neg_one_lt_half

/-- `exp (-9/4) ≤ 1/8`. -/
private lemma exp_neg_nine_quarters_le : Real.exp (-(9 / 4 : ℝ)) ≤ 1 / 8 := by
  have h1 : (2.7182818283 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 2
  have h2 : (1 : ℝ) + 1 / 4 ≤ Real.exp (1 / 4) := by
    have h := Real.add_one_le_exp (1 / 4 : ℝ)
    linarith
  have h3 : Real.exp (9 / 4 : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have h4 : (8 : ℝ) ≤ Real.exp (9 / 4 : ℝ) := by
    rw [h3]
    nlinarith [Real.exp_pos (1 / 4 : ℝ)]
  rw [Real.exp_neg]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h4

/-- `exp (-4) ≤ 1/16`. -/
private lemma exp_neg_four_le : Real.exp (-(4 : ℝ)) ≤ 1 / 16 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have h2 : (16 : ℝ) ≤ Real.exp 4 := by
    have h3 : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul (x := (1 : ℝ)) (n := 4)]
      norm_num
    rw [h3]
    have h4 : (2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    norm_num at h4 ⊢
    exact h4
  rw [Real.exp_neg]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) h2

/-- `3 ≤ exp (5/4)`. -/
private lemma three_le_exp_five_quarters : (3 : ℝ) ≤ Real.exp (5 / 4 : ℝ) := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
  have h2 : (1 : ℝ) + 1 / 4 ≤ Real.exp (1 / 4) := by
    have h := Real.add_one_le_exp (1 / 4 : ℝ)
    linarith
  have h3 : Real.exp (5 / 4 : ℝ) = Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add]
    norm_num
  rw [h3]
  nlinarith [Real.exp_pos (1 / 4 : ℝ)]

/-- `exp y ≤ 1` for `y ≤ 0`. -/
private lemma exp_le_one_of_nonpos {y : ℝ} (hy : y ≤ 0) : Real.exp y ≤ 1 :=
  Real.exp_le_one_iff.mpr hy

/-- `exp y ≤ 1/2` for `y ≤ -1`. -/
private lemma exp_le_half_of_le {y : ℝ} (hy : y ≤ -(1 : ℝ)) : Real.exp y ≤ 1 / 2 :=
  (Real.exp_le_exp.mpr hy).trans exp_neg_one_le_half

/-- `exp y ≤ 1/8` for `y ≤ -9/4`. -/
private lemma exp_le_inv_eight_of_le {y : ℝ} (hy : y ≤ -(9 / 4 : ℝ)) : Real.exp y ≤ 1 / 8 :=
  (Real.exp_le_exp.mpr hy).trans exp_neg_nine_quarters_le

/-- `exp y ≤ 1/16` for `y ≤ -4`. -/
private lemma exp_le_inv_sixteen_of_le {y : ℝ} (hy : y ≤ -(4 : ℝ)) : Real.exp y ≤ 1 / 16 :=
  (Real.exp_le_exp.mpr hy).trans exp_neg_four_le

/-- `exp (-j²/4) ≤ 2^{-j}` for `j ≥ 4`. -/
private lemma exp_neg_sq_div_four_le_inv_pow_two {j : ℕ} (hj : 4 ≤ j) :
    Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ (1 / 2 : ℝ) ^ j := by
  have hx : (2 : ℝ) ≤ Real.exp ((j : ℝ) / 4) := by
    have h := Real.add_one_le_exp ((j : ℝ) / 4)
    have h4 : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hpow : (2 : ℝ) ^ j ≤ Real.exp ((j : ℝ) ^ 2 / 4) := by
    have h1 : Real.exp ((j : ℝ) ^ 2 / 4) = Real.exp ((j : ℝ) / 4) ^ j := by
      rw [← Real.exp_nat_mul (x := (j : ℝ) / 4) (n := j)]
      congr 1
      ring
    rw [h1]
    exact pow_le_pow_left₀ (by norm_num) hx j
  have h5 : ((2 : ℝ) ^ j)⁻¹ = (1 / 2 : ℝ) ^ j := by
    rw [← inv_pow]
    simp [one_div]
  have hkey : -((j : ℝ)) ^ 2 / 4 = -((j : ℝ) ^ 2 / 4) := by ring
  calc Real.exp (-((j : ℝ)) ^ 2 / 4)
      = (Real.exp ((j : ℝ) ^ 2 / 4))⁻¹ := by rw [hkey, Real.exp_neg]
    _ ≤ ((2 : ℝ) ^ j)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hpow
    _ = (1 / 2 : ℝ) ^ j := h5

/-- `exp (-j²/4) ≤ 3^{-j}` for `j ≥ 5`. -/
private lemma exp_neg_sq_div_four_le_inv_pow_three {j : ℕ} (hj : 5 ≤ j) :
    Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ (1 / 3 : ℝ) ^ j := by
  have h5 : (5 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hx : (3 : ℝ) ≤ Real.exp ((j : ℝ) / 4) := by
    have h54 : Real.exp (5 / 4 : ℝ) ≤ Real.exp ((j : ℝ) / 4) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [three_le_exp_five_quarters]
  have hpow : (3 : ℝ) ^ j ≤ Real.exp ((j : ℝ) ^ 2 / 4) := by
    have h1 : Real.exp ((j : ℝ) ^ 2 / 4) = Real.exp ((j : ℝ) / 4) ^ j := by
      rw [← Real.exp_nat_mul (x := (j : ℝ) / 4) (n := j)]
      congr 1
      ring
    rw [h1]
    exact pow_le_pow_left₀ (by norm_num) hx j
  have h6 : ((3 : ℝ) ^ j)⁻¹ = (1 / 3 : ℝ) ^ j := by
    rw [← inv_pow]
    simp [one_div]
  have hkey : -((j : ℝ)) ^ 2 / 4 = -((j : ℝ) ^ 2 / 4) := by ring
  calc Real.exp (-((j : ℝ)) ^ 2 / 4)
      = (Real.exp ((j : ℝ) ^ 2 / 4))⁻¹ := by rw [hkey, Real.exp_neg]
    _ ≤ ((3 : ℝ) ^ j)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hpow
    _ = (1 / 3 : ℝ) ^ j := h6

/-- `exp y ≤ 2^{-j}` for `j ≥ 4` and `y ≤ -j²/4`. -/
private lemma exp_le_inv_pow_two {j : ℕ} (hj : 4 ≤ j) {y : ℝ}
    (hy : y ≤ -((j : ℝ)) ^ 2 / 4) : Real.exp y ≤ (1 / 2 : ℝ) ^ j :=
  (Real.exp_le_exp.mpr hy).trans (exp_neg_sq_div_four_le_inv_pow_two hj)

/-- `exp y ≤ 3^{-j}` for `j ≥ 5` and `y ≤ -j²/4`. -/
private lemma exp_le_inv_pow_three {j : ℕ} (hj : 5 ≤ j) {y : ℝ}
    (hy : y ≤ -((j : ℝ)) ^ 2 / 4) : Real.exp y ≤ (1 / 3 : ℝ) ^ j :=
  (Real.exp_le_exp.mpr hy).trans (exp_neg_sq_div_four_le_inv_pow_three hj)

/-! ## 2. Sums of geometric type -/

/-- A finite geometric sum is bounded by the full geometric series. -/
private lemma sum_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (s : Finset ℕ) :
    ∑ i ∈ s, x ^ i ≤ (1 - x)⁻¹ := by
  have hxnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hsumm : Summable (fun i : ℕ => x ^ i) := summable_geometric_of_norm_lt_one hxnorm
  have h := hsumm.sum_le_tsum s (fun i _ => pow_nonneg hx0 i)
  rwa [tsum_geometric_of_norm_lt_one hxnorm] at h

/-- Reindexing a sum over `{j ∈ s | N ≤ j}` by `j ↦ j - N`. -/
private lemma sum_sub_shift_eq {N : ℕ} (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ (s.filter (fun j => N ≤ j)).image (fun j => j - N), f i
      = ∑ j ∈ s.filter (fun j => N ≤ j), f (j - N) := by
  apply Finset.sum_image
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  simp only at hab
  omega

/-- `(i+5)² ≤ 25·2^i`. -/
private lemma sq_shift_le (i : ℕ) : (((i : ℝ) + 5) ^ 2) ≤ 25 * 2 ^ i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    have hstep : (((n : ℝ) + 6) ^ 2) ≤ (6 / 5 : ℝ) ^ 2 * (((n : ℝ) + 5) ^ 2) := by
      have h : (25 : ℝ) * ((n : ℝ) + 6) ^ 2 ≤ 36 * ((n : ℝ) + 5) ^ 2 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      have h36 : ((6 / 5 : ℝ) ^ 2) = 36 / 25 := by norm_num
      rw [h36]
      linarith
    have h2pos : (0 : ℝ) ≤ 2 ^ n := by positivity
    calc ((((n : ℕ) + 1 : ℕ) : ℝ) + 5) ^ 2 = ((n : ℝ) + 6) ^ 2 := by
          push_cast
          ring
      _ ≤ (6 / 5 : ℝ) ^ 2 * (((n : ℝ) + 5) ^ 2) := hstep
      _ ≤ (6 / 5 : ℝ) ^ 2 * (25 * 2 ^ n) := by
          apply mul_le_mul_of_nonneg_left ih
          norm_num
      _ ≤ 25 * 2 ^ (n + 1) := by
          have hp : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
          rw [hp]
          nlinarith

/-- **`∑_{j ∈ s} e^{-j²/4} ≤ 3`.** -/
private lemma sum_exp_neg_sq_div_four_le (s : Finset ℕ) :
    ∑ j ∈ s, Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ 3 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun j => j < 4)
    (f := fun j => Real.exp (-((j : ℝ)) ^ 2 / 4))
  rw [← hsplit]
  have h1 : ∑ j ∈ s.filter (fun j => j < 4), Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ 21 / 8 := by
    have hsub : ∑ j ∈ s.filter (fun j => j < 4), Real.exp (-((j : ℝ)) ^ 2 / 4)
        ≤ ∑ j ∈ Finset.range 4, Real.exp (-((j : ℝ)) ^ 2 / 4) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_range.mpr hx.2
      · intro i _ _
        positivity
    refine hsub.trans ?_
    have hrange : ∑ j ∈ Finset.range 4, Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ 21 / 8 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      have t0 : Real.exp (-(((((0 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 :=
        exp_le_one_of_nonpos (by norm_num)
      have t1 : Real.exp (-(((((1 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 :=
        exp_le_one_of_nonpos (by norm_num)
      have t2 : Real.exp (-(((((2 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 / 2 :=
        exp_le_half_of_le (by norm_num)
      have t3 : Real.exp (-(((((3 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 / 8 :=
        exp_le_inv_eight_of_le (by norm_num)
      linarith
    exact hrange
  have h2 : ∑ j ∈ s.filter (fun j => ¬ j < 4), Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ 1 / 8 := by
    have hfe : s.filter (fun j => ¬ j < 4) = s.filter (fun j => 4 ≤ j) := by
      apply Finset.filter_congr
      intro j _
      exact not_lt
    rw [hfe]
    have hpt : ∀ j ∈ s.filter (fun j => 4 ≤ j),
        Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ (1 / 2 : ℝ) ^ j := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact exp_le_inv_pow_two hj.2 le_rfl
    refine (Finset.sum_le_sum hpt).trans ?_
    set img := (s.filter (fun j => 4 ≤ j)).image (fun j => j - 4) with himg
    have h1 : ∑ i ∈ img, (1 / 2 : ℝ) ^ (i + 4) = ∑ j ∈ s.filter (fun j => 4 ≤ j), (1 / 2 : ℝ) ^ j := by
      rw [himg, sum_sub_shift_eq]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Nat.sub_add_cancel hj.2]
    rw [← h1]
    have h16 : ∀ i : ℕ, (1 / 2 : ℝ) ^ (i + 4) ≤ (1 / 16) * (1 / 2 : ℝ) ^ i := by
      intro i
      have h : (1 / 2 : ℝ) ^ (i + 4) = (1 / 16) * (1 / 2 : ℝ) ^ i := by
        rw [pow_add]
        norm_num
        ring
      rw [h]
    calc ∑ i ∈ img, (1 / 2 : ℝ) ^ (i + 4)
        ≤ ∑ i ∈ img, (1 / 16) * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum (fun i _ => h16 i)
      _ = (1 / 16) * ∑ i ∈ img, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / 16) * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have h := sum_pow_le (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) img
          have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
          rwa [h2] at h
      _ = 1 / 8 := by norm_num
  linarith

/-- **`∑_{j ∈ s} j²e^{-j²/4} ≤ 8`.** -/
private lemma sum_sq_mul_exp_neg_sq_div_four_le (s : Finset ℕ) :
    ∑ j ∈ s, (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ 8 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun j => j < 5)
    (f := fun j => (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4))
  rw [← hsplit]
  have h1 : ∑ j ∈ s.filter (fun j => j < 5), (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)
      ≤ 41 / 8 := by
    have hsub : ∑ j ∈ s.filter (fun j => j < 5), (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)
        ≤ ∑ j ∈ Finset.range 5, (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_range.mpr hx.2
      · intro i _ _
        positivity
    refine hsub.trans ?_
    have hrange : ∑ j ∈ Finset.range 5, (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)
        ≤ 41 / 8 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have t0 : ((((0 : ℕ)) : ℝ)) ^ 2 * Real.exp (-(((((0 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 0 :=
        le_of_eq (by norm_num)
      have t1 : ((((1 : ℕ)) : ℝ)) ^ 2 * Real.exp (-(((((1 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 := by
        have h : Real.exp (-(((((1 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 := exp_le_one_of_nonpos (by norm_num)
        nlinarith
      have t2 : ((((2 : ℕ)) : ℝ)) ^ 2 * Real.exp (-(((((2 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 2 := by
        have h : Real.exp (-(((((2 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 / 2 := exp_le_half_of_le (by norm_num)
        nlinarith
      have t3 : ((((3 : ℕ)) : ℝ)) ^ 2 * Real.exp (-(((((3 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 9 / 8 := by
        have h : Real.exp (-(((((3 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 / 8 := exp_le_inv_eight_of_le (by norm_num)
        nlinarith
      have t4 : ((((4 : ℕ)) : ℝ)) ^ 2 * Real.exp (-(((((4 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 := by
        have h : Real.exp (-(((((4 : ℕ)) : ℝ))) ^ 2 / 4) ≤ 1 / 16 := exp_le_inv_sixteen_of_le (by norm_num)
        nlinarith
      linarith
    exact hrange
  have h2 : ∑ j ∈ s.filter (fun j => ¬ j < 5), (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)
      ≤ 25 / 81 := by
    have hfe : s.filter (fun j => ¬ j < 5) = s.filter (fun j => 5 ≤ j) := by
      apply Finset.filter_congr
      intro j _
      exact not_lt
    rw [hfe]
    have hpt : ∀ j ∈ s.filter (fun j => 5 ≤ j),
        (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ (25 / 243) * (2 / 3 : ℝ) ^ (j - 5) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hj5 : 5 ≤ j := hj.2
      have hjeq : j = (j - 5) + 5 := (Nat.sub_add_cancel hj5).symm
      have hcast : (j : ℝ) = ((j - 5 : ℕ) : ℝ) + 5 := by
        rw [hjeq]
        push_cast
        ring
      have h1 : (j : ℝ) ^ 2 ≤ 25 * 2 ^ (j - 5) := by
        rw [hcast]
        exact sq_shift_le (j - 5)
      have h2 : Real.exp (-((j : ℝ)) ^ 2 / 4) ≤ (1 / 3 : ℝ) ^ j :=
        exp_le_inv_pow_three hj5 le_rfl
      have h3 : (1 / 3 : ℝ) ^ j = (1 / 243) * (1 / 3 : ℝ) ^ (j - 5) := by
        rw [hjeq, pow_add]
        norm_num
        ring
      calc (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)
          ≤ (25 * 2 ^ (j - 5)) * (1 / 3 : ℝ) ^ j :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ = (25 / 243) * (2 ^ (j - 5) * (1 / 3 : ℝ) ^ (j - 5)) := by
            rw [h3]
            ring
        _ = (25 / 243) * (2 / 3 : ℝ) ^ (j - 5) := by
            congr 1
            rw [← mul_pow]
            norm_num
    refine (Finset.sum_le_sum hpt).trans ?_
    set img := (s.filter (fun j => 5 ≤ j)).image (fun j => j - 5) with himg
    have h1 : ∑ i ∈ img, (25 / 243) * (2 / 3 : ℝ) ^ i
        = ∑ j ∈ s.filter (fun j => 5 ≤ j), (25 / 243) * (2 / 3 : ℝ) ^ (j - 5) := by
      rw [himg, sum_sub_shift_eq]
    rw [← h1]
    have hg : ∑ i ∈ img, (2 / 3 : ℝ) ^ i ≤ 3 := by
      have h := sum_pow_le (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) img
      have h2 : (1 - (2 / 3 : ℝ))⁻¹ = 3 := by norm_num
      rwa [h2] at h
    calc ∑ i ∈ img, (25 / 243) * (2 / 3 : ℝ) ^ i
        = (25 / 243) * ∑ i ∈ img, (2 / 3 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
      _ ≤ (25 / 243) * 3 := mul_le_mul_of_nonneg_left hg (by norm_num)
      _ = 25 / 81 := by norm_num
  linarith

/-! ## 3. The pointwise bound -/

/-- On the far set, `ℓt - 2R = √6 + ℓ(t - T)` with `T = (2R+√6)/ℓ`, so the weight is at
most `e^{-3/2}` times a Gaussian in `t - T`, which is dominated by the same Gaussian
evaluated at the shell index `k ≤ t`. -/
private lemma exp_weight_le {ℓ R t : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hcon : 2 * R + Real.sqrt 6 ≤ ℓ * t) (k : ℕ) (hk : (k : ℝ) ≤ t) :
    Real.exp (-((ℓ * t - 2 * R)) ^ 2 / 4)
      ≤ Real.exp (-(3 / 2)) *
        Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4) := by
  have hR0 : 0 ≤ R := hR
  have ht0 : 0 ≤ t := ht
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  set T : ℝ := (2 * R + Real.sqrt 6) / ℓ with hT
  have htT : T ≤ t := by
    rw [hT, div_le_iff₀ hℓpos]
    linarith [hcon]
  have hid : ℓ * t - 2 * R = Real.sqrt 6 + ℓ * (t - T) := by
    rw [hT]
    field_simp
    ring
  have hsq : 6 + (t - T) ^ 2 ≤ (ℓ * t - 2 * R) ^ 2 := by
    rw [hid]
    have h1 : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
    have h2 : (1 : ℝ) ≤ ℓ ^ 2 := by nlinarith
    nlinarith [h1, Real.sqrt_nonneg 6, mul_nonneg (sub_nonneg.mpr htT) hℓpos.le,
      sq_nonneg (t - T)]
  have hfirst : Real.exp (-((ℓ * t - 2 * R)) ^ 2 / 4)
      ≤ Real.exp (-(3 / 2)) * Real.exp (-((t - T)) ^ 2 / 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hsq]
  have hsec : Real.exp (-((t - T)) ^ 2 / 4)
      ≤ Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    have h1 : (max 0 ((k : ℝ) - T)) ^ 2 ≤ (t - T) ^ 2 := by
      by_cases h : T ≤ (k : ℝ)
      · have hm : max 0 ((k : ℝ) - T) = (k : ℝ) - T := max_eq_right (by linarith)
        rw [hm]
        have h2 : (k : ℝ) - T ≤ t - T := by linarith
        have h3 : (0 : ℝ) ≤ (k : ℝ) - T := by linarith
        nlinarith
      · have hm : max 0 ((k : ℝ) - T) = 0 := max_eq_left (by linarith)
        rw [hm]
        simpa using sq_nonneg (t - T)
    linarith
  calc Real.exp (-((ℓ * t - 2 * R)) ^ 2 / 4)
      ≤ Real.exp (-(3 / 2)) * Real.exp (-((t - T)) ^ 2 / 4) := hfirst
    _ ≤ Real.exp (-(3 / 2)) * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hsec (Real.exp_pos _).le

/-! ## 4. Counting the max-norm fibres -/

/-- A fibre of the max-norm map on a set of nonzero lattice vectors has at most `26k²`
elements, by `Work.BoseRowsFS.card_shell_boxZ_le`. -/
private lemma card_fibre_maxNat_le (u : Finset (Fin 3 → ℤ)) (hnz : ∀ a ∈ u, a ≠ 0)
    (k : ℕ) : (u.filter (fun a => maxNat a = k)).card ≤ 26 * k ^ 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hempty : u.filter (fun a => maxNat a = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hcon
      have h1 : 1 ≤ maxNat a := maxNat_pos (hnz a ha)
      omega
    rw [hempty]
    simp
  · have hsub : (u.filter (fun a => maxNat a = k)).image (fun a => a) ⊆ boxZ k \ boxZ (k - 1) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [mem_boxZ_iff_maxNat_le]
        omega
      · intro hcon
        rw [mem_boxZ_iff_maxNat_le] at hcon
        omega
    have hcard : (u.filter (fun a => maxNat a = k)).card ≤ 26 * k ^ 2 := by
      have himg : (u.filter (fun a => maxNat a = k)).image (fun a => a)
          = u.filter (fun a => maxNat a = k) := Finset.image_id
      rw [← himg]
      exact (Finset.card_le_card hsub).trans (card_shell_boxZ_le k hk)
    exact_mod_cast hcard

/-! ## 5. The shell sum -/

/-- `∑_{k<K} k² ≤ K³/3`. -/
private lemma sum_range_sq_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (k : ℝ) ^ 2 ≤ (K : ℝ) ^ 3 / 3 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : ((n : ℝ)) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 / 3 - (n : ℝ) ^ 3 / 3 := by
      have hc : (((n : ℕ) : ℝ) + 1) ^ 3 = (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1 := by
        ring
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      rw [hc]
      linarith
    linarith

/-- The arithmetic endgame: `(26/12)K³ + 39K² + 104 ≤ 1000(1+R)³` for `0 ≤ K ≤ 3.45(1+R)`. -/
private lemma far_tail_endgame {R K : ℝ} (hR : 0 ≤ R) (hK0 : 0 ≤ K)
    (hK : K ≤ 3.45 * (1 + R)) :
    (26 / 12) * K ^ 3 + 39 * K ^ 2 + 104 ≤ 1000 * (1 + R) ^ 3 := by
  have h1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hK3 : K ^ 3 ≤ (3.45 * (1 + R)) ^ 3 := pow_le_pow_left₀ hK0 hK 3
  have hK2 : K ^ 2 ≤ (3.45 * (1 + R)) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have h2 : (1 + R) ^ 2 ≤ (1 + R) ^ 3 := by nlinarith
  have h3 : (1 : ℝ) ≤ (1 + R) ^ 3 := by nlinarith
  nlinarith [hK3, hK2, h2, h3, h1, hR]

/-- `∑_{k ∈ s} 26k²·e^{-3/2}·exp(-(max 0 (k-T))²/4) ≤ 1000(1+R)³`, the majorant of the
lattice sum, with `T = (2R+√6)/ℓ`. -/
private lemma far_tail_shell_sum_le {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R) (s : Finset ℕ) :
    ∑ k ∈ s, 26 * (k : ℝ) ^ 2 *
        (Real.exp (-(3 / 2)) * Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4))
      ≤ 1000 * (1 + R) ^ 3 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  set T : ℝ := (2 * R + Real.sqrt 6) / ℓ with hT
  set c : ℝ := Real.exp (-(3 / 2)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hcle : c ≤ 1 / 4 := by
    rw [hc]
    exact exp_neg_three_halves_le
  set K : ℕ := Nat.ceil T with hK
  have hTnonneg : 0 ≤ T := by
    rw [hT]
    positivity
  have hKT : T ≤ (K : ℝ) := Nat.le_ceil T
  have hKlt : (K : ℝ) < T + 1 := by
    rw [hK]
    exact Nat.ceil_lt_add_one hTnonneg
  have hTub : T ≤ 2 * R + Real.sqrt 6 := by
    rw [hT, div_le_iff₀ hℓpos]
    nlinarith [hR, hℓ, Real.sqrt_nonneg 6]
  have hsqrt6 : Real.sqrt 6 ≤ 2.45 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg 6]
  have hKub : (K : ℝ) ≤ 3.45 * (1 + R) := by
    have h1 : (K : ℝ) ≤ 2 * R + 3.45 := by linarith
    nlinarith [hR]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun k => k < K)
    (f := fun k => 26 * (k : ℝ) ^ 2 * (c * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4)))
  have hpart1 : ∑ k ∈ s.filter (fun k => k < K),
      26 * (k : ℝ) ^ 2 * (c * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4))
      ≤ 26 * c * ((K : ℝ) ^ 3 / 3) := by
    have hstep : ∑ k ∈ s.filter (fun k => k < K),
        26 * (k : ℝ) ^ 2 * (c * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4))
        = ∑ k ∈ s.filter (fun k => k < K), 26 * c * (k : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      have hk1 : k + 1 ≤ K := hk.2
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hk1
      rw [Nat.cast_add, Nat.cast_one] at hcast
      have hkT : (k : ℝ) < T := by linarith
      have hz : max 0 ((k : ℝ) - T) = 0 := max_eq_left (by linarith)
      have hW : Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4) = 1 := by
        rw [hz]
        simp
      rw [hW, mul_one]
      ring
    rw [hstep, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ k ∈ s.filter (fun k => k < K), (k : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.range K, (k : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_filter] at hx
            exact Finset.mem_range.mpr hx.2
          · intro i _ _
            positivity
      _ ≤ (K : ℝ) ^ 3 / 3 := sum_range_sq_le K
  have hpart2 : ∑ k ∈ s.filter (fun k => ¬ k < K),
      26 * (k : ℝ) ^ 2 * (c * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4))
      ≤ 52 * (K : ℝ) ^ 2 * c * 3 + 52 * c * 8 := by
    have hfe : s.filter (fun k => ¬ k < K) = s.filter (fun k => K ≤ k) := by
      apply Finset.filter_congr
      intro k _
      exact not_lt
    rw [hfe]
    have hstep1 : ∑ k ∈ s.filter (fun k => K ≤ k),
        26 * (k : ℝ) ^ 2 * (c * Real.exp (-((max 0 ((k : ℝ) - T))) ^ 2 / 4))
        ≤ ∑ k ∈ s.filter (fun k => K ≤ k),
            26 * (k : ℝ) ^ 2 * (c * Real.exp (-(((k : ℝ) - (K : ℝ))) ^ 2 / 4)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_filter] at hk
      have hkK : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.2
      have hz : max 0 ((k : ℝ) - T) = (k : ℝ) - T := max_eq_right (by linarith)
      rw [hz]
      have hsq : ((k : ℝ) - (K : ℝ)) ^ 2 ≤ ((k : ℝ) - T) ^ 2 := by nlinarith [hkK, hKT]
      have hexp : Real.exp (-(((k : ℝ) - T)) ^ 2 / 4)
          ≤ Real.exp (-(((k : ℝ) - (K : ℝ))) ^ 2 / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hc0) (by positivity)
    refine hstep1.trans ?_
    set img := (s.filter (fun k => K ≤ k)).image (fun k => k - K) with himg
    have heq : ∑ k ∈ s.filter (fun k => K ≤ k),
        26 * (k : ℝ) ^ 2 * (c * Real.exp (-(((k : ℝ) - (K : ℝ))) ^ 2 / 4))
        = ∑ j ∈ img, 26 * (((K + j : ℕ) : ℝ)) ^ 2 * (c * Real.exp (-((j : ℝ)) ^ 2 / 4)) := by
      have hpoint : ∀ k ∈ s.filter (fun k => K ≤ k),
          26 * (k : ℝ) ^ 2 * (c * Real.exp (-(((k : ℝ) - (K : ℝ))) ^ 2 / 4))
            = 26 * (((K + (k - K) : ℕ) : ℝ)) ^ 2
                * (c * Real.exp (-((((k - K : ℕ)) : ℝ)) ^ 2 / 4)) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkK : K ≤ k := hk.2
        have h1 : (((K + (k - K) : ℕ) : ℝ)) = (k : ℝ) := by
          rw [Nat.cast_add, Nat.cast_sub hkK]
          ring
        have h2 : (((k - K : ℕ)) : ℝ) = (k : ℝ) - (K : ℝ) := Nat.cast_sub hkK
        rw [h1, h2]
      calc ∑ k ∈ s.filter (fun k => K ≤ k),
            26 * (k : ℝ) ^ 2 * (c * Real.exp (-(((k : ℝ) - (K : ℝ))) ^ 2 / 4))
          = ∑ k ∈ s.filter (fun k => K ≤ k),
              26 * (((K + (k - K) : ℕ) : ℝ)) ^ 2
                * (c * Real.exp (-((((k - K : ℕ)) : ℝ)) ^ 2 / 4)) :=
            Finset.sum_congr rfl hpoint
        _ = ∑ j ∈ img, 26 * (((K + j : ℕ) : ℝ)) ^ 2 * (c * Real.exp (-((j : ℝ)) ^ 2 / 4)) := by
            rw [himg]
            exact (sum_sub_shift_eq (N := K) s
              (f := fun j => 26 * (((K + j : ℕ) : ℝ)) ^ 2
                * (c * Real.exp (-((j : ℝ)) ^ 2 / 4)))).symm
    rw [heq]
    have hterm : ∑ j ∈ img, 26 * (((K + j : ℕ) : ℝ)) ^ 2 * (c * Real.exp (-((j : ℝ)) ^ 2 / 4))
        ≤ 52 * (K : ℝ) ^ 2 * c * (∑ j ∈ img, Real.exp (-((j : ℝ)) ^ 2 / 4))
          + 52 * c * (∑ j ∈ img, (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      have h1 : (((K + j : ℕ) : ℝ)) ^ 2 ≤ 2 * (K : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2 := by
        rw [Nat.cast_add]
        nlinarith [sq_nonneg ((K : ℝ) - (j : ℝ))]
      have hexp : (0 : ℝ) < Real.exp (-((j : ℝ)) ^ 2 / 4) := Real.exp_pos _
      nlinarith [h1, hc0, hexp.le, mul_nonneg hc0 hexp.le]
    refine hterm.trans ?_
    have hA := sum_exp_neg_sq_div_four_le img
    have hB := sum_sq_mul_exp_neg_sq_div_four_le img
    have h3 : 52 * (K : ℝ) ^ 2 * c * (∑ j ∈ img, Real.exp (-((j : ℝ)) ^ 2 / 4))
        ≤ 52 * (K : ℝ) ^ 2 * c * 3 := mul_le_mul_of_nonneg_left hA (by positivity)
    have h4 : 52 * c * (∑ j ∈ img, (j : ℝ) ^ 2 * Real.exp (-((j : ℝ)) ^ 2 / 4))
        ≤ 52 * c * 8 := mul_le_mul_of_nonneg_left hB (by positivity)
    linarith
  have hfin : 26 * c * ((K : ℝ) ^ 3 / 3) + (52 * (K : ℝ) ^ 2 * c * 3 + 52 * c * 8)
      ≤ 1000 * (1 + R) ^ 3 := by
    have h1 : 26 * c * ((K : ℝ) ^ 3 / 3) ≤ 26 * ((K : ℝ) ^ 3 / 3) * (1 / 4) := by
      have h := mul_le_mul_of_nonneg_left hcle (by positivity : (0 : ℝ) ≤ 26 * ((K : ℝ) ^ 3 / 3))
      linarith [h]
    have h2 : 52 * (K : ℝ) ^ 2 * c * 3 ≤ 52 * (K : ℝ) ^ 2 * (1 / 4) * 3 := by
      have h := mul_le_mul_of_nonneg_left hcle (by positivity : (0 : ℝ) ≤ 52 * (K : ℝ) ^ 2 * 3)
      linarith [h]
    have h3 : 52 * c * 8 ≤ 52 * (1 / 4) * 8 := by
      have h := mul_le_mul_of_nonneg_left hcle (by norm_num : (0 : ℝ) ≤ 52 * 8)
      linarith [h]
    have h4 := far_tail_endgame hR (Nat.cast_nonneg K) hKub
    linarith
  rw [← hsplit]
  linarith [hpart1, hpart2, hfin]

/-! ## 6. Assembly -/

/-- The majorant estimate for a finite set of far lattice vectors. -/
private lemma far_tail_finset_le {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R)
    (u : Finset (Fin 3 → ℤ)) (hnz : ∀ m ∈ u, m ≠ 0)
    (hcon : ∀ m ∈ u, 2 * R + Real.sqrt 6 ≤ ℓ * ‖vecZ m‖) :
    ∑ m ∈ u, Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4) ≤ 1000 * (1 + R) ^ 3 := by
  have hfib := Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image maxNat) (g := maxNat)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun m => Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4))
  rw [← hfib]
  have hterm : ∀ k ∈ u.image maxNat,
      ∑ m ∈ u.filter (fun m => maxNat m = k), Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4)
        ≤ 26 * (k : ℝ) ^ 2 *
            (Real.exp (-(3 / 2)) *
              Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4)) := by
    intro k _
    have hpt : ∀ m ∈ u.filter (fun m => maxNat m = k),
        Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4)
          ≤ Real.exp (-(3 / 2)) *
              Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      have h1 := exp_weight_le hℓ hR (norm_nonneg (vecZ m)) (hcon m hm.1) (maxNat m)
        (norm_vecZ_ge_maxNat m)
      simpa [hm.2] using h1
    have hcard : ((u.filter (fun m => maxNat m = k)).card : ℝ) ≤ 26 * (k : ℝ) ^ 2 := by
      have := card_fibre_maxNat_le u hnz k
      exact_mod_cast this
    calc ∑ m ∈ u.filter (fun m => maxNat m = k), Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4)
        ≤ ∑ m ∈ u.filter (fun m => maxNat m = k),
            (Real.exp (-(3 / 2)) *
              Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4)) :=
          Finset.sum_le_sum hpt
      _ = ((u.filter (fun m => maxNat m = k)).card : ℝ) *
            (Real.exp (-(3 / 2)) *
              Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 26 * (k : ℝ) ^ 2 *
            (Real.exp (-(3 / 2)) *
              Real.exp (-((max 0 ((k : ℝ) - (2 * R + Real.sqrt 6) / ℓ))) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  exact le_trans (Finset.sum_le_sum hterm) (far_tail_shell_sum_le hℓ hR _)

theorem far_tail_le {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ) :
    (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖Work.BoseRowsFS.vecZ m‖ < 2 * R + Real.sqrt 6)},
        Real.exp (-((ℓ * ‖Work.BoseRowsFS.vecZ m.1‖ - 2 * R)) ^ 2 / 4))
      ≤ 1000 * (1 + R) ^ 3 := by
  have _hRℓ : R ≤ ℓ := hRℓ
  refine Real.tsum_le_of_sum_le
    (f := fun m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖Work.BoseRowsFS.vecZ m‖ < 2 * R + Real.sqrt 6)} =>
      Real.exp (-((ℓ * ‖Work.BoseRowsFS.vecZ m.1‖ - 2 * R)) ^ 2 / 4))
    (fun m => (Real.exp_pos _).le) (fun u => ?_)
  have hmem : ∀ m ∈ u.image Subtype.val, m ≠ 0 ∧ 2 * R + Real.sqrt 6 ≤ ℓ * ‖vecZ m‖ := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨x.2.1, not_lt.mp x.2.2⟩
  have hconv : ∑ m ∈ u, Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R)) ^ 2 / 4)
      = ∑ m ∈ u.image Subtype.val, Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R)) ^ 2 / 4) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Subtype.val_injective hxy
  rw [hconv]
  exact far_tail_finset_le hℓ hR _ (fun m hm => (hmem m hm).1) (fun m hm => (hmem m hm).2)

end Work.BoseRowsFS
