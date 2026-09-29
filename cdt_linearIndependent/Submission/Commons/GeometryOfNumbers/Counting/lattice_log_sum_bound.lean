import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Star
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.Analysis.SpecialFunctions.ExpLog.log_le_sum_inv_of_le
import Submission.Commons.Analysis.Series.sum_pow_le
import Submission.Commons.Analysis.SpecialFunctions.ExpLog.one_add_pow_le_exp
import Submission.Commons.Analysis.SpecialFunctions.ExpLog.exp_sub_one_le_two_mul

namespace Commons.GeometryOfNumbers.Counting

open MeasureTheory Metric Finset
open scoped BigOperators

noncomputable section

/-- The point of `EuclideanSpace ℝ (Fin n)` attached to a vector of integers. -/
def intPt (n : ℕ) (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

@[simp] lemma intPt_apply {n : ℕ} (k : Fin n → ℤ) (i : Fin n) :
    (intPt n k) i = (k i : ℝ) := rfl

@[simp] lemma intPt_zero (n : ℕ) : intPt n 0 = 0 := by
  ext i
  simp [intPt]

lemma norm_intPt_sq {n : ℕ} (k : Fin n → ℤ) :
    ‖intPt n k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [intPt]
  exact norm_toLp_intLattice k

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
lemma one_le_norm_intPt {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    1 ≤ ‖intPt n k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h2 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ ((k i : ℝ)) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h2 2
    simpa using h
  have hsum : (1 : ℝ) ≤ ∑ j, ((k j : ℝ)) ^ 2 :=
    le_trans h3 (Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i))
  have hsq : (1 : ℝ) ≤ ‖intPt n k‖ ^ 2 := by rw [norm_intPt_sq]; exact hsum
  have hx : 0 ≤ ‖intPt n k‖ := norm_nonneg _
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx, Real.sqrt_one] at this

lemma norm_intPt_eq_zero_iff {n : ℕ} (k : Fin n → ℤ) : ‖intPt n k‖ = 0 ↔ k = 0 := by
  rw [← sq_eq_zero_iff, norm_intPt_sq]
  constructor
  · intro h
    funext i
    have h1 : ((k i : ℝ)) ^ 2 = 0 :=
      le_antisymm (by
        have := Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i)
        rw [h] at this
        exact this) (sq_nonneg _)
    simpa using h1
  · intro h
    simp [h]

/-- The volume of a ball in `ℝ^n` is `r ^ n` times the volume of the unit ball. -/
lemma volume_ball_toReal (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal
      = r ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have h1 := EuclideanSpace.volume_ball (Fin n) (0 : EuclideanSpace ℝ (Fin n)) r
  have h2 := EuclideanSpace.volume_ball (Fin n) (0 : EuclideanSpace ℝ (Fin n)) 1
  simp only [Fintype.card_fin] at h1 h2
  rw [h1, h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_pow,
    one_mul]

/-- Lattice points in a ball of radius `r`, bounded by the volume of the ball of radius
`r + √n / 2`. -/
lemma card_int_points_le_volume (n : ℕ) (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    (Nat.card {x : Fin n → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ r ^ 2} : ℝ)
      ≤ (r + Real.sqrt n / 2) ^ n
          * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  have h := card_int_points_ball_le_volume (d := n) (by omega) hr
  rwa [volume_ball_toReal n (r + Real.sqrt n / 2) hn (by positivity)] at h

/-- The sum studied in this file. -/
def logSum (n : ℕ) (R : ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, max 0 (Real.log (R / ‖intPt n k‖))

lemma logSum_nonneg (n : ℕ) (R : ℝ) : 0 ≤ logSum n R :=
  tsum_nonneg fun _ => le_max_left _ _

lemma max_log_zero_of_lt {n : ℕ} {R : ℝ} (hR : 1 ≤ R) {M : ℕ} (hRM : R ≤ (M : ℝ))
    {k : Fin n → ℤ} (hk : (M : ℝ) ^ 2 < ∑ j, ((k j : ℝ)) ^ 2) :
    max 0 (Real.log (R / ‖intPt n k‖)) = 0 := by
  have hnorm : (M : ℝ) < ‖intPt n k‖ := by
    have h2 : (M : ℝ) ^ 2 < ‖intPt n k‖ ^ 2 := by rw [norm_intPt_sq]; exact hk
    have h3 : Real.sqrt ((M : ℝ) ^ 2) < Real.sqrt (‖intPt n k‖ ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) h2
    rwa [Real.sqrt_sq (Nat.cast_nonneg M), Real.sqrt_sq (norm_nonneg _)] at h3
  have hlt : R < ‖intPt n k‖ := lt_of_le_of_lt hRM hnorm
  have hpos : 0 < R / ‖intPt n k‖ := div_pos (by linarith) (by linarith)
  have hle : R / ‖intPt n k‖ ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < ‖intPt n k‖)]
    exact le_of_lt hlt
  exact max_eq_left (Real.log_nonpos hpos.le hle)

lemma logSum_eq_finset_sum (n : ℕ) {R : ℝ} (hR : 1 ≤ R) (M : ℕ) (hRM : R ≤ (M : ℝ)) :
    logSum n R = ∑ k ∈ (finite_int_points_ball (d := n) (M : ℝ)).toFinset,
      max 0 (Real.log (R / ‖intPt n k‖)) := by
  have hzero : ∀ k ∉ (finite_int_points_ball (d := n) (M : ℝ)).toFinset,
      max 0 (Real.log (R / ‖intPt n k‖)) = 0 := by
    intro k hk
    exact max_log_zero_of_lt hR hRM (not_le.mp fun h => hk ((Set.Finite.mem_toFinset _).mpr h))
  rw [logSum, tsum_eq_sum hzero]

lemma logSum_summable (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    Summable fun k : Fin n → ℤ => max 0 (Real.log (R / ‖intPt n k‖)) := by
  set M : ℕ := Nat.ceil R with hM
  have hRM : R ≤ (M : ℝ) := Nat.le_ceil R
  have hzero : ∀ k ∉ (finite_int_points_ball (d := n) (M : ℝ)).toFinset,
      max 0 (Real.log (R / ‖intPt n k‖)) = 0 := by
    intro k hk
    exact max_log_zero_of_lt hR hRM (not_le.mp fun h => hk ((Set.Finite.mem_toFinset _).mpr h))
  exact (hasSum_sum_of_ne_finset_zero hzero).summable

/-- Pointwise bound of the summand by a truncated harmonic sum. -/
lemma max_log_le_sum_indicator {n : ℕ} {R : ℝ} (hR : 1 ≤ R) {M : ℕ} (hRM : R ≤ (M : ℝ))
    (k : Fin n → ℤ) :
    max 0 (Real.log (R / ‖intPt n k‖))
      ≤ ∑ i ∈ Finset.Icc 1 M,
          (1 / (i : ℝ)) * (if ‖intPt n k‖ ≤ (i : ℝ) + 1 then 1 else 0) := by
  have hsum_nonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 M,
      (1 / (i : ℝ)) * (if ‖intPt n k‖ ≤ (i : ℝ) + 1 then 1 else 0) := by
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : ‖intPt n k‖ ≤ (i : ℝ) + 1
    · simp only [h, if_true, mul_one]
      positivity
    · simp only [h, if_false, mul_zero, le_refl]
  by_cases h1 : 1 ≤ ‖intPt n k‖
  · by_cases h2 : ‖intPt n k‖ ≤ R
    · have hmax : max 0 (Real.log (R / ‖intPt n k‖)) = Real.log (R / ‖intPt n k‖) :=
        max_eq_right (Real.log_nonneg (by
          rw [one_le_div (by linarith : (0 : ℝ) < ‖intPt n k‖)]
          exact h2))
      rw [hmax]
      refine (Commons.Analysis.SpecialFunctions.ExpLog.log_le_sum_inv_of_le
        (‖intPt n k‖) R M h1 h2 hRM).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : ‖intPt n k‖ ≤ (i : ℝ) + 1
      · simp [h]
      · simp [h]
    · have hlt : R < ‖intPt n k‖ := lt_of_not_ge h2
      have hpos : 0 < R / ‖intPt n k‖ := div_pos (by linarith) (by linarith)
      have hle : R / ‖intPt n k‖ ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < ‖intPt n k‖)]
        exact le_of_lt hlt
      have hmax : max 0 (Real.log (R / ‖intPt n k‖)) = 0 :=
        max_eq_left (Real.log_nonpos hpos.le hle)
      rw [hmax]
      exact hsum_nonneg
  · push Not at h1
    have hk0 : k = 0 := by
      by_contra hk
      exact absurd (one_le_norm_intPt hk) (not_le.mpr h1)
    subst hk0
    have hmax : max 0 (Real.log (R / ‖intPt n 0‖)) = 0 := by
      rw [intPt_zero]
      simp
    rw [hmax]
    exact hsum_nonneg

/-- The truncated harmonic sum of the lattice-point counts dominates the sum. -/
lemma logSum_le_sum_card (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 1 ≤ R) :
    logSum n R ≤ ∑ i ∈ Finset.Icc 1 (Nat.ceil R),
      (1 / (i : ℝ)) * (Nat.card {x : Fin n → ℤ //
        (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} : ℝ) := by
  set M : ℕ := Nat.ceil R with hM
  have hRM : R ≤ (M : ℝ) := Nat.le_ceil R
  rw [logSum_eq_finset_sum n hR M hRM]
  set S : Set (Fin n → ℤ) := {x | (∑ j, ((x j : ℝ)) ^ 2) ≤ (M : ℝ) ^ 2} with hS
  have hSfin : S.Finite := finite_int_points_ball (M : ℝ)
  calc ∑ k ∈ hSfin.toFinset, max 0 (Real.log (R / ‖intPt n k‖))
      ≤ ∑ k ∈ hSfin.toFinset, ∑ i ∈ Finset.Icc 1 M,
          (1 / (i : ℝ)) * (if ‖intPt n k‖ ≤ (i : ℝ) + 1 then 1 else 0) :=
        Finset.sum_le_sum fun k _ => max_log_le_sum_indicator hR hRM k
    _ = ∑ i ∈ Finset.Icc 1 M, ∑ k ∈ hSfin.toFinset,
          (1 / (i : ℝ)) * (if ‖intPt n k‖ ≤ (i : ℝ) + 1 then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * ∑ k ∈ hSfin.toFinset,
          (if ‖intPt n k‖ ≤ (i : ℝ) + 1 then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (Nat.card {x : Fin n → ℤ //
          (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hnn : (0 : ℝ) ≤ 1 / (i : ℝ) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hnn
        set T : Set (Fin n → ℤ) := {x | (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} with hT
        have hTfin : T.Finite := finite_int_points_ball ((i : ℝ) + 1)
        haveI : Fintype T := hTfin.fintype
        have hsub : hSfin.toFinset.filter (fun k => ‖intPt n k‖ ≤ (i : ℝ) + 1)
            ⊆ hTfin.toFinset := by
          intro k hk
          rw [Finset.mem_filter] at hk
          rw [Set.Finite.mem_toFinset]
          have h2 : ‖intPt n k‖ ^ 2 ≤ ((i : ℝ) + 1) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hk.2 2
          rwa [norm_intPt_sq] at h2
        rw [Finset.sum_boole]
        have hcard : (hSfin.toFinset.filter (fun k => ‖intPt n k‖ ≤ (i : ℝ) + 1)).card
            ≤ Nat.card {x : Fin n → ℤ // (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} := by
          calc (hSfin.toFinset.filter (fun k => ‖intPt n k‖ ≤ (i : ℝ) + 1)).card
              ≤ hTfin.toFinset.card := Finset.card_le_card hsub
            _ = Nat.card T := hTfin.card_toFinset.trans Nat.card_eq_fintype_card.symm
            _ = Nat.card {x : Fin n → ℤ // (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} := rfl
        exact_mod_cast hcard

/-- Reindexing: `∑_{m=1}^{n} f m = ∑_{k<n} f (k+1)`. -/
lemma sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 n, f m = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- The truncated harmonic sum is at most the number of terms. -/
lemma sum_inv_le_card (M : ℕ) : ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ ≤ M := by
  calc ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ ≤ ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
        rw [inv_le_one₀ hjpos]
        exact_mod_cast hj1
    _ = M := by
        rw [sum_Icc_one_eq_sum_range]
        simp

/-- The binomial theorem in the form `∑_{m ≤ n} C(n,m) u^m = (1+u)^n`. -/
lemma binom_sum_range (n : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * u ^ m = (1 + u) ^ n := by
  have h := add_pow u (1 : ℝ) n
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using h.symm

/-- `∑_{m=1}^{n} C(n,m) u^m = (1+u)^n - 1`. -/
lemma binom_sum_Icc (n : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.Icc 1 n, (n.choose m : ℝ) * u ^ m = (1 + u) ^ n - 1 := by
  rw [sum_Icc_one_eq_sum_range, ← binom_sum_range n u, Finset.sum_range_succ']
  simp

/-- `∑_{m=1}^{n-1} C(n,m) u^m ≤ (1+u)^n - 1` for `u ≥ 0`. -/
lemma binom_sum_Icc_le (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * u ^ m ≤ (1 + u) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have h := binom_sum_Icc n u
    have hsub : Finset.Icc 1 (n - 1) ⊆ Finset.Icc 1 n := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    have h1 : ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * u ^ m
        ≤ ∑ m ∈ Finset.Icc 1 n, (n.choose m : ℝ) * u ^ m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    linarith [h1, h]

/-- **The discrete sum estimate.**  For `n ≥ 2`, `0 ≤ β ≤ n` and `10^6 n² β ≤ M+1`,
`∑_{j=1}^{M} (j+β)^n / j ≤ 2 (M+1)^n / n`.  This is the discretised form of
`∫_1^{M+1} (t+β)^n/t dt ≈ (M+1)^n/n`; the hypothesis makes the discretisation error small. -/
lemma inv_mul_pow_sum_le (n : ℕ) (β : ℝ) (M : ℕ) (hn : 2 ≤ n) (hβ : 0 ≤ β) (hβn : β ≤ n)
    (hM : 10 ^ 6 * (n : ℝ) ^ 2 * β ≤ (M : ℝ) + 1) :
    ∑ j ∈ Finset.Icc 1 M, ((j : ℝ) + β) ^ n / (j : ℝ) ≤ 2 * ((M : ℝ) + 1) ^ n / n := by
  set A : ℝ := (M : ℝ) + 1 with hA
  have hM' : 10 ^ 6 * (n : ℝ) ^ 2 * β ≤ A := by rw [hA]; exact hM
  have hM'' : 10 ^ 6 * ((n : ℝ) ^ 2 * β) ≤ A := by linarith [hM']
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hA]; push_cast
    linarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  set u : ℝ := β / A with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu_le : u ≤ 1 / (10 ^ 6 * (n : ℝ) ^ 2) := by
    have hc : (0 : ℝ) < 10 ^ 6 * (n : ℝ) ^ 2 := by positivity
    rw [hu, div_le_iff₀ hApos,
      show (1 : ℝ) / (10 ^ 6 * (n : ℝ) ^ 2) * A = A / (10 ^ 6 * (n : ℝ) ^ 2) by ring,
      le_div_iff₀ hc]
    nlinarith [hM', hc]
  have hu1 : u ≤ 1 := by
    have hc : (1 : ℝ) ≤ 10 ^ 6 * (n : ℝ) ^ 2 := by nlinarith [hn1]
    calc u ≤ 1 / (10 ^ 6 * (n : ℝ) ^ 2) := hu_le
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hc
  have hnu : (n : ℝ) * u ≤ 1 / 2 := by
    have h1 : (n : ℝ) * u ≤ (n : ℝ) * (1 / (10 ^ 6 * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hu_le (by positivity)
    have h2 : (n : ℝ) * (1 / (10 ^ 6 * (n : ℝ) ^ 2)) = 1 / (10 ^ 6 * (n : ℝ)) := by
      field_simp
    rw [h2] at h1
    have h3 : (1 : ℝ) / (10 ^ 6 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 6 * (n : ℝ))]
      linarith
    linarith
  have hexp : (1 + u) ^ n - 1 ≤ 2 * ((n : ℝ) * u) := by
    have h1 := Commons.Analysis.SpecialFunctions.ExpLog.one_add_pow_le_exp n u hu0
    have h2 := Commons.Analysis.SpecialFunctions.ExpLog.exp_sub_one_le_two_mul
      ((n : ℝ) * u) (by positivity) hnu
    linarith
  -- the exact decomposition of the sum
  have hsplit : ∑ j ∈ Finset.Icc 1 M, ((j : ℝ) + β) ^ n / (j : ℝ)
      = ∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m
          * (∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ (n - 1 - m))
        + β ^ n * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ := by
    have hpt : ∀ j ∈ Finset.Icc 1 M, ((j : ℝ) + β) ^ n / (j : ℝ)
        = (∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m * (j : ℝ) ^ (n - 1 - m))
          + β ^ n * ((j : ℝ))⁻¹ := by
      intro j hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        have : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        exact_mod_cast (by omega : 0 < j)
      have hpow : ((j : ℝ) + β) ^ n
          = (∑ m ∈ Finset.range n, β ^ m * (j : ℝ) ^ (n - m) * (n.choose m : ℝ)) + β ^ n := by
        rw [add_comm ((j : ℝ)) β, add_pow, Finset.sum_range_succ]
        simp
      rw [hpow, add_div, Finset.sum_div]
      congr 1
      · refine Finset.sum_congr rfl fun m hm => ?_
        have hm_lt : m < n := Finset.mem_range.mp hm
        rw [show n - m = (n - 1 - m) + 1 by omega, pow_succ]
        field_simp
    calc ∑ j ∈ Finset.Icc 1 M, ((j : ℝ) + β) ^ n / (j : ℝ)
        = ∑ j ∈ Finset.Icc 1 M, ((∑ m ∈ Finset.range n,
              (n.choose m : ℝ) * β ^ m * (j : ℝ) ^ (n - 1 - m))
            + β ^ n * ((j : ℝ))⁻¹) := Finset.sum_congr rfl hpt
      _ = (∑ j ∈ Finset.Icc 1 M, ∑ m ∈ Finset.range n,
              (n.choose m : ℝ) * β ^ m * (j : ℝ) ^ (n - 1 - m))
            + ∑ j ∈ Finset.Icc 1 M, β ^ n * ((j : ℝ))⁻¹ := Finset.sum_add_distrib
      _ = (∑ m ∈ Finset.range n, ∑ j ∈ Finset.Icc 1 M,
              (n.choose m : ℝ) * β ^ m * (j : ℝ) ^ (n - 1 - m))
            + β ^ n * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ = ∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m
              * (∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ (n - 1 - m))
            + β ^ n * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ := by
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
  rw [hsplit]
  -- binomial identity
  have hbinom : ∑ m ∈ Finset.Icc 1 n, (n.choose m : ℝ) * β ^ m * A ^ (n - m)
      = (A + β) ^ n - A ^ n := by
    rw [sum_Icc_one_eq_sum_range]
    have h := add_pow β A n
    rw [add_comm β A] at h
    rw [h, Finset.sum_range_succ']
    simp [mul_comm, mul_left_comm, mul_assoc]
  -- power identity
  have hAu : A ^ n * u ^ (n - 1) = β ^ (n - 1) * A := by
    have h1 : n - 1 + 1 = n := by omega
    rw [hu, div_pow, mul_div_assoc', mul_comm (A ^ n) (β ^ (n - 1)),
      div_eq_iff (pow_ne_zero (n - 1) hAne), mul_assoc, ← pow_succ', h1]
  have hAu1 : (A + β) ^ n = A ^ n * (1 + u) ^ n := by
    have h1 : A * (1 + u) = A + β := by
      rw [hu, mul_add, mul_one, mul_div_cancel₀ β hAne]
    rw [← h1, mul_pow]
  -- bound the m ≥ 1 tail of the first sum
  have htail : ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * β ^ m
        * (A ^ (n - m) / ((n - m : ℕ) : ℝ)) ≤ (A + β) ^ n - A ^ n := by
    have hmm : ∀ m ∈ Finset.Icc 1 (n - 1),
        (n.choose m : ℝ) * β ^ m * (A ^ (n - m) / ((n - m : ℕ) : ℝ))
          ≤ (n.choose m : ℝ) * β ^ m * A ^ (n - m) := by
      intro m hm
      have hnm1 : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
        have : 1 ≤ n - m := by
          have := (Finset.mem_Icc.mp hm).2
          omega
        exact_mod_cast this
      have hnn : (0 : ℝ) ≤ (n.choose m : ℝ) * β ^ m * A ^ (n - m) := by positivity
      calc (n.choose m : ℝ) * β ^ m * (A ^ (n - m) / ((n - m : ℕ) : ℝ))
          = (n.choose m : ℝ) * β ^ m * A ^ (n - m) / ((n - m : ℕ) : ℝ) := by ring
        _ ≤ (n.choose m : ℝ) * β ^ m * A ^ (n - m) := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < ((n - m : ℕ) : ℝ))]
            nlinarith [hnn, hnm1]
    have hsub : Finset.Icc 1 (n - 1) ⊆ Finset.Icc 1 n := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    have hsubset : ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * β ^ m * A ^ (n - m)
        ≤ ∑ m ∈ Finset.Icc 1 n, (n.choose m : ℝ) * β ^ m * A ^ (n - m) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    calc ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * β ^ m
          * (A ^ (n - m) / ((n - m : ℕ) : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * β ^ m * A ^ (n - m) :=
          Finset.sum_le_sum hmm
      _ ≤ ∑ m ∈ Finset.Icc 1 n, (n.choose m : ℝ) * β ^ m * A ^ (n - m) := hsubset
      _ = (A + β) ^ n - A ^ n := hbinom
  -- decompose the m = 0 term of the first sum
  have hdecomp : ∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m
        * (A ^ (n - m) / ((n - m : ℕ) : ℝ))
      = A ^ n / n + ∑ m ∈ Finset.Icc 1 (n - 1), (n.choose m : ℝ) * β ^ m
          * (A ^ (n - m) / ((n - m : ℕ) : ℝ)) := by
    have h := Finset.sum_range_succ'
      (fun m : ℕ => (n.choose m : ℝ) * β ^ m * (A ^ (n - m) / ((n - m : ℕ) : ℝ))) (n - 1)
    rw [show n - 1 + 1 = n by omega] at h
    rw [h, ← sum_Icc_one_eq_sum_range (n - 1)
      (fun m : ℕ => (n.choose m : ℝ) * β ^ m * (A ^ (n - m) / ((n - m : ℕ) : ℝ)))]
    simp [add_comm]
  -- termwise bound of the first sum
  have hterm : ∀ m ∈ Finset.range n,
      (n.choose m : ℝ) * β ^ m * (∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ (n - 1 - m))
        ≤ (n.choose m : ℝ) * β ^ m * (A ^ (n - m) / ((n - m : ℕ) : ℝ)) := by
    intro m hm
    have hm_lt : m < n := Finset.mem_range.mp hm
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := Commons.Analysis.Series.sum_pow_le M (n - 1 - m)
    rw [← hA] at h
    have hexp_eq : (n - 1 - m) + 1 = n - m := by omega
    have hcast : (((n - 1 - m : ℕ)) : ℝ) + 1 = (((n - m : ℕ)) : ℝ) := by
      calc (((n - 1 - m : ℕ)) : ℝ) + 1 = (((n - 1 - m : ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring
        _ = (((n - m : ℕ)) : ℝ) := by rw [hexp_eq]
    rw [hcast, hexp_eq] at h
    exact h
  -- the harmonic part
  have hharm : ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ ≤ (M : ℝ) := sum_inv_le_card M
  have hharm2 : β ^ n * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹ ≤ β ^ n * A := by
    refine le_trans (mul_le_mul_of_nonneg_left hharm (pow_nonneg hβ n)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ n)
    rw [hA]; push_cast; linarith
  -- assemble
  have hfirst : ∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m
        * (∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ (n - 1 - m))
      ≤ A ^ n / n + ((A + β) ^ n - A ^ n) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [hdecomp]
    exact add_le_add le_rfl htail
  have hfinal : A ^ n / n + ((A + β) ^ n - A ^ n) + β ^ n * A ≤ 2 * A ^ n / n := by
    have hmid : (A + β) ^ n - A ^ n ≤ (1 / 500000) * (A ^ n / n) := by
      rw [hAu1]
      have h3 : A ^ n * (1 + u) ^ n - A ^ n = A ^ n * ((1 + u) ^ n - 1) := by ring
      rw [h3]
      have h4 : A ^ n * ((1 + u) ^ n - 1) ≤ A ^ n * (2 * ((n : ℝ) * u)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have h5 : A ^ n * (2 * ((n : ℝ) * u)) ≤ (1 / 500000) * (A ^ n / n) := by
        have h6 : (n : ℝ) * u ≤ 1 / (10 ^ 6 * (n : ℝ)) := by
          calc (n : ℝ) * u ≤ (n : ℝ) * (1 / (10 ^ 6 * (n : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hu_le (by positivity)
            _ = 1 / (10 ^ 6 * (n : ℝ)) := by field_simp
        have hrw : (1 : ℝ) / 500000 * (A ^ n / n) = A ^ n * (2 / (10 ^ 6 * (n : ℝ))) := by
          field_simp
          ring
        rw [hrw, mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < A ^ n)]
        calc 2 * ((n : ℝ) * u) ≤ 2 * (1 / (10 ^ 6 * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left h6 (by norm_num)
          _ = 2 / (10 ^ 6 * (n : ℝ)) := by ring
      linarith
    have hlast : β ^ n * A ≤ (1 / 1000000) * (A ^ n / n) := by
      have h7 : n - 1 + 1 = n := by omega
      have h8 : A ^ n * (β * u ^ (n - 1)) = β ^ n * A := by
        calc A ^ n * (β * u ^ (n - 1)) = β * (A ^ n * u ^ (n - 1)) := by ring
          _ = β * (β ^ (n - 1) * A) := by rw [hAu]
          _ = β ^ n * A := by rw [← mul_assoc, ← pow_succ', h7]
      rw [← h8]
      have h10 : u ^ (n - 1) ≤ u := by
        calc u ^ (n - 1) ≤ u ^ 1 := pow_le_pow_of_le_one hu0 hu1 (by omega)
          _ = u := pow_one u
      have h9 : β * u ^ (n - 1) ≤ 1 / (10 ^ 6 * (n : ℝ)) := by
        have hb : β * u ^ (n - 1) ≤ (n : ℝ) * u := by
          have hb1 : (0 : ℝ) ≤ u ^ (n - 1) := by positivity
          have hb2 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
          exact mul_le_mul hβn h10 hb1 hb2
        have hc : (n : ℝ) * u ≤ 1 / (10 ^ 6 * (n : ℝ)) := by
          calc (n : ℝ) * u ≤ (n : ℝ) * (1 / (10 ^ 6 * (n : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hu_le (le_of_lt hnpos)
            _ = 1 / (10 ^ 6 * (n : ℝ)) := by field_simp
        linarith
      calc A ^ n * (β * u ^ (n - 1)) ≤ A ^ n * (1 / (10 ^ 6 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left h9 (by positivity)
        _ = (1 / 1000000) * (A ^ n / n) := by
            have hn' : (n : ℝ) ≠ 0 := by positivity
            field_simp
            ring
    have hAnn : (0 : ℝ) ≤ A ^ n / n := by positivity
    calc A ^ n / n + ((A + β) ^ n - A ^ n) + β ^ n * A
        ≤ A ^ n / n + (1 / 500000) * (A ^ n / n) + (1 / 1000000) * (A ^ n / n) := by
          linarith [hmid, hlast]
      _ = (1 + 1 / 500000 + 1 / 1000000) * (A ^ n / n) := by ring
      _ ≤ 2 * (A ^ n / n) := by
          refine mul_le_mul_of_nonneg_right ?_ hAnn
          norm_num
      _ = 2 * A ^ n / n := by ring
  calc ∑ m ∈ Finset.range n, (n.choose m : ℝ) * β ^ m
        * (∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ (n - 1 - m))
      + β ^ n * ∑ j ∈ Finset.Icc 1 M, ((j : ℝ))⁻¹
      ≤ A ^ n / n + ((A + β) ^ n - A ^ n) + β ^ n * A := by linarith [hfirst, hharm2]
    _ ≤ 2 * A ^ n / n := hfinal
    _ = 2 * ((M : ℝ) + 1) ^ n / n := by rw [hA]

/-- `exp (1/2) ≤ 2`. -/
lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2)]

/-- `1/2 ≤ log 2`. -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  exact exp_half_le_two

/-- **Upper bound** for the logarithmic lattice sum. -/
lemma logSum_upper (n : ℕ) (hn : 2 ≤ n) {R : ℝ}
    (hR : 10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n) ≤ R) :
    logSum n R ≤ 4 * R ^ n
      * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / n := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set ω : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hω
  have hωnn : 0 ≤ ω := ENNReal.toReal_nonneg
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hbase : (1 : ℝ) ≤ 10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n) := by
    nlinarith [hs1, hn2, sq_nonneg ((n : ℝ) - 2)]
  have hR1 : 1 ≤ R := le_trans hbase hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  set M : ℕ := Nat.ceil R with hM
  have hRM : R ≤ (M : ℝ) := Nat.le_ceil R
  have hMle : (M : ℝ) + 1 ≤ R + 2 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ R by linarith)
    rw [← hM] at h
    linarith
  set β : ℝ := 1 + Real.sqrt n / 2 with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβn : β ≤ n := by
    rw [hβ]
    have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) - 2 := by linarith
    have hsq : (n : ℝ) ≤ (2 * (n : ℝ) - 2) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2), hn2]
    have hsqrt : Real.sqrt n ≤ 2 * (n : ℝ) - 2 := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq h2n] at h
    linarith
  have hMβ : 10 ^ 6 * (n : ℝ) ^ 2 * β ≤ (M : ℝ) + 1 := by
    have h1 : 10 ^ 6 * (n : ℝ) ^ 2 * β ≤ 10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n) := by
      rw [hβ]
      nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg (n : ℝ)]
    linarith [hR, h1, hRM]
  have h1 := logSum_le_sum_card n hn1 hR1
  have h2 : ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (Nat.card {x : Fin n → ℤ //
        (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} : ℝ)
      ≤ ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (((i : ℝ) + 1 + Real.sqrt n / 2) ^ n * ω) := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := card_int_points_le_volume n hn1 (r := (i : ℝ) + 1) (by positivity)
    rwa [← hω] at h
  have h3 : ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (((i : ℝ) + 1 + Real.sqrt n / 2) ^ n * ω)
      = ω * ∑ i ∈ Finset.Icc 1 M, ((i : ℝ) + 1 + Real.sqrt n / 2) ^ n / (i : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h4 : ∑ i ∈ Finset.Icc 1 M, ((i : ℝ) + 1 + Real.sqrt n / 2) ^ n / (i : ℝ)
      ≤ 2 * ((M : ℝ) + 1) ^ n / n := by
    refine le_of_eq_of_le ?_ (inv_mul_pow_sum_le n β M hn hβ0 hβn hMβ)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ] at *
    ring
  have h5 : ω * (2 * ((M : ℝ) + 1) ^ n / n) ≤ 4 * R ^ n * ω / n := by
    have h6 : ((M : ℝ) + 1) ^ n ≤ 2 * R ^ n := by
      have h8 : R + 2 = R * (1 + 2 / R) := by field_simp
      have h9 : (n : ℝ) * (2 / R) ≤ 1 / 2 := by
        have h10 : 4 * (n : ℝ) ≤ R := by
          have h11 : (4 : ℝ) * (n : ℝ) ≤ 10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n) := by
            nlinarith [hs1, hn2]
          linarith [hR, h11]
        have h12 : (n : ℝ) * (2 / R) = 2 * (n : ℝ) / R := by ring
        rw [h12, div_le_iff₀ hRpos]
        linarith
      calc ((M : ℝ) + 1) ^ n ≤ (R + 2) ^ n := pow_le_pow_left₀ (by positivity) hMle n
        _ = (R * (1 + 2 / R)) ^ n := by rw [h8]
        _ = R ^ n * (1 + 2 / R) ^ n := by rw [mul_pow]
        _ ≤ R ^ n * Real.exp ((n : ℝ) * (2 / R)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Commons.Analysis.SpecialFunctions.ExpLog.one_add_pow_le_exp n (2 / R) (by positivity)
        _ ≤ R ^ n * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_trans (Real.exp_le_exp.mpr h9) exp_half_le_two
        _ = 2 * R ^ n := by ring
    have h13 : (0 : ℝ) ≤ 2 * ω / n := by positivity
    calc ω * (2 * ((M : ℝ) + 1) ^ n / n) = (2 * ω / n) * ((M : ℝ) + 1) ^ n := by ring
      _ ≤ (2 * ω / n) * (2 * R ^ n) := mul_le_mul_of_nonneg_left h6 h13
      _ = 4 * R ^ n * ω / n := by ring
  calc logSum n R ≤ ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (Nat.card {x : Fin n → ℤ //
        (∑ j, ((x j : ℝ)) ^ 2) ≤ ((i : ℝ) + 1) ^ 2} : ℝ) := h1
    _ ≤ ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) * (((i : ℝ) + 1 + Real.sqrt n / 2) ^ n * ω) := h2
    _ = ω * ∑ i ∈ Finset.Icc 1 M, ((i : ℝ) + 1 + Real.sqrt n / 2) ^ n / (i : ℝ) := h3
    _ ≤ ω * (2 * ((M : ℝ) + 1) ^ n / n) := mul_le_mul_of_nonneg_left h4 hωnn
    _ ≤ 4 * R ^ n * ω / n := h5

/-- A nonzero integer vector all of whose coordinates lie in `[0,m]` with `m √n ≤ R/2`
contributes at least `log 2` to the logarithmic lattice sum. -/
lemma log_two_le_log_ratio {n m : ℕ} {R : ℝ} {k : Fin n → ℤ} (hk : k ≠ 0)
    (hbox : ∀ i : Fin n, (0 : ℤ) ≤ k i ∧ k i ≤ (m : ℤ))
    (hle2 : (m : ℝ) * Real.sqrt n ≤ R / 2) (hRpos : 0 < R) :
    Real.log 2 ≤ max 0 (Real.log (R / ‖intPt n k‖)) := by
  have hsq : ∑ i, ((k i : ℝ)) ^ 2 ≤ (n : ℝ) * (m : ℝ) ^ 2 := by
    have hb : ∀ i : Fin n, ((k i : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
      intro i
      have h1 : (0 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast (hbox i).1
      have h2 : (k i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hbox i).2
      have h3 := mul_self_le_mul_self h1 h2
      simpa [sq] using h3
    calc ∑ i, ((k i : ℝ)) ^ 2 ≤ ∑ _i : Fin n, (m : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hb i
      _ = (n : ℝ) * (m : ℝ) ^ 2 := by simp
  have hnorm_le : ‖intPt n k‖ ≤ (m : ℝ) * Real.sqrt n := by
    have h2 : ‖intPt n k‖ ^ 2 ≤ (m : ℝ) ^ 2 * (n : ℝ) := by
      rw [norm_intPt_sq]
      linarith [hsq]
    have h3 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul (x := (m : ℝ) ^ 2) (by positivity),
      Real.sqrt_sq (show (0 : ℝ) ≤ (m : ℝ) by positivity)] at h3
    exact h3
  have hnorm_le2 : ‖intPt n k‖ ≤ R / 2 := le_trans hnorm_le hle2
  have hpos : 0 < ‖intPt n k‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_intPt hk)
  have hge2 : 2 ≤ R / ‖intPt n k‖ := by
    rw [le_div_iff₀ hpos]
    linarith
  have hlog : Real.log 2 ≤ Real.log (R / ‖intPt n k‖) := Real.log_le_log (by norm_num) hge2
  have hmax : max 0 (Real.log (R / ‖intPt n k‖)) = Real.log (R / ‖intPt n k‖) :=
    max_eq_right (le_trans (Real.log_nonneg (by norm_num)) hlog)
  rw [hmax]
  exact hlog

/-- **Lower bound** for the logarithmic lattice sum. -/
lemma logSum_lower (n : ℕ) (hn : 2 ≤ n) {R : ℝ}
    (hR : 12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n ≤ R) :
    3 * R ≤ logSum n R := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hbig : (0 : ℝ) < 12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n := by positivity
  have hRpos : 0 < R := lt_of_lt_of_le hbig hR
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ 12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ (Real.sqrt n) ^ n := one_le_pow₀ hs1
      nlinarith [h2, h3]
    linarith [hR, h1]
  set x : ℝ := R / (2 * Real.sqrt n) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  set m : ℕ := Nat.floor x with hm
  have hxm : x < (m : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one x
    rwa [← hm] at h
  have hsn : Real.sqrt n ≤ (n : ℝ) := by
    have hle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h := le_mul_of_one_le_left (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn1)
      simpa [pow_two] using h
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at h
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_floor_iff, hx, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt n)]
    have h2 : (2 : ℝ) * (n : ℝ) ≤ 12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n := by
      have hp1 : (1 : ℝ) ≤ (Real.sqrt n) ^ n := one_le_pow₀ hs1
      have hpn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
        have hlt : (n : ℕ) < 2 ^ n := Nat.lt_two_pow_self
        exact_mod_cast (le_of_lt hlt)
      calc (2 : ℝ) * (n : ℝ) ≤ 12 * (n : ℝ) := by linarith
        _ ≤ 12 * (2 : ℝ) ^ n := by linarith
        _ = 12 * (2 : ℝ) ^ n * 1 := by ring
        _ ≤ 12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n :=
            mul_le_mul_of_nonneg_left hp1 (by positivity)
    linarith [hR, h2, hsn]
  -- the finite set of "box" points
  set K : Finset (Fin n → ℤ) := ((Finset.univ : Finset (Fin n → Fin (m + 1))).image
      (fun f i => ((f i : ℕ) : ℤ))).erase 0 with hKdef
  have hinj : Function.Injective (fun f : Fin n → Fin (m + 1) => fun i => ((f i : ℕ) : ℤ)) := by
    intro f g hfg
    funext i
    have h1 : (f i : ℕ) = (g i : ℕ) := by
      have h := congrFun hfg i
      simp only at h
      exact_mod_cast h
    exact Fin.ext h1
  have hcard_image : ((Finset.univ : Finset (Fin n → Fin (m + 1))).image
      (fun f i => ((f i : ℕ) : ℤ))).card = (m + 1) ^ n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun]
    simp
  have hzero_mem : (0 : Fin n → ℤ) ∈ (Finset.univ : Finset (Fin n → Fin (m + 1))).image
      (fun f i => ((f i : ℕ) : ℤ)) := by
    refine Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, ?_⟩
    ext i
    simp
  have hKcard : K.card = (m + 1) ^ n - 1 := by
    rw [hKdef, Finset.card_erase_of_mem hzero_mem, hcard_image]
  have hterm : ∀ k ∈ K, Real.log 2 ≤ max 0 (Real.log (R / ‖intPt n k‖)) := by
    intro k hk
    rw [hKdef, Finset.mem_erase] at hk
    obtain ⟨hkne, hkimg⟩ := hk
    obtain ⟨f, -, hfk⟩ := Finset.mem_image.mp hkimg
    have hbox : ∀ i : Fin n, (0 : ℤ) ≤ k i ∧ k i ≤ (m : ℤ) := by
      intro i
      rw [← hfk]
      refine ⟨by simp, ?_⟩
      have hfi : (f i : ℕ) ≤ m := Nat.le_of_lt_succ (f i).isLt
      show (((f i : ℕ)) : ℤ) ≤ ((m : ℕ) : ℤ)
      exact_mod_cast hfi
    have hmx : (m : ℝ) ≤ x := by
      rw [hm]
      exact Nat.floor_le (le_of_lt hxpos)
    have hle2 : (m : ℝ) * Real.sqrt n ≤ R / 2 := by
      have h := mul_le_mul_of_nonneg_right hmx (le_of_lt hspos)
      rw [hx] at h
      have h2 : R / (2 * Real.sqrt n) * Real.sqrt n = R / 2 := by
        field_simp
      linarith [h, h2]
    exact log_two_le_log_ratio hkne hbox hle2 hRpos
  have hsum_ge : ∑ k ∈ K, max 0 (Real.log (R / ‖intPt n k‖)) ≤ logSum n R :=
    Summable.sum_le_tsum K (fun k _ => le_max_left _ _) (logSum_summable n hR1)
  have hKsum : (K.card : ℝ) * Real.log 2
      ≤ ∑ k ∈ K, max 0 (Real.log (R / ‖intPt n k‖)) := by
    have h1 : ∑ k ∈ K, Real.log 2 ≤ ∑ k ∈ K, max 0 (Real.log (R / ‖intPt n k‖)) :=
      Finset.sum_le_sum hterm
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  have hpow1 : (1 : ℕ) ≤ (m + 1) ^ n := one_le_pow₀ (by omega : 1 ≤ m + 1)
  have hm2 : (2 : ℝ) ≤ ((m : ℝ) + 1) ^ n := by
    have h1 : (2 : ℕ) ≤ m + 1 := by omega
    have h2 : (2 : ℕ) ≤ (m + 1) ^ n :=
      le_trans h1 (Nat.le_self_pow (by omega : n ≠ 0) (m + 1))
    have h3 : (2 : ℝ) ≤ (((m + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h2
    have hcast : (((m + 1) ^ n : ℕ) : ℝ) = ((m : ℝ) + 1) ^ n := by push_cast; ring
    rwa [hcast] at h3
  have hpow_ge : (R / (2 * Real.sqrt n)) ^ n ≤ ((m : ℝ) + 1) ^ n :=
    pow_le_pow_left₀ (le_of_lt hxpos) (le_of_lt hxm) n
  have hcard_ge : ((m : ℝ) + 1) ^ n - 1 ≤ (K.card : ℝ) := by
    have hcast : (((m + 1) ^ n : ℕ) : ℝ) = ((m : ℝ) + 1) ^ n := by push_cast; ring
    have h1 : ((((m + 1) ^ n - 1 : ℕ)) : ℝ) = ((m : ℝ) + 1) ^ n - 1 := by
      rw [Nat.cast_sub hpow1, Nat.cast_one, hcast]
    rw [hKcard, h1]
  have hk1 : 3 * (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n ≤ R ^ (n - 1) * Real.log 2 := by
    have hRp : R ≤ R ^ (n - 1) := by
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ (n - 1) := pow_le_pow_right₀ hR1 (by omega : 1 ≤ n - 1)
    have hb : 3 * (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n ≤ R * (1 / 2) := by
      have h4 : 3 * (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n
          = 6 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n := by rw [pow_succ]; ring
      rw [h4]
      linarith [hR]
    calc 3 * (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n ≤ R * (1 / 2) := hb
      _ ≤ R ^ (n - 1) * Real.log 2 := by
          refine mul_le_mul hRp half_le_log_two (by norm_num) (by positivity)
  have hk2 : 3 * R ≤ R ^ n * Real.log 2 / ((2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n) := by
    have hden : (0 : ℝ) < (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n := by positivity
    rw [le_div_iff₀ hden]
    have h1 : R ^ n * Real.log 2 = R * (R ^ (n - 1) * Real.log 2) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn1]
    rw [h1]
    calc 3 * R * ((2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n)
        = R * (3 * (2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n) := by ring
      _ ≤ R * (R ^ (n - 1) * Real.log 2) := mul_le_mul_of_nonneg_left hk1 (le_of_lt hRpos)
  have hident : (R / (2 * Real.sqrt n)) ^ n * Real.log 2 / 2
      = R ^ n * Real.log 2 / ((2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n) := by
    rw [div_pow, mul_pow, pow_succ]
    have hden : (0 : ℝ) < (2 : ℝ) ^ n * (Real.sqrt n) ^ n * 2 := by positivity
    field_simp
  calc 3 * R ≤ R ^ n * Real.log 2 / ((2 : ℝ) ^ (n + 1) * (Real.sqrt n) ^ n) := hk2
    _ = (R / (2 * Real.sqrt n)) ^ n * Real.log 2 / 2 := hident.symm
    _ ≤ ((m : ℝ) + 1) ^ n * Real.log 2 / 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hpow_ge (Real.log_nonneg (by norm_num))
    _ ≤ (K.card : ℝ) * Real.log 2 := by
        have h1 : ((m : ℝ) + 1) ^ n / 2 ≤ (K.card : ℝ) := by nlinarith [hcard_ge, hm2]
        calc ((m : ℝ) + 1) ^ n * Real.log 2 / 2 = (((m : ℝ) + 1) ^ n / 2) * Real.log 2 := by ring
          _ ≤ (K.card : ℝ) * Real.log 2 :=
              mul_le_mul_of_nonneg_right h1 (Real.log_nonneg (by norm_num))
    _ ≤ ∑ k ∈ K, max 0 (Real.log (R / ‖intPt n k‖)) := hKsum
    _ ≤ logSum n R := hsum_ge

/-- The logarithmic lattice sum grows at least linearly and at most like the volume. -/
theorem lattice_log_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (3 * R ≤ ∑' k : Fin n → ℤ, max 0 (Real.log (R / ‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : EuclideanSpace ℝ (Fin n))‖))) ∧
      (∑' k : Fin n → ℤ, max 0 (Real.log (R / ‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : EuclideanSpace ℝ (Fin n))‖)))
        ≤ 4 * R ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / n := by
  refine ⟨max (10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n))
    (12 * (2 : ℝ) ^ n * (Real.sqrt n) ^ n), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 10 ^ 6 * (n : ℝ) ^ 2 * (1 + Real.sqrt n) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  · intro R hR
    constructor
    · exact logSum_lower n hn (le_trans (le_max_right _ _) hR)
    · exact logSum_upper n hn (le_trans (le_max_left _ _) hR)

end

end Commons.GeometryOfNumbers.Counting