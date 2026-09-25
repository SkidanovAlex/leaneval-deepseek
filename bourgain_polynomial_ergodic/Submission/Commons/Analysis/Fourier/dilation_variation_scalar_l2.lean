/-
  `Commons.Analysis.Fourier.dilation_variation_scalar_l2`

  Target (Bourgain 1989, *Pointwise ergodic theorems for arithmetic sets*, §3, Lemma 3.28
  specialised to the `L²` case): for every Schwartz window `Ψ` there is `C > 0` such that
  for every `2 < s ≤ 3` and every `g ∈ L² ∩ L^∞`,

      ∫⁻ x, (s-variation over t > 0 of  t ↦ (g * Ψ_t)(x))²  ≤  (C/(s-2))² · ∫⁻ |g|² .

  This file collects the elementary, sorry-free part of the reduction used for that
  statement; the analytic core (Bourgain's `(3.11)`–`(3.14)`) is discussed in
  `STATUS_dilation_variation.md`.
-/
import Mathlib
import Submission.Commons.Analysis.Fourier.fejer_handle_dyadic_variation_l2
import Submission.Commons.Analysis.Fourier.dilation_variation_aemeasurable
import Submission.Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv
import Submission.Commons.Analysis.Fourier.dyadic_square_function_l2
import Submission.Commons.Analysis.Fourier.multiplier_eq_convolution_ae
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

namespace Commons.Analysis.Fourier

open scoped _root_.BigOperators _root_.ENNReal _root_.FourierTransform _root_.Topology _root_.RealInnerProductSpace
open MeasureTheory

/-! ## 1. Numerical inequalities for the variation -/

/-- `ℓ^s ↪ ℓ²` for `s ≥ 2` on a finset, in the form needed for a chain of differences:
the `s`-norm of a finite family of nonnegative numbers is at most its `2`-norm. -/
lemma sum_rpow_le_sum_sq {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ t, 0 ≤ a i)
    {s : ℝ} (hs : 2 ≤ s) :
    (∑ i ∈ t, a i ^ s) ^ (1 / s) ≤ (∑ i ∈ t, a i ^ 2) ^ (1 / 2 : ℝ) := by
  have hs0 : 0 < s := by linarith
  have hs2 : (0:ℝ) ≤ s / 2 - 1 := by linarith
  set P : ℝ := ∑ i ∈ t, a i ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => by positivity
  have hPs : 0 ≤ ∑ i ∈ t, a i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  -- `a i ^ s = (a i ^ 2) ^ (s/2)`
  have hsq : ∀ i, 0 ≤ a i → a i ^ s = (a i ^ 2) ^ (s / 2 : ℝ) := by
    intro i hi
    have h2 : a i ^ (2 : ℝ) = a i ^ 2 := Real.rpow_natCast (a i) 2
    rw [← h2, ← Real.rpow_mul hi 2 (s / 2)]
    congr 1
    ring
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  · -- degenerate case: all terms vanish
    have hall : ∀ i ∈ t, a i = 0 := by
      intro i hi
      have h2 : a i ^ 2 ≤ P :=
        Finset.single_le_sum (f := fun i => a i ^ 2) (fun j _ => by positivity) hi
      have hzero : a i ^ 2 = 0 := le_antisymm (by simpa [hPz] using h2) (by positivity)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    have hz : ∑ i ∈ t, a i ^ s = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hall i hi]
      exact Real.zero_rpow hs0.ne'
    rw [hz, Real.zero_rpow (by positivity : (1:ℝ)/s ≠ 0)]
    positivity
  · have hterm : ∀ i ∈ t, a i ^ s ≤ P ^ (s / 2 - 1) * a i ^ 2 := by
      intro i hi
      have hai : 0 ≤ a i := ha i hi
      have h2 : a i ^ 2 ≤ P :=
        Finset.single_le_sum (f := fun i => a i ^ 2) (fun j _ => by positivity) hi
      rcases eq_or_lt_of_le hai with h | h
      · rw [← h, Real.zero_rpow hs0.ne']
        positivity
      · have hid : (a i ^ 2) ^ (s / 2 : ℝ) = (a i ^ 2) ^ (s / 2 - 1) * a i ^ 2 := by
          conv_lhs => rw [show (s / 2 : ℝ) = (s / 2 - 1) + 1 by ring]
          rw [Real.rpow_add (by positivity : (0:ℝ) < a i ^ 2) (s / 2 - 1) 1, Real.rpow_one]
        rw [hsq i hai, hid]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) h2 hs2) (by positivity)
    have hsum : (∑ i ∈ t, a i ^ s) ≤ P ^ (s / 2) := by
      calc (∑ i ∈ t, a i ^ s) ≤ ∑ i ∈ t, P ^ (s / 2 - 1) * a i ^ 2 := Finset.sum_le_sum hterm
        _ = P ^ (s / 2 - 1) * P := by rw [Finset.mul_sum]
        _ = P ^ (s / 2) := by
            rw [show P ^ (s / 2 - 1) * P = P ^ (s / 2 - 1) * P ^ (1 : ℝ) by rw [Real.rpow_one],
              ← Real.rpow_add hPpos (s / 2 - 1) 1]
            congr 1
            ring
    calc (∑ i ∈ t, a i ^ s) ^ (1 / s)
        ≤ ((∑ i ∈ t, a i ^ 2) ^ (s / 2)) ^ (1 / s) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) s)
            (by simpa [hP] using hsum) (by positivity)
      _ = (∑ i ∈ t, a i ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hPs]
          congr 1
          field_simp



/-- **Weighted Minkowski for the `ℓ^s`-norm.**  For nonnegative weights `w` and real numbers
`d i j`, the `ℓ^s`-norm (in `j`) of the weighted sum `∑ i, w i * d i j` is at most the weighted
sum of the `ℓ^s`-norms.  This is the algebraic step "the variation of an average of families is at
most the average of the variations" (Bourgain's `(3.13)` transference step). -/
lemma sum_mul_Lp_le {ι : Type*} (t : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i)
    (d : ι → ℕ → ℝ) {s : ℝ} (hs : 1 ≤ s) (J : ℕ) :
    (∑ j ∈ Finset.range J, |∑ i ∈ t, w i * d i j| ^ s) ^ (1 / s)
      ≤ ∑ i ∈ t, w i * (∑ j ∈ Finset.range J, |d i j| ^ s) ^ (1 / s) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, abs_zero, Real.zero_rpow (by linarith : s ≠ 0),
        Finset.sum_const, smul_zero, Real.zero_rpow (by positivity : (1:ℝ) / s ≠ 0)]
      exact le_refl 0
  | insert i₀ t h₀ ih =>
      have hw₀ : 0 ≤ w i₀ := hw i₀ (Finset.mem_insert_self i₀ t)
      have hwt : ∀ i ∈ t, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
      have hinner : ∀ j, (∑ i ∈ insert i₀ t, w i * d i j)
          = w i₀ * d i₀ j + ∑ i ∈ t, w i * d i j := fun j => Finset.sum_insert h₀
      rw [Finset.sum_insert h₀]
      have hstep := Real.Lp_add_le (Finset.range J) (fun j => w i₀ * d i₀ j)
        (fun j => ∑ i ∈ t, w i * d i j) hs
      have hhom : (∑ j ∈ Finset.range J, |w i₀ * d i₀ j| ^ s) ^ (1 / s)
          = w i₀ * (∑ j ∈ Finset.range J, |d i₀ j| ^ s) ^ (1 / s) := by
        have h1 : ∀ j, |w i₀ * d i₀ j| ^ s = w i₀ ^ s * |d i₀ j| ^ s := by
          intro j
          rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_nonneg hw₀]
        have hsum : (∑ j ∈ Finset.range J, |w i₀ * d i₀ j| ^ s)
            = w i₀ ^ s * ∑ j ∈ Finset.range J, |d i₀ j| ^ s := by
          simp only [h1, ← Finset.mul_sum]
        rw [hsum, Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_mul hw₀, mul_one_div, div_self (by linarith : s ≠ 0), Real.rpow_one]
      calc (∑ j ∈ Finset.range J, |∑ i ∈ insert i₀ t, w i * d i j| ^ s) ^ (1 / s)
          = (∑ j ∈ Finset.range J,
              |w i₀ * d i₀ j + ∑ i ∈ t, w i * d i j| ^ s) ^ (1 / s) := by
            congr 1
            exact Finset.sum_congr rfl fun j _ => by rw [hinner j]
        _ ≤ (∑ j ∈ Finset.range J, |w i₀ * d i₀ j| ^ s) ^ (1 / s)
              + (∑ j ∈ Finset.range J, |∑ i ∈ t, w i * d i j| ^ s) ^ (1 / s) := hstep
        _ ≤ w i₀ * (∑ j ∈ Finset.range J, |d i₀ j| ^ s) ^ (1 / s)
              + ∑ i ∈ t, w i * (∑ j ∈ Finset.range J, |d i j| ^ s) ^ (1 / s) := by
            rw [hhom]
            exact add_le_add_right (ih hwt)
              (w i₀ * (∑ j ∈ Finset.range J, |d i₀ j| ^ s) ^ (1 / s))


/-- Nonnegative form of `sum_mul_Lp_le` (the `|·|` on the inner sum is redundant). -/
lemma sum_mul_Lp_le_of_nonneg {ι : Type*} (t : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i)
    (d : ι → ℕ → ℝ) (hd : ∀ i j, 0 ≤ d i j) {s : ℝ} (hs : 1 ≤ s) (J : ℕ) :
    (∑ j ∈ Finset.range J, (∑ i ∈ t, w i * d i j) ^ s) ^ (1 / s)
      ≤ ∑ i ∈ t, w i * (∑ j ∈ Finset.range J, d i j ^ s) ^ (1 / s) := by
  have h := sum_mul_Lp_le t w hw d hs J
  have e1 : (∑ j ∈ Finset.range J, |∑ i ∈ t, w i * d i j| ^ s)
      = ∑ j ∈ Finset.range J, (∑ i ∈ t, w i * d i j) ^ s :=
    Finset.sum_congr rfl fun j _ =>
      congrArg (fun x : ℝ => x ^ s)
        (abs_of_nonneg (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hd i j)))
  have e2 : ∀ i, (∑ j ∈ Finset.range J, |d i j| ^ s) = ∑ j ∈ Finset.range J, d i j ^ s :=
    fun i => Finset.sum_congr rfl fun j _ => congrArg (fun x : ℝ => x ^ s) (abs_of_nonneg (hd i j))
  rw [e1] at h
  simpa only [e2] using h

/-- **Minkowski for the `v_s`-variation.**  The `s`-variation (supremum over increasing chains)
of a weighted average of families is at most the weighted average of the `s`-variations:

  `V_s(∑_i w_i A_i) ≤ ∑_i w_i V_s(A_i)`   for `w ≥ 0`, `s ≥ 1`.

This is the step of the Fejér-handle proof (`fejer_handle_dyadic_variation_l2`) in which the
averaging over the grid offsets `θ` commutes with the variation. -/
lemma chain_average_le {ι : Type*} (t : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i)
    (A : ι → ℕ → ℂ) {s : ℝ} (hs : 1 ≤ s) (u : ℕ → ℕ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
        ‖(∑ i ∈ t, w i * A i (u (j + 1))) - (∑ i ∈ t, w i * A i (u j))‖ ^ s) ^ (1 / s)
      ≤ ∑ i ∈ t, w i * (∑ j ∈ Finset.range J,
          ‖A i (u (j + 1)) - A i (u j)‖ ^ s) ^ (1 / s) := by
  classical
  have hlin : ∀ j, (∑ i ∈ t, w i * A i (u (j + 1))) - (∑ i ∈ t, w i * A i (u j))
      = ∑ i ∈ t, w i * (A i (u (j + 1)) - A i (u j)) := by
    intro j
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hpoint : ∀ j, ‖∑ i ∈ t, w i * (A i (u (j + 1)) - A i (u j))‖
      ≤ ∑ i ∈ t, w i * ‖A i (u (j + 1)) - A i (u j)‖ := by
    intro j
    calc ‖∑ i ∈ t, w i * (A i (u (j + 1)) - A i (u j))‖
        ≤ ∑ i ∈ t, ‖w i * (A i (u (j + 1)) - A i (u j))‖ := norm_sum_le _ _
      _ = ∑ i ∈ t, w i * ‖A i (u (j + 1)) - A i (u j)‖ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [norm_mul]
          simp [abs_of_nonneg (hw i hi)]
  have h1 : (∑ j ∈ Finset.range J,
        ‖∑ i ∈ t, w i * (A i (u (j + 1)) - A i (u j))‖ ^ s) ^ (1 / s)
      ≤ (∑ j ∈ Finset.range J,
          (∑ i ∈ t, w i * ‖A i (u (j + 1)) - A i (u j)‖) ^ s) ^ (1 / s) := by
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => by positivity)
      (Finset.sum_le_sum fun j _ => Real.rpow_le_rpow (norm_nonneg _) (hpoint j) (by linarith))
      (by positivity)
  have h2 := sum_mul_Lp_le_of_nonneg t w hw (fun i j => ‖A i (u (j + 1)) - A i (u j)‖)
    (fun i j => norm_nonneg _) hs J
  have h2' : (∑ j ∈ Finset.range J,
        (∑ i ∈ t, w i * ‖A i (u (j + 1)) - A i (u j)‖) ^ s) ^ (1 / s)
      ≤ ∑ i ∈ t, w i * (∑ j ∈ Finset.range J,
          ‖A i (u (j + 1)) - A i (u j)‖ ^ s) ^ (1 / s) := by
    exact h2
  calc (∑ j ∈ Finset.range J,
        ‖(∑ i ∈ t, w i * A i (u (j + 1))) - (∑ i ∈ t, w i * A i (u j))‖ ^ s) ^ (1 / s)
      = (∑ j ∈ Finset.range J,
        ‖∑ i ∈ t, w i * (A i (u (j + 1)) - A i (u j))‖ ^ s) ^ (1 / s) := by
          simp only [hlin]
    _ ≤ ∑ i ∈ t, w i * (∑ j ∈ Finset.range J,
          ‖A i (u (j + 1)) - A i (u j)‖ ^ s) ^ (1 / s) := le_trans h1 h2'


/-- **Subadditivity of the chain quantity.**  The `ℓ^s`-norm of the sums of two families is at most
the sum of the `ℓ^s`-norms: `‖a + b‖_{ℓ^s} ≤ ‖a‖_{ℓ^s} + ‖b‖_{ℓ^s}`.  This is the elementary step
behind "the `v_s`-variation of a sum of families is at most the sum of the variations", used when a
window `Ψ` is split into a handle plus a mean-zero remainder. -/
lemma chain_add_Lp_le {ι : Type*} (t : Finset ι) (a b : ι → ℂ) {s : ℝ} (hs : 1 ≤ s) :
    (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1 / s)
      ≤ (∑ i ∈ t, ‖a i‖ ^ s) ^ (1 / s) + (∑ i ∈ t, ‖b i‖ ^ s) ^ (1 / s) := by
  have h1 : (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1 / s)
      ≤ (∑ i ∈ t, (‖a i‖ + ‖b i‖) ^ s) ^ (1 / s) := by
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by linarith))
      (by positivity)
  have h2 := Real.Lp_add_le t (fun i => ‖a i‖) (fun i => ‖b i‖) hs
  calc (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1 / s)
      ≤ (∑ i ∈ t, (‖a i‖ + ‖b i‖) ^ s) ^ (1 / s) := h1
    _ = (∑ i ∈ t, |‖a i‖ + ‖b i‖| ^ s) ^ (1 / s) := by
        simp only [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (∑ i ∈ t, |‖a i‖| ^ s) ^ (1 / s) + (∑ i ∈ t, |‖b i‖| ^ s) ^ (1 / s) := h2
    _ = (∑ i ∈ t, ‖a i‖ ^ s) ^ (1 / s) + (∑ i ∈ t, ‖b i‖ ^ s) ^ (1 / s) := by
        simp only [abs_of_nonneg (norm_nonneg _)]

/-! ## 2. The target statement (Bourgain 1989, §3, Lemmas 3.11/3.28, `L²` case)

The analytic core (the variational estimate for the dilates of a Schwartz window) is reduced in
`STATUS_dilation_variation.md`.  The elementary input proved above (`sum_rpow_le_sum_sq`, the
`ℓ^s ↪ ℓ²` comparison for chains of differences) is used at every step of that reduction. -/

/-- `ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2:ℝ)`. -/
lemma ofReal_norm_sq_enorm {E : Type*} [NormedAddCommGroup E] (z : E) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2:ℝ) := by
  rw [Commons.Analysis.Fourier.enorm_eq_ofReal_norm_aux,
    Commons.Analysis.Fourier.rpow_two_eq_sq, ← ENNReal.ofReal_pow (norm_nonneg z) 2]

/-- **`ℓ^s`-variation of a sequence is dominated by the `ℓ²`-norm of its values** (`s ≥ 2`).
For `s > 2` the `v_s`-norm over chains is at most `2` times the `ℓ²`-norm of the values. -/
lemma chain_variation_le_tsum {E : Type*} [NormedAddCommGroup E] (a : ℤ → E) {s : ℝ} (hs : 2 ≤ s)
    (J : ℕ) (k : Fin (J + 1) → ℤ) (hk : StrictMono k) :
    ENNReal.ofReal ((∑ j : Fin J,
        ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ (1/s))
      ≤ 2 * (∑' l : ℤ, ‖a l‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
  classical
  have hk_inj : Function.Injective k := hk.injective
  set S : ℝ := ∑ i : Fin (J+1), ‖a (k i)‖ ^ (2:ℕ) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  set M : ℝ := S ^ (1/2 : ℝ) with hM
  have hMnn : 0 ≤ M := Real.rpow_nonneg hSnn _
  have hMsq : M ^ (2:ℕ) = S := by
    rw [hM, ← Real.rpow_natCast (S ^ (1/2:ℝ)) 2, ← Real.rpow_mul hSnn]; norm_num
  have hval : ∀ i : Fin (J+1), ‖a (k i)‖ ≤ M := by
    intro i
    have h1 : ‖a (k i)‖ ^ (2:ℕ) ≤ S :=
      Finset.single_le_sum (f := fun i => ‖a (k i)‖ ^ (2:ℕ)) (fun j _ => by positivity)
        (Finset.mem_univ i)
    calc ‖a (k i)‖ = (‖a (k i)‖ ^ (2:ℕ)) ^ (1/2:ℝ) := by
          rw [← Real.rpow_natCast ‖a (k i)‖ 2, ← Real.rpow_mul (norm_nonneg _)]; norm_num
      _ ≤ (M ^ (2:ℕ)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow (by positivity) (by rw [hMsq]; exact h1) (by norm_num)
      _ = M := by rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hMnn]; norm_num
  have hQ : ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℕ) ≤ 4 * M^2 := by
    have hstep : ∀ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℕ)
        ≤ 2 * (‖a (k (Fin.castSucc j))‖ ^ (2:ℕ) + ‖a (k (Fin.succ j))‖ ^ (2:ℕ)) := by
      intro j
      have h1 : (‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖) ^ (2:ℕ)
          = ‖a (k (Fin.castSucc j))‖^2 + 2*(‖a (k (Fin.castSucc j))‖*‖a (k (Fin.succ j))‖)
            + ‖a (k (Fin.succ j))‖^2 := by ring
      have h2 : 2*(‖a (k (Fin.castSucc j))‖*‖a (k (Fin.succ j))‖)
          ≤ ‖a (k (Fin.castSucc j))‖^2 + ‖a (k (Fin.succ j))‖^2 := by
        have := two_mul_le_add_sq ‖a (k (Fin.castSucc j))‖ ‖a (k (Fin.succ j))‖
        linarith [this]
      calc ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℕ)
          ≤ (‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖) ^ (2:ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
        _ ≤ 2 * (‖a (k (Fin.castSucc j))‖ ^ (2:ℕ) + ‖a (k (Fin.succ j))‖ ^ (2:ℕ)) := by
            rw [h1]; nlinarith [h2]
    have h1 : ∑ j : Fin J, ‖a (k (Fin.castSucc j))‖ ^ (2:ℕ) ≤ S := by
      rw [hS, Fin.sum_univ_castSucc]; exact le_add_of_nonneg_right (by positivity)
    have h2 : ∑ j : Fin J, ‖a (k (Fin.succ j))‖ ^ (2:ℕ) ≤ S := by
      rw [hS, Fin.sum_univ_succ]; exact le_add_of_nonneg_left (by positivity)
    calc ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℕ)
        ≤ ∑ j : Fin J, 2 * (‖a (k (Fin.castSucc j))‖ ^ (2:ℕ) + ‖a (k (Fin.succ j))‖ ^ (2:ℕ)) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = 2 * ((∑ j : Fin J, ‖a (k (Fin.castSucc j))‖ ^ (2:ℕ))
              + (∑ j : Fin J, ‖a (k (Fin.succ j))‖ ^ (2:ℕ))) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ 4 * M^2 := by
          have h3 : (∑ j : Fin J, ‖a (k (Fin.castSucc j))‖ ^ (2:ℕ))
              + (∑ j : Fin J, ‖a (k (Fin.succ j))‖ ^ (2:ℕ)) ≤ 2 * M^2 := by
            have : (2:ℝ) * M^2 = S + S := by rw [hMsq]; ring
            linarith [h1, h2, this]
          linarith [h3]
  have hmain : ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s ≤ 2^s * M^s := by
    have hterm : ∀ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s
        ≤ (2*M)^(s-2) * ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℝ) := by
      intro j
      set d := ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ with hd
      have hdnn : 0 ≤ d := norm_nonneg _
      have hdle : d ≤ 2 * M := by
        calc d ≤ ‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hval _) (hval _)
          _ = 2 * M := by ring
      have hs2 : (0:ℝ) ≤ s - 2 := by linarith
      have hsp : d^s = d^(s-2) * d^(2:ℝ) := by
        have h := Real.rpow_add_of_nonneg (x := d) (y := s-2) (z := 2) hdnn hs2
          (show (0:ℝ) ≤ 2 by norm_num)
        conv_lhs => rw [show s = (s-2)+2 by ring]
        exact h
      rw [hsp]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (z := s-2) hdnn hdle hs2) (by positivity)
    calc ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s
        ≤ ∑ j : Fin J, (2*M)^(s-2) * ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℝ) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (2*M)^(s-2) * ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (2*M)^(s-2) * (4 * M^2) := by
          have he : (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℝ))
              = ∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ (2:ℕ) :=
            Finset.sum_congr rfl fun j _ => Real.rpow_natCast _ 2
          rw [he]; exact mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = 2^s * M^s := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hMnn]
          have h4 : (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
          have h2 : (2:ℝ)^(s-2) * (2:ℝ)^(2:ℕ) = 2^s := by
            rw [← Real.rpow_natCast (2:ℝ) 2,
              ← Real.rpow_add_of_nonneg (x := (2:ℝ)) (y := s-2) (z := ((2:ℕ):ℝ))
                (by norm_num) (by linarith) (by norm_num)]
            congr 1; ring
          have hM' : M^(s-2) * M^(2:ℕ) = M^s := by
            rw [← Real.rpow_natCast M 2,
              ← Real.rpow_add_of_nonneg (x := M) (y := s-2) (z := ((2:ℕ):ℝ))
                hMnn (by linarith) (by norm_num)]
            congr 1; ring
          have key : (2:ℝ)^(s-2) * M^(s-2) * (4 * M^2)
              = ((2:ℝ)^(s-2) * (2:ℝ)^(2:ℕ)) * (M^(s-2) * M^(2:ℕ)) := by
            rw [h4]; ring
          rw [key, h2, hM']
  have hreal : (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ (1/s) ≤ 2 * M := by
    calc (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ (1/s)
        ≤ (2^s * M^s) ^ (1/s) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) hmain (by positivity)
      _ = 2 * M := by
          rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) s) (Real.rpow_nonneg hMnn s)]
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul hMnn]
          rw [show s * (1/s) = 1 by field_simp]
          simp
  have hMenn : ENNReal.ofReal M = (∑ i : Fin (J+1), ‖a (k i)‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
    rw [hM, ← ENNReal.ofReal_rpow_of_nonneg hSnn (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact Finset.sum_congr rfl fun i _ => ofReal_norm_sq_enorm _
  calc ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ (1/s))
      ≤ ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    _ = 2 * (∑ i : Fin (J+1), ‖a (k i)‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by rw [hMenn]
    _ ≤ 2 * (∑' l : ℤ, ‖a l‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
        refine mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow ?_ (by norm_num)) (by norm_num)
        rw [← Finset.sum_image (s := Finset.univ) (g := k) (f := fun l : ℤ => ‖a l‖ₑ ^ (2:ℝ))
          (fun x _ y _ hxy => hk_inj hxy)]
        exact ENNReal.sum_le_tsum _


/-! ## 3. The dyadic samples, the level function, and the bookkeeping reduction

We reduce the variation over *all* chains of positive reals to (i) the variation over the dyadic
samples `2^l` and (ii) the `ℓ²`-sum over the dyadic levels `[2^l, 2^{l+1}]` of the level
"total variations" `∫_{2^l}^{2^{l+1}} h`.

For a family `α` whose increments are dominated by a nonnegative `h` via the fundamental theorem
of calculus (`‖α y - α x‖ ≤ ∫_x^y h`), the chain is decomposed according to the level of its
points: the within-level jumps and the boundary chords are bounded by the level integrals of `h`,
while the "long" jumps are bounded by the dyadic samples of `α`.
-/

/-- Integer level of a positive real: the unique `l : ℤ` with `2^l ≤ t < 2^(l+1)`. -/
noncomputable def lev (t : ℝ) : ℤ := ⌊Real.logb 2 t⌋

lemma zpow_two_lev_le (t : ℝ) (ht : 0 < t) : (2:ℝ)^(lev t) ≤ t := by
  have h : ((lev t : ℝ)) ≤ Real.logb 2 t := Int.floor_le _
  have h1 : (2:ℝ)^((lev t : ℝ)) ≤ (2:ℝ)^(Real.logb 2 t) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  rw [Real.rpow_logb (by norm_num) (by norm_num) ht] at h1
  rwa [Real.rpow_intCast] at h1

lemma lt_zpow_two_lev_succ (t : ℝ) (ht : 0 < t) : t < (2:ℝ)^(lev t + 1) := by
  have h : Real.logb 2 t < ((lev t : ℝ)) + 1 := Int.lt_floor_add_one _
  have h1 : (2:ℝ)^(Real.logb 2 t) < (2:ℝ)^(((lev t : ℝ)) + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
  rw [Real.rpow_logb (by norm_num) (by norm_num) ht] at h1
  rw [← Real.rpow_intCast (2:ℝ) (lev t + 1)]
  have h2 : (((lev t + 1 : ℤ) : ℝ)) = ((lev t : ℝ)) + 1 := by push_cast; ring
  rw [h2]; exact h1

lemma lev_mono {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) : lev t ≤ lev u := by
  have hu : 0 < u := lt_of_lt_of_le ht htu
  by_contra h
  push_neg at h
  have h1 : lev u + 1 ≤ lev t := by omega
  have h2 : (2:ℝ)^(lev u + 1) ≤ (2:ℝ)^(lev t) := by
    apply zpow_le_zpow_right₀ (by norm_num) h1
  have h3 : u < (2:ℝ)^(lev u + 1) := lt_zpow_two_lev_succ u hu
  have h4 : (2:ℝ)^(lev t) ≤ t := zpow_two_lev_le t ht
  linarith



/-- The triangular (de la Vallée-Poussin) kernel `Λ x = max 0 (1 - |x|)` has total mass `1`. -/
lemma integral_triangular_kernel : ∫ x : ℝ, max 0 (1 - |x|) = 1 := by
  have hf : ∀ x ∉ Set.Icc (-1:ℝ) 1, max 0 (1 - |x|) = 0 := by
    intro x hx
    have hx' : 1 ≤ |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [max_eq_left]; linarith
  have h1 : ∫ x in Set.Icc (-1:ℝ) 1, max 0 (1 - |x|) = ∫ x : ℝ, max 0 (1 - |x|) :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hf
  have hcont : Continuous fun x : ℝ => max 0 (1 - |x|) := by fun_prop
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => max 0 (1 - |x|)) MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [← h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-1) 0) (hI 0 1)]
  have e1 : (∫ x in (-1:ℝ)..0, max 0 (1 - |x|)) = ∫ x in (-1:ℝ)..0, (1 + x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hx
    change max 0 (1 - |x|) = 1 + x
    rw [abs_of_nonpos hx.2, show (1:ℝ) - -x = 1 + x by ring,
      max_eq_right (by linarith [hx.1])]
  have e2 : (∫ x in (0:ℝ)..1, max 0 (1 - |x|)) = ∫ x in (0:ℝ)..1, (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
    change max 0 (1 - |x|) = 1 - x
    rw [abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]
  rw [e1, e2]
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (by exact (continuous_id.intervalIntegrable _ _)),
      intervalIntegral.integral_const, integral_id]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const) (by exact (continuous_id.intervalIntegrable _ _)),
      intervalIntegral.integral_const, integral_id]
  norm_num

section Bookkeeping

variable {E : Type*} [NormedAddCommGroup E]

/-- The dyadic `s`-variation of a family `α` over strictly increasing `Fin`-chains in `ℤ`. -/
noncomputable def dyadicVar (α : ℝ → E) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (k : Fin (J+1) → ℤ), ⨆ (_ : StrictMono k),
    ENNReal.ofReal ((∑ j : Fin J,
      ‖α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j)))‖ ^ s) ^ (1/s))

lemma dyadicVar_le_def (α : ℝ → E) (s : ℝ) (J : ℕ) (k : Fin (J+1) → ℤ) (hk : StrictMono k) :
    ENNReal.ofReal ((∑ j : Fin J,
        ‖α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j)))‖ ^ s) ^ (1/s))
      ≤ dyadicVar α s :=
  le_iSup_of_le J (le_iSup_of_le k (le_iSup (fun _ : StrictMono k => ENNReal.ofReal _) hk))

lemma nondecr_chain_le (α : ℝ → E) {s : ℝ} (hs : 0 < s) (e : ℕ → ℤ) (he : Monotone e) :
    ∀ N : ℕ, ENNReal.ofReal ((∑ i ∈ Finset.range N, ‖α ((2:ℝ)^(e i)) - α ((2:ℝ)^(e (i+1)))‖ ^ s) ^ (1/s))
      ≤ dyadicVar α s := by
  have key : ∀ N, ∃ (m : ℕ) (k : Fin (m+1) → ℤ), StrictMono k ∧ k (Fin.last m) = e N ∧
      (∑ i ∈ Finset.range N, ‖α ((2:ℝ)^(e i)) - α ((2:ℝ)^(e (i+1)))‖ ^ s)
        ≤ ∑ j : Fin m, ‖α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j)))‖ ^ s := by
    intro N
    induction N with
    | zero =>
        refine ⟨0, fun _ => e 0, fun a b hab => absurd hab (by omega), rfl, ?_⟩
        simp
    | succ N ih =>
        obtain ⟨m, k, hk, hklast, hineq⟩ := ih
        by_cases hc : e (N+1) = e N
        · refine ⟨m, k, hk, by rw [hc]; exact hklast, ?_⟩
          rw [Finset.sum_range_succ]
          have hz : ‖α ((2:ℝ)^(e N)) - α ((2:ℝ)^(e (N+1)))‖ ^ s = 0 := by
            rw [hc, sub_self, norm_zero]; exact Real.zero_rpow (ne_of_gt hs)
          rw [hz, add_zero]; exact hineq
        · have hlt : e N < e (N+1) := lt_of_le_of_ne (he (Nat.le_succ N)) (fun h => hc h.symm)
          set k' : Fin (m+2) → ℤ := fun i => if h : (i:ℕ) < m+1 then k ⟨i, h⟩ else e (N+1) with hk'def
          have key_cs : ∀ i : Fin (m+1), k' i.castSucc = k i := by
            intro i
            have h : ((i.castSucc : Fin (m+2)) : ℕ) < m+1 := by simp [Fin.val_castSucc, i.isLt]
            rw [hk'def]; simp only [dif_pos h]
            exact congrArg k (Fin.ext rfl)
          have key_last : k' (Fin.last (m+1)) = e (N+1) := by
            have h : ¬ ((Fin.last (m+1) : Fin (m+2)) : ℕ) < m+1 := by simp
            rw [hk'def]; simp only [dif_neg h]
          have key_mono : StrictMono k' := by
            intro a b hab
            rw [Fin.lt_def] at hab
            by_cases ha : (a:ℕ) < m+1
            · rw [show k' a = k ⟨a.val, ha⟩ from by rw [hk'def]; simp only [dif_pos ha]]
              by_cases hb : (b:ℕ) < m+1
              · rw [show k' b = k ⟨b.val, hb⟩ from by rw [hk'def]; simp only [dif_pos hb]]
                exact hk (by rw [Fin.lt_def]; exact hab)
              · rw [show k' b = e (N+1) from by rw [hk'def]; simp only [dif_neg hb]]
                have h1 : k ⟨a.val, ha⟩ ≤ k (Fin.last m) :=
                  hk.monotone (by rw [Fin.le_def]; simp only [Fin.val_mk, Fin.val_last]; omega)
                rw [hklast] at h1
                exact lt_of_le_of_lt h1 hlt
            · exfalso; have := a.isLt; omega
          refine ⟨m+1, k', key_mono, key_last, ?_⟩
          rw [Finset.sum_range_succ, Fin.sum_univ_castSucc]
          have hsum : (∑ j : Fin m, ‖α ((2:ℝ)^(k' ((j.castSucc : Fin (m+1)).castSucc)))
                - α ((2:ℝ)^(k' ((j.castSucc : Fin (m+1)).succ)))‖ ^ s)
              = ∑ j : Fin m, ‖α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j)))‖ ^ s := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have h1 : k' ((j.castSucc : Fin (m+1)).castSucc) = k (j.castSucc) := by
              have h : (((j.castSucc : Fin (m+1)).castSucc : Fin (m+2)) : ℕ) < m+1 := by
                simp [Fin.val_castSucc, j.isLt]
              rw [hk'def]; simp only [dif_pos h]
              exact congrArg k (Fin.ext rfl)
            have h2 : k' ((j.castSucc : Fin (m+1)).succ) = k (j.succ) := by
              have h : (((j.castSucc : Fin (m+1)).succ : Fin (m+2)) : ℕ) < m+1 := by
                simp [Fin.val_succ]
              have e1 : k' (((j.castSucc : Fin (m+1)).succ : Fin (m+2)))
                  = k ⟨((j.castSucc : Fin (m+1)).succ : Fin (m+2)), h⟩ := by
                rw [hk'def]; exact dif_pos h
              rw [e1]
              exact congrArg k (Fin.ext rfl)
            rw [h1, h2]
          have hlast : ‖α ((2:ℝ)^(k' ((Fin.last m : Fin (m+1)).castSucc)))
              - α ((2:ℝ)^(k' ((Fin.last m : Fin (m+1)).succ)))‖ ^ s
              = ‖α ((2:ℝ)^(e N)) - α ((2:ℝ)^(e (N+1)))‖ ^ s := by
            have h1 : k' ((Fin.last m : Fin (m+1)).castSucc) = e N := by
              have h : (((Fin.last m : Fin (m+1)).castSucc : Fin (m+2)) : ℕ) < m+1 := by
                simp
              rw [show k' ((Fin.last m : Fin (m+1)).castSucc)
                  = k ⟨((Fin.last m : Fin (m+1)).castSucc : Fin (m+2)), h⟩ from by
                rw [hk'def]; simp only [dif_pos h]]
              rw [show (⟨((Fin.last m : Fin (m+1)).castSucc : Fin (m+2)), h⟩ : Fin (m+1))
                  = Fin.last m from Fin.ext rfl, hklast]
            have h2 : k' ((Fin.last m : Fin (m+1)).succ) = e (N+1) := by
              have h : ¬ ((((Fin.last m : Fin (m+1)).succ : Fin (m+2))) : ℕ) < m+1 := by simp
              rw [show k' ((Fin.last m : Fin (m+1)).succ) = e (N+1) from by
                rw [hk'def]; simp only [dif_neg h]]
            rw [h1, h2]
          rw [hsum, hlast]
          linarith [hineq]
  intro N
  obtain ⟨m, k, hk, -, hineq⟩ := key N
  have h1 : ENNReal.ofReal ((∑ i ∈ Finset.range N, ‖α ((2:ℝ)^(e i)) - α ((2:ℝ)^(e (i+1)))‖ ^ s) ^ (1/s))
      ≤ ENNReal.ofReal ((∑ j : Fin m,
          ‖α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j)))‖ ^ s) ^ (1/s)) :=
    ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) hineq (by positivity))
  exact h1.trans (dyadicVar_le_def α s m k hk)

/-- Interval integrability is symmetric in the endpoints, so a hypothesis giving it for
`0 < x ≤ y` gives it for all pairs of positive endpoints. -/
lemma intervalIntegrable_of_pos {h : ℝ → ℝ}
    (hint : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable h MeasureTheory.volume x y) :
    ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y := by
  intro x y hx hy
  rcases le_total x y with h | h
  · exact hint x y hx h
  · exact (hint y x hy h).symm

/-- A sub-interval of a dyadic level has smaller `h`-integral than the whole level, for
nonnegative `h`. -/
lemma interval_integral_le_level (h : ℝ → ℝ) (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (l : ℤ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxlo : (2:ℝ)^l ≤ x) (hxy : x ≤ y) (hyhi : y ≤ (2:ℝ)^(l+1)) :
    (∫ t in x..y, h t) ≤ ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t := by
  have hL : 0 < (2:ℝ)^l := zpow_pos (by norm_num) l
  have hU : (2:ℝ)^l ≤ (2:ℝ)^(l+1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hUpos : 0 < (2:ℝ)^(l+1) := lt_of_lt_of_le hL hU
  have hLy : (2:ℝ)^l ≤ y := le_trans hxlo hxy
  have h1 : (∫ t in ((2:ℝ)^l)..y, h t)
      = (∫ t in ((2:ℝ)^l)..x, h t) + ∫ t in x..y, h t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ hL hx) (hint _ _ hx hy)).symm
  have h2 : (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)
      = (∫ t in ((2:ℝ)^l)..y, h t) + ∫ t in y..((2:ℝ)^(l+1)), h t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ hL hy) (hint _ _ hy hUpos)).symm
  have h3 : 0 ≤ ∫ t in ((2:ℝ)^l)..x, h t :=
    intervalIntegral.integral_nonneg hxlo (fun t _ => hh t)
  have h4 : 0 ≤ ∫ t in y..((2:ℝ)^(l+1)), h t :=
    intervalIntegral.integral_nonneg hyhi (fun t _ => hh t)
  linarith

/-- A jump of `α` between two points of the same dyadic level `[2^l, 2^(l+1)]` is dominated by
the level integral of `h`. -/
lemma jump_le_level_integral {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    (l : ℤ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxlo : (2:ℝ)^l ≤ x) (hxhi : x ≤ (2:ℝ)^(l+1))
    (hylo : (2:ℝ)^l ≤ y) (hyhi : y ≤ (2:ℝ)^(l+1)) :
    ‖α y - α x‖ ≤ ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t := by
  rcases le_total x y with hxy | hyx
  · exact (hFTC x y hx hxy).trans (interval_integral_le_level h hh hint l hx hy hxlo hxy hyhi)
  · rw [norm_sub_rev]
    exact (hFTC y x hy hyx).trans (interval_integral_le_level h hh hint l hy hx hylo hyx hxhi)

/-- **`ℓ^s` vs `ℓ²` on dyadic levels.**  For a finite set `L` of levels and a nonnegative level
weight `A`, the `ℓ^s`-sum of the level weights is bounded by the `ℓ²`-sum over *all* levels. -/
lemma level_sum_le_square_tsum (A : ℤ → ℝ) (hA : ∀ l, 0 ≤ A l) (L : Finset ℤ)
    {s : ℝ} (hs : 2 ≤ s) :
    ENNReal.ofReal ((∑ l ∈ L, A l ^ s) ^ (1/s))
      ≤ (∑' l : ℤ, (ENNReal.ofReal (A l)) ^ (2:ℝ)) ^ (1/2 : ℝ) := by
  have hs0 : 0 ≤ s := by linarith
  have hpow : ∀ l : ℤ, ENNReal.ofReal (A l ^ s) = (ENNReal.ofReal (A l)) ^ s :=
    fun l => (ENNReal.ofReal_rpow_of_nonneg (hA l) hs0).symm
  have hsum : ENNReal.ofReal (∑ l ∈ L, A l ^ s) = ∑ l ∈ L, (ENNReal.ofReal (A l)) ^ s := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => Real.rpow_nonneg (hA l) s)]
    exact Finset.sum_congr rfl fun l _ => hpow l
  have hnn : 0 ≤ ∑ l ∈ L, A l ^ s := Finset.sum_nonneg fun l _ => Real.rpow_nonneg (hA l) s
  calc ENNReal.ofReal ((∑ l ∈ L, A l ^ s) ^ (1/s))
      = (ENNReal.ofReal (∑ l ∈ L, A l ^ s)) ^ (1/s) :=
        (ENNReal.ofReal_rpow_of_nonneg hnn (by positivity)).symm
    _ = (∑ l ∈ L, (ENNReal.ofReal (A l)) ^ s) ^ (1/s) := by rw [hsum]
    _ ≤ (∑ l ∈ L, (ENNReal.ofReal (A l)) ^ (2:ℝ)) ^ (1/2 : ℝ) :=
        Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv L (fun l => ENNReal.ofReal (A l))
          (by norm_num) hs
    _ ≤ (∑' l : ℤ, (ENNReal.ofReal (A l)) ^ (2:ℝ)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum L) (by norm_num)

/-- The crossing "dyadic chord" part `j ↦ α (2^(lv (succ j))) - α (2^(lv (castSucc j)))` is
dominated by the dyadic variation: the map `j ↦ lv (castSucc j)` is nondecreasing, so
`nondecr_chain_le` applies. -/
lemma crossing_chord_le_dyadicVar {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) {s : ℝ}
    (hs : 0 < s) {N : ℕ} (lv : Fin (N+1) → ℤ) (hlv : Monotone lv) (X : Finset (Fin N))
    (hX : ∀ j ∈ X, lv (Fin.castSucc j) < lv (Fin.succ j)) :
    ENNReal.ofReal
        ((∑ j ∈ X, ‖α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j)))‖ ^ s) ^ (1/s))
      ≤ dyadicVar α s := by
  set e : ℕ → ℤ := fun i => lv ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ with he
  have hemono : Monotone e := fun i j hij =>
    hlv (Fin.mk_le_mk.mpr (min_le_min_right N hij))
  have hN := nondecr_chain_le α hs e hemono N
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hN
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) s) ?_
    (by positivity)
  have h1 : ∑ j ∈ X, ‖α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j)))‖ ^ s
      ≤ ∑ j : Fin N, ‖α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j)))‖ ^ s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
      (fun j _ _ => Real.rpow_nonneg (norm_nonneg _) s)
  have h2 : ∑ j : Fin N, ‖α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j)))‖ ^ s
      = ∑ i ∈ Finset.range N, ‖α ((2:ℝ)^(e i)) - α ((2:ℝ)^(e (i+1)))‖ ^ s := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ‖α ((2:ℝ)^(e i)) - α ((2:ℝ)^(e (i+1)))‖ ^ s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1' : e j.val = lv (Fin.castSucc j) := by
      simp only [he]; congr 1; ext
      simp [Fin.val_castSucc]
    have h2' : e (j.val+1) = lv (Fin.succ j) := by
      simp only [he]; congr 1; ext
      simp [Nat.min_eq_left (Nat.succ_le_of_lt j.isLt), Fin.val_succ]
    rw [h1', h2', norm_sub_rev]
  rw [h2] at h1
  exact h1


/-- Triangle inequality for a left-nested sum of four vectors. -/
lemma norm_four_le {E : Type*} [NormedAddCommGroup E] (x y z w : E) :
    ‖x + (y + (z + w))‖ ≤ ‖x‖ + (‖y‖ + (‖z‖ + ‖w‖)) := by
  calc ‖x + (y + (z + w))‖ ≤ ‖x‖ + ‖y + (z + w)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + (‖y‖ + ‖z + w‖) := add_le_add le_rfl (norm_add_le _ _)
    _ ≤ ‖x‖ + (‖y‖ + (‖z‖ + ‖w‖)) := add_le_add le_rfl (add_le_add le_rfl (norm_add_le _ _))

/-- Minkowski for the `ℓ^s`-norm of *nonnegative* real families. -/
lemma Lp_add_le_of_nonneg {ι : Type*} (t : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ t, 0 ≤ f i) (hg : ∀ i ∈ t, 0 ≤ g i) {s : ℝ} (hs : 1 ≤ s) :
    (∑ i ∈ t, (f i + g i) ^ s) ^ (1 / s)
      ≤ (∑ i ∈ t, f i ^ s) ^ (1 / s) + (∑ i ∈ t, g i ^ s) ^ (1 / s) := by
  have h1 : ∀ i ∈ t, |f i + g i| = f i + g i :=
    fun i hi => abs_of_nonneg (add_nonneg (hf i hi) (hg i hi))
  have h2 : ∀ i ∈ t, |f i| = f i := fun i hi => abs_of_nonneg (hf i hi)
  have h3 : ∀ i ∈ t, |g i| = g i := fun i hi => abs_of_nonneg (hg i hi)
  have e1 : (∑ i ∈ t, |f i + g i| ^ s) = ∑ i ∈ t, (f i + g i) ^ s :=
    Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
  have e2 : (∑ i ∈ t, |f i| ^ s) = ∑ i ∈ t, f i ^ s :=
    Finset.sum_congr rfl fun i hi => by rw [h2 i hi]
  have e3 : (∑ i ∈ t, |g i| ^ s) = ∑ i ∈ t, g i ^ s :=
    Finset.sum_congr rfl fun i hi => by rw [h3 i hi]
  have h := Real.Lp_add_le t f g hs
  rwa [e1, e2, e3] at h

/-- A family of "chords" of `α`, each contained in the dyadic level `g j`, is bounded by the
`ℓ^s`-sum of the level integrals of `h`, provided `g` is injective on the index set. -/
lemma sum_levelchord_le {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 0 ≤ s) {N : ℕ} (X : Finset (Fin N)) (g : Fin N → ℤ) (x y : Fin N → ℝ)
    (hker : Set.InjOn g ↑X)
    (hxpos : ∀ j ∈ X, 0 < x j) (hypos : ∀ j ∈ X, 0 < y j)
    (hxlo : ∀ j ∈ X, (2:ℝ)^(g j) ≤ x j) (hxhi : ∀ j ∈ X, x j ≤ (2:ℝ)^(g j + 1))
    (hylo : ∀ j ∈ X, (2:ℝ)^(g j) ≤ y j) (hyhi : ∀ j ∈ X, y j ≤ (2:ℝ)^(g j + 1)) :
    (∑ j ∈ X, ‖α (y j) - α (x j)‖ ^ s) ^ (1/s)
      ≤ (∑ l ∈ X.image g, (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s) ^ (1/s) := by
  have hterm : ∀ j ∈ X, ‖α (y j) - α (x j)‖ ≤ ∫ t in ((2:ℝ)^(g j))..((2:ℝ)^(g j + 1)), h t :=
    fun j hj => jump_le_level_integral α h hh hint hFTC (g j) (hxpos j hj) (hypos j hj)
      (hxlo j hj) (hxhi j hj) (hylo j hj) (hyhi j hj)
  have hsum : (∑ j ∈ X, ‖α (y j) - α (x j)‖ ^ s)
      ≤ ∑ j ∈ X, (∫ t in ((2:ℝ)^(g j))..((2:ℝ)^(g j+1)), h t) ^ s :=
    Finset.sum_le_sum fun j hj => Real.rpow_le_rpow (norm_nonneg _) (hterm j hj) hs
  calc (∑ j ∈ X, ‖α (y j) - α (x j)‖ ^ s) ^ (1/s)
      ≤ (∑ j ∈ X, (∫ t in ((2:ℝ)^(g j))..((2:ℝ)^(g j+1)), h t) ^ s) ^ (1/s) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) hsum
          (by positivity)
    _ = (∑ l ∈ X.image g, (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s) ^ (1/s) := by
        congr 1
        exact (Finset.sum_image (f := fun l : ℤ =>
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s) hker).symm

/-- `ENNReal` form of `sum_levelchord_le_le`: the `ℓ^s`-sum of the level integrals is dominated by
the dyadic `ℓ²`-sum over *all* levels. -/
lemma sum_levelchord_le_tsum {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 2 ≤ s) {N : ℕ} (X : Finset (Fin N)) (g : Fin N → ℤ) (x y : Fin N → ℝ)
    (hker : Set.InjOn g ↑X)
    (hxpos : ∀ j ∈ X, 0 < x j) (hypos : ∀ j ∈ X, 0 < y j)
    (hxlo : ∀ j ∈ X, (2:ℝ)^(g j) ≤ x j) (hxhi : ∀ j ∈ X, x j ≤ (2:ℝ)^(g j + 1))
    (hylo : ∀ j ∈ X, (2:ℝ)^(g j) ≤ y j) (hyhi : ∀ j ∈ X, y j ≤ (2:ℝ)^(g j + 1)) :
    ENNReal.ofReal ((∑ j ∈ X, ‖α (y j) - α (x j)‖ ^ s) ^ (1/s))
      ≤ (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)) ^ (2:ℝ))
          ^ (1/2 : ℝ) := by
  have hA : ∀ l : ℤ, 0 ≤ ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t :=
    fun l => intervalIntegral.integral_nonneg (zpow_le_zpow_right₀ (by norm_num) (by omega))
      (fun t _ => hh t)
  have h1 : ENNReal.ofReal ((∑ j ∈ X, ‖α (y j) - α (x j)‖ ^ s) ^ (1/s))
      ≤ ENNReal.ofReal ((∑ l ∈ X.image g,
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s) ^ (1/s)) :=
    ENNReal.ofReal_le_ofReal
      (sum_levelchord_le α h hh hint hFTC (by linarith) X g x y hker hxpos hypos hxlo hxhi hylo hyhi)
  exact h1.trans (level_sum_le_square_tsum (fun l : ℤ => ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)
    hA (X.image g) hs)

end Bookkeeping

open _root_.MeasureTheory

/-- A crossing index `j` (with `lv (castSucc j) < lv (succ j)`) is the **last** index of its level:
the level map `j ↦ lv (castSucc j)` is injective on the crossing set. -/
lemma injOn_crossing_level_left {N : ℕ} (lv : Fin (N+1) → ℤ) (hlv : Monotone lv) :
    Set.InjOn (fun j : Fin N => lv (Fin.castSucc j))
      {j : Fin N | lv (Fin.castSucc j) < lv (Fin.succ j)} := by
  intro j hj j' hj' heq
  simp only [] at heq
  have hj1 : lv (Fin.castSucc j) < lv (Fin.succ j) := hj
  have hj'1 : lv (Fin.castSucc j') < lv (Fin.succ j') := hj'
  rcases le_total (j : ℕ) (j' : ℕ) with h | h
  · refine Fin.ext (le_antisymm h ?_)
    by_contra hne
    have hlt : (j : ℕ) < (j' : ℕ) := by omega
    have h1 : lv (Fin.succ j) ≤ lv (Fin.castSucc j) := by
      have e : (Fin.succ j : Fin (N+1)) = Fin.castSucc (⟨j.val+1, by omega⟩ : Fin N) := Fin.ext rfl
      calc lv (Fin.succ j) = lv (Fin.castSucc (⟨j.val+1, by omega⟩ : Fin N)) := by rw [e]
        _ ≤ lv (Fin.castSucc j') :=
            hlv (Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_mk, Fin.val_castSucc]; omega))
        _ = lv (Fin.castSucc j) := heq.symm
    omega
  · refine Fin.ext (le_antisymm ?_ h)
    by_contra hne
    have hlt : (j' : ℕ) < (j : ℕ) := by omega
    have h1 : lv (Fin.succ j') ≤ lv (Fin.castSucc j') := by
      have e : (Fin.succ j' : Fin (N+1)) = Fin.castSucc (⟨j'.val+1, by omega⟩ : Fin N) := Fin.ext rfl
      calc lv (Fin.succ j') = lv (Fin.castSucc (⟨j'.val+1, by omega⟩ : Fin N)) := by rw [e]
        _ ≤ lv (Fin.castSucc j) :=
            hlv (Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_mk, Fin.val_castSucc]; omega))
        _ = lv (Fin.castSucc j') := heq
    omega

/-- A crossing index `j` has `j + 1` the **first** index of its level: the level map
`j ↦ lv (succ j)` is injective on the crossing set. -/
lemma injOn_crossing_level_right {N : ℕ} (lv : Fin (N+1) → ℤ) (hlv : Monotone lv) :
    Set.InjOn (fun j : Fin N => lv (Fin.succ j))
      {j : Fin N | lv (Fin.castSucc j) < lv (Fin.succ j)} := by
  intro j hj j' hj' heq
  simp only [] at heq
  have hj1 : lv (Fin.castSucc j) < lv (Fin.succ j) := hj
  have hj'1 : lv (Fin.castSucc j') < lv (Fin.succ j') := hj'
  rcases le_total (j : ℕ) (j' : ℕ) with h | h
  · refine Fin.ext (le_antisymm h ?_)
    by_contra hne
    have hlt : (j : ℕ) < (j' : ℕ) := by omega
    have h1 : lv (Fin.succ j) < lv (Fin.succ j') :=
      lt_of_le_of_lt (hlv (Fin.le_iff_val_le_val.mpr
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))) hj'1
    exact absurd (heq ▸ h1) (lt_irrefl _)
  · refine Fin.ext (le_antisymm ?_ h)
    by_contra hne
    have hlt : (j' : ℕ) < (j : ℕ) := by omega
    have h1 : lv (Fin.succ j') < lv (Fin.succ j) :=
      lt_of_le_of_lt (hlv (Fin.le_iff_val_le_val.mpr
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))) hj1
    exact absurd (heq.symm ▸ h1) (lt_irrefl _)

theorem chain_sum_le_integral {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y, 0 < x → x ≤ y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 1 ≤ s) {N : ℕ} (a : Fin (N+1) → ℝ) (ha : ∀ j, 0 < a j)
    (hmono : StrictMono a) :
    (∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
      ≤ ∫ t in (a 0)..(a (Fin.last N)), h t := by
  have hterm : ∀ j : Fin N,
      ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖
        ≤ ∫ t in (a (Fin.castSucc j))..(a (Fin.succ j)), h t :=
    fun j => hFTC _ _ (ha _) (hmono Fin.castSucc_lt_succ).le
  have hlp : (∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
      ≤ ∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ := by
    set M := ∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ with hM
    have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h2 : (∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ≤ M ^ s := by
      have hstep : ∀ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s
          ≤ M ^ (s-1) * ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ := by
        intro j
        have hdnn : 0 ≤ ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ := norm_nonneg _
        have hdM : ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ≤ M :=
          Finset.single_le_sum (f := fun j => ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        have hsp : ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s
            = ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ (s-1)
              * ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ (1:ℝ) := by
          rw [← Real.rpow_add_of_nonneg hdnn (by linarith) (by norm_num)]
          congr 1; ring
        rw [hsp, Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hdnn hdM (by linarith)) hdnn
      calc ∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s
          ≤ ∑ j : Fin N, M ^ (s-1) * ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = M ^ (s-1) * M := by rw [Finset.mul_sum]
        _ = M ^ s := by
            rw [show M ^ (s-1) * M = M ^ (s-1) * M ^ (1:ℝ) by rw [Real.rpow_one],
              ← Real.rpow_add_of_nonneg hMnn (by linarith) (by norm_num),
              show (s-1)+1 = s by ring]
    calc (∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
        ≤ (M ^ s) ^ (1/s) := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0:ℝ) ≤ 1/s)
      _ = M := by
          rw [← Real.rpow_mul hMnn, show s * (1/s) = 1 by rw [mul_one_div, div_self (by linarith : s ≠ 0)], Real.rpow_one]
  have hsum : ∑ j : Fin N, (∫ t in (a (Fin.castSucc j))..(a (Fin.succ j)), h t)
      = ∫ t in (a 0)..(a (Fin.last N)), h t := by
    set b : ℕ → ℝ := fun k => if h : k ≤ N then a ⟨k, Nat.lt_succ_of_le h⟩ else a (Fin.last N)
    have hb0 : b 0 = a 0 := by simp [b]
    have hbN : b N = a (Fin.last N) := by
      rw [show b N = a ⟨N, Nat.lt_succ_self N⟩ from by simp [b]]
      exact congrArg a (Fin.ext rfl)
    have hbc : ∀ j : Fin N, a (Fin.castSucc j) = b j.val := by
      intro j
      rw [show b j.val = a ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ from by simp [b]]
      exact congrArg a (Fin.ext rfl)
    have hbs : ∀ j : Fin N, a (Fin.succ j) = b (j.val+1) := by
      intro j
      rw [show b (j.val+1) = a ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩ from by
        simp [b, Nat.succ_le_of_lt j.isLt]]
      exact congrArg a (Fin.ext rfl)
    have hdiff : ∀ k < N, 0 < b k ∧ b k ≤ b (k+1) := by
      intro k hk
      have h1 : b k = a ⟨k, by omega⟩ := by simp [b, show k ≤ N by omega]
      have h2 : b (k+1) = a ⟨k+1, by omega⟩ := by simp [b, show k+1 ≤ N by omega]
      rw [h1, h2]
      exact ⟨ha _, (hmono (by simp)).le⟩
    rw [← hb0, ← hbN, ← intervalIntegral.sum_integral_adjacent_intervals
      (a := b) (n := N) (f := h) (fun k hk => hint (b k) (b (k+1)) (hdiff k hk).1 (hdiff k hk).2)]
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbc j, hbs j]
  calc (∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
      ≤ ∑ j : Fin N, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ := hlp
    _ ≤ ∑ j : Fin N, (∫ t in (a (Fin.castSucc j))..(a (Fin.succ j)), h t) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ∫ t in (a 0)..(a (Fin.last N)), h t := hsum

/-- Reindex a sum over `F : Finset (Fin N)` by the level `j ↦ lv (castSucc j)`. -/
theorem sum_fiberwise_level {N : ℕ} (lv : Fin (N+1) → ℤ) (F : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ j ∈ F, f j = ∑ l ∈ F.image (fun j : Fin N => lv (Fin.castSucc j)),
        ∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l), f j :=
  (Finset.sum_fiberwise_of_maps_to (s := F) (f := f)
    (g := fun j : Fin N => lv (Fin.castSucc j))
    (t := F.image (fun j : Fin N => lv (Fin.castSucc j)))
    (fun j hj => Finset.mem_image_of_mem _ hj)).symm

/-- **`ℓ^s ⊆ ℓ¹` for `s ≥ 1`**: for nonnegative `f` on a finset,
`(∑ f_i^s)^{1/s} ≤ ∑ f_i`. -/
theorem lpow_sum_le_sum {ι : Type*} (F : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ F, 0 ≤ f i)
    {s : ℝ} (hs : 1 ≤ s) :
    (∑ i ∈ F, f i ^ s) ^ (1/s) ≤ ∑ i ∈ F, f i := by
  set M := ∑ i ∈ F, f i with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg hf
  have h2 : (∑ i ∈ F, f i ^ s) ≤ M ^ s := by
    have hstep : ∀ i ∈ F, f i ^ s ≤ M ^ (s-1) * f i := by
      intro i hi
      have hinn : 0 ≤ f i := hf i hi
      have hiM : f i ≤ M := Finset.single_le_sum (fun j _ => hf j ‹j ∈ F›) hi
      have hsp : f i ^ s = f i ^ (s-1) * f i ^ (1:ℝ) := by
        rw [← Real.rpow_add_of_nonneg hinn (by linarith) (by norm_num)]
        congr 1; ring
      rw [hsp, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hinn hiM (by linarith)) hinn
    calc ∑ i ∈ F, f i ^ s ≤ ∑ i ∈ F, M ^ (s-1) * f i := Finset.sum_le_sum hstep
      _ = M ^ (s-1) * M := by rw [← Finset.mul_sum]
      _ = M ^ s := by
          rw [show M ^ (s-1) * M = M ^ (s-1) * M ^ (1:ℝ) by rw [Real.rpow_one],
            ← Real.rpow_add_of_nonneg hMnn (by linarith) (by norm_num),
            show (s-1)+1 = s by ring]
  calc (∑ i ∈ F, f i ^ s) ^ (1/s) ≤ (M ^ s) ^ (1/s) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) s) h2
          (by positivity : (0:ℝ) ≤ 1/s)
    _ = M := by
        rw [← Real.rpow_mul hMnn,
          show s * (1/s) = 1 by rw [mul_one_div, div_self (by linarith : s ≠ 0)], Real.rpow_one]

/-- **`hFTC` term bound** for a single jump of the chain: the increment over `[a_j, a_{j+1}]` is
dominated by the interval integral of `h`. -/
lemma chain_term_le_integral {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hFTC : ∀ x y, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {N : ℕ} (a : Fin (N+1) → ℝ) (ha : ∀ j, 0 < a j) (hmono : StrictMono a) (j : Fin N) :
    ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖
      ≤ ∫ t in (a (Fin.castSucc j))..(a (Fin.succ j)), h t :=
  hFTC _ _ (ha _) (hmono Fin.castSucc_lt_succ).le

/-- The primitive `φ z = ∫_{2^l}^z h` of a nonnegative, interval-integrable `h` is monotone on
`[2^l, ∞)`. -/
lemma primitive_mono (h : ℝ → ℝ) (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (l : ℤ) :
    ∀ x y : ℝ, (2:ℝ)^l ≤ x → x ≤ y →
      (∫ t in ((2:ℝ)^l)..x, h t) ≤ ∫ t in ((2:ℝ)^l)..y, h t := by
  intro x y hxle hxy
  have hL : 0 < (2:ℝ)^l := zpow_pos (by norm_num) l
  have hx : 0 < x := lt_of_lt_of_le hL hxle
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h1 : (∫ t in ((2:ℝ)^l)..y, h t)
      = (∫ t in ((2:ℝ)^l)..x, h t) + (∫ t in x..y, h t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ hL hx) (hint _ _ hx hy)).symm
  rw [h1]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hxy (fun t _ => hh t))

/-- Each term is a difference of the primitive `φ z = ∫_{2^l}^z h`. -/
lemma interval_integral_primitive_sub (h : ℝ → ℝ)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (l : ℤ) (x y : ℝ) (hx : (2:ℝ)^l ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, h t)
      = (∫ t in ((2:ℝ)^l)..y, h t) - ∫ t in ((2:ℝ)^l)..x, h t := by
  have hL : 0 < (2:ℝ)^l := zpow_pos (by norm_num) l
  have hx' : 0 < x := lt_of_lt_of_le hL hx
  have hy : 0 < y := lt_of_lt_of_le hx' hxy
  exact (intervalIntegral.integral_interval_sub_left (hint _ _ hL hy) (hint _ _ hL hx')).symm

set_option maxHeartbeats 800000 in
lemma sum_primitive_diff_le (h : ℝ → ℝ) (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (l : ℤ) {ι : Type*} [LinearOrder ι] (a b : ι → ℝ) (G : Finset ι) (L U : ℝ)
    (hL : (2:ℝ)^l ≤ L) (hLU : L ≤ U)
    (hLx : ∀ x ∈ G, L ≤ a x) (hbU : ∀ x ∈ G, b x ≤ U)
    (hab : ∀ x ∈ G, a x ≤ b x) (hdisj : ∀ x ∈ G, ∀ y ∈ G, x < y → b x ≤ a y) :
    ∑ x ∈ G, (∫ t in (a x)..(b x), h t)
      ≤ (∫ t in ((2:ℝ)^l)..U, h t) - ∫ t in ((2:ℝ)^l)..L, h t := by
  have key : ∀ n : ℕ, ∀ G : Finset ι, G.card = n → ∀ (L U : ℝ), (2:ℝ)^l ≤ L → L ≤ U →
      (∀ x ∈ G, L ≤ a x) → (∀ x ∈ G, b x ≤ U) →
      (∀ x ∈ G, a x ≤ b x) → (∀ x ∈ G, ∀ y ∈ G, x < y → b x ≤ a y) →
      ∑ x ∈ G, (∫ t in (a x)..(b x), h t)
        ≤ (∫ t in ((2:ℝ)^l)..U, h t) - ∫ t in ((2:ℝ)^l)..L, h t := by
   intro n
   induction n using Nat.strongRecOn with
   | ind n ih =>
    intro G hG L U hL hLU hLx hbU hab hdisj
    have hterm : ∀ x ∈ G, (∫ t in (a x)..(b x), h t)
        = (∫ t in ((2:ℝ)^l)..(b x), h t) - ∫ t in ((2:ℝ)^l)..(a x), h t :=
      fun x hx => interval_integral_primitive_sub h hint l (a x) (b x) (hL.trans (hLx x hx)) (hab x hx)
    rcases G.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.sum_empty]
      exact sub_nonneg.mpr (primitive_mono h hh hint l L U hL hLU)
    · set c := G.max' hne with hc
      have hcmem : c ∈ G := Finset.max'_mem G hne
      have hLc : L ≤ a c := hLx c hcmem
      have hbc : b c ≤ U := hbU c hcmem
      have hcard : (G.erase c).card < n := by
        rw [← hG, Finset.card_erase_of_mem hcmem]
        exact Nat.pred_lt (Finset.card_ne_zero_of_mem hcmem)
      have hEr : ∀ x ∈ G.erase c, b x ≤ a c := by
        intro x hx
        have hxG : x ∈ G := Finset.mem_of_mem_erase hx
        have hxc : x ≠ c := Finset.ne_of_mem_erase hx
        exact hdisj x hxG c hcmem (lt_of_le_of_ne (Finset.le_max' G x hxG) hxc)
      have ih' := ih (G.erase c).card hcard (G.erase c) rfl L (a c) hL hLc (fun x hx => hLx x (Finset.mem_of_mem_erase hx)) hEr
        (fun x hx => hab x (Finset.mem_of_mem_erase hx))
        (fun x hx y hy => hdisj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
      have hsplit : ∑ x ∈ G, (∫ t in (a x)..(b x), h t)
          = (∫ t in (a c)..(b c), h t) + ∑ x ∈ G.erase c, (∫ t in (a x)..(b x), h t) := by
        conv_lhs => rw [show G = insert c (G.erase c) from (Finset.insert_erase hcmem).symm]
        rw [Finset.sum_insert (show c ∉ G.erase c by simp [Finset.mem_erase])]
      rw [hsplit, hterm c hcmem]
      have hbc' : (∫ t in ((2:ℝ)^l)..(b c), h t) ≤ ∫ t in ((2:ℝ)^l)..U, h t :=
        primitive_mono h hh hint l (b c) U (hL.trans (hLc.trans (hab c hcmem))) hbc
      linarith
  exact key G.card G rfl L U hL hLU hLx hbU hab hdisj

set_option maxHeartbeats 1600000 in
theorem within_level_grouping {E : Type*} [NormedAddCommGroup E] (α : ℝ → E) (h : ℝ → ℝ)
    (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 1 ≤ s) {N : ℕ} (a : Fin (N+1) → ℝ) (ha : ∀ j, 0 < a j)
    (hmono : StrictMono a) (lv : Fin (N+1) → ℤ) (hlv : Monotone lv)
    (hlo : ∀ j, (2:ℝ)^(lv j) ≤ a j) (hhi : ∀ j, a j < (2:ℝ)^(lv j + 1))
    (F : Finset (Fin N)) (hF : ∀ j ∈ F, lv (Fin.castSucc j) = lv (Fin.succ j)) :
    (∑ j ∈ F, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
      ≤ (∑ l ∈ F.image (fun j : Fin N => lv (Fin.castSucc j)),
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s) ^ (1/s) := by
  have hLU : ∀ l : ℤ, (2:ℝ)^l ≤ (2:ℝ)^(l+1) := fun l =>
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hfib : ∀ l ∈ F.image (fun j : Fin N => lv (Fin.castSucc j)),
      ∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
        ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s
      ≤ (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s := by
    intro l hl
    have hsum : ∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
        ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖
        ≤ ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t := by
      refine (Finset.sum_le_sum fun j _ =>
        chain_term_le_integral α h hFTC a ha hmono j).trans ?_
      have hsp := sum_primitive_diff_le h hh hint l (fun j : Fin N => a (Fin.castSucc j))
        (fun j : Fin N => a (Fin.succ j)) (F.filter (fun j => lv (Fin.castSucc j) = l))
        ((2:ℝ)^l) ((2:ℝ)^(l+1)) le_rfl (hLU l)
        (fun j hj => by rw [Finset.mem_filter] at hj; rw [← hj.2]; exact hlo _)
        (fun j hj => by
          rw [Finset.mem_filter] at hj
          have hjl : lv (Fin.succ j) = l := by rw [← hF j hj.1, hj.2]
          rw [← hjl]; exact le_of_lt (hhi _))
        (fun j _ => (hmono Fin.castSucc_lt_succ).le)
        (fun x _ y _ hxy => hmono.monotone (Fin.le_iff_val_le_val.mpr (by
          simp only [Fin.val_castSucc, Fin.val_succ]; omega)))
      simpa [intervalIntegral.integral_same] using hsp
    have h1 : (∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
        ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)
        ≤ ∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
            ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ :=
      lpow_sum_le_sum _ _ (fun j _ => norm_nonneg _) hs
    have hA : 0 ≤ ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t :=
      intervalIntegral.integral_nonneg (hLU l) (fun t _ => hh t)
    calc ∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
          ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s
        = ((∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
            ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s) ^ (1/s)) ^ s := by
          rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ => by positivity),
            show (1:ℝ)/s * s = 1 by rw [div_mul_cancel₀ _ (by linarith : s ≠ 0)], Real.rpow_one]
      _ ≤ (∑ j ∈ F.filter (fun j => lv (Fin.castSucc j) = l),
            ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖) ^ s :=
          Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ ≤ (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t) ^ s :=
          Real.rpow_le_rpow (by positivity) hsum (by linarith)
  rw [sum_fiberwise_level lv F
    (fun j => ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s)]
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_le_sum hfib) (by positivity)

/-- The per-chain "bookkeeping" estimate: for every increasing chain of positive reals, the
`ℓ^s`-variation of `α` along it is bounded by the dyadic level square function plus the dyadic
`s`-variation of `α`. -/
theorem chain_variation_le_dyadic_add_within {E : Type*} [NormedAddCommGroup E]
    (α : ℝ → E) (h : ℝ → ℝ) (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 2 ≤ s) (N : ℕ) (a : Fin (N+1) → ℝ) (ha : ∀ j, 0 < a j)
    (hmono : StrictMono a) :
    ENNReal.ofReal ((∑ j : Fin N, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
      ≤ 100 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)) ^ (2:ℝ)) ^ (1/2:ℝ)
          + dyadicVar α s) := by
  classical
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  set lv : Fin (N+1) → ℤ := fun j => lev (a j) with hlvdef
  have hlv : Monotone lv := fun i j hij => lev_mono (ha i) (hmono.monotone hij)
  have hlo : ∀ j, (2:ℝ)^(lv j) ≤ a j := fun j => zpow_two_lev_le _ (ha j)
  have hhi : ∀ j, a j < (2:ℝ)^(lv j + 1) := fun j => lt_zpow_two_lev_succ _ (ha j)
  set S : ℝ≥0∞ := (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)) ^ (2:ℝ)) ^ (1/2:ℝ)
    with hSdef
  set D : ℝ≥0∞ := dyadicVar α s with hDdef
  set W : Finset (Fin N) := Finset.univ.filter (fun j => lv (Fin.castSucc j) = lv (Fin.succ j))
    with hWdef
  set X : Finset (Fin N) := Finset.univ.filter (fun j => ¬ (lv (Fin.castSucc j) = lv (Fin.succ j)))
    with hXdef
  have hWm : ∀ j ∈ W, lv (Fin.castSucc j) = lv (Fin.succ j) := fun j hj => (Finset.mem_filter.mp hj).2
  have hXlt : ∀ j ∈ X, lv (Fin.castSucc j) < lv (Fin.succ j) := by
    intro j hj
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 : lv (Fin.castSucc j) ≤ lv (Fin.succ j) := hlv (Fin.castSucc_lt_succ (i := j)).le
    exact lt_of_le_of_ne h2 h1
  -- the split of the sum over all indices into `W` and `X`
  have hsplit : (∑ j : Fin N, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s)
      = (∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s)
        + (∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun j : Fin N => lv (Fin.castSucc j) = lv (Fin.succ j))
      (f := fun j : Fin N => ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s)
    rw [← hWdef, ← hXdef] at h
    exact h.symm
  -- within bucket
  have hWb : ENNReal.ofReal
      ((∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)) ≤ S := by
    have h1 : (∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s)
        = ∑ j ∈ W, ‖α (a (Fin.succ j)) - α (a (Fin.castSucc j))‖ ^ s :=
      Finset.sum_congr rfl fun j _ => by rw [norm_sub_rev]
    rw [h1]
    have h2 := within_level_grouping α h hh hint hFTC hs1 a ha hmono lv hlv hlo hhi W hWm
    refine (ENNReal.ofReal_le_ofReal h2).trans ?_
    exact level_sum_le_square_tsum (fun l : ℤ => ∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)
      (fun l => intervalIntegral.integral_nonneg (zpow_le_zpow_right₀ (by norm_num) (by omega))
        (fun t _ => hh t)) (W.image (fun j : Fin N => lv (Fin.castSucc j))) hs

  -- the four pieces of the crossing decomposition
  set b1 : Fin N → ℝ := fun j => ‖α ((2:ℝ)^(lv (Fin.castSucc j) + 1)) - α (a (Fin.castSucc j))‖
    with hb1def
  set b2 : Fin N → ℝ := fun j => ‖α ((2:ℝ)^(lv (Fin.castSucc j))) - α ((2:ℝ)^(lv (Fin.castSucc j) + 1))‖
    with hb2def
  set b3 : Fin N → ℝ := fun j => ‖α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j)))‖
    with hb3def
  set b4 : Fin N → ℝ := fun j => ‖α (a (Fin.succ j)) - α ((2:ℝ)^(lv (Fin.succ j)))‖
    with hb4def
  have hβle : ∀ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ≤ b1 j + (b2 j + (b3 j + b4 j)) := by
    intro j hj
    have htel : α (a (Fin.succ j)) - α (a (Fin.castSucc j))
        = (α ((2:ℝ)^(lv (Fin.castSucc j) + 1)) - α (a (Fin.castSucc j)))
          + ((α ((2:ℝ)^(lv (Fin.castSucc j))) - α ((2:ℝ)^(lv (Fin.castSucc j) + 1)))
          + ((α ((2:ℝ)^(lv (Fin.succ j))) - α ((2:ℝ)^(lv (Fin.castSucc j))))
          + (α (a (Fin.succ j)) - α ((2:ℝ)^(lv (Fin.succ j)))))) := by abel
    rw [norm_sub_rev, htel]
    exact norm_four_le (E := E) _ _ _ _
  -- the `ℓ^s`-triangle inequality for the four pieces
  have hXsum : (∑ j ∈ X, (b1 j + (b2 j + (b3 j + b4 j))) ^ s) ^ (1/s)
      ≤ ((∑ j ∈ X, b1 j ^ s) ^ (1/s) + (∑ j ∈ X, b2 j ^ s) ^ (1/s))
        + ((∑ j ∈ X, b3 j ^ s) ^ (1/s) + (∑ j ∈ X, b4 j ^ s) ^ (1/s)) := by
    have hA1 := Lp_add_le_of_nonneg X b1 (fun j => b2 j + (b3 j + b4 j))
      (fun j _ => norm_nonneg _) (fun j _ => by positivity) hs1
    have hA2 := Lp_add_le_of_nonneg X b2 (fun j => b3 j + b4 j)
      (fun j _ => norm_nonneg _) (fun j _ => by positivity) hs1
    have hA3 := Lp_add_le_of_nonneg X b3 b4
      (fun j _ => norm_nonneg _) (fun j _ => norm_nonneg _) hs1
    linarith
  -- the four level bounds
  have hker1 : Set.InjOn (fun j : Fin N => lv (Fin.castSucc j)) ↑X := by
    intro x hx y hy hxy
    exact injOn_crossing_level_left lv hlv (hXlt x hx) (hXlt y hy) hxy
  have hker2 : Set.InjOn (fun j : Fin N => lv (Fin.succ j)) ↑X := by
    intro x hx y hy hxy
    exact injOn_crossing_level_right lv hlv (hXlt x hx) (hXlt y hy) hxy
  have hb1S : ENNReal.ofReal ((∑ j ∈ X, b1 j ^ s) ^ (1/s)) ≤ S :=
    sum_levelchord_le_tsum α h hh hint hFTC hs X (fun j => lv (Fin.castSucc j))
      (fun j => a (Fin.castSucc j)) (fun j => (2:ℝ)^(lv (Fin.castSucc j) + 1)) hker1
      (fun j _ => ha _) (fun j _ => zpow_pos (by norm_num) _)
      (fun j _ => hlo _) (fun j _ => (hhi _).le)
      (fun j _ => zpow_le_zpow_right₀ (by norm_num) (by omega)) (fun j _ => le_rfl)
  have hb2S : ENNReal.ofReal ((∑ j ∈ X, b2 j ^ s) ^ (1/s)) ≤ S :=
    sum_levelchord_le_tsum α h hh hint hFTC hs X (fun j => lv (Fin.castSucc j))
      (fun j => (2:ℝ)^(lv (Fin.castSucc j) + 1)) (fun j => (2:ℝ)^(lv (Fin.castSucc j))) hker1
      (fun j _ => zpow_pos (by norm_num) _) (fun j _ => zpow_pos (by norm_num) _)
      (fun j _ => zpow_le_zpow_right₀ (by norm_num) (by omega)) (fun j _ => le_rfl)
      (fun j _ => zpow_le_zpow_right₀ (by norm_num) (by omega))
      (fun j _ => zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hb4S : ENNReal.ofReal ((∑ j ∈ X, b4 j ^ s) ^ (1/s)) ≤ S :=
    sum_levelchord_le_tsum α h hh hint hFTC hs X (fun j => lv (Fin.succ j))
      (fun j => (2:ℝ)^(lv (Fin.succ j))) (fun j => a (Fin.succ j)) hker2
      (fun j _ => zpow_pos (by norm_num) _) (fun j _ => ha _)
      (fun j _ => le_rfl) (fun j _ => zpow_le_zpow_right₀ (by norm_num) (by omega))
      (fun j _ => hlo _) (fun j _ => (hhi _).le)
  have hb3D : ENNReal.ofReal ((∑ j ∈ X, b3 j ^ s) ^ (1/s)) ≤ D :=
    crossing_chord_le_dyadicVar α hs0 lv hlv X hXlt
  have hb1b : ENNReal.ofReal ((∑ j ∈ X, b1 j ^ s) ^ (1/s)) ≤ S + D :=
    hb1S.trans (self_le_add_right S D)
  have hb2b : ENNReal.ofReal ((∑ j ∈ X, b2 j ^ s) ^ (1/s)) ≤ S + D :=
    hb2S.trans (self_le_add_right S D)
  have hb4b : ENNReal.ofReal ((∑ j ∈ X, b4 j ^ s) ^ (1/s)) ≤ S + D :=
    hb4S.trans (self_le_add_right S D)
  have hb3b : ENNReal.ofReal ((∑ j ∈ X, b3 j ^ s) ^ (1/s)) ≤ S + D :=
    hb3D.trans (self_le_add_left D S)
  -- combine
  have hXd : ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
      ≤ 4 * (S + D) := by
    have hstep : ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
        ≤ (ENNReal.ofReal ((∑ j ∈ X, b1 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b2 j ^ s) ^ (1/s)))
          + (ENNReal.ofReal ((∑ j ∈ X, b3 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b4 j ^ s) ^ (1/s))) := by
      have hle : (∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)
          ≤ (∑ j ∈ X, (b1 j + (b2 j + (b3 j + b4 j))) ^ s) ^ (1/s) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s)
          (Finset.sum_le_sum fun j hj => Real.rpow_le_rpow (norm_nonneg _) (hβle j hj) hs0.le)
          (by positivity)
      have hle2 : ENNReal.ofReal ((∑ j ∈ X, (b1 j + (b2 j + (b3 j + b4 j))) ^ s) ^ (1/s))
          ≤ ENNReal.ofReal (((∑ j ∈ X, b1 j ^ s) ^ (1/s) + (∑ j ∈ X, b2 j ^ s) ^ (1/s))
            + ((∑ j ∈ X, b3 j ^ s) ^ (1/s) + (∑ j ∈ X, b4 j ^ s) ^ (1/s))) :=
        ENNReal.ofReal_le_ofReal hXsum
      have e : ENNReal.ofReal (((∑ j ∈ X, b1 j ^ s) ^ (1/s) + (∑ j ∈ X, b2 j ^ s) ^ (1/s))
            + ((∑ j ∈ X, b3 j ^ s) ^ (1/s) + (∑ j ∈ X, b4 j ^ s) ^ (1/s)))
          = (ENNReal.ofReal ((∑ j ∈ X, b1 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b2 j ^ s) ^ (1/s)))
            + (ENNReal.ofReal ((∑ j ∈ X, b3 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b4 j ^ s) ^ (1/s))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
      calc ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
          ≤ ENNReal.ofReal ((∑ j ∈ X, (b1 j + (b2 j + (b3 j + b4 j))) ^ s) ^ (1/s)) :=
            ENNReal.ofReal_le_ofReal hle
        _ ≤ ENNReal.ofReal (((∑ j ∈ X, b1 j ^ s) ^ (1/s) + (∑ j ∈ X, b2 j ^ s) ^ (1/s))
              + ((∑ j ∈ X, b3 j ^ s) ^ (1/s) + (∑ j ∈ X, b4 j ^ s) ^ (1/s))) := hle2
        _ = _ := e
    refine hstep.trans ?_
    calc (ENNReal.ofReal ((∑ j ∈ X, b1 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b2 j ^ s) ^ (1/s)))
          + (ENNReal.ofReal ((∑ j ∈ X, b3 j ^ s) ^ (1/s)) + ENNReal.ofReal ((∑ j ∈ X, b4 j ^ s) ^ (1/s)))
        ≤ (S + D) + (S + D) + ((S + D) + (S + D)) :=
          add_le_add (add_le_add hb1b hb2b) (add_le_add hb3b hb4b)
      _ = 4 * (S + D) := by ring
  -- put everything together
  have hfinalB : ENNReal.ofReal ((∑ j : Fin N, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
      ≤ (ENNReal.ofReal ((∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)))
        + (ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))) := by
    have hle : (∑ j : Fin N, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)
        ≤ (∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)
          + (∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s) := by
      rw [hsplit]
      exact Real.rpow_add_le_add_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s)
        (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) (by positivity)
        ((div_le_one hs0).mpr hs1)
    have h1 : 0 ≤ (∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) _
    have h2 : 0 ≤ (∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) _
    calc ENNReal.ofReal ((∑ j : Fin N, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
        ≤ ENNReal.ofReal ((∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)
            + (∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal ((∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s))
            + ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)) :=
          ENNReal.ofReal_add h1 h2
  refine hfinalB.trans ?_
  have hclose : S + 4 * (S + D) ≤ 100 * (S + D) := by
    have h1 : S ≤ S + D := le_add_right le_rfl
    have h3 : S + 4*(S+D) ≤ (S+D) + 4*(S+D) := add_le_add h1 le_rfl
    have h4 : (S+D) + 4*(S+D) ≤ 100*(S+D) := by
      have e : (S+D) + 4*(S+D) = 5*(S+D) := by ring
      rw [e]; exact mul_le_mul_left (by norm_num) (S+D)
    exact h3.trans h4
  calc (ENNReal.ofReal ((∑ j ∈ W, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)))
        + (ENNReal.ofReal ((∑ j ∈ X, ‖α (a (Fin.castSucc j)) - α (a (Fin.succ j))‖ ^ s) ^ (1/s)))
      ≤ S + 4 * (S + D) := add_le_add hWb hXd
    _ ≤ 100 * (S + D) := hclose

lemma dyadicVar_inv_le {E : Type*} [NormedAddCommGroup E] (A : ℝ → E) (s : ℝ) :
    dyadicVar A s ≤ dyadicVar (fun t : ℝ => A t⁻¹) s := by
  rw [dyadicVar, dyadicVar]
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
  set tau : Fin (J+1) → Fin (J+1) := fun j => ⟨J - j.val, by omega⟩ with htau
  set rho : Fin J → Fin J := fun j => ⟨J - 1 - j.val, by omega⟩ with hrho
  have h1 : ∀ j : Fin J, tau (Fin.castSucc j) = @Fin.succ J (rho j) := by
    intro j; apply Fin.ext
    show J - j.val = (J - 1 - j.val) + 1
    omega
  have h2 : ∀ j : Fin J, tau (@Fin.succ J j) = Fin.castSucc (rho j) := by
    intro j; apply Fin.ext
    show J - (j.val + 1) = J - 1 - j.val
    omega
  have h3 : ∀ i : Fin J, rho (rho i) = i := by
    intro i; apply Fin.ext
    show J - 1 - (J - 1 - i.val) = i.val
    omega
  set m : Fin (J+1) → ℤ := fun j => - k (tau j) with hm
  have hmono : StrictMono m := by
    intro a b hab
    have hba : (tau b).val < (tau a).val := by
      show J - b.val < J - a.val
      omega
    have hlt : tau b < tau a := hba
    show - k (tau a) < - k (tau b)
    exact neg_lt_neg (hk hlt)
  have hmeq : ∀ j : Fin J,
      (A (((2:ℝ) ^ (m (Fin.castSucc j)))⁻¹) : E) = A ((2:ℝ) ^ (k (@Fin.succ J (rho j)))) := by
    intro j
    congr 1
    rw [hm]
    simp only
    rw [h1 j]
    simp
  have hmeq2 : ∀ j : Fin J,
      (A (((2:ℝ) ^ (m (@Fin.succ J j)))⁻¹) : E) = A ((2:ℝ) ^ (k (Fin.castSucc (rho j)))) := by
    intro j
    congr 1
    rw [hm]
    simp only
    rw [h2 j]
    simp
  have hsum : (∑ j : Fin J, ‖A (((2:ℝ) ^ (m (Fin.castSucc j)))⁻¹)
        - A (((2:ℝ) ^ (m (@Fin.succ J j)))⁻¹)‖ ^ s)
      = ∑ i : Fin J, ‖A ((2:ℝ) ^ (k (Fin.castSucc i))) - A ((2:ℝ) ^ (k (@Fin.succ J i)))‖ ^ s := by
    have step1 : (∑ j : Fin J, ‖A (((2:ℝ) ^ (m (Fin.castSucc j)))⁻¹)
        - A (((2:ℝ) ^ (m (@Fin.succ J j)))⁻¹)‖ ^ s)
        = ∑ j : Fin J, ‖A ((2:ℝ) ^ (k (@Fin.succ J (rho j))))
            - A ((2:ℝ) ^ (k (Fin.castSucc (rho j))))‖ ^ s := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmeq j, hmeq2 j]
    rw [step1]
    have hinv : Function.Involutive rho := h3
    have hcomp := Fintype.sum_bijective rho hinv.bijective
      (fun j : Fin J => ‖A ((2:ℝ) ^ (k (@Fin.succ J (rho j))))
        - A ((2:ℝ) ^ (k (Fin.castSucc (rho j))))‖ ^ s)
      (fun i : Fin J => ‖A ((2:ℝ) ^ (k (@Fin.succ J i)))
        - A ((2:ℝ) ^ (k (Fin.castSucc i)))‖ ^ s)
      (fun j => rfl)
    rw [hcomp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sub_rev]
  have hUV : ENNReal.ofReal ((∑ j : Fin J,
        ‖A ((2:ℝ) ^ (k (Fin.castSucc j))) - A ((2:ℝ) ^ (k (@Fin.succ J j)))‖ ^ s) ^ (1/s))
      = ENNReal.ofReal ((∑ j : Fin J,
        ‖A (((2:ℝ) ^ (m (Fin.castSucc j)))⁻¹)
          - A (((2:ℝ) ^ (m (@Fin.succ J j)))⁻¹)‖ ^ s) ^ (1/s)) := by
    rw [hsum]
  exact le_trans (le_of_eq hUV)
    (le_iSup_of_le J (le_iSup_of_le m (le_iSup (fun _ : StrictMono m => _) hmono)))

lemma chain_ls_add_le {E : Type*} [NormedAddCommGroup E] {ι : Type*} (t : Finset ι) (a b : ι → E)
    {s : ℝ} (hs : 1 ≤ s) :
    (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1/s)
      ≤ (∑ i ∈ t, ‖a i‖ ^ s) ^ (1/s) + (∑ i ∈ t, ‖b i‖ ^ s) ^ (1/s) := by
  have h1 : (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1/s) ≤ (∑ i ∈ t, (‖a i‖ + ‖b i‖) ^ s) ^ (1/s) := by
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by linarith))
      (by positivity)
  have h2 := Real.Lp_add_le t (fun i => ‖a i‖) (fun i => ‖b i‖) hs
  calc (∑ i ∈ t, ‖a i + b i‖ ^ s) ^ (1/s)
      ≤ (∑ i ∈ t, (‖a i‖ + ‖b i‖) ^ s) ^ (1/s) := h1
    _ = (∑ i ∈ t, |‖a i‖ + ‖b i‖| ^ s) ^ (1/s) := by
        simp only [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (∑ i ∈ t, |‖a i‖| ^ s) ^ (1/s) + (∑ i ∈ t, |‖b i‖| ^ s) ^ (1/s) := h2
    _ = (∑ i ∈ t, ‖a i‖ ^ s) ^ (1/s) + (∑ i ∈ t, ‖b i‖ ^ s) ^ (1/s) := by
        simp only [abs_of_nonneg (norm_nonneg _)]

lemma dyadicVar_add_le {E : Type*} [NormedAddCommGroup E] (α β : ℝ → E) {s : ℝ} (hs : 1 ≤ s) :
    dyadicVar (fun t => α t + β t) s ≤ dyadicVar α s + dyadicVar β s := by
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
  have hab : ∀ j : Fin J,
      α ((2:ℝ)^(k (Fin.castSucc j))) + β ((2:ℝ)^(k (Fin.castSucc j)))
        - (α ((2:ℝ)^(k (Fin.succ j))) + β ((2:ℝ)^(k (Fin.succ j))))
      = (α ((2:ℝ)^(k (Fin.castSucc j))) - α ((2:ℝ)^(k (Fin.succ j))))
        + (β ((2:ℝ)^(k (Fin.castSucc j))) - β ((2:ℝ)^(k (Fin.succ j)))) := by
    intro j; abel
  simp only [hab]
  refine le_trans (ENNReal.ofReal_le_ofReal (chain_ls_add_le _ _ _ hs)) ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (dyadicVar_le_def α s J k hk) (dyadicVar_le_def β s J k hk)

/-- **Bookkeeping.**  If the increments of `α` are dominated by `∫ h` (FTC), then the `s`-variation
of `α` over chains of positive reals is bounded by a constant times the `ℓ²`-sum over the dyadic
levels of the level integrals of `h`, plus the dyadic `s`-variation of `α`. -/
theorem variation_cont_le_dyadic_add_within {E : Type*} [NormedAddCommGroup E]
    (α : ℝ → E) (h : ℝ → ℝ) (hh : ∀ t : ℝ, 0 ≤ h t)
    (hint : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable h MeasureTheory.volume x y)
    (hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → ‖α y - α x‖ ≤ ∫ t in x..y, h t)
    {s : ℝ} (hs : 2 ≤ s) :
    (⨆ (J : ℕ) (u : Fin (J+1) → {t : ℝ // 0 < t}), ⨆ (_ : StrictMono fun j => ((u j : ℝ))),
        ENNReal.ofReal ((∑ j : Fin J,
          ‖α ((u (Fin.castSucc j) : ℝ)) - α ((u (Fin.succ j) : ℝ))‖ ^ s) ^ (1/s)))
      ≤ 100 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), h t)) ^ (2:ℝ)) ^ (1/2 : ℝ)
          + dyadicVar α s) := by
  have hint2 := intervalIntegrable_of_pos hint
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => ?_
  exact chain_variation_le_dyadic_add_within α h hh hint2 hFTC hs J (fun j => ((u j : {t : ℝ // 0 < t}) : ℝ))
    (fun j => (u j).2) hu

-- `ThetaS Ψ` is `z ↦ Ψ z + z • Ψ' z` as a Schwartz function.
noncomputable def ThetaS (Ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  Ψ + SchwartzMap.smulLeftCLM ℂ (fun z : ℝ => (z : ℂ)) (SchwartzMap.derivCLM ℂ ℂ Ψ)

lemma ThetaS_apply (Ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ThetaS Ψ x = Ψ x + x * deriv (Ψ : ℝ → ℂ) x := by
  have hg : Function.HasTemperateGrowth (fun z : ℝ => (z : ℂ)) := by fun_prop
  simp only [ThetaS, add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

-- The derivative of a Schwartz function has vanishing integral.
lemma integral_derivCLM_eq_zero (f : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ f : ℝ → ℂ) x = 0 := by
  refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun x : ℝ => (f : ℝ → ℂ) x)
    (f' := fun x : ℝ => (SchwartzMap.derivCLM ℂ ℂ f : ℝ → ℂ) x) ?_ ?_ ?_
  · intro x
    rw [SchwartzMap.derivCLM_apply]
    exact SchwartzMap.hasDerivAt f x
  · exact (SchwartzMap.derivCLM ℂ ℂ f).integrable
  · exact f.integrable

-- `∫ Θ = 0`.
lemma integral_ThetaS (Ψ : SchwartzMap ℝ ℂ) : ∫ x : ℝ, ThetaS Ψ x = 0 := by
  have hg : Function.HasTemperateGrowth (fun z : ℝ => (z : ℂ)) := by fun_prop
  have hprod : ∀ x : ℝ, HasDerivAt (fun z : ℝ => (z : ℂ) * Ψ z)
      (Ψ x + x * deriv (Ψ : ℝ → ℂ) x) x := by
    intro x
    have hz : HasDerivAt (fun z : ℝ => (z : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hΨ : HasDerivAt (fun z : ℝ => (Ψ : ℝ → ℂ) z) (deriv (Ψ : ℝ → ℂ) x) x :=
      SchwartzMap.hasDerivAt Ψ x
    have h := hz.mul hΨ
    simpa only [Pi.mul_def, one_mul] using h
  calc ∫ x : ℝ, ThetaS Ψ x
      = ∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ
          (SchwartzMap.smulLeftCLM ℂ (fun z : ℝ => (z : ℂ)) Ψ) : ℝ → ℂ) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [ThetaS_apply, ← (hprod x).deriv, SchwartzMap.derivCLM_apply,
          SchwartzMap.smulLeftCLM_apply hg]
        simp only [smul_eq_mul]
    _ = 0 := integral_derivCLM_eq_zero _

/-! ## 4. The two analytic inputs

`Theta Ψ` is the (mean-zero) kernel whose dilation gives the derivative of the dilation family:
`∂_t (g * Ψ_t) = - t⁻¹ • (g * Theta Ψ_t)`.
-/

/-- The triangular kernel `Λ x = max 0 (1 - |x|)` as a complex function. -/
noncomputable def Lam (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma triangular_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (-1:ℝ) 1) : max 0 (1 - |x|) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h1 : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  exact max_eq_left (by linarith)

/-- `max 0 (1 - |x|)` is supported in `[-1,1]`. -/
lemma hasCompactSupport_lam_real : HasCompactSupport fun x : ℝ => max 0 (1 - |x|) :=
  HasCompactSupport.intro (K := Set.Icc (-1:ℝ) 1) isCompact_Icc
    (fun x hx => triangular_eq_zero hx)

lemma integral_lam : ∫ x : ℝ, Lam x = 1 := by
  have hcont : Continuous fun x : ℝ => max 0 (1 - |x|) := by fun_prop
  have hint : Integrable (fun x : ℝ => max 0 (1 - |x|)) volume :=
    hcont.integrable_of_hasCompactSupport hasCompactSupport_lam_real
  have h := ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  simp only [Complex.ofRealCLM_apply] at h
  simp only [Lam]
  rw [h, integral_triangular_kernel]
  norm_num

lemma integrable_lam : Integrable Lam volume := by
  have hcont : Continuous Lam := by
    unfold Lam; fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-1:ℝ) 1) isCompact_Icc ?_
  intro x hx
  show Lam x = 0
  unfold Lam
  rw [triangular_eq_zero hx, Complex.ofReal_zero]

/-- The mean-zero remainder `Ψ - (∫Ψ)·Λ`. -/
noncomputable def Rem (Ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun x => (Ψ : ℝ → ℂ) x - (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * Lam x

lemma integral_Rem (Ψ : SchwartzMap ℝ ℂ) : ∫ x : ℝ, Rem Ψ x = 0 := by
  have h1 : (∫ x : ℝ, Rem Ψ x)
      = (∫ x : ℝ, (Ψ : ℝ → ℂ) x) - ∫ x : ℝ, (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * Lam x := by
    unfold Rem
    exact integral_sub Ψ.integrable (integrable_lam.const_mul _)
  rw [h1, integral_const_mul, integral_lam]
  ring


lemma integrable_Rem (Ψ : SchwartzMap ℝ ℂ) : Integrable (Rem Ψ) volume := by
  have h : Integrable (fun x : ℝ => (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * Lam x) volume :=
    integrable_lam.const_mul _
  exact Ψ.integrable.sub h

/-- Quadratic decay of `ThetaS Ψ`. -/
lemma norm_ThetaS_le (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖ThetaS Ψ x‖ ≤ C / (1 + |x|) ^ 2 := by
  have hS0 : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 0 0 (ThetaS Ψ) :=
    le_trans (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℂ (ThetaS Ψ) 0)
  have hS2 : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 2 0 (ThetaS Ψ) := by
    have h := SchwartzMap.le_seminorm' ℂ 2 0 (ThetaS Ψ) 1
    simpa using le_trans (mul_nonneg (by positivity) (norm_nonneg _)) h
  refine ⟨4 * SchwartzMap.seminorm ℂ 0 0 (ThetaS Ψ) + 4 * SchwartzMap.seminorm ℂ 2 0 (ThetaS Ψ) + 1,
    by linarith, fun x => ?_⟩
  have hkey : ‖ThetaS Ψ x‖ * (1 + |x|) ^ 2
      ≤ 4 * SchwartzMap.seminorm ℂ 0 0 (ThetaS Ψ) + 4 * SchwartzMap.seminorm ℂ 2 0 (ThetaS Ψ) := by
    by_cases hx : |x| ≤ 1
    · have h1 : ‖ThetaS Ψ x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (ThetaS Ψ) :=
        SchwartzMap.norm_le_seminorm ℂ (ThetaS Ψ) x
      have h2 : (1 + |x|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg x]
      have h3 : 0 ≤ ‖ThetaS Ψ x‖ := norm_nonneg _
      have : ‖ThetaS Ψ x‖ * (1 + |x|) ^ 2 ≤ SchwartzMap.seminorm ℂ 0 0 (ThetaS Ψ) * 4 := by
        exact mul_le_mul h1 h2 (by positivity) hS0
      linarith
    · have hx' : 1 < |x| := not_le.mp hx
      have h1 : |x| ^ 2 * ‖ThetaS Ψ x‖ ≤ SchwartzMap.seminorm ℂ 2 0 (ThetaS Ψ) :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ (ThetaS Ψ) 2 x
      have h2 : (1 + |x|) ^ 2 ≤ 4 * |x| ^ 2 := by
        have hx0 : 0 < |x| := by linarith
        nlinarith [abs_nonneg x]
      have h3 : 0 ≤ ‖ThetaS Ψ x‖ := norm_nonneg _
      have : ‖ThetaS Ψ x‖ * (1 + |x|) ^ 2 ≤ ‖ThetaS Ψ x‖ * (4 * |x| ^ 2) :=
        mul_le_mul_of_nonneg_left h2 h3
      linarith
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 + |x|) ^ 2)]
  linarith [hkey]

/-- `(a + b)² ≤ 4(a² + b²)` in `ℝ≥0∞`. -/
lemma add_sq_le_four (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left a b) (le_max_right a b)
  have hmax : (max a b) ^ 2 = max (a ^ 2) (b ^ 2) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left' h 2)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left' h 2)]
  calc (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' hab 2
    _ = 4 * (max a b) ^ 2 := by rw [mul_pow]; norm_num
    _ = 4 * max (a ^ 2) (b ^ 2) := by rw [hmax]
    _ ≤ 4 * (a ^ 2 + b ^ 2) := by
        gcongr
        exact max_le (self_le_add_right (a ^ 2) (b ^ 2)) (self_le_add_left (b ^ 2) (a ^ 2))

/-- `Θ Ψ (z) = Ψ z + z • Ψ' z`;  `∫ Θ = 0`. -/
noncomputable def Theta (Ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun z => (Ψ z) + z • deriv (Ψ : ℝ → ℂ) z

lemma integrable_mul_x_lam : Integrable (fun x : ℝ => x • Lam x) volume := by
  have hcont : Continuous fun x : ℝ => x • Lam x := by unfold Lam; fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-1:ℝ) 1) isCompact_Icc ?_
  intro x hx
  show x • Lam x = 0
  unfold Lam
  rw [triangular_eq_zero hx, Complex.ofReal_zero, smul_zero]

lemma integrable_rem_mul_x (Ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => x • Rem Ψ x) volume := by
  have hg : Function.HasTemperateGrowth (fun z : ℝ => (z : ℂ)) := by fun_prop
  have h1 : Integrable (fun x : ℝ => x • (Ψ : ℝ → ℂ) x) volume := by
    have h := (SchwartzMap.smulLeftCLM ℂ (fun z : ℝ => (z : ℂ)) Ψ).integrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    rw [SchwartzMap.smulLeftCLM_apply hg] at h
    simpa using h
  have h2 : Integrable (fun x : ℝ => (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * (x • Lam x)) volume :=
    integrable_mul_x_lam.const_mul _
  convert h1.sub h2 using 1
  ext x
  simp only [Rem, Pi.sub_apply, smul_sub, Complex.real_smul]
  ring

/-- For `w ≠ 0`, `‖∫_a^b e^{-i w x} dx‖ ≤ 2/|w|`. -/
lemma norm_integral_cexp_le (w : ℝ) (hw : w ≠ 0) (a b : ℝ) :
    ‖∫ x in a..b, Complex.exp (-(w * x * Complex.I))‖ ≤ 2 / |w| := by
  have hc : ((w : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hw) Complex.I_ne_zero
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => Complex.exp (-(w * x * Complex.I)) / (-((w : ℂ) * Complex.I)))
        (Complex.exp (-(w * x * Complex.I))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -((w : ℂ) * (x : ℂ) * Complex.I))
        (-((w : ℂ) * Complex.I)) x := by
      have h2 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have h3 := h2.mul_const (-((w : ℂ) * Complex.I))
      simpa only [one_mul, mul_one, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using h3
    have h4 := h1.cexp
    have h5 := h4.div_const (-((w : ℂ) * Complex.I))
    refine h5.congr_deriv ?_
    rw [mul_div_assoc, div_self (neg_ne_zero.mpr hc), mul_one]
  have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (-(w * x * Complex.I))) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(w * x * Complex.I))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hb : ‖Complex.exp (-(w * b * Complex.I)) / (-((w : ℂ) * Complex.I))‖ = 1 / |w| := by
    rw [norm_div, Complex.norm_exp]
    have hre : (-((w : ℂ) * (b : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have ha : ‖Complex.exp (-(w * a * Complex.I)) / (-((w : ℂ) * Complex.I))‖ = 1 / |w| := by
    rw [norm_div, Complex.norm_exp]
    have hre : (-((w : ℂ) * (a : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  calc ‖Complex.exp (-(w * b * Complex.I)) / (-((w : ℂ) * Complex.I))
        - Complex.exp (-(w * a * Complex.I)) / (-((w : ℂ) * Complex.I))‖
      ≤ ‖Complex.exp (-(w * b * Complex.I)) / (-((w : ℂ) * Complex.I))‖
        + ‖Complex.exp (-(w * a * Complex.I)) / (-((w : ℂ) * Complex.I))‖ := norm_sub_le _ _
    _ = 1 / |w| + 1 / |w| := by rw [hb, ha]
    _ = 2 / |w| := by ring

lemma sq_sinc_le (x : ℝ) : Real.sinc x ^ 2 ≤ 2 / (1 + |x|) := by
  have h1 : Real.sinc x ^ 2 = |Real.sinc x| ^ 2 := (sq_abs _).symm
  rw [h1]
  by_cases hx : |x| ≤ 1
  · have h : |Real.sinc x| ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sinc_le_one x, abs_nonneg (Real.sinc x)]
    have h2 : (1:ℝ) ≤ 2 / (1 + |x|) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + |x|)]
      linarith
    linarith
  · have hx1 : 1 < |x| := not_le.mp hx
    have h0 : x ≠ 0 := by
      intro h; rw [h] at hx1; norm_num at hx1
    have h2 : |Real.sinc x| ≤ |x|⁻¹ := abs_sinc_le_inv_abs h0
    have h3 : |Real.sinc x| ^ 2 ≤ (|x|⁻¹) ^ 2 := by
      nlinarith [abs_nonneg (Real.sinc x), inv_pos.mpr (abs_pos.mpr h0)]
    have h4 : (|x|⁻¹) ^ 2 ≤ 2 / (1 + |x|) := by
      rw [inv_pow, inv_eq_one_div, div_le_div_iff₀ (by positivity : (0:ℝ) < |x| ^ 2)
        (by positivity : (0:ℝ) < 1 + |x|)]
      nlinarith [abs_nonneg x, hx1, sq_nonneg |x|]
    linarith

lemma fourier_Lam_eq (ξ : ℝ) :
    FourierTransform.fourier Lam ξ
      = ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have hfun : (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ y ξ) * Complex.I) • Lam y)
      = fun y : ℝ => (tri y : ℂ) * Complex.exp (↑(-(2 * Real.pi * y * ξ)) * Complex.I) := by
    funext y
    rw [Real.inner_apply]
    simp only [Lam]
    rw [show max 0 (1 - |y|) = tri y from by rw [tri]; exact max_comm _ _]
    rw [smul_eq_mul, mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  rw [hfun]
  exact integral_tri_mul_exp ξ

/-- `𝓕 Λ` decays like `η⁻¹` (`Λ̂ = sinc²`). -/
lemma fourier_Lam_decay : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
    ‖FourierTransform.fourier Lam ξ‖ ≤ C * (1 + |ξ|) ^ (-1 : ℝ) := by
  refine ⟨2, by norm_num, fun ξ => ?_⟩
  have hs : ‖((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ)‖ = Real.sinc (Real.pi * ξ) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [fourier_Lam_eq, hs, Real.rpow_neg_one]
  have hL : Real.sinc (Real.pi * ξ) ^ 2 ≤ 2 * (1 + |Real.pi * ξ|)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact sq_sinc_le (Real.pi * ξ)
  refine hL.trans ?_
  have hpi : (1:ℝ) ≤ Real.pi := by
    have := Real.pi_gt_three; linarith
  have h5 : (1 + |ξ|) ≤ (1 + |Real.pi * ξ|) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg ξ, hpi]
  have h6 : (1 + |Real.pi * ξ|)⁻¹ ≤ (1 + |ξ|)⁻¹ :=
    inv_anti₀ (by positivity) h5
  linarith

/-- Quadratic decay of an arbitrary Schwartz function. -/
lemma schwartz_decay_two (f : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2 := by
  have hS0 : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 0 0 f :=
    le_trans (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℂ f 0)
  have hS2 : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 2 0 f := by
    have h := SchwartzMap.le_seminorm' ℂ 2 0 f 1
    simpa using le_trans (mul_nonneg (by positivity) (norm_nonneg _)) h
  refine ⟨4 * SchwartzMap.seminorm ℂ 0 0 f + 4 * SchwartzMap.seminorm ℂ 2 0 f + 1,
    by linarith, fun x => ?_⟩
  have hkey : ‖f x‖ * (1 + |x|) ^ 2
      ≤ 4 * SchwartzMap.seminorm ℂ 0 0 f + 4 * SchwartzMap.seminorm ℂ 2 0 f := by
    by_cases hx : |x| ≤ 1
    · have h1 : ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f x
      have h2 : (1 + |x|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg x]
      have h3 : 0 ≤ ‖f x‖ := norm_nonneg _
      have : ‖f x‖ * (1 + |x|) ^ 2 ≤ SchwartzMap.seminorm ℂ 0 0 f * 4 :=
        mul_le_mul h1 h2 (by positivity) hS0
      linarith
    · have hx' : 1 < |x| := not_le.mp hx
      have h1 : |x| ^ 2 * ‖f x‖ ≤ SchwartzMap.seminorm ℂ 2 0 f :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 x
      have h2 : (1 + |x|) ^ 2 ≤ 4 * |x| ^ 2 := by
        have hx0 : 0 < |x| := by linarith
        nlinarith [abs_nonneg x]
      have h3 : 0 ≤ ‖f x‖ := norm_nonneg _
      have : ‖f x‖ * (1 + |x|) ^ 2 ≤ ‖f x‖ * (4 * |x| ^ 2) :=
        mul_le_mul_of_nonneg_left h2 h3
      linarith
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 + |x|) ^ 2)]
  linarith [hkey]

/-- Polynomial decay of `𝓕 Ψ` for a Schwartz function `Ψ`. -/
lemma fourier_schwartz_decay (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier (Ψ : ℝ → ℂ) ξ‖ ≤ C * (1 + |ξ|) ^ (-2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_decay_two (FourierTransform.fourier Ψ)
  refine ⟨C, hC0, fun ξ => ?_⟩
  have hfun : FourierTransform.fourier (Ψ : ℝ → ℂ) ξ = FourierTransform.fourier Ψ ξ := by
    rw [show (Ψ : ℝ → ℂ) = (⇑Ψ) from rfl]
    exact (congrFun (SchwartzMap.fourier_coe Ψ) ξ).symm
  rw [hfun]
  refine (hC ξ).trans ?_
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |ξ|), Real.rpow_ofNat, div_eq_mul_inv]

/-- Linearity of the Fourier transform on the mean-zero remainder. -/
lemma fourier_Rem_eq (Ψ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourier (Rem Ψ) ξ
      = FourierTransform.fourier (Ψ : ℝ → ℂ) ξ
        - (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * FourierTransform.fourier Lam ξ := by
  set c : ℂ := ∫ z : ℝ, (Ψ : ℝ → ℂ) z with hc
  have hEnorm : ∀ v : ℝ, ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)‖ = 1 := by
    intro v
    rw [Complex.norm_exp]
    have hre : (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hEA : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have h1 : MeasureTheory.Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (Ψ : ℝ → ℂ) v)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine (Ψ.integrable (μ := MeasureTheory.volume)).norm.mono'
      (hEA.smul (Ψ.continuous.aestronglyMeasurable)) ?_
    filter_upwards with v
    rw [norm_smul, hEnorm v, one_mul]
  have h2 : MeasureTheory.Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (c * Lam v))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine (integrable_lam.norm.const_mul ‖c‖).mono'
      (hEA.smul (integrable_lam.aestronglyMeasurable.const_mul c)) ?_
    filter_upwards with v
    rw [norm_smul, hEnorm v, one_mul, norm_mul]
  rw [Real.fourier_eq', Real.fourier_eq', Real.fourier_eq']
  have hpt : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • Rem Ψ v)
      = fun v : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (Ψ : ℝ → ℂ) v
          - Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (c * Lam v) := by
    funext v
    simp only [Rem, ← hc, smul_sub]
  rw [hpt, MeasureTheory.integral_sub h1 h2]
  congr 1
  have hsm : (fun a : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ a ξ) * Complex.I) • (c * Lam a))
      = fun a : ℝ => c • (Complex.exp (↑(-2 * Real.pi * inner ℝ a ξ) * Complex.I) • Lam a) := by
    funext a
    simp only [smul_eq_mul]
    ring
  rw [hsm, MeasureTheory.integral_smul c (fun a : ℝ =>
    Complex.exp (↑(-2 * Real.pi * inner ℝ a ξ) * Complex.I) • Lam a), smul_eq_mul]

/-- Polynomial decay of `𝓕 (Rem Ψ)`. -/
lemma rem_fourier_decay (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier (Rem Ψ) ξ‖ ≤ C * (1 + |ξ|) ^ (-N) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := fourier_schwartz_decay Ψ
  obtain ⟨C₂, hC₂0, hC₂⟩ := fourier_Lam_decay
  refine ⟨C₁ + ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * C₂, 1, by positivity, by norm_num, fun ξ => ?_⟩
  have hB2 : (1:ℝ) + |ξ| ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ]
  have hinv : ((1 + |ξ|) ^ 2)⁻¹ ≤ (1 + |ξ|)⁻¹ :=
    inv_anti₀ (by linarith [abs_nonneg ξ] : (0:ℝ) < 1 + |ξ|) hB2
  have h2 : ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z) * FourierTransform.fourier Lam ξ‖
      ≤ ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * C₂ * (1 + |ξ|) ^ (-1 : ℝ) := by
    rw [norm_mul]
    calc ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * ‖FourierTransform.fourier Lam ξ‖
        ≤ ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * (C₂ * (1 + |ξ|) ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC₂ ξ) (norm_nonneg _)
      _ = ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * C₂ * (1 + |ξ|) ^ (-1 : ℝ) := by ring
  rw [fourier_Rem_eq]
  calc ‖FourierTransform.fourier (Ψ : ℝ → ℂ) ξ
          - (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * FourierTransform.fourier Lam ξ‖
      ≤ ‖FourierTransform.fourier (Ψ : ℝ → ℂ) ξ‖
        + ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z) * FourierTransform.fourier Lam ξ‖ := norm_sub_le _ _
    _ ≤ C₁ * (1 + |ξ|) ^ (-2 : ℝ) + ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * C₂ *
          (1 + |ξ|) ^ (-1 : ℝ) := add_le_add (hC₁ ξ) h2
    _ ≤ (C₁ + ‖(∫ z : ℝ, (Ψ : ℝ → ℂ) z)‖ * C₂) * (1 + |ξ|) ^ (-(1:ℝ)) := by
        rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |ξ|),
          Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |ξ|), Real.rpow_one, Real.rpow_ofNat]
        have h3 : C₁ * ((1 + |ξ|) ^ 2)⁻¹ ≤ C₁ * (1 + |ξ|)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hC₁0.le
        linarith [h3]

/-- **The dyadic square function of the mean-zero remainder `Rem Ψ` is `L²`-bounded**, reduced to
the commons lemma `Commons.Analysis.Fourier.dyadic_square_function_l2`; only the Schwartz-type
decay of `𝓕 (Rem Ψ)` (equivalently `𝓕 Λ = O(η⁻¹)`, since `Λ = 1_I ⋆ 1_I`) remains to be proved
separately. -/
theorem dyadic_square_function_rem (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ),
      MemLp g 2 (volume : Measure ℝ) →
      ∫⁻ x : ℝ, (∑' l : ℤ,
          ‖(∫ y : ℝ, g y * ((2:ℝ)^l * Rem Ψ ((x - y) * (2:ℝ)^l)))‖ₑ ^ (2 : ℝ))
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    Commons.Analysis.Fourier.dyadic_square_function_l2 (Rem Ψ) (integrable_Rem Ψ)
      (integrable_rem_mul_x Ψ) (integral_Rem Ψ) (rem_fourier_decay Ψ)
  exact ⟨C, hC0, hC⟩

lemma theta_decay (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ,
      ‖(fun z : ℝ => (Ψ : ℝ → ℂ) z + z • deriv (Ψ : ℝ → ℂ) z) z‖ ≤ C / (1 + |z|)^2 := by
  obtain ⟨C, hC0, hC⟩ := norm_ThetaS_le Ψ
  refine ⟨C, hC0, fun z => ?_⟩
  have h : (fun z : ℝ => (Ψ : ℝ → ℂ) z + z • deriv (Ψ : ℝ → ℂ) z) z = ThetaS Ψ z := by
    simp only
    rw [ThetaS_apply, Complex.real_smul]
  rw [h]; exact hC z

theorem hasDerivAt_conv_dilate (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ)
    (hg : MemLp g 2 (volume : Measure ℝ)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ y : ℝ, g y * (s⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / s)))
      (-(t⁻¹) • ∫ y : ℝ, g y * (t⁻¹ • (fun z : ℝ => (Ψ : ℝ → ℂ) z + z • deriv (Ψ : ℝ → ℂ) z) ((x - y) / t))) t := by
  obtain ⟨C, hC0, hCΘ⟩ := theta_decay Ψ
  obtain ⟨C', hC'0, hC'⟩ := schwartz_decay_two Ψ
  set Th : ℝ → ℂ := fun z => (Ψ : ℝ → ℂ) z + z • deriv (Ψ : ℝ → ℂ) z with hTh
  set al : ℝ := min (t/4) (1/2) with hal
  have hal0 : 0 < al := by rw [hal]; positivity
  have hal1 : al ≤ t/4 := min_le_left _ _
  have hal2 : al ≤ 1/2 := min_le_right _ _
  set K : ℝ := max (1 + 2*x^2) 2 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith [le_max_right (1 + 2*x^2) (2:ℝ)]
  have hK2 : (2:ℝ) ≤ K := by rw [hK]; exact le_max_right _ _
  have hKx : 1 + 2*x^2 ≤ K := by rw [hK]; exact le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  set M : ℝ := max (C / al^2) (C' * t / al^2) * K with hM
  have hmax0 : 0 ≤ max (C / al^2) (C' * t / al^2) := by positivity
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hMCK : C / al^2 * K ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le
  have hMC'K : C' * t / al^2 * K ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hK0.le
  have hscale : ∀ (c s : ℝ), t/2 < s → al * (1 + |c|) ≤ s + |c| := by
    intro c s hs
    rcases le_total |c| 1 with h | h
    · have h1 : 1 + |c| ≤ 2 := by linarith
      have h2 : al * (1 + |c|) ≤ al * 2 := mul_le_mul_of_nonneg_left h1 hal0.le
      have h3 : al * 2 ≤ t/2 := by nlinarith [hal1, ht]
      linarith [abs_nonneg c]
    · have h2 : al * (1 + |c|) ≤ (1/2) * (1 + |c|) := mul_le_mul_of_nonneg_right hal2 (by positivity)
      have h3 : (1/2) * (1 + |c|) ≤ |c| := by linarith
      linarith [h2, h3]
  have hKy : ∀ y : ℝ, 1 + y^2 ≤ K * (1 + (x - y)^2) := by
    intro y
    have h1 : y^2 ≤ 2*x^2 + 2*(x-y)^2 := by nlinarith [sq_nonneg (2*x - y)]
    have h3 : (1 + 2*x^2) + 2*(x-y)^2 ≤ K * (1 + (x-y)^2) := by
      have h4 : (1 + 2*x^2) + 2*(x-y)^2 ≤ K + K*(x-y)^2 :=
        add_le_add (by linarith [hKx]) (by
          have := mul_le_mul_of_nonneg_left hK2 (sq_nonneg (x - y)); linarith [this])
      nlinarith [h4]
    linarith [h1, h3]
  -- key denominator bound
  have hkey : ∀ (y D σ : ℝ), 0 ≤ D → t/2 < σ →
      D / (σ + |x - y|)^2 ≤ D / al^2 * K * (1 + y^2)⁻¹ := by
    intro y D σ hD hs
    set u : ℝ := |x - y| with hu
    have hu0 : 0 ≤ u := by rw [hu]; exact abs_nonneg _
    have hu2 : u^2 = (x - y)^2 := by rw [hu, sq_abs]
    have hs0 : 0 < σ := lt_trans (by positivity) hs
    have hsp : al * (1 + u) ≤ σ + u := hscale (x - y) σ hs
    have hsp0 : 0 < al * (1 + u) := mul_pos hal0 (by linarith)
    have hsu : 0 < σ + u := by linarith
    have hsq : (al * (1 + u))^2 ≤ (σ + u)^2 := by nlinarith [hsp, hsp0, hsu]
    have hinv1 : ((σ + u)^2)⁻¹ ≤ ((al * (1 + u))^2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have hsplit : ((al * (1 + u))^2)⁻¹ = (al^2)⁻¹ * ((1 + u)^2)⁻¹ := by
      rw [mul_pow, mul_inv]
    have hinv2 : ((1 + u)^2)⁻¹ ≤ (1 + u^2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [hu0])
    have hinv3 : (1 + u^2)⁻¹ ≤ K * (1 + y^2)⁻¹ := by
      have h1 : 0 < 1 + u^2 := by positivity
      have h2 : 0 < 1 + y^2 := by positivity
      have hmain := hKy y
      rw [← hu2] at hmain
      have hmul : (1 + u^2)⁻¹ * (1 + y^2) ≤ K := by
        have h := mul_le_mul_of_nonneg_right hmain (le_of_lt (inv_pos.mpr h1))
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1), mul_one] at h
        linarith [h]
      rw [← div_eq_mul_inv K (1 + y^2), le_div_iff₀ h2]
      exact hmul
    have hmain2 : ((σ + u)^2)⁻¹ ≤ (al^2)⁻¹ * K * (1 + y^2)⁻¹ := by
      have h5 : (al^2)⁻¹ * ((1 + u)^2)⁻¹ ≤ (al^2)⁻¹ * ((1 + u^2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv2 (by positivity)
      have h6 : (al^2)⁻¹ * ((1 + u^2)⁻¹) ≤ (al^2)⁻¹ * (K * (1 + y^2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv3 (by positivity)
      calc ((σ + u)^2)⁻¹ ≤ ((al * (1 + u))^2)⁻¹ := hinv1
        _ = (al^2)⁻¹ * ((1 + u)^2)⁻¹ := hsplit
        _ ≤ (al^2)⁻¹ * ((1 + u^2)⁻¹) := h5
        _ ≤ (al^2)⁻¹ * (K * (1 + y^2)⁻¹) := h6
        _ = (al^2)⁻¹ * K * (1 + y^2)⁻¹ := by ring
    calc D / (σ + u)^2 = D * ((σ + u)^2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ D * ((al^2)⁻¹ * K * (1 + y^2)⁻¹) := mul_le_mul_of_nonneg_left hmain2 hD
      _ = D / al^2 * K * (1 + y^2)⁻¹ := by rw [div_eq_mul_inv]; ring
  -- integrability of the universal bound
  have hInt1 : Integrable (fun y : ℝ => ‖g y‖^2) volume := by
    have := hg.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hInt2 : Integrable (fun y : ℝ => (1 + y^2)⁻¹) volume := integrable_inv_one_add_sq
  have hcont2 : Continuous fun y : ℝ => (1 + y^2)⁻¹ :=
    (by fun_prop : Continuous fun y : ℝ => 1 + y^2).inv₀ (fun y => by positivity)
  have hkey_int : ∀ A : ℝ, 0 ≤ A → Integrable (fun y : ℝ => A * ‖g y‖ * (1 + y^2)⁻¹) volume := by
    intro A hA
    have hsum : Integrable (fun y : ℝ => (A/2) * ‖g y‖^2 + (A/2) * (1 + y^2)⁻¹) volume :=
      (hInt1.const_mul (A/2)).add (hInt2.const_mul (A/2))
    refine hsum.mono' ?_ ?_
    · exact ((hg.aestronglyMeasurable.norm.const_mul A)).mul hcont2.aestronglyMeasurable
    · filter_upwards with y
      have hb : 0 < 1 + y^2 := by positivity
      have hb1 : (1 + y^2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hb]; nlinarith [sq_nonneg y]
      have hb2 : ((1 + y^2)⁻¹)^2 ≤ (1 + y^2)⁻¹ := by
        have h0 : 0 ≤ (1 + y^2)⁻¹ := by positivity
        nlinarith [hb1, h0]
      have hfour : 2 * (‖g y‖ * (1 + y^2)⁻¹) ≤ ‖g y‖^2 + (1 + y^2)⁻¹ := by
        nlinarith [sq_nonneg (‖g y‖ - (1 + y^2)⁻¹), hb2, norm_nonneg (g y)]
      have hn : ‖A * ‖g y‖ * (1 + y^2)⁻¹‖ = A * ‖g y‖ * (1 + y^2)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hn]
      nlinarith [hfour, hA, norm_nonneg (g y), (by positivity : (0:ℝ) ≤ (1 + y^2)⁻¹)]
  -- bound for F'
  have hbF' : ∀ (y s : ℝ), t/2 < s →
      ‖g y * (-(s⁻¹) • (s⁻¹ • Th ((x - y)/s)))‖ ≤ M * ‖g y‖ * (1 + y^2)⁻¹ := by
    intro y s hs
    have hs0 : 0 < s := lt_trans (by positivity) hs
    set u : ℝ := |x - y| with hu
    have hu0 : 0 ≤ u := by rw [hu]; exact abs_nonneg _
    have habs : |(x - y)/s| = u/s := by rw [abs_div, abs_of_pos hs0, hu]
    have hnr1 : ‖(-(s⁻¹) : ℝ)‖ = s⁻¹ := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have hnr2 : ‖(s⁻¹ : ℝ)‖ = s⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have hnorm : ‖-(s⁻¹) • (s⁻¹ • Th ((x - y)/s))‖
        = s⁻¹ * s⁻¹ * ‖Th ((x - y)/s)‖ := by
      rw [norm_smul, norm_smul, hnr1, hnr2]; ring
    have hth : ‖Th ((x - y)/s)‖ ≤ C / (1 + u/s)^2 := by
      rw [hTh]; rw [← habs]; exact hCΘ _
    have hstep : s⁻¹ * s⁻¹ * (C / (1 + u/s)^2) = C / (s + u)^2 := by
      have hd : (1 + u/s) ≠ 0 := by positivity
      have hd2 : s + u ≠ 0 := by positivity
      field_simp
      try ring
    have hkeyy := hkey y C s hC0.le hs
    rw [← hu] at hkeyy
    rw [norm_mul, hnorm]
    have hstep2 : ‖g y‖ * (s⁻¹ * s⁻¹ * ‖Th ((x - y)/s)‖) ≤ ‖g y‖ * (C / (s + u)^2) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc s⁻¹ * s⁻¹ * ‖Th ((x - y)/s)‖ ≤ s⁻¹ * s⁻¹ * (C / (1 + u/s)^2) :=
            mul_le_mul_of_nonneg_left hth (by positivity)
        _ = C / (s + u)^2 := hstep
    refine hstep2.trans ?_
    have h3 : C / (s + u)^2 ≤ M * (1 + y^2)⁻¹ := by
      calc C / (s + u)^2 ≤ C / al^2 * K * (1 + y^2)⁻¹ := hkeyy
        _ ≤ M * (1 + y^2)⁻¹ := mul_le_mul_of_nonneg_right hMCK (by positivity)
    calc ‖g y‖ * (C / (s + u)^2) ≤ ‖g y‖ * (M * (1 + y^2)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = M * ‖g y‖ * (1 + y^2)⁻¹ := by ring
  -- bound for F at t
  have hbF : ∀ y : ℝ, ‖g y * (t⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/t))‖ ≤ M * ‖g y‖ * (1 + y^2)⁻¹ := by
    intro y
    set u : ℝ := |x - y| with hu
    have hu0 : 0 ≤ u := by rw [hu]; exact abs_nonneg _
    have habs : |(x - y)/t| = u/t := by rw [abs_div, abs_of_pos ht, hu]
    have hnr : ‖(t⁻¹ : ℝ)‖ = t⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have hnorm : ‖t⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/t)‖ = t⁻¹ * ‖(Ψ : ℝ → ℂ) ((x - y)/t)‖ := by
      rw [norm_smul, hnr]
    have hΨ : ‖(Ψ : ℝ → ℂ) ((x - y)/t)‖ ≤ C' / (1 + u/t)^2 := by
      rw [← habs]; exact hC' _
    have hstep : t⁻¹ * (C' / (1 + u/t)^2) = C' * t / (t + u)^2 := by
      have hd : (1 + u/t) ≠ 0 := by positivity
      have hd2 : t + u ≠ 0 := by positivity
      field_simp
      try ring
    have hkeyy := hkey y (C' * t) t (by positivity) (by linarith)
    rw [← hu] at hkeyy
    rw [norm_mul, hnorm]
    have hstep2 : ‖g y‖ * (t⁻¹ * ‖(Ψ : ℝ → ℂ) ((x - y)/t)‖) ≤ ‖g y‖ * (C' * t / (t + u)^2) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc t⁻¹ * ‖(Ψ : ℝ → ℂ) ((x - y)/t)‖ ≤ t⁻¹ * (C' / (1 + u/t)^2) :=
            mul_le_mul_of_nonneg_left hΨ (by positivity)
        _ = C' * t / (t + u)^2 := hstep
    refine hstep2.trans ?_
    have h3 : C' * t / (t + u)^2 ≤ M * (1 + y^2)⁻¹ :=
      calc C' * t / (t + u)^2 ≤ C' * t / al^2 * K * (1 + y^2)⁻¹ := hkeyy
        _ ≤ M * (1 + y^2)⁻¹ := mul_le_mul_of_nonneg_right hMC'K (by positivity)
    calc ‖g y‖ * (C' * t / (t + u)^2) ≤ ‖g y‖ * (M * (1 + y^2)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = M * ‖g y‖ * (1 + y^2)⁻¹ := by ring
  -- apply the parametric derivative lemma
  have hbd_int : Integrable (fun y : ℝ => M * ‖g y‖ * (1 + y^2)⁻¹) volume := hkey_int M hMnn
  have hThcont : Continuous Th := by
    have hh : Th = (ThetaS Ψ : ℝ → ℂ) := by
      funext z
      rw [hTh]
      simp only
      rw [ThetaS_apply, Complex.real_smul]
    rw [hh]
    exact (ThetaS Ψ).continuous
  have hF'_meas : AEStronglyMeasurable
      (fun y : ℝ => g y * (-(t⁻¹) • (t⁻¹ • Th ((x - y)/t)))) volume := by
    have hcont : Continuous fun y : ℝ => -(t⁻¹) • (t⁻¹ • Th ((x - y)/t)) :=
      (((hThcont.comp (by fun_prop : Continuous fun y : ℝ => (x - y)/t)).const_smul (t⁻¹))).const_smul (-(t⁻¹))
    exact hg.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun y : ℝ => g y * (s⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/s))) volume := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    refine hg.aestronglyMeasurable.mul ?_
    exact (((SchwartzMap.continuous Ψ).comp (by fun_prop : Continuous fun y : ℝ => (x - y)/s)).const_smul (s⁻¹)).aestronglyMeasurable
  have hF_int : Integrable (fun y : ℝ => g y * (t⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/t))) volume := by
    refine hbd_int.mono' ?_ ?_
    · refine hg.aestronglyMeasurable.mul ?_
      exact (((SchwartzMap.continuous Ψ).comp (by fun_prop : Continuous fun y : ℝ => (x - y)/t)).const_smul (t⁻¹)).aestronglyMeasurable
    · filter_upwards with y
      exact hbF y
  have hdiff : ∀ᵐ y ∂(volume : Measure ℝ), ∀ s ∈ Set.Ioi (t/2),
      HasDerivAt (fun s : ℝ => g y * (s⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / s)))
        (g y * (-(s⁻¹) • (s⁻¹ • Th ((x - y) / s)))) s := by
    refine Filter.Eventually.of_forall fun y s hs => ?_
    have hs0 : s ≠ 0 := ne_of_gt (lt_trans (by positivity) hs)
    have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-((s:ℝ)^2)⁻¹) s := hasDerivAt_inv hs0
    have h2 : HasDerivAt (fun s : ℝ => (x - y) / s) ((x - y) * (-((s:ℝ)^2)⁻¹)) s := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv hs0).const_mul (x - y)
    have h3 : HasDerivAt (fun s : ℝ => (Ψ : ℝ → ℂ) ((x - y) / s))
        (deriv (Ψ : ℝ → ℂ) ((x - y) / s) * ((x - y) * (-((s:ℝ)^2)⁻¹))) s := by
      have hh := (SchwartzMap.hasDerivAt Ψ ((x - y)/s)).scomp s h2
      simpa [Function.comp_def, Complex.real_smul, mul_comm] using hh
    have h4 := h1.smul h3
    refine (h4.const_mul (g y)).congr_deriv ?_
    simp only [hTh]
    congr 1
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    simp only [Complex.real_smul]
    push_cast
    field_simp
    ring
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := fun s y => g y * (s⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/s)))
    (F' := fun s y => g y * (-(s⁻¹) • (s⁻¹ • Th ((x - y)/s))))
    (x₀ := t) (s := Set.Ioi (t/2)) (μ := volume) (bound := fun y => M * ‖g y‖ * (1 + y^2)⁻¹)
    (isOpen_Ioi.mem_nhds (by linarith : t/2 < t)) hF_meas hF_int hF'_meas
    (by filter_upwards with y; exact fun s hs => hbF' y s hs) hbd_int hdiff
  have hval : (∫ y : ℝ, g y * (-(t⁻¹) • (t⁻¹ • Th ((x - y)/t))))
      = -(t⁻¹) • ∫ y : ℝ, g y * (t⁻¹ • Th ((x - y)/t)) := by
    have h1 : (∫ y : ℝ, g y * (-(t⁻¹) • (t⁻¹ • Th ((x - y)/t))))
        = ∫ y : ℝ, (-(t⁻¹)) • (g y * (t⁻¹ • Th ((x - y)/t))) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with y
      simp only [Complex.real_smul]
      ring
    rw [h1, MeasureTheory.integral_smul (-(t⁻¹)) (fun y : ℝ => g y * (t⁻¹ • Th ((x - y)/t)))]
  rw [hval] at hderiv
  exact hderiv

lemma Theta_eq_ThetaS (Ψ : SchwartzMap ℝ ℂ) : Theta Ψ = ⇑(ThetaS Ψ) := by
  funext z
  rw [Theta, ThetaS_apply]
  simp only [Complex.real_smul]

noncomputable def hfun (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ) : ℝ → ℝ :=
  fun t => 0 ⊔ (‖∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ / t)

lemma hfun_nonneg (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ) :
    ∀ t : ℝ, 0 ≤ hfun Ψ g x t := fun t => le_sup_left

lemma hfun_eq (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    hfun Ψ g x t = ‖∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ / t := by
  rw [hfun]
  exact sup_eq_right.mpr (div_nonneg (norm_nonneg _) ht.le)

lemma continuousOn_conv_theta (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ)
    (hg : MemLp g 2 (volume : Measure ℝ)) {x' y' : ℝ} (hx' : 0 < x') (hxy : x' ≤ y') :
    ContinuousOn (fun t : ℝ => ∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))) (Set.Icc x' y') := by
  obtain ⟨C, hC0, hCΘ⟩ := theta_decay Ψ
  have hy'0 : 0 < y' := lt_of_lt_of_le hx' hxy
  have hM00 : 0 < x'⁻¹ + y' := by positivity
  set K : ℝ := max (1 + 2*x^2) 2 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith [le_max_right (1 + 2*x^2) (2:ℝ)]
  have hK2 : (2:ℝ) ≤ K := by rw [hK]; exact le_max_right _ _
  have hKx : 1 + 2*x^2 ≤ K := by rw [hK]; exact le_max_left _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hM'0 : 0 ≤ C * (x'⁻¹ + y') * K := by positivity
  have hKy : ∀ y : ℝ, 1 + y^2 ≤ K * (1 + (x - y)^2) := by
    intro y
    have h1 : y^2 ≤ 2*x^2 + 2*(x-y)^2 := by nlinarith [sq_nonneg (2*x - y)]
    have h3 : (1 + 2*x^2) + 2*(x-y)^2 ≤ K * (1 + (x-y)^2) := by
      have h4 : (1 + 2*x^2) + 2*(x-y)^2 ≤ K + K*(x-y)^2 :=
        add_le_add (by linarith [hKx]) (by
          have := mul_le_mul_of_nonneg_left hK2 (sq_nonneg (x - y)); linarith [this])
      nlinarith [h4]
    linarith [h1, h3]
  have hkey : ∀ (u t : ℝ), 0 ≤ u → t ∈ Set.Icc x' y' → t/(t+u)^2 ≤ (x'⁻¹ + y')/(1+u^2) := by
    intro u t hu0 ht
    have ht1 : x' ≤ t := ht.1
    have ht2 : t ≤ y' := ht.2
    have ht0 : 0 < t := lt_of_lt_of_le hx' ht1
    have h1 : 0 < (t+u)^2 := by positivity
    have h2 : 0 < 1 + u^2 := by positivity
    rw [div_le_div_iff₀ h1 h2]
    have hfac : 0 ≤ x'⁻¹ + y' := le_of_lt (by positivity : (0:ℝ) < x'⁻¹ + y')
    rcases le_total u t with h | h
    · have hu2 : u^2 ≤ t^2 := by nlinarith [hu0, h]
      have a : t ≤ t^2 * x'⁻¹ := by
        have h2 : t * x' ≤ t^2 := by nlinarith [ht1, ht0]
        have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ x'⁻¹)
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hx'), mul_one] at h3
        linarith [h3]
      have b : t^3 ≤ y' * t^2 := by nlinarith [ht2, ht0, sq_nonneg t]
      have htu2 : t^2 ≤ (t+u)^2 := by nlinarith [hu0]
      have e1 : t * (1 + u^2) ≤ t * (1 + t^2) := by nlinarith [hu2, ht0]
      have e2 : t * (1 + t^2) ≤ (x'⁻¹ + y') * (t+u)^2 := by
        have hh : t * (1 + t^2) = t + t^3 := by ring
        have hh2 : t^2 * x'⁻¹ + y' * t^2 ≤ (x'⁻¹ + y') * (t+u)^2 := by
          have hh3 : t^2 * x'⁻¹ ≤ (t+u)^2 * x'⁻¹ := mul_le_mul_of_nonneg_right htu2 (by positivity)
          have hh4 : y' * t^2 ≤ y' * (t+u)^2 := mul_le_mul_of_nonneg_left htu2 hy'0.le
          linarith [hh3, hh4]
        linarith [hh, a, b, hh2]
      linarith [e1, e2]
    · have a : t ≤ (t+u)^2 * (x'⁻¹) := by
        have h2 : t * x' ≤ (t+u)^2 := by nlinarith [ht1, ht0, hu0]
        have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ x'⁻¹)
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hx'), mul_one] at h3
        linarith [h3]
      have b : t * u^2 ≤ y' * (t+u)^2 := by
        have h1' : u^2 ≤ (t+u)^2 := by nlinarith [ht0]
        have h2' : t * u^2 ≤ y' * u^2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)
        have h3' : y' * u^2 ≤ y' * (t+u)^2 := mul_le_mul_of_nonneg_left h1' hy'0.le
        linarith
      have e1 : t * (1 + u^2) = t + t * u^2 := by ring
      have e2 : t + t * u^2 ≤ (x'⁻¹ + y') * (t+u)^2 := by
        linarith [a, b, hfac]
      linarith [e1, e2]
  have hKy' : ∀ y u : ℝ, u = |x - y| → (1 + u^2)⁻¹ ≤ K * (1 + y^2)⁻¹ := by
    intro y u hu
    have hu2 : u^2 = (x - y)^2 := by rw [hu, sq_abs]
    have h1 : 0 < 1 + u^2 := by positivity
    have h2 : 0 < 1 + y^2 := by positivity
    have hmain := hKy y
    rw [← hu2] at hmain
    have hmul : (1 + u^2)⁻¹ * (1 + y^2) ≤ K := by
      have h := mul_le_mul_of_nonneg_right hmain (le_of_lt (inv_pos.mpr h1))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1), mul_one] at h
      linarith [h]
    rw [← div_eq_mul_inv K (1 + y^2), le_div_iff₀ h2]
    exact hmul
  have hbound : ∀ (y t : ℝ), t ∈ Set.Icc x' y' →
      ‖g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ ≤ C * (x'⁻¹ + y') * K * ‖g y‖ * (1 + y^2)⁻¹ := by
    intro y t ht
    have ht1 : x' ≤ t := ht.1
    have ht0 : 0 < t := lt_of_lt_of_le hx' ht1
    set u : ℝ := |x - y| with hu
    have hu0 : 0 ≤ u := by rw [hu]; exact abs_nonneg _
    have hnr : ‖(t⁻¹ : ℝ)‖ = t⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    have habs : |(x - y)/t| = u/t := by rw [abs_div, abs_of_pos ht0, hu]
    have hnorm : ‖g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ = ‖g y‖ * (t⁻¹ * ‖Theta Ψ ((x - y)/t)‖) := by
      rw [norm_mul, norm_smul, hnr]
    have hth : ‖Theta Ψ ((x - y)/t)‖ ≤ C / (1 + u/t)^2 := by
      rw [← habs]; exact hCΘ _
    have hsplit : t⁻¹ * (C / (1 + u/t)^2) = C * t / (t + u)^2 := by
      have hd : (1 + u/t) ≠ 0 := by positivity
      have htne : t ≠ 0 := ne_of_gt ht0
      field_simp
    have hkeyy := hkey u t hu0 ht
    have hKy'u := hKy' y u hu
    have hden : C * t / (t + u)^2 ≤ C * (x'⁻¹ + y') * K * (1 + y^2)⁻¹ := by
      calc C * t / (t + u)^2 = C * (t/(t+u)^2) := by ring
        _ ≤ C * ((x'⁻¹ + y')/(1+u^2)) := mul_le_mul_of_nonneg_left hkeyy hC0.le
        _ = C * (x'⁻¹ + y') * (1+u^2)⁻¹ := by ring
        _ ≤ C * (x'⁻¹ + y') * (K * (1+y^2)⁻¹) :=
            mul_le_mul_of_nonneg_left hKy'u (by positivity)
        _ = C * (x'⁻¹ + y') * K * (1 + y^2)⁻¹ := by ring
    rw [hnorm]
    calc ‖g y‖ * (t⁻¹ * ‖Theta Ψ ((x - y)/t)‖)
        ≤ ‖g y‖ * (t⁻¹ * (C / (1 + u/t)^2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hth (by positivity)) (norm_nonneg _)
      _ = ‖g y‖ * (C * t / (t + u)^2) := by rw [hsplit]
      _ ≤ ‖g y‖ * (C * (x'⁻¹ + y') * K * (1 + y^2)⁻¹) :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = C * (x'⁻¹ + y') * K * ‖g y‖ * (1 + y^2)⁻¹ := by ring
  have hInt1 : Integrable (fun y : ℝ => ‖g y‖^2) volume := by
    have := hg.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hInt2 : Integrable (fun y : ℝ => (1 + y^2)⁻¹) volume := integrable_inv_one_add_sq
  have hcont2 : Continuous fun y : ℝ => (1 + y^2)⁻¹ :=
    (by fun_prop : Continuous fun y : ℝ => 1 + y^2).inv₀ (fun y => by positivity)
  have hbd_int : Integrable (fun y : ℝ => C * (x'⁻¹ + y') * K * ‖g y‖ * (1 + y^2)⁻¹) volume := by
    set A : ℝ := C * (x'⁻¹ + y') * K with hA
    have hAnn : 0 ≤ A := by rw [hA]; positivity
    have hsum : Integrable (fun y : ℝ => (A/2) * ‖g y‖^2 + (A/2) * (1 + y^2)⁻¹) volume :=
      (hInt1.const_mul (A/2)).add (hInt2.const_mul (A/2))
    refine hsum.mono' ?_ ?_
    · exact ((hg.aestronglyMeasurable.norm.const_mul A)).mul hcont2.aestronglyMeasurable
    · filter_upwards with y
      have hb : 0 < 1 + y^2 := by positivity
      have hb1 : (1 + y^2)⁻¹ ≤ 1 := by rw [inv_le_one₀ hb]; nlinarith [sq_nonneg y]
      have hb2 : ((1 + y^2)⁻¹)^2 ≤ (1 + y^2)⁻¹ := by
        have h0 : 0 ≤ (1 + y^2)⁻¹ := by positivity
        nlinarith [hb1, h0]
      have hfour : 2 * (‖g y‖ * (1 + y^2)⁻¹) ≤ ‖g y‖^2 + (1 + y^2)⁻¹ := by
        nlinarith [sq_nonneg (‖g y‖ - (1 + y^2)⁻¹), hb2, norm_nonneg (g y)]
      have hn : ‖A * ‖g y‖ * (1 + y^2)⁻¹‖ = A * ‖g y‖ * (1 + y^2)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hn]
      have hgoal : A * ‖g y‖ * (1 + y^2)⁻¹ ≤ (A/2) * ‖g y‖^2 + (A/2) * (1 + y^2)⁻¹ := by
        nlinarith [hfour, hAnn, norm_nonneg (g y), (by positivity : (0:ℝ) ≤ (1 + y^2)⁻¹)]
      simpa [hA] using hgoal
  have hThetacont : Continuous (Theta Ψ) := by
    rw [Theta_eq_ThetaS]
    exact SchwartzMap.continuous (ThetaS Ψ)
  have hgc : ∀ c t : ℝ, Continuous fun y : ℝ => (c - y)/t := fun c t =>
    (continuous_const.sub continuous_id).div_const t
  refine continuousOn_of_dominated ?_ ?_ hbd_int ?_
  · intro t ht
    have hc : Continuous fun y : ℝ => Theta Ψ ((x - y)/t) := hThetacont.comp (hgc x t)
    exact hg.aestronglyMeasurable.mul (hc.const_smul (t⁻¹)).aestronglyMeasurable
  · intro t ht
    filter_upwards with y
    exact hbound y t ht
  · filter_upwards with y
    have hgcOn : ContinuousOn (fun t : ℝ => (x - y)/t) (Set.Icc x' y') := by
      have h1 : ContinuousOn (fun t : ℝ => (x - y) * t⁻¹) (Set.Icc x' y') :=
        (continuous_const.continuousOn).mul
          (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le hx' ht.1)))
      simpa [div_eq_mul_inv] using h1
    have h1c : ContinuousOn (fun t : ℝ => Theta Ψ ((x - y)/t)) (Set.Icc x' y') :=
      hThetacont.continuousOn.comp hgcOn (fun t _ => Set.mem_univ _)
    have h2c : ContinuousOn (fun t : ℝ => t⁻¹ • Theta Ψ ((x - y)/t)) (Set.Icc x' y') :=
      ContinuousOn.smul (f := fun t : ℝ => t⁻¹) (g := fun t : ℝ => Theta Ψ ((x - y)/t))
        (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le hx' ht.1))) h1c
    exact continuous_const.continuousOn.mul h2c

lemma continuousOn_hfun (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ)
    (hg : MemLp g 2 (volume : Measure ℝ)) {x' y' : ℝ} (hx' : 0 < x') (hxy : x' ≤ y') :
    ContinuousOn (hfun Ψ g x) (Set.Icc x' y') := by
  have h1 := (continuousOn_conv_theta Ψ g x hg hx' hxy).norm
  have h4 : ContinuousOn (fun t : ℝ => ‖∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ / t)
      (Set.Icc x' y') :=
    ContinuousOn.div (f := fun t : ℝ => ‖∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖)
      (g := fun t : ℝ => t) h1 continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le hx' ht.1))
  exact ContinuousOn.sup continuousOn_const h4

lemma intervalIntegrable_hfun (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ)
    (hg : MemLp g 2 (volume : Measure ℝ)) {x' y' : ℝ} (hx' : 0 < x') (hxy : x' ≤ y') :
    IntervalIntegrable (hfun Ψ g x) volume x' y' := by
  have h := continuousOn_hfun Ψ g x hg hx' hxy
  refine ContinuousOn.intervalIntegrable ?_
  rwa [Set.uIcc_of_le hxy]

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory

lemma conv_dilate_ftc (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ)
    (hg : MemLp g 2 (volume : Measure ℝ)) {x' y' : ℝ} (hx' : 0 < x') (hxy : x' ≤ y') :
    ‖(∫ y : ℝ, g y * (y'⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/y')))
        - (∫ y : ℝ, g y * (x'⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/x')))‖ ≤ ∫ t in x'..y', hfun Ψ g x t := by
  have huI : Set.uIcc x' y' = Set.Icc x' y' := Set.uIcc_of_le hxy
  have hderiv : ∀ t ∈ Set.uIcc x' y',
      HasDerivAt (fun s : ℝ => ∫ y : ℝ, g y * (s⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/s)))
        (-(t⁻¹) • ∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))) t := by
    intro t ht
    rw [huI] at ht
    exact hasDerivAt_conv_dilate Ψ g x hg (lt_of_lt_of_le hx' ht.1)
  have hF'int : IntervalIntegrable
      (fun t : ℝ => -(t⁻¹) • ∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))) volume x' y' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huI]
    have h1 := continuousOn_conv_theta Ψ g x hg hx' hxy
    have h2 : ContinuousOn (fun t : ℝ => -(t⁻¹)) (Set.Icc x' y') :=
      (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le hx' ht.1))).neg
    exact ContinuousOn.smul (f := fun t : ℝ => -(t⁻¹))
      (g := fun t : ℝ => ∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))) h2 h1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hF'int
  rw [← hFTC]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
  have hcongr : ∀ t ∈ Set.uIcc x' y',
      ‖-(t⁻¹) • (∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t)))‖ = hfun Ψ g x t := by
    intro t ht
    rw [huI] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hx' ht.1
    have h1 : ‖-(t⁻¹) • (∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t)))‖
        = t⁻¹ * ‖∫ y : ℝ, g y * (t⁻¹ • Theta Ψ ((x - y)/t))‖ := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    rw [h1, hfun_eq Ψ g x ht0, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr hcongr]

lemma norm_fourier_le_integral_norm' {k : ℝ → ℂ} (hk : Integrable k) (ξ : ℝ) :
    ‖FourierTransform.fourier k ξ‖ ≤ ∫ z : ℝ, ‖k z‖ := by
  rw [Real.fourier_eq]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [Circle.norm_smul, one_mul])

theorem lintegral_convolution_sq_eq_l2 {g k : ℝ → ℂ} (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hk1 : MemLp k 1 (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ENNReal.ofReal ‖∫ y : ℝ, g y * k (x - y)‖ ^ (2:ℝ)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖(FourierTransform.fourier (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ * ‖FourierTransform.fourier k ξ‖) ^ (2:ℝ) := by
  have hkI : Integrable k := memLp_one_iff_integrable.mp hk1
  have hFk_cont : Continuous (fun ξ : ℝ => FourierTransform.fourier k ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hkI
  have hkt : MemLp (fun ξ : ℝ => FourierTransform.fourier k ξ) ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound hFk_cont.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ξ => norm_fourier_le_integral_norm' hkI ξ)
  have hmc := multiplier_eq_convolution_ae k hkI hkt (hg2.toLp g)
  have hgcoe : ∀ x : ℝ, (∫ y : ℝ, g y * k (x - y)) = ∫ y : ℝ, (hg2.toLp g : ℝ → ℂ) y * k (x - y) :=
    fun x => MeasureTheory.integral_congr_ae ((MemLp.coeFn_toLp hg2).symm.mul (Filter.EventuallyEq.refl _ _))
  simp only [hgcoe]
  have hstep : (∫⁻ x : ℝ,
        ENNReal.ofReal ‖∫ y : ℝ, (hg2.toLp g : ℝ → ℂ) y * k (x - y)‖ ^ (2:ℝ))
      = ∫⁻ x : ℝ, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ => FourierTransform.fourier k ξ) hkt
          (hg2.toLp g) : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hmc] with x hx
    rw [hx, Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm]
  rw [hstep, ← Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ => FourierTransform.fourier k ξ) hkt (hg2.toLp g)),
    Commons.Analysis.Fourier.BoundaryLayer.enorm_multiplier_sq]
  refine lintegral_congr (fun ξ => ?_)
  have h1 : (‖FourierTransform.fourier k ξ‖ₑ : ENNReal) ^ (2:ℝ) = ENNReal.ofReal (‖FourierTransform.fourier k ξ‖ ^ 2) := by
    rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : (‖((FourierTransform.fourier (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ₑ : ENNReal) ^ (2:ℝ)
      = ENNReal.ofReal (‖((FourierTransform.fourier (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2) := by
    rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity),
    show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (by positivity)]
  congr 1
  ring

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier

open scoped RealInnerProductSpace

/-- `FourierTransform.fourier (c · K) = c · FourierTransform.fourier K`. -/
lemma fourier_const_mul_schwartz (K : SchwartzMap ℝ ℂ) (c : ℂ) :
    FourierTransform.fourier (fun z : ℝ => c * (K : ℝ → ℂ) z) = fun ξ : ℝ => c * (FourierTransform.fourier K : SchwartzMap ℝ ℂ) ξ := by
  funext ξ
  rw [Real.fourier_eq']
  have h : (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)
        • (c * (K : ℝ → ℂ) v))
      = c * ∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (K : ℝ → ℂ) v := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]; ring
  rw [h]
  congr 1
  rw [congrFun (SchwartzMap.fourier_coe K) ξ, Real.fourier_eq']

/-- `FourierTransform.fourier (z ↦ t⁻¹ • K (z/t)) ξ = FourierTransform.fourier K (t ξ)`. -/
lemma fourier_dilate_schwartz (K : SchwartzMap ℝ ℂ) {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    FourierTransform.fourier (fun z : ℝ => t⁻¹ • (K : ℝ → ℂ) (z / t)) ξ = (FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ) := by
  have h1 : (fun z : ℝ => t⁻¹ • (K : ℝ → ℂ) (z / t))
      = fun z : ℝ => (fun w : ℝ => ((t⁻¹ : ℝ) : ℂ) * (K : ℝ → ℂ) w) (z / t) := by
    funext z; rw [Complex.real_smul]
  rw [h1, fourier_comp_div (fun w : ℝ => ((t⁻¹ : ℝ) : ℂ) * (K : ℝ → ℂ) w) ht ξ,
    congrFun (fourier_const_mul_schwartz K ((t⁻¹ : ℝ) : ℂ)) (ξ * t)]
  have h2 : (t : ℂ) * (((t⁻¹ : ℝ) : ℂ) * (FourierTransform.fourier K : SchwartzMap ℝ ℂ) (ξ * t))
      = (FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt ht), Complex.ofReal_one,
      one_mul, mul_comm ξ t]
  rw [h2]


open _root_.MeasureTheory

lemma integrable_dilation_real {K : ℝ → ℂ} (hK : Integrable K) {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => t⁻¹ • K (z / t)) := by
  have htne : t⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt ht)
  have h := (hK.comp_smul (R := t⁻¹) htne).const_mul (((t⁻¹ : ℝ) : ℂ))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Complex.real_smul, div_eq_mul_inv, smul_eq_mul]
  congr 2
  ring

/-- `‖x • K x‖` is integrable for Schwartz `K`. -/
lemma integrable_norm_smul_id (K : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ‖x • (K : ℝ → ℂ) x‖) := by
  have hg : Function.HasTemperateGrowth (fun z : ℝ => (z : ℂ)) := by fun_prop
  have h := (SchwartzMap.smulLeftCLM ℂ (fun z : ℝ => (z : ℂ)) K).integrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  rw [SchwartzMap.smulLeftCLM_apply hg] at h
  exact h.norm

/-- **Lipschitz at `0` of `𝓕K`** when `∫K = 0`. -/
lemma fourier_abs_le_of_integral_zero (K : SchwartzMap ℝ ℂ)
    (hK0 : (∫ x : ℝ, (K : ℝ → ℂ) x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) ξ‖ ≤ C * |ξ| := by
  refine ⟨2 * Real.pi * (∫ x : ℝ, ‖x • (K : ℝ → ℂ) x‖) + 1, by positivity, fun ξ => ?_⟩
  have hcoe : ∀ y : ℝ, (FourierTransform.fourier K : SchwartzMap ℝ ℂ) y
      = ∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * (v * y)) * Complex.I) • (K : ℝ → ℂ) v := by
    intro y
    rw [congrFun (SchwartzMap.fourier_coe K) y, Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Real.inner_apply]
  have hE : Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) • (K : ℝ → ℂ) v) := by
    have hcont : Continuous fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) :=
      Complex.continuous_exp.comp (by fun_prop)
    refine (K.integrable).norm.mono'
      ((hcont.aestronglyMeasurable).mul K.continuous.aestronglyMeasurable) ?_
    filter_upwards with v
    rw [smul_eq_mul, norm_mul]
    have h1 : ‖Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, one_mul]
  have hsub : (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) • (K : ℝ → ℂ) v)
      = ∫ v : ℝ, (Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) - 1) • (K : ℝ → ℂ) v := by
    have h := MeasureTheory.integral_sub hE (K.integrable)
    rw [hK0, sub_zero] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [sub_smul, one_smul]
  rw [hcoe ξ, hsub]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hb : ∀ v : ℝ,
      ‖(Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) - 1) • (K : ℝ → ℂ) v‖
        ≤ 2 * Real.pi * |ξ| * ‖v • (K : ℝ → ℂ) v‖ := by
    intro v
    have h2 : ‖Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) - 1‖
        ≤ ‖(-2 * Real.pi * (v * ξ) : ℝ)‖ := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * Real.pi * (v * ξ))
      simpa only [Complex.ofReal_mul, mul_comm, Complex.ofReal_neg, Complex.ofReal_ofNat,
        mul_assoc, mul_left_comm] using this
    have h3 : ‖Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) - 1‖ ≤ 2 * Real.pi * |v| * |ξ| := by
      refine h2.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_mul]
      ring
    have h5 : ‖v • (K : ℝ → ℂ) v‖ = |v| * ‖(K : ℝ → ℂ) v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [norm_smul]
    have h6 : (2 * Real.pi * |v| * |ξ|) * ‖(K : ℝ → ℂ) v‖
        = 2 * Real.pi * |ξ| * ‖v • (K : ℝ → ℂ) v‖ := by rw [h5]; ring
    rw [← h6]
    exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  have hint : Integrable (fun v : ℝ => 2 * Real.pi * |ξ| * ‖v • (K : ℝ → ℂ) v‖) :=
    (integrable_norm_smul_id K).const_mul _
  calc ∫ v : ℝ, ‖(Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) - 1) • (K : ℝ → ℂ) v‖
      ≤ ∫ v : ℝ, 2 * Real.pi * |ξ| * ‖v • (K : ℝ → ℂ) v‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun v => hb v)
    _ = 2 * Real.pi * |ξ| * ∫ v : ℝ, ‖v • (K : ℝ → ℂ) v‖ := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (2 * Real.pi * (∫ x : ℝ, ‖x • (K : ℝ → ℂ) x‖) + 1) * |ξ| := by
        have hnn : 0 ≤ ∫ x : ℝ, ‖x • (K : ℝ → ℂ) x‖ := integral_nonneg (fun v => norm_nonneg _)
        nlinarith [abs_nonneg ξ, hnn]


open _root_.MeasureTheory

open scoped _root_.BigOperators _root_.ENNReal _root_.FourierTransform _root_.Topology _root_.RealInnerProductSpace

/-- The within-level ("short") variations are bounded in `L²` (with an `s`-independent constant)
by the continuum square function of the mean-zero kernel `Theta Ψ`. -/
lemma lintegral_inv_mul_comp_mul_le {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫⁻ t, ENNReal.ofReal t⁻¹ * ψ (t * ξ)
      ≤ ∫⁻ u in {u : ℝ | u ≠ 0}, ENNReal.ofReal |u|⁻¹ * ψ u := by
  set F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |u|⁻¹ * ψ u with hFdef
  have hF : Measurable F := by rw [hFdef]; measurability
  have hξa : |ξ| ≠ 0 := abs_ne_zero.mpr hξ
  have hpt : ∀ t : ℝ, ENNReal.ofReal t⁻¹ * ψ (t * ξ)
      = ENNReal.ofReal |ξ| * (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t := by
    intro t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
      change ENNReal.ofReal t⁻¹ * ψ (t * ξ)
        = ENNReal.ofReal |ξ| * (ENNReal.ofReal |t * ξ|⁻¹ * ψ (t * ξ))
      have h1 : t⁻¹ = |ξ| * |t * ξ|⁻¹ := by
        rw [abs_mul, abs_of_pos ht, mul_inv, ← mul_assoc, mul_comm |ξ| t⁻¹, mul_assoc,
          mul_inv_cancel₀ hξa, mul_one]
      rw [h1, ENNReal.ofReal_mul (abs_nonneg ξ), mul_assoc]
    · have htle : t ≤ 0 := le_of_not_gt ht
      rw [Set.indicator_of_notMem (by simpa using ht), mul_zero]
      have htinv : t⁻¹ ≤ 0 := by
        rcases lt_or_eq_of_le htle with h | h
        · exact le_of_lt ((inv_neg'').mpr h)
        · rw [h]; simp
      rw [ENNReal.ofReal_eq_zero.mpr htinv, zero_mul]
  have hmeasG : Measurable (fun t : ℝ => (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t) :=
    (hF.comp (by fun_prop : Measurable fun t : ℝ => t * ξ)).indicator measurableSet_Ioi
  have hsmul : Measure.map (fun t : ℝ => ξ • t) volume = ENNReal.ofReal |ξ⁻¹| • volume := by
    have h := MeasureTheory.Measure.map_addHaar_smul (μ := volume) (E := ℝ) hξ
    simpa using h
  have hcancel : ENNReal.ofReal |ξ| * ENNReal.ofReal |ξ⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg ξ), abs_inv, mul_inv_cancel₀ hξa, ENNReal.ofReal_one]
  rcases lt_trichotomy ξ 0 with hneg | hzero | hpos
  · -- ξ < 0 : the factor `1_{t > 0}` becomes `1_{ξt < 0}`
    have hkey : ∀ t : ℝ, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t
        = (Set.Iio (0:ℝ)).indicator F (ξ • t) := by
      intro t
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · have h2 : ξ • t ∈ Set.Iio (0:ℝ) := by
          rw [Set.mem_Iio, smul_eq_mul]
          rw [Set.mem_Ioi] at ht
          exact mul_neg_of_neg_of_pos hneg ht
        rw [if_pos ht, if_pos h2, smul_eq_mul, mul_comm]
      · have h2 : ξ • t ∉ Set.Iio (0:ℝ) := by
          rw [Set.mem_Iio, smul_eq_mul]
          intro hc
          exact ht (Set.mem_Ioi.mpr (by nlinarith [hneg, hc]))
        rw [if_neg ht, if_neg h2]
    have hstep : ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t
        = ENNReal.ofReal |ξ⁻¹| * ∫⁻ u in Set.Iio (0:ℝ), F u := by
      rw [lintegral_congr hkey,
        ← lintegral_map (f := (Set.Iio (0:ℝ)).indicator F) (g := fun t : ℝ => ξ • t)
          (hF.indicator measurableSet_Iio) (by fun_prop),
        hsmul, lintegral_smul_measure, smul_eq_mul]
      congr 1
      rw [← lintegral_indicator measurableSet_Iio (f := F)]
    calc ∫⁻ t, ENNReal.ofReal t⁻¹ * ψ (t * ξ)
        = ENNReal.ofReal |ξ| * ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t := by
          rw [lintegral_congr hpt]; exact lintegral_const_mul _ hmeasG
      _ = ENNReal.ofReal |ξ| * (ENNReal.ofReal |ξ⁻¹| * ∫⁻ u in Set.Iio (0:ℝ), F u) := by
          rw [hstep]
      _ = ∫⁻ u in Set.Iio (0:ℝ), F u := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ ∫⁻ u in {u : ℝ | u ≠ 0}, F u := by
          refine lintegral_mono_set ?_
          intro u hu
          rw [Set.mem_Iio] at hu
          exact ne_of_lt hu
  · exact absurd hzero hξ
  · -- ξ > 0
    have hkey : ∀ t : ℝ, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t
        = (Set.Ioi (0:ℝ)).indicator F (ξ • t) := by
      intro t
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · have h2 : ξ • t ∈ Set.Ioi (0:ℝ) := by
          rw [Set.mem_Ioi, smul_eq_mul]
          rw [Set.mem_Ioi] at ht
          exact mul_pos hpos ht
        rw [if_pos ht, if_pos h2, smul_eq_mul, mul_comm]
      · have h2 : ξ • t ∉ Set.Ioi (0:ℝ) := by
          rw [Set.mem_Ioi, smul_eq_mul]
          intro hc
          exact ht (Set.mem_Ioi.mpr (by nlinarith [hpos, hc]))
        rw [if_neg ht, if_neg h2]
    have hstep : ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t
        = ENNReal.ofReal |ξ⁻¹| * ∫⁻ u in Set.Ioi (0:ℝ), F u := by
      rw [lintegral_congr hkey,
        ← lintegral_map (f := (Set.Ioi (0:ℝ)).indicator F) (g := fun t : ℝ => ξ • t)
          (hF.indicator measurableSet_Ioi) (by fun_prop),
        hsmul, lintegral_smul_measure, smul_eq_mul]
      congr 1
      rw [← lintegral_indicator measurableSet_Ioi (f := F)]
    calc ∫⁻ t, ENNReal.ofReal t⁻¹ * ψ (t * ξ)
        = ENNReal.ofReal |ξ| * ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => F (t * ξ)) t := by
          rw [lintegral_congr hpt]; exact lintegral_const_mul _ hmeasG
      _ = ENNReal.ofReal |ξ| * (ENNReal.ofReal |ξ⁻¹| * ∫⁻ u in Set.Ioi (0:ℝ), F u) := by
          rw [hstep]
      _ = ∫⁻ u in Set.Ioi (0:ℝ), F u := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ ∫⁻ u in {u : ℝ | u ≠ 0}, F u := by
          refine lintegral_mono_set ?_
          intro u hu
          rw [Set.mem_Ioi] at hu
          exact ne_of_gt hu


lemma aemeasurable_dilate_convolution {K f : ℝ → ℂ} (hKc : Continuous K) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun p : ℝ × ℝ =>
      ∫ y, f y * ((((p.2⁻¹ : ℝ)) : ℂ) * K ((p.1 - y)/p.2))) (volume.prod volume) := by
  have hkern : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      f q.2 * ((((q.1.2⁻¹ : ℝ)) : ℂ) * K ((q.1.1 - q.2)/q.1.2)))
      ((volume.prod volume).prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f q.2)
        ((volume.prod volume).prod volume) := hf.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
        ((((q.1.2⁻¹ : ℝ)) : ℂ) * K ((q.1.1 - q.2)/q.1.2)))
        ((volume.prod volume).prod volume) := by
      refine Measurable.aestronglyMeasurable ?_
      have hA : Measurable (fun q : (ℝ × ℝ) × ℝ => ((((q.1.2⁻¹ : ℝ)) : ℂ))) := by
        refine Measurable.complex_ofReal ?_
        exact measurable_inv.comp (measurable_snd.comp measurable_fst)
      have hB' : Measurable (fun q : (ℝ × ℝ) × ℝ => K ((q.1.1 - q.2)/q.1.2)) := by
        refine hKc.measurable.comp ?_
        measurability
      exact hA.mul hB'
    exact h1.mul h2
  exact (hkern.integral_prod_right').aemeasurable

/-- **Joint measurability of the `g`-integrand in `(x, t)`.** -/
lemma aemeasurable_gJoint {K f : ℝ → ℂ} (hKc : Continuous K) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (Function.uncurry (fun x t : ℝ => ENNReal.ofReal t⁻¹ *
      (ENNReal.ofReal ‖∫ y : ℝ, f y * ((((t⁻¹ : ℝ)) : ℂ) * K ((x - y)/t))‖) ^ (2:ℝ)))
      (volume.prod volume) := by
  have hB := aemeasurable_dilate_convolution (K := K) hKc hf
  have h2 : AEMeasurable (fun p : ℝ × ℝ =>
      (ENNReal.ofReal ‖∫ y : ℝ, f y * ((((p.2⁻¹ : ℝ)) : ℂ) * K ((p.1 - y)/p.2))‖) ^ (2:ℝ))
      (volume.prod volume) := (hB.norm.ennreal_ofReal).pow_const _
  exact (Measurable.ennreal_ofReal (measurable_inv.comp measurable_snd)).aemeasurable.mul h2




/-- Monotonicity of the restricted integral on a measurable set. -/
lemma lintegral_mono_restrict {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ≥0∞}
    (h : ∀ u ∈ s, f u ≤ g u) : ∫⁻ u in s, f u ≤ ∫⁻ u in s, g u := by
  rw [← lintegral_indicator hs f, ← lintegral_indicator hs g]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ s
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]; exact h u hu
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]

/-- Finiteness of the "g-function" constant: for a Schwartz `K` with `∫K = 0` the integral
`∫⁻_{u≠0} |u|⁻¹ ‖𝓕K u‖²` is finite.  (Lipschitz at `0` from the vanishing mean, plus
quadratic Schwartz decay at infinity.) -/
lemma lintegral_inv_mul_fourier_schwartz_le (K : SchwartzMap ℝ ℂ)
    (hK0 : (∫ x : ℝ, (K : ℝ → ℂ) x) = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∫⁻ u in {u : ℝ | u ≠ 0},
        ENNReal.ofReal |u|⁻¹ * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ ^ 2)
        ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fourier_abs_le_of_integral_zero K hK0
  obtain ⟨C₂, hC₂pos, hC₂⟩ := schwartz_decay_two (FourierTransform.fourier K)
  set F : ℝ → ℝ := fun u => ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ with hFdef
  have hFnn : ∀ u : ℝ, 0 ≤ F u := fun u => norm_nonneg _
  refine ⟨C₁ ^ 2 * 2 + C₂ ^ 2 * Real.pi, by positivity, ?_⟩
  have hrew : ∫⁻ u in {u : ℝ | u ≠ 0},
        ENNReal.ofReal |u|⁻¹ * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ ^ 2)
      = ∫⁻ u in {u : ℝ | u ≠ 0}, ENNReal.ofReal (|u|⁻¹ * F u ^ 2) := by
    refine lintegral_congr fun u => ?_
    rw [show (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ ^ 2) = F u ^ 2 from rfl]
    exact (ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg u))).symm
  rw [hrew]
  have hmono : ∫⁻ u in {u : ℝ | u ≠ 0}, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2) := by
    have h := lintegral_mono_set (μ := (volume : Measure ℝ)) (s := {u : ℝ | u ≠ 0})
      (t := Set.univ) (f := fun u => ENNReal.ofReal (|u|⁻¹ * F u ^ 2))
      (fun u _ => Set.mem_univ u)
    simpa using h
  have hsplit : ∫⁻ u : ℝ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2) ∂(volume : Measure ℝ)
      = (∫⁻ u in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|u|⁻¹ * F u ^ 2))
        + (∫⁻ u in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)) := by
    rw [lintegral_add_compl (μ := (volume : Measure ℝ)) (A := Set.Icc (-1:ℝ) 1)
      (fun u : ℝ => ENNReal.ofReal (|u|⁻¹ * F u ^ 2)) measurableSet_Icc]
  have hreg1 : ∫⁻ u in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
      ≤ ENNReal.ofReal (C₁ ^ 2 * 2) := by
    have hpt : ∀ u ∈ Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|u|⁻¹ * F u ^ 2) ≤ ENNReal.ofReal (C₁ ^ 2) := by
      intro u hu
      refine ENNReal.ofReal_le_ofReal ?_
      have hu1 : |u| ≤ 1 := abs_le.mpr (by rw [Set.mem_Icc] at hu; exact hu)
      have h2 : F u ^ 2 ≤ (C₁ * |u|) ^ 2 := pow_le_pow_left₀ (hFnn u) (hC₁ u) 2
      rcases eq_or_lt_of_le (abs_nonneg u) with h | h
      · rw [← h, inv_zero, zero_mul]; positivity
      · have hinv : |u|⁻¹ * |u| ^ 2 = |u| := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt h), one_mul]
        calc |u|⁻¹ * F u ^ 2 ≤ |u|⁻¹ * (C₁ * |u|) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (abs_nonneg u))
          _ = C₁ ^ 2 * (|u|⁻¹ * |u| ^ 2) := by ring
          _ = C₁ ^ 2 * |u| := by rw [hinv]
          _ ≤ C₁ ^ 2 := by nlinarith [abs_nonneg u, sq_nonneg C₁, hC₁pos, hu1]
    calc ∫⁻ u in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
        ≤ ∫⁻ u in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (C₁ ^ 2) :=
          lintegral_mono_restrict measurableSet_Icc hpt
      _ = ENNReal.ofReal (C₁ ^ 2) * (volume : Measure ℝ) (Set.Icc (-1:ℝ) 1) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      _ = ENNReal.ofReal (C₁ ^ 2) * ENNReal.ofReal 2 := by
          rw [Real.volume_Icc]; norm_num
      _ = ENNReal.ofReal (C₁ ^ 2 * 2) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg C₁)]
  have hreg2 : ∫⁻ u in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
      ≤ ENNReal.ofReal (C₂ ^ 2 * Real.pi) := by
    have hpt : ∀ u ∈ (Set.Icc (-1:ℝ) 1)ᶜ,
        ENNReal.ofReal (|u|⁻¹ * F u ^ 2) ≤ ENNReal.ofReal (C₂ ^ 2 * (1 + u ^ 2)⁻¹) := by
      intro u hu
      refine ENNReal.ofReal_le_ofReal ?_
      have hu1 : 1 < |u| := by
        rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hF2 : F u ^ 2 ≤ (C₂ / (1 + |u|) ^ 2) ^ 2 := pow_le_pow_left₀ (hFnn u) (hC₂ u) 2
      have h4 : (C₂ / (1 + |u|) ^ 2) ^ 2 = C₂ ^ 2 / (1 + |u|) ^ 4 := by
        rw [div_pow, ← pow_mul]
      have hstep : |u|⁻¹ * F u ^ 2 ≤ C₂ ^ 2 / (1 + |u|) ^ 4 := by
        calc |u|⁻¹ * F u ^ 2 ≤ |u|⁻¹ * (C₂ ^ 2 / (1 + |u|) ^ 4) := by
              rw [← h4]
              exact mul_le_mul_of_nonneg_left hF2 (inv_nonneg.mpr (abs_nonneg u))
          _ ≤ 1 * (C₂ ^ 2 / (1 + |u|) ^ 4) :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (le_of_lt hu1)) (by positivity)
          _ = C₂ ^ 2 / (1 + |u|) ^ 4 := one_mul _
      have hle : 1 + u ^ 2 ≤ (1 + |u|) ^ 4 := by
        have h1 : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by
          have := sq_abs u; nlinarith [abs_nonneg u]
        exact h1.trans (pow_le_pow_right₀ (by linarith [abs_nonneg u] : (1:ℝ) ≤ 1 + |u|)
          (by norm_num))
      calc |u|⁻¹ * F u ^ 2 ≤ C₂ ^ 2 / (1 + |u|) ^ 4 := hstep
        _ = C₂ ^ 2 * ((1 + |u|) ^ 4)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ C₂ ^ 2 * (1 + u ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hle) (sq_nonneg C₂)
    calc ∫⁻ u in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
        ≤ ∫⁻ u in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (C₂ ^ 2 * (1 + u ^ 2)⁻¹) :=
          lintegral_mono_restrict (measurableSet_Icc.compl) hpt
      _ ≤ ∫⁻ u : ℝ, ENNReal.ofReal (C₂ ^ 2 * (1 + u ^ 2)⁻¹) := by
          have h := lintegral_mono_set (μ := (volume : Measure ℝ)) (s := (Set.Icc (-1:ℝ) 1)ᶜ)
            (t := Set.univ) (f := fun u => ENNReal.ofReal (C₂ ^ 2 * (1 + u ^ 2)⁻¹))
            (fun u _ => Set.mem_univ u)
          simpa using h
      _ = ∫⁻ u : ℝ, ENNReal.ofReal (C₂ ^ 2) * ENNReal.ofReal ((1 + u ^ 2)⁻¹) :=
          lintegral_congr fun u => ENNReal.ofReal_mul (sq_nonneg C₂)
      _ = ENNReal.ofReal (C₂ ^ 2) * ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2)⁻¹) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (C₂ ^ 2) * ENNReal.ofReal Real.pi := by
          rw [← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
            (Filter.Eventually.of_forall fun x => by positivity), integral_univ_inv_one_add_sq]
      _ = ENNReal.ofReal (C₂ ^ 2 * Real.pi) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg C₂)]
  calc ∫⁻ u in {u : ℝ | u ≠ 0}, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2) := hmono
    _ = (∫⁻ u in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|u|⁻¹ * F u ^ 2))
        + (∫⁻ u in (Set.Icc (-1:ℝ) 1)ᶜ, ENNReal.ofReal (|u|⁻¹ * F u ^ 2)) := hsplit
    _ ≤ ENNReal.ofReal (C₁ ^ 2 * 2) + ENNReal.ofReal (C₂ ^ 2 * Real.pi) := add_le_add hreg1 hreg2
    _ = ENNReal.ofReal (C₁ ^ 2 * 2 + C₂ ^ 2 * Real.pi) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm


theorem g_function_dilation_schwartz (K : SchwartzMap ℝ ℂ)
    (hK0 : (∫ x : ℝ, (K : ℝ → ℂ) x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℂ, MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖∫ y : ℝ, f y * (t⁻¹ • (K : ℝ → ℂ) ((x - y)/t))‖) ^ (2:ℝ)
        ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀le⟩ := lintegral_inv_mul_fourier_schwartz_le K hK0
  refine ⟨C₀, hC₀pos, fun f hf => ?_⟩
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fourier_abs_le_of_integral_zero K hK0
  have hF0 : ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) 0‖ = 0 := by
    have h := hC₁ 0
    simp only [abs_zero, mul_zero] at h
    exact le_antisymm h (norm_nonneg _)
  set G : ℝ → ℝ → ℂ := fun t x => ∫ y : ℝ, f y * (t⁻¹ • (K : ℝ → ℂ) ((x - y)/t)) with hG
  set FF : Lp ℂ 2 (volume : Measure ℝ) := FourierTransform.fourier (hf.toLp f) with hFF
  set A : ℝ≥0∞ := ∫⁻ u in {u : ℝ | u ≠ 0},
      ENNReal.ofReal |u|⁻¹ * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ ^ 2) with hA
  have hAle : A ≤ ENNReal.ofReal C₀ := by rw [hA]; exact hC₀le
  -- The integrand vanishes for `t ≤ 0`, so the restricted integral is the unrestricted one.
  have hPhi_zero : ∀ t : ℝ, t ≤ 0 → ∀ x : ℝ,
      ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) = 0 := by
    intro t ht x
    have htinv : t⁻¹ ≤ 0 := by
      rcases lt_or_eq_of_le ht with h | h
      · exact le_of_lt (inv_neg''.mpr h)
      · rw [h]; simp
    rw [ENNReal.ofReal_eq_zero.mpr htinv, zero_mul]
  have hIoi : ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)
      = ∫⁻ x, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) := by
    refine lintegral_congr fun x => ?_
    have hind : (Set.Ioi (0:ℝ)).indicator
          (fun t : ℝ => ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ))
        = fun t : ℝ => ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) := by
      funext t
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht,
          (hPhi_zero t (le_of_not_gt (by rwa [Set.mem_Ioi] at ht)) x).symm]
    rw [← lintegral_indicator measurableSet_Ioi, hind]
  -- joint measurability in `(x,t)`, hence Tonelli
  have hjoint : AEMeasurable
      (Function.uncurry (fun x t : ℝ => ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)))
      (volume.prod volume) := by
    have h0 := aemeasurable_gJoint (K := (K : ℝ → ℂ)) K.continuous hf
    refine h0.congr ?_
    filter_upwards with p
    simp only [Function.uncurry, hG]
    rfl
  have hswap : ∫⁻ x, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)
      = ∫⁻ t : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) :=
    lintegral_lintegral_swap (f := fun x t : ℝ => ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)) hjoint
  -- pull the constant `t⁻¹` out of the inner `x`-integral
  have hstepB : ∫⁻ t : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)
      = ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ x : ℝ, (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)) := by
    refine lintegral_congr fun t => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Plancherel for the convolution with `t⁻¹ • K(·/t)`, for `t > 0`
  have hperT : ∀ t : ℝ, 0 < t →
      ∫⁻ x : ℝ, (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)
        = ∫⁻ ξ : ℝ, (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
            * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ) := by
    intro t ht
    have hk1 : MemLp (fun z : ℝ => t⁻¹ • (K : ℝ → ℂ) (z / t)) 1 (volume : Measure ℝ) :=
      memLp_one_iff_integrable.mpr (integrable_dilation_real K.integrable ht)
    have hmain := lintegral_convolution_sq_eq_l2 (g := f) hf hk1
    rw [hmain]
    refine lintegral_congr fun ξ => ?_
    rw [fourier_dilate_schwartz K ht ξ]
  have hstepC : ∀ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ x : ℝ, (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ))
      = ENNReal.ofReal t⁻¹ * (∫⁻ ξ : ℝ, (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)) := by
    intro t
    by_cases ht : 0 < t
    · rw [hperT t ht]
    · have hz : ENNReal.ofReal t⁻¹ = 0 := by
        refine ENNReal.ofReal_eq_zero.mpr ?_
        rcases lt_or_eq_of_le (le_of_not_gt ht) with h | h
        · exact le_of_lt (inv_neg''.mpr h)
        · rw [h]; simp
      rw [hz, zero_mul, zero_mul]
  have hstepD : ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ x : ℝ, (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ))
      = ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ ξ : ℝ, (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)) := by
    refine lintegral_congr fun t => ?_
    rw [hstepC t]
  have hstepE : ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ ξ : ℝ, (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ))
      = ∫⁻ t : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ) := by
    refine lintegral_congr fun t => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hstepF : ∫⁻ t : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)
      = ∫⁻ ξ : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ) := by
    refine lintegral_lintegral_swap (f := fun t ξ : ℝ => ENNReal.ofReal t⁻¹
      * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)) ?_
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1⁻¹) (volume.prod volume) :=
      (Measurable.ennreal_ofReal (measurable_inv.comp measurable_fst)).aemeasurable
    have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖(FF : ℝ → ℂ) p.2‖) (volume.prod volume) :=
      ((MeasureTheory.Lp.aestronglyMeasurable FF).aemeasurable.comp_snd).norm
    have h3 : AEMeasurable (fun p : ℝ × ℝ =>
        ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (p.1 * p.2)‖) (volume.prod volume) :=
      (((FourierTransform.fourier K : SchwartzMap ℝ ℂ).continuous.measurable.comp
        (measurable_fst.mul measurable_snd)).norm).aemeasurable
    have h4 : AEMeasurable (fun p : ℝ × ℝ => (ENNReal.ofReal (‖(FF : ℝ → ℂ) p.2‖
        * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (p.1 * p.2)‖)) ^ (2:ℝ))
        (volume.prod volume) := ((h2.mul h3).ennreal_ofReal).pow_const _
    exact h1.mul h4
  -- factor the inner `t`-integral
  have hinner : ∀ ξ : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
          * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)
      = ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * (∫⁻ t : ℝ, ENNReal.ofReal t⁻¹
          * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2)) := by
    intro ξ
    have hcongr : (fun t : ℝ => ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
            * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ))
        = fun t : ℝ => ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * (ENNReal.ofReal t⁻¹
            * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2)) := by
      funext t
      rw [show (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
              * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)
            = ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2)
              * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2) from by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
            mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]]
      rw [show ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2)
              * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2))
            = ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * (ENNReal.ofReal t⁻¹
              * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2)) from by
          ac_rfl]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hstepH : ∀ ξ : ℝ, (∫⁻ t : ℝ, ENNReal.ofReal t⁻¹
      * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2)) ≤ A := by
    intro ξ
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      have hz : ∀ t : ℝ, ENNReal.ofReal t⁻¹
          * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * 0)‖ ^ 2) = 0 := by
        intro t
        rw [mul_zero, hF0]
        simp
      rw [lintegral_congr hz]
      simp
    · rw [hA]
      exact lintegral_inv_mul_comp_mul_le
        (ψ := fun u : ℝ => ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) u‖ ^ 2))
        (by
          refine Measurable.ennreal_ofReal ?_
          exact ((FourierTransform.fourier K : SchwartzMap ℝ ℂ).continuous.norm).pow 2 |>.measurable) hξ
  have hplanch : ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2)
      = ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2) := by
    have hFFeq : FF = FourierTransform.fourier (hf.toLp f) := hFF
    have hcongr1 : ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2)
        = ∫⁻ ξ : ℝ, ‖(FF : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ) := by
      refine lintegral_congr fun ξ => ?_
      rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
        ENNReal.ofReal_pow (norm_nonneg _), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
        ENNReal.rpow_natCast]
    rw [hcongr1, hFFeq, ← Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral
        (FourierTransform.fourier (hf.toLp f)),
      Commons.Analysis.Fourier.BoundaryLayer.enorm_fourier,
      Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral (hf.toLp f)]
    refine lintegral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf] with x hx
    rw [hx, Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
      ENNReal.ofReal_pow (norm_nonneg _), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
      ENNReal.rpow_natCast]
  have hstepI : ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * A
      ≤ ENNReal.ofReal C₀ * ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2) := by
    calc ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * A
        ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * ENNReal.ofReal C₀ :=
          lintegral_mono fun ξ => mul_le_mul_of_nonneg_left hAle (by positivity)
      _ = (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2)) * ENNReal.ofReal C₀ :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2)) * ENNReal.ofReal C₀ := by rw [hplanch]
      _ = ENNReal.ofReal C₀ * ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2) := mul_comm _ _
  calc ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)
      = ∫⁻ x, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) := hIoi
    _ = ∫⁻ t : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ) := hswap
    _ = ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ x : ℝ, (ENNReal.ofReal ‖G t x‖) ^ (2:ℝ)) := hstepB
    _ = ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (∫⁻ ξ : ℝ, (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
        * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ)) := hstepD
    _ = ∫⁻ t : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
        * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ) := hstepE
    _ = ∫⁻ ξ : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖
        * ‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖)) ^ (2:ℝ) := hstepF
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * (∫⁻ t : ℝ, ENNReal.ofReal t⁻¹
        * ENNReal.ofReal (‖(FourierTransform.fourier K : SchwartzMap ℝ ℂ) (t * ξ)‖ ^ 2)) := by
        refine lintegral_congr fun ξ => hinner ξ
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(FF : ℝ → ℂ) ξ‖ ^ 2) * A := by
        refine lintegral_mono fun ξ => mul_le_mul_of_nonneg_left (hstepH ξ) (by positivity)
    _ ≤ ENNReal.ofReal C₀ * ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2) := hstepI



/-- The real (Bochner) integral is dominated by the `ℝ≥0∞` integral, with no measurability
hypothesis on `f` (if `f` is not measurable the Bochner integral is `0`). -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases h : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae hf h]
    exact ENNReal.ofReal_toReal_le
  · have hni : ¬ Integrable f μ := fun hi => h hi.aestronglyMeasurable
    rw [integral_undef hni]
    simp

lemma iUnion_dyadic_Ioc : (⋃ l : ℤ, Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))) = Set.Ioi (0:ℝ) := by
  ext t
  constructor
  · intro ht
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp ht
    exact lt_of_lt_of_le (zpow_pos (by norm_num) l) (le_of_lt hl.1)
  · intro ht
    rcases eq_or_lt_of_le (zpow_two_lev_le t ht) with h | h
    · have hlt : (2:ℝ)^(lev t - 1) < t := by
        have h1 : (2:ℝ)^(lev t - 1) < (2:ℝ)^(lev t) :=
          zpow_lt_zpow_right₀ (by norm_num : (1:ℝ) < 2) (by omega)
        rwa [h] at h1
      refine Set.mem_iUnion.mpr ⟨lev t - 1, hlt, ?_⟩
      rw [show (lev t - 1) + 1 = lev t by ring]
      exact le_of_eq h.symm
    · exact Set.mem_iUnion.mpr ⟨lev t, h, le_of_lt (lt_zpow_two_lev_succ t ht)⟩

lemma pairwiseDisjoint_dyadic_Ioc :
    Pairwise (Function.onFun Disjoint (fun l : ℤ => Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)))) := by
  intro l l' hll'
  rw [Function.onFun, Set.disjoint_left]
  intro t ht ht'
  simp only [Set.mem_Ioc] at ht ht'
  rcases lt_or_gt_of_ne hll' with h | h
  · have h2 : ((2:ℝ)^(l+1)) ≤ ((2:ℝ)^l') :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    linarith [ht.2, ht'.1, h2]
  · have h2 : ((2:ℝ)^(l'+1)) ≤ ((2:ℝ)^l) :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    linarith [ht'.2, ht.1, h2]

/-- The auxiliary `g`-function approach to the "within level" variation term. -/
theorem within_level_variation_l2 (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ),
      MemLp g 2 (volume : Measure ℝ) →
      MemLp g ⊤ (volume : Measure ℝ) →
      ∫⁻ x, (∑' l : ℤ, (ENNReal.ofReal
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖∫ y, g y * (t⁻¹ * Theta Ψ ((x-y)/t))‖ / t)) ^ (2:ℝ))
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := g_function_dilation_schwartz (ThetaS Ψ) (integral_ThetaS Ψ)
  have key (g : ℝ → ℂ) (hg2 : MemLp g 2 (volume : Measure ℝ))
      (hgt : MemLp g ⊤ (volume : Measure ℝ)) :
      ∫⁻ x, (∑' l : ℤ, (ENNReal.ofReal
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖∫ y, g y * (t⁻¹ * Theta Ψ ((x-y)/t))‖ / t)) ^ (2:ℝ))
        ≤ ENNReal.ofReal (C₀ + 1) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
    set G : ℝ → ℝ → ℂ := fun t x => ∫ y : ℝ, g y * (t⁻¹ * Theta Ψ ((x - y)/t)) with hG
    have hContTheta : Continuous (Theta Ψ) := by
      rw [Theta_eq_ThetaS]; exact (ThetaS Ψ).continuous
    have hGmeas : ∀ x : ℝ, AEMeasurable (fun t : ℝ => G t x) (volume : Measure ℝ) := by
      intro x
      have hker : AEStronglyMeasurable
          (fun q : ℝ × ℝ => g q.2 * (q.1⁻¹ * Theta Ψ ((x - q.2)/q.1))) (volume.prod volume) := by
        have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ => g q.2) (volume.prod volume) :=
          hg2.aestronglyMeasurable.comp_snd
        have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1⁻¹ * Theta Ψ ((x - q.2)/q.1))
            (volume.prod volume) := by
          refine Measurable.aestronglyMeasurable ?_
          have hsub : Measurable (fun q : ℝ × ℝ => (x - q.2) / q.1) :=
            (measurable_const.sub measurable_snd).div measurable_fst
          have hval : Measurable (fun q : ℝ × ℝ => Theta Ψ ((x - q.2) / q.1)) :=
            hContTheta.measurable.comp hsub
          have hsc : Measurable (fun q : ℝ × ℝ => ((q.1⁻¹ : ℝ) : ℂ)) :=
            Measurable.complex_ofReal measurable_fst.inv
          exact Measurable.mul hsc hval
        exact h1.mul h2
      have hres := hker.integral_prod_right' (ν := (volume : Measure ℝ))
      simpa [hG] using hres.aemeasurable
    have hGjoint : AEMeasurable (fun p : ℝ × ℝ => G p.2 p.1) (volume.prod volume) := by
      have h0 := aemeasurable_dilate_convolution (K := (ThetaS Ψ : ℝ → ℂ)) (ThetaS Ψ).continuous hg2
      refine h0.congr ?_
      filter_upwards with p
      simp only [hG]
      congr 1
      ext y
      rw [Theta_eq_ThetaS]
    have hGjoint' : AEMeasurable (fun p : ℝ × ℝ => G p.1 p.2) (volume.prod volume) := by
      have h1 : AEMeasurable (fun p : ℝ × ℝ => G p.2 p.1)
          ((volume.prod volume).map Prod.swap) := by
        rw [Measure.prod_swap]; exact hGjoint
      exact h1.comp_measurable measurable_swap
    have hΦmeas : AEMeasurable (Function.uncurry
        (fun t x : ℝ => ENNReal.ofReal (‖G t x‖ ^ 2 / t))) (volume.prod volume) := by
      have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖G p.1 p.2‖) (volume.prod volume) := hGjoint'.norm
      have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖G p.1 p.2‖ ^ 2 / p.1) (volume.prod volume) :=
        (h1.pow_const 2).div measurable_fst.aemeasurable
      change AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (‖G p.1 p.2‖ ^ 2 / p.1))
        (volume.prod volume)
      exact h2.ennreal_ofReal
    have hΦmeas' : AEMeasurable (Function.uncurry
        (fun x t : ℝ => ENNReal.ofReal (‖G t x‖ ^ 2 / t))) (volume.prod volume) := by
      have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖G p.2 p.1‖) (volume.prod volume) := hGjoint.norm
      have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖G p.2 p.1‖ ^ 2 / p.2) (volume.prod volume) :=
        (h1.pow_const 2).div measurable_snd.aemeasurable
      change AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (‖G p.2 p.1‖ ^ 2 / p.2))
        (volume.prod volume)
      exact h2.ennreal_ofReal
    have hpoint : ∀ l : ℤ, ∀ x : ℝ,
        (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖G t x‖ / t)) ^ (2:ℝ)
          ≤ ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)), ENNReal.ofReal (‖G t x‖ ^ 2 / t) := by
      intro l x
      set a : ℝ := (2:ℝ)^l with ha
      set b : ℝ := (2:ℝ)^(l+1) with hb
      have ha_pos : 0 < a := by rw [ha]; exact zpow_pos (by norm_num) l
      have hb_eq : b = a * 2 := by rw [ha, hb, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]
      have hab : a ≤ b := by rw [hb_eq]; nlinarith [ha_pos]
      have hbd : b - a = a := by rw [hb_eq]; ring
      have hFmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal (‖G t x‖ / t))
          (volume.restrict (Set.Ioc a b)) := by
        have h1 : AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖G t x‖)
            (volume.restrict (Set.Ioc a b)) := ((hGmeas x).restrict.norm).ennreal_ofReal
        have h2 : AEMeasurable (fun t : ℝ => ENNReal.ofReal t⁻¹)
            (volume.restrict (Set.Ioc a b)) :=
          (Measurable.ennreal_ofReal measurable_inv).aemeasurable
        refine (h1.mul h2).congr ?_
        filter_upwards with t
        simp only [Pi.mul_apply]
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (norm_nonneg _)]
      have hA : ENNReal.ofReal (∫ t in a..b, ‖G t x‖ / t)
          ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ / t) := by
        rw [intervalIntegral.integral_of_le hab]
        refine ofReal_integral_le_lintegral ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (norm_nonneg _) (le_of_lt (lt_trans ha_pos ht.1))
      have hpq : (2:ℝ).HolderConjugate (2:ℝ) :=
        Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
      have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b)) hpq
          hFmeas (aemeasurable_const (b := (1:ℝ≥0∞)))
      have hone : ((1:ℝ≥0∞)) ^ (2:ℝ) = 1 := by rw [ENNReal.rpow_two, one_pow]
      have hhold' : ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ / t)
          ≤ (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
            * (∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞)) ^ ((1:ℝ)/2) := by
        have h := hhold
        simp only [Pi.mul_apply, Pi.one_apply, mul_one, hone] at h
        exact h
      have hsq : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ / t)) ^ 2
          ≤ (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ))
            * (∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞)) := by
        calc (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ / t)) ^ 2
            ≤ ((∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
                * (∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞)) ^ ((1:ℝ)/2)) ^ 2 := pow_le_pow_left' hhold' 2
          _ = (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ))
                * (∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞)) := by
              rw [mul_pow]
              congr 1
              · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
                  show ((1:ℝ)/2) * ((2:ℕ):ℝ) = 1 by norm_num, ENNReal.rpow_one]
              · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
                  show ((1:ℝ)/2) * ((2:ℕ):ℝ) = 1 by norm_num, ENNReal.rpow_one]
      have hvol : ∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞) = ENNReal.ofReal a := by
        rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc, hbd]
      have hfin : (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ)) * ENNReal.ofReal a
          ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := by
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := lt_of_lt_of_le ha_pos (le_of_lt ht.1)
        have hge : a ≤ t := le_of_lt ht.1
        have h1 : (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ)
            = ENNReal.ofReal (‖G t x‖ ^ 2 / t ^ 2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow (div_nonneg (norm_nonneg _) (le_of_lt ht0))]
          congr 1
          rw [div_pow]
        rw [h1, mul_comm, ← ENNReal.ofReal_mul (le_of_lt ha_pos)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hle2 : t * (t ^ 2)⁻¹ = t⁻¹ := by
          field_simp
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc a * (‖G t x‖ ^ 2 * (t ^ 2)⁻¹) = ‖G t x‖ ^ 2 * (a * (t ^ 2)⁻¹) := by ring
          _ ≤ ‖G t x‖ ^ 2 * t⁻¹ := by
              rw [← hle2]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hge (by positivity)) (sq_nonneg _)
      calc (ENNReal.ofReal (∫ t in a..b, ‖G t x‖ / t)) ^ (2:ℝ)
          = (ENNReal.ofReal (∫ t in a..b, ‖G t x‖ / t)) ^ 2 := by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
        _ ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ / t)) ^ 2 := pow_le_pow_left' hA 2
        _ ≤ (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ))
              * (∫⁻ t in Set.Ioc a b, (1:ℝ≥0∞)) := hsq
        _ = (∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖G t x‖ / t)) ^ (2:ℝ))
              * ENNReal.ofReal a := by rw [hvol]
        _ ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hfin
    have hlevmeas : ∀ l : ℤ, AEMeasurable (fun x : ℝ =>
        ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)), ENNReal.ofReal (‖G t x‖ ^ 2 / t))
        (volume : Measure ℝ) := by
      intro l
      have hind : Function.uncurry (fun x t : ℝ =>
          (Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))).indicator
            (fun s : ℝ => ENNReal.ofReal (‖G s x‖ ^ 2 / s)) t)
          = (Set.univ ×ˢ Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))).indicator
              (fun p : ℝ × ℝ => ENNReal.ofReal (‖G p.2 p.1‖ ^ 2 / p.2)) := by
        funext p
        simp only [Function.uncurry, Set.indicator, Set.mem_prod, Set.mem_univ, true_and]
      have h := AEMeasurable.lintegral_prod_right
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun x t : ℝ => (Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))).indicator
            (fun s : ℝ => ENNReal.ofReal (‖G s x‖ ^ 2 / s)) t)
        (by rw [hind]
            exact hΦmeas'.indicator (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc))
      simpa only [lintegral_indicator measurableSet_Ioc] using h
    have htonelli : ∀ l : ℤ,
        ∫⁻ x : ℝ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)), ENNReal.ofReal (‖G t x‖ ^ 2 / t)
          = ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
              ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := by
      intro l
      have hAEM : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (‖G p.2 p.1‖ ^ 2 / p.2))
          (volume.prod (volume.restrict (Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))))) := by
        have h := hΦmeas'.restrict (s := Set.univ ×ˢ Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)))
        rw [← Measure.prod_restrict, Measure.restrict_univ] at h
        exact h
      exact lintegral_lintegral_swap (μ := (volume : Measure ℝ))
        (ν := volume.restrict (Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1))))
        (f := fun x t : ℝ => ENNReal.ofReal (‖G t x‖ ^ 2 / t)) hAEM
    have hstep1 : ∫⁻ x, (∑' l : ℤ, (ENNReal.ofReal
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖G t x‖ / t)) ^ (2:ℝ))
        ≤ ∫⁻ x, ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ENNReal.ofReal (‖G t x‖ ^ 2 / t) :=
      lintegral_mono fun x => ENNReal.tsum_le_tsum fun l => hpoint l x
    have hstep2 : ∫⁻ x, ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
          ENNReal.ofReal (‖G t x‖ ^ 2 / t)
        = ∑' l : ℤ, ∫⁻ x, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ENNReal.ofReal (‖G t x‖ ^ 2 / t) :=
      lintegral_tsum fun l => hlevmeas l
    have hstep3 : ∑' l : ℤ, ∫⁻ x, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
          ENNReal.ofReal (‖G t x‖ ^ 2 / t)
        = ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t) :=
      tsum_congr fun l => htonelli l
    have hstep4 : ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
          ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t)
        = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := by
      rw [← lintegral_iUnion (fun l : ℤ => measurableSet_Ioc) pairwiseDisjoint_dyadic_Ioc,
        iUnion_dyadic_Ioc]
    have hstep5 : ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t)
        = ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (‖G t x‖ ^ 2 / t) := by
      have hAEM : AEMeasurable (Function.uncurry (fun t x : ℝ => ENNReal.ofReal (‖G t x‖ ^ 2 / t)))
          ((volume.restrict (Set.Ioi (0:ℝ))).prod volume) := by
        have h := hΦmeas.restrict (s := Set.Ioi (0:ℝ) ×ˢ Set.univ)
        rw [← Measure.prod_restrict, Measure.restrict_univ] at h
        exact h
      exact lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0:ℝ)))
        (ν := (volume : Measure ℝ)) (f := fun t x : ℝ => ENNReal.ofReal (‖G t x‖ ^ 2 / t)) hAEM
    have hstep6 : ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (‖G t x‖ ^ 2 / t)
        ≤ ENNReal.ofReal (C₀ + 1) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
      have hGeq : ∀ t x : ℝ, (∫ y : ℝ, g y * (t⁻¹ * Theta Ψ ((x - y)/t)))
          = ∫ y : ℝ, g y * (t⁻¹ • (ThetaS Ψ : ℝ → ℂ) ((x - y)/t)) := by
        intro t x
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        rw [Theta_eq_ThetaS]
        simp only
        rw [← Complex.real_smul]
      have hrew : ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (‖G t x‖ ^ 2 / t)
          = ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal t⁻¹
              * (ENNReal.ofReal ‖∫ y : ℝ, g y * (t⁻¹ • (ThetaS Ψ : ℝ → ℂ) ((x - y)/t))‖) ^ (2:ℝ) := by
        refine lintegral_congr fun x => lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [show ‖G t x‖ = ‖∫ y : ℝ, g y * (t⁻¹ • (ThetaS Ψ : ℝ → ℂ) ((x - y)/t))‖ from by
          rw [hG]; exact congrArg norm (hGeq t x)]
        rw [show ENNReal.ofReal (‖∫ y : ℝ, g y * (t⁻¹ • (ThetaS Ψ : ℝ → ℂ) ((x - y)/t))‖ ^ 2 / t)
              = ENNReal.ofReal t⁻¹
                * (ENNReal.ofReal ‖∫ y : ℝ, g y * (t⁻¹ • (ThetaS Ψ : ℝ → ℂ) ((x - y)/t))‖) ^ (2:ℝ) from by
            rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
              show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, mul_comm]]
      rw [hrew]
      refine (hC₀ g hg2).trans ?_
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) (by positivity)
    calc ∫⁻ x, (∑' l : ℤ, (ENNReal.ofReal
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖G t x‖ / t)) ^ (2:ℝ))
        ≤ ∫⁻ x, ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hstep1
      _ = ∑' l : ℤ, ∫⁻ x, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hstep2
      _ = ∑' l : ℤ, ∫⁻ t in Set.Ioc ((2:ℝ)^l) ((2:ℝ)^(l+1)),
            ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hstep3
      _ = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ x : ℝ, ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hstep4
      _ = ∫⁻ x, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (‖G t x‖ ^ 2 / t) := hstep5
      _ ≤ ENNReal.ofReal (C₀ + 1) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := hstep6
  exact ⟨C₀ + 1, by linarith, key⟩




lemma norm_ofReal' (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

lemma norm_Lam_le (z : ℝ) : ‖Lam z‖ ≤ 4 * ((1 + |z|)⁻¹) ^ 2 := by
  have hnorm : ‖Lam z‖ = max 0 (1 - |z|) := by
    rw [show Lam z = ((max 0 (1 - |z|) : ℝ) : ℂ) from rfl, norm_ofReal',
      abs_of_nonneg (le_max_left _ _)]
  rw [hnorm]
  by_cases hz : |z| ≤ 1
  · have h1 : max 0 (1 - |z|) ≤ 1 := max_le zero_le_one (by have := abs_nonneg z; linarith)
    have h2 : (1:ℝ) ≤ 4 * ((1 + |z|)⁻¹) ^ 2 := by
      rw [inv_pow, le_mul_inv_iff₀ (by positivity : (0:ℝ) < (1+|z|)^2)]
      nlinarith [abs_nonneg z]
    exact h1.trans h2
  · rw [max_eq_left (by have := not_le.mp hz; linarith : 1 - |z| ≤ 0)]
    positivity

lemma rem_decay (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, ‖Rem Ψ z‖ ≤ C * ((1 + |z|)⁻¹) ^ 2 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := schwartz_decay_two Ψ
  set cc : ℂ := ∫ z : ℝ, (Ψ : ℝ → ℂ) z with hcc
  refine ⟨C₁ + 4 * ‖cc‖ + 1, by positivity, fun z => ?_⟩
  have h1 : ‖(Ψ : ℝ → ℂ) z‖ ≤ C₁ / (1 + |z|) ^ 2 := hC₁ z
  have h2 : ‖cc * Lam z‖ ≤ ‖cc‖ * (4 * ((1 + |z|)⁻¹) ^ 2) :=
    le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left (norm_Lam_le z) (norm_nonneg _))
  have h3 : Rem Ψ z = (Ψ : ℝ → ℂ) z - cc * Lam z := by rw [Rem, ← hcc]
  rw [h3]
  have h4 : C₁ / (1+|z|)^2 = C₁ * ((1+|z|)⁻¹)^2 := by rw [inv_pow, div_eq_mul_inv]
  have h5 : ‖cc‖ * (4 * ((1 + |z|)⁻¹) ^ 2) = 4 * ‖cc‖ * ((1 + |z|)⁻¹) ^ 2 := by ring
  calc ‖(Ψ : ℝ → ℂ) z - cc * Lam z‖
      ≤ ‖(Ψ : ℝ → ℂ) z‖ + ‖cc * Lam z‖ := norm_sub_le _ _
    _ ≤ C₁ * ((1 + |z|)⁻¹) ^ 2 + 4 * ‖cc‖ * ((1 + |z|)⁻¹) ^ 2 := by
        rw [h4] at h1; rw [h5] at h2; linarith
    _ ≤ (C₁ + 4 * ‖cc‖ + 1) * ((1 + |z|)⁻¹) ^ 2 := by
        have hnn : 0 ≤ ((1 + |z|)⁻¹) ^ 2 := by positivity
        nlinarith [hnn]

lemma continuous_rem (Ψ : SchwartzMap ℝ ℂ) : Continuous (Rem Ψ) := by
  have h1 : Continuous fun z : ℝ => (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * Lam z :=
    continuous_const.mul (by unfold Lam; fun_prop)
  have h2 : Rem Ψ = fun z : ℝ => (Ψ : ℝ → ℂ) z - (∫ z : ℝ, (Ψ : ℝ → ℂ) z) * Lam z := rfl
  rw [h2]
  exact Ψ.continuous.sub h1

/-- Pointwise domination of the dilated kernel. -/
lemma kernel_pointwise_bound {K : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ z : ℝ, ‖K z‖ ≤ C * ((1 + |z|)⁻¹) ^ 2) (t x y : ℝ) :
    ‖t • K ((x - y) * t)‖ ≤ C * (1 + |t|) * ((1 + |x - y|)⁻¹) := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := hK ((x - y) * t)
  rw [abs_mul] at h
  have hgoal : |t| * ((1 + |x - y| * |t|)⁻¹) ^ 2 ≤ (1 + |t|) * (1 + |x - y|)⁻¹ := by
    rw [inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg (x - y), abs_nonneg t, sq_nonneg (|x - y| * |t|),
      mul_nonneg (abs_nonneg (x - y)) (abs_nonneg t)]
  calc |t| * ‖K ((x - y) * t)‖
      ≤ |t| * (C * ((1 + |x - y| * |t|)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg t)
    _ = C * (|t| * ((1 + |x - y| * |t|)⁻¹) ^ 2) := by ring
    _ ≤ C * ((1 + |t|) * (1 + |x - y|)⁻¹) := mul_le_mul_of_nonneg_left hgoal hC
    _ = C * (1 + |t|) * (1 + |x - y|)⁻¹ := by ring

lemma memLp_translate_inv (x : ℝ) : MemLp (fun y : ℝ => (1 + |x - y|)⁻¹) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop :
    AEStronglyMeasurable (fun y : ℝ => (1 + |x - y|)⁻¹) volume)]
  have hint : Integrable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) volume := by
    have h := (integrable_inv_one_add_sq).comp_sub_right x
    have heq : (fun t : ℝ => (1 + (t - x) ^ 2)⁻¹) = fun y : ℝ => (1 + (x - y) ^ 2)⁻¹ := by
      funext t; ring_nf
    rwa [heq] at h
  refine Integrable.mono' hint (by fun_prop) ?_
  filter_upwards with y
  have hnn : (0:ℝ) ≤ (1 + |x - y|)⁻¹ := by positivity
  rw [Real.norm_of_nonneg hnn, inv_pow]
  have hle : (1 : ℝ) + (x - y) ^ 2 ≤ (1 + |x - y|) ^ 2 := by
    have h2 : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (x - y), h2]
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ((1 + |x - y|) ^ 2)⁻¹)]
  exact inv_anti₀ (by positivity) hle

lemma integrable_conv_kernel {K : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ z : ℝ, ‖K z‖ ≤ C * ((1 + |z|)⁻¹) ^ 2) (hKc : Continuous K)
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) (t x : ℝ) :
    Integrable (fun y : ℝ => g y * (t • K ((x - y) * t))) := by
  have hdom : Integrable (fun y : ℝ => ‖g y‖ * (C * (1 + |t|) * (1 + |x - y|)⁻¹)) volume :=
    MemLp.integrable_mul hg.norm ((memLp_translate_inv x).const_mul (C * (1 + |t|)))
  refine hdom.mono' ?_ ?_
  · have hm : Measurable (fun y : ℝ => t • K ((x - y) * t)) := by
      have hcont : Continuous (fun y : ℝ => t • K ((x - y) * t)) := by
        fun_prop
      exact hcont.measurable
    exact hg.aestronglyMeasurable.mul hm.aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (kernel_pointwise_bound hC hK t x y) (norm_nonneg _)

lemma dyadicVar_le_tsum (A : ℝ → ℂ) {s : ℝ} (hs : 2 ≤ s) :
    dyadicVar A s ≤ 2 * (∑' l : ℤ, ‖A ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  rw [dyadicVar]
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
  exact chain_variation_le_tsum (fun l : ℤ => A ((2:ℝ)^l)) hs J k hk

/-- The sup over (arbitrary) chains of the dyadic samples equals the `dyadicVar`. -/
lemma dyadicVar_eq_sup (A : ℝ → ℂ) (s : ℝ) :
    dyadicVar A s = ⨆ (J : ℕ) (k : Fin (J+1) → ℤ), ⨆ (_ : StrictMono k),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖A ((2:ℝ)^(k (Fin.castSucc j))) - A ((2:ℝ)^(k (Fin.succ j)))‖ ^ s) ^ (1/s)) := rfl

lemma aemeasurable_conv_kernel {Ψ : SchwartzMap ℝ ℂ} {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (u : ℝ) :
    AEMeasurable (fun x : ℝ => ∫ y : ℝ, g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/u))) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.2 * (u⁻¹ • (Ψ : ℝ → ℂ) ((p.1 - p.2)/u))) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (volume.prod volume) :=
      hg.aestronglyMeasurable.comp_snd
    have h2 : Measurable (fun p : ℝ × ℝ => u⁻¹ • (Ψ : ℝ → ℂ) ((p.1 - p.2)/u)) := by
      have hcont : Continuous (fun p : ℝ × ℝ => u⁻¹ • (Ψ : ℝ → ℂ) ((p.1 - p.2)/u)) := by
        fun_prop
      exact hcont.measurable
    exact h1.mul h2.aestronglyMeasurable
  exact hjoint.integral_prod_right'.aemeasurable

lemma aemeasurable_finset_sum' {ι α M : Type*} [MeasurableSpace α] {μ : Measure α}
    [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]
    {s : Finset ι} {f : ι → α → M} (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (fun x : α => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => 0 := by
        funext x; simp
      rw [hone]
      exact aemeasurable_const
  | insert a s ha ih =>
      have ha' : AEMeasurable (f a) μ := h a (Finset.mem_insert_self a s)
      have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hgoal : (fun x : α => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
        funext x; rw [Finset.sum_insert ha]
      rw [hgoal]
      exact ha'.add ih'

lemma aemeasurable_dyadicVar (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ} (hg : MemLp g 2 volume) (s : ℝ) :
    AEMeasurable (fun x : ℝ =>
      dyadicVar (fun u : ℝ => ∫ y : ℝ, g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/u))) s) volume := by
  have hwin := aemeasurable_conv_kernel (Ψ := Ψ) (g := g) hg
  simp only [dyadicVar_eq_sup]
  refine AEMeasurable.iSup (fun J : ℕ => ?_)
  refine AEMeasurable.iSup (fun k : Fin (J+1) → ℤ => ?_)
  refine AEMeasurable.iSup (fun hk : StrictMono k => ?_)
  refine AEMeasurable.ennreal_ofReal ?_
  exact (aemeasurable_finset_sum' (M := ℝ) (s := Finset.univ)
    (f := fun j : Fin J => fun x : ℝ =>
      ‖(∫ y : ℝ, g y * (((2:ℝ)^(k (Fin.castSucc j)))⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/((2:ℝ)^(k (Fin.castSucc j))))))
        - (∫ y : ℝ, g y * (((2:ℝ)^(k (Fin.succ j)))⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/((2:ℝ)^(k (Fin.succ j))))))‖ ^ s)
    (fun j _ => (((hwin ((2:ℝ)^(k (Fin.castSucc j)))).sub
      (hwin ((2:ℝ)^(k (Fin.succ j))))).norm).pow_const s)).pow_const ((1:ℝ)/s)

lemma sq_rpow_half (a : ℝ≥0∞) : (a ^ ((1:ℝ)/2)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((1:ℝ)/2) * ((2:ℕ):ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- The within-level square function of `hfun Ψ g ·` is the one appearing in
`within_level_variation_l2`. -/
lemma within_level_ident (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ) :
    (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
      = ∑' l : ℤ, (ENNReal.ofReal
          (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖∫ y : ℝ, g y * (t⁻¹ * Theta Ψ ((x-y)/t))‖ / t)) ^ (2:ℝ) := by
  refine tsum_congr fun l => ?_
  congr 1
  refine congrArg ENNReal.ofReal ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    (by omega : l ≤ l + 1))] at ht
  rw [hfun_eq Ψ g x (lt_of_lt_of_le (zpow_pos (by norm_num) l) ht.1)]
  congr 1

lemma smul_lam_eq' {u x y : ℝ} (hu : 0 < u) :
    u • Lam ((x - y) * u) = ((u : ℂ) * ((max 0 (1 - u * |x - y|) : ℝ) : ℂ)) := by
  rw [show Lam ((x - y) * u) = ((max 0 (1 - |(x - y) * u|) : ℝ) : ℂ) from rfl, Complex.real_smul]
  congr 1
  have hreal : max 0 (1 - |(x - y) * u|) = max 0 (1 - u * |x - y|) := by
    rw [abs_mul, abs_of_pos hu, mul_comm]
  rw [hreal]

lemma dyadicVar_betaLam (c : ℂ) (g : ℝ → ℂ) (x : ℝ) (s : ℝ) :
    dyadicVar (fun u : ℝ => ∫ y : ℝ, (c * g y) * (u • Lam ((x - y) * u))) s
      = ⨆ (J : ℕ) (k : Fin (J+1) → ℤ), ⨆ (_ : StrictMono k),
          ENNReal.ofReal ((∑ j : Fin J, ‖(∫ y : ℝ, (c * g y) * ((2:ℝ)^(k (Fin.castSucc j)) * max 0 (1 - (2:ℝ)^(k (Fin.castSucc j)) * |x - y|))) - (∫ y : ℝ, (c * g y) * ((2:ℝ)^(k (Fin.succ j)) * max 0 (1 - (2:ℝ)^(k (Fin.succ j)) * |x - y|)))‖ ^ s) ^ (1/s)) := by
  simp only [dyadicVar_eq_sup]
  refine iSup_congr fun J => iSup_congr fun k => iSup_congr fun hk => ?_
  have h1 : ∀ j : Fin J,
      (∫ y : ℝ, (c * g y) * (((2:ℝ)^(k (Fin.castSucc j))) • Lam ((x - y) * (2:ℝ)^(k (Fin.castSucc j)))))
        = ∫ y : ℝ, (c * g y) * ((2:ℝ)^(k (Fin.castSucc j)) * max 0 (1 - (2:ℝ)^(k (Fin.castSucc j)) * |x - y|)) := by
    intro j
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    congr 1
    rw [show Lam ((x - y) * (2:ℝ)^(k (Fin.castSucc j)))
        = (((max 0 (1 - |(x - y) * (2:ℝ)^(k (Fin.castSucc j))|) : ℝ)) : ℂ) from rfl,
      Complex.real_smul]
    push_cast
    congr 1
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _), mul_comm]
  have h2 : ∀ j : Fin J,
      (∫ y : ℝ, (c * g y) * (((2:ℝ)^(k (Fin.succ j))) • Lam ((x - y) * (2:ℝ)^(k (Fin.succ j)))))
        = ∫ y : ℝ, (c * g y) * ((2:ℝ)^(k (Fin.succ j)) * max 0 (1 - (2:ℝ)^(k (Fin.succ j)) * |x - y|)) := by
    intro j
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    congr 1
    rw [show Lam ((x - y) * (2:ℝ)^(k (Fin.succ j)))
        = (((max 0 (1 - |(x - y) * (2:ℝ)^(k (Fin.succ j))|) : ℝ)) : ℂ) from rfl,
      Complex.real_smul]
    push_cast
    congr 1
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _), mul_comm]
  simp only [h1, h2]

lemma betaR_zpow (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (x : ℝ) (l : ℤ) :
    (fun u : ℝ => ∫ y : ℝ, g y * (u • Rem Ψ ((x - y) * u))) ((2:ℝ)^l)
      = ∫ y : ℝ, g y * ((2:ℝ)^l * Rem Ψ ((x - y) * (2:ℝ)^l)) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.real_smul]
  push_cast
  ring

lemma aemeasurable_conv_kernel' {K : ℝ → ℂ} (hKc : Continuous K) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (u : ℝ) :
    AEMeasurable (fun x : ℝ => ∫ y : ℝ, g y * (u • K ((x - y) * u))) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.2 * (u • K ((p.1 - p.2) * u))) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (volume.prod volume) :=
      hg.aestronglyMeasurable.comp_snd
    have h2 : Measurable (fun p : ℝ × ℝ => u • K ((p.1 - p.2) * u)) := by
      have hcont : Continuous (fun p : ℝ × ℝ => u • K ((p.1 - p.2) * u)) := by
        fun_prop
      exact hcont.measurable
    exact h1.mul h2.aestronglyMeasurable
  exact hjoint.integral_prod_right'.aemeasurable

lemma aemeasurable_dyadicVar' {K : ℝ → ℂ} (hKc : Continuous K) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (s : ℝ) :
    AEMeasurable (fun x : ℝ =>
      dyadicVar (fun u : ℝ => ∫ y : ℝ, g y * (u • K ((x - y) * u))) s) volume := by
  have hwin := aemeasurable_conv_kernel' (K := K) hKc (g := g) hg
  simp only [dyadicVar_eq_sup]
  refine AEMeasurable.iSup (fun J : ℕ => ?_)
  refine AEMeasurable.iSup (fun k : Fin (J+1) → ℤ => ?_)
  refine AEMeasurable.iSup (fun hk : StrictMono k => ?_)
  refine AEMeasurable.ennreal_ofReal ?_
  exact (aemeasurable_finset_sum' (M := ℝ) (s := Finset.univ)
    (f := fun j : Fin J => fun x : ℝ =>
      ‖(∫ y : ℝ, g y * (((2:ℝ)^(k (Fin.castSucc j))) • K ((x - y) * (2:ℝ)^(k (Fin.castSucc j)))))
        - (∫ y : ℝ, g y * (((2:ℝ)^(k (Fin.succ j))) • K ((x - y) * (2:ℝ)^(k (Fin.succ j)))))‖ ^ s)
    (fun j _ => (((hwin ((2:ℝ)^(k (Fin.castSucc j)))).sub
      (hwin ((2:ℝ)^(k (Fin.succ j))))).norm).pow_const s)).pow_const ((1:ℝ)/s)

/-- Pointwise splitting of the dilated window `Ψ` into its mean part and `Rem Ψ`. -/
lemma conv_split (Ψ : SchwartzMap ℝ ℂ) (c : ℂ) (hc : c = ∫ z : ℝ, (Ψ : ℝ → ℂ) z)
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) (t x : ℝ) :
    (∫ y : ℝ, g y * (t • (Ψ : ℝ → ℂ) ((x - y) * t)))
      = c * (∫ y : ℝ, g y * (t • Lam ((x - y) * t)))
        + (∫ y : ℝ, g y * (t • Rem Ψ ((x - y) * t))) := by
  obtain ⟨AΨ, hAΨpos, hAΨ⟩ := schwartz_decay_two Ψ
  obtain ⟨AR, hARpos, hAR⟩ := rem_decay Ψ
  have hΨdec : ∀ z : ℝ, ‖(Ψ : ℝ → ℂ) z‖ ≤ AΨ * ((1 + |z|)⁻¹) ^ 2 := by
    intro z
    have h := hAΨ z
    rw [div_eq_mul_inv, ← inv_pow] at h
    exact h
  have hintΛ : Integrable (fun y : ℝ => g y * (t • Lam ((x - y) * t))) :=
    integrable_conv_kernel (by norm_num : (0:ℝ) ≤ 4) norm_Lam_le (by unfold Lam; fun_prop) hg t x
  have hintR : Integrable (fun y : ℝ => g y * (t • Rem Ψ ((x - y) * t))) :=
    integrable_conv_kernel hARpos.le hAR (continuous_rem Ψ) hg t x
  have hpt : ∀ y : ℝ, g y * (t • (Ψ : ℝ → ℂ) ((x - y) * t))
      = c * (g y * (t • Lam ((x - y) * t))) + g y * (t • Rem Ψ ((x - y) * t)) := by
    intro y
    have h1 : (Ψ : ℝ → ℂ) ((x - y) * t) = c * Lam ((x - y) * t) + Rem Ψ ((x - y) * t) := by
      rw [Rem, ← hc]; ring
    rw [h1, smul_add]
    simp only [Complex.real_smul]
    ring
  calc (∫ y : ℝ, g y * (t • (Ψ : ℝ → ℂ) ((x - y) * t)))
      = ∫ y : ℝ, (c * (g y * (t • Lam ((x - y) * t)))
          + g y * (t • Rem Ψ ((x - y) * t))) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ y : ℝ, c * (g y * (t • Lam ((x - y) * t))))
          + (∫ y : ℝ, g y * (t • Rem Ψ ((x - y) * t))) :=
        integral_add (hintΛ.const_mul c) hintR
    _ = c * (∫ y : ℝ, g y * (t • Lam ((x - y) * t)))
          + (∫ y : ℝ, g y * (t • Rem Ψ ((x - y) * t))) := by
        rw [integral_const_mul]

lemma aemeasurable_conv_kernel_max {φ : ℝ → ℝ} (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (u : ℝ) :
    AEMeasurable (fun x : ℝ => ∫ y : ℝ, g y * (((u * φ ((x - y) * u) : ℝ)) : ℂ)) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.2 * (((u * φ ((p.1 - p.2) * u) : ℝ)) : ℂ)) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (volume.prod volume) :=
      hg.aestronglyMeasurable.comp_snd
    have h2 : Measurable (fun p : ℝ × ℝ => (((u * φ ((p.1 - p.2) * u) : ℝ)) : ℂ)) := by
      have hcont : Continuous (fun p : ℝ × ℝ => u * φ ((p.1 - p.2) * u)) := by fun_prop
      exact Measurable.complex_ofReal hcont.measurable
    exact h1.mul h2.aestronglyMeasurable
  exact hjoint.integral_prod_right'.aemeasurable

lemma aemeasurable_dyadicVar_max {φ : ℝ → ℝ} (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (s : ℝ) :
    AEMeasurable (fun x : ℝ =>
      dyadicVar (fun u : ℝ => ∫ y : ℝ, g y * (((u * φ ((x - y) * u) : ℝ)) : ℂ)) s) volume := by
  have hwin := aemeasurable_conv_kernel_max (φ := φ) hφc (g := g) hg
  simp only [dyadicVar_eq_sup]
  refine AEMeasurable.iSup (fun J : ℕ => ?_)
  refine AEMeasurable.iSup (fun k : Fin (J+1) → ℤ => ?_)
  refine AEMeasurable.iSup (fun hk : StrictMono k => ?_)
  refine AEMeasurable.ennreal_ofReal ?_
  exact (aemeasurable_finset_sum' (M := ℝ) (s := Finset.univ)
    (f := fun j : Fin J => fun x : ℝ =>
      ‖(∫ y : ℝ, g y * ((((2:ℝ)^(k (Fin.castSucc j)) * φ ((x - y) * (2:ℝ)^(k (Fin.castSucc j))) : ℝ)) : ℂ))
        - (∫ y : ℝ, g y * ((((2:ℝ)^(k (Fin.succ j)) * φ ((x - y) * (2:ℝ)^(k (Fin.succ j))) : ℝ)) : ℂ))‖ ^ s)
    (fun j _ => (((hwin ((2:ℝ)^(k (Fin.castSucc j)))).sub
      (hwin ((2:ℝ)^(k (Fin.succ j))))).norm).pow_const s)).pow_const ((1:ℝ)/s)

/-- The dyadic supremum of the Λ-part of `βΛ` is *literally* the handle's supremum
(the text is copied verbatim from `fejer_handle_dyadic_variation_l2`). -/
lemma dyadicVar_betaLam_max (c : ℂ) (g : ℝ → ℂ) (x : ℝ) (s : ℝ) :
    dyadicVar (fun u : ℝ => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|))) s
      = ⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J,
          ‖(∫ y : ℝ, (c * g y) * ((2:ℝ) ^ (k (Fin.castSucc j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.castSucc j)) * |x - y|)))
           - (∫ y : ℝ, (c * g y) * ((2:ℝ) ^ (k (Fin.succ j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.succ j)) * |x - y|)))‖ ^ s) ^ (1/s)) := by
  simp only [dyadicVar_eq_sup]
  refine iSup_congr fun J => iSup_congr fun k => iSup_congr fun hk => ?_
  refine congrArg ENNReal.ofReal ?_
  refine congrArg (fun t : ℝ => t ^ ((1:ℝ)/s)) ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine congrArg (fun t : ℝ => t ^ s) ?_
  simp only [Complex.ofReal_zpow]

/-- Measurability of the dilated triangular-kernel convolution `x ↦ ∫ y, (c*g y) * (u * (1-u|x-y|)_+)`. -/
lemma aemeasurable_conv_kernel_lam {g : ℝ → ℂ} (hg : MemLp g 2 volume) (c : ℂ) (u : ℝ) :
    AEMeasurable (fun x : ℝ => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|))) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (c * g p.2) * (u * max 0 (1 - u * |p.1 - p.2|)))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => c * g p.2) (volume.prod volume) :=
      (hg.aestronglyMeasurable.comp_snd).const_mul c
    have h2 : Measurable
        (fun p : ℝ × ℝ => (u : ℂ) * ((max 0 (1 - u * |p.1 - p.2|) : ℝ) : ℂ)) := by
      have hcont : Continuous
          (fun p : ℝ × ℝ => (u : ℂ) * ((max 0 (1 - u * |p.1 - p.2|) : ℝ) : ℂ)) := by
        fun_prop
      exact hcont.measurable
    exact h1.mul h2.aestronglyMeasurable
  exact hjoint.integral_prod_right'.aemeasurable

/-- Measurability of the dyadic variation of the triangular-kernel part. -/
lemma aemeasurable_dyadicVar_lam {g : ℝ → ℂ} (hg : MemLp g 2 volume) (c : ℂ) (s : ℝ) :
    AEMeasurable (fun x : ℝ =>
      dyadicVar (fun u : ℝ => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|))) s) volume := by
  have hwin := aemeasurable_conv_kernel_lam (g := g) hg c
  simp only [dyadicVar_eq_sup]
  refine AEMeasurable.iSup (fun J : ℕ => ?_)
  refine AEMeasurable.iSup (fun k : Fin (J+1) → ℤ => ?_)
  refine AEMeasurable.iSup (fun hk : StrictMono k => ?_)
  refine AEMeasurable.ennreal_ofReal ?_
  exact (aemeasurable_finset_sum' (M := ℝ) (s := Finset.univ)
    (f := fun j : Fin J => fun x : ℝ =>
      ‖(∫ y : ℝ, (c * g y) * (((((2:ℝ)^(k (Fin.castSucc j)) : ℝ)) : ℂ) *
            ((max 0 (1 - (2:ℝ)^(k (Fin.castSucc j)) * |x - y|) : ℝ) : ℂ)))
        - (∫ y : ℝ, (c * g y) * (((((2:ℝ)^(k (Fin.succ j)) : ℝ)) : ℂ) *
            ((max 0 (1 - (2:ℝ)^(k (Fin.succ j)) * |x - y|) : ℝ) : ℂ)))‖ ^ s)
    (fun j _ => (((hwin ((2:ℝ)^(k (Fin.castSucc j)))).sub
      (hwin ((2:ℝ)^(k (Fin.succ j))))).norm).pow_const s)).pow_const ((1:ℝ)/s)

theorem dilation_variation_scalar_l2 (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) (g : ℝ → ℂ),
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.MemLp g ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x : ℝ, (⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
          ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
            (ENNReal.ofReal ((∑ j : Fin J,
              ‖(∫ y : ℝ, g y * (((u (Fin.castSucc j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.castSucc j) : ℝ)))))
               - (∫ y : ℝ, g y * (((u (Fin.succ j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.succ j) : ℝ)))))‖ ^ s) ^ ((1:ℝ)/s)))) ^ (2 : ℝ)
        ≤ ENNReal.ofReal ((C / (s - 2)) ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := within_level_variation_l2 Ψ
  obtain ⟨Ch, hChpos, hCh⟩ := fejer_handle_dyadic_variation_l2
  obtain ⟨Cr, hCrpos, hCr⟩ := dyadic_square_function_rem Ψ
  set c : ℂ := ∫ z : ℝ, (Ψ : ℝ → ℂ) z with hc
  refine ⟨200 * (Cw + 4 * Ch ^ 2 * ‖c‖ ^ 2 + 16 * Cr + 1), by positivity, ?_⟩
  intro s hs hs3 g hg2 hgt
  obtain ⟨AΨ, hAΨpos, hAΨ⟩ := schwartz_decay_two Ψ
  obtain ⟨AR, hARpos, hAR⟩ := rem_decay Ψ
  have hΨdec : ∀ z : ℝ, ‖(Ψ : ℝ → ℂ) z‖ ≤ AΨ * ((1 + |z|)⁻¹) ^ 2 := by
    intro z
    have h := hAΨ z
    rw [div_eq_mul_inv] at h
    rwa [inv_pow]
  set α : ℝ → ℝ → ℂ := fun x u => ∫ y : ℝ, g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y)/u)) with hα
  set βΛ : ℝ → ℝ → ℂ := fun x u => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|)) with hβΛ
  set βR : ℝ → ℝ → ℂ := fun x u => ∫ y : ℝ, g y * (u • Rem Ψ ((x - y) * u)) with hβR
  have hβΛeq : ∀ x : ℝ,
      βΛ x = fun u : ℝ => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|)) := by
    intro x; rw [hβΛ]
  have hβReq : ∀ x : ℝ, βR x = fun u : ℝ => ∫ y : ℝ, g y * (u • Rem Ψ ((x - y) * u)) := by
    intro x; rw [hβR]
  have hαinv : ∀ x t : ℝ,
      α x t⁻¹ = ∫ y : ℝ, g y * (t • (Ψ : ℝ → ℂ) ((x - y) * t)) := by
    intro x t
    rw [hα]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    congr 1
    rw [inv_inv, div_inv_eq_mul]
  have hΛconst : ∀ x t : ℝ, (∫ y : ℝ, (c * g y) * (t • Lam ((x - y) * t)))
      = c * (∫ y : ℝ, g y * (t • Lam ((x - y) * t))) := by
    intro x t
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    ring
  have hsplit : ∀ x t : ℝ, 0 < t → (∫ y : ℝ, g y * (t • (Ψ : ℝ → ℂ) ((x - y) * t)))
      = βΛ x t + βR x t := by
    intro x t ht
    rw [hβΛeq x, hβReq x]
    simp only []
    rw [conv_split Ψ c hc hg2 t x]
    congr 1
    rw [← hΛconst x t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    congr 1
    rw [smul_lam_eq' (u := t) (x := x) (y := y) ht, ← Complex.ofReal_mul]
  have hDαle : ∀ x : ℝ, dyadicVar (fun t : ℝ => α x t⁻¹) s
      ≤ dyadicVar (βΛ x) s + dyadicVar (βR x) s := by
    intro x
    refine le_trans ?_ (dyadicVar_add_le (βΛ x) (βR x) (by linarith : (1:ℝ) ≤ s))
    simp only [dyadicVar_eq_sup]
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    refine le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk ?_))
    refine le_of_eq ?_
    refine congrArg ENNReal.ofReal ?_
    refine congrArg (fun t : ℝ => t ^ ((1:ℝ)/s)) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine congrArg (fun t : ℝ => t ^ s) ?_
    rw [hαinv x ((2:ℝ)^(k (Fin.castSucc j))),
      hsplit x ((2:ℝ)^(k (Fin.castSucc j))) (zpow_pos (by norm_num) _),
      hαinv x ((2:ℝ)^(k (Fin.succ j))),
      hsplit x ((2:ℝ)^(k (Fin.succ j))) (zpow_pos (by norm_num) _)]
  -- pointwise bound
  have hVx : ∀ x : ℝ, (⨆ (J : ℕ) (u : Fin (J+1) → {t : ℝ // 0 < t}),
        ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
          ENNReal.ofReal ((∑ j : Fin J, ‖α x ((u (Fin.castSucc j)) : ℝ) - α x ((u (Fin.succ j)) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)))
      ≤ 100 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
          + dyadicVar (α x) s) := by
    intro x
    exact variation_cont_le_dyadic_add_within (α := α x) (h := hfun Ψ g x)
      (hfun_nonneg Ψ g x) (fun a b ha hab => intervalIntegrable_hfun Ψ g x hg2 ha hab)
      (fun a b ha hab => conv_dilate_ftc Ψ g x hg2 ha hab) (le_of_lt hs)
  -- decomposition of the dyadic variation
  have hDbound : ∀ x : ℝ, dyadicVar (α x) s
      ≤ dyadicVar (βΛ x) s + 2 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    intro x
    refine (dyadicVar_inv_le (α x) s).trans ((hDαle x).trans ?_)
    exact add_le_add le_rfl (dyadicVar_le_tsum (βR x) (by linarith : (2:ℝ) ≤ s))
  -- measurability
  have hαmeas : AEMeasurable (fun x : ℝ => (dyadicVar (α x) s) ^ 2) volume := by
    have h := aemeasurable_dyadicVar (Ψ := Ψ) (g := g) hg2 s
    have h' : AEMeasurable (fun x : ℝ => dyadicVar (α x) s) volume := by
      simpa only [hα] using h
    exact h'.pow_const 2
  -- within-level bound
  have hSq : ∫⁻ x : ℝ, (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
      ≤ ENNReal.ofReal Cw * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
    rw [show (fun x : ℝ => ∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
        = fun x : ℝ => ∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), ‖∫ y : ℝ, g y * (t⁻¹ * Theta Ψ ((x-y)/t))‖ / t)) ^ (2:ℝ) from
      funext fun x => within_level_ident Ψ g x]
    exact hCw g hg2 hgt
  -- handle bound
  have hDh : ∫⁻ x : ℝ, (dyadicVar (βΛ x) s) ^ 2
      ≤ ENNReal.ofReal ((Ch/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖c * g x‖^2) := by
    refine (lintegral_mono fun x => ?_).trans
      (hCh s hs hs3 (fun y => c * g y) (hg2.const_mul c) (hgt.const_mul c))
    refine le_of_eq ?_
    rw [show (βΛ x) = (fun u : ℝ => ∫ y : ℝ, (c * g y) * (u * max 0 (1 - u * |x - y|)))
        from hβΛeq x, dyadicVar_betaLam_max c g x s]
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  have hcg : ∫⁻ x : ℝ, ENNReal.ofReal (‖c * g x‖^2)
      = ENNReal.ofReal (‖c‖^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _)]
  -- remainder bound
  have hRrS : ∫⁻ x : ℝ, (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal Cr * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
    refine (lintegral_mono fun x => le_of_eq (tsum_congr fun l => ?_)).trans (hCr g hg2)
    rw [hβReq x, betaR_zpow]
  have hDhmeas : AEMeasurable (fun x : ℝ => (dyadicVar (βΛ x) s) ^ 2) volume := by
    have h := aemeasurable_dyadicVar_lam (g := g) hg2 c s
    have h' : AEMeasurable (fun x : ℝ => dyadicVar (βΛ x) s) volume := by
      simpa only [hβΛeq] using h
    exact h'.pow_const 2
  have hD2 : ∫⁻ x : ℝ, (dyadicVar (α x) s) ^ 2
      ≤ (4 * ENNReal.ofReal ((Ch/(s-2))^2) * ENNReal.ofReal (‖c‖^2) + 16 * ENNReal.ofReal Cr)
          * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2) := by
    have hpt : ∀ x : ℝ, (dyadicVar (α x) s) ^ 2
        ≤ 4 * (dyadicVar (βΛ x) s) ^ 2 + 16 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) := by
      intro x
      calc (dyadicVar (α x) s) ^ 2
          ≤ (dyadicVar (βΛ x) s + 2 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ 2 :=
            pow_le_pow_left' (hDbound x) 2
        _ ≤ 4 * ((dyadicVar (βΛ x) s) ^ 2
              + (2 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ 2) :=
            add_sq_le_four _ _
        _ = 4 * (dyadicVar (βΛ x) s) ^ 2 + 16 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) := by
            rw [mul_pow, sq_rpow_half]; ring
    have hDh4 : AEMeasurable (fun x : ℝ => 4 * (dyadicVar (βΛ x) s) ^ 2) volume :=
      hDhmeas.const_mul 4
    calc ∫⁻ x : ℝ, (dyadicVar (α x) s) ^ 2
        ≤ ∫⁻ x : ℝ, (4 * (dyadicVar (βΛ x) s) ^ 2 + 16 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ))) :=
          lintegral_mono hpt
      _ = (∫⁻ x : ℝ, 4 * (dyadicVar (βΛ x) s) ^ 2)
            + ∫⁻ x : ℝ, 16 * (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) :=
          lintegral_add_left' hDh4 _
      _ = 4 * (∫⁻ x : ℝ, (dyadicVar (βΛ x) s) ^ 2)
            + 16 * ∫⁻ x : ℝ, (∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) := by
          rw [lintegral_const_mul' 4 (fun x : ℝ => dyadicVar (βΛ x) s ^ 2) (by norm_num),
            lintegral_const_mul' 16 (fun x : ℝ => ∑' l : ℤ, ‖βR x ((2:ℝ)^l)‖ₑ ^ (2:ℝ)) (by norm_num)]
      _ ≤ 4 * (ENNReal.ofReal ((Ch/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖c * g x‖^2))
            + 16 * (ENNReal.ofReal Cr * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hDh (by norm_num))
            (mul_le_mul_of_nonneg_left hRrS (by norm_num))
      _ = (4 * ENNReal.ofReal ((Ch/(s-2))^2) * ENNReal.ofReal (‖c‖^2) + 16 * ENNReal.ofReal Cr)
            * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2) := by
          rw [hcg]; ring
  -- arithmetic
  have harith : ENNReal.ofReal (40000 * (Cw + 4 * (Ch / (s - 2)) ^ 2 * ‖c‖ ^ 2 + 16 * Cr))
      ≤ ENNReal.ofReal ((200 * (Cw + 4 * Ch ^ 2 * ‖c‖ ^ 2 + 16 * Cr + 1) / (s - 2)) ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 0 < s - 2 := by linarith
    have hdl : (s - 2) ^ 2 ≤ 1 := by nlinarith
    have hdpos : (0:ℝ) < (s - 2) ^ 2 := by positivity
    have hcnn : 0 ≤ ‖c‖ ^ 2 := by positivity
    have hkey : 4 * (Ch / (s - 2)) ^ 2 * ‖c‖ ^ 2 = 4 * Ch ^ 2 * ‖c‖ ^ 2 / (s - 2) ^ 2 := by
      rw [div_pow]; ring
    rw [hkey]
    have hgoal : 40000 * (Cw + 4 * Ch ^ 2 * ‖c‖ ^ 2 / (s - 2) ^ 2 + 16 * Cr)
        = (40000 * (Cw * (s - 2) ^ 2 + 4 * Ch ^ 2 * ‖c‖ ^ 2 + 16 * Cr * (s - 2) ^ 2)) / (s - 2) ^ 2 := by
      field_simp
    rw [hgoal, div_pow, div_le_div_iff_of_pos_right hdpos]
    have h1 : Cw * (s - 2) ^ 2 ≤ Cw := by nlinarith [hCwpos.le, hdl]
    have h3 : Cr * (s - 2) ^ 2 ≤ Cr := by nlinarith [hCrpos.le, hdl]
    nlinarith [h1, h3, hcnn, hCwpos.le, hChpos.le, hCrpos.le,
      sq_nonneg (Cw + 4 * Ch^2 * ‖c‖^2 + 16*Cr), mul_nonneg hCwpos.le hcnn]

  -- the constant bookkeeping at the very end
  have hK : 100 ^ 2 * 4 * (ENNReal.ofReal Cw + (4 * ENNReal.ofReal ((Ch/(s-2))^2)
      * ENNReal.ofReal (‖c‖^2) + 16 * ENNReal.ofReal Cr))
      = ENNReal.ofReal (40000 * (Cw + 4 * (Ch/(s-2))^2 * ‖c‖^2 + 16 * Cr)) := by
    have hnn : (0:ℝ) ≤ 4 * ((Ch/(s-2))^2 * ‖c‖^2) + 16 * Cr :=
      add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hCrpos.le)
    have e4 : (4:ℝ≥0∞) * ENNReal.ofReal ((Ch/(s-2))^2) * ENNReal.ofReal (‖c‖^2)
        = ENNReal.ofReal (4 * ((Ch/(s-2))^2 * ‖c‖^2)) := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg _))]
      congr 1; ring
    have e16 : (16:ℝ≥0∞) * ENNReal.ofReal Cr = ENNReal.ofReal (16 * Cr) := by
      rw [show (16:ℝ≥0∞) = ENNReal.ofReal (16:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)]
    have eadd1 : ENNReal.ofReal (4 * ((Ch/(s-2))^2 * ‖c‖^2)) + ENNReal.ofReal (16 * Cr)
        = ENNReal.ofReal (4 * ((Ch/(s-2))^2 * ‖c‖^2) + 16 * Cr) :=
      (ENNReal.ofReal_add
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hCrpos.le)).symm
    rw [show (100:ℝ≥0∞)^2 * 4 = ENNReal.ofReal (40000:ℝ) by norm_num, e4, e16, eadd1,
      (ENNReal.ofReal_add hCwpos.le hnn).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 40000)]
    congr 1; ring
  calc ∫⁻ x : ℝ, (⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
          ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
            (ENNReal.ofReal ((∑ j : Fin J,
              ‖(∫ y : ℝ, g y * (((u (Fin.castSucc j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.castSucc j) : ℝ)))))
               - (∫ y : ℝ, g y * (((u (Fin.succ j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.succ j) : ℝ)))))‖ ^ s) ^ ((1:ℝ)/s)))) ^ (2 : ℝ)
      = ∫⁻ x : ℝ, (⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
          ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
            (ENNReal.ofReal ((∑ j : Fin J, ‖α x ((u (Fin.castSucc j)) : ℝ) - α x ((u (Fin.succ j)) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)))) ^ 2 := by
          refine lintegral_congr fun x => ?_
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
    _ ≤ ∫⁻ x : ℝ, (100 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
          + dyadicVar (α x) s)) ^ 2 :=
          lintegral_mono fun x => pow_le_pow_left' (hVx x) 2
    _ = ∫⁻ x : ℝ, 100 ^ 2 * (((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
          + dyadicVar (α x) s) ^ 2) := by
          refine lintegral_congr fun x => ?_
          rw [mul_pow]
    _ ≤ ∫⁻ x : ℝ, 100 ^ 2 * (4 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
          + (dyadicVar (α x) s) ^ 2)) := by
          refine lintegral_mono fun x => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
                + dyadicVar (α x) s)) ^ 2
              ≤ 4 * (((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ 2
                + (dyadicVar (α x) s) ^ 2) := add_sq_le_four _ _
            _ = 4 * ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
                + (dyadicVar (α x) s) ^ 2) := by rw [sq_rpow_half]
    _ = 100 ^ 2 * 4 * ∫⁻ x : ℝ, ((∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
          + (dyadicVar (α x) s) ^ 2) := by
          rw [← lintegral_const_mul' (100 ^ 2 * 4)
            (fun x : ℝ => (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ))
              + (dyadicVar (α x) s) ^ 2) (by norm_num)]
          exact lintegral_congr fun x => (mul_assoc _ _ _).symm
    _ = 100 ^ 2 * 4 * ((∫⁻ x : ℝ, (∑' l : ℤ, (ENNReal.ofReal (∫ t in ((2:ℝ)^l)..((2:ℝ)^(l+1)), hfun Ψ g x t)) ^ (2:ℝ)))
          + ∫⁻ x : ℝ, (dyadicVar (α x) s) ^ 2) := by
          rw [lintegral_add_right' _ hαmeas]
    _ ≤ 100 ^ 2 * 4 * (ENNReal.ofReal Cw * (∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2))
          + (4 * ENNReal.ofReal ((Ch/(s-2))^2) * ENNReal.ofReal (‖c‖^2) + 16 * ENNReal.ofReal Cr)
            * (∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hSq hD2) (by positivity)
    _ = 100 ^ 2 * 4 * (ENNReal.ofReal Cw + (4 * ENNReal.ofReal ((Ch/(s-2))^2) * ENNReal.ofReal (‖c‖^2) + 16 * ENNReal.ofReal Cr))
          * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by ring_nf
    _ ≤ ENNReal.ofReal ((200 * (Cw + 4 * Ch ^ 2 * ‖c‖ ^ 2 + 16 * Cr + 1) / (s - 2)) ^ 2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK]
          exact harith













end Commons.Analysis.Fourier
