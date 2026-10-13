import Mathlib
import Submission.Work.WilE4.CAD.type_local
import Submission.Work.WilE4.CAD.threshold_along_tendsto

set_option maxHeartbeats 1000000

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open Polynomial

/-- The realised sign vector set of a non-degenerate specialised family is closed along a sequence
of non-degenerate parameter values, provided the evaluating arguments `w n` are *frequently
unbounded* in absolute value.

The point is that beyond a threshold the sign of `(q (P i) y).eval z` is the sign of the leading
coefficient times the sign of `z` raised to the degree.  The degrees are constant along the
sequence and at the limit, so the threshold can be taken uniform (that is
`threshold_along_tendsto`); frequent unboundedness of `|w n|` then supplies an index `n₀` at which
`a n₀` is close to `x` and `|w n₀|` exceeds the threshold, and the sign of `w n₀` tells us whether
to realise `v` at the large argument `M` or at `-M`. -/
theorem realized_of_tendsto_unbdd_good {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {d : Fin k → ℕ} {x : Fin m → ℝ} (hgoodx : Good P d x)
    {a : ℕ → Fin m → ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds x)) (hgoodn : ∀ n, Good P d (a n))
    {v : Fin k → SignType} {w : ℕ → ℝ}
    (hwv : ∀ n, ∀ i, SignType.sign ((q (P i) (a n)).eval (w n)) = v i)
    (hunb : ∀ M : ℝ, ∃ᶠ n in Filter.atTop, M < |w n|) :
    realized P x v := by
  -- The leading coefficient of `q (P i) x` does not vanish.
  have hne0 : ∀ i, q (P i) x ≠ 0 := by
    intro i hz
    have hcc := hgoodx.2.2 i
    rw [hz, Polynomial.derivative_zero] at hcc
    exact not_isCoprime_zero_zero hcc
  have hc : ∀ i, (q (P i) x).coeff (d i) ≠ 0 := by
    intro i
    rw [← hgoodx.1 i, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (hne0 i)
  -- Uniform asymptotic description of the signs at large arguments, at `x` and along the sequence.
  have hthr : ∀ i, ∃ R > 0,
      (∀ y : ℝ, R ≤ |y| → SignType.sign ((q (P i) x).eval y)
          = SignType.sign ((q (P i) x).coeff (d i)) * SignType.sign y ^ (d i)) ∧
      (∀ᶠ n in Filter.atTop, ∀ y : ℝ, R ≤ |y| →
          SignType.sign ((q (P i) (a n)).eval y)
            = SignType.sign ((q (P i) (a n)).coeff (d i)) * SignType.sign y ^ (d i)) := fun i =>
    threshold_along_tendsto (Q := fun y => q (P i) y) (x₀ := x) (a := a) (d := d i)
      (continuous_q_coeff (P i)) ha (hgoodx.1 i) (fun n => (hgoodn n).1 i)
  set rho : Fin k → ℝ := fun i => Classical.choose (hthr i) with hrhodef
  set M : ℝ := 1 + ∑ i, rho i with hMdef
  have hrho_pos : ∀ i, 0 < rho i := fun i => (Classical.choose_spec (hthr i)).1
  have hMpos : 0 < M := by
    have hsum : 0 ≤ ∑ i, rho i := Finset.sum_nonneg fun i _ => le_of_lt (hrho_pos i)
    rw [hMdef]
    linarith
  have hrho_le : ∀ i, rho i ≤ M := by
    intro i
    rw [hMdef]
    have h2 : rho i ≤ ∑ j, rho j :=
      Finset.single_le_sum (fun j _ => le_of_lt (hrho_pos j)) (Finset.mem_univ i)
    linarith
  have hformx : ∀ i, ∀ y : ℝ, M ≤ |y| →
      SignType.sign ((q (P i) x).eval y)
        = SignType.sign ((q (P i) x).coeff (d i)) * SignType.sign y ^ (d i) := fun i y hy =>
    (Classical.choose_spec (hthr i)).2.1 y (le_trans (hrho_le i) hy)
  have hforma : ∀ i, ∀ᶠ n in Filter.atTop, ∀ y : ℝ, M ≤ |y| →
      SignType.sign ((q (P i) (a n)).eval y)
        = SignType.sign ((q (P i) (a n)).coeff (d i)) * SignType.sign y ^ (d i) := fun i =>
    ((Classical.choose_spec (hthr i)).2.2).mono fun _ hn y hy => hn y (le_trans (hrho_le i) hy)
  have hsgn : ∀ i, ∀ᶠ n in Filter.atTop,
      SignType.sign ((q (P i) (a n)).coeff (d i))
        = SignType.sign ((q (P i) x).coeff (d i)) := fun i =>
    ha.eventually
      (eventually_sign_eq_of_ne_zero (continuous_q_coeff (P i) (d i)).continuousAt (hc i))
  have hev : ∀ᶠ n in Filter.atTop,
      (∀ i, SignType.sign ((q (P i) (a n)).coeff (d i))
        = SignType.sign ((q (P i) x).coeff (d i))) ∧
      (∀ i, ∀ y : ℝ, M ≤ |y| → SignType.sign ((q (P i) (a n)).eval y)
        = SignType.sign ((q (P i) (a n)).coeff (d i)) * SignType.sign y ^ (d i)) :=
    ((Filter.eventually_all).mpr hsgn).and ((Filter.eventually_all).mpr hforma)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- One index at which the parameter is close to `x` and the argument is beyond the threshold.
  obtain ⟨n₀, hw₀, hn₀⟩ : ∃ n, M < |w n| ∧ N ≤ n :=
    ((hunb M).and_eventually (Filter.eventually_atTop.mpr ⟨N, fun _ hn => hn⟩)).exists
  obtain ⟨hsgn₀, hform₀⟩ := hN n₀ hn₀
  have hwne : w n₀ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hw₀
    linarith
  rcases lt_or_gt_of_ne hwne with hneg | hpos
  · -- `w n₀ < 0`: realise `v` at the large negative argument `-M`.
    refine ⟨-M, fun i => ?_⟩
    have habs : M ≤ |-M| := by rw [abs_neg, abs_of_pos hMpos]
    have h1 := hformx i (-M) habs
    have h2 : v i = SignType.sign ((q (P i) x).coeff (d i)) * (-1 : SignType) ^ (d i) := by
      rw [← hwv n₀ i, hform₀ i (w n₀) (le_of_lt hw₀), hsgn₀ i, sign_neg hneg]
    rw [h1, sign_neg (show -M < 0 by linarith)]
    exact h2.symm
  · -- `0 < w n₀`: realise `v` at the large positive argument `M`.
    refine ⟨M, fun i => ?_⟩
    have habs : M ≤ |M| := by rw [abs_of_pos hMpos]
    have h1 := hformx i M habs
    have h2 : v i = SignType.sign ((q (P i) x).coeff (d i)) := by
      rw [← hwv n₀ i, hform₀ i (w n₀) (le_of_lt hw₀), hsgn₀ i, sign_pos hpos, one_pow,
        mul_one]
    rw [h1, sign_pos hMpos, one_pow, mul_one]
    exact h2.symm

end Work.WilE4.CAD
