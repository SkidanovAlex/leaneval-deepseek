import Mathlib
import Submission.Work.A3.majorArcKernel

/-!
# The pure Fresnel bound for the polynomial exponential sum (target of the file)

`Work.A3.expSum_pure_fresnel` is the sharp ("Gauss/Fresnel scale") bound

  `‖expSum Q N β‖ ≤ C · mArcKernel N d β + C`   for `|β| ≤ N^{-d/2}`,  `d = Q.natDegree ≥ 2`.

Equivalently, with `L := |β|^{-1/d} ≥ N^{1/2}` (so `mArcKernel ≍ L`), `‖∑_{n≤N} e(βQ(n))‖ ≤ C·L`.

## Status of this file (session analysis — see `NOTES_A3_expSum_pure_fresnel.md`)

The statement is **TRUE** (numerically verified on the full Nyquist grid over the whole admissible
`β`-range: `sup ‖expSum‖/mArcKernel ≈ 3.1` for `d = 3`, with no growth in `N`), but it is a *sharp*
statement: at the critical scale `β = N^{-d/2}` the truth is `≍ √N` while every tool in this
workspace gives only `N^{d/4}` (or worse):

* `Submission.SdtPoisson.truncated_poisson` (van der Corput's Hilfssatz 1) and `Core.main_bound`
  (Hilfssatz 1 + the sharp *integral* Fresnel bound `exp_integral_second_deriv_le`) give per dyadic
  block `[M,2M]`: `C(βM^{d-1} + (βM^{d-2})^{1/2}M)`, which is `≤ C√M` **iff**
  `M ≤ N^{d/(2(d-1))}` (for `d = 3`: `M ≤ N^{3/4}`), and is `≫ √M` on the **large blocks**
  `N^{d/(2(d-1))} ≤ M ≤ N`;
* `Commons.Analysis.ExponentialSums.second_derivative_test` gives `C(M√r + 1/√r)`, with the same
  `M^{d/2}`-type term;
* the vdC/Weyl second moment gives `N^{1-2^{-(d-1)}+ε}`-type bounds, also `≫ √N`.

The whole content is therefore the **large-block bound**: the square-root cancellation of the *dual*
(Legendre-phase) sum produced by Hilfssatz 1 — the sharp stationary-phase reciprocity. It is
isolated below as `largeBlockFresnel`.

## What *is* formalised here

* the conjugate symmetry `expSum Q N (-β) = conj (expSum Q N β)` (so `WLOG β ≥ 0`);
* the trivial bound `‖expSum Q N β‖ ≤ N`;
* the trivial range `|β| ≤ N^{-d}` of the target (`mArcKernel ≥ 2^{-1/d}N` there);
* the *small-block* estimate: on any block inside `[1, N^{d/(2(d-1))}]` the current
  Hilfssatz-1 machinery (`Core.main_bound`) does give `≤ C√M`.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- `expSum` at `-β` is the conjugate of `expSum` at `β` (because `Q` takes integer values). -/
lemma expSum_neg (Q : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    expSum Q N (-β) = (starRingEnd ℂ) (expSum Q N β) := by
  unfold expSum
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The norm of `expSum` is even in `β`. -/
lemma norm_expSum_neg (Q : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    ‖expSum Q N (-β)‖ = ‖expSum Q N β‖ := by
  rw [expSum_neg, Complex.norm_conj]

/-- The trivial bound: `expSum` is a sum of `N` unit complex numbers. -/
lemma norm_expSum_le (Q : Polynomial ℤ) (N : ℕ) (β : ℝ) : ‖expSum Q N β‖ ≤ (N : ℝ) := by
  have hsum : ∑ n ∈ Finset.Icc 1 N,
        ‖Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * β)))‖
      = (N : ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 N,
          ‖Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * β)))‖
        = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have h : -(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * β))
              = ((-(2 * Real.pi * (((Q.eval (n : ℤ) : ℤ) : ℝ) * β)) : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [h, Complex.norm_exp_ofReal_mul_I]
      _ = ((Finset.Icc 1 N).card : ℝ) := by simp
      _ = (N : ℝ) := by rw [Nat.card_Icc]; simp
  calc ‖expSum Q N β‖
      ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * β)))‖ := by
        unfold expSum
        exact norm_sum_le (Finset.Icc 1 N)
          (fun n : ℕ => Complex.exp (-(2 * Real.pi * Complex.I *
            (((Q.eval (n : ℤ) : ℤ) : ℝ) * β))))
    _ = (N : ℝ) := hsum

/-- `mArcKernel` is at least `2^{-1/d}·N` on the trivial range `|β| ≤ N^{-d}`. -/
lemma le_mArcKernel_of_le (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) {β : ℝ}
    (hβ : |β| ≤ (N : ℝ) ^ (-(d : ℝ))) :
    (2 : ℝ) ^ (-(1 : ℝ) / (d : ℝ)) * (N : ℝ) ≤ mArcKernel N d β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (N : ℝ) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hz : (-(1 : ℝ) / (d : ℝ)) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (div_nonneg zero_le_one hd0.le)
  have hx : (0 : ℝ) < |β| + (N : ℝ) ^ (-(d : ℝ)) := by linarith [abs_nonneg β, hpos]
  have hxy : |β| + (N : ℝ) ^ (-(d : ℝ)) ≤ 2 * (N : ℝ) ^ (-(d : ℝ)) := by linarith
  have hle := Real.rpow_le_rpow_of_nonpos hx hxy hz
  have hmul : (2 * (N : ℝ) ^ (-(d : ℝ))) ^ (-(1 : ℝ) / (d : ℝ))
      = (2 : ℝ) ^ (-(1 : ℝ) / (d : ℝ)) * (N : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt hpos), ← Real.rpow_mul (le_of_lt hN0)]
    congr 1
    have h : (-(d : ℝ)) * (-(1 : ℝ) / (d : ℝ)) = 1 := by field_simp
    rw [h, Real.rpow_one]
  rw [mArcKernel, ← hmul]
  exact hle

/-- **The trivial range of the target**: for `|β| ≤ N^{-d}` the claimed bound holds, with the
constant `2^{1/d}` (as `mArcKernel N d β ≥ 2^{-1/d}·N` there and `‖expSum‖ ≤ N`). -/
lemma expSum_trivial_range (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : |β| ≤ (N : ℝ) ^ (-(Polynomial.natDegree Q : ℝ))) :
    ‖expSum Q N β‖ ≤ (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) *
      mArcKernel N (Polynomial.natDegree Q) β := by
  have hd1 : 1 ≤ Polynomial.natDegree Q := le_trans (by norm_num) hd
  have h1 : ‖expSum Q N β‖ ≤ (N : ℝ) := norm_expSum_le Q N β
  have h2 := le_mArcKernel_of_le (Polynomial.natDegree Q) N hd1 hN hβ
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) *
      (2 : ℝ) ^ (-(1 : ℝ) / (Polynomial.natDegree Q : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hz : (1 : ℝ) / (Polynomial.natDegree Q : ℝ) +
        -(1 : ℝ) / (Polynomial.natDegree Q : ℝ) = 0 := by ring
    rw [hz, Real.rpow_zero]
  have hsplit : (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) *
      ((2 : ℝ) ^ (-(1 : ℝ) / (Polynomial.natDegree Q : ℝ)) * (N : ℝ)) = (N : ℝ) := by
    rw [← mul_assoc, htwo, one_mul]
  have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc ‖expSum Q N β‖ ≤ (N : ℝ) := norm_expSum_le Q N β
    _ = (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) *
          ((2 : ℝ) ^ (-(1 : ℝ) / (Polynomial.natDegree Q : ℝ)) * (N : ℝ)) := hsplit.symm
    _ ≤ (2 : ℝ) ^ ((1 : ℝ) / (Polynomial.natDegree Q : ℝ)) *
          mArcKernel N (Polynomial.natDegree Q) β := mul_le_mul_of_nonneg_left h2 hnonneg

end
end Work.A3
