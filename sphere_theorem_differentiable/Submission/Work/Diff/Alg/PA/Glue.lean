import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.compact_frob
import Submission.Work.Diff.Alg.PA.CS_bounds
import Submission.Work.Diff.GE.curv4_trace
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.PP.Q_Iso
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Glue lemmas for `Work.Diff.Alg.pinching_algebra`

Elementary computations about `Q`, `frobSq`, `scalAlg`, `frobSqTF` and the tensor pairing `tpair`
that the assembly of `PinchingAlgebra` needs.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Homogeneity of `Q`, `frobSq` and `scalAlg` -/

/-- `Q` is homogeneous of degree two. -/
theorem Q_smul (n : ℕ) (c : ℝ) (R : Curv4 n) : Q (c • R) = c ^ 2 • Q R := by
  ext i j k l
  have h : ∀ p q : Fin n,
      c * R i j p q * (c * R k l p q) + 2 * (c * R i p k q) * (c * R j p l q)
        - 2 * (c * R i p l q) * (c * R j p k q)
      = c ^ 2 * (R i j p q * R k l p q + 2 * R i p k q * R j p l q
          - 2 * R i p l q * R j p k q) := by
    intro p q; ring
  simp only [Q, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  exact h p q

/-- `frobSq` is homogeneous of degree two. -/
theorem frobSq_smul (n : ℕ) (c : ℝ) (R : Curv4 n) : frobSq (c • R) = c ^ 2 * frobSq R := by
  rw [← tpair_self n (c • R), tpair_smul_left, tpair_smul_right, tpair_self n R]
  ring

/-- `scalAlg` is homogeneous of degree one. -/
theorem scalAlg_smul (n : ℕ) (c : ℝ) (R : Curv4 n) : scalAlg (c • R) = c * scalAlg R := by
  simp only [scalAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- `scal (Q R) = 2 |Ric|²` in the `ricSq` normalisation. -/
theorem scalAlg_Q' (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) :
    scalAlg (Q R) = 2 * ricSq R := by
  have h := Work.Diff.Alg.Pinch.scalAlg_Q n hR
  simpa only [ricSq, Work.Diff.Alg.Pinch.ric, sq] using h

/-! ## Norm bounds -/

/-- Each component is bounded by the norm of the array. -/
theorem comp_le_norm (R : Curv4 n) (i j k l : Fin n) : |R i j k l| ≤ ‖R‖ :=
  Work.Diff.L.Curv4.abs_apply_le_norm R i j k l

/-- `frobSq` is bounded by `n⁴` times the squared norm. -/
theorem frobSq_le_norm (R : Curv4 n) : frobSq R ≤ (n : ℝ) ^ 4 * ‖R‖ ^ 2 := by
  have hterm : ∀ i j k l : Fin n, R i j k l ^ 2 ≤ ‖R‖ ^ 2 := by
    intro i j k l
    have h := comp_le_norm R i j k l
    have h2 : |R i j k l| ≤ |‖R‖| := by rwa [abs_of_nonneg (norm_nonneg R)]
    exact sq_le_sq.mpr h2
  calc frobSq R = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 := rfl
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, ‖R‖ ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro k _
        apply Finset.sum_le_sum; intro l _
        exact hterm i j k l
    _ = (n : ℝ) ^ 4 * ‖R‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `√(frobSq R) ≤ n² ‖R‖`. -/
theorem sqrt_frobSq_le_norm (R : Curv4 n) :
    Real.sqrt (frobSq R) ≤ (n : ℝ) ^ 2 * ‖R‖ := by
  have h1 : Real.sqrt (frobSq R) ≤ Real.sqrt ((n : ℝ) ^ 4 * ‖R‖ ^ 2) :=
    Real.sqrt_le_sqrt (frobSq_le_norm R)
  have h2 : Real.sqrt ((n : ℝ) ^ 4 * ‖R‖ ^ 2) = (n : ℝ) ^ 2 * ‖R‖ := by
    rw [show (n : ℝ) ^ 4 * ‖R‖ ^ 2 = ((n : ℝ) ^ 2 * ‖R‖) ^ 2 from by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  rwa [h2] at h1

/-- `frobSqTF` is bounded by `frobSq` plus the correction term. -/
theorem frobSqTF_le (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) :
    frobSqTF R ≤ frobSq R + 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hd : 0 ≤ 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    positivity
  rw [frobSqTF]
  linarith

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have h3 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `√(frobSqTF R) ≤ √(frobSq R) + √(2 scalAlg R ^ 2 / (n (n-1)))`. -/
theorem sqrt_frobSqTF_le (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) :
    Real.sqrt (frobSqTF R)
      ≤ Real.sqrt (frobSq R) + Real.sqrt (2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have h1 : frobSqTF R ≤ frobSq R + 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
    frobSqTF_le n hn R
  refine le_trans (Real.sqrt_le_sqrt h1) ?_
  refine le_trans (sqrt_add_le' _ _ (frobSq_nonneg R) ?_) (le_refl _)
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  positivity


/-! ## The trace-free part of `R` and its bounds -/

/-- The trace-free part: `frobSqTF R` is the squared norm of `R - (S/(n(n-1))) Iso n`. -/
theorem frobSqTF_eq (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) :
    frobSqTF R = frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) := by
  rw [(Work.Diff.GE.curv4_trace R hR).2.1]
  simp only [frobSq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The denomination `n(n-1)` is positive for `n ≥ 2`. -/
theorem denom_pos (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem denom_ne (n : ℕ) (hn : 2 ≤ n) : ((n : ℝ) * ((n : ℝ) - 1)) ≠ 0 :=
  ne_of_gt (denom_pos n hn)

/-- Expansion of the squared norm of the trace-free part. -/
theorem frobSq_sub_iso (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) (hR : IsAlgCurv R) :
    frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
      = frobSq R - 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [frobSq_sub_smul, tpair_Iso hR, frobSq_Iso]
  have hd := denom_ne n hn
  field_simp
  ring

/-- `√(frobSqTF R) = √(frobSq R°)` and `√(frobSq R°) ≤ √(frobSq R)`. -/
theorem sqrt_frobSq_sub_iso_le (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) (hR : IsAlgCurv R) :
    Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
      ≤ Real.sqrt (frobSq R) := by
  apply Real.sqrt_le_sqrt
  rw [frobSq_sub_iso n hn R hR]
  have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := denom_pos n hn
  have h2 : 0 ≤ 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  linarith

/-- The coefficient `S/(n(n-1))` is bounded by `√(frobSq R)`. -/
theorem abs_iso_coeff_le (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) (hR : IsAlgCurv R) :
    |scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))| ≤ Real.sqrt (frobSq R) := by
  have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := denom_pos n hn
  have hdne : ((n : ℝ) * ((n : ℝ) - 1)) ≠ 0 := ne_of_gt hd
  have h0 : 0 ≤ frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) :=
    frobSq_nonneg _
  rw [frobSq_sub_iso n hn R hR] at h0
  have h1 : scalAlg R ^ 2 / (((n : ℝ) * ((n : ℝ) - 1)) ^ 2) ≤ frobSq R := by
    have hd2 : (2 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have h3 : 2 * scalAlg R ^ 2 ≤ frobSq R * ((n : ℝ) * ((n : ℝ) - 1)) := by
      have h4 : 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ frobSq R := by linarith
      exact (div_le_iff₀ hd).mp h4
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (((n : ℝ) * ((n : ℝ) - 1)) ^ 2))]
    nlinarith [frobSq_nonneg R, h3, hd, hd2]
  have h2 : Real.sqrt (scalAlg R ^ 2 / (((n : ℝ) * ((n : ℝ) - 1)) ^ 2)) ≤ Real.sqrt (frobSq R) :=
    Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (scalAlg R ^ 2 / (((n : ℝ) * ((n : ℝ) - 1)) ^ 2))
      = |scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))| := by
    rw [← div_pow, Real.sqrt_sq_eq_abs]
  rwa [h3] at h2

/-- `tpair (R - (S/(n(n-1))) Iso) Iso = 0`. -/
theorem tpair_sub_iso_eq_zero (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) (hR : IsAlgCurv R) :
    tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Iso n) = 0 := by
  rw [tpair_sub_left, tpair_smul_left, tpair_Iso hR, tpair_self n (Iso n), frobSq_Iso]
  have hd := denom_ne n hn
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : ((n : ℝ) - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- `√(frobSq (c • R)) = |c| √(frobSq R)`. -/
theorem sqrt_frobSq_smul (n : ℕ) (c : ℝ) (R : Curv4 n) :
    Real.sqrt (frobSq (c • R)) = |c| * Real.sqrt (frobSq R) := by
  rw [frobSq_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- `√(2 S²/d) ≤ n² ‖R‖ √(2/d)`. -/
theorem sqrt_scal_sq_div_le (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) :
    Real.sqrt (2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (n : ℝ) ^ 2 * ‖R‖ * Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := denom_pos n hn
  have hq : (0 : ℝ) ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  have h : 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))
      = (2 / ((n : ℝ) * ((n : ℝ) - 1))) * scalAlg R ^ 2 := by ring
  rw [h, Real.sqrt_mul hq, Real.sqrt_sq_eq_abs]
  have hS : |scalAlg R| ≤ (n : ℝ) ^ 2 * ‖R‖ := Work.Diff.L.abs_scalAlg_le R
  have h1 : Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) * |scalAlg R|
      ≤ Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) * ((n : ℝ) ^ 2 * ‖R‖) :=
    mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
  calc Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) * |scalAlg R|
      ≤ Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) * ((n : ℝ) ^ 2 * ‖R‖) := h1
    _ = (n : ℝ) ^ 2 * ‖R‖ * Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by ring


/-! ## Additivity of the pairing -/

theorem tpair_add_left (n : ℕ) (A A' B : Curv4 n) :
    tpair n (A + A') B = tpair n A B + tpair n A' B := by
  simp only [tpair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem tpair_add_right (n : ℕ) (A B B' : Curv4 n) :
    tpair n A (B + B') = tpair n A B + tpair n A B' := by
  rw [tpair_comm n A (B + B'), tpair_add_left, tpair_comm n B A, tpair_comm n B' A]

/-- `qPair` is `tpair` against `Q`. -/
theorem qPair_eq_tpair (n : ℕ) (R : Curv4 n) : qPair R = tpair n R (Q R) := rfl

end Work.Diff.Alg.PA
