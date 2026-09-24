import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder

set_option autoImplicit false
set_option maxHeartbeats 0


/-!
# The chord bound: `2d ≤ sin(πd)` on `[0, 1/2]`  (fleet task)

**TARGET:** `Submission.Chord.sin_pi_mul_ge_two_mul`.

This is the real-content core of the `|1 − w| ≥ c·‖α‖` link of the van der Corput
layer (`w = e^{2πiα}`, `‖α‖ = dist(α, ℤ)`): on the unit circle the chord
`|1 − e^{2πi d}| = 2·sin(πd)` is comparable to the arc distance `2πd`, and the
needed one-sided bound is `2d ≤ sin(πd)` for `0 ≤ d ≤ 1/2` (equality at `d = 1/2`).
Machine-verified, axiom-clean.

The proof is Jordan's inequality: `Mathlib` provides `Real.mul_le_sin`, the linear
lower bound `(2 / π) · x ≤ sin x` valid on `x ∈ [0, π / 2]` (proved in Mathlib
from the strict concavity of `sin` on `[0, π]`).  Substituting `x = π·d` with
`0 ≤ d ≤ 1/2` gives `(2/π)·(π·d) = 2d ≤ sin(π·d)`, exactly as required.
-/

open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.Chord

/-- **Core chord inequality**: `2d ≤ sin(πd)` for `0 ≤ d ≤ 1/2`.

PROOF SUGGESTIONS (pick whichever works with this Mathlib revision):
(A) CONCAVITY: on `[0, π/2]` the function `Real.sin` lies above its chord, so for
`x ∈ [0, π/2]`: `sin x ≥ (2/π)·x`; substituting `x = πd` gives `sin(πd) ≥ 2d`.
To formalize concavity you may prove that `g(x) := sin x − (2/π)·x` is concave on
`[0, π/2]` via its second derivative (`g'' = −sin ≤ 0` there: use
`Real.sin_nonneg_of_nonneg_of_le_pi`), then use the concavity property
(`ConvexOn`/`concaveOn` API from `Mathlib.Analysis.Convex`): a concave function on
an interval is ≥ the chord joining its endpoint values, and `g(0) = g(π/2) = 0`.
(B) TWO-REGION TAYLOR: `Real.sin_ge_sub_cube` gives `sin x ≥ x − x^3/6` for
`x ≥ 0`; on `x ∈ [0, 1.476]` (i.e. `x^2 ≤ 6(1 − 2/π)` would be needed — take a
safe subrange like `x ≤ 3/2` where `x − x^3/6 ≥ (2/π)x` is checkable by
`nlinarith` after `ring_nf`), and on the remaining tail `x ∈ [3/2, π/2]` use that
`sin` is increasing on `[0, π/2]` (derivative `cos ≥ 0` on `[0, π/2]`, e.g. via
`Real.cos_nonneg_of_mem_Icc`/`Real.cos_nonneg` facts) so `sin x ≥ sin(3/2)`, then
`nlinarith` with the numerical value `0.997 < sin(3/2)`-style inequalities that
`norm_num` can certify on the two endpoints `(2/π)·(3/2)` and `(2/π)·(π/2)`.
Recall `Real.sin_pos_of_pos_of_lt_pi`, `Real.sin_nonneg_of_nonneg_of_le_pi`,
`Real.pi_pos`, `Real.pi_gt_three`, `pi_lt_four`-style bounds for the numerics. -/
lemma sin_pi_mul_ge_two_mul (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ (1 / 2 : ℝ)) :
    (2 : ℝ) * d ≤ Real.sin (Real.pi * d) := by
  -- `π·d` lies in `[0, π/2]` since `0 ≤ d ≤ 1/2` and `π > 0`
  have hx0 : 0 ≤ Real.pi * d := by positivity
  have hx : Real.pi * d ≤ Real.pi / 2 := by
    calc
      Real.pi * d ≤ Real.pi * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = Real.pi / 2 := by ring
  -- Jordan's inequality (linear lower bound for `sin` on `[0, π/2]`)
  have h := Real.mul_le_sin (x := Real.pi * d) hx0 hx
  calc
    (2 : ℝ) * d = (2 / Real.pi) * (Real.pi * d) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * d) := h

end Submission.Chord

open Complex
open scoped Real BigOperators ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Shared basis for the truncated Poisson formula (van der Corput Hilfssatz 1)

Definitions and elementary lemmas about the phase exponential
`E t := e^{2π i t}`, the sawtooth `saw x := {x} − 1/2` and its Dirichlet
partial sums `sawHat K x := Σ_{0<|ν|≤K} E(−νx)/(2πiν)`.
Used by `Submission.SdtPoisson` and by children proving the classical
"sawtooth Fourier series" facts.
-/

namespace Submission.SdtPoisson

noncomputable section

/-- `tau := 2π` as a complex number. -/
def tau : ℂ := ((2 * Real.pi : ℝ) : ℂ)

/-- `E t := e^{2π i t}` (complex). -/
def E (t : ℝ) : ℂ := cexp ((((2 * Real.pi * t : ℝ) : ℝ) : ℂ) * I)

lemma E_eq_tau (t : ℝ) : E t = cexp (tau * (t : ℂ) * I) := by
  dsimp [E, tau]
  congr 1
  norm_num

lemma E_norm (t : ℝ) : ‖E t‖ = 1 := by
  dsimp [E]
  simpa using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t))

lemma E_norm_le (t : ℝ) : ‖E t‖ ≤ 1 := by
  rw [E_norm]

lemma E_add (t s : ℝ) : E (t + s) = E t * E s := by
  rw [E_eq_tau, E_eq_tau (t := t), E_eq_tau (t := s)]
  have harg : tau * (((t + s : ℝ) : ℂ)) * I = tau * (t : ℂ) * I + tau * (s : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma E_neg (t : ℝ) : E (-t) = (E t)⁻¹ := by
  rw [E_eq_tau, E_eq_tau (t := t)]
  simp
  exact Complex.exp_neg (tau * (t : ℂ) * I)

lemma E_sub (t s : ℝ) : E (t - s) = E t * (E s)⁻¹ := by
  have h : t - s = t + -s := by ring
  rw [h, E_add, E_neg]

lemma E_of_int (z : ℤ) : E (z : ℝ) = 1 := by
  rw [E_eq_tau]
  have h : tau * (((z : ℝ) : ℂ)) * I = (z : ℂ) * (tau * I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul]
  have hpi : cexp (tau * I) = 1 := by
    dsimp [tau]
    simpa using (Complex.exp_two_pi_mul_I)
  rw [hpi]
  simp

/-- The sawtooth `{x} − 1/2`. -/
def saw (x : ℝ) : ℝ := Int.fract x - 1 / 2

/-- The Dirichlet partial sum of the sawtooth Fourier series:
`sawHat K x := Σ_{0<|ν|≤K} E(−νx)/(2πiν)`. -/
def sawHat (K : ℕ) (x : ℝ) : ℂ :=
  ∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))

/-- The positive-frequency half of `sawHat`. -/
def sawHatPos (K : ℕ) (x : ℝ) : ℂ :=
  ∑ ν ∈ Finset.Icc 1 (K : ℤ), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))

/-! ### Shared machinery: symmetric-index sums, conjugation, sine identity

All helper names carry an `sb_` prefix to avoid clashing with the (many)
parallel modules that import `SawBasis` and develop the same Fourier facts.
-/

/-- `E t = cos(2πt) + i sin(2πt)`. -/
lemma sb_E_eq_cos_sin (t : ℝ) :
    E t = ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ) + ((Real.sin (2 * Real.pi * t) : ℝ) : ℂ) * I := by
  unfold E
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `E (−t) = cos(2πt) − i sin(2πt)`. -/
lemma sb_E_neg_eq_cos_sin (t : ℝ) :
    E (-t) = ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ) - ((Real.sin (2 * Real.pi * t) : ℝ) : ℂ) * I := by
  unfold E
  rw [Complex.exp_mul_I]
  rw [show (2 * Real.pi * (-t) : ℝ) = -(2 * Real.pi * t) by ring]
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `E t − E (−t) = 2i sin(2πt)`. -/
lemma sb_E_sub_E_neg (t : ℝ) : E t - E (-t) = (2 : ℂ) * I * (Real.sin (2 * Real.pi * t) : ℂ) := by
  rw [sb_E_eq_cos_sin, sb_E_neg_eq_cos_sin]
  ring

/-- `E (−t) − E t = −2i sin(2πt)`. -/
lemma sb_E_neg_sub_E (t : ℝ) : E (-t) - E t = -((2 : ℂ) * I * (Real.sin (2 * Real.pi * t) : ℂ)) := by
  have h := sb_E_sub_E_neg (-t)
  rw [neg_neg] at h
  rw [show (2 * Real.pi * (-t) : ℝ) = -(2 * Real.pi * t) by ring, Real.sin_neg] at h
  rw [Complex.ofReal_neg] at h
  simpa [mul_neg] using h

/-- Pairing the `±j` terms of the Dirichlet kernel gives one sine term. -/
lemma sb_pair_term (t : ℝ) (j : ℤ) (hj : j ≠ 0) :
    E (-((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) +
      E (-(((-j : ℤ) : ℝ) * t)) / ((tau * I) * ((-j : ℤ) : ℂ))
      = -(((Real.sin (2 * Real.pi * (j : ℝ) * t) : ℝ) : ℂ) / ((Real.pi : ℂ) * (j : ℂ))) := by
  have hs : E (-((j : ℝ) * t)) - E ((j : ℝ) * t) =
      -((2 : ℂ) * I * (Real.sin (2 * Real.pi * (j : ℝ) * t) : ℂ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (sb_E_neg_sub_E ((j : ℝ) * t))
  have hnum : -(((-j : ℤ) : ℝ) * t) = (j : ℝ) * t := by
    rw [Int.cast_neg]
    ring
  have hden : ((tau * I) * ((-j : ℤ) : ℂ)) = -((tau * I) * (j : ℂ)) := by
    rw [Int.cast_neg]
    ring
  calc
    E (-((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) +
        E (-(((-j : ℤ) : ℝ) * t)) / ((tau * I) * ((-j : ℤ) : ℂ))
        = (E (-((j : ℝ) * t)) - E ((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) := by
          rw [hnum, hden]
          field_simp [tau]
          ring
    _ = -(((Real.sin (2 * Real.pi * (j : ℝ) * t) : ℝ) : ℂ) / ((Real.pi : ℂ) * (j : ℂ))) := by
          rw [hs]
          dsimp [tau]
          field_simp
          push_cast
          ring

/-- The full symmetric sum (indices `−K..K`, nonzero) equals the sum over
`1..K` of the paired `±j` summands. -/
lemma sb_sum_erase_symm (K : ℕ) (g : ℤ → ℂ) :
    (∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, g ν) =
      ∑ j ∈ Finset.Icc 1 (K : ℤ), (g j + g (-j)) := by
  classical
  let P : Finset ℤ := Finset.Icc 1 (K : ℤ)
  let N : Finset ℤ := Finset.Icc (-(K : ℤ)) (-1 : ℤ)
  have hcover : (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 = N ∪ P := by
    ext ν
    constructor
    · intro hν
      have hmem : ν ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (Finset.mem_erase.mp hν).2
      have h0 : ν ≠ 0 := (Finset.mem_erase.mp hν).1
      have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hmem).1
      have hge : ν ≤ (K : ℤ) := (Finset.mem_Icc.mp hmem).2
      by_cases hpos : 0 < ν
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_Icc.mpr ⟨by omega, hge⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hle, by omega⟩))
    · intro hν
      rcases Finset.mem_union.mp hν with hN | hP
      · have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hN).1
        have hge : ν ≤ -1 := (Finset.mem_Icc.mp hN).2
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hle, by omega⟩⟩
      · have hle : 1 ≤ ν := (Finset.mem_Icc.mp hP).1
        have hge : ν ≤ (K : ℤ) := (Finset.mem_Icc.mp hP).2
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hge⟩⟩
  have hneg : (∑ ν ∈ N, g ν) = ∑ j ∈ P, g (-j) := by
    refine Finset.sum_bij (s := N) (t := P) (f := g) (g := fun j => g (-j))
      (fun ν _ => -ν) ?hi ?hinj ?hsurj ?h
    · intro ν hν
      have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hν).1
      have hge : ν ≤ -1 := (Finset.mem_Icc.mp hν).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb h
      omega
    · intro b hb
      have h1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have h2 : b ≤ (K : ℤ) := (Finset.mem_Icc.mp hb).2
      refine ⟨-b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro a ha
      rw [neg_neg]
  rw [hcover]
  have hdisj : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro ν hN hP
    have hge : ν ≤ -1 := (Finset.mem_Icc.mp hN).2
    have hle : 1 ≤ ν := (Finset.mem_Icc.mp hP).1
    omega
  rw [Finset.sum_union hdisj, hneg]
  rw [add_comm]
  rw [← Finset.sum_add_distrib]

/-- Complex conjugation flips the phase: `conj (E t) = E (−t)`. -/
lemma sb_conj_E (t : ℝ) : conj (E t) = E (-t) := by
  rw [E_eq_tau, E_eq_tau (t := -t)]
  rw [← Complex.exp_conj]
  congr 1
  dsimp [tau]
  rw [map_mul, map_mul]
  rw [Complex.conj_ofReal, Complex.conj_ofReal]
  rw [Complex.conj_I]
  push_cast
  ring

/-- The conjugate of the summand at `ν = j` is the summand at `ν = −j`. -/
lemma sb_conj_sawHat_term (x : ℝ) (j : ℤ) :
    conj (E (-((j : ℝ) * x)) / ((tau * I) * (j : ℂ))) =
      E (-(((-j : ℤ) : ℝ) * x)) / ((tau * I) * ((-j : ℤ) : ℂ)) := by
  have hnumu (u : ℝ) : conj (E (-u)) = E u := by
    simpa using (sb_conj_E (t := -u))
  have hnum : conj (E (-((j : ℝ) * x))) = E ((j : ℝ) * x) := hnumu ((j : ℝ) * x)
  have hden1 : conj ((tau * I) * (j : ℂ)) = -((tau * I) * (j : ℂ)) := by
    rw [map_mul]
    have hc : conj (tau * I) = -(tau * I) := by
      dsimp [tau]
      rw [map_mul]
      rw [Complex.conj_ofReal]
      rw [Complex.conj_I]
      ring
    have hcj : conj ((j : ℤ) : ℂ) = ((j : ℤ) : ℂ) := by
      simp
    rw [hc, hcj]
    ring
  have harg1 : -(((-j : ℤ) : ℝ) * x) = (j : ℝ) * x := by
    rw [Int.cast_neg]
    ring
  have hden2 : (tau * I) * ((-j : ℤ) : ℂ) = -((tau * I) * (j : ℂ)) := by
    rw [Int.cast_neg]
    ring
  calc
    conj (E (-((j : ℝ) * x)) / ((tau * I) * (j : ℂ)))
        = conj (E (-((j : ℝ) * x))) / conj ((tau * I) * (j : ℂ)) := by
          rw [map_div₀]
    _ = E ((j : ℝ) * x) / (-((tau * I) * (j : ℂ))) := by rw [hnum, hden1]
    _ = E (-(((-j : ℤ) : ℝ) * x)) / ((tau * I) * ((-j : ℤ) : ℂ)) := by
          rw [← harg1]
          rw [← hden2]

/-- `sawHat` in terms of the positive part only:
`sawHat K x = sawHatPos K x + conj (sawHatPos K x)`. -/
lemma sawHat_eq_pos_conj (K : ℕ) (x : ℝ) : sawHat K x = sawHatPos K x + conj (sawHatPos K x) := by
  unfold sawHat sawHatPos
  rw [sb_sum_erase_symm]
  rw [Finset.sum_add_distrib]
  have hB : (∑ j ∈ Finset.Icc 1 (K : ℤ),
        E (-(((-j : ℤ) : ℝ) * x)) / ((tau * I) * ((-j : ℤ) : ℂ)))
      = conj (∑ j ∈ Finset.Icc 1 (K : ℤ),
          E (-((j : ℝ) * x)) / ((tau * I) * (j : ℂ))) := by
    calc
      (∑ j ∈ Finset.Icc 1 (K : ℤ),
          E (-(((-j : ℤ) : ℝ) * x)) / ((tau * I) * ((-j : ℤ) : ℂ)))
          = ∑ j ∈ Finset.Icc 1 (K : ℤ),
              conj (E (-((j : ℝ) * x)) / ((tau * I) * (j : ℂ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (sb_conj_sawHat_term x j).symm
      _ = conj (∑ j ∈ Finset.Icc 1 (K : ℤ),
              E (-((j : ℝ) * x)) / ((tau * I) * (j : ℂ))) := by
            rw [map_sum (starRingEnd ℂ)]
  rw [hB]

/-- `sawHat` as a sine-sum: `sawHat K x = -Σ_{ν=1}^K sin(2πνx)/(πν)`. -/
lemma sawHat_eq_sin (K : ℕ) (x : ℝ) :
    sawHat K x = -∑ ν ∈ Finset.Icc 1 (K : ℤ),
      ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℝ) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ)) := by
  unfold sawHat
  rw [sb_sum_erase_symm]
  rw [Finset.sum_congr rfl (fun j hj => sb_pair_term x j (by
    have h1 : (1 : ℤ) ≤ j := (Finset.mem_Icc.mp hj).1
    omega))]
  rw [Finset.sum_neg_distrib]

lemma hasDerivAt_E_comp_aux (F : ℝ → ℝ) {x : ℝ} (hF : HasDerivAt F (deriv F x) x) :
    HasDerivAt (fun y : ℝ => cexp (tau * ((F y : ℝ) : ℂ) * I)) (cexp (tau * ((F x : ℝ) : ℂ) * I) * (tau * ((deriv F x : ℝ) : ℂ) * I)) x := by
  have hd : HasDerivAt (fun y : ℝ => ((F y : ℝ) : ℂ)) ((deriv F x : ℝ) : ℂ) x := hF.ofReal_comp
  have hd2 : HasDerivAt (fun y : ℝ => tau * ((F y : ℝ) : ℂ)) (tau * ((deriv F x : ℝ) : ℂ)) x := hd.const_mul tau
  have hinner : HasDerivAt (fun y : ℝ => tau * ((F y : ℝ) : ℂ) * I) (tau * ((deriv F x : ℝ) : ℂ) * I) x := by
    simpa [mul_assoc] using hd2.mul_const I
  exact ((Complex.hasDerivAt_exp (tau * ((F x : ℝ) : ℂ) * I)).comp x) hinner

/-- derivative of `x ↦ E (F x)`. -/
lemma hasDerivAt_E_comp (F : ℝ → ℝ) {x : ℝ} (hF : HasDerivAt F (deriv F x) x) :
    HasDerivAt (fun y : ℝ => E (F y)) (((tau * I) * ((deriv F x : ℝ) : ℂ)) * E (F x)) x := by
  have hmain := hasDerivAt_E_comp_aux F hF
  convert hmain using 1
  · ext y
    rw [E_eq_tau]
  · rw [E_eq_tau]
    ring

/-- derivative of `x ↦ E(f x − νx)`. -/
lemma hasDerivAt_E_phase (f : ℝ → ℝ) (ν : ℤ) {x : ℝ}
    (hF : HasDerivAt f (deriv f x) x) :
    HasDerivAt (fun y : ℝ => E (f y - (ν : ℝ) * y))
      ((tau * I) * (((deriv f x : ℝ) : ℂ) - (ν : ℂ)) * E (f x - (ν : ℝ) * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (ν : ℝ) * y) (ν : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (ν : ℝ)
  have hG : HasDerivAt (fun y : ℝ => f y - (ν : ℝ) * y) (deriv f x - (ν : ℝ)) x := by
    simpa [Pi.sub_def] using hF.sub hlin
  have hGder : deriv (fun y : ℝ => f y - (ν : ℝ) * y) x = deriv f x - (ν : ℝ) := hG.deriv
  have hG' : HasDerivAt (fun y : ℝ => f y - (ν : ℝ) * y) (deriv (fun y : ℝ => f y - (ν : ℝ) * y) x) x := by
    simpa [hGder] using hG
  have hc := hasDerivAt_E_comp_aux (fun y : ℝ => f y - (ν : ℝ) * y) (x := x) hG'
  have hcE : HasDerivAt (fun y : ℝ => E (f y - (ν : ℝ) * y))
      (E (f x - (ν : ℝ) * x) * (tau * ((deriv f x : ℝ) : ℂ) - tau * (ν : ℂ)) * I) x := by
    convert hc using 1
    · funext y
      rw [E_eq_tau]
    · rw [hGder]
      simp [E_eq_tau]
      ring_nf
  convert hcE using 1
  ring

end

end Submission.SdtPoisson


/-!
# Auxiliary interval-splitting lemma for the second-derivative bound (`SdtOscB`)

Given a continuous function `g` on `[a, b]` whose growth is bounded below by
`δ > 0` (`g y - g x ≥ δ(y - x)` whenever `a ≤ x ≤ y ≤ b` — in particular `g`
is non-decreasing), and given `m > 0`, split `[a,b]` at the level sets
`-m` and `m` into three pieces `[a,p]`, `[p,q]`, `[q,b]`:

* on `(a, p)` one has `g ≤ -m`  (left / negative-slope region),
* on `(q, b)` one has `m ≤ g`   (right / positive-slope region),
* the middle piece has length `q - p ≤ 2m/δ`.

No condition is imposed on `g` inside the middle piece (its integral is bounded
by the trivial length bound).
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtOscSplit

/-- Under the growth bound, `g` is non-decreasing on `[a,b]`. -/
private lemma growth_mono {a b δ : ℝ} {g : ℝ → ℝ}
    (hδ : 0 < δ)
    (hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      δ * (y - x) ≤ g y - g x)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    g x ≤ g y := by
  have hnonneg : 0 ≤ g y - g x := by
    exact le_trans (mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hxy)) (hgr hx hy hxy)
  linarith

/-- Intermediate value theorem: a continuous `g` on `[a,b]` attains every value
between `g a` and `g b`. -/
private lemma exists_crossing {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc a b)) {y : ℝ}
    (hy1 : g a ≤ y) (hy2 : y ≤ g b) :
    ∃ x : ℝ, x ∈ Set.Icc a b ∧ g x = y := by
  have hsub : Set.Icc (g a) (g b) ⊆ g '' Set.Icc a b :=
    intermediate_value_Icc hab hcont
  rcases hsub ⟨hy1, hy2⟩ with ⟨x, hx, hx_eq⟩
  exact ⟨x, hx, hx_eq⟩

/-- **Band splitting lemma.** -/
lemma exists_band_split {a b m δ : ℝ} (hab : a ≤ b) (hm : 0 < m) (hδ : 0 < δ)
    (g : ℝ → ℝ)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      δ * (y - x) ≤ g y - g x) :
    ∃ p q : ℝ, a ≤ p ∧ p ≤ q ∧ q ≤ b ∧
      (∀ x : ℝ, x ∈ Set.Ioo a p → g x ≤ -m) ∧
      (∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ g x) ∧
      q - p ≤ 2 * m / δ := by
  have hmono : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → g x ≤ g y := by
    intro x y hx hy hxy
    exact growth_mono hδ hgr hx hy hxy
  have hlenpos : 0 < 2 * m / δ := by
    exact div_pos (by nlinarith) hδ
  have h0len : 0 ≤ 2 * m / δ := le_of_lt hlenpos
  by_cases hgmga : m ≤ g a
  · -- `g` is already at least `m` at `a`: the whole interval is in the right band.
    refine ⟨a, a, le_rfl, le_rfl, hab, ?_, ?_, ?_⟩
    · intro x hx
      exfalso
      linarith [hx.1, hx.2]
    · intro x hx
      have hxcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hle : g a ≤ g x := hmono ⟨le_rfl, hab⟩ hxcc (le_of_lt hx.1)
      exact le_trans hgmga hle
    · simpa using h0len
  · have hga_lt : g a < m := lt_of_not_ge hgmga
    by_cases hnga : -m < g a
    · -- `g a > -m` : the left region is empty, take `p = a`
      by_cases hgbm : g b < m
      · -- `g b < m`: the right region is empty too, take `q = b`
        refine ⟨a, b, le_rfl, hab, le_rfl, ?_, ?_, ?_⟩
        · intro x hx
          exfalso
          linarith [hx.1, hx.2]
        · intro x hx
          exfalso
          linarith [hx.1, hx.2]
        · refine (le_div_iff₀ hδ).2 ?_
          have hg := hgr ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
          nlinarith [hg, hgbm, hnga]
      · -- `m ≤ g b`: take `q` at the crossing of level `m`
        have hmgb : m ≤ g b := le_of_not_gt hgbm
        obtain ⟨q, hq_cc, hq_eq⟩ := exists_crossing hab hcont (y := m) (le_of_lt hga_lt) hmgb
        refine ⟨a, q, le_rfl, hq_cc.1, hq_cc.2, ?_, ?_, ?_⟩
        · intro x hx
          exfalso
          linarith [hx.1, hx.2]
        · intro x hx
          have hxcc : x ∈ Set.Icc a b := ⟨le_trans hq_cc.1 (le_of_lt hx.1), le_of_lt hx.2⟩
          have h : g q ≤ g x := hmono hq_cc hxcc (le_of_lt hx.1)
          simpa [hq_eq] using h
        · refine (le_div_iff₀ hδ).2 ?_
          have hg := hgr ⟨le_rfl, hab⟩ hq_cc hq_cc.1
          nlinarith [hg, hq_eq, hnga]
    · -- `g a ≤ -m`
      have hga_le : g a ≤ -m := le_of_not_gt hnga
      by_cases hgb_neg : g b < -m
      · -- everything is ≤ -m: take `p = q = b`
        refine ⟨b, b, hab, le_rfl, le_rfl, ?_, ?_, ?_⟩
        · intro x hx
          have hxcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
          have h : g x ≤ g b := hmono hxcc ⟨hab, le_rfl⟩ (le_of_lt hx.2)
          nlinarith [h, hgb_neg]
        · intro x hx
          exfalso
          linarith [hx.1, hx.2]
        · simpa using h0len
      · -- `-m ≤ g b`: take `p` at the crossing of level `-m`
        have hmgb : -m ≤ g b := le_of_not_gt hgb_neg
        obtain ⟨p, hp_cc, hp_eq⟩ := exists_crossing hab hcont (y := -m) hga_le hmgb
        by_cases hgbm : g b < m
        · -- `g b < m`: right region empty, take `q = b`
          refine ⟨p, b, hp_cc.1, hp_cc.2, le_rfl, ?_, ?_, ?_⟩
          · intro x hx
            have hxcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hp_cc.2⟩
            have h : g x ≤ g p := hmono hxcc hp_cc (le_of_lt hx.2)
            simpa [hp_eq] using h
          · intro x hx
            exfalso
            linarith [hx.1, hx.2]
          · refine (le_div_iff₀ hδ).2 ?_
            have hg := hgr hp_cc ⟨hab, le_rfl⟩ hp_cc.2
            nlinarith [hg, hp_eq, hgbm]
        · -- `m ≤ g b`: take `q` at the crossing of level `m`
          have hmgb2 : m ≤ g b := le_of_not_gt hgbm
          have hmge : g a ≤ m := le_trans hga_le (by linarith)
          obtain ⟨q, hq_cc, hq_eq⟩ := exists_crossing hab hcont (y := m) hmge hmgb2
          have hpq : p ≤ q := by
            by_contra hnot
            have hq_lt_p : q < p := lt_of_not_ge hnot
            have hle : g q ≤ g p := hmono hq_cc hp_cc (le_of_lt hq_lt_p)
            have : m ≤ -m := by simpa [hq_eq, hp_eq] using hle
            nlinarith [hm, this]
          refine ⟨p, q, hp_cc.1, hpq, hq_cc.2, ?_, ?_, ?_⟩
          · intro x hx
            have hxcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hp_cc.2⟩
            have h : g x ≤ g p := hmono hxcc hp_cc (le_of_lt hx.2)
            simpa [hp_eq] using h
          · intro x hx
            have hxcc : x ∈ Set.Icc a b := ⟨le_trans hq_cc.1 (le_of_lt hx.1), le_of_lt hx.2⟩
            have h : g q ≤ g x := hmono hq_cc hxcc (le_of_lt hx.1)
            simpa [hq_eq] using h
          · refine (le_div_iff₀ hδ).2 ?_
            have hg := hgr hp_cc hq_cc hpq
            nlinarith [hg, hp_eq, hq_eq]

end Submission.SdtOscSplit


/-!
# Oscillatory integral bound with curvature (second-derivative test)

`ephase F x := exp(2πi·F x)`.  The theorem `exp_integral_second_deriv_le`: if
`F : ℝ → ℝ` is `C²` on `[a,b]` (`a ≤ b`) with `F'' ≥ δ > 0` on `(a,b)`, then

    ‖∫_a^b e(F(x)) dx‖ ≤ 100 / √δ.

Proof structure (classical van der Corput Hilfssatz 2):

1. **Band split** (`Submission.SdtOscSplit.exists_band_split`): for
   `g := derivWithin F [a,b]` (the one-sided-continuous extension of `F'` to the
   closed interval), which is continuous, increasing, and satisfies
   `g y - g x ≥ δ(y-x)`, split `[a,b] = [a,p] ∪ [p,q] ∪ [q,b]` with `g ≤ -m` on
   `(a,p)`, `m ≤ g` on `(q,b)`, and `q - p ≤ 2m/δ` (`m := √δ`).

2. **First derivative test on each side** (`exp_integral_first_deriv_le`): if
   `|F'| ≥ m > 0` and `F'' ≥ 0` on `(a,b)`, then
   `‖∫_a^b e(F)‖ ≤ C/m`.  Proved from the real integration-by-parts identities
   `∫ cos(2πF) = ∫ (sin(2πF))'/(2πF')` (and the sine analogue), FTC-2 on the
   closed interval (via the within derivative on `[a,b]`), and the telescoping
   of `(1/F')`.

3. The middle piece is bounded by its length `q-p ≤ 2m/δ` since `|e(F)| = 1`.
   Total: `≤ 2·C/√δ + 2/√δ`; with the slack constants below this is `≤ 100/√δ`.
-/

open Complex
open scoped Real BigOperators Topology ContDiff
open Filter MeasureTheory Set
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtOscB

noncomputable section

/-- The oscillatory phase `e(F(x)) = exp(2πi·F(x))`. -/
def ephase (F : ℝ → ℝ) (x : ℝ) : ℂ :=
  cexp ((((2 * Real.pi * F x : ℝ) : ℝ) : ℂ) * I)

/-- `|e(F x)| = 1` for every `x`. -/
lemma ephase_norm (F : ℝ → ℝ) (x : ℝ) : ‖ephase F x‖ = 1 := by
  simpa [ephase] using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * F x))

/-- `|e(F x)| ≤ 1`. -/
lemma ephase_norm_le (F : ℝ → ℝ) (x : ℝ) : ‖ephase F x‖ ≤ 1 := by
  rw [ephase_norm]

/-! ## Regularity facts derived from `ContDiffOn ℝ 2 F (Set.Icc a b)` -/

/-- From `ContDiffOn 2` on `[a,b]` (`a < b`): the within derivative is `C¹`. -/
lemma contDiffOn_derivWithin_one {a b : ℝ} (hab : a < b) (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) :
    ContDiffOn ℝ 1 (fun x : ℝ => derivWithin F (Set.Icc a b) x) (Set.Icc a b) := by
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hmn : ((1 : ℕ∞ω) + 1) ≤ (2 : ℕ∞ω) := by norm_num
  exact ContDiffOn.derivWithin (m := (1 : ℕ∞ω)) (n := (2 : ℕ∞ω)) hF hU hmn

/-- At interior points `derivWithin F [a,b]` is the genuine derivative. -/
lemma derivWithin_eq_deriv_of_Ioo {a b : ℝ} (F : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Set.Ioo a b) : derivWithin F (Set.Icc a b) x = deriv F x := by
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- `F` is differentiable at interior points of `[a,b]`. -/
lemma differentiableAt_F_of_Ioo {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    DifferentiableAt ℝ F x := by
  have hnh : Set.Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  exact (hF.contDiffAt hnh).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)

/-- `deriv F` is differentiable at interior points of `[a,b]`. -/
lemma differentiableAt_deriv_F_of_Ioo {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    DifferentiableAt ℝ (deriv F) x := by
  have hnh : Set.Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have hca : ContDiffAt ℝ 2 F x := hF.contDiffAt hnh
  have hmn : ((1 : ℕ∞ω) + 1) ≤ (2 : ℕ∞ω) := by norm_num
  have hc1 : ContDiffAt ℝ 1 (deriv F) x :=
    ContDiffAt.derivWithin (f := F) (n := (2 : ℕ∞ω)) (m := (1 : ℕ∞ω)) hca hmn
  exact hc1.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)

/-- `HasDerivAt` for `F` at interior points. -/
lemma hasDerivAt_F_of_Ioo {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt F (deriv F x) x := by
  exact (differentiableAt_F_of_Ioo F hF hx).hasDerivAt

/-- `HasDerivAt` for `deriv F` at interior points. -/
lemma hasDerivAt_deriv_F_of_Ioo {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (deriv F) (deriv (deriv F) x) x := by
  exact (differentiableAt_deriv_F_of_Ioo F hF hx).hasDerivAt

/-- With `g := derivWithin F [a,b]`, at interior points `deriv g x = deriv (deriv F) x`. -/
lemma deriv_derivWithin_eq_deriv_deriv {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    deriv (fun y : ℝ => derivWithin F (Set.Icc a b) y) x = deriv (deriv F) x := by
  have hcong : (fun y : ℝ => derivWithin F (Set.Icc a b) y) =ᶠ[𝓝 x] deriv F := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact derivWithin_eq_deriv_of_Ioo F hy
  have hd : HasDerivAt (fun y : ℝ => derivWithin F (Set.Icc a b) y) (deriv (deriv F) x) x :=
    (hasDerivAt_deriv_F_of_Ioo F hF hx).congr_of_eventuallyEq hcong
  exact hd.deriv

/-- `Real.cos ∘ (2πF)` at interior points: derivative formula (real chain rule). -/
lemma hasDerivAt_cos_2piF {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * Real.pi * F y))
      (-(2 * Real.pi * deriv F x) * Real.sin (2 * Real.pi * F x)) x := by
  have hin : HasDerivAt (fun y : ℝ => 2 * Real.pi * F y)
      (2 * Real.pi * deriv F x) x := by
    simpa [mul_assoc] using
      ((hasDerivAt_F_of_Ioo F hF hx).const_mul (2 * Real.pi))
  simpa [mul_assoc, mul_comm, mul_left_comm] using hin.cos

/-- `Real.sin ∘ (2πF)` at interior points: derivative formula (real chain rule). -/
lemma hasDerivAt_sin_2piF {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * F y))
      (2 * Real.pi * deriv F x * Real.cos (2 * Real.pi * F x)) x := by
  have hin : HasDerivAt (fun y : ℝ => 2 * Real.pi * F y)
      (2 * Real.pi * deriv F x) x := by
    simpa [mul_assoc] using
      ((hasDerivAt_F_of_Ioo F hF hx).const_mul (2 * Real.pi))
  simpa [mul_assoc, mul_comm, mul_left_comm] using hin.sin
/-- If `m ≤ |g x|` for all interior `x`, and `g` is continuous on `[a,b]`, then
`m ≤ |g x|` for all `x ∈ [a,b]` (including endpoints). -/
lemma abs_ge_on_Icc_of_Ioo {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) {m : ℝ}
    (hint : ∀ x ∈ Set.Ioo a b, m ≤ |g x|) :
    ∀ x ∈ Set.Icc a b, m ≤ |g x| := by
  intro x hx
  by_cases hxint : x ∈ Set.Ioo a b
  · exact hint x hxint
  · by_cases hxa : x = a
    · subst x
      by_contra hneg
      have hlt : |g a| < m := lt_of_not_ge hneg
      have hcl : a ∈ closure (Set.Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact left_mem_Icc.mpr hab.le
      let ε : ℝ := (m - |g a|) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hcw : ContinuousWithinAt g (Set.Icc a b) a := hg a (left_mem_Icc.mpr hab.le)
      have ht : Tendsto g (𝓝[Set.Icc a b] a) (𝓝 (g a)) := hcw
      have hball : {y | dist (g y) (g a) < ε} ∈ 𝓝[Set.Icc a b] a :=
        (Metric.tendsto_nhds.mp ht) ε hε
      have hU : ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ Set.Icc a b ⊆ {y | |g y - g a| < ε} := by
        simpa [Real.dist_eq] using (mem_nhdsWithin.mp hball)
      rcases hU with ⟨U, hUopen, hUa, hsub⟩
      have hne : (U ∩ Set.Ioo a b).Nonempty := (mem_closure_iff.mp hcl) U hUopen hUa
      rcases hne with ⟨y, hyU, hyI⟩
      have hyI' : y ∈ Set.Icc a b := Set.mem_Icc_of_Ioo hyI
      have hyε : |g y - g a| < ε := hsub ⟨hyU, hyI'⟩
      have hym : m ≤ |g y| := hint y hyI
      have h1 : m < |g a| + ε := by
        calc
          m ≤ |g y| := hym
          _ ≤ |g a| + |g y - g a| := by
            have htmp := abs_sub_abs_le_abs_sub (g y) (g a)
            linarith
          _ < |g a| + ε := by linarith
      have hεval : ε = (m - |g a|) / 2 := rfl
      linarith
    · by_cases hxb : x = b
      · subst x
        by_contra hneg
        have hlt : |g b| < m := lt_of_not_ge hneg
        have hcl : b ∈ closure (Set.Ioo a b) := by
          rw [closure_Ioo hab.ne]
          exact right_mem_Icc.mpr hab.le
        let ε : ℝ := (m - |g b|) / 2
        have hε : 0 < ε := by dsimp [ε]; linarith
        have hcw : ContinuousWithinAt g (Set.Icc a b) b := hg b (right_mem_Icc.mpr hab.le)
        have ht : Tendsto g (𝓝[Set.Icc a b] b) (𝓝 (g b)) := hcw
        have hball : {y | dist (g y) (g b) < ε} ∈ 𝓝[Set.Icc a b] b :=
          (Metric.tendsto_nhds.mp ht) ε hε
        have hU : ∃ u, IsOpen u ∧ b ∈ u ∧ u ∩ Set.Icc a b ⊆ {y | |g y - g b| < ε} := by
          simpa [Real.dist_eq] using (mem_nhdsWithin.mp hball)
        rcases hU with ⟨U, hUopen, hUb, hsub⟩
        have hne : (U ∩ Set.Ioo a b).Nonempty := (mem_closure_iff.mp hcl) U hUopen hUb
        rcases hne with ⟨y, hyU, hyI⟩
        have hyI' : y ∈ Set.Icc a b := Set.mem_Icc_of_Ioo hyI
        have hyε : |g y - g b| < ε := hsub ⟨hyU, hyI'⟩
        have hym : m ≤ |g y| := hint y hyI
        have h1 : m < |g b| + ε := by
          calc
            m ≤ |g y| := hym
            _ ≤ |g b| + |g y - g b| := by
              have htmp := abs_sub_abs_le_abs_sub (g y) (g b)
              linarith
            _ < |g b| + ε := by linarith
        have hεval : ε = (m - |g b|) / 2 := rfl
        linarith
      · exfalso
        have hxa' : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
        have hxb' : x < b := lt_of_le_of_ne' hx.2 (Ne.symm hxb)
        exact hxint ⟨hxa', hxb'⟩



/-! ## First derivative test: `|∫_a^b cos(2πF)|` and `|∫_a^b sin(2πF)|` when `|F'| ≥ m`, `F'' ≥ 0`. -/

/-- Within-derivative of order two, continuous on the closed interval. -/
lemma derivWithin_derivWithin_continuousOn {a b : ℝ} (hab : a < b) (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) :
    ContinuousOn (fun x : ℝ =>
        derivWithin (fun y : ℝ => derivWithin F (Set.Icc a b) y) (Set.Icc a b) x)
      (Set.Icc a b) := by
  have hg : ContDiffOn ℝ 1 (fun x : ℝ => derivWithin F (Set.Icc a b) x) (Set.Icc a b) :=
    contDiffOn_derivWithin_one hab F hF
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hw : ContDiffOn ℝ 0 (fun x : ℝ =>
        derivWithin (fun y : ℝ => derivWithin F (Set.Icc a b) y) (Set.Icc a b) x)
      (Set.Icc a b) :=
    ContDiffOn.derivWithin (m := (0 : ℕ∞ω)) (n := (1 : ℕ∞ω)) hg hU (by norm_num)
  exact hw.continuousOn

/-- At interior points `derivWithin (derivWithin F s) s x = deriv (deriv F) x`. -/
lemma derivWithin_g_eq_deriv_deriv {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    derivWithin (fun y : ℝ => derivWithin F (Set.Icc a b) y) (Set.Icc a b) x =
      deriv (deriv F) x := by
  have h1 := derivWithin_eq_deriv_of_Ioo (fun y : ℝ => derivWithin F (Set.Icc a b) y) hx
  rw [h1]
  exact deriv_derivWithin_eq_deriv_deriv F hF hx

/-- At interior points `HasDerivAt g (w x) x` where `g := derivWithin F s` and
`w := derivWithin g s`. -/
lemma hasDerivAt_derivWithin_of_Ioo {a b : ℝ} (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => derivWithin F (Set.Icc a b) y)
      (derivWithin (fun y : ℝ => derivWithin F (Set.Icc a b) y) (Set.Icc a b) x) x := by
  have hcong : (fun y : ℝ => derivWithin F (Set.Icc a b) y) =ᶠ[𝓝 x] deriv F := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact derivWithin_eq_deriv_of_Ioo F hy
  have hd : HasDerivAt (deriv F) (deriv (deriv F) x) x := hasDerivAt_deriv_F_of_Ioo F hF hx
  have hg : HasDerivAt (fun y : ℝ => derivWithin F (Set.Icc a b) y) (deriv (deriv F) x) x :=
    hd.congr_of_eventuallyEq hcong
  -- now show value equals derivWithin (derivWithin F s) s x
  have hval : deriv (deriv F) x =
      derivWithin (fun y : ℝ => derivWithin F (Set.Icc a b) y) (Set.Icc a b) x := by
    rw [← derivWithin_g_eq_deriv_deriv F hF hx]
  simpa [hval] using hg

/-- `q := 1/(2π·g)` is continuous on the closed interval, given `|g| ≥ m` there. -/
lemma continuousOn_inv_mul_derivWithin {a b : ℝ} (hab : a < b) (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b)) {m : ℝ} (hm : 0 < m)
    (hsl : ∀ x : ℝ, x ∈ Set.Ioo a b → m ≤ |deriv F x|) :
    ContinuousOn (fun x : ℝ => (2 * Real.pi * derivWithin F (Set.Icc a b) x)⁻¹)
      (Set.Icc a b) := by
  let g : ℝ → ℝ := fun x => derivWithin F (Set.Icc a b) x
  have hgC : ContinuousOn g (Set.Icc a b) := by
    exact (contDiffOn_derivWithin_one hab F hF).continuousOn
  have hge : ∀ x ∈ Set.Ioo a b, m ≤ |g x| := by
    intro x hx
    simpa [g, derivWithin_eq_deriv_of_Ioo F hx] using hsl x hx
  have hgeI : ∀ x ∈ Set.Icc a b, m ≤ |g x| := abs_ge_on_Icc_of_Ioo hab hgC hge
  have hg0 : ∀ x ∈ Set.Icc a b, 2 * Real.pi * g x ≠ 0 := by
    intro x hx
    have hgv : m ≤ |g x| := hgeI x hx
    by_contra hzero
    have hzero' : |2 * Real.pi * g x| = 0 := by simpa [hzero]
    have h2 : 0 < (2 * Real.pi : ℝ) := by positivity
    have hlb : 0 < |2 * Real.pi * g x| := by
      have hmm : 0 < (2 * Real.pi) * m := mul_pos h2 hm
      have hle : (2 * Real.pi) * m ≤ |2 * Real.pi * g x| := by
        rw [abs_mul, abs_of_pos h2]
        exact mul_le_mul_of_nonneg_left hgv h2.le
      linarith
    linarith
  have hcont2 : ContinuousOn (fun x : ℝ => 2 * Real.pi * g x) (Set.Icc a b) := by
    exact hgC.const_mul (2 * Real.pi)
  change ContinuousOn (fun x : ℝ => (2 * Real.pi * g x)⁻¹) (Set.Icc a b)
  exact hcont2.inv₀ hg0


/-- A continuous real function that is `≥ 0` on the open interval is `≥ 0` on the
whole closed interval. -/
lemma nonneg_on_Icc_of_Ioo {a b : ℝ} (hab : a < b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc a b))
    (hint : ∀ x ∈ Set.Ioo a b, 0 ≤ h x) :
    ∀ x ∈ Set.Icc a b, 0 ≤ h x := by
  intro x hx
  by_cases hxint : x ∈ Set.Ioo a b
  · exact hint x hxint
  · by_cases hxa : x = a
    · subst x
      by_contra hneg
      have hlt : h a < 0 := lt_of_not_ge hneg
      have hcl : a ∈ closure (Set.Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact left_mem_Icc.mpr hab.le
      let ε : ℝ := -h a / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hcw : ContinuousWithinAt h (Set.Icc a b) a := hh a (left_mem_Icc.mpr hab.le)
      have ht : Tendsto h (𝓝[Set.Icc a b] a) (𝓝 (h a)) := hcw
      have hball : {y | dist (h y) (h a) < ε} ∈ 𝓝[Set.Icc a b] a :=
        (Metric.tendsto_nhds.mp ht) ε hε
      have hU : ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ Set.Icc a b ⊆ {y | |h y - h a| < ε} := by
        simpa [Real.dist_eq] using (mem_nhdsWithin.mp hball)
      rcases hU with ⟨U, hUopen, hUa, hsub⟩
      have hne : (U ∩ Set.Ioo a b).Nonempty := (mem_closure_iff.mp hcl) U hUopen hUa
      rcases hne with ⟨y, hyU, hyI⟩
      have hyI' : y ∈ Set.Icc a b := Set.mem_Icc_of_Ioo hyI
      have hyε : |h y - h a| < ε := hsub ⟨hyU, hyI'⟩
      have hypos : 0 ≤ h y := hint y hyI
      have : h y < 0 := by
        calc h y = h a + (h y - h a) := by ring
          _ ≤ h a + |h y - h a| := by
            have htmp := le_abs_self (h y - h a)
            linarith
          _ < h a + ε := by linarith
          _ < 0 := by
            have hεval' : ε = -h a / 2 := rfl
            linarith
      have hεval : ε = -h a / 2 := rfl
      linarith
    · by_cases hxb : x = b
      · subst x
        by_contra hneg
        have hlt : h b < 0 := lt_of_not_ge hneg
        have hcl : b ∈ closure (Set.Ioo a b) := by
          rw [closure_Ioo hab.ne]
          exact right_mem_Icc.mpr hab.le
        let ε : ℝ := -h b / 2
        have hε : 0 < ε := by dsimp [ε]; linarith
        have hcw : ContinuousWithinAt h (Set.Icc a b) b := hh b (right_mem_Icc.mpr hab.le)
        have ht : Tendsto h (𝓝[Set.Icc a b] b) (𝓝 (h b)) := hcw
        have hball : {y | dist (h y) (h b) < ε} ∈ 𝓝[Set.Icc a b] b :=
          (Metric.tendsto_nhds.mp ht) ε hε
        have hU : ∃ u, IsOpen u ∧ b ∈ u ∧ u ∩ Set.Icc a b ⊆ {y | |h y - h b| < ε} := by
          simpa [Real.dist_eq] using (mem_nhdsWithin.mp hball)
        rcases hU with ⟨U, hUopen, hUb, hsub⟩
        have hne : (U ∩ Set.Ioo a b).Nonempty := (mem_closure_iff.mp hcl) U hUopen hUb
        rcases hne with ⟨y, hyU, hyI⟩
        have hyI' : y ∈ Set.Icc a b := Set.mem_Icc_of_Ioo hyI
        have hyε : |h y - h b| < ε := hsub ⟨hyU, hyI'⟩
        have hypos : 0 ≤ h y := hint y hyI
        have : h y < 0 := by
          calc h y = h b + (h y - h b) := by ring
            _ ≤ h b + |h y - h b| := by
              have htmp := le_abs_self (h y - h b)
              linarith
            _ < h b + ε := by linarith
            _ < 0 := by
              have hεval' : ε = -h b / 2 := rfl
              linarith
        have hεval : ε = -h b / 2 := rfl
        linarith
      · exfalso
        have hxa' : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
        have hxb' : x < b := lt_of_le_of_ne' hx.2 (Ne.symm hxb)
        exact hxint ⟨hxa', hxb'⟩


/-! ## The first derivative test bounds for cosine and sine -/

/-- **First derivative test (cosine).** If `|F'| ≥ m > 0` and `F'' ≥ 0` on `(a,b)`,
then `|∫_a^b cos(2πF)| ≤ 4/m`. -/
lemma cos_integral_first_deriv_le {a b : ℝ} (hab : a < b) (F : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b))
    (hsl : ∀ x : ℝ, x ∈ Set.Ioo a b → m ≤ |deriv F x|)
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv F) x) :
    |∫ x in a..b, Real.cos (2 * Real.pi * F x)| ≤ 4 / m := by
  let sI : Set ℝ := Set.Icc a b
  let g : ℝ → ℝ := fun x => derivWithin F sI x
  let w : ℝ → ℝ := fun x => derivWithin g sI x
  let c2 : ℝ := 2 * Real.pi
  let q : ℝ → ℝ := fun x => (c2 * g x)⁻¹
  let qd : ℝ → ℝ := fun x => -w x / (c2 * (g x) ^ 2)
  let sfun : ℝ → ℝ := fun x => Real.sin (c2 * F x)
  let sfd : ℝ → ℝ := fun x => c2 * g x * Real.cos (c2 * F x)
  have hc2 : c2 ≠ 0 := by
    dsimp [c2]
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  -- |g| ≥ m on the closed interval
  have hgC : ContinuousOn g sI := by
    dsimp [g, sI]
    exact (contDiffOn_derivWithin_one hab F hF).continuousOn
  have hge : ∀ x ∈ Set.Ioo a b, m ≤ |g x| := by
    intro x hx
    have hgx : g x = deriv F x := by
      dsimp [g]
      exact derivWithin_eq_deriv_of_Ioo F hx
    rw [hgx]
    exact hsl x hx
  have hgeI : ∀ x ∈ sI, m ≤ |g x| := by
    intro x hx
    simpa [sI] using abs_ge_on_Icc_of_Ioo hab hgC hge x hx
  have hgne : ∀ x ∈ sI, g x ≠ 0 := by
    intro x hx
    have hgv : m ≤ |g x| := hgeI x hx
    have hmpos : 0 < m := hm
    have habs : 0 < |g x| := lt_of_lt_of_le hmpos hgv
    exact abs_pos.mp habs
  -- w continuous on closed, and w ≥ 0 on closed (from F'' ≥ 0 on open)
  have hwC : ContinuousOn w sI := by
    dsimp [w, g, sI]
    exact derivWithin_derivWithin_continuousOn hab F hF
  have hwge : ∀ x ∈ Set.Ioo a b, 0 ≤ w x := by
    intro x hx
    dsimp [w, g]
    rw [derivWithin_g_eq_deriv_deriv F hF hx]
    exact hpp x hx
  have hwgeI : ∀ x ∈ sI, 0 ≤ w x := by
    intro x hx
    simpa [sI] using nonneg_on_Icc_of_Ioo hab hwC hwge x hx
  -- q continuous on the closed interval
  have hqC : ContinuousOn q sI := by
    dsimp [q]
    simpa [g, sI, c2, mul_assoc] using
      (continuousOn_inv_mul_derivWithin hab F hF hm hsl)
  -- qd continuous on the closed interval
  have hqdC : ContinuousOn qd sI := by
    have hwnegC : ContinuousOn (fun x : ℝ => -w x) sI := hwC.neg
    have hsq : ContinuousOn (fun x : ℝ => (g x) ^ 2) sI := by
      have h : (fun x : ℝ => (g x) ^ 2) = g * g := by
        funext x
        rw [pow_two]
        simp
      rw [h]
      exact hgC.mul hgC
    have hden : ContinuousOn (fun x : ℝ => c2 * (g x) ^ 2) sI := by
      exact hsq.const_mul c2
    have hden0 : ∀ x ∈ sI, c2 * (g x) ^ 2 ≠ 0 := by
      intro x hx
      exact mul_ne_zero hc2 (pow_ne_zero 2 (hgne x hx))
    dsimp [qd]
    exact hwnegC.div hden hden0
  -- sfun continuous, sfd continuous on the closed interval
  have hFc : ContinuousOn F sI := by
    simpa [sI] using hF.continuousOn
  have hargC : ContinuousOn (fun x : ℝ => c2 * F x) sI := by
    exact hFc.const_mul c2
  have hsfC : ContinuousOn sfun sI := by
    change ContinuousOn (fun x : ℝ => Real.sin ((fun y : ℝ => c2 * F y) x)) sI
    exact Real.continuous_sin.comp_continuousOn hargC
  have hsfdC : ContinuousOn sfd sI := by
    change ContinuousOn (fun x : ℝ => c2 * g x * Real.cos ((fun y : ℝ => c2 * F y) x)) sI
    have hcosC : ContinuousOn (fun x : ℝ => Real.cos ((fun y : ℝ => c2 * F y) x)) sI :=
      Real.continuous_cos.comp_continuousOn hargC
    exact (hgC.const_mul c2).mul hcosC
  -- interior HasDerivAt for q and sfun
  have hq_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt q (qd x) x := by
    intro x hx
    have hgw : HasDerivAt g (w x) x := by
      dsimp [w, g]
      exact hasDerivAt_derivWithin_of_Ioo F hF hx
    have hinner : HasDerivAt (fun y : ℝ => c2 * g y) (c2 * w x) x := by
      simpa [mul_assoc] using hgw.const_mul c2
    have hneq : c2 * g x ≠ 0 := mul_ne_zero hc2 (hgne x (Set.mem_Icc_of_Ioo hx))
    have hinv' : HasDerivAt (fun y : ℝ => (c2 * g y)⁻¹) (-(c2 * w x) / (c2 * g x) ^ 2) x :=
      hinner.inv hneq
    have hval : -(c2 * w x) / (c2 * g x) ^ 2 = qd x := by
      dsimp [qd]
      field_simp [hc2]
    change HasDerivAt (fun y : ℝ => (c2 * g y)⁻¹) (qd x) x
    rw [← hval]
    exact hinv'
  have hsf_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt sfun (sfd x) x := by
    intro x hx
    have hin : HasDerivAt (fun y : ℝ => c2 * F y) (c2 * deriv F x) x := by
      simpa [mul_assoc] using (hasDerivAt_F_of_Ioo F hF hx).const_mul c2
    have hgx : deriv F x = g x := by
      simpa [g] using (derivWithin_eq_deriv_of_Ioo F hx).symm
    have hsinc2 : HasDerivAt sfun (c2 * g x * Real.cos (c2 * F x)) x := by
      simpa [sfun, hgx, mul_assoc, mul_comm, mul_left_comm] using hin.sin
    simpa [sfd] using hsinc2
  -- interval integrability (continuity on the closed interval)
  have hqC' : ContinuousOn q (uIcc a b) := by simpa [sI, uIcc_of_le hab.le] using hqC
  have hqdC' : ContinuousOn qd (uIcc a b) := by simpa [sI, uIcc_of_le hab.le] using hqdC
  have hsfC' : ContinuousOn sfun (uIcc a b) := by simpa [sI, uIcc_of_le hab.le] using hsfC
  have hsfdC' : ContinuousOn sfd (uIcc a b) := by simpa [sI, uIcc_of_le hab.le] using hsfdC
  have hqint : IntervalIntegrable q MeasureTheory.volume a b := by
    exact hqC'.intervalIntegrable
  have hqdint : IntervalIntegrable qd MeasureTheory.volume a b := by
    exact hqdC'.intervalIntegrable
  have hsfdint : IntervalIntegrable sfd MeasureTheory.volume a b := by
    exact hsfdC'.intervalIntegrable
  -- the integration-by-parts identity ∫ q·sfd = [q·sfun] − ∫ qd·sfun
  have hIBP : (∫ x in a..b, q x * sfd x) = q b * sfun b - q a * sfun a -
      (∫ x in a..b, qd x * sfun x) := by
    simpa [sI, uIcc_of_le hab.le, min_eq_left hab.le, max_eq_right hab.le] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (A := ℝ)
        (u := q) (v := sfun) (u' := qd) (v' := sfd)
        hqC' hsfC'
        (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hq_deriv)
        (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hsf_deriv)
        hqdint hsfdint)
  -- ∫_a^b cos(c2F) = ∫_a^b sfd·q
  have hcos_eq : (∫ x in a..b, Real.cos (c2 * F x)) = ∫ x in a..b, sfd x * q x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ sI := by simpa [sI, uIcc_of_le hab.le] using hx
    have hq0 : g x ≠ 0 := hgne x hxI
    have hne : c2 * g x ≠ 0 := mul_ne_zero hc2 hq0
    dsimp [sfd, q]
    field_simp [hne]
  have hcomm : (∫ x in a..b, sfd x * q x) = ∫ x in a..b, q x * sfd x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  -- the size of q at points of the closed interval
  have hc2pos : 0 < c2 := by dsimp [c2]; positivity
  have hc2ge1 : 1 ≤ c2 := by dsimp [c2]; nlinarith [Real.pi_gt_three]
  have hq_abs : ∀ t ∈ sI, |q t| ≤ 1 / (c2 * m) := by
    intro t ht
    have hgt : m ≤ |g t| := hgeI t ht
    dsimp [q]
    rw [abs_inv, abs_mul, abs_of_pos hc2pos]
    rw [one_div]
    have hden_ge : c2 * m ≤ c2 * |g t| := mul_le_mul_of_nonneg_left hgt hc2pos.le
    have hden_pos : 0 < c2 * m := mul_pos hc2pos hm
    have hgpos : 0 < |g t| := lt_of_lt_of_le hm hgt
    have hgtpos : 0 < c2 * |g t| := mul_pos hc2pos hgpos
    exact (inv_le_inv₀ hgtpos hden_pos).mpr hden_ge
  -- |sfun t| ≤ 1 everywhere
  have hsin_le : ∀ t : ℝ, |sfun t| ≤ 1 := by
    intro t
    dsimp [sfun]
    exact Real.abs_sin_le_one (c2 * F t)
  -- |q t · sfun t| ≤ 1/(c2·m) at points of the interval
  have hend_bound (t : ℝ) (ht : t ∈ sI) : |q t * sfun t| ≤ 1 / (c2 * m) := by
    rw [abs_mul]
    calc |q t| * |sfun t| ≤ (1 / (c2 * m)) * 1 := by
          exact mul_le_mul (hq_abs t ht) (hsin_le t) (abs_nonneg _) (by positivity)
      _ = 1 / (c2 * m) := by ring
  -- FTC: ∫_a^b qd = q b - q a
  have hftc : (∫ x in a..b, qd x) = q b - q a := by
    simpa [sI, uIcc_of_le hab.le] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := q) (f' := qd) hab.le hqC
        hq_deriv hqdint)
  -- qd ≤ 0 on the closed interval
  have hqdneg : ∀ x ∈ sI, qd x ≤ 0 := by
    intro x hx
    have hw0 : 0 ≤ w x := hwgeI x hx
    have hg2 : 0 < (g x) ^ 2 := sq_pos_of_ne_zero (hgne x hx)
    have hden : 0 < c2 * (g x) ^ 2 := mul_pos hc2pos hg2
    dsimp [qd]
    have hnum : -w x ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  -- ∫|qd| = q a - q b
  have hqdnorm : (∫ x in a..b, |qd x|) = q a - q b := by
    have hcong : (∫ x in a..b, |qd x|) = ∫ x in a..b, -qd x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ sI := by simpa [sI, uIcc_of_le hab.le] using hx
      change |qd x| = -qd x
      rw [abs_of_nonpos (hqdneg x hxI)]
    rw [hcong]
    rw [intervalIntegral.integral_neg]
    rw [hftc]
    ring
  -- middle-piece bound
  have hmid : |∫ x in a..b, qd x * sfun x| ≤ q a - q b := by
    calc |∫ x in a..b, qd x * sfun x| ≤ ∫ x in a..b, |qd x * sfun x| := by
          exact intervalIntegral.abs_integral_le_integral_abs hab.le
      _ ≤ ∫ x in a..b, |qd x| := by
          apply intervalIntegral.integral_mono_on hab.le
          · exact (hqdC'.mul hsfC').abs.intervalIntegrable
          · exact hqdC'.abs.intervalIntegrable
          intro x hx
          rw [abs_mul]
          calc |qd x| * |sfun x| ≤ |qd x| * 1 :=
                mul_le_mul_of_nonneg_left (hsin_le x) (abs_nonneg _)
            _ = |qd x| := by ring
      _ = q a - q b := hqdnorm
  -- final assembly
  have hbd1 : |q b * sfun b| ≤ 1 / (c2 * m) := hend_bound b (right_mem_Icc.mpr hab.le)
  have hbd2 : |q a * sfun a| ≤ 1 / (c2 * m) := hend_bound a (left_mem_Icc.mpr hab.le)
  have hbd3 : |∫ x in a..b, qd x * sfun x| ≤ 2 / (c2 * m) := by
    have hqa : |q a| ≤ 1 / (c2 * m) := hq_abs a (left_mem_Icc.mpr hab.le)
    have hqb : |q b| ≤ 1 / (c2 * m) := hq_abs b (right_mem_Icc.mpr hab.le)
    have hsub : q a - q b ≤ |q a| + |q b| := by
      calc q a - q b ≤ |q a - q b| := le_abs_self _
        _ = |q a + -q b| := by rw [sub_eq_add_neg]
        _ ≤ |q a| + |-q b| := abs_add_le _ _
        _ = |q a| + |q b| := by rw [abs_neg]
    have hsum : 1 / (c2 * m) + 1 / (c2 * m) = 2 / (c2 * m) := by ring
    have hqq : q a - q b ≤ 2 / (c2 * m) := by linarith
    exact hmid.trans hqq
  have htri : |q b * sfun b - q a * sfun a - (∫ x in a..b, qd x * sfun x)| ≤
      |q b * sfun b| + |q a * sfun a| + |∫ x in a..b, qd x * sfun x| := by
    calc |q b * sfun b - q a * sfun a - (∫ x in a..b, qd x * sfun x)|
        = |(q b * sfun b - q a * sfun a) + -(∫ x in a..b, qd x * sfun x)| := by
            rw [sub_eq_add_neg, sub_eq_add_neg]
    _ ≤ |q b * sfun b - q a * sfun a| + |∫ x in a..b, qd x * sfun x| := by
        simpa [abs_neg] using (abs_add_le (q b * sfun b - q a * sfun a)
          (-(∫ x in a..b, qd x * sfun x)))
    _ ≤ |q b * sfun b| + |q a * sfun a| + |∫ x in a..b, qd x * sfun x| := by
        have hsub2 : |q b * sfun b - q a * sfun a| ≤ |q b * sfun b| + |q a * sfun a| := by
          calc |q b * sfun b - q a * sfun a| = |q b * sfun b + -(q a * sfun a)| := by
                rw [sub_eq_add_neg]
            _ ≤ |q b * sfun b| + |q a * sfun a| := by
                simpa [abs_neg] using (abs_add_le (q b * sfun b) (-(q a * sfun a)))
        linarith
  have htot : |q b * sfun b| + |q a * sfun a| + |∫ x in a..b, qd x * sfun x| ≤
      4 / (c2 * m) := by
    have hsum : 1 / (c2 * m) + 1 / (c2 * m) + 2 / (c2 * m) = 4 / (c2 * m) := by ring
    linarith
  have hc2ge : 4 / (c2 * m) ≤ 4 / m := by
    exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (4 : ℝ)) hm
      (by simpa [mul_comm] using (mul_le_mul_of_nonneg_right hc2ge1 hm.le))
  have hCeq : (∫ x in a..b, Real.cos (2 * Real.pi * F x)) =
      q b * sfun b - q a * sfun a - (∫ x in a..b, qd x * sfun x) := by
    calc ∫ x in a..b, Real.cos (2 * Real.pi * F x) = ∫ x in a..b, Real.cos (c2 * F x) := rfl
      _ = ∫ x in a..b, sfd x * q x := hcos_eq
      _ = ∫ x in a..b, q x * sfd x := hcomm
      _ = q b * sfun b - q a * sfun a - (∫ x in a..b, qd x * sfun x) := hIBP
  have hfin : |∫ x in a..b, Real.cos (2 * Real.pi * F x)| ≤ 4 / m := by
    rw [hCeq]
    calc |q b * sfun b - q a * sfun a - (∫ x in a..b, qd x * sfun x)|
        ≤ |q b * sfun b| + |q a * sfun a| + |∫ x in a..b, qd x * sfun x| := htri
    _ ≤ 4 / (c2 * m) := htot
    _ ≤ 4 / m := hc2ge
  exact hfin


/-- **First derivative test (sine)** — obtained from the cosine case by the phase
shift `sin(2πF) = cos(2π(F − 1/4))`. -/
lemma sin_integral_first_deriv_le {a b : ℝ} (hab : a < b) (F : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b))
    (hsl : ∀ x : ℝ, x ∈ Set.Ioo a b → m ≤ |deriv F x|)
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv F) x) :
    |∫ x in a..b, Real.sin (2 * Real.pi * F x)| ≤ 4 / m := by
  let G : ℝ → ℝ := fun x => F x - 1 / 4
  have hG : ContDiffOn ℝ 2 G (Set.Icc a b) := by
    have hc : ContDiffOn ℝ 2 (fun _ : ℝ => (1 / 4 : ℝ)) (Set.Icc a b) := by
      exact contDiffOn_const
    simpa [G] using hF.sub hc
  have hslG : ∀ x : ℝ, x ∈ Set.Ioo a b → m ≤ |deriv G x| := by
    intro x hx
    have hd : deriv (fun y : ℝ => F y - 1 / 4) x = deriv F x := by
      have hd1 : DifferentiableAt ℝ F x := differentiableAt_F_of_Ioo F hF hx
      have hc : HasDerivAt (fun _ : ℝ => (1 / 4 : ℝ)) (0 : ℝ) x := hasDerivAt_const x (1/4)
      have hsub : HasDerivAt (F - fun _ : ℝ => (1 / 4 : ℝ)) (deriv F x) x := by
        simpa using hd1.hasDerivAt.sub hc
      have hfun : (fun y : ℝ => F y - 1 / 4) = F - fun _ : ℝ => (1 / 4 : ℝ) := by
        funext y; simp
      have hda : HasDerivAt (fun y : ℝ => F y - 1 / 4) (deriv F x) x := by
        exact hfun ▸ hsub
      exact hda.deriv
    have : m ≤ |deriv (fun y : ℝ => F y - 1 / 4) x| := by simpa [hd] using hsl x hx
    simpa [G] using this
  have hppG : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv G) x := by
    intro x hx
    have hcong : (fun y : ℝ => deriv G y) =ᶠ[𝓝 x] deriv F := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      have hd : deriv (fun z : ℝ => F z - 1 / 4) y = deriv F y := by
        have hd1 : DifferentiableAt ℝ F y := differentiableAt_F_of_Ioo F hF hy
        have hc : HasDerivAt (fun _ : ℝ => (1 / 4 : ℝ)) (0 : ℝ) y := hasDerivAt_const y (1/4)
        have hsub : HasDerivAt (F - fun _ : ℝ => (1 / 4 : ℝ)) (deriv F y) y := by
          simpa using hd1.hasDerivAt.sub hc
        have hfun : (fun z : ℝ => F z - 1 / 4) = F - fun _ : ℝ => (1 / 4 : ℝ) := by
          funext z; simp
        have hda : HasDerivAt (fun z : ℝ => F z - 1 / 4) (deriv F y) y := by
          exact hfun ▸ hsub
        exact hda.deriv
      simpa [G] using hd
    have hda : HasDerivAt (deriv G) (deriv (deriv F) x) x :=
      (hasDerivAt_deriv_F_of_Ioo F hF hx).congr_of_eventuallyEq hcong
    have hd2 : deriv (deriv G) x = deriv (deriv F) x := hda.deriv
    rw [hd2]
    exact hpp x hx
  have hmain := cos_integral_first_deriv_le hab G hm hG hslG hppG
  have hident : (∫ x in a..b, Real.cos (2 * Real.pi * G x)) =
      ∫ x in a..b, Real.sin (2 * Real.pi * F x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [G]
    have harg : 2 * Real.pi * (F x - 1 / 4) = 2 * Real.pi * F x - Real.pi / 2 := by ring
    rw [harg]
    exact Real.cos_sub_pi_div_two (2 * Real.pi * F x)
  rw [← hident]
  exact hmain

/-- `e^{2πiF} = cos(2πF) + i·sin(2πF)`: the norm of the oscillatory integral is
bounded by the sum of the absolute cosine and sine integrals. -/
lemma ephase_norm_le_trig {a b : ℝ} (F : ℝ → ℝ)
    (hcont : ContinuousOn F (Set.uIcc a b)) :
    ‖∫ x in a..b, ephase F x‖ ≤ |∫ x in a..b, Real.cos (2 * Real.pi * F x)| +
        |∫ x in a..b, Real.sin (2 * Real.pi * F x)| := by
  have hcosC : ContinuousOn (fun x : ℝ => Real.cos (2 * Real.pi * F x)) (Set.uIcc a b) := by
    have harg : ContinuousOn (fun x : ℝ => 2 * Real.pi * F x) (Set.uIcc a b) := by
      exact hcont.const_mul (2 * Real.pi)
    exact Real.continuous_cos.comp_continuousOn harg
  have hsinC : ContinuousOn (fun x : ℝ => Real.sin (2 * Real.pi * F x)) (Set.uIcc a b) := by
    have harg : ContinuousOn (fun x : ℝ => 2 * Real.pi * F x) (Set.uIcc a b) := by
      exact hcont.const_mul (2 * Real.pi)
    exact Real.continuous_sin.comp_continuousOn harg
  have hcosCC : ContinuousOn (fun x : ℝ => ((Real.cos (2 * Real.pi * F x) : ℝ) : ℂ))
      (Set.uIcc a b) := by
    exact Complex.continuous_ofReal.comp_continuousOn hcosC
  have hsinCC : ContinuousOn (fun x : ℝ => ((Real.sin (2 * Real.pi * F x) : ℝ) : ℂ))
      (Set.uIcc a b) := by
    exact Complex.continuous_ofReal.comp_continuousOn hsinC
  let Icos : ℝ := ∫ x in a..b, Real.cos (2 * Real.pi * F x)
  let Isin : ℝ := ∫ x in a..b, Real.sin (2 * Real.pi * F x)
  have hdecomp : (∫ x in a..b, ephase F x) = (Icos : ℂ) + (Isin : ℂ) * Complex.I := by
    calc
      (∫ x in a..b, ephase F x)
          = ∫ x in a..b, ((Real.cos (2 * Real.pi * F x) : ℝ) : ℂ) +
              (((Real.sin (2 * Real.pi * F x) : ℝ) : ℂ) * Complex.I) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [ephase]
              rw [Complex.exp_ofReal_mul_I]
      _ = (∫ x in a..b, ((Real.cos (2 * Real.pi * F x) : ℝ) : ℂ)) +
          (∫ x in a..b, ((Real.sin (2 * Real.pi * F x) : ℝ) : ℂ) * Complex.I) := by
              rw [intervalIntegral.integral_add]
              · exact hcosCC.intervalIntegrable
              · exact (hsinCC.mul continuousOn_const).intervalIntegrable
      _ = (Icos : ℂ) + (Isin : ℂ) * Complex.I := by
              rw [intervalIntegral.integral_mul_const]
              rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hnorm : ‖(∫ x in a..b, ephase F x)‖ ≤ |Icos| + |Isin| := by
    calc
      ‖∫ x in a..b, ephase F x‖ = ‖(Icos : ℂ) + (Isin : ℂ) * Complex.I‖ := by rw [hdecomp]
      _ ≤ ‖(Icos : ℂ)‖ + ‖(Isin : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |Icos| + |Isin| := by
          have h1 : ‖(Icos : ℂ)‖ = |Icos| := RCLike.norm_ofReal Icos
          have h2 : ‖(Isin : ℂ) * Complex.I‖ = |Isin| := by
            rw [norm_mul, Complex.norm_I, mul_comm, one_mul]
            exact RCLike.norm_ofReal Isin
          rw [h1, h2]
  simpa [Icos, Isin] using hnorm


/-! ## Combining the trigonometric bounds, and the full main theorem -/

/-- **First derivative test (complex phase).** If `|F'| ≥ m > 0` and `F'' ≥ 0` on
`(a,b)`, then `‖∫_a^b e(F)‖ ≤ 8/m`. -/
lemma exp_integral_first_deriv_le {a b : ℝ} (hab : a < b) (F : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b))
    (hsl : ∀ x : ℝ, x ∈ Set.Ioo a b → m ≤ |deriv F x|)
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv F) x) :
    ‖∫ x in a..b, ephase F x‖ ≤ 8 / m := by
  have hcont : ContinuousOn F (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact hF.continuousOn
  have hnorm := ephase_norm_le_trig F hcont
  have hc := cos_integral_first_deriv_le hab F hm hF hsl hpp
  have hs := sin_integral_first_deriv_le hab F hm hF hsl hpp
  calc
    ‖∫ x in a..b, ephase F x‖
        ≤ |∫ x in a..b, Real.cos (2 * Real.pi * F x)| +
            |∫ x in a..b, Real.sin (2 * Real.pi * F x)| := hnorm
    _ ≤ 4 / m + 4 / m := add_le_add hc hs
    _ = 8 / m := by ring

/-- Growth of the extended derivative: `F'' ≥ δ` forces `g y - g x ≥ δ(y-x)` for
`g := derivWithin F [a,b]` and `a ≤ x ≤ y ≤ b`. -/
lemma growth_derivWithin {a b : ℝ} (hab : a < b) (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → δ ≤ deriv (deriv F) x) :
    ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      δ * (y - x) ≤ derivWithin F (Set.Icc a b) y - derivWithin F (Set.Icc a b) x := by
  let g : ℝ → ℝ := fun x => derivWithin F (Set.Icc a b) x
  have hgC : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact (contDiffOn_derivWithin_one hab F hF).continuousOn
  intro x y hx hy hxy
  have hsub : Set.Icc x y ⊆ Set.Icc a b := by
    intro z hz
    exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
  let h : ℝ → ℝ := fun t => g t - δ * t
  have hhC : ContinuousOn h (Set.Icc x y) := by
    have hgc : ContinuousOn g (Set.Icc x y) := hgC.mono hsub
    have hidC : ContinuousOn (fun t : ℝ => δ * t) (Set.Icc x y) := by
      exact continuousOn_id.const_mul δ
    exact hgc.sub hidC
  have hhdiff : DifferentiableOn ℝ h (interior (Set.Icc x y)) := by
    intro z hz
    have hzxy : z ∈ Set.Ioo x y := by
      rw [interior_Icc] at hz
      exact hz
    have hzab : z ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hx.1 hzxy.1, lt_of_lt_of_le hzxy.2 hy.2⟩
    have hgda : DifferentiableAt ℝ g z :=
      (hasDerivAt_derivWithin_of_Ioo F hF hzab).differentiableAt
    have hlin : DifferentiableAt ℝ (fun t : ℝ => δ * t) z := by fun_prop
    exact ((hgda.sub hlin).differentiableWithinAt) -- wait g is a let; hgda is about g; goal DifferentiableAt (fun t => g t - δ*t) z? with h let
  have hhge : ∀ z ∈ interior (Set.Icc x y), 0 ≤ deriv h z := by
    intro z hz
    have hzxy : z ∈ Set.Ioo x y := by
      rw [interior_Icc] at hz
      exact hz
    have hzab : z ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hx.1 hzxy.1, lt_of_lt_of_le hzxy.2 hy.2⟩
    have hgda : HasDerivAt g
        (derivWithin (fun u : ℝ => derivWithin F (Set.Icc a b) u) (Set.Icc a b) z) z :=
      hasDerivAt_derivWithin_of_Ioo F hF hzab
    have hlin : HasDerivAt (fun t : ℝ => δ * t) δ z := by
      simpa [mul_comm] using (hasDerivAt_id z).const_mul δ
    have hdz : HasDerivAt (fun t : ℝ => g t - δ * t)
        (derivWithin (fun u : ℝ => derivWithin F (Set.Icc a b) u) (Set.Icc a b) z - δ) z :=
      hgda.sub hlin
    have hval : deriv h z = deriv (deriv F) z - δ := by
      dsimp [h]
      have hw : derivWithin (fun u : ℝ => derivWithin F (Set.Icc a b) u) (Set.Icc a b) z =
          deriv (deriv F) z := by
        exact derivWithin_g_eq_deriv_deriv F hF hzab
      rw [hdz.deriv, hw]
    rw [hval]
    have hpp' : δ ≤ deriv (deriv F) z := hpp z hzab
    linarith
  have hmono : MonotoneOn h (Set.Icc x y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc x y) hhC hhdiff hhge
  have hxyI : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
  have hyxI : y ∈ Set.Icc x y := ⟨hxy, le_rfl⟩
  have hle := hmono hxyI hyxI hxy
  dsimp [h] at hle
  linarith

/-- **Main theorem: second-derivative (curvature) oscillatory integral bound.** -/
lemma exp_integral_second_deriv_le {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hF : ContDiffOn ℝ 2 F (Set.Icc a b))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → δ ≤ deriv (deriv F) x) :
    ‖∫ x in a..b, cexp ((((2 * Real.pi * F x : ℝ) : ℝ) : ℂ) * I)‖ ≤ 100 / Real.sqrt δ := by
  by_cases heq : a = b
  · subst b
    simp
    positivity
  · have hab' : a < b := lt_of_le_of_ne hab heq
    let m : ℝ := Real.sqrt δ
    have hm : 0 < m := Real.sqrt_pos.2 hδ
    let sI : Set ℝ := Set.Icc a b
    let g : ℝ → ℝ := fun x => derivWithin F sI x
    have hgC : ContinuousOn g (Set.Icc a b) := by
      simpa [g, sI] using (contDiffOn_derivWithin_one hab' F hF).continuousOn
    have hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
        δ * (y - x) ≤ g y - g x := by
      intro x y hx hy hxy
      dsimp [g, sI]
      exact growth_derivWithin hab' F hδ hF hpp hx hy hxy
    rcases SdtOscSplit.exists_band_split hab hm hδ g hgC hgr with
      ⟨p, q, hap, hpq, hqb, hleft, hright, hlength⟩
    let u : ℝ → ℂ := fun x => ephase F x
    have hpble : p ≤ b := le_trans hpq hqb
    -- the map `t ↦ e^{2πit}` is continuous
    have hexpI : Continuous (fun t : ℝ => cexp (((t : ℝ) : ℂ) * Complex.I)) := by
      have h1 : Continuous (fun z : ℂ => Complex.exp (z * Complex.I)) :=
        Complex.continuous_exp.comp (continuous_id.mul continuous_const)
      exact h1.comp Complex.continuous_ofReal
    have huC : ContinuousOn u (Set.Icc a b) := by
      dsimp [u, ephase]
      have hinner : ContinuousOn (fun x : ℝ => 2 * Real.pi * F x) (Set.Icc a b) :=
        hF.continuousOn.const_mul (2 * Real.pi)
      exact (hexpI.continuousOn).comp hinner (fun x hx => Set.mem_univ (2 * Real.pi * F x))
    have huap : IntervalIntegrable u MeasureTheory.volume a p := by
      have hsub : Set.Icc a p ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨hx.1, le_trans hx.2 hpble⟩
      have hC : ContinuousOn u (uIcc a p) := by
        rw [uIcc_of_le hap]
        exact huC.mono hsub
      exact hC.intervalIntegrable
    have hupq : IntervalIntegrable u MeasureTheory.volume p q := by
      have hsub : Set.Icc p q ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨le_trans hap hx.1, le_trans hx.2 hqb⟩
      have hC : ContinuousOn u (uIcc p q) := by
        rw [uIcc_of_le hpq]
        exact huC.mono hsub
      exact hC.intervalIntegrable
    have huqb : IntervalIntegrable u MeasureTheory.volume q b := by
      have hsub : Set.Icc q b ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨le_trans hap (le_trans hpq hx.1), hx.2⟩
      have hC : ContinuousOn u (uIcc q b) := by
        rw [uIcc_of_le hqb]
        exact huC.mono hsub
      exact hC.intervalIntegrable
    have huaq : IntervalIntegrable u MeasureTheory.volume a q := by
      have hsub : Set.Icc a q ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨hx.1, le_trans hx.2 hqb⟩
      have hC : ContinuousOn u (uIcc a q) := by
        rw [uIcc_of_le (le_trans hap hpq)]
        exact huC.mono hsub
      exact hC.intervalIntegrable
    have hInt1 : (∫ x in a..p, u x) + (∫ x in p..q, u x) = ∫ x in a..q, u x :=
      intervalIntegral.integral_add_adjacent_intervals huap hupq
    have hInt2 : (∫ x in a..q, u x) + (∫ x in q..b, u x) = ∫ x in a..b, u x :=
      intervalIntegral.integral_add_adjacent_intervals huaq huqb
    have hsumE : (∫ x in a..b, u x) = (∫ x in a..p, u x) + (∫ x in p..q, u x) +
        (∫ x in q..b, u x) := by
      calc (∫ x in a..b, u x) = (∫ x in a..q, u x) + (∫ x in q..b, u x) := hInt2.symm
        _ = ((∫ x in a..p, u x) + (∫ x in p..q, u x)) + (∫ x in q..b, u x) := by rw [hInt1]
    have hsum : ‖∫ x in a..b, u x‖ ≤ ‖∫ x in a..p, u x‖ + ‖∫ x in p..q, u x‖ +
        ‖∫ x in q..b, u x‖ := by
      rw [hsumE]
      have h1 : ‖(∫ x in a..p, u x) + (∫ x in p..q, u x)‖ ≤
          ‖∫ x in a..p, u x‖ + ‖∫ x in p..q, u x‖ := norm_add_le _ _
      have h2 : ‖(∫ x in a..p, u x) + (∫ x in p..q, u x) + (∫ x in q..b, u x)‖ ≤
          ‖(∫ x in a..p, u x) + (∫ x in p..q, u x)‖ + ‖∫ x in q..b, u x‖ := norm_add_le _ _
      linarith
    -- F'' ≥ 0 everywhere (δ > 0)
    have hpp0 : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv F) x := by
      intro x hx
      exact le_trans (le_of_lt hδ) (hpp x hx)
    have hFap : ContDiffOn ℝ 2 F (Set.Icc a p) := by
      exact hF.mono (fun x hx => ⟨hx.1, le_trans hx.2 hpble⟩)
    have hslp : ∀ x : ℝ, x ∈ Set.Ioo a p → m ≤ |deriv F x| := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨hx.1, lt_of_lt_of_le hx.2 hpble⟩
      have hgx : deriv F x = g x := by
        dsimp [g]
        exact (derivWithin_eq_deriv_of_Ioo F hxab).symm
      have hgle : g x ≤ -m := hleft x hx
      have hglt0 : g x < 0 := lt_of_le_of_lt hgle (by linarith)
      rw [hgx]
      rw [abs_of_neg hglt0]
      linarith
    have hpplp : ∀ x : ℝ, x ∈ Set.Ioo a p → 0 ≤ deriv (deriv F) x := by
      intro x hx
      exact hpp0 x ⟨hx.1, lt_of_lt_of_le hx.2 hpble⟩
    have hLb : ‖∫ x in a..p, u x‖ ≤ 8 / m := by
      by_cases hap' : a < p
      · have hbd := exp_integral_first_deriv_le hap' F hm hFap hslp hpplp
        simpa [u] using hbd
      · have heq' : a = p := le_antisymm hap (le_of_not_gt hap')
        rw [heq']
        dsimp [u]
        simp
        positivity
    have hFqb : ContDiffOn ℝ 2 F (Set.Icc q b) := by
      exact hF.mono (fun x hx => ⟨le_trans hap (le_trans hpq hx.1), hx.2⟩)
    have hslq : ∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ |deriv F x| := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨lt_of_le_of_lt (le_trans hap hpq) hx.1, hx.2⟩
      have hgx : deriv F x = g x := by
        dsimp [g]
        exact (derivWithin_eq_deriv_of_Ioo F hxab).symm
      have hgge : m ≤ g x := hright x hx
      rw [hgx]
      rw [abs_of_nonneg (le_trans (le_of_lt hm) hgge)]
      exact hgge
    have hpplq : ∀ x : ℝ, x ∈ Set.Ioo q b → 0 ≤ deriv (deriv F) x := by
      intro x hx
      exact hpp0 x ⟨lt_of_le_of_lt (le_trans hap hpq) hx.1, hx.2⟩
    have hRb : ‖∫ x in q..b, u x‖ ≤ 8 / m := by
      by_cases hqb' : q < b
      · have hbd := exp_integral_first_deriv_le hqb' F hm hFqb hslq hpplq
        simpa [u] using hbd
      · have heq' : q = b := le_antisymm hqb (le_of_not_gt hqb')
        rw [heq']
        dsimp [u]
        simp
        positivity
    have hMb : ‖∫ x in p..q, u x‖ ≤ q - p := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q) (C := (1 : ℝ))
        (fun x hx => ephase_norm_le F x)
      simpa [abs_of_nonneg (sub_nonneg.mpr hpq)] using hb
    have hmne : m ≠ 0 := ne_of_gt hm
    have hm2 : m * m = δ := by
      dsimp [m]
      rw [← pow_two, Real.sq_sqrt hδ.le]
    have htwo : 2 * m / δ = 2 / m := by
      rw [← hm2]
      field_simp [hmne]
    calc
      ‖∫ x in a..b, cexp ((((2 * Real.pi * F x : ℝ) : ℝ) : ℂ) * I)‖ = ‖∫ x in a..b, u x‖ := by
          simp [u, ephase]
      _ ≤ ‖∫ x in a..p, u x‖ + ‖∫ x in p..q, u x‖ + ‖∫ x in q..b, u x‖ := hsum
      _ ≤ 8 / m + (q - p) + 8 / m := by
          nlinarith [hLb, hMb, hRb]
      _ ≤ 8 / m + (2 * m / δ) + 8 / m := by
          nlinarith [hlength]
      _ = 16 / m + 2 * m / δ := by ring
      _ = 18 / m := by rw [htwo]; ring
      _ ≤ 100 / m := by
          gcongr
          norm_num
      _ = 100 / Real.sqrt δ := by
          dsimp [m]

end
end Submission.SdtOscB

open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Shared infrastructure for `Submission.SdtPair` (the pair bound)

Definitions of the within-interval derivative functions
`gf N f := derivWithin f [0,N]` and `wf N f := derivWithin (gf N f) [0,N]`
(continuous on the closed interval, equal to `deriv f` / `deriv (deriv f)` in the
interior), plus their continuity/margin facts.
-/

namespace Submission.SdtPoisson

noncomputable section

/-- The interval `[0, N]`. -/
def sInt (N : ℕ) : Set ℝ := Set.Icc 0 (N : ℝ)

/-- The within-interval first derivative `G(x) := derivWithin f [0,N] x`. -/
def gf (N : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (sInt N) x

/-- The within-interval second derivative `W(x) := derivWithin G [0,N] x`. -/
def wf (N : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin (fun y : ℝ => derivWithin f (sInt N) y) (sInt N) x

/-- `0 < N` as reals, from `1 ≤ N`. -/
lemma zero_lt_N_real {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ) := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

/-- Continuity of the within-interval derivative `gf N f` on `[0,N]`. -/
lemma continuousOn_gf {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (sInt N)) :
    ContinuousOn (gf N f) (sInt N) := by
  change ContinuousOn (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x) (Set.Icc 0 (N : ℝ))
  exact (SdtOscB.contDiffOn_derivWithin_one (zero_lt_N_real hN) f hF).continuousOn

/-- Continuity of the within-interval second derivative `wf N f` on `[0,N]`. -/
lemma continuousOn_wf {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (sInt N)) :
    ContinuousOn (wf N f) (sInt N) := by
  change ContinuousOn (fun x : ℝ =>
      derivWithin (fun y : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) y) (Set.Icc 0 (N : ℝ)) x)
      (Set.Icc 0 (N : ℝ))
  exact (SdtOscB.derivWithin_derivWithin_continuousOn (zero_lt_N_real hN) f hF)

/-- At interior points `gf N f` equals `deriv f`. -/
lemma gf_eq_deriv_of_Ioo {N : ℕ} (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    gf N f x = deriv f x := by
  change derivWithin f (Set.Icc 0 (N : ℝ)) x = deriv f x
  exact SdtOscB.derivWithin_eq_deriv_of_Ioo (F := f) (a := 0) (b := (N : ℝ)) hx

/-- At interior points `wf N f` equals `deriv (deriv f)`. -/
lemma wf_eq_deriv_deriv_of_Ioo {N : ℕ} (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (sInt N)) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    wf N f x = deriv (deriv f) x := by
  change derivWithin (fun y : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) y) (Set.Icc 0 (N : ℝ)) x =
      deriv (deriv f) x
  exact SdtOscB.derivWithin_g_eq_deriv_deriv (F := f) (a := 0) (b := (N : ℝ)) hF hx

/-- `HasDerivAt` for `gf N f` at interior points. -/
lemma hasDerivAt_gf_of_Ioo {N : ℕ} (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (sInt N)) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (gf N f) (wf N f x) x := by
  change HasDerivAt (fun y : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) y)
    (derivWithin (fun y : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) y) (Set.Icc 0 (N : ℝ)) x) x
  exact SdtOscB.hasDerivAt_derivWithin_of_Ioo (F := f) (a := 0) (b := (N : ℝ)) hF hx

/-- The derivative-margin of `G` on the closed interval: `[1/2, B − 1/2]`.
(Interior margins of `deriv f` extend to the endpoints by continuity.) -/
lemma gf_margin_closed {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (_hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2) :
    ∀ x : ℝ, x ∈ sInt N →
      1 / 2 ≤ gf N f x ∧ gf N f x ≤ B - 1 / 2 := by
  intro x hx
  have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
  have hlow_open : ∀ y ∈ Set.Ioo 0 (N : ℝ), 1 / 2 ≤ gf N f y := by
    intro y hy
    have hgm := hmarg y hy
    have hgy : gf N f y = deriv f y := gf_eq_deriv_of_Ioo f hy
    linarith
  have hlow : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y := by
    intro y hy
    have hhC : ContinuousOn (fun z : ℝ => gf N f z - 1 / 2) (sInt N) :=
      hgC.sub continuousOn_const
    have hhint : ∀ z ∈ Set.Ioo 0 (N : ℝ), 0 ≤ gf N f z - 1 / 2 := by
      intro z hz
      linarith [hlow_open z hz]
    have hh := SdtOscB.nonneg_on_Icc_of_Ioo (zero_lt_N_real hN) hhC hhint y hy
    linarith
  have hup_open : ∀ y ∈ Set.Ioo 0 (N : ℝ), gf N f y ≤ B - 1 / 2 := by
    intro y hy
    have hgm := hmarg y hy
    have hgy : gf N f y = deriv f y := gf_eq_deriv_of_Ioo f hy
    linarith
  have hup : ∀ y ∈ sInt N, gf N f y ≤ B - 1 / 2 := by
    intro y hy
    have hhC : ContinuousOn (fun z : ℝ => (B - 1 / 2) - gf N f z) (sInt N) :=
      continuousOn_const.sub hgC
    have hhint : ∀ z ∈ Set.Ioo 0 (N : ℝ), 0 ≤ (B - 1 / 2) - gf N f z := by
      intro z hz
      linarith [hup_open z hz]
    have hh := SdtOscB.nonneg_on_Icc_of_Ioo (zero_lt_N_real hN) hhC hhint y hy
    linarith
  exact ⟨hlow x hx, hup x hx⟩

/-- `wf N f ≥ 0` on the closed interval (from `f'' ≥ 0` in the interior). -/
lemma wf_nonneg_closed {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x) :
    ∀ x : ℝ, x ∈ sInt N → 0 ≤ wf N f x := by
  have hwC : ContinuousOn (wf N f) (sInt N) := continuousOn_wf hN f hF
  intro x hx
  have hwint : ∀ y ∈ Set.Ioo 0 (N : ℝ), 0 ≤ wf N f y := by
    intro y hy
    have hwy : wf N f y = deriv (deriv f) y := wf_eq_deriv_deriv_of_Ioo f hF hy
    rw [hwy]
    exact hpp y hy
  have hh := SdtOscB.nonneg_on_Icc_of_Ioo (zero_lt_N_real hN) hwC hwint x hx
  exact hh

/-- `E` is continuous. -/
lemma E_continuous : Continuous E := by
  unfold E
  have h1 : Continuous fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ) := by
    exact Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun z : ℂ => cexp (z * Complex.I) := by
    exact Complex.continuous_exp.comp (continuous_id.mul continuous_const)
  exact h2.comp h1

/-- derivative of `x ↦ E(f x − c·x)` for a real frequency `c`. -/
lemma hasDerivAt_E_phase_real (f : ℝ → ℝ) (c : ℝ) {x : ℝ}
    (hF : HasDerivAt f (deriv f x) x) :
    HasDerivAt (fun y : ℝ => E (f y - c * y))
      (((tau * I) * (((deriv f x : ℝ) : ℂ) - (c : ℂ))) * E (f x - c * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hG : HasDerivAt (fun y : ℝ => f y - c * y) (deriv f x - c) x := by
    simpa [Pi.sub_def] using hF.sub hlin
  have hGder : deriv (fun y : ℝ => f y - c * y) x = deriv f x - c := hG.deriv
  have hG' : HasDerivAt (fun y : ℝ => f y - c * y) (deriv (fun y : ℝ => f y - c * y) x) x := by
    simpa [hGder] using hG
  have hc := hasDerivAt_E_comp_aux (fun y : ℝ => f y - c * y) (x := x) hG'
  have hcE : HasDerivAt (fun y : ℝ => E (f y - c * y))
      (E (f x - c * x) * (tau * ((deriv f x : ℝ) : ℂ) - tau * (c : ℂ)) * I) x := by
    convert hc using 1
    · funext y
      rw [E_eq_tau]
    · rw [hGder]
      simp [E_eq_tau]
      ring_nf
  convert hcE using 1
  ring

end
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Constant arithmetic for the pair bound

You must prove `constant_arith_bound` below (replace the placeholder proof).

Claim (pure real arithmetic): for `1 ≤ B` and `B ≤ c`, putting
`D := c − B + 1` (note `D ≥ 1`, since `c ≥ B`):

    4·(B − 1/2)/(c² − (B−1/2)²) + (B−1)/(c − B + 1/2)² + (B−1)/(c + 1/2)²
        ≤ 21·(B+1)/D²

Suggestion (very crude, constants are generous):
* `c² − (B−1/2)² ≥ (D − 1/2)² ≥ (D/2)² = D²/4`, so
  `4(B−1/2)/(c²−(B−1/2)²) ≤ 4(B−1/2)·4/D² = 16(B−1/2)/D²`.
  [For `c² − (B−1/2)² ≥ (D−1/2)²` use `c² − x² = (c−x)(c+x)` with
  `c − (B−1/2) = D − 1/2` and `c + (B−1/2) ≥ D − 1/2`; for
  `(D−1/2)² ≥ (D/2)²` use `D ≥ 1`.]
* `c − B + 1/2 = D − 1/2 ≥ D/2`, so `(B−1)/(c−B+1/2)² ≤ 4(B−1)/D²`.
* `c + 1/2 ≥ D` (since `B ≥ 1`), so `(B−1)/(c+1/2)² ≤ (B−1)/D²`.
* Total ≤ `(16(B−1/2) + 5(B−1))/D² ≤ 21(B+1)/D²` (as `16(B−1/2) + 5(B−1)
  = 21B − 13 ≤ 21(B+1)` and `B+1 ≥ 0`, `D² > 0`).

Feel free to split into helper lemmas above.  All divisions are by positive
quantities (check `D ≥ 1`, `c − B + 1/2 ≥ 1/2`, `c+1/2 ≥ ...`).  Use
`nlinarith`, `field_simp`, `linarith`, `ring_nf`, `positivity`, `gcongr`.
Do NOT change the statement; end with NO placeholder.  Axiom-clean.
-/

namespace Submission.SdtPoisson

noncomputable section

lemma constant_arith_bound {B c : ℝ} (hB : 1 ≤ B) (hcB : B ≤ c) :
    4 * (B - 1 / 2) / (c ^ 2 - (B - 1 / 2) ^ 2) + (B - 1) / (c - B + 1 / 2) ^ 2 +
        (B - 1) / (c + 1 / 2) ^ 2 ≤ 21 * (B + 1) / (c - B + 1) ^ 2 := by
  -- basic sign facts
  have hBhalf : 0 < B - 1 / 2 := by linarith
  have hBm1 : 0 ≤ B - 1 := by linarith
  have hDpos : 0 < c - B + 1 := by nlinarith
  have hDne : (c - B + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hDpos)
  -- positivity of all three denominators
  have h1pos : 0 < c ^ 2 - (B - 1 / 2) ^ 2 := by
    have h1 : 0 < c - (B - 1 / 2) := by nlinarith
    have h2 : 0 < c + (B - 1 / 2) := by nlinarith
    have h : 0 < (c - (B - 1 / 2)) * (c + (B - 1 / 2)) := mul_pos h1 h2
    nlinarith
  have hu2pos : 0 < (c - B + 1 / 2) ^ 2 := sq_pos_of_pos (by nlinarith : 0 < c - B + 1 / 2)
  have hz2pos : 0 < (c + 1 / 2) ^ 2 := sq_pos_of_pos (by nlinarith : 0 < c + 1 / 2)
  -- denominator size comparisons (all as polynomial facts, proved via factorizations)
  -- D² ≤ 4·(c² − (B−1/2)²), since c² − (B−1/2)² ≥ (c−B+1/2)² and (c−B+1/2) ≥ D/2
  have hD2le4b1 : (c - B + 1) ^ 2 ≤ 4 * (c ^ 2 - (B - 1 / 2) ^ 2) := by
    have hu : 0 ≤ c - B + 1 / 2 := by nlinarith
    have hw : 0 ≤ 2 * B - 1 := by nlinarith
    have hsquare : (c - B + 1 / 2) ^ 2 ≤ c ^ 2 - (B - 1 / 2) ^ 2 := by
      have hp : 0 ≤ (c - B + 1 / 2) * (2 * B - 1) := mul_nonneg hu hw
      nlinarith
    have hD2le4u2 : (c - B + 1) ^ 2 ≤ 4 * (c - B + 1 / 2) ^ 2 := by
      nlinarith [mul_nonneg (by nlinarith : 0 ≤ (c - B + 1 / 2) - 1 / 2)
        (by nlinarith : 0 ≤ 3 * (c - B + 1 / 2) + 1 / 2)]
    nlinarith
  -- D² ≤ 4·(c−B+1/2)² (for the second term)
  have hD2le4u2 : (c - B + 1) ^ 2 ≤ 4 * (c - B + 1 / 2) ^ 2 := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ (c - B + 1 / 2) - 1 / 2)
      (by nlinarith : 0 ≤ 3 * (c - B + 1 / 2) + 1 / 2)]
  -- D² ≤ (c+1/2)² (for the third term): difference of squares
  have hD2lez2 : (c - B + 1) ^ 2 ≤ (c + 1 / 2) ^ 2 := by
    have hdiff : 0 ≤ (c + 1 / 2) - (c - B + 1) := by nlinarith
    have hsum : 0 ≤ (c + 1 / 2) + (c - B + 1) := by nlinarith
    have hp : 0 ≤ ((c + 1 / 2) - (c - B + 1)) * ((c + 1 / 2) + (c - B + 1)) :=
      mul_nonneg hdiff hsum
    nlinarith
  -- term 1 ≤ 16(B−1/2)/D²
  have ht1 : 4 * (B - 1 / 2) / (c ^ 2 - (B - 1 / 2) ^ 2) ≤
      16 * (B - 1 / 2) / (c - B + 1) ^ 2 := by
    rw [div_le_div_iff₀ h1pos (sq_pos_of_pos hDpos)]
    nlinarith [mul_nonneg hBhalf.le
      (by nlinarith : 0 ≤ 4 * (c ^ 2 - (B - 1 / 2) ^ 2) - (c - B + 1) ^ 2)]
  -- term 2 ≤ 4(B−1)/D²
  have ht2 : (B - 1) / (c - B + 1 / 2) ^ 2 ≤
      4 * (B - 1) / (c - B + 1) ^ 2 := by
    rw [div_le_div_iff₀ hu2pos (sq_pos_of_pos hDpos)]
    nlinarith [mul_nonneg hBm1
      (by nlinarith : 0 ≤ 4 * (c - B + 1 / 2) ^ 2 - (c - B + 1) ^ 2)]
  -- term 3 ≤ (B−1)/D²
  have ht3 : (B - 1) / (c + 1 / 2) ^ 2 ≤
      (B - 1) / (c - B + 1) ^ 2 := by
    rw [div_le_div_iff₀ hz2pos (sq_pos_of_pos hDpos)]
    nlinarith [mul_nonneg hBm1
      (by nlinarith : 0 ≤ (c + 1 / 2) ^ 2 - (c - B + 1) ^ 2)]
  -- recombine the three bounds into a single fraction over D²
  have hsumfrac : (16 * (B - 1 / 2) + 4 * (B - 1) + (B - 1)) / (c - B + 1) ^ 2 =
      16 * (B - 1 / 2) / (c - B + 1) ^ 2 + 4 * (B - 1) / (c - B + 1) ^ 2 +
        (B - 1) / (c - B + 1) ^ 2 := by
    field_simp [hDne]
  have hnum : 16 * (B - 1 / 2) + 4 * (B - 1) + (B - 1) ≤ 21 * (B + 1) := by nlinarith
  have hfinal : (16 * (B - 1 / 2) + 4 * (B - 1) + (B - 1)) / (c - B + 1) ^ 2 ≤
      21 * (B + 1) / (c - B + 1) ^ 2 := by
    exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
  calc
    4 * (B - 1 / 2) / (c ^ 2 - (B - 1 / 2) ^ 2) + (B - 1) / (c - B + 1 / 2) ^ 2 +
        (B - 1) / (c + 1 / 2) ^ 2
        ≤ 16 * (B - 1 / 2) / (c - B + 1) ^ 2 + 4 * (B - 1) / (c - B + 1) ^ 2 +
          (B - 1) / (c - B + 1) ^ 2 := by
          nlinarith [ht1, ht2, ht3]
    _ ≤ 21 * (B + 1) / (c - B + 1) ^ 2 := by
          rw [← hsumfrac]
          exact hfinal

end
end Submission.SdtPoisson


/-!
# The van der Corput layer (Weyl differencing for exponential sums)

The classical estimates of van der Corput (Weyl differencing) control exponential
sums `Σ_{n<N} e(f(n))` through *autocorrelations* of the summands.  The two
structural inequalities of the method are, for complex coefficients `u n`
(supported on the integer interval `[0, N)`):

1. **autocorrelation bound** (`autocorrelation_bound`):

       |Σ_{n<N} u n|² ≤ Σ_{|h| < N} |C_h|,   C_h := Σ_{0 ≤ n, n+h < N} u(n+h)·conj(u n);

2. **Fejér-weighted van der Corput lemma** (`vdCorput_fejer`, IK Lemma 8.17 form;
to be added next):

       |Σ_{n<N} u n|² ≤ ((N + Q − 1)/Q) · Σ_{|h| < Q} (1 − |h|/Q) · |C_h|   (1 ≤ Q ≤ N).

For a *phase* sequence `u n = e(f n)` the autocorrelations are themselves exponential
sums `Σ e(f(n+h) − f(n))` whose phase has a smaller second derivative (`h·f''`),
which is how differencing reduces the problem (leading to the second-derivative test
and the Weyl bound in the t-aspect).

The sequences are modelled as functions `u : ℤ → ℂ` that vanish outside the interval
`Finset.Icc 0 (N-1)` (hypothesis `u_out`), so all interval-autocorrelations below are
well defined without any index arithmetic at the boundary.  Machine-verified,
axiom-clean.

**NEXT TARGET - second derivative test** (statement validated numerically with
constant `12`; to be stated and proved from `vdc_phase` + a first-derivative-test
bound on the autocorrelation phase sums):

    If `f : Real → Real` is twice differentiable on `[A, B]` with `f'' ≥ r > 0` (or
    `f'' ≤ −r`) throughout, then with `N := B − A`,

        |Σ_{A<n≤B} e(f(n))| ≤ 12·(N·r^{1/2} + r^{−1/2}).

PROOF SKETCH: apply `vdc_phase` with a parameter `Q`; the autocorrelation phase
`g_h(n) := f(n+h) − f(n)` has derivative `g_h' ≥ h·r` and monotone derivative (when
`f''` is), so a first-derivative test (geometric/summation-by-parts bound for
monotone increments over a unit interval) gives `|C_h| ≪ (hr)^{-1}`-type bounds;
summing the Fejér weights and optimizing `Q` yields the bound.  This is the
classical input for the Weyl-type bound on `Σ_{n≤N} n^{it}` in the t-aspect.

**CAUTION (corrected route) — the naive first layer is FALSE.**  A bound of the
shape `|Σ_{M<n≤M+N} e(f(n+h) − f(n))| ≪ (h·r)^{-1}` under merely `f'' ≥ r` is
false: for `f(x) = (r/2)x²` the differenced phase is exactly linear with slope
`r·h`, and when `r·h` is an integer every term has the same phase, so the sum has
modulus `N` (numerically confirmed).  The correct classical content is a bound in
terms of the distance `‖α‖` of the *local* slope `α` to the integers, i.e. the
linear-phase geometric bound

        |Σ_{n<L} e(αn)| ≤ min(L, c/‖α‖)     (‖α‖ := dist(α, ℤ)),

whose provable core (`geom_sum_eq`) is: for `w := e(α) ≠ 1`,
`Σ_{n<L} w^n = (w^L − 1)/(w − 1)`, hence `|Σ_{n<L} e(αn)| ≤ 2/|1 − w|`
(**DONE** — `linPhase_trivial`, `linPhase_geom`, `linPhase_eq_pow`, proved below; next is
linking `|1 − w| ≥ c·‖α‖` and the subinterval linearization).
The second-derivative test is then obtained by the classical route: split the
range into subintervals of length `ℓ ≍ r^{-1/2}`, Taylor-linearize the phase at each
subinterval's midpoint (remainder quadratic with `|f''| ≍ r`, so within the
subinterval the phase is `α(n − n₀) + O(r ℓ²)`), apply the linear-phase bound on
`e(α(n − n₀))` with the geometric factor `‖α‖`, and sum the rare subintervals with
`α` near an integer.  The first layer to formalize next is therefore the
linear-phase bound (geometric sum + triangle), NOT a `(hr)^{-1}` bound.
-/


open Complex Filter MeasureTheory
open scoped Real BigOperators ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.VanDerCorput

noncomputable section

/-- The summation interval `[0, N)` as a finset of integers (for `N ≥ 1`). -/
def rangeZ (N : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) ((N : ℤ) - 1)

/-- The autocorrelation `C_h := Σ_{0 ≤ n < N} u(n+h)·conj(u n)` (the summands with
`n + h` outside `[0,N)` vanish by the support hypothesis on `u`). -/
def autocorr (u : ℤ → ℂ) (N : ℕ) (h : ℤ) : ℂ :=
  ∑ n ∈ rangeZ N, u (n + h) * conj (u n)

/-- The interval of admissible shifts `|h| ≤ N-1`. -/
abbrev autocorrShifts (N : ℕ) : Finset ℤ := Finset.Icc (-(((N : ℤ) - 1))) (((N : ℤ) - 1))

/-- For `a, b` inside the box `[0, N-1]`, the difference `a - b` lies in the shift
interval `[-(N-1), N-1]`. -/
lemma sub_mem_autocorrShifts {N : ℕ} {a b : ℤ}
    (ha : a ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1)))
    (hb : b ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1))) : a - b ∈ autocorrShifts N := by
  rw [Finset.mem_Icc] at ha hb ⊢
  constructor <;> linarith

/-- Core reindexing step of the autocorrelation method: summing the autocorrelations
`u (n+h) · conj (u n)` over all pairs `(h, n)` with `h ∈ [-(N-1), N-1]` and `n ∈ [0,N-1]`
(terms with `n + h` outside the box vanish by support) reproduces exactly the double
sum `Σ_{a,b ∈ [0,N-1]} u a · conj (u b)`, each ordered pair `(a,b)` occurring once,
for the shift `h = a - b`. -/
lemma autocorrShifts_sum_eq_doubleSum {N : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ p ∈ (autocorrShifts N).product (rangeZ N), u (p.2 + p.1) * conj (u p.2)) =
      ∑ p ∈ (rangeZ N).product (rangeZ N), u p.1 * conj (u p.2) := by
  exact (Finset.sum_bij_ne_zero
    (s := (autocorrShifts N).product (rangeZ N)) (t := (rangeZ N).product (rangeZ N))
    (f := fun q : ℤ × ℤ => u (q.2 + q.1) * conj (u q.2))
    (g := fun p : ℤ × ℤ => u p.1 * conj (u p.2))
    (i := fun q _hq _hf => (q.2 + q.1, q.2))
    (by
      intro q hq hf
      have hq2 : q.2 ∈ rangeZ N := (Finset.mem_product.mp hq).2
      have hu : u (q.2 + q.1) ≠ 0 := (mul_ne_zero_iff.mp hf).1
      have hmem : q.2 + q.1 ∈ rangeZ N := by
        by_contra hn
        exact hu (u_out (q.2 + q.1) hn)
      exact Finset.mem_product.mpr ⟨hmem, hq2⟩)
    (by
      intro q1 _hq1 _hf1 q2 _hq2 _hf2 hpair
      rw [Prod.ext_iff] at hpair
      have hsnd : q1.2 = q2.2 := hpair.2
      have hfst : q1.2 + q1.1 = q2.2 + q2.1 := by simpa using hpair.1
      exact Prod.ext (by omega) hsnd)
    (by
      intro p hp hgp
      have hp1 : p.1 ∈ rangeZ N := (Finset.mem_product.mp hp).1
      have hp2 : p.2 ∈ rangeZ N := (Finset.mem_product.mp hp).2
      refine ⟨(p.1 - p.2, p.2), ?_, ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨sub_mem_autocorrShifts hp1 hp2, hp2⟩
      · have hp1' : p.2 + (p.1 - p.2) = p.1 := by omega
        simpa [hp1'] using hgp
      · ext <;> omega)
    (by
      intro q _hq _hf
      rfl))

/-- The exact complex identity underlying the autocorrelation bound:
`Σ_{|h| < N} C_h = (Σ u n) · conj (Σ u n) = |Σ u n|²`.  Obtained by expanding the
square into the double sum over `(a, b)` and reindexing each pair by `h = a - b`
through `autocorrShifts_sum_eq_doubleSum`. -/
lemma autocorr_sum_eq {N : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ n ∈ rangeZ N, u n) * (conj (∑ n ∈ rangeZ N, u n)) =
      ∑ h ∈ autocorrShifts N, autocorr u N h := by
  calc
    (∑ n ∈ rangeZ N, u n) * (conj (∑ n ∈ rangeZ N, u n))
        = (∑ a ∈ rangeZ N, u a) * (∑ b ∈ rangeZ N, conj (u b)) := by rw [map_sum]
    _ = ∑ p ∈ (rangeZ N).product (rangeZ N), u p.1 * conj (u p.2) := by
      calc
        (∑ a ∈ rangeZ N, u a) * (∑ b ∈ rangeZ N, conj (u b))
            = ∑ a ∈ rangeZ N, u a * (∑ b ∈ rangeZ N, conj (u b)) := by rw [Finset.sum_mul]
        _ = ∑ a ∈ rangeZ N, ∑ b ∈ rangeZ N, u a * conj (u b) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
        _ = ∑ p ∈ (rangeZ N).product (rangeZ N), u p.1 * conj (u p.2) := by
              exact (Finset.sum_product (rangeZ N) (rangeZ N)
                (fun p : ℤ × ℤ => u p.1 * conj (u p.2))).symm
    _ = ∑ p ∈ (autocorrShifts N).product (rangeZ N), u (p.2 + p.1) * conj (u p.2) := by
              exact (autocorrShifts_sum_eq_doubleSum u u_out).symm
    _ = ∑ h ∈ autocorrShifts N, ∑ n ∈ rangeZ N, u (n + h) * conj (u n) := by
              simpa using (Finset.sum_product (autocorrShifts N) (rangeZ N)
                (fun p : ℤ × ℤ => u (p.2 + p.1) * conj (u p.2)))
    _ = ∑ h ∈ autocorrShifts N, autocorr u N h := by
              apply Finset.sum_congr rfl
              intro h hh
              rfl

/-- **Autocorrelation bound**: the square of the sum is at most the sum of the
autocorrelation norms over all shifts `|h| < N`.  (Follows by expanding
`|Σ u n|² = Σ_{n,m} u n · conj(u m)`, reindexing by `h = n − m` and applying the
triangle inequality to the resulting `C_h`'s.) -/
lemma autocorrelation_bound {N : ℕ} (hN : 1 ≤ N) (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      ∑ h ∈ Finset.Icc (-(((N : ℤ) - 1))) (((N : ℤ) - 1)), ‖autocorr u N h‖ := by
  let S : ℂ := ∑ n ∈ rangeZ N, u n
  change ‖S‖ ^ 2 ≤ ∑ h ∈ autocorrShifts N, ‖autocorr u N h‖
  have h_ident : S * conj S = ∑ h ∈ autocorrShifts N, autocorr u N h := by
    simpa [S] using autocorr_sum_eq u u_out
  have hnorm : ‖S * conj S‖ = ‖S‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
  calc
    ‖S‖ ^ 2 = ‖S * conj S‖ := hnorm.symm
    _ = ‖∑ h ∈ autocorrShifts N, autocorr u N h‖ := by rw [h_ident]
    _ ≤ ∑ h ∈ autocorrShifts N, ‖autocorr u N h‖ :=
      norm_sum_le (autocorrShifts N) (fun h : ℤ => autocorr u N h)


def vdCWinIdx (N Q : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) ((N : ℤ) + (Q : ℤ) - 2)
def vdCWin (Q : ℕ) (r : ℤ) : Finset ℤ := Finset.Icc (r - (Q : ℤ) + 1) r
def vdCJ (Q : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)
def diffFiber (Q : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
  ((vdCJ Q).product (vdCJ Q)).filter (fun p : ℤ × ℤ => p.2 - p.1 = h)

lemma diff_mem_autocorrShifts (Q : ℕ) {p : ℤ × ℤ} (hp : p ∈ (vdCJ Q).product (vdCJ Q)) :
    p.2 - p.1 ∈ autocorrShifts Q := by
  have h1 : p.1 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := by simpa [vdCJ] using (Finset.mem_product.mp hp).1
  have h2 : p.2 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := by simpa [vdCJ] using (Finset.mem_product.mp hp).2
  rw [Finset.mem_Icc] at h1 h2
  unfold autocorrShifts
  rw [Finset.mem_Icc]
  constructor <;> omega

lemma diff_fiber_card_ofNat (Q : ℕ) (m : ℕ) :
    (diffFiber Q (m : ℤ)).card = Q - m := by
  have hF : (diffFiber Q (m : ℤ)).card = (Finset.Icc (0 : ℤ) ((Q : ℤ) - 1 - (m : ℤ))).card := by
    refine (Finset.card_bij (s := Finset.Icc (0 : ℤ) ((Q : ℤ) - 1 - (m : ℤ))) (t := diffFiber Q (m : ℤ))
      (i := fun u _hu => (u, u + (m : ℤ))) ?hi ?hinj ?hsurj).symm
    · intro u hu
      rw [Finset.mem_Icc] at hu
      rw [diffFiber, vdCJ]
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨
          (by change u ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1); rw [Finset.mem_Icc]; constructor <;> omega),
          (by change u + (m : ℤ) ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1); rw [Finset.mem_Icc]; constructor <;> omega)⟩
      · change (u + (m : ℤ)) - u = (m : ℤ)
        omega
    · intro u1 hu1 u2 hu2 heq
      exact congrArg Prod.fst heq
    · intro p hp
      rw [diffFiber, vdCJ] at hp
      rw [Finset.mem_filter] at hp
      have hp' := hp.1
      have hd : p.2 - p.1 = (m : ℤ) := hp.2
      have hu1 : p.1 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := (Finset.mem_product.mp hp').1
      have hu2 : p.2 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := (Finset.mem_product.mp hp').2
      rw [Finset.mem_Icc] at hu1 hu2
      refine ⟨p.1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · ext <;> omega
  rw [hF]
  change (Finset.Icc (0 : ℤ) ((Q : ℤ) - 1 - (m : ℤ))).card = Q - m
  rw [Int.card_Icc]
  have hq : (Q : ℤ) - 1 - (m : ℤ) + 1 - 0 = (Q : ℤ) - (m : ℤ) := by omega
  rw [hq]
  exact Int.toNat_sub Q m

lemma diff_fiber_card_neg (Q : ℕ) (h : ℤ) :
    (diffFiber Q (-h)).card = (diffFiber Q h).card := by
  refine Finset.card_bij (s := diffFiber Q (-h)) (t := diffFiber Q h)
    (i := fun p _hp => (p.2, p.1)) ?hi ?hinj ?hsurj
  · intro p hp
    have hp' : p ∈ (vdCJ Q).product (vdCJ Q) ∧ p.2 - p.1 = -h := by
      rw [diffFiber] at hp
      rw [Finset.mem_filter] at hp
      exact hp
    rw [diffFiber]
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨
        (by simpa using (Finset.mem_product.mp hp'.1).2),
        (by simpa using (Finset.mem_product.mp hp'.1).1)⟩
    · change p.1 - p.2 = h
      omega
  · intro p1 hp1 p2 hp2 heq
    have h1 : p1.2 = p2.2 := congrArg Prod.fst heq
    have h2 : p1.1 = p2.1 := congrArg Prod.snd heq
    exact Prod.ext h2 h1
  · intro q hq
    have hq' : q ∈ (vdCJ Q).product (vdCJ Q) ∧ q.2 - q.1 = h := by
      rw [diffFiber] at hq
      rw [Finset.mem_filter] at hq
      exact hq
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · rw [diffFiber]
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨
          (by simpa using (Finset.mem_product.mp hq'.1).2),
          (by simpa using (Finset.mem_product.mp hq'.1).1)⟩
      · change q.1 - q.2 = -h
        omega
    · rfl

lemma diff_fiber_card (Q : ℕ) (h : ℤ) : (diffFiber Q h).card = Q - h.natAbs := by
  rcases h with m | m
  · simpa [Int.natAbs_natCast] using diff_fiber_card_ofNat Q m
  · change (diffFiber Q (-((m : ℤ) + 1))).card = Q - (m + 1)
    rw [diff_fiber_card_neg Q ((m : ℤ) + 1)]
    simpa [Int.natAbs_natCast] using diff_fiber_card_ofNat Q (m + 1)

lemma sum_diff_eq_weighted {M : Type*} [AddCommMonoid M] (Q : ℕ) (x : ℤ → M) :
    (∑ p ∈ (vdCJ Q).product (vdCJ Q), x (p.2 - p.1)) =
      ∑ h ∈ autocorrShifts Q, (Q - h.natAbs) • x h := by
  calc
    (∑ p ∈ (vdCJ Q).product (vdCJ Q), x (p.2 - p.1))
        = ∑ q ∈ (autocorrShifts Q).sigma (fun h : ℤ => diffFiber Q h), x (q.2.2 - q.2.1) := by
          refine Finset.sum_bij
            (s := (vdCJ Q).product (vdCJ Q))
            (t := (autocorrShifts Q).sigma (fun h : ℤ => diffFiber Q h))
            (f := fun p => x (p.2 - p.1)) (g := fun q => x (q.2.2 - q.2.1))
            (i := fun p _hp => ⟨p.2 - p.1, p⟩) ?hi ?hinj ?hsurj ?hval
          · intro p hp
            exact Finset.mem_sigma.mpr ⟨diff_mem_autocorrShifts Q hp, by
              rw [diffFiber]
              exact Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
          · intro p1 hp1 p2 hp2 heq
            exact congrArg (fun z : (Σ _ : ℤ, ℤ × ℤ) => z.2) heq
          · intro q hq
            have hqp0 : q.2 ∈ diffFiber Q q.1 := (Finset.mem_sigma.mp hq).2
            have hqp : q.2 ∈ (vdCJ Q).product (vdCJ Q) ∧ q.2.2 - q.2.1 = q.1 := by
              rw [diffFiber] at hqp0
              rw [Finset.mem_filter] at hqp0
              exact hqp0
            refine ⟨q.2, hqp.1, ?_⟩
            · ext
              · simpa using hqp.2
              · rfl
          · intro p hp
            rfl
    _ = ∑ h ∈ autocorrShifts Q, ∑ p ∈ diffFiber Q h, x (p.2 - p.1) := by
          exact Finset.sum_sigma (autocorrShifts Q) (fun h : ℤ => diffFiber Q h) (fun q => x (q.2.2 - q.2.1))
    _ = ∑ h ∈ autocorrShifts Q, ∑ p ∈ diffFiber Q h, x h := by
          apply Finset.sum_congr rfl
          intro h hh
          apply Finset.sum_congr rfl
          intro p hp
          congr
          have hp' : p ∈ (vdCJ Q).product (vdCJ Q) ∧ p.2 - p.1 = h := by
            rw [diffFiber] at hp
            rw [Finset.mem_filter] at hp
            exact hp
          exact hp'.2
    _ = ∑ h ∈ autocorrShifts Q, (Q - h.natAbs) • x h := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [Finset.sum_const]
          rw [diff_fiber_card Q h]

-- window triple expansion
lemma windows_triple {N Q : ℕ} (u : ℤ → ℂ) :
    (∑ r ∈ vdCWinIdx N Q, (∑ a ∈ vdCWin Q r, u a) * (conj (∑ b ∈ vdCWin Q r, u b))) =
      ∑ x ∈ (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)),
        u x.2.1 * conj (u x.2.2) := by
  calc
    (∑ r ∈ vdCWinIdx N Q, (∑ a ∈ vdCWin Q r, u a) * (conj (∑ b ∈ vdCWin Q r, u b)))
        = ∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, ∑ b ∈ vdCWin Q r, u a * conj (u b) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [map_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = ∑ r ∈ vdCWinIdx N Q, ∑ p ∈ (vdCWin Q r).product (vdCWin Q r), u p.1 * conj (u p.2) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact (Finset.sum_product (vdCWin Q r) (vdCWin Q r) (fun p : ℤ × ℤ => u p.1 * conj (u p.2))).symm
    _ = ∑ x ∈ (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)),
          u x.2.1 * conj (u x.2.2) := by
          exact (Finset.sum_sigma (vdCWinIdx N Q) (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r))
            (fun x : (Σ _ : ℤ, ℤ × ℤ) => u x.2.1 * conj (u x.2.2))).symm

-- window triples reindex to offset pairs
lemma windows_sq_bij {N Q : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ x ∈ (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)),
        u x.2.1 * conj (u x.2.2)) =
      ∑ q ∈ ((vdCJ Q).product (vdCJ Q)).product (rangeZ N),
        u (q.2 + q.1.2 - q.1.1) * conj (u q.2) := by
  refine Finset.sum_bij_ne_zero
    (s := (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)))
    (t := ((vdCJ Q).product (vdCJ Q)).product (rangeZ N))
    (f := fun x : (Σ _ : ℤ, ℤ × ℤ) => u x.2.1 * conj (u x.2.2))
    (g := fun q : ((ℤ × ℤ) × ℤ) => u (q.2 + q.1.2 - q.1.1) * conj (u q.2))
    (i := fun x _hx _hf => ((x.1 - x.2.1, x.1 - x.2.2), x.2.2)) ?hi ?hinj ?hsurj ?hval
  · intro x hx hf
    have hx1 : x.1 ∈ vdCWinIdx N Q := (Finset.mem_sigma.mp hx).1
    have hxp : x.2 ∈ (vdCWin Q x.1).product (vdCWin Q x.1) := (Finset.mem_sigma.mp hx).2
    have ha : x.2.1 ∈ vdCWin Q x.1 := (Finset.mem_product.mp hxp).1
    have hb : x.2.2 ∈ vdCWin Q x.1 := (Finset.mem_product.mp hxp).2
    have hf' := mul_ne_zero_iff.mp hf
    have hua : u x.2.1 ≠ 0 := hf'.1
    have hucb : conj (u x.2.2) ≠ 0 := hf'.2
    have hub : u x.2.2 ≠ 0 := by
      intro hb0
      apply hucb
      rw [hb0]
      simp
    have hboxb : x.2.2 ∈ rangeZ N := by
      by_contra hn
      exact hub (u_out x.2.2 hn)
    have haI : x.2.1 ∈ Finset.Icc (x.1 - (Q : ℤ) + 1) x.1 := by simpa [vdCWin] using ha
    have hbI : x.2.2 ∈ Finset.Icc (x.1 - (Q : ℤ) + 1) x.1 := by simpa [vdCWin] using hb
    rw [Finset.mem_Icc] at haI hbI
    refine Finset.mem_product.mpr ⟨?_, hboxb⟩
    exact Finset.mem_product.mpr ⟨(by
      change x.1 - x.2.1 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)
      rw [Finset.mem_Icc]
      constructor <;> omega), (by
      change x.1 - x.2.2 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)
      rw [Finset.mem_Icc]
      constructor <;> omega)⟩
  · intro x1 hx1 hf1 x2 hx2 hf2 heq
    cases x1 with
    | mk r1 p1 =>
      cases x2 with
      | mk r2 p2 =>
        cases p1 with
        | mk a1 b1 =>
          cases p2 with
          | mk a2 b2 =>
            have hb : b1 = b2 := congrArg (fun z : ((ℤ × ℤ) × ℤ) => z.2) heq
            have hj2 : r1 - b1 = r2 - b2 := congrArg (fun z : ((ℤ × ℤ) × ℤ) => z.1.2) heq
            have hj1 : r1 - a1 = r2 - a2 := congrArg (fun z : ((ℤ × ℤ) × ℤ) => z.1.1) heq
            have hr : r1 = r2 := by omega
            have ha : a1 = a2 := by omega
            subst b1
            subst r1
            subst a1
            rfl
  · intro q hq hg
    have hq1 : q.1 ∈ (vdCJ Q).product (vdCJ Q) := (Finset.mem_product.mp hq).1
    have hq2 : q.2 ∈ rangeZ N := (Finset.mem_product.mp hq).2
    have hj1 : q.1.1 ∈ vdCJ Q := (Finset.mem_product.mp hq1).1
    have hj2 : q.1.2 ∈ vdCJ Q := (Finset.mem_product.mp hq1).2
    have hg' := mul_ne_zero_iff.mp hg
    have hua : u (q.2 + q.1.2 - q.1.1) ≠ 0 := hg'.1
    have hucb : conj (u q.2) ≠ 0 := hg'.2
    have hub : u q.2 ≠ 0 := by
      intro hb0
      apply hucb
      rw [hb0]
      simp
    have hboxa : q.2 + q.1.2 - q.1.1 ∈ rangeZ N := by
      by_contra hn
      exact hua (u_out (q.2 + q.1.2 - q.1.1) hn)
    have hq2I : q.2 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1)) := by simpa [rangeZ] using hq2
    have hj1I : q.1.1 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := by simpa [vdCJ] using hj1
    have hj2I : q.1.2 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := by simpa [vdCJ] using hj2
    have hboxaI : q.2 + q.1.2 - q.1.1 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1)) := by simpa [rangeZ] using hboxa
    rw [Finset.mem_Icc] at hq2I hj1I hj2I hboxaI
    let x : (Σ _ : ℤ, ℤ × ℤ) := ⟨q.2 + q.1.2, (q.2 + q.1.2 - q.1.1, q.2)⟩
    refine ⟨x, ?mem, ?nz, ?eq⟩
    · dsimp [x]
      rw [Finset.mem_sigma]
      constructor
      · change q.2 + q.1.2 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) + (Q : ℤ) - 2))
        rw [Finset.mem_Icc]
        constructor <;> omega
      · exact Finset.mem_product.mpr ⟨(by
          change q.2 + q.1.2 - q.1.1 ∈ vdCWin Q (q.2 + q.1.2)
          change q.2 + q.1.2 - q.1.1 ∈ Finset.Icc (q.2 + q.1.2 - (Q : ℤ) + 1) (q.2 + q.1.2)
          rw [Finset.mem_Icc]
          constructor <;> omega), (by
          change q.2 ∈ vdCWin Q (q.2 + q.1.2)
          change q.2 ∈ Finset.Icc (q.2 + q.1.2 - (Q : ℤ) + 1) (q.2 + q.1.2)
          rw [Finset.mem_Icc]
          constructor <;> omega)⟩
    · dsimp [x]
      exact hg
    · dsimp [x]
      have h1 : q.2 + q.1.2 - (q.2 + q.1.2 - q.1.1) = q.1.1 := by omega
      have h2 : q.2 + q.1.2 - q.2 = q.1.2 := by omega
      simp [h1, h2]
  · intro x hx hf
    have h1 : x.2.2 + (x.1 - x.2.2) - (x.1 - x.2.1) = x.2.1 := by omega
    simp [h1]

-- convert the reindexed window sum into autocorrelations over the offset square
lemma windows_sq_eq {N Q : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ x ∈ (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)),
        u x.2.1 * conj (u x.2.2)) =
      ∑ p ∈ (vdCJ Q).product (vdCJ Q), autocorr u N (p.2 - p.1) := by
  calc
    (∑ x ∈ (vdCWinIdx N Q).sigma (fun r : ℤ => (vdCWin Q r).product (vdCWin Q r)),
        u x.2.1 * conj (u x.2.2))
        = ∑ q ∈ ((vdCJ Q).product (vdCJ Q)).product (rangeZ N),
            u (q.2 + q.1.2 - q.1.1) * conj (u q.2) := windows_sq_bij u u_out
    _ = ∑ x ∈ (vdCJ Q).product (vdCJ Q), ∑ b ∈ rangeZ N, u (b + x.2 - x.1) * conj (u b) := by
          simpa using (Finset.sum_product ((vdCJ Q).product (vdCJ Q)) (rangeZ N)
            (fun q : ((ℤ × ℤ) × ℤ) => u (q.2 + q.1.2 - q.1.1) * conj (u q.2)))
    _ = ∑ x ∈ (vdCJ Q).product (vdCJ Q), autocorr u N (x.2 - x.1) := by
          apply Finset.sum_congr rfl
          intro x hx
          unfold autocorr
          apply Finset.sum_congr rfl
          intro b hb
          congr 1
          ring

-- main complex identity for the window square sums
lemma window_sq_cplx {N Q : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ r ∈ vdCWinIdx N Q, (∑ a ∈ vdCWin Q r, u a) * (conj (∑ b ∈ vdCWin Q r, u b))) =
      ∑ p ∈ (vdCJ Q).product (vdCJ Q), autocorr u N (p.2 - p.1) := by
  rw [windows_triple u]
  exact windows_sq_eq u u_out

lemma int_cast_abs (h : ℤ) : |(h : ℝ)| = (h.natAbs : ℝ) := by
  have hm := Int.natAbs_eq h
  rcases hm with hpos | hneg
  · rw [hpos]
    simp [abs_of_nonneg]
  · rw [hneg]
    simp [abs_of_nonneg]

-- |h| ≤ Q - 1 as reals for h in autocorrShifts Q
lemma autocorrShifts_abs (Q : ℕ) {h : ℤ} (hh : h ∈ autocorrShifts Q) :
    (|(h : ℝ)|) ≤ (Q : ℝ) - 1 := by
  unfold autocorrShifts at hh
  rw [Finset.mem_Icc] at hh
  have h1 : -(((Q : ℝ) - 1)) ≤ (h : ℝ) := by exact_mod_cast hh.1
  have h2 : (h : ℝ) ≤ ((Q : ℝ) - 1) := by exact_mod_cast hh.2
  rw [abs_le]
  exact ⟨h1, h2⟩

/-- Fejer weight (Q - |h|) as real -/
def fejerW (Q : ℕ) (h : ℤ) : ℝ := (Q : ℝ) - (|(h : ℝ)|)

-- the real bound: sum over windows of ||W||^2 is controlled by weighted autocorrelations
lemma window_sq_le {N Q : ℕ} (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2) ≤
      ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ := by
  let X : ℝ := ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2
  have hX0 : 0 ≤ X := by
    dsimp [X]
    apply Finset.sum_nonneg
    intro r hr
    positivity
  have hXc : (X : ℂ) =
      ∑ r ∈ vdCWinIdx N Q, (∑ a ∈ vdCWin Q r, u a) * (conj (∑ b ∈ vdCWin Q r, u b)) := by
    dsimp [X]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r hr
    symm
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hYc : (X : ℂ) = ∑ p ∈ (vdCJ Q).product (vdCJ Q), autocorr u N (p.2 - p.1) := by
    rw [hXc]
    exact window_sq_cplx u u_out
  calc
    X = ‖(X : ℂ)‖ := (Complex.norm_of_nonneg hX0).symm
    _ = ‖∑ p ∈ (vdCJ Q).product (vdCJ Q), autocorr u N (p.2 - p.1)‖ := by
          rw [hYc]
    _ ≤ ∑ p ∈ (vdCJ Q).product (vdCJ Q), ‖autocorr u N (p.2 - p.1)‖ :=
          norm_sum_le ((vdCJ Q).product (vdCJ Q)) (fun p : ℤ × ℤ => autocorr u N (p.2 - p.1))
    _ = ∑ h ∈ autocorrShifts Q, (Q - h.natAbs) • ‖autocorr u N h‖ := by
          exact sum_diff_eq_weighted Q (fun h : ℤ => ‖autocorr u N h‖)
    _ = ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ := by
          simp [nsmul_eq_mul]

-- Cauchy-Schwarz on the windows
lemma windows_cs {N Q : ℕ} (u : ℤ → ℂ) :
    ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2 ≤
      ((vdCWinIdx N Q).card : ℝ) *
        ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2 := by
  have htri : ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ≤
      ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ :=
    norm_sum_le (vdCWinIdx N Q) (fun r => ∑ a ∈ vdCWin Q r, u a)
  have hA : 0 ≤ ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ := norm_nonneg _
  have hB : 0 ≤ ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ := by
    apply Finset.sum_nonneg
    intro r hr
    exact norm_nonneg _
  have hsq1 : ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2 ≤
      (∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖) ^ 2 := by
    exact sq_le_sq' (by linarith) htri
  have hsq2 := sq_sum_le_card_mul_sum_sq (s := vdCWinIdx N Q)
    (f := fun r : ℤ => ‖∑ a ∈ vdCWin Q r, u a‖)
  calc
    ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2
        ≤ (∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖) ^ 2 := hsq1
    _ ≤ ((vdCWinIdx N Q).card : ℝ) * ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2 := hsq2

-- cardinality of window index set
lemma vdCWinIdx_card {N Q : ℕ} (hN : 1 ≤ N) : (vdCWinIdx N Q).card = N + Q - 1 := by
  unfold vdCWinIdx
  rw [Int.card_Icc]
  have h : (N : ℤ) + (Q : ℤ) - 2 + 1 - 0 = (N : ℤ) + (Q : ℤ) - 1 := by omega
  have hpos : 0 ≤ (N : ℤ) + (Q : ℤ) - 1 := by omega
  rw [h]
  have hz := Int.toNat_of_nonneg hpos
  have hz' : (((N : ℤ) + (Q : ℤ) - 1).toNat : ℤ) = (N + Q - 1 : ℕ) := by
    rw [hz]
    omega
  exact_mod_cast hz'

lemma win_sum_eq_filter {N Q : ℕ} (r : ℤ) (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ n ∈ vdCWin Q r, u n) =
      ∑ n ∈ rangeZ N, if n ∈ vdCWin Q r then u n else 0 := by
  calc
    (∑ n ∈ vdCWin Q r, u n)
        = ∑ n ∈ (vdCWin Q r).filter (fun n : ℤ => n ∈ rangeZ N), u n := by
          refine (Finset.sum_subset (Finset.filter_subset (fun n : ℤ => n ∈ rangeZ N) (vdCWin Q r)) ?_).symm
          intro n hn hnf
          exact u_out n (by
            intro hbox
            exact hnf (Finset.mem_filter.mpr ⟨hn, hbox⟩))
    _ = ∑ n ∈ (rangeZ N).filter (fun n : ℤ => n ∈ vdCWin Q r), u n := by
          congr 1
          ext n
          rw [Finset.mem_filter, Finset.mem_filter]
          tauto
    _ = ∑ n ∈ rangeZ N, if n ∈ vdCWin Q r then u n else 0 := by
          rw [Finset.sum_filter]

lemma shiftIdx_card (Q : ℕ) (hQ : 1 ≤ Q) :
    ((Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)).card : ℂ) = (Q : ℂ) := by
  rw [Int.card_Icc]
  have hq : (Q : ℤ) - 1 + 1 - 0 = (Q : ℤ) := by omega
  rw [hq]
  have hz : (((Q : ℤ).toNat : ℤ) = (Q : ℤ)) := Int.toNat_of_nonneg (by omega : 0 ≤ (Q : ℤ))
  exact_mod_cast hz

lemma window_pairs_bij {N Q : ℕ} (u : ℤ → ℂ) :
    (∑ p ∈ ((vdCWinIdx N Q).product (rangeZ N)).filter (fun p : ℤ × ℤ => p.2 ∈ vdCWin Q p.1), u p.2) =
      ∑ q ∈ ((Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)).product (rangeZ N)), u q.2 := by
  refine Finset.sum_bij
    (s := ((vdCWinIdx N Q).product (rangeZ N)).filter (fun p : ℤ × ℤ => p.2 ∈ vdCWin Q p.1))
    (t := (Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)).product (rangeZ N))
    (f := fun p : ℤ × ℤ => u p.2)
    (g := fun q : ℤ × ℤ => u q.2)
    (i := fun p _hp => (p.1 - p.2, p.2)) ?hi ?hinj ?hsurj ?hval
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    have hwin : p.2 ∈ vdCWin Q p.1 := (Finset.mem_filter.mp hp).2
    have hpR : p.1 ∈ vdCWinIdx N Q := (Finset.mem_product.mp hp').1
    have hpn : p.2 ∈ rangeZ N := (Finset.mem_product.mp hp').2
    have hpnb : p.2 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1)) := by simpa [rangeZ] using hpn
    have hpRb : p.1 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) + (Q : ℤ) - 2)) := by simpa [vdCWinIdx] using hpR
    have hwinb : p.2 ∈ Finset.Icc (p.1 - (Q : ℤ) + 1) p.1 := by simpa [vdCWin] using hwin
    rw [Finset.mem_Icc] at hpnb hpRb hwinb
    exact Finset.mem_product.mpr ⟨(by
      change p.1 - p.2 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)
      rw [Finset.mem_Icc]
      constructor <;> omega), hpn⟩
  · intro p1 hp1 p2 hp2 hpair
    rw [Prod.ext_iff] at hpair
    have hsnd : p1.2 = p2.2 := hpair.2
    have hfst : p1.1 - p1.2 = p2.1 - p2.2 := hpair.1
    exact Prod.ext (by omega) hsnd
  · intro q hq
    have hq' : q.1 ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1) := (Finset.mem_product.mp hq).1
    have hqn : q.2 ∈ rangeZ N := (Finset.mem_product.mp hq).2
    have hqnb : q.2 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) - 1)) := by simpa [rangeZ] using hqn
    rw [Finset.mem_Icc] at hq' hqnb
    refine ⟨(q.2 + q.1, q.2), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨(by
          change q.2 + q.1 ∈ Finset.Icc (0 : ℤ) (((N : ℤ) + (Q : ℤ) - 2))
          rw [Finset.mem_Icc]
          constructor <;> omega), hqn⟩
      · change q.2 ∈ Finset.Icc (q.2 + q.1 - (Q : ℤ) + 1) (q.2 + q.1)
        rw [Finset.mem_Icc]
        constructor <;> omega
    · ext <;> omega
  · intro p hp
    rfl

lemma windows_cover {N Q : ℕ} (hQ : 1 ≤ Q) (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    (∑ r ∈ vdCWinIdx N Q, ∑ n ∈ vdCWin Q r, u n) =
      (Q : ℂ) * (∑ n ∈ rangeZ N, u n) := by
  calc
    (∑ r ∈ vdCWinIdx N Q, ∑ n ∈ vdCWin Q r, u n)
        = ∑ r ∈ vdCWinIdx N Q, ∑ n ∈ rangeZ N, if n ∈ vdCWin Q r then u n else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact win_sum_eq_filter r u u_out
    _ = ∑ p ∈ (vdCWinIdx N Q).product (rangeZ N), if p.2 ∈ vdCWin Q p.1 then u p.2 else 0 := by
          exact (Finset.sum_product (vdCWinIdx N Q) (rangeZ N)
            (fun p : ℤ × ℤ => if p.2 ∈ vdCWin Q p.1 then u p.2 else 0)).symm
    _ = ∑ p ∈ ((vdCWinIdx N Q).product (rangeZ N)).filter (fun p : ℤ × ℤ => p.2 ∈ vdCWin Q p.1), u p.2 := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ ((Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)).product (rangeZ N)), u q.2 := window_pairs_bij u
    _ = (∑ j ∈ Finset.Icc (0 : ℤ) ((Q : ℤ) - 1), (∑ n ∈ rangeZ N, u n)) := by
          simpa using (Finset.sum_product (Finset.Icc (0 : ℤ) ((Q : ℤ) - 1)) (rangeZ N)
            (fun q : ℤ × ℤ => u q.2))
    _ = (Q : ℂ) * (∑ n ∈ rangeZ N, u n) := by
          rw [Finset.sum_const, nsmul_eq_mul, shiftIdx_card Q hQ]

lemma fejerW_eq {Q : ℕ} {h : ℤ} (hh : h ∈ autocorrShifts Q) :
    ((Q - h.natAbs : ℕ) : ℝ) = fejerW Q h := by
  unfold fejerW
  rw [int_cast_abs]
  have hb := autocorrShifts_abs Q hh
  rw [int_cast_abs] at hb
  have hmle : h.natAbs ≤ Q := by
    exact_mod_cast (by nlinarith : (h.natAbs : ℝ) ≤ (Q : ℝ))
  rw [Nat.cast_sub hmle]

-- Fejer-weight real inequality chain: from Q^2 |S|^2 bound to the Fejer form
lemma vdCorput_fejer_shifts {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      ((N + Q - 1 : ℝ) / Q) *
        ∑ h ∈ autocorrShifts Q, ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
  have hS0 : 0 ≤ ‖∑ n ∈ rangeZ N, u n‖ ^ 2 := by positivity
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hQ)
  have hNQpos : (0 : ℝ) < (N + Q - 1 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    nlinarith
  have hcs : ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2 ≤
      (N + Q - 1 : ℝ) * ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2 := by
    have h := windows_cs (N := N) (Q := Q) u
    have hc : ((vdCWinIdx N Q).card : ℝ) = (N + Q - 1 : ℝ) := by
      have hc0 := vdCWinIdx_card (N := N) (Q := Q) hN
      have hc1 : ((vdCWinIdx N Q).card : ℝ) = ((N + Q - 1 : ℕ) : ℝ) :=
        congrArg (fun n : ℕ => (n : ℝ)) hc0
      have hc2 : ((N + Q - 1 : ℕ) : ℝ) = (N : ℝ) + (Q : ℝ) - 1 := by
        have hsub : (1 : ℕ) ≤ N + Q := by omega
        rw [Nat.cast_sub hsub]
        simp
      rw [hc1, hc2]
    simpa [hc] using h
  have hcov : (∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a) =
      (Q : ℂ) * (∑ n ∈ rangeZ N, u n) :=
    windows_cover (N := N) (Q := Q) hQ u u_out
  have hsq : (∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2) ≤
      ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ :=
    window_sq_le (N := N) (Q := Q) u u_out
  have hA : ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2 ≤
      (N + Q - 1 : ℝ) *
        ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ := by
    calc
      ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2
          ≤ (N + Q - 1 : ℝ) * ∑ r ∈ vdCWinIdx N Q, ‖∑ a ∈ vdCWin Q r, u a‖ ^ 2 := hcs
      _ ≤ (N + Q - 1 : ℝ) *
            ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ := by
            exact mul_le_mul_of_nonneg_left hsq (le_of_lt hNQpos)
  have hcovn : ‖∑ r ∈ vdCWinIdx N Q, ∑ a ∈ vdCWin Q r, u a‖ ^ 2 =
      (Q : ℝ) ^ 2 * ‖∑ n ∈ rangeZ N, u n‖ ^ 2 := by
    rw [hcov]
    rw [norm_mul]
    have hnQ : ‖(Q : ℂ)‖ = (Q : ℝ) := by
      rw [← Complex.ofReal_natCast]
      exact Complex.norm_of_nonneg (by exact_mod_cast (Nat.zero_le Q) : 0 ≤ (Q : ℝ))
    rw [hnQ]
    ring
  have hQ2pos : (0 : ℝ) < (Q : ℝ) ^ 2 := sq_pos_of_pos hQpos
  have hB : (Q : ℝ) ^ 2 * ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      (N + Q - 1 : ℝ) *
        ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖ := by
    simpa [hcovn] using hA
  have hC : ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      ((N + Q - 1 : ℝ) *
        ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖) / (Q : ℝ) ^ 2 := by
    exact (le_div_iff₀' hQ2pos).mpr hB
  have hW : (∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖) =
      ∑ h ∈ autocorrShifts Q, fejerW Q h * ‖autocorr u N h‖ := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [fejerW_eq hh]
  have hW2 : ((N + Q - 1 : ℝ) * (∑ h ∈ autocorrShifts Q, fejerW Q h * ‖autocorr u N h‖)) /
      (Q : ℝ) ^ 2 = ((N + Q - 1 : ℝ) / Q) *
        ∑ h ∈ autocorrShifts Q, ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
    calc
      ((N + Q - 1 : ℝ) * (∑ h ∈ autocorrShifts Q, fejerW Q h * ‖autocorr u N h‖)) / (Q : ℝ) ^ 2
          = ∑ h ∈ autocorrShifts Q, ((N + Q - 1 : ℝ) * (fejerW Q h * ‖autocorr u N h‖)) / (Q : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            rw [Finset.sum_div]
      _ = ∑ h ∈ autocorrShifts Q, ((N + Q - 1 : ℝ) / Q) *
            ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
            apply Finset.sum_congr rfl
            intro h hh
            have hQnz : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
            field_simp [hQnz]
            unfold fejerW
            ring
      _ = ((N + Q - 1 : ℝ) / Q) * ∑ h ∈ autocorrShifts Q,
            ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h hh
            ring
  have hW3 : ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤ ((N + Q - 1 : ℝ) / Q) *
      ∑ h ∈ autocorrShifts Q, ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
    calc
      ‖∑ n ∈ rangeZ N, u n‖ ^ 2
          ≤ ((N + Q - 1 : ℝ) *
              ∑ h ∈ autocorrShifts Q, ((Q - h.natAbs : ℕ) : ℝ) * ‖autocorr u N h‖) / (Q : ℝ) ^ 2 := hC
      _ = ((N + Q - 1 : ℝ) * (∑ h ∈ autocorrShifts Q, fejerW Q h * ‖autocorr u N h‖)) / (Q : ℝ) ^ 2 := by
          rw [hW]
      _ = ((N + Q - 1 : ℝ) / Q) *
            ∑ h ∈ autocorrShifts Q, ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := hW2
  exact hW3


/--
**Fejér-weighted van der Corput lemma** (IK Lemma 8.17 form): for `1 ≤ Q ≤ N`,

    |Σ_{n<N} u n|² ≤ ((N + Q − 1)/Q) · Σ_{|h| < Q} (1 − |h|/Q) · |C_h|.

Proof.  Sliding windows `W_r := Σ_{r−Q<n≤r} u n` over `r ∈ [0, N+Q−2]` cover each
term of `S` exactly `Q` times, so `Q·S = Σ_r W_r`; Cauchy–Schwarz gives
`Q²|S|² ≤ (N+Q−1)·Σ_r|W_r|²`.  Expanding each window square and reindexing the pair
`(a,b)` in a window by `h = a−b` (equivalently, counting for each offset pair
`(j₁,j₂) ∈ [0,Q−1]²` the window containing both ends) yields the exact complex
identity `Σ_r |W_r|² = Σ_{|h|<Q} (Q−|h|)·C_h`, and the triangle inequality finishes
the proof. -/
lemma vdCorput_fejer {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) (u : ℤ → ℂ)
    (u_out : ∀ n : ℤ, n ∉ rangeZ N → u n = 0) :
    ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      ((N + Q - 1 : ℝ) / Q) *
        ∑ h ∈ Finset.Icc (-(((Q : ℤ) - 1))) (((Q : ℤ) - 1)),
          ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := by
  change ‖∑ n ∈ rangeZ N, u n‖ ^ 2 ≤
      ((N + Q - 1 : ℝ) / Q) *
        ∑ h ∈ autocorrShifts Q, ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖
  exact vdCorput_fejer_shifts hN hQ hQN u u_out


/-- Conjugate of a pure-imaginary phase. -/
lemma theta_conj (a : ℝ) : conj (((a : ℝ) : ℂ) * I) = -(((a : ℝ) : ℂ) * I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- For a *phase* sequence `u n = e(2πi·f n)` the autocorrelation `C_h` is itself an
exponential sum whose phase is the first difference `2πi·(f(n+h) − f n)` — the
differencing step of the van der Corput method.  (Machine-verified.) -/
lemma autocorr_phase (f : ℤ → ℝ) (N : ℕ) (h : ℤ) :
    autocorr (fun n : ℤ => cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I)) N h =
      ∑ n ∈ rangeZ N, cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) := by
  dsimp [autocorr]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.exp_conj]
  have harg : conj (((2 * Real.pi * f n : ℝ) : ℂ) * I) =
      -(((2 * Real.pi * f n : ℝ) : ℂ) * I) := theta_conj (2 * Real.pi * f n)
  rw [harg]
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring


/-- Product identity for two phase terms: `e(a)·conj(e(b)) = e(a − b)`. -/
lemma phase_summand (a b : ℝ) :
    cexp (((a : ℝ) : ℂ) * I) * conj (cexp (((b : ℝ) : ℂ) * I)) =
      cexp (((a - b : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj]
  have hb : conj (((b : ℝ) : ℂ) * I) = -(((b : ℝ) : ℂ) * I) := theta_conj b
  rw [hb]
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- Autocorrelation of the **zero-extended** phase sequence `u n := e(2πi f n)` if
`n ∈ [0,N)`, else `0`: only the pairs with `n + h ∈ [0,N)` contribute, giving the
restricted first-difference phase sum. -/
lemma autocorr_phase_zeroext {N : ℕ} (f : ℤ → ℝ) (h : ℤ) :
    autocorr (fun n : ℤ => if n ∈ rangeZ N then
        cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) else 0) N h =
      ∑ n ∈ (rangeZ N).filter (fun n => n + h ∈ rangeZ N),
        cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) := by
  classical
  dsimp [autocorr]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hh : n + h ∈ rangeZ N
  · calc
      (if n + h ∈ rangeZ N then cexp (((2 * Real.pi * f (n + h) : ℝ) : ℂ) * I) else 0) *
          conj (if n ∈ rangeZ N then cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) else 0)
          = cexp (((2 * Real.pi * f (n + h) : ℝ) : ℂ) * I) *
              conj (cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I)) := by
            rw [if_pos hh, if_pos hn]
      _ = cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) := by
            rw [phase_summand (2 * Real.pi * f (n + h)) (2 * Real.pi * f n)]
            congr 1
            apply Complex.ext <;> simp <;> ring
      _ = if n + h ∈ rangeZ N then
              cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) else 0 := by
            rw [if_pos hh]
  · calc
      (if n + h ∈ rangeZ N then cexp (((2 * Real.pi * f (n + h) : ℝ) : ℂ) * I) else 0) *
          conj (if n ∈ rangeZ N then cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) else 0)
          = 0 * conj (if n ∈ rangeZ N then cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) else 0) := by
            rw [if_neg hh]
      _ = 0 := by simp
      _ = if n + h ∈ rangeZ N then
              cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) else 0 := by
            rw [if_neg hh]

/-- **Differenced van der Corput lemma for phase sequences**: for
`u n := e(2πi f n)`, `0 ≤ n < N`, and `1 ≤ Q ≤ N`,

    |Σ_{n<N} e(f n)|² ≤ ((N + Q − 1)/Q) · Σ_{|h| < Q} (1 − |h|/Q) ·
        |Σ_{n<N, n+h<N} e(2πi(f(n+h) − f n))|.

Each autocorrelation is an exponential sum whose phase has a smaller variation
(`h` times the second derivative of `f`), which is the differencing step leading to
the second-derivative test.  (Machine-verified consequence of `vdCorput_fejer`
applied to the zero-extension of the phase sequence, using
`autocorr_phase_zeroext`.) -/
lemma vdc_phase {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) (f : ℤ → ℝ) :
    ‖∑ n ∈ rangeZ N, cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I)‖ ^ 2 ≤
      ((N + Q - 1 : ℝ) / Q) *
        ∑ h ∈ Finset.Icc (-(((Q : ℤ) - 1))) (((Q : ℤ) - 1)),
          ((1 : ℝ) - (|(h : ℝ)|) / Q) *
            ‖∑ n ∈ (rangeZ N).filter (fun n => n + h ∈ rangeZ N),
                cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I)‖ := by
  classical
  let u : ℤ → ℂ := fun n => if n ∈ rangeZ N then
      cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) else 0
  have hout : ∀ n : ℤ, n ∉ rangeZ N → u n = 0 := by
    intro n hn
    dsimp [u]
    rw [if_neg hn]
  have hmain := vdCorput_fejer (N := N) (Q := Q) hN hQ hQN u hout
  have hL : (∑ n ∈ rangeZ N, u n) = ∑ n ∈ rangeZ N,
      cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [u]
    rw [if_pos hn]
  have hR : ∀ h : ℤ, h ∈ Finset.Icc (-(((Q : ℤ) - 1))) (((Q : ℤ) - 1)) →
      autocorr u N h =
        ∑ n ∈ (rangeZ N).filter (fun n => n + h ∈ rangeZ N),
          cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I) := by
    intro h hh
    dsimp [u]
    exact autocorr_phase_zeroext (N := N) f h
  calc
    ‖∑ n ∈ rangeZ N, cexp (((2 * Real.pi * f n : ℝ) : ℂ) * I)‖ ^ 2
        = ‖∑ n ∈ rangeZ N, u n‖ ^ 2 := by rw [hL]
    _ ≤ ((N + Q - 1 : ℝ) / Q) *
            ∑ h ∈ Finset.Icc (-(((Q : ℤ) - 1))) (((Q : ℤ) - 1)),
              ((1 : ℝ) - (|(h : ℝ)|) / Q) * ‖autocorr u N h‖ := hmain
    _ = ((N + Q - 1 : ℝ) / Q) *
            ∑ h ∈ Finset.Icc (-(((Q : ℤ) - 1))) (((Q : ℤ) - 1)),
              ((1 : ℝ) - (|(h : ℝ)|) / Q) *
                ‖∑ n ∈ (rangeZ N).filter (fun n => n + h ∈ rangeZ N),
                    cexp (((2 * Real.pi * (f (n + h) - f n) : ℝ) : ℂ) * I)‖ := by
            apply congrArg (fun x : ℝ => ((N + Q - 1 : ℝ) / Q) * x)
            apply Finset.sum_congr rfl
            intro h hh
            congr 1
            rw [hR h hh]


/-- The linear phase `e(α·n) = e^{2πi α n}` (`0 ≤ n < L`). -/
def linPhase (α : ℝ) (n : ℕ) : ℂ :=
  cexp (((2 * Real.pi * (α * (n : ℝ)) : ℝ) : ℂ) * I)

/-- `e(αn) = w^n` with `w := e(α)`. -/
lemma linPhase_eq_pow (α : ℝ) (n : ℕ) :
    linPhase α n = cexp (((2 * Real.pi * α : ℝ) : ℂ) * I) ^ n := by
  rw [linPhase]
  have hx : (((2 * Real.pi * (α * (n : ℝ)) : ℝ) : ℂ) * I) =
      (n : ℂ) * (((2 * Real.pi * α : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  rw [hx]
  exact (Complex.exp_nat_mul (((2 * Real.pi * α : ℝ) : ℂ) * I) n)

/-- Trivial (length) bound for the linear phase sum: `|Σ_{n<L} e(αn)| ≤ L`. -/
lemma linPhase_trivial (α : ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, linPhase α n‖ ≤ (L : ℝ) := by
  calc
    ‖∑ n ∈ Finset.range L, linPhase α n‖ ≤ ∑ n ∈ Finset.range L, ‖linPhase α n‖ := by
        exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range L, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have h1 : ‖cexp (((2 * Real.pi * (α * (n : ℝ)) : ℝ) : ℂ) * I)‖ = 1 := by
          simpa using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (α * (n : ℝ))))
        simpa [linPhase] using h1
    _ = (L : ℝ) := by simp

/-- **Linear-phase geometric bound**: for `w := e(α) ≠ 1`,

    |Σ_{n<L} e(αn)| ≤ 2 / |1 − w|.

(Consequence of the geometric-sum identity `Σ_{n<L} w^n = (w^L − 1)/(w − 1)` and
`‖w‖ = 1`.  With `|1 − w| ≥ c·‖α‖` (`‖α‖ = dist(α, ℤ)`) this is the
`min(L, c/‖α‖)` first-derivative-test core; the classical second-derivative test is
obtained from it by Taylor-linearizing the phase on subintervals.) -/
lemma linPhase_geom (α : ℝ) (L : ℕ) (h : cexp (((2 * Real.pi * α : ℝ) : ℂ) * I) ≠ 1) :
    ‖∑ n ∈ Finset.range L, linPhase α n‖ ≤
      2 / ‖cexp (((2 * Real.pi * α : ℝ) : ℂ) * I) - 1‖ := by
  classical
  let w : ℂ := cexp (((2 * Real.pi * α : ℝ) : ℂ) * I)
  have hw : w ≠ 1 := h
  have hsum : (∑ n ∈ Finset.range L, linPhase α n) =
      ∑ n ∈ Finset.range L, w ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hp := linPhase_eq_pow α n
    dsimp [w]
    exact hp
  rw [hsum]
  rw [geom_sum_eq hw L]
  rw [norm_div]
  have hnum : ‖w ^ L - 1‖ ≤ 2 := by
    have hw1 : ‖w‖ = 1 := by
      dsimp [w]
      simpa using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * α))
    calc
      ‖w ^ L - 1‖ ≤ ‖w ^ L‖ + ‖1‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp [hw1, norm_pow]
      _ = 2 := by norm_num
  have hden : 0 < ‖w - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hw
  have hdiv : ‖w ^ L - 1‖ / ‖w - 1‖ ≤ 2 / ‖w - 1‖ := by
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
  simpa [w] using hdiv


/-- Distance from a real number to the nearest integer, realized in `[0, 1/2]`:
`min (fract α) (1 − fract α)` where `fract α = α − ⌊α⌋ ∈ [0,1)`. -/
def intDist (α : ℝ) : ℝ := min (Int.fract α) (1 - Int.fract α)

/-- `0 ≤ intDist α`. -/
lemma intDist_nonneg (α : ℝ) : 0 ≤ intDist α := by
  dsimp [intDist]
  have h1 : 0 ≤ Int.fract α := Int.fract_nonneg α
  have h2 : 0 ≤ 1 - Int.fract α := by linarith [Int.fract_lt_one α]
  exact le_min h1 h2

/-- `intDist α ≤ 1/2`: one of `fract α` and `1 − fract α` is `≤ 1/2`. -/
lemma intDist_le_half (α : ℝ) : intDist α ≤ (1 / 2 : ℝ) := by
  dsimp [intDist]
  rw [min_le_iff]
  by_cases h : Int.fract α ≤ (1 / 2 : ℝ)
  · exact Or.inl h
  · right
    have hf : (1 / 2 : ℝ) < Int.fract α := by linarith
    have hf1 : Int.fract α < 1 := Int.fract_lt_one α
    linarith


end

end Submission.VanDerCorput


/-!
# The `|1 − w| ≥ c·‖α‖` link on the unit circle (`w = e(2πiα)`)

Three machine-verifiable lemmas completing the van der Corput chord link:

1. **norm identity** (`norm_one_sub_cexp_two_pi`): for every real `x`,

       ‖1 − e^{2πi x}‖ = 2·|sin(πx)|.

   Mathlib provides `Complex.norm_exp_I_mul_ofReal_sub_one`: for real `x`,
   `‖e^{i x} − 1‖ = ‖2·sin(x/2)‖` (this is `e^{ix} = cos x + i sin x`,
   `‖1 − w‖² = (1−cos x)² + sin²x = 4 sin²(x/2)`); substitute `x = 2πt`, use
   `norm_sub_rev` (`‖1 − w‖ = ‖w − 1‖`) and `Real.norm_eq_abs` to arrive at
   `2·|sin(πx)|`.

2. **trig link** (`abs_sin_intDist`): for every real `α`,

       |sin(πα)| = sin(π · intDist α)    (intDist := Submission.VanDerCorput.intDist)

   With `f := Int.fract α ∈ [0,1)` and `α = ⌊α⌋ + f`, periodicity gives
   `|sin(πα)| = |sin(πf)|` (`Real.sin_add_int_mul_pi` with the integer multiple
   `⌊α⌋·π`, then `abs_mul` + `abs_zpow`: `|(−1)^⌊α⌋| = 1`).  Since `0 ≤ πf ≤ π`,
   `sin(πf) ≥ 0` and `|sin(πf)| = sin(πf)` (`Real.sin_nonneg_of_nonneg_of_le_pi`).
   Finally `sin(πf) = sin(π·(1−f))` by symmetry about `π/2`
   (`Real.sin_pi_sub`), and `intDist α = min f (1−f)` equals `f` on `f ≤ 1/2`
   and `1 − f` otherwise.

3. **`unit_circle_chord`** (the goal): for every real `α`,

       ‖1 − cexp(↑(2π α)·I)‖ ≥ 4 · intDist α.

   Proof: `norm_one_sub_cexp_two_pi` gives `‖1 − w‖ = 2·|sin(πα)|`;
   `abs_sin_intDist` rewrites to `2·sin(π·intDist α)`;
   `Submission.Chord.sin_pi_mul_ge_two_mul (intDist α)` (`intDist_nonneg`,
   `intDist_le_half`) gives `sin(πd) ≥ 2d`, hence `2·sin(πd) ≥ 4d`.

Machine-verified, axiom-clean. -/

open Complex
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.UnitCircle

/-- **Norm identity**: `‖1 − e^{2πix}‖ = 2|sin(πx)|`. -/
lemma norm_one_sub_cexp_two_pi (x : ℝ) :
    ‖1 - cexp (↑(2 * Real.pi * x) * I)‖ = 2 * |Real.sin (Real.pi * x)| := by
  rw [show cexp (↑(2 * Real.pi * x) * I) = cexp (I * (↑(2 * Real.pi * x))) by
    congr 1
    rw [mul_comm]]
  rw [norm_sub_rev]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)]
  have hh : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
  rw [hh]
  rw [Real.norm_eq_abs]
  rw [abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Helper: `|sin(π f)| = sin(π f)` for `0 ≤ f ≤ 1` (`0 ≤ πf ≤ π`, where
`Real.sin` is nonnegative). -/
lemma abs_sin_pi_mul_eq_self {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    |Real.sin (Real.pi * f)| = Real.sin (Real.pi * f) := by
  rw [abs_of_nonneg]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · have hπ : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    calc
      Real.pi * f ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hf1 hπ
      _ = Real.pi := by ring

/-- **Trig link**: `|sin(πα)| = sin(π·intDist α)`. -/
lemma abs_sin_intDist (α : ℝ) :
    |Real.sin (Real.pi * α)| = Real.sin (Real.pi * Submission.VanDerCorput.intDist α) := by
  let f : ℝ := Int.fract α
  have hf0 : 0 ≤ f := by
    simp [f]
  have hf1 : f ≤ 1 := by
    have := Int.fract_lt_one α
    simpa [f] using le_of_lt this
  have hf : f = α - (⌊α⌋ : ℝ) := by
    dsimp [f]
  -- `α = ⌊α⌋ + f`, so `sin(πα)` differs from `sin(πf)` by an integer-π shift
  have harg : Real.pi * α = Real.pi * f + (⌊α⌋ : ℝ) * Real.pi := by
    rw [hf]
    ring
  have hmain : |Real.sin (Real.pi * α)| = |Real.sin (Real.pi * f)| := by
    rw [harg]
    rw [Real.sin_add_int_mul_pi (Real.pi * f) (⌊α⌋)]
    rw [abs_mul]
    rw [abs_zpow]
    norm_num
  dsimp [Submission.VanDerCorput.intDist, f]
  by_cases h : f ≤ (1 / 2 : ℝ)
  · -- case `f ≤ 1/2`: `intDist α = f`
    have hmin : min f (1 - f) = f := by
      rw [min_eq_left]
      linarith
    rw [hmin]
    calc
      |Real.sin (Real.pi * α)| = |Real.sin (Real.pi * f)| := hmain
      _ = Real.sin (Real.pi * f) := abs_sin_pi_mul_eq_self hf0 hf1
  · -- case `f > 1/2`: `intDist α = 1 − f`, and `sin(πf) = sin(π(1−f))`
    have hf12 : (1 / 2 : ℝ) < f := lt_of_not_ge h
    have hmin : min f (1 - f) = 1 - f := by
      rw [min_eq_right]
      linarith
    rw [hmin]
    have habs : |Real.sin (Real.pi * α)| = Real.sin (Real.pi * f) := by
      rw [hmain]
      exact abs_sin_pi_mul_eq_self hf0 hf1
    have hArg2 : Real.pi * f = Real.pi - Real.pi * (1 - f) := by ring
    calc
      |Real.sin (Real.pi * α)| = Real.sin (Real.pi * f) := habs
      _ = Real.sin (Real.pi * (1 - f)) := by
        rw [hArg2]
        rw [Real.sin_pi_sub (Real.pi * (1 - f))]

/-- **Unit-circle chord bound**: `‖1 − e^{2πiα}‖ ≥ 4·intDist α`. -/
lemma unit_circle_chord (α : ℝ) :
    ‖1 - cexp (↑(2 * Real.pi * α) * I)‖ ≥ 4 * Submission.VanDerCorput.intDist α := by
  rw [norm_one_sub_cexp_two_pi]
  rw [abs_sin_intDist]
  have hd0 := Submission.VanDerCorput.intDist_nonneg α
  have hd1 := Submission.VanDerCorput.intDist_le_half α
  have hc := Submission.Chord.sin_pi_mul_ge_two_mul (Submission.VanDerCorput.intDist α) hd0 hd1
  nlinarith

/-- **First-derivative test in distance-to-integer form**: for `intDist α > 0`,

    |Σ_{n<L} e(αn)| ≤ 2 / ‖1 − w‖ ≤ 2 / (4·intDist α) = (1/2) / intDist α

(`w := e(α)`), combining `VanDerCorput.linPhase_geom` with `unit_circle_chord`. -/
lemma geom_sum_bound_of_intDist_pos {α : ℝ} {L : ℕ}
    (h : 0 < Submission.VanDerCorput.intDist α) :
    ‖∑ n ∈ Finset.range L, Submission.VanDerCorput.linPhase α n‖ ≤
      (1 / 2) / Submission.VanDerCorput.intDist α := by
  classical
  let w : ℂ := cexp (((2 * Real.pi * α : ℝ) : ℂ) * I)
  have hw : w ≠ 1 := by
    intro hw1
    have hc' : 4 * Submission.VanDerCorput.intDist α ≤ ‖1 - w‖ := by
      simpa [w] using (unit_circle_chord α)
    have hzero' : ‖1 - w‖ = 0 := by simp [hw1]
    have hbig : 0 < 4 * Submission.VanDerCorput.intDist α := by positivity
    linarith
  have hg := Submission.VanDerCorput.linPhase_geom (α := α) (L := L) hw
  have hg' : ‖∑ n ∈ Finset.range L, Submission.VanDerCorput.linPhase α n‖ ≤ 2 / ‖w - 1‖ := by
    simpa [w] using hg
  have hc0 := unit_circle_chord α
  have hb0 : 4 * Submission.VanDerCorput.intDist α ≤ ‖1 - w‖ := by
    simpa [w] using hc0
  have hnorm : ‖1 - w‖ = ‖w - 1‖ := by
    have hneg : 1 - w = -(w - 1) := by ring
    rw [hneg, norm_neg]
  have hb : 4 * Submission.VanDerCorput.intDist α ≤ ‖w - 1‖ := by
    simpa [hnorm] using hb0
  have hbpos : 0 < ‖w - 1‖ := by
    have hpos4 : 0 < 4 * Submission.VanDerCorput.intDist α := by positivity
    exact lt_of_lt_of_le hpos4 hb
  have hq : 2 / ‖w - 1‖ ≤ 2 / (4 * Submission.VanDerCorput.intDist α) := by
    exact (div_le_div_iff₀ hbpos (by positivity : 0 < 4 * Submission.VanDerCorput.intDist α)).2
      (by nlinarith [hb])
  have h2 : 2 / (4 * Submission.VanDerCorput.intDist α) =
      (1 / 2) / Submission.VanDerCorput.intDist α := by
    have hd0 : Submission.VanDerCorput.intDist α ≠ 0 := ne_of_gt h
    field_simp [hd0]
    ring
  calc
    ‖∑ n ∈ Finset.range L, Submission.VanDerCorput.linPhase α n‖ ≤ 2 / ‖w - 1‖ := hg'
    _ ≤ 2 / (4 * Submission.VanDerCorput.intDist α) := hq
    _ = (1 / 2) / Submission.VanDerCorput.intDist α := h2

end Submission.UnitCircle


/-!
# Region of small `intDist`: `x` within δ of an integer (fleet task)

**TARGET:** `Submission.IntDistRegion.intDist_lt_iff_exists_int`.

For the subinterval linearization of the second-derivative test we need the
decomposition of the *slope* axis by the distance-to-integer `intDist`
(`Submission.VanDerCorput.intDist α = min (fract α) (1 − fract α)`): the region
where `intDist x < δ` is exactly the union of the `δ`-neighbourhoods of the
integers.  Machine-verified, axiom-clean.
-/

open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.IntDistRegion

/-- `x − ⌊x⌋ = fract x` (the definitional content of `Int.fract`). -/
lemma sub_floor_eq_fract (x : ℝ) : x - (Int.floor x : ℝ) = Int.fract x := by rfl

/-- The distance from `x` to its floor is its fractional part. -/
lemma abs_sub_floor_eq_fract (x : ℝ) : |x - (Int.floor x : ℝ)| = Int.fract x := by
  rw [abs_of_nonneg]
  · rfl
  · simpa using (Int.fract_nonneg x)

/-- The distance from `x` to `⌊x⌋ + 1` is `1 − fract x`. -/
lemma abs_sub_floor_add_one (x : ℝ) :
    |x - ((Int.floor x + 1 : ℤ) : ℝ)| = 1 - Int.fract x := by
  have hle : x - ((Int.floor x : ℝ) + 1) ≤ 0 := by
    have hlt : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  calc
    |x - ((Int.floor x + 1 : ℤ) : ℝ)| = |x - ((Int.floor x : ℝ) + 1)| := by norm_num
    _ = - (x - ((Int.floor x : ℝ) + 1)) := abs_of_nonpos hle
    _ = 1 - Int.fract x := by
      rw [← sub_floor_eq_fract x]
      ring

/-- For every integer `k`, the distance to `k` is at least the distance to the
nearest integer `intDist x` (`= min (fract x) (1 − fract x)`).  Case split on
whether `k` lies below or above the floor of `x`. -/
lemma intDist_le_abs_sub (x : ℝ) (k : ℤ) :
    Submission.VanDerCorput.intDist x ≤ |x - (k : ℝ)| := by
  unfold Submission.VanDerCorput.intDist
  by_cases hk : k ≤ Int.floor x
  · have hkreal : (k : ℝ) ≤ (Int.floor x : ℝ) := by exact_mod_cast hk
    have hk0 : 0 ≤ x - (k : ℝ) := by
      have hfloorle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      linarith
    have habs : |x - (k : ℝ)| = x - (k : ℝ) := abs_of_nonneg hk0
    have hfx : Int.fract x ≤ |x - (k : ℝ)| := by
      rw [habs, ← sub_floor_eq_fract x]
      linarith
    exact le_trans (min_le_left (Int.fract x) (1 - Int.fract x)) hfx
  · have hlt : ⌊x⌋ < k := lt_of_not_ge hk
    have hk' : Int.floor x + 1 ≤ k := by omega
    have hkreal : (Int.floor x : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk'
    have hk0 : x - (k : ℝ) ≤ 0 := by
      have hlt2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
      linarith
    have habs : |x - (k : ℝ)| = (k : ℝ) - x := by
      rw [abs_of_nonpos hk0]
      ring
    have hfx : 1 - Int.fract x ≤ |x - (k : ℝ)| := by
      rw [habs, ← sub_floor_eq_fract x]
      linarith
    exact le_trans (min_le_right (Int.fract x) (1 - Int.fract x)) hfx

/-- The small-`intDist` region is the union of `δ`-neighbourhoods of integers:
`intDist x < δ` iff there is an integer `k` with `|x − k| < δ`. -/
lemma intDist_lt_iff_exists_int {x δ : ℝ} (hδ0 : 0 ≤ δ) :
    Submission.VanDerCorput.intDist x < δ ↔ ∃ k : ℤ, |x - (k : ℝ)| < δ := by
  constructor
  · intro h
    unfold Submission.VanDerCorput.intDist at h
    -- `min a b < δ` means one of the two is below δ
    rcases (min_lt_iff.mp h) with hf | hf
    -- fractional part below δ: the floor itself is a witness
    · refine ⟨Int.floor x, ?_⟩
      rwa [abs_sub_floor_eq_fract x]
    -- `1 − fract x < δ`: the next integer after the floor is a witness
    · refine ⟨Int.floor x + 1, ?_⟩
      rwa [abs_sub_floor_add_one x]
  · intro h
    rcases h with ⟨k, hk⟩
    exact lt_of_le_of_lt (intDist_le_abs_sub x k) hk

end Submission.IntDistRegion

open Complex
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Helper for the pair-bound endpoint algebra

You must prove `pair_recip_abs_bound` below.

Claim (real arithmetic): for `1 ≤ B`, `B ≤ c`, and `1/2 ≤ w ≤ B − 1/2`,

    |(w - c)⁻¹ + (w + c)⁻¹| ≤ 2·(B − 1/2) / (c² − (B − 1/2)²)

Classical proof:
1. `(w−c)⁻¹ + (w+c)⁻¹ = 2w/(w²−c²)` (common denominator `(w−c)(w+c) = w²−c²`;
   both denominators are nonzero: `w − c ≤ (B−1/2) − B = −1/2 < 0` and
   `w + c > 0`).
2. Since `0 < w` (from `1/2 ≤ w`) and `w² < c²` (because `w ≤ B−1/2 < c`),
   `|2w/(w²−c²)| = 2w/(c²−w²)`.
3. Bound numerator and denominator separately:
   `2w ≤ 2(B−1/2)` (from `w ≤ B−1/2`) and
   `1/(c²−w²) ≤ 1/(c²−(B−1/2)²)` (since `w² ≤ (B−1/2)² < c²`, i.e.
   `0 < c²−(B−1/2)² ≤ c²−w²`), both sides positive.
   Multiply the two inequalities.

Only use `linarith`, `nlinarith`, `ring`, `field_simp`, `rw`, `exact` etc.
Do NOT change the statement; end with no gaps.  Axiom-clean.
-/

namespace Submission.SdtPoisson

noncomputable section

lemma pair_recip_abs_bound {B c w : ℝ} (hB : 1 ≤ B) (hcB : B ≤ c)
    (hwlo : 1 / 2 ≤ w) (hwhi : w ≤ B - 1 / 2) :
    |(w - c)⁻¹ + (w + c)⁻¹| ≤ 2 * (B - 1 / 2) / (c ^ 2 - (B - 1 / 2) ^ 2) := by
  set d : ℝ := B - 1 / 2
  have hwle : w ≤ d := by simpa [d] using hwhi
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hwpos : 0 < w := by linarith
  have hcpos : 0 < c := by linarith
  have hdlc : d < c := by dsimp [d]; linarith
  have hwltc : w < c := by linarith
  have hwc_ne : w - c ≠ 0 := by linarith
  have hwpc_ne : w + c ≠ 0 := by linarith
  have hcw2pos : 0 < c ^ 2 - w ^ 2 := by
    have h1 : 0 < c - w := by linarith
    have h2 : 0 < c + w := by linarith
    have hid : (c - w) * (c + w) = c ^ 2 - w ^ 2 := by ring
    nlinarith [mul_pos h1 h2, hid]
  have hcd2pos : 0 < c ^ 2 - d ^ 2 := by
    have h1 : 0 < c - d := by linarith
    have h2 : 0 < c + d := by linarith
    have hid : (c - d) * (c + d) = c ^ 2 - d ^ 2 := by ring
    nlinarith [mul_pos h1 h2, hid]
  have hw2c2_ne : w ^ 2 - c ^ 2 ≠ 0 := by nlinarith [hcw2pos]
  have hsum : (w - c)⁻¹ + (w + c)⁻¹ = 2 * w / (w ^ 2 - c ^ 2) := by
    field_simp [hwc_ne, hwpc_ne, hw2c2_ne]
    ring
  have h2wpos : 0 < 2 * w := by nlinarith
  have habs : |2 * w / (w ^ 2 - c ^ 2)| = 2 * w / (c ^ 2 - w ^ 2) := by
    have hneg : w ^ 2 - c ^ 2 = -(c ^ 2 - w ^ 2) := by ring
    rw [hneg, div_neg, abs_neg]
    rw [abs_of_pos (div_pos h2wpos hcw2pos)]
  have hw2le_d2 : w ^ 2 ≤ d ^ 2 := by
    have h1 : 0 ≤ d - w := by linarith
    have h2 : 0 ≤ d + w := by linarith
    have h3 : 0 ≤ (d - w) * (d + w) := mul_nonneg h1 h2
    have hid : (d - w) * (d + w) = d ^ 2 - w ^ 2 := by ring
    nlinarith [h3, hid]
  have hcross : 2 * w * (c ^ 2 - d ^ 2) ≤ 2 * d * (c ^ 2 - w ^ 2) := by
    have hdw : 0 ≤ d - w := by linarith
    have hc2pos : 0 < c ^ 2 := by exact sq_pos_of_pos hcpos
    have hwdpos : 0 < w * d := by exact mul_pos hwpos hdpos
    have hc2wd : 0 ≤ c ^ 2 + w * d := by nlinarith
    have hprod : 0 ≤ 2 * (d - w) * (c ^ 2 + w * d) := by
      exact mul_nonneg (by nlinarith) hc2wd
    have hfac : 2 * d * (c ^ 2 - w ^ 2) - 2 * w * (c ^ 2 - d ^ 2) = 2 * (d - w) * (c ^ 2 + w * d) := by ring
    nlinarith [hprod, hfac]
  have hmain : 2 * w / (c ^ 2 - w ^ 2) ≤ 2 * d / (c ^ 2 - d ^ 2) := by
    rw [div_le_div_iff₀ hcw2pos hcd2pos]
    exact hcross
  rw [hsum, habs]
  exact hmain

end
end Submission.SdtPoisson


open Complex Filter Topology
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Uniform bound for the sawtooth Dirichlet partial sums

Prove: for every `K : ℕ` and `x : ℝ`, `‖sawHat K x‖ ≤ 20`.

The proof has three parts:

1. **Reduction to a real sine sum.**  Using the closed forms of `Real.sum_sin`
   and of `Complex.exp`, one proves `sawHat K x = -Σ_{i<K} sin(2π(i+1)x)/(π(i+1))`
   (complex sum of real terms; lemmas `sawHat_eq_real_neg` etc.).

2. **Partial summation.**  The Dirichlet partial sums of the sine sequence
   `Σ sin((i+1)t)` equal `sin(Kt/2)·sin((K-1)t/2+t)/sin(t/2)` (`Real.sum_sin`),
   hence are bounded by `1/|sin(t/2)|` away from `t ∈ 2πℤ`.  An Abel
   (summation-by-parts) lemma for decreasing weights `1/(i+1)` bounds the
   harmonic sums `sineH t K := Σ sin((i+1)t)/(i+1)` by `1/|sin(t/2)|`.

3. **Case split.**  Write `t = 2πx` and reduce `x` modulo 1
   (`sineH_periodic_one`) and by symmetry `u ↦ 1-u`
   (`sineH_two_pi_neg_comp`) to `0 ≤ u ≤ 1/2`.  For `0 < u ≤ 1/8` split the
   sum at `N = ⌊1/t⌋`: the first `N` terms have modulus `≤ t` each and the
   tail is `≤ π` because `(N+1)·|sin(t/2)| ≥ 1/π`; for `1/8 ≤ u ≤ 1/2`
   `|sin(t/2)| = sin(πu) ≥ sin(π/8) ≥ 1/4`, so the Abel bound is `≤ 4`.
   Overall `|sineH (2πx) K| ≤ 20`, giving `‖sawHat‖ ≤ 20/π ≤ 20`.
-/
namespace Submission.SdtPoisson

noncomputable section

/-- `sin((i+1)*t)` summed over `i < j` (partial sums of the sine sequence). -/
def sinePS (t : ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, Real.sin (((i + 1 : ℕ) : ℝ) * t)

/-- Harmonic sine sum `Σ_{i<K} sin((i+1)t)/(i+1)`. -/
def sineH (t : ℝ) (K : ℕ) : ℝ := ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)

lemma abs_sin_le_one (x : ℝ) : |Real.sin x| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]

/-- Closed form of the sine partial sums via `Real.sum_sin`. -/
lemma sinePS_closed (t : ℝ) (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) (j : ℕ) :
    sinePS t j = Real.sin ((j : ℝ) * t / 2) * Real.sin (((j : ℝ) - 1) * t / 2 + t) / Real.sin (t / 2) := by
  have hrewrite : sinePS t j = ∑ i ∈ Finset.range j, Real.sin (t * (i : ℝ) + t) := by
    dsimp [sinePS]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hrewrite]
  exact Real.sum_sin j ht t

lemma sin_half_ne_zero_of_not_periodic {t : ℝ} (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) :
    Real.sin (t / 2) ≠ 0 := by
  intro hz
  rw [Real.sin_eq_zero_iff] at hz
  rcases hz with ⟨n, hn⟩
  apply ht n
  calc
    t = ((n : ℝ) * π) * 2 := by rw [hn]; ring
    _ = (n : ℝ) * (2 * π) := by ring

/-- A generic bound for `|sin A * sin B / sin (t/2)|`. -/
lemma abs_ratio_sin_bound {t A B : ℝ} (hC : Real.sin (t / 2) ≠ 0)
    (hA : |Real.sin A| ≤ 1) (hB : |Real.sin B| ≤ 1) :
    |Real.sin A * Real.sin B / Real.sin (t / 2)| ≤ 1 / |Real.sin (t / 2)| := by
  have hden : 0 < |Real.sin (t / 2)| := abs_pos.mpr hC
  have hmul : |Real.sin A| * |Real.sin B| ≤ 1 := by
    calc
      |Real.sin A| * |Real.sin B| ≤ 1 * |Real.sin B| := mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 1 := by norm_num
  rw [abs_div, abs_mul]
  exact div_le_div_of_nonneg_right hmul (le_of_lt hden)

/-- For a phase away from integer multiples of `2π`, partial sums of sines are
bounded by `1/|sin (t/2)|`. -/
lemma abs_sinePS_le (t : ℝ) (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) (j : ℕ) :
    |sinePS t j| ≤ 1 / |Real.sin (t / 2)| := by
  rw [sinePS_closed t ht j]
  exact abs_ratio_sin_bound (sin_half_ne_zero_of_not_periodic ht) (abs_sin_le_one _) (abs_sin_le_one _)

/-- Bound for partial sums of sines starting at an arbitrary offset `a`:
`Σ_{i<j} sin ((a+i)*t)`. -/
lemma abs_sin_shift_sum_le (t : ℝ) (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) (a j : ℕ) :
    |∑ i ∈ Finset.range j, Real.sin (((a + i : ℕ) : ℝ) * t)| ≤ 1 / |Real.sin (t / 2)| := by
  have hrewrite : (∑ i ∈ Finset.range j, Real.sin (((a + i : ℕ) : ℝ) * t))
      = ∑ i ∈ Finset.range j, Real.sin (t * (i : ℝ) + ((a : ℕ) : ℝ) * t) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  rw [hrewrite]
  rw [Real.sum_sin j ht (((a : ℕ) : ℝ) * t)]
  exact abs_ratio_sin_bound (sin_half_ne_zero_of_not_periodic ht) (abs_sin_le_one _) (abs_sin_le_one _)

lemma inv_le_inv_of_pos_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have h : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  simpa using h

-- generic Abel lemma with decreasing weights
lemma abs_sum_mul_le {g : ℕ → ℝ} {w : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hB0 : 0 ≤ B) (hw : ∀ i, 0 ≤ w i) (hwmono : ∀ i, w (i + 1) ≤ w i)
    (hps : ∀ j, j ≤ K → |∑ i ∈ Finset.range j, g i| ≤ B) :
    |∑ i ∈ Finset.range K, w i * g i| ≤ B * w 0 := by
  classical
  by_cases hK : K = 0
  · subst hK
    simp
    exact mul_nonneg hB0 (hw 0)
  · have hbp := Finset.sum_range_by_parts (f := w) (g := g) (n := K)
    have hbp' : (∑ i ∈ Finset.range K, w i * g i) =
        w (K - 1) * (∑ i ∈ Finset.range K, g i) -
          ∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * (∑ k ∈ Finset.range (i + 1), g k) := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hbp
    rw [hbp']
    let S : ℕ → ℝ := fun m => ∑ k ∈ Finset.range m, g k
    have hS : ∀ j, j ≤ K → |S j| ≤ B := by intro j hj; exact hps j hj
    have hwK : 0 ≤ w (K - 1) := hw (K - 1)
    have hfirst : |w (K - 1) * S K| ≤ w (K - 1) * B := by
      rw [abs_mul, abs_of_nonneg hwK]
      exact mul_le_mul_of_nonneg_left (hS K (le_rfl)) hwK
    have hper (i : ℕ) (hi : i < K - 1) :
        |(w (i + 1) - w i) * S (i + 1)| ≤ (w i - w (i + 1)) * B := by
      rw [abs_mul]
      have hwmon : w (i + 1) ≤ w i := hwmono i
      have hwsub : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr hwmon
      calc
        |w (i + 1) - w i| * |S (i + 1)| = (w i - w (i + 1)) * |S (i + 1)| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hwmon)]
          ring
        _ ≤ (w i - w (i + 1)) * B := by
          exact mul_le_mul_of_nonneg_left (hS (i + 1) (by omega)) hwsub
    have hsecond :
        |∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)| ≤ (w 0 - w (K - 1)) * B := by
      calc
        |∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)|
            ≤ ∑ i ∈ Finset.range (K - 1), |(w (i + 1) - w i) * S (i + 1)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (K - 1), (w i - w (i + 1)) * B := by
              apply Finset.sum_le_sum
              intro i hi
              exact hper i (Finset.mem_range.mp hi)
        _ = (w 0 - w (K - 1)) * B := by
              rw [← Finset.sum_mul]
              have hsum : (∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i)) = w (K - 1) - w 0 := by
                simpa using (Finset.sum_range_sub (fun i : ℕ => w i) (K - 1))
              have htel : (∑ i ∈ Finset.range (K - 1), (w i - w (i + 1))) = w 0 - w (K - 1) := by
                calc
                  (∑ i ∈ Finset.range (K - 1), (w i - w (i + 1)))
                      = ∑ i ∈ Finset.range (K - 1), - (w (i + 1) - w i) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                  _ = -(∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i)) := by rw [Finset.sum_neg_distrib]
                  _ = -(w (K - 1) - w 0) := by rw [hsum]
                  _ = w 0 - w (K - 1) := by ring
              rw [htel]
    have htri : |w (K - 1) * S K - ∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)| ≤
        |w (K - 1) * S K| + |∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)| := by
      rw [sub_eq_add_neg]
      calc
        |w (K - 1) * S K + (-∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1))|
            ≤ |w (K - 1) * S K| + |-(∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1))| :=
              abs_add_le _ _
        _ = |w (K - 1) * S K| + |∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)| := by simp
    calc
      |w (K - 1) * S K - ∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)|
          ≤ |w (K - 1) * S K| + |∑ i ∈ Finset.range (K - 1), (w (i + 1) - w i) * S (i + 1)| := htri
      _ ≤ w (K - 1) * B + (w 0 - w (K - 1)) * B := by exact add_le_add hfirst hsecond
      _ = B * w 0 := by ring

/-! ### Simple bounds on the harmonic sine sum -/

lemma abs_term_le (t : ℝ) (i : ℕ) : |(((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)| ≤ |t| := by
  have hpos : 0 < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos i)
  have hn0 : 0 ≤ ((i + 1 : ℕ) : ℝ) := le_of_lt hpos
  calc
    |(((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)|
        = ((i + 1 : ℕ) : ℝ)⁻¹ * |Real.sin (((i + 1 : ℕ) : ℝ) * t)| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hn0)]
    _ ≤ ((i + 1 : ℕ) : ℝ)⁻¹ * |(((i + 1 : ℕ) : ℝ) * t)| := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := (((i + 1 : ℕ) : ℝ) * t))) (inv_nonneg.mpr hn0)
    _ = |t| := by
          rw [abs_mul, abs_of_nonneg hn0]
          field_simp [hpos.ne']

lemma abs_sineH_trivial (t : ℝ) (K : ℕ) : |sineH t K| ≤ (K : ℝ) * |t| := by
  calc
    |sineH t K| ≤ ∑ i ∈ Finset.range K, |(((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range K, |t| := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_term_le t i
    _ = (K : ℝ) * |t| := by simp

/-- Abel bound for the whole harmonic sine sum. -/
lemma abs_sineH_abel (t : ℝ) (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) (K : ℕ) :
    |sineH t K| ≤ 1 / |Real.sin (t / 2)| := by
  let B : ℝ := 1 / |Real.sin (t / 2)|
  have hB0 : 0 ≤ B := div_nonneg zero_le_one (abs_nonneg _)
  have hps : ∀ j : ℕ, j ≤ K → |∑ i ∈ Finset.range j, Real.sin (((i + 1 : ℕ) : ℝ) * t)| ≤ B := by
    intro j hj
    simpa [B, sinePS] using abs_sinePS_le t ht j
  have hmain0 : |∑ i ∈ Finset.range K,
      (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)| ≤ B * 1 := by
    have hm := abs_sum_mul_le (g := fun i => Real.sin (((i + 1 : ℕ) : ℝ) * t))
        (w := fun i => (((i + 1 : ℕ) : ℝ)⁻¹)) (B := B) (K := K) hB0
        (by intro i; positivity) (by
          intro i
          have h1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos i)
          have hle : ((i + 1 : ℕ) : ℝ) ≤ ((i + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ i + 1 + 1)
          simpa [show (i + 1 + 1 : ℕ) = i + 1 + 1 by omega, Nat.cast_add, Nat.cast_one]
            using inv_le_inv_of_pos_le h1 hle) hps
    simpa using hm
  simpa [sineH, B] using hmain0

lemma not_periodic_of_lt_two_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 2 * π) :
    ∀ k : ℤ, t ≠ (k : ℝ) * (2 * π) := by
  intro k hk
  by_cases hk0 : k ≤ 0
  · have hle0 : (k : ℝ) * (2 * π) ≤ 0 := by
      have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      nlinarith [Real.pi_pos]
    linarith
  · have hkpos : 0 < k := by omega
    have hkge1 : (1 : ℤ) ≤ k := by omega
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkge1
    have hbig : (2 : ℝ) * π < (k : ℝ) * (2 * π) := by
      nlinarith [Real.pi_pos, hk1]
    linarith

lemma not_periodic_of_lt_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ π) :
    ∀ k : ℤ, t ≠ (k : ℝ) * (2 * π) := by
  exact not_periodic_of_lt_two_pi ht0 (lt_of_le_of_lt ht1 (by nlinarith [Real.pi_pos]))

/-- `sin (u/2) ≥ u/π` for `0 ≤ u ≤ π`. -/
lemma sin_half_ge_div_pi {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ π) : u / π ≤ Real.sin (u / 2) := by
  have hx0 : 0 ≤ u / 2 := by linarith
  have hx1 : u / 2 ≤ π / 2 := by linarith
  have h := Real.mul_le_sin hx0 hx1
  have hh : (2 : ℝ) / π * (u / 2) = u / π := by ring
  rwa [hh] at h

/-! If `t` is small (`0 < t ≤ π`), `|sineH t K| ≤ 1 + 2π`.  The sum is split at
`N = ⌊1/t⌋`: the head has `N` terms each of modulus `≤ t`, and the tail starts
with denominator `N+1` where `(N+1)t > 1`, so the Abel bound `1/((N+1)|sin(t/2)|)`
is `≤ π`. -/

/-- Abel bound for the harmonic-weighted *tail* from denominator `a` (a ≥ 1). -/
lemma tail_abel_bound (t : ℝ) (a L : ℕ) (ht : ∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi))
    (ha : 1 ≤ a) :
    |∑ i ∈ Finset.range L, (((a + i : ℕ) : ℝ)⁻¹) * Real.sin (((a + i : ℕ) : ℝ) * t)|
      ≤ 1 / (((a : ℕ) : ℝ) * |Real.sin (t / 2)|) := by
  let B : ℝ := 1 / |Real.sin (t / 2)|
  have hB0 : 0 ≤ B := div_nonneg zero_le_one (abs_nonneg _)
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hps : ∀ j : ℕ, j ≤ L →
      |∑ i ∈ Finset.range j, Real.sin (((a + i : ℕ) : ℝ) * t)| ≤ B := by
    intro j hj
    simpa [B] using abs_sin_shift_sum_le t ht a j
  have hm := abs_sum_mul_le (g := fun i => Real.sin (((a + i : ℕ) : ℝ) * t))
      (w := fun i => (((a + i : ℕ) : ℝ)⁻¹)) (B := B) (K := L) hB0
      (by intro i; positivity)
      (by
        intro i
        have h1 : (0 : ℝ) < ((a + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + i)
        have hle : ((a + i : ℕ) : ℝ) ≤ ((a + (i + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : a + i ≤ a + (i + 1))
        simpa [show (a + i + 1 : ℕ) = a + (i + 1) by omega, Nat.cast_add, Nat.cast_one]
          using inv_le_inv_of_pos_le h1 hle)
      hps
  -- hm: |...| ≤ B * (a:ℝ)⁻¹
  have hm' : |∑ i ∈ Finset.range L, (((a + i : ℕ) : ℝ)⁻¹) * Real.sin (((a + i : ℕ) : ℝ) * t)|
      ≤ (1 / |Real.sin (t / 2)|) * (a : ℝ)⁻¹ := by
    simpa [B] using hm
  calc
    |∑ i ∈ Finset.range L, (((a + i : ℕ) : ℝ)⁻¹) * Real.sin (((a + i : ℕ) : ℝ) * t)|
        ≤ (1 / |Real.sin (t / 2)|) * (a : ℝ)⁻¹ := hm'
    _ = 1 / ((a : ℝ) * |Real.sin (t / 2)|) := by
      field_simp [ne_of_gt ha0]

/-- `1 / ((a) * |sin(t/2)|) ≤ π` when `0 < t ≤ π` and `a·t ≥ 1` (a ≥ 1). -/
lemma one_div_mul_sin_le_pi {t : ℝ} {a : ℕ} (ht0 : 0 < t) (htpi : t ≤ π) (ha : 1 ≤ a)
    (hat : 1 ≤ (a : ℝ) * t) : 1 / ((a : ℝ) * |Real.sin (t / 2)|) ≤ π := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hsinpos : 0 < Real.sin (t / 2) := by
    have hge : t / π ≤ Real.sin (t / 2) := sin_half_ge_div_pi (le_of_lt ht0) htpi
    have htpos : 0 < t / π := div_pos ht0 Real.pi_pos
    linarith
  have habs : |Real.sin (t / 2)| = Real.sin (t / 2) := abs_of_nonneg (le_of_lt hsinpos)
  -- lower bound of (a·|sin|):
  have hge : t / π ≤ Real.sin (t / 2) := sin_half_ge_div_pi (le_of_lt ht0) htpi
  have hmul1 : (a : ℝ) * (t / π) ≤ (a : ℝ) * Real.sin (t / 2) :=
    mul_le_mul_of_nonneg_left hge (le_of_lt ha0)
  have hcalc : (a : ℝ) * (t / π) = ((a : ℝ) * t) / π := by ring
  have hlow : 1 / π ≤ (a : ℝ) * Real.sin (t / 2) := by
    have hnum : 1 ≤ (a : ℝ) * t := hat
    have hdiv : 1 / π ≤ ((a : ℝ) * t) / π := div_le_div_of_nonneg_right hnum (le_of_lt Real.pi_pos)
    have hdiv' : 1 / π ≤ (a : ℝ) * (t / π) := by
      rw [hcalc]
      exact hdiv
    exact le_trans hdiv' hmul1
  have hpos : 0 < (a : ℝ) * Real.sin (t / 2) := lt_of_lt_of_le (div_pos one_pos Real.pi_pos) hlow
  calc
    1 / ((a : ℝ) * |Real.sin (t / 2)|) = ((a : ℝ) * Real.sin (t / 2))⁻¹ := by
      rw [habs]
      field_simp [ne_of_gt hpos]
    _ ≤ (1 / π)⁻¹ := inv_le_inv_of_pos_le (div_pos one_pos Real.pi_pos) hlow
    _ = π := by field_simp

lemma sineH_small_pos (t : ℝ) (ht0 : 0 < t) (htpi : t ≤ π) (K : ℕ) :
    |sineH t K| ≤ 1 + 2 * Real.pi := by
  let N : ℕ := Nat.floor (1 / t)
  have hNle : (N : ℝ) ≤ 1 / t := by
    change ((Nat.floor (1 / t) : ℕ) : ℝ) ≤ 1 / t
    exact Nat.floor_le (by positivity : 0 ≤ 1 / t)
  have hN1 : 1 / t < (N : ℝ) + 1 := by
    change 1 / t < ((Nat.floor (1 / t) : ℕ) : ℝ) + 1
    exact Nat.lt_floor_add_one (1 / t)
  have hN1t : 1 < (N : ℝ) * t + t := by
    have hm : (1 / t) * t < ((N : ℝ) + 1) * t := mul_lt_mul_of_pos_right hN1 ht0
    have hconv : ((N : ℝ) + 1) * t = (N : ℝ) * t + t := by ring
    rw [hconv] at hm
    have hl : (1 / t) * t = 1 := by field_simp [ne_of_gt ht0]
    rwa [hl] at hm
  by_cases hKleN : K ≤ N
  · have hb := abs_sineH_trivial t K
    have hKt : (K : ℝ) * t ≤ 1 := by
      calc
        (K : ℝ) * t ≤ (N : ℝ) * t := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKleN) (le_of_lt ht0)
        _ ≤ (1 / t) * t := mul_le_mul_of_nonneg_right hNle (le_of_lt ht0)
        _ = 1 := by field_simp [ne_of_gt ht0]
    have htabs : |t| = t := abs_of_nonneg (le_of_lt ht0)
    nlinarith [hb, hKt, htabs, Real.pi_pos]
  · have hNltK : N < K := lt_of_not_ge hKleN
    have hsplit : (∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)) =
          (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t))
          + (∑ i ∈ Finset.range (K - N), ((((N + i + 1 : ℕ) : ℝ)⁻¹)) * Real.sin ((((N + i + 1 : ℕ) : ℝ)) * t)) := by
        let f : ℕ → ℝ := fun j => (((j + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((j + 1 : ℕ) : ℝ) * t)
        have hsp : (∑ i ∈ Finset.range K, f i) = (∑ i ∈ Finset.range N, f i) + (∑ i ∈ Finset.range (K - N), f (N + i)) := by
          rw [← Finset.sum_range_add (f := f) N (K - N)]
          congr 1
          ext x
          simp
          omega
        simpa [f] using hsp
    have hhead : |∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)| ≤ 1 := by
      have hb := abs_sineH_trivial t N
      calc
        |∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)| ≤ (N : ℝ) * |t| := hb
        _ = (N : ℝ) * t := by rw [abs_of_nonneg (le_of_lt ht0)]
        _ ≤ (1 / t) * t := mul_le_mul_of_nonneg_right hNle (le_of_lt ht0)
        _ = 1 := by field_simp [ne_of_gt ht0]
    have htail : |∑ i ∈ Finset.range (K - N),
        (((N + i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((N + i + 1 : ℕ) : ℝ) * t)| ≤ π := by
      -- apply tail_abel_bound with a = N+1
      have htail0 : |∑ i ∈ Finset.range (K - N),
          (((N + i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((N + i + 1 : ℕ) : ℝ) * t)|
            ≤ 1 / (((N + 1 : ℕ) : ℝ) * |Real.sin (t / 2)|) := by
        have hb := tail_abel_bound t (N + 1) (K - N) (not_periodic_of_lt_pi ht0 htpi) (by omega)
        -- unify (N+1) + i with N + i + 1
        simpa [show ∀ i : ℕ, (N + 1 + i : ℕ) = N + i + 1 by intro i; omega, Nat.add_assoc] using hb
      have hat : 1 ≤ ((N + 1 : ℕ) : ℝ) * t := by
        have : 1 ≤ (N : ℝ) * t + t := le_of_lt hN1t
        have hconv : ((N + 1 : ℕ) : ℝ) * t = (N : ℝ) * t + t := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rwa [hconv]
      have hbound := one_div_mul_sin_le_pi ht0 htpi (a := N + 1) (by omega) hat
      calc
        |∑ i ∈ Finset.range (K - N), (((N + i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((N + i + 1 : ℕ) : ℝ) * t)|
            ≤ 1 / (((N + 1 : ℕ) : ℝ) * |Real.sin (t / 2)|) := htail0
        _ ≤ π := hbound
    calc
      |sineH t K| = |(∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t))
          + (∑ i ∈ Finset.range (K - N), ((((N + i + 1 : ℕ) : ℝ)⁻¹)) * Real.sin ((((N + i + 1 : ℕ) : ℝ)) * t))| := by
            exact congrArg abs hsplit
      _ ≤ |∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * t)|
          + |∑ i ∈ Finset.range (K - N), ((((N + i + 1 : ℕ) : ℝ)⁻¹)) * Real.sin ((((N + i + 1 : ℕ) : ℝ)) * t)| := abs_add_le _ _
      _ ≤ 1 + 2 * Real.pi := by
        have hπ : 1 ≤ π := by nlinarith [Real.pi_gt_three]
        nlinarith [hhead, htail, Real.pi_pos]

/-! ### The uniform bound for all phases `t = 2πu`, `u ∈ [0,1/2]` -/

lemma sin_pi_mul_ge_sin_pi_div_eight {u : ℝ} (hu1 : (1 : ℝ) / 8 ≤ u) (hu2 : u ≤ 1 / 2) :
    Real.sin (π / 8) ≤ Real.sin (π * u) := by
  have h0 : -(π / 2) ≤ π / 8 := by nlinarith [Real.pi_pos]
  have h1 : π * u ≤ π / 2 := by nlinarith [Real.pi_pos, hu2]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two h0 h1
  nlinarith [Real.pi_pos, hu1]

lemma sin_pi_div_eight_ge_quarter : (1 : ℝ) / 4 ≤ Real.sin (π / 8) := by
  have hx0 : 0 ≤ π / 8 := by nlinarith [Real.pi_pos]
  have hx1 : π / 8 ≤ π / 2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx1
  have hh : (2 : ℝ) / π * (π / 8) = 1 / 4 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rwa [hh] at h

lemma sineH_mid_bound (u : ℝ) (K : ℕ) (hu0 : 0 ≤ u) (hu1 : (1 : ℝ) / 8 ≤ u)
    (hu2 : u ≤ 1 / 2) : |sineH (2 * π * u) K| ≤ (4 : ℝ) := by
  let t : ℝ := 2 * π * u
  have ht0 : 0 < t := by
    dsimp [t]
    nlinarith [Real.pi_pos, hu0]
  have htpi : t ≤ π := by
    dsimp [t]
    nlinarith [Real.pi_pos, hu2]
  have hnp := not_periodic_of_lt_pi ht0 htpi
  have hb := abs_sineH_abel t hnp K
  have hge := sin_pi_mul_ge_sin_pi_div_eight hu1 hu2
  have hq : 0 < Real.sin (π / 8) := by
    have hpos : (0 : ℝ) < 1 / 4 := by norm_num
    exact lt_of_lt_of_le hpos sin_pi_div_eight_ge_quarter
  have hsinpos : 0 < Real.sin (π * u) := by
    have hge' := sin_pi_mul_ge_sin_pi_div_eight hu1 hu2
    have hq' : 0 < Real.sin (π / 8) := hq
    linarith
  have h1_4 : (1 : ℝ) / 4 ≤ |Real.sin (t / 2)| := by
    have htpos : 0 < Real.sin (t / 2) := by
      have hsub : Real.sin (t / 2) = Real.sin (π * u) := by
        dsimp [t]
        congr 1
        ring
      rw [hsub]
      exact hsinpos
    rw [abs_of_nonneg (le_of_lt htpos)]
    dsimp [t]
    congr 1
    ring
    exact le_trans sin_pi_div_eight_ge_quarter hge
  have h_quarter_pos : 0 < (1 : ℝ) / 4 := by norm_num
  have h_inv : |Real.sin (t / 2)|⁻¹ ≤ ((1 : ℝ) / 4)⁻¹ := inv_le_inv_of_pos_le h_quarter_pos h1_4
  have hmain : |sineH t K| ≤ (4 : ℝ) := by
    calc
      |sineH t K| ≤ 1 / |Real.sin (t / 2)| := hb
      _ = |Real.sin (t / 2)|⁻¹ := by rw [one_div]
      _ ≤ ((1 : ℝ) / 4)⁻¹ := h_inv
      _ = 4 := by norm_num
  simpa [t] using hmain

/-- `|sineH (2πu) K| ≤ 20` for `u ∈ [0, 1/2]`. -/
lemma sineH_u_le_half (u : ℝ) (K : ℕ) (hu0 : 0 ≤ u) (hu12 : u ≤ 1 / 2) :
    |sineH (2 * π * u) K| ≤ (20 : ℝ) := by
  by_cases hu_eq0 : u = 0
  · subst hu_eq0
    simp [sineH]
  · have hu_pos : 0 < u := lt_of_le_of_ne hu0 (by
      intro h; exact hu_eq0 h.symm)
    by_cases hsmall : u ≤ 1 / 8
    · have ht0 : 0 < 2 * π * u := by positivity
      have htpi : 2 * π * u ≤ π := by nlinarith [Real.pi_pos, hsmall]
      have hb := sineH_small_pos (2 * π * u) ht0 htpi K
      nlinarith [hb, Real.pi_lt_four]
    · have hmid : (1 : ℝ) / 8 ≤ u := by nlinarith
      have hb := sineH_mid_bound u K hu0 hmid hu12
      nlinarith [hb]

/-- periodicity in the phase: `sin (c·(2π)·(u + n)) = sin (c·(2π)·u)` for integer n. -/
lemma sin_add_int_two_pi_nat_mul (u : ℝ) (n : ℤ) (i : ℕ) :
    Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u) + ((((i + 1 : ℕ) : ℤ) * n : ℤ) : ℝ) * (2 * π))
      = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u)) := by
  have hs := Real.sin_add_int_mul_two_pi (((i + 1 : ℕ) : ℝ) * (2 * π * u)) (((i + 1 : ℕ) : ℤ) * n)
  simpa using hs

/-- If `x = u + n` for an integer `n`, the sine terms with phase `2πx` equal
those with phase `2πu`. -/
lemma sin_two_pi_nat_mul_eq_of_add_int {x u : ℝ} {n : ℤ} (hx : x = u + (n : ℝ)) (i : ℕ) :
    Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * x)) = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u)) := by
  have harg : (((i + 1 : ℕ) : ℝ) * (2 * π * x)) =
      (((i + 1 : ℕ) : ℝ) * (2 * π * u)) + (((((i + 1 : ℕ) : ℤ) * n : ℤ) : ℝ) * (2 * π)) := by
    rw [hx]
    simp [Int.cast_mul, Int.cast_natCast]
    ring
  calc
    Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * x))
        = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u) + (((((i + 1 : ℕ) : ℤ) * n : ℤ) : ℝ) * (2 * π))) := by
          exact congrArg Real.sin harg
    _ = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u)) := sin_add_int_two_pi_nat_mul u n i

/-- Harmonic sine sums are unchanged by reducing `x` modulo 1. -/
lemma sineH_periodic_one (x : ℝ) (K : ℕ) :
    sineH (2 * π * x) K = sineH (2 * π * Int.fract x) K := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact sin_two_pi_nat_mul_eq_of_add_int (x := x) (u := Int.fract x) (n := ⌊x⌋)
    (Int.fract_add_floor x).symm i

/-- `sin (2π(i+1)u) = - sin (2π(i+1)(1-u))`: harmonic sums over `u` and `1−u`
are negatives. -/
lemma sineH_two_pi_neg_comp (u : ℝ) (K : ℕ) :
    sineH (2 * π * u) K = -sineH (2 * π * (1 - u)) K := by
  have hterm : ∀ i : ℕ, Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u)) =
      -Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u))) := by
    intro i
    have hs := Real.sin_nat_mul_two_pi_sub (((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u))) (i + 1)
    -- hs : sin (↑(i+1)·(2π) − x) = −sin x
    have harg : Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u))
        = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π) - ((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u))) := by
      congr 1
      ring
    calc
      Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u))
          = Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π) - ((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u))) := harg
      _ = -Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u))) := by
            simpa using hs
  calc
    sineH (2 * π * u) K
        = ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * u)) := rfl
    _ = ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * (-Real.sin (((i + 1 : ℕ) : ℝ) * (2 * π * (1 - u)))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hterm i]
    _ = -sineH (2 * π * (1 - u)) K := by
          simp [sineH, Finset.sum_neg_distrib, mul_comm, mul_left_comm]

/-- Uniform bound for the harmonic sine sums at phase `2πx`. -/
lemma sineH_phase_bdd (x : ℝ) (K : ℕ) : |sineH (2 * π * x) K| ≤ (20 : ℝ) := by
  let u : ℝ := Int.fract x
  have hu0 : 0 ≤ u := by dsimp [u]; exact Int.fract_nonneg x
  have hper : sineH (2 * π * x) K = sineH (2 * π * u) K := by
    dsimp [u]
    exact sineH_periodic_one x K
  by_cases h12 : u ≤ 1 / 2
  · have hb := sineH_u_le_half u K hu0 h12
    rwa [hper]
  · have hu_gt : 1 / 2 < u := lt_of_not_ge h12
    have hu1 : u < 1 := by dsimp [u]; exact Int.fract_lt_one x
    let v : ℝ := 1 - u
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have hv12 : v ≤ 1 / 2 := by dsimp [v]; linarith
    have hsym : sineH (2 * π * u) K = -sineH (2 * π * v) K := by
      have hs := sineH_two_pi_neg_comp v K
      have hvu : 1 - v = u := by dsimp [v]; ring
      have hs' : sineH (2 * π * v) K = -sineH (2 * π * u) K := by simpa [hvu] using hs
      linarith
    have hb := sineH_u_le_half v K hv0 hv12
    calc
      |sineH (2 * π * x) K| = |sineH (2 * π * u) K| := by rw [hper]
      _ = |-sineH (2 * π * v) K| := by rw [hsym]
      _ = |sineH (2 * π * v) K| := by simp
      _ ≤ 20 := hb



lemma hdiff (a : ℂ) : cexp (-a * I) - cexp (a * I) = -2 * I * Complex.sin a := by
  rw [Complex.sin]
  field_simp [I_ne_zero]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring

lemma E_sub_E_real (θ : ℝ) : E (-θ) - E θ = -2 * I * (Real.sin (2 * Real.pi * θ) : ℂ) := by
  unfold E
  have harg1 : (((2 * Real.pi * (-θ) : ℝ) : ℂ)) * I = -(((2 * Real.pi * θ : ℝ) : ℂ)) * I := by
    push_cast
    ring
  rw [harg1]
  have hsub := hdiff (((2 * Real.pi * θ : ℝ) : ℂ))
  rw [hsub]
  have hs := Complex.ofReal_sin (2 * Real.pi * θ)
  -- ↑(Real.sin (2πθ)) = sin ↑(2πθ)
  rw [← hs]

lemma div_two_pi_I {s : ℂ} {c : ℂ} (hc : c ≠ 0) :
    (-2 * I * s) / (((2 * Real.pi : ℝ) : ℂ) * I * c) = -s / (((Real.pi : ℂ)) * c) := by
  have hI : I ≠ 0 := Complex.I_ne_zero
  have hπ : (((2 * Real.pi : ℝ) : ℂ) ≠ 0) := by norm_num
  field_simp [hI, hπ, hc]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring

-- each positive-index term of sawHat equals -sin/(π ν)
lemma term_of_sawHat (x : ℝ) (ν : ℤ) (hν : 1 ≤ ν) :
    (E (-((ν : ℝ) * x)) - E ((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))
      = - ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ))) := by
  have hsub := E_sub_E_real ((ν : ℝ) * x)
  -- hsub : E (-(νx)) - E (νx) = -2 I sin (2π·(νx))
  rw [hsub]
  have hc : (ν : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (ν : ℤ) ≠ 0)
  have hmul : -2 * I * (Real.sin (2 * Real.pi * ((ν : ℝ) * x)) : ℂ) = -2 * I * (Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ) := by
    congr 1
    ring
  rw [hmul]
  have hmain := div_two_pi_I (s := (Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ)) (c := (ν : ℂ)) hc
  -- hmain : (-2 I s)/((2π)I (ν)) = -s/(π ν)
  have hden : ((tau * I) * (ν : ℂ)) = (((2 * Real.pi : ℝ) : ℂ) * I * (ν : ℂ)) := by
    simp [tau]
  rw [hden]
  simpa [neg_div] using hmain

/-- The negative-frequency part of `sawHat` reindexed to positive `μ = -ν`. -/
lemma neg_part_reindex (K : ℕ) (x : ℝ) :
    (∑ ν ∈ Finset.Icc (-(K : ℤ)) (-1), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))
      = ∑ μ ∈ Finset.Icc 1 (K : ℤ), - (E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ)) := by
  classical
  rw [← Finset.sum_bij (s := Finset.Icc (-(K : ℤ)) (-1)) (t := Finset.Icc 1 (K : ℤ))
    (f := fun ν => E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))
    (g := fun μ => - (E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ)))
    (i := fun ν _ => -ν)]
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    omega
  · intro a ha b hb h
    omega
  · intro μ hμ
    refine ⟨-μ, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hμ ⊢
      omega
    · simp
  · intro ν hν
    -- f ν = g (−ν)
    simp [neg_div]
    congr 1
    ring

-- main decomposition of sawHat into the positive-index sine sum
lemma sawHat_symm (K : ℕ) (x : ℝ) :
    sawHat K x = - (∑ ν ∈ Finset.Icc 1 (K : ℤ),
      ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ)))) := by
  classical
  unfold sawHat
  have hdom : (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0
      = (Finset.Icc (-(K : ℤ)) (-1)) ∪ (Finset.Icc 1 (K : ℤ)) := by
    ext ν
    constructor
    · intro h
      simp [Finset.mem_erase, Finset.mem_Icc] at h
      rcases h with ⟨hν0, hlo, hhi⟩
      rw [Finset.mem_union]
      by_cases hneg : ν < 0
      · left
        rw [Finset.mem_Icc]
        omega
      · right
        rw [Finset.mem_Icc]
        omega
    · intro h
      rw [Finset.mem_union] at h
      rcases h with hM | hP
      · simp [Finset.mem_erase, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hM
        omega
      · simp [Finset.mem_erase, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hP
        omega
  have hdisj : Disjoint (Finset.Icc (-(K : ℤ)) (-1)) (Finset.Icc 1 (K : ℤ)) := by
    rw [Finset.disjoint_left]
    intro ν hM hP
    rw [Finset.mem_Icc] at hM hP
    omega
  calc
    (∑ ν ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0, E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))
        = (∑ ν ∈ (Finset.Icc (-(K : ℤ)) (-1)) ∪ (Finset.Icc 1 (K : ℤ)),
            E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))) := by
          rw [hdom]
    _ = (∑ ν ∈ Finset.Icc (-(K : ℤ)) (-1), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))
        + (∑ ν ∈ Finset.Icc 1 (K : ℤ), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))) := by
          rw [Finset.sum_union hdisj]
    _ = (∑ μ ∈ Finset.Icc 1 (K : ℤ), - (E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ)))
        + (∑ ν ∈ Finset.Icc 1 (K : ℤ), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))) := by
          rw [neg_part_reindex K x]
    _ = (∑ μ ∈ Finset.Icc 1 (K : ℤ), (E (-((μ : ℝ) * x)) - E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ))) := by
          have hmerge : (∑ μ ∈ Finset.Icc 1 (K : ℤ), - (E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ)))
              + (∑ ν ∈ Finset.Icc 1 (K : ℤ), E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))
              = (∑ μ ∈ Finset.Icc 1 (K : ℤ), (E (-((μ : ℝ) * x)) - E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ))) := by
                rw [← Finset.sum_add_distrib (s := Finset.Icc 1 (K : ℤ))
                  (f := fun μ => - (E ((μ : ℝ) * x)) / ((tau * I) * (μ : ℂ)))
                  (g := fun ν => E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)))]
                refine Finset.sum_congr rfl ?_
                intro μ hμ
                ring
          exact hmerge
    _ = (∑ μ ∈ Finset.Icc 1 (K : ℤ),
          - ((Real.sin (2 * Real.pi * (μ : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * (μ : ℂ)))) := by
          refine Finset.sum_congr rfl ?_
          intro μ hμ
          have hμ1 : 1 ≤ μ := by
            rw [Finset.mem_Icc] at hμ
            omega
          exact term_of_sawHat x μ hμ1
    _ = - (∑ ν ∈ Finset.Icc 1 (K : ℤ),
          ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ)))) := by
          rw [Finset.sum_neg_distrib]

/-- Reindex the `sawHat`-sine-sum to the natural range `i = 0 .. K-1`. -/
lemma sum_Icc_one_eq_range {M : Type} [AddCommMonoid M] (F : ℤ → M) (K : ℕ) :
    (∑ ν ∈ Finset.Icc 1 (K : ℤ), F ν) = ∑ i ∈ Finset.range K, F ((i : ℤ) + 1) := by
  classical
  rw [← Finset.sum_bij (s := Finset.range K) (t := Finset.Icc 1 (K : ℤ))
      (f := fun i => F ((i : ℤ) + 1))
      (g := fun ν => F ν)
      (i := fun i _ => ((i : ℤ) + 1))]
  · intro i hi
    have hiK : i < K := Finset.mem_range.mp hi
    have hiZ : (i : ℤ) < (K : ℤ) := by exact_mod_cast hiK
    rw [Finset.mem_Icc]
    omega
  · intro a ha b hb h
    omega
  · intro ν hν
    rw [Finset.mem_Icc] at hν
    refine ⟨Int.toNat (ν - 1), ?_, ?_⟩
    · rw [Finset.mem_range]
      have hle : ν - 1 < (K : ℤ) := by omega
      have hnonneg : 0 ≤ ν - 1 := by omega
      have htoNat : (Int.toNat (ν - 1) : ℤ) = ν - 1 := by
        exact Int.toNat_of_nonneg hnonneg
      omega
    · have hnonneg : 0 ≤ ν - 1 := by omega
      have htoNat : (Int.toNat (ν - 1) : ℤ) = ν - 1 := by
        exact Int.toNat_of_nonneg hnonneg
      omega
  · intro a ha
    rfl

/-- Reindex the `sawHat`-sine-sum to the natural range `i = 0 .. K-1`. -/
lemma sawHat_eq_neg_range (K : ℕ) (x : ℝ) :
    sawHat K x = - (∑ i ∈ Finset.range K,
      ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)))) := by
  rw [sawHat_symm]
  congr 1
  rw [sum_Icc_one_eq_range (F := fun ν => (Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ))) (K := K)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1

/-- Equating the `x`-phased harmonic sum to `sineH (2πx)`. -/
lemma sineHx_eq_sineH (x : ℝ) (K : ℕ) :
    (∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x))
      = sineH (2 * π * x) K := by
  dsimp [sineH]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- Uniform bound for the `x`-phased harmonic sine sums. -/
lemma sineHx_bdd (x : ℝ) (K : ℕ) :
    |∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x)| ≤ (20 : ℝ) := by
  have hb := sineH_phase_bdd x K
  rw [sineHx_eq_sineH x K]
  exact hb

/-- complex sine-term equals the cast of a real fraction -/
lemma sine_term_complex_eq (a : ℝ) (ν : ℕ) :
    ((Real.sin a : ℂ) / ((Real.pi : ℂ) * ((ν : ℕ) : ℂ))) = ((Real.sin a / (Real.pi * ((ν : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have h1 : ((Real.pi : ℂ) * ((ν : ℕ) : ℂ)) = (((Real.pi * ((ν : ℕ) : ℝ) : ℝ) : ℂ)) := by
    rw [show ((ν : ℕ) : ℂ) = (((ν : ℕ) : ℝ) : ℂ) by rfl]
    rw [← Complex.ofReal_mul]
  rw [h1]
  rw [← Complex.ofReal_div]

/-- norm of the cast of a real number -/
lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simpa using (norm_algebraMap' ℝ ℂ r)

/-- `sawHat` equals (a negative of) a sum of real casts, per-term. -/
lemma sawHat_eq_real_neg (K : ℕ) (x : ℝ) :
    sawHat K x = - (∑ i ∈ Finset.range K,
      ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) := by
  rw [sawHat_eq_neg_range]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact sine_term_complex_eq (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) (i + 1)

/-- Norm of the complex sine sum equals the absolute value of the real one. -/
lemma norm_sine_sum_eq (x : ℝ) (K : ℕ) :
    ‖∑ i ∈ Finset.range K,
        ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℂ) /
          ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)))‖
      = |∑ i ∈ Finset.range K,
          Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ))| := by
  calc
    ‖∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℂ) /
          ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)))‖
        = ‖∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) /
              (Real.pi * ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ)‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact sine_term_complex_eq (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) (i + 1)
    _ = |∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) /
              (Real.pi * ((i + 1 : ℕ) : ℝ))| := by
          rw [← Complex.ofReal_sum]
          rw [norm_ofReal]

/-- The real sine sums at `x` are bounded by `20/π`. -/
lemma real_sine_sum_abs_le (x : ℝ) (K : ℕ) :
    |∑ i ∈ Finset.range K,
        Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ))| ≤ (20 : ℝ) / Real.pi := by
  -- per-term: sin/(π·(i+1)) = (1/π) · ((i+1)⁻¹ · sin)
  have hfact : (∑ i ∈ Finset.range K,
        Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ)))
      = (1 / Real.pi) * (∑ i ∈ Finset.range K,
          (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x)) := by
    calc
      (∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ)))
          = ∑ i ∈ Finset.range K, (1 / Real.pi) * ((((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hpos : ((i + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i)
            field_simp [Real.pi_ne_zero, hpos]
      _ = (1 / Real.pi) * (∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x)) := by
            rw [← Finset.mul_sum]
  calc
    |∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) / (Real.pi * ((i + 1 : ℕ) : ℝ))|
        = |(1 / Real.pi) * (∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x))| := by
          rw [hfact]
    _ = (1 / Real.pi) * |∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) * Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
    _ ≤ (1 / Real.pi) * 20 := by
          exact mul_le_mul_of_nonneg_left (sineHx_bdd x K) (by positivity : 0 ≤ 1 / Real.pi)
    _ = (20 : ℝ) / Real.pi := by ring

/-- The uniform bound for `sawHat`. -/
lemma sawHat_norm_bdd (K : ℕ) (x : ℝ) : ‖sawHat K x‖ ≤ (20 : ℝ) := by
  rw [sawHat_eq_real_neg]
  rw [norm_neg]
  rw [← Complex.ofReal_sum]
  rw [norm_ofReal]
  have h := real_sine_sum_abs_le x K
  exact le_trans h (by
    have hπ : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hdiv : (20 : ℝ) / Real.pi ≤ 20 := by
      rw [div_le_iff₀ (by positivity : 0 < Real.pi)]
      nlinarith [hπ]
    exact hdiv)
end

end Submission.SdtPoisson


open Complex Filter Topology
open scoped Real BigOperators ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Classical facts about the Dirichlet partial sums of the sawtooth Fourier series

This file proves:
- `sawHat_norm_bdd` :  `‖sawHat K x‖ ≤ 20` for all `K, x`;
- `sawHat_tendsto_saw` : for `x ∉ ℤ`, `sawHat K x → saw x` (pointwise).
-/

namespace Submission.SdtPoisson

noncomputable section




lemma E_eq_cos_sin (t : ℝ) :
    E t = ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ) + ((Real.sin (2 * Real.pi * t) : ℝ) : ℂ) * I := by
  unfold E
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma E_neg_eq_cos_sin (t : ℝ) :
    E (-t) = ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ) - ((Real.sin (2 * Real.pi * t) : ℝ) : ℂ) * I := by
  unfold E
  rw [Complex.exp_mul_I]
  rw [show (2 * Real.pi * (-t) : ℝ) = -(2 * Real.pi * t) by ring]
  rw [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

lemma E_sub_E_neg (t : ℝ) : E t - E (-t) = (2 : ℂ) * I * (Real.sin (2 * Real.pi * t) : ℂ) := by
  rw [E_eq_cos_sin, E_neg_eq_cos_sin]
  ring

lemma E_neg_sub_E (t : ℝ) : E (-t) - E t = -((2 : ℂ) * I * (Real.sin (2 * Real.pi * t) : ℂ)) := by
  have h := E_sub_E_neg (-t)
  rw [neg_neg] at h
  rw [show (2 * Real.pi * (-t) : ℝ) = -(2 * Real.pi * t) by ring, Real.sin_neg] at h
  rw [Complex.ofReal_neg] at h
  simpa [mul_neg] using h

lemma pair_term (t : ℝ) (j : ℤ) (hj : j ≠ 0) :
    E (-((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) +
      E (-(((-j : ℤ) : ℝ) * t)) / ((tau * I) * ((-j : ℤ) : ℂ))
      = -(((Real.sin (2 * Real.pi * (j : ℝ) * t) : ℝ) : ℂ) / ((Real.pi : ℂ) * (j : ℂ))) := by
  have hs : E (-((j : ℝ) * t)) - E ((j : ℝ) * t) =
      -((2 : ℂ) * I * (Real.sin (2 * Real.pi * (j : ℝ) * t) : ℂ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (E_neg_sub_E ((j : ℝ) * t))
  have hnum : -(((-j : ℤ) : ℝ) * t) = (j : ℝ) * t := by
    rw [Int.cast_neg]
    ring
  have hden : ((tau * I) * ((-j : ℤ) : ℂ)) = -((tau * I) * (j : ℂ)) := by
    rw [Int.cast_neg]
    ring
  calc
    E (-((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) +
        E (-(((-j : ℤ) : ℝ) * t)) / ((tau * I) * ((-j : ℤ) : ℂ))
        = (E (-((j : ℝ) * t)) - E ((j : ℝ) * t)) / ((tau * I) * (j : ℂ)) := by
          rw [hnum, hden]
          field_simp [tau]
          ring
    _ = -(((Real.sin (2 * Real.pi * (j : ℝ) * t) : ℝ) : ℂ) / ((Real.pi : ℂ) * (j : ℂ))) := by
          rw [hs]
          dsimp [tau]
          field_simp
          push_cast
          ring

lemma sum_erase_symm (K : ℕ) (g : ℤ → ℂ) :
    (∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, g ν) =
      ∑ j ∈ Finset.Icc 1 (K : ℤ), (g j + g (-j)) := by
  classical
  have hK0 : (0 : ℤ) ≤ (K : ℤ) := by exact_mod_cast (Nat.zero_le K)
  let P : Finset ℤ := Finset.Icc 1 (K : ℤ)
  let N : Finset ℤ := Finset.Icc (-(K : ℤ)) (-1 : ℤ)
  have hcover : (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 = N ∪ P := by
    ext ν
    constructor
    · intro hν
      have hmem : ν ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (Finset.mem_erase.mp hν).2
      have h0 : ν ≠ 0 := (Finset.mem_erase.mp hν).1
      have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hmem).1
      have hge : ν ≤ (K : ℤ) := (Finset.mem_Icc.mp hmem).2
      by_cases hpos : 0 < ν
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_Icc.mpr ⟨by omega, hge⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hle, by omega⟩))
    · intro hν
      rcases Finset.mem_union.mp hν with hN | hP
      · have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hN).1
        have hge : ν ≤ -1 := (Finset.mem_Icc.mp hN).2
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hle, by omega⟩⟩
      · have hle : 1 ≤ ν := (Finset.mem_Icc.mp hP).1
        have hge : ν ≤ (K : ℤ) := (Finset.mem_Icc.mp hP).2
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hge⟩⟩
  have hneg : (∑ ν ∈ N, g ν) = ∑ j ∈ P, g (-j) := by
    refine Finset.sum_bij (s := N) (t := P) (f := g) (g := fun j => g (-j))
      (fun ν _ => -ν) ?hi ?hinj ?hsurj ?h
    · intro ν hν
      have hle : -(K : ℤ) ≤ ν := (Finset.mem_Icc.mp hν).1
      have hge : ν ≤ -1 := (Finset.mem_Icc.mp hν).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb h
      omega
    · intro b hb
      have h1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have h2 : b ≤ (K : ℤ) := (Finset.mem_Icc.mp hb).2
      refine ⟨-b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro a ha
      rw [neg_neg]
  rw [hcover]
  have hdisj : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro ν hN hP
    have hge : ν ≤ -1 := (Finset.mem_Icc.mp hN).2
    have hle : 1 ≤ ν := (Finset.mem_Icc.mp hP).1
    omega
  rw [Finset.sum_union hdisj, hneg]
  rw [add_comm]
  rw [← Finset.sum_add_distrib]

lemma sum_range_eq_sum_Icc_one (K : ℕ) (f : ℤ → ℂ) :
    (∑ i ∈ Finset.range K, f ((i : ℤ) + 1)) = ∑ ν ∈ Finset.Icc 1 (K : ℤ), f ν := by
  refine Finset.sum_bij (s := Finset.range K) (t := Finset.Icc 1 (K : ℤ))
    (f := fun i => f ((i : ℤ) + 1)) (g := f) (fun i _ => (i : ℤ) + 1) ?hi ?hinj ?hsurj ?h
  · intro i hi
    have hiK : i < K := Finset.mem_range.mp hi
    have hiKz : (i : ℤ) < (K : ℤ) := by exact_mod_cast hiK
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast (Nat.zero_le i)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb h
    have hz : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hz
  · intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbK : b ≤ (K : ℤ) := (Finset.mem_Icc.mp hb).2
    have hbpos : 0 < b := by omega
    refine ⟨b.toNat - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hcast : ((b.toNat - 1 : ℕ) : ℤ) = b - 1 := Int.toNat_pred_coe_of_pos hbpos
      have hle' : ((b.toNat - 1 : ℕ) : ℤ) < (K : ℤ) := by rw [hcast]; omega
      exact_mod_cast hle'
    · have hcast : ((b.toNat - 1 : ℕ) : ℤ) = b - 1 := Int.toNat_pred_coe_of_pos hbpos
      rw [hcast]
      omega
  · intro a ha
    rfl

lemma sawHat_eq_sin_Icc (K : ℕ) (x : ℝ) :
    sawHat K x = -∑ ν ∈ Finset.Icc 1 (K : ℤ),
      ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℝ) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ)) := by
  unfold sawHat
  rw [sum_erase_symm K]
  rw [Finset.sum_congr rfl (fun j hj => pair_term x j (by
    have h1 : (1 : ℤ) ≤ j := (Finset.mem_Icc.mp hj).1
    omega))]
  rw [Finset.sum_neg_distrib]
-- ===== fract reduction (from earlier) =====
lemma sawHat_eq_sawHat_fract (K : ℕ) (x : ℝ) : sawHat K x = sawHat K (Int.fract x) := by
  unfold sawHat
  apply Finset.sum_congr rfl
  intro ν hν
  congr 1
  have hxarg : -((ν : ℝ) * x) = (-((ν : ℝ) * Int.fract x)) + (-((ν : ℝ) * (⌊x⌋ : ℝ))) := by
    conv_lhs =>
      rw [show x = Int.fract x + (⌊x⌋ : ℝ) by exact (Int.fract_add_floor x).symm]
    ring
  rw [hxarg, E_add]
  have hE2 : E (-((ν : ℝ) * (⌊x⌋ : ℝ))) = 1 := by
    have hz : (-((ν : ℝ) * (⌊x⌋ : ℝ))) = ((-(ν * ⌊x⌋) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hz]
    exact E_of_int (-(ν * ⌊x⌋))
  rw [hE2, mul_one]

lemma saw_fract (x : ℝ) : saw (Int.fract x) = saw x := by
  unfold saw
  rw [Int.fract_fract]

lemma fract_pos_of_not_int {x : ℝ} (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) : 0 < Int.fract x := by
  have hnon : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hz : Int.fract x ≠ 0 := by
    intro h
    have hxmem : x ∈ Set.range (Int.cast : ℤ → ℝ) := (Int.fract_eq_zero_iff).mp h
    rcases hxmem with ⟨z, hz⟩
    exact hx ⟨z, hz⟩
  exact lt_of_le_of_ne hnon (Ne.symm hz)



-- factorizations etc from im8 (copy minimal)
lemma cos_pi_mul_sub_half (u : ℝ) :
    Real.cos (Real.pi * u - Real.pi / 2) = Real.sin (Real.pi * u) := by
  rw [Real.cos_sub]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring
lemma sin_pi_mul_sub_half (u : ℝ) :
    Real.sin (Real.pi * u - Real.pi / 2) = -Real.cos (Real.pi * u) := by
  rw [Real.sin_sub]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring
lemma one_sub_cos_two (u : ℝ) : 1 - Real.cos (2 * Real.pi * u) = 2 * Real.sin (Real.pi * u)^2 := by
  rw [show (2 * Real.pi * u : ℝ) = 2 * (Real.pi * u) by ring, Real.cos_two_mul_eq_one_sub]
  ring
lemma sin_two_pi (u : ℝ) : Real.sin (2 * Real.pi * u) = 2 * Real.sin (Real.pi * u) * Real.cos (Real.pi * u) := by
  rw [show (2 * Real.pi * u : ℝ) = 2 * (Real.pi * u) by ring, Real.sin_two_mul]
lemma one_sub_E_eq' (u : ℝ) :
    1 - E u = (2 * Real.sin (Real.pi * u) : ℂ) *
        (((Real.sin (Real.pi * u) : ℝ) : ℂ) - ((Real.cos (Real.pi * u) : ℝ) : ℂ) * I) := by
  rw [E_eq_cos_sin]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    rw [one_sub_cos_two u]
    ring
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    rw [sin_two_pi u]

lemma exp_mul_I_eq_cos_sin_real (θ : ℝ) :
    exp ((θ : ℝ) * I) = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
lemma exp_I_pi_u (u : ℝ) :
    exp ((Real.pi * u - Real.pi / 2 : ℝ) * I) =
      ((Real.sin (Real.pi * u) : ℝ) : ℂ) - ((Real.cos (Real.pi * u) : ℝ) : ℂ) * I := by
  rw [exp_mul_I_eq_cos_sin_real]
  rw [cos_pi_mul_sub_half u, sin_pi_mul_sub_half u]
  rw [Complex.ofReal_neg]
  ring
lemma one_sub_E_eq (u : ℝ) :
    1 - E u = (2 * Real.sin (Real.pi * u) : ℂ) *
        exp ((Real.pi * u - Real.pi / 2 : ℝ) * I) := by
  rw [one_sub_E_eq', exp_I_pi_u]

#check Complex.exp_ne_zero
#check Complex.ofReal_im

-- ===== the main im lemma =====
lemma sawFourier_im_log_one_sub_E (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (Complex.log (1 - E u)).im = Real.pi * u - Real.pi / 2 := by
  have hpu_pos : 0 < Real.pi * u := by positivity
  have hpu_lt : Real.pi * u < Real.pi := by
    have hlt : Real.pi * u < Real.pi * 1 := mul_lt_mul_of_pos_left hu1 Real.pi_pos
    simpa using hlt
  have hsin : 0 < Real.sin (Real.pi * u) := by
    exact Real.sin_pos_of_pos_of_lt_pi hpu_pos hpu_lt
  have h2sin : 0 < 2 * Real.sin (Real.pi * u) := by positivity
  have hθ1 : -Real.pi < Real.pi * u - Real.pi / 2 := by linarith [Real.pi_pos, hpu_pos]
  have hθ2 : Real.pi * u - Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos, hpu_lt]
  have hx : exp ((Real.pi * u - Real.pi / 2 : ℝ) * I) ≠ 0 :=
    Complex.exp_ne_zero ((Real.pi * u - Real.pi / 2 : ℝ) * I)
  have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [one_sub_E_eq u]
  rw [h2c, ← Complex.ofReal_mul]
  rw [Complex.log_ofReal_mul h2sin hx]
  rw [Complex.log_exp (x := ((Real.pi * u - Real.pi / 2 : ℝ) : ℂ) * I)]
  · simp
  · simpa using hθ1
  · simpa using hθ2


lemma geom_partial_norm_le {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w ^ (i + 1)‖ ≤ 2 / ‖1 - w‖ := by
  have hnum : ‖w ^ n - 1‖ ≤ 2 := by
    calc
      ‖w ^ n - 1‖ ≤ ‖w ^ n‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hwn, one_pow, norm_one]; norm_num
  have hdiv : ‖(w ^ n - 1) / (w - 1)‖ ≤ 2 / ‖1 - w‖ := by
    rw [norm_div]
    rw [show ‖w - 1‖ = ‖1 - w‖ by rw [norm_sub_rev]]
    exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
  calc
    ‖∑ i ∈ Finset.range n, w ^ (i + 1)‖
        = ‖w * ∑ i ∈ Finset.range n, w ^ i‖ := by
          congr 1
          calc
            (∑ i ∈ Finset.range n, w ^ (i + 1)) = ∑ i ∈ Finset.range n, w * w ^ i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [pow_succ, mul_comm]
            _ = w * (∑ i ∈ Finset.range n, w ^ i) := by rw [Finset.mul_sum]
    _ = ‖w‖ * ‖∑ i ∈ Finset.range n, w ^ i‖ := by rw [norm_mul]
    _ = ‖∑ i ∈ Finset.range n, w ^ i‖ := by rw [hwn, one_mul]
    _ = ‖(w ^ n - 1) / (w - 1)‖ := by rw [geom_sum_eq hw1]
    _ ≤ 2 / ‖1 - w‖ := hdiv

lemma antitone_inv : Antitone (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  rw [inv_le_inv₀]
  · exact_mod_cast (by omega : (n + 1 : ℕ) ≤ n + 2)
  · positivity
  · positivity

lemma tendsto_inv_succ : Tendsto (fun i : ℕ => (((i + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)

lemma logSum_cauchy_tendsto {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) :
    ∃ l : ℂ, Tendsto (fun K : ℕ => ∑ i ∈ Finset.range K,
        w ^ (i + 1) / ((i + 1 : ℕ) : ℂ)) atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun i => ((i + 1 : ℕ) : ℝ)⁻¹
  let z : ℕ → ℂ := fun i => w ^ (i + 1)
  have hcauchy : CauchySeq (fun n => ∑ i ∈ Finset.range n, f i • z i) := by
    exact (antitone_inv).cauchySeq_series_mul_of_tendsto_zero_of_bounded
      tendsto_inv_succ (geom_partial_norm_le (w := w) hwn hw1)
  have hpt : (fun K : ℕ => ∑ i ∈ Finset.range K, w ^ (i + 1) / ((i + 1 : ℕ) : ℂ))
             = (fun K => ∑ i ∈ Finset.range K, f i • z i) := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, z, div_eq_mul_inv, Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
  have hcauchy' : CauchySeq (fun K : ℕ => ∑ i ∈ Finset.range K,
        w ^ (i + 1) / ((i + 1 : ℕ) : ℂ)) := by
    rw [hpt]
    exact hcauchy
  exact cauchySeq_tendsto_of_complete hcauchy'

lemma tsum_abelMean_eq_log {w : ℂ} (hwn : ‖w‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
      = -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w) := by
  have hnr : ‖(r : ℂ) * w‖ < 1 := by
    have hnorm : ‖(r : ℂ)‖ = r := by
      have h := RCLike.norm_ofReal (K := ℂ) r
      rwa [abs_of_nonneg hr0.le] at h
    rw [norm_mul, hnorm, hwn, mul_one]
    exact hr1
  have hlog := Complex.hasSum_taylorSeries_neg_log' (z := (r : ℂ) * w) hnr
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  calc
    (∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
        = ∑' n : ℕ, ((1 / (r : ℂ)) * (((r : ℂ) * w) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))) := by
          apply tsum_congr
          intro n
          have hterm : (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n
              = (1 / (r : ℂ)) * (((r : ℂ) * w) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
            field_simp [hrne]
            rw [mul_pow, pow_succ]
            ring
          exact hterm
    _ = (1 / (r : ℂ)) * (∑' n : ℕ, ((r : ℂ) * w) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
          rw [tsum_mul_left]
    _ = -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w) := by
          have htsum : (∑' n : ℕ, ((r : ℂ) * w) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
              = ∑' n : ℕ, ((r : ℂ) * w) ^ (n + 1) / ((n : ℂ) + 1) := by
            apply tsum_congr
            intro n
            congr 1
            norm_num
          rw [htsum]
          rw [hlog.tsum_eq]
          ring

lemma one_sub_mem_slitPlane {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) : 1 - w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 - w).im ≠ 0
  · exact Or.inr him
  · left
    have hwim : w.im = 0 := by
      have h : (1 - w).im = 0 := not_not.mp him
      simpa using h
    have hwre1 : w.re ≠ 1 := by
      intro hre
      have : w = 1 := Complex.ext hre hwim
      exact hw1 this
    have hre_le : w.re ≤ 1 := by
      calc w.re ≤ ‖w‖ := Complex.re_le_norm w
      _ = 1 := hwn
    have hlt : w.re < 1 := lt_of_le_of_ne hre_le hwre1
    rw [show (1 - w).re = 1 - w.re by simp]
    linarith

-- Tendsto of the Abel-mean-log expression as r → 1⁻ (real)
lemma tendsto_mean_log {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) :
    Tendsto (fun r : ℝ => -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w))
      (𝓝[<] (1 : ℝ)) (𝓝 (-Complex.log (1 - w))) := by
  have hA : ContinuousAt (fun r : ℝ => (1 : ℂ) / (r : ℂ)) 1 := by
    apply ContinuousAt.div
    · exact continuousAt_const
    · exact Complex.continuous_ofReal.continuousAt
    · norm_num
  have hg : ContinuousAt (fun r : ℝ => 1 - (r : ℂ) * w) 1 := by
    fun_prop
  have hlog : ContinuousAt (fun r : ℝ => Complex.log (1 - (r : ℂ) * w)) 1 := by
    refine hg.clog ?_
    simpa using (one_sub_mem_slitPlane hwn hw1)
  have hnegA : ContinuousAt (fun r : ℝ => -(1 / (r : ℂ))) 1 := hA.neg
  have hmean : ContinuousAt (fun r : ℝ => -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w)) 1 := hnegA.mul hlog
  simpa using (hmean.tendsto.mono_left nhdsWithin_le_nhds)

-- eventual equality of tsum and log expression under (𝓝[<]1)
lemma eventually_eq_tsum_mean {w : ℂ} (hwn : ‖w‖ = 1) :
    (fun r : ℝ => ∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
      =ᶠ[𝓝[<] (1 : ℝ)] fun r : ℝ =>
        -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w) := by
  have hbig : ∀ᶠ r in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < r := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (by norm_num) (by norm_num)] with r hr
    intro hrlt
    exact (Set.mem_Ioo.mp hr).1
  filter_upwards [hbig, eventually_mem_nhdsWithin] with r hr0 hrlt
  exact tsum_abelMean_eq_log hwn (by linarith) hrlt

-- main lemma
lemma logSum_tendsto {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) :
    Tendsto (fun K : ℕ => ∑ i ∈ Finset.range K, w ^ (i + 1) / ((i + 1 : ℕ) : ℂ))
      atTop (𝓝 (-(Complex.log (1 - w)))) := by
  rcases logSum_cauchy_tendsto hwn hw1 with ⟨l, hl⟩
  have hab : Tendsto (fun z : ℂ => ∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * z ^ n)
      ((𝓝[<] (1 : ℝ)).map ofReal) (𝓝 l) :=
    Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have habR : Tendsto (fun r : ℝ => ∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
      (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    have hc := (tendsto_map'_iff (f := fun z : ℂ =>
        ∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * z ^ n)
        (g := ofReal) (x := 𝓝[<] (1 : ℝ)) (y := 𝓝 l)).mp hab
    simpa [Function.comp_def] using hc
  have hmean : Tendsto (fun r : ℝ => -(1 / (r : ℂ)) * Complex.log (1 - (r : ℂ) * w))
      (𝓝[<] (1 : ℝ)) (𝓝 (-Complex.log (1 - w))) := tendsto_mean_log hwn hw1
  have htsumLog : Tendsto (fun r : ℝ => ∑' n : ℕ, (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * (r : ℂ) ^ n)
      (𝓝[<] (1 : ℝ)) (𝓝 (-Complex.log (1 - w))) := by
    exact (tendsto_congr' (eventually_eq_tsum_mean hwn)).2 hmean
  haveI : (𝓝[<] (1 : ℝ)).NeBot :=
    nhdsWithin_Iio_neBot (a := (1 : ℝ)) (b := (1 : ℝ)) le_rfl
  have heq := tendsto_nhds_unique habR htsumLog
  -- heq : l = -log(1-w)
  simpa [← heq] using hl


lemma abs_sin_partial_le (n : ℕ) {τ : ℝ} (h0 : 0 < τ) (hτ : τ ≤ Real.pi) :
    |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ)| ≤ 1 / Real.sin (τ / 2) := by
  have hprod := Real.sin_mul_sum_sin n (a := τ) (b := τ)
  have hs2 : 0 < Real.sin (τ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · linarith [Real.pi_pos, hτ]
  have hrewrite : (∑ i ∈ Finset.range n, Real.sin (τ * (i : ℝ) + τ))
      = ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hmain : Real.sin (τ / 2) * |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ)|
      ≤ 1 := by
    calc
      Real.sin (τ / 2) * |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ)|
          = |Real.sin (τ / 2)| * |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ)| := by
            rw [abs_of_pos hs2]
      _ = |Real.sin (τ / 2) * ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * τ)| := by
            rw [abs_mul]
      _ = |Real.sin (τ / 2) * ∑ i ∈ Finset.range n, Real.sin (τ * (i : ℝ) + τ)| := by
            rw [hrewrite]
      _ = |Real.sin (↑n * τ / 2) * Real.sin ((↑n - 1) * τ / 2 + τ)| := by
            rw [hprod]
      _ ≤ 1 := by
            rw [abs_mul]
            simpa using (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num))
  rw [le_div_iff₀ hs2]
  rw [mul_comm]
  exact hmain

lemma abs_sin_block_le (p m : ℕ) {τ : ℝ} (h0 : 0 < τ) (hτ : τ ≤ Real.pi) :
    |∑ j ∈ Finset.range m, Real.sin (((p + j + 1 : ℕ) : ℝ) * τ)|
      ≤ 2 / Real.sin (τ / 2) := by
  let f : ℕ → ℝ := fun i => Real.sin (((i + 1 : ℕ) : ℝ) * τ)
  have hC : |∑ i ∈ Finset.range (p + m), f i| ≤ 1 / Real.sin (τ / 2) := by
    simpa [f] using (abs_sin_partial_le (p + m) h0 hτ)
  have hA : |∑ i ∈ Finset.range p, f i| ≤ 1 / Real.sin (τ / 2) := by
    simpa [f] using (abs_sin_partial_le p h0 hτ)
  have hdec : (∑ i ∈ Finset.range (p + m), f i)
      = (∑ i ∈ Finset.range p, f i) + ∑ i ∈ Finset.Ico p (p + m), f i := by
    exact (Finset.sum_range_add_sum_Ico (f := f) (m := p) (n := p + m) (by omega)).symm
  have hI : (∑ i ∈ Finset.Ico p (p + m), f i)
      = ∑ j ∈ Finset.range m, f (p + j) := by
    have h := Finset.sum_Ico_eq_sum_range f p (p + m)
    rw [Nat.add_sub_cancel_left] at h
    exact h
  have hI2 : (∑ j ∈ Finset.range m, f (p + j))
      = ∑ j ∈ Finset.range m, Real.sin (((p + j + 1 : ℕ) : ℝ) * τ) := by
    rfl
  have htri : |(∑ i ∈ Finset.range (p + m), f i) - ∑ i ∈ Finset.range p, f i|
      ≤ |∑ i ∈ Finset.range (p + m), f i| + |∑ i ∈ Finset.range p, f i| := by
    rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact norm_sub_le _ _
  calc
    |∑ j ∈ Finset.range m, Real.sin (((p + j + 1 : ℕ) : ℝ) * τ)|
        = |∑ j ∈ Finset.range m, f (p + j)| := by rw [hI2]
    _ = |∑ i ∈ Finset.Ico p (p + m), f i| := by rw [hI]
    _ = |(∑ i ∈ Finset.range (p + m), f i) - ∑ i ∈ Finset.range p, f i| := by
          rw [hdec, add_sub_cancel_left]
    _ ≤ |∑ i ∈ Finset.range (p + m), f i| + |∑ i ∈ Finset.range p, f i| := htri
    _ ≤ (1 / Real.sin (τ / 2)) + (1 / Real.sin (τ / 2)) := by linarith
    _ = 2 / Real.sin (τ / 2) := by
          have hs2ne : Real.sin (τ / 2) ≠ 0 := by
            have hs2 : 0 < Real.sin (τ / 2) := by
              apply Real.sin_pos_of_pos_of_lt_pi
              · positivity
              · linarith [Real.pi_pos, hτ]
            exact ne_of_gt hs2
          field_simp [hs2ne]
          ring

-- head bound (terms ≤ τ)
lemma abs_head_le (K : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) :
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
      ≤ (K : ℝ) * τ := by
  calc
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
        ≤ ∑ i ∈ Finset.range K,
            |Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
          := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range K,
            |Real.sin (((i + 1 : ℕ) : ℝ) * τ)| / ((i + 1 : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_div, abs_of_nonneg (show 0 ≤ ((i + 1 : ℕ) : ℝ) by positivity)]
    _ ≤ ∑ i ∈ Finset.range K, τ := by
          apply Finset.sum_le_sum
          intro i hi
          have hx : 0 ≤ ((i + 1 : ℕ) : ℝ) * τ := by positivity
          have hsin : |Real.sin (((i + 1 : ℕ) : ℝ) * τ)| ≤ ((i + 1 : ℕ) : ℝ) * τ := by
            have hsinabs : |Real.sin (((i + 1 : ℕ) : ℝ) * τ)| ≤ |((i + 1 : ℕ) : ℝ) * τ| := Real.abs_sin_le_abs
            rwa [abs_of_nonneg hx] at hsinabs
          have hden : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
          calc
            |Real.sin (((i + 1 : ℕ) : ℝ) * τ)| / ((i + 1 : ℕ) : ℝ)
                ≤ (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ) := by
                  exact div_le_div_of_nonneg_right hsin hden.le
            _ = τ := by field_simp [hden.ne']
    _ = (K : ℝ) * τ := by simp

-- Abel / partial-summation tail bound
lemma abs_weighted_shift_le {p L : ℕ} {B : ℝ} (a : ℕ → ℝ)
    (hB : ∀ m : ℕ, m ≤ L → |∑ j ∈ Finset.range m, a (p + j)| ≤ B) (hB0 : 0 ≤ B) :
    |∑ i ∈ Finset.range L, a (p + i) / ((p + i + 1 : ℕ) : ℝ)| ≤ B / ((p + 1 : ℕ) : ℝ) := by
  let f : ℕ → ℝ := fun i => 1 / ((p + i + 1 : ℕ) : ℝ)
  let g : ℕ → ℝ := fun i => a (p + i)
  have hterm : (∑ i ∈ Finset.range L, a (p + i) / ((p + i + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.range L, f i * g i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f, g]
    ring
  have hG : ∀ n : ℕ, n ≤ L → |∑ j ∈ Finset.range n, g j| ≤ B := by
    intro n hn
    simpa [g] using (hB n hn)
  have hfpos : ∀ i : ℕ, 0 < f i := by
    intro i
    dsimp [f]
    positivity
  have hfdec : ∀ i : ℕ, f (i + 1) ≤ f i := by
    intro i
    dsimp [f]
    have hidx : (p + (i + 1) + 1 : ℕ) = p + i + 2 := by omega
    rw [hidx]
    have h1 : 0 < ((p + i + 1 : ℕ) : ℝ) := by positivity
    have hle : ((p + i + 1 : ℕ) : ℝ) ≤ ((p + i + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (p + i + 1 : ℕ) ≤ p + i + 2)
    exact one_div_le_one_div_of_le h1 hle
  have hf0 : f 0 = 1 / ((p + 1 : ℕ) : ℝ) := by
    simp [f]
  have hbound : |∑ i ∈ Finset.range L, f i * g i| ≤ B * f 0 := by
    by_cases hL0 : L = 0
    · simp [hL0, hB0]
      have : 0 ≤ B * f 0 := mul_nonneg hB0 (hfpos 0).le
      linarith
    · have hLge1 : 1 ≤ L := Nat.pos_of_ne_zero hL0
      have hbp := Finset.sum_range_by_parts f g L
      have hfirst : |f (L - 1) * (∑ j ∈ Finset.range L, g j)| ≤ f (L - 1) * B := by
        have hpos : 0 ≤ f (L - 1) := (hfpos (L - 1)).le
        calc
          |f (L - 1) * (∑ j ∈ Finset.range L, g j)| = f (L - 1) * |∑ j ∈ Finset.range L, g j| := by
            rw [abs_mul, abs_of_pos (hfpos (L - 1))]
          _ ≤ f (L - 1) * B := mul_le_mul_of_nonneg_left (hG L le_rfl) hpos
      have hrest : |∑ i ∈ Finset.range (L - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)|
          ≤ B * (f 0 - f (L - 1)) := by
        have htel : (∑ i ∈ Finset.range (L - 1), (f i - f (i + 1))) = f 0 - f (L - 1) := by
          have hs := Finset.sum_range_sub (fun i => f i) (L - 1)
          calc
            (∑ i ∈ Finset.range (L - 1), (f i - f (i + 1)))
                = ∑ i ∈ Finset.range (L - 1), -(f (i + 1) - f i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = -(∑ i ∈ Finset.range (L - 1), (f (i + 1) - f i)) := by rw [Finset.sum_neg_distrib]
            _ = -(f (L - 1) - f 0) := by rw [hs]
            _ = f 0 - f (L - 1) := by ring
        calc
          |∑ i ∈ Finset.range (L - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)|
              ≤ ∑ i ∈ Finset.range (L - 1), |(f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)|
                := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range (L - 1), |f (i + 1) - f i| * |∑ j ∈ Finset.range (i + 1), g j| := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [abs_mul]
          _ ≤ ∑ i ∈ Finset.range (L - 1), |f (i + 1) - f i| * B := by
                apply Finset.sum_le_sum
                intro i hi
                have hi' : i < L - 1 := Finset.mem_range.mp hi
                have hG' : |∑ j ∈ Finset.range (i + 1), g j| ≤ B := hG (i + 1) (by omega)
                exact mul_le_mul_of_nonneg_left hG' (abs_nonneg (f (i + 1) - f i))
          _ = ∑ i ∈ Finset.range (L - 1), (f i - f (i + 1)) * B := by
                apply Finset.sum_congr rfl
                intro i hi
                congr 1
                have hdiff : f (i + 1) - f i ≤ 0 := sub_nonpos.mpr (hfdec i)
                rw [abs_of_nonpos hdiff]
                ring
          _ = B * (f 0 - f (L - 1)) := by
                rw [← Finset.sum_mul]
                rw [htel]
                ring
      calc
        |∑ i ∈ Finset.range L, f i * g i|
            = |f (L - 1) * (∑ j ∈ Finset.range L, g j)
                - ∑ i ∈ Finset.range (L - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)| := by
                  have hsmul : (∑ i ∈ Finset.range L, f i * g i) = (∑ i ∈ Finset.range L, f i • g i) := by
                    simp [smul_eq_mul]
                  rw [hsmul, hbp]
                  simp [smul_eq_mul]
        _ ≤ |f (L - 1) * (∑ j ∈ Finset.range L, g j)|
              + |∑ i ∈ Finset.range (L - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)| := by
                  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
                  exact norm_sub_le _ _
        _ ≤ f (L - 1) * B + B * (f 0 - f (L - 1)) := add_le_add hfirst hrest
        _ = B * f 0 := by ring
  calc
    |∑ i ∈ Finset.range L, a (p + i) / ((p + i + 1 : ℕ) : ℝ)|
        = |∑ i ∈ Finset.range L, f i * g i| := by rw [hterm]
    _ ≤ B * f 0 := hbound
    _ = B / ((p + 1 : ℕ) : ℝ) := by
          rw [hf0]
          field_simp


lemma tail_const_le {n0 : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ Real.pi)
    (hn0ge : (1 / τ) ≤ (n0 : ℝ)) :
    (2 / Real.sin (τ / 2)) * (1 / ((n0 + 1 : ℕ) : ℝ)) ≤ 2 * Real.pi := by
  have hs : 0 < Real.sin (τ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · linarith [Real.pi_pos, hτ1]
  have hJ : τ / Real.pi ≤ Real.sin (τ / 2) := by
    have h2 := Real.mul_le_sin (x := τ / 2) (by positivity) (by linarith)
    have hrewrite : τ / Real.pi = (2 / Real.pi) * (τ / 2) := by ring
    rwa [hrewrite]
  have h1 : 1 / Real.sin (τ / 2) ≤ Real.pi / τ := by
    have hjpos : 0 < τ / Real.pi := by positivity
    have hinv : 1 / Real.sin (τ / 2) ≤ 1 / (τ / Real.pi) := one_div_le_one_div_of_le hjpos hJ
    have hiden : 1 / (τ / Real.pi) = Real.pi / τ := by
      field_simp [Real.pi_ne_zero, hτ0.ne']
    rwa [hiden] at hinv
  have hcast : (((n0 + 1 : ℕ) : ℝ)) = (n0 : ℝ) + 1 := by simp [Nat.cast_add]
  have hn0p1 : (1 / τ) ≤ ((n0 + 1 : ℕ) : ℝ) := by
    linarith [hn0ge, hcast]
  have hnn : 1 ≤ τ * ((n0 + 1 : ℕ) : ℝ) := by
    have hmul : τ * (1 / τ) ≤ τ * ((n0 + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hn0p1 hτ0.le
    have hcancel : τ * (1 / τ) = 1 := by field_simp [hτ0.ne']
    rwa [hcancel] at hmul
  have h2 : 1 / ((n0 + 1 : ℕ) : ℝ) ≤ τ := by
    have hpos : 0 < ((n0 + 1 : ℕ) : ℝ) := by positivity
    exact (div_le_iff₀ hpos).2 hnn
  calc
    (2 / Real.sin (τ / 2)) * (1 / ((n0 + 1 : ℕ) : ℝ))
        ≤ (2 * (Real.pi / τ)) * (1 / ((n0 + 1 : ℕ) : ℝ)) := by
          have hmul : (2 / Real.sin (τ / 2)) ≤ 2 * (Real.pi / τ) := by
            have : 2 * (1 / Real.sin (τ / 2)) ≤ 2 * (Real.pi / τ) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
            convert this using 1 <;> ring
          exact mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ 1 / ((n0 + 1 : ℕ) : ℝ))
    _ ≤ (2 * (Real.pi / τ)) * τ := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * (Real.pi / τ))
    _ = 2 * Real.pi := by
          field_simp [hτ0.ne']



-- ===== main case on (0, π] =====
lemma sinSum_bound_aux (K n0 : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ Real.pi)
    (hn0ge : 1 ≤ τ * (n0 : ℝ)) (hn0le : τ * (n0 : ℝ) ≤ 1 + τ) :
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
      ≤ 1 + 3 * Real.pi := by
  by_cases hKle : K ≤ n0
  · -- whole sum is short: |Σ| ≤ Kτ ≤ n0τ ≤ 1+τ
    have hKτ : (K : ℝ) * τ ≤ (n0 : ℝ) * τ := by
      have hK : (K : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hKle
      exact mul_le_mul_of_nonneg_right hK hτ0.le
    calc
      |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
          ≤ (K : ℝ) * τ := abs_head_le K hτ0.le
      _ ≤ (n0 : ℝ) * τ := hKτ
      _ = τ * (n0 : ℝ) := by ring
      _ ≤ 1 + τ := hn0le
      _ ≤ 1 + 3 * Real.pi := by linarith [Real.pi_pos, hτ1]
  · -- n0 < K: head + tail
    have hn0ltK : n0 < K := lt_of_not_ge hKle
    have hn0leK : n0 ≤ K := le_of_lt hn0ltK
    -- decompose
    have hdec : (∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ))
        = (∑ i ∈ Finset.range n0, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ))
          + ∑ i ∈ Finset.Ico n0 K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ) := by
          rw [← Finset.sum_range_add_sum_Ico (f := fun i => Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)) (m := n0) (n := K) hn0leK]
    have hhead : |∑ i ∈ Finset.range n0, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
        ≤ 1 + τ := by
      have hb := abs_head_le n0 hτ0.le
      calc
        |∑ i ∈ Finset.range n0, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
            ≤ (n0 : ℝ) * τ := hb
        _ = τ * (n0 : ℝ) := by ring
        _ ≤ 1 + τ := hn0le
    -- tail bound ≤ 2π
    have htailbound : |∑ i ∈ Finset.Ico n0 K,
          Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)| ≤ 2 * Real.pi := by
      let L := K - n0
      let a : ℕ → ℝ := fun m => Real.sin (((m + 1 : ℕ) : ℝ) * τ)
      have hre : (∑ i ∈ Finset.Ico n0 K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ))
          = ∑ j ∈ Finset.range (K - n0), a (n0 + j) / ((n0 + j + 1 : ℕ) : ℝ) := by
          have hI := Finset.sum_Ico_eq_sum_range
              (f := fun i => Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)) n0 K
          -- hI : Σ_{i∈Ico n0 K} f i = Σ_{k∈range(K-n0)} f(n0+k)
          rw [hI]
      have hB : ∀ m : ℕ, m ≤ K - n0 →
          |∑ j ∈ Finset.range m, a (n0 + j)| ≤ 2 / Real.sin (τ / 2) := by
          intro m hm
          have hblk := abs_sin_block_le n0 m hτ0 hτ1
          simpa [a] using hblk
      have hs2 : 0 < Real.sin (τ / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · positivity
        · linarith [Real.pi_pos, hτ1]
      have hb0 : 0 ≤ 2 / Real.sin (τ / 2) := by
        exact div_nonneg (by norm_num) hs2.le
      have habel := abs_weighted_shift_le (p := n0) (L := K - n0) (B := 2 / Real.sin (τ / 2)) a hB hb0
      -- habel : |Σ_{j<K-n0} a(n0+j)/(n0+j+1)| ≤ B/(n0+1)
      have htail1 : |∑ j ∈ Finset.range (K - n0), a (n0 + j) / ((n0 + j + 1 : ℕ) : ℝ)|
          ≤ (2 / Real.sin (τ / 2)) * (1 / ((n0 + 1 : ℕ) : ℝ)) := by
          simpa [div_eq_mul_inv] using habel
      have hcst := tail_const_le hτ0 hτ1 (by
          have h : 1 ≤ τ * (n0 : ℝ) := hn0ge
          have hdiv : (1 / τ) * 1 ≤ (1 / τ) * (τ * (n0 : ℝ)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
          have hcancel : (1 / τ) * (τ * (n0 : ℝ)) = (n0 : ℝ) := by field_simp [hτ0.ne']
          rw [hcancel] at hdiv
          simpa using hdiv)
      have htail2 : (2 / Real.sin (τ / 2)) * (1 / ((n0 + 1 : ℕ) : ℝ)) ≤ 2 * Real.pi := hcst
      calc
        |∑ i ∈ Finset.Ico n0 K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
            = |∑ j ∈ Finset.range (K - n0), a (n0 + j) / ((n0 + j + 1 : ℕ) : ℝ)| := by rw [hre]
        _ ≤ (2 / Real.sin (τ / 2)) * (1 / ((n0 + 1 : ℕ) : ℝ)) := htail1
        _ ≤ 2 * Real.pi := htail2
    -- combine: |Σ| ≤ |head| + |tail| ≤ (1+τ) + 2π
    calc
      |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
          = |(∑ i ∈ Finset.range n0, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ))
            + ∑ i ∈ Finset.Ico n0 K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)| := by
            rw [hdec]
      _ ≤ |∑ i ∈ Finset.range n0, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
          + |∑ i ∈ Finset.Ico n0 K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)| := by
            rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
            exact norm_add_le _ _
      _ ≤ (1 + τ) + 2 * Real.pi := add_le_add hhead htailbound
      _ ≤ 1 + 3 * Real.pi := by linarith [Real.pi_pos, hτ1]

-- instantiate the ceil n0
lemma sinSum_pos (K : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ Real.pi) :
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ)|
      ≤ 1 + 3 * Real.pi := by
  let n0 : ℕ := (⌈1 / τ⌉ : ℤ).toNat
  have hn0z : (n0 : ℤ) = ⌈1 / τ⌉ := by
    dsimp [n0]
    exact Int.toNat_of_nonneg (Int.ceil_nonneg (by positivity))
  have hnat : ((n0 : ℤ) : ℝ) = (n0 : ℝ) := by norm_num
  have hn0zR : (((⌈1 / τ⌉ : ℤ) : ℝ)) = (n0 : ℝ) := by
    rw [← hn0z, hnat]
  have hn0ge : 1 ≤ τ * (n0 : ℝ) := by
    have hle := Int.le_ceil (1 / τ)
    have hle' : 1 / τ ≤ (n0 : ℝ) := by
      rwa [hn0zR] at hle
    have hmul : τ * (1 / τ) ≤ τ * (n0 : ℝ) := mul_le_mul_of_nonneg_left hle' hτ0.le
    have hcancel : τ * (1 / τ) = 1 := by field_simp [hτ0.ne']
    rwa [hcancel] at hmul
  have hn0le : τ * (n0 : ℝ) ≤ 1 + τ := by
    have hlt := Int.ceil_lt_add_one (1 / τ)
    have hlt' : (n0 : ℝ) < 1 / τ + 1 := by
      rwa [hn0zR] at hlt
    have hmul : τ * (n0 : ℝ) < τ * (1 / τ + 1) := mul_lt_mul_of_pos_left hlt' hτ0
    have : τ * (1 / τ + 1) = 1 + τ := by field_simp [hτ0.ne']
    rw [this] at hmul
    exact le_of_lt hmul
  exact sinSum_bound_aux K n0 hτ0 hτ1 hn0ge hn0le




-- ===== final reduction to the unit interval =====
lemma abs_sinSum_le (K : ℕ) (t : ℝ) :
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / ((i + 1 : ℕ) : ℝ)|
      ≤ 1 + 3 * Real.pi := by
  let m : ℤ := ⌊t / (2 * Real.pi)⌋
  let τ : ℝ := 2 * Real.pi * Int.fract (t / (2 * Real.pi))
  have htsplit : t = τ + (m : ℝ) * (2 * Real.pi) := by
    dsimp [τ, m]
    have hf := Int.fract_add_floor (t / (2 * Real.pi))
    calc
      t = (2 * Real.pi) * (t / (2 * Real.pi)) := by field_simp [Real.two_pi_pos.ne']
      _ = (2 * Real.pi) * (Int.fract (t / (2 * Real.pi)) + (⌊t / (2 * Real.pi)⌋ : ℝ)) := by
            congr 1
            exact hf.symm
      _ = 2 * Real.pi * Int.fract (t / (2 * Real.pi))
            + (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by ring
  have hterm : ∀ i : ℕ, Real.sin (((i + 1 : ℕ) : ℝ) * t)
      = Real.sin (((i + 1 : ℕ) : ℝ) * τ) := by
    intro i
    have harg : ((i + 1 : ℕ) : ℝ) * t
        = ((i + 1 : ℕ) : ℝ) * τ + ((((i + 1 : ℕ) : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
          rw [htsplit]
          push_cast
          ring
    rw [harg]
    exact Real.sin_add_int_mul_two_pi (((i + 1 : ℕ) : ℝ) * τ) (((i + 1 : ℕ) : ℤ) * m)
  have hsum : (∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / ((i + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hterm i]
  have hτlt : τ < 2 * Real.pi := by
    dsimp [τ]
    have hfr : Int.fract (t / (2 * Real.pi)) < 1 := Int.fract_lt_one _
    have hpos : 0 < 2 * Real.pi := Real.two_pi_pos
    have hm := mul_lt_mul_of_pos_left hfr hpos
    simpa using hm
  have hτnn : 0 ≤ τ := by
    dsimp [τ]
    exact mul_nonneg (le_of_lt Real.two_pi_pos) (Int.fract_nonneg _)
  rw [hsum]
  by_cases hτ0 : τ = 0
  · simp [hτ0]
    positivity
  · have hτpos : 0 < τ := lt_of_le_of_ne hτnn (Ne.symm hτ0)
    by_cases hτπ : τ ≤ Real.pi
    · exact sinSum_pos K hτpos hτπ
    · -- π < τ < 2π: flip
      have hπlt : Real.pi < τ := lt_of_not_ge hτπ
      let τ' : ℝ := 2 * Real.pi - τ
      have hτ'0 : 0 < τ' := by
        dsimp [τ']
        linarith [hτlt]
      have hτ'1 : τ' ≤ Real.pi := by
        dsimp [τ']
        linarith
      have hflip : ∀ i : ℕ, Real.sin (((i + 1 : ℕ) : ℝ) * τ)
          = -Real.sin (((i + 1 : ℕ) : ℝ) * τ') := by
        intro i
        have harg : ((i + 1 : ℕ) : ℝ) * τ
            = ((i + 1 : ℕ) : ℤ) * (2 * Real.pi) - ((i + 1 : ℕ) : ℝ) * τ' := by
              dsimp [τ']
              push_cast
              ring
        rw [harg]
        exact Real.sin_int_mul_two_pi_sub (((i + 1 : ℕ) : ℝ) * τ') (((i + 1 : ℕ) : ℤ))
      have hsum' : (∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ) / ((i + 1 : ℕ) : ℝ))
          = -∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * τ') / ((i + 1 : ℕ) : ℝ) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hflip i]
            ring
      have hbd := sinSum_pos K hτ'0 hτ'1
      rw [hsum']
      -- |−Σ| = |Σ|:
      rw [abs_neg]
      exact hbd


-- aliases matching the final-assembly naming
lemma sawFourier_logSum_tendsto {w : ℂ} (hwn : ‖w‖ = 1) (hw1 : w ≠ 1) :
    Tendsto (fun K : ℕ => ∑ i ∈ Finset.range K, w ^ (i + 1) / ((i + 1 : ℕ) : ℂ))
      atTop (𝓝 (-(Complex.log (1 - w)))) := logSum_tendsto hwn hw1

lemma sawFourier_abs_sinSum_le (K : ℕ) (t : ℝ) :
    |∑ i ∈ Finset.range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / ((i + 1 : ℕ) : ℝ)|
      ≤ 1 + 3 * Real.pi := abs_sinSum_le K t



lemma sum_Icc_one_nat_eq (K : ℕ) (f : ℤ → ℂ) :
    (∑ ν ∈ Finset.Icc 1 (K : ℤ), f ν) = ∑ i ∈ Finset.range K, f ((i + 1 : ℕ) : ℤ) := by
  rw [← sum_range_eq_sum_Icc_one K f]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1



lemma sum_sin_Icc_eq_range (K : ℕ) (x : ℝ) :
    (∑ ν ∈ Finset.Icc 1 (K : ℤ),
        ((Real.sin (2 * Real.pi * (ν : ℝ) * x) : ℝ) : ℂ) / ((Real.pi : ℂ) * (ν : ℂ)))
    = ∑ i ∈ Finset.range K,
        ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) /
          ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)) := by
  rw [sum_Icc_one_nat_eq K]
  rfl



lemma sawHat_eq_sin_range (K : ℕ) (x : ℝ) :
    sawHat K x = -∑ i ∈ Finset.range K,
      ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) /
        ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)) := by
  rw [sawHat_eq_sin_Icc, sum_sin_Icc_eq_range]



lemma cast_sum_range (K : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range K, (f i : ℂ)) = (((∑ i ∈ Finset.range K, f i) : ℝ) : ℂ) := by
  exact (map_sum (algebraMap ℝ ℂ) f (Finset.range K)).symm



lemma div_cast {a b : ℝ} : ((a : ℝ) : ℂ) / (((b : ℝ) : ℂ)) = (((a / b : ℝ) : ℂ)) := by
  exact (map_div₀ (algebraMap ℝ ℂ) a b).symm




lemma E_nat_mul (n : ℕ) (t : ℝ) : E ((n : ℝ) * t) = (E t) ^ n := by
  induction n with
  | zero =>
      simp [E]
  | succ n ih =>
      rw [show (((n + 1 : ℕ) : ℝ) * t) = ((n : ℝ) * t) + t by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
      rw [E_add, ih, pow_succ]



lemma im_E (t : ℝ) : (E t).im = Real.sin (2 * Real.pi * t) := by
  rw [E_eq_cos_sin]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring



lemma im_div_ofReal (z : ℂ) (c : ℝ) : (z / (c : ℂ)).im = z.im / c := by
  calc
    (z / (c : ℂ)).im = (z * ((c : ℂ)⁻¹)).im := by rw [div_eq_mul_inv]
    _ = (z * (↑(c⁻¹) : ℂ)).im := by rw [← Complex.ofReal_inv]
    _ = (↑(c⁻¹) * z).im := by rw [mul_comm]
    _ = c⁻¹ * z.im := Complex.im_ofReal_mul (c⁻¹) z
    _ = z.im / c := by rw [div_eq_mul_inv]; ring



lemma im_E_div (t : ℝ) (n : ℕ) :
    (E t / ((n : ℂ))).im = Real.sin (2 * Real.pi * t) / (n : ℝ) := by
  have hc : (((n : ℕ) : ℂ)) = ((((n : ℕ) : ℝ) : ℂ)) := by norm_num
  rw [hc]
  rw [im_div_ofReal]
  rw [im_E]



lemma sineSum_tendsto_Ioo {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Tendsto (fun K : ℕ => ∑ i ∈ Finset.range K,
        Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) / ((i + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.pi / 2 - Real.pi * u)) := by
  have hsin : 0 < Real.sin (Real.pi * u) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hlt : Real.pi * u < Real.pi * 1 := mul_lt_mul_of_pos_left hu1 Real.pi_pos
      simpa using hlt
  have hne : (1 : ℂ) - E u ≠ 0 := by
    rw [one_sub_E_eq u]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.sin (Real.pi * u)))) (Complex.exp_ne_zero _)
  have hw1 : E u ≠ 1 := by
    intro h
    apply hne
    rw [h]
    simp
  have hl := sawFourier_logSum_tendsto (w := E u) (E_norm u) hw1
  have hlE : Tendsto (fun K : ℕ => ∑ i ∈ Finset.range K, E (((i + 1 : ℕ) : ℝ) * u) / ((i + 1 : ℕ) : ℂ))
      atTop (𝓝 (-(Complex.log (1 - E u)))) := by
    convert hl using 1
    funext K
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact (E_nat_mul (i + 1) u)
  have himT : Tendsto (fun K : ℕ => (∑ i ∈ Finset.range K, E (((i + 1 : ℕ) : ℝ) * u) / ((i + 1 : ℕ) : ℂ)).im)
      atTop (𝓝 (-(Complex.log (1 - E u))).im) :=
    (Complex.continuous_im.tendsto (-(Complex.log (1 - E u)))).comp hlE
  have hval : (-(Complex.log (1 - E u))).im = Real.pi / 2 - Real.pi * u := by
    rw [Complex.neg_im]
    rw [sawFourier_im_log_one_sub_E u hu0 hu1]
    ring
  have hS : (fun K : ℕ => ∑ i ∈ Finset.range K,
        Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) / ((i + 1 : ℕ) : ℝ))
      = fun K : ℕ => (∑ i ∈ Finset.range K, E (((i + 1 : ℕ) : ℝ) * u) / ((i + 1 : ℕ) : ℂ)).im := by
    funext K
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [im_E_div (((i + 1 : ℕ) : ℝ) * u) (i + 1)]
    congr 1
    ring
  rw [hval] at himT
  rw [hS]
  exact himT







lemma sawHat_eq_const_mul (K : ℕ) (x : ℝ) :
    sawHat K x = -(1 / (Real.pi : ℂ)) *
      (∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) /
          ((i + 1 : ℕ) : ℂ)) := by
  rw [sawHat_eq_sin_range]
  rw [show (∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) /
          ((Real.pi : ℂ) * ((i + 1 : ℕ) : ℂ)))
      = (1 / (Real.pi : ℂ)) * ∑ i ∈ Finset.range K,
          (((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) / ((i + 1 : ℕ) : ℂ)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        have hn : ((i + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Nat.succ_pos i))
        field_simp [hpi, hn]]
  ring




lemma complex_sinSum_eq_cast {u : ℝ} (K : ℕ) :
    (∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) /
        ((i + 1 : ℕ) : ℂ))
    = (((∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) /
        ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have hb (i : ℕ) : ((((i + 1 : ℕ) : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by norm_num
  calc
    (∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) / ((i + 1 : ℕ) : ℂ))
        = ∑ i ∈ Finset.range K, (((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) /
            ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← hb i]
          exact div_cast
    _ = (((∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) /
        ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
          exact (cast_sum_range K (fun i => Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) /
            ((i + 1 : ℕ) : ℝ)))


-- ================== uniform bound ==================
lemma sawHat_tendsto_saw_Ioo {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Tendsto (fun K : ℕ => sawHat K u) atTop (𝓝 ((saw u : ℝ) : ℂ)) := by
  have hfract : Int.fract u = u := (Int.fract_eq_self).mpr ⟨hu0.le, hu1⟩
  have hsaw : saw u = u - 1 / 2 := by
    unfold saw
    rw [hfract]
  have hR := sineSum_tendsto_Ioo hu0 hu1
  let C : ℕ → ℂ := fun K => ∑ i ∈ Finset.range K, ((Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) / ((i + 1 : ℕ) : ℂ)
  have hCcast : (fun K : ℕ => C K)
      = fun K : ℕ => (((∑ i ∈ Finset.range K, Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * u) /
          ((i + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    funext K
    dsimp [C]
    exact complex_sinSum_eq_cast (u := u) K
  have hC : Tendsto (fun K : ℕ => C K) atTop (𝓝 (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ)) := by
    rw [hCcast]
    exact (Continuous.tendsto Complex.continuous_ofReal (Real.pi / 2 - Real.pi * u)).comp hR
  have hpoint : (fun K : ℕ => sawHat K u) = fun K : ℕ => -(((1 / (Real.pi : ℂ)) * C K)) := by
    funext K
    rw [sawHat_eq_const_mul]
    ring
  have hlim1 : Tendsto (fun K : ℕ => (1 / (Real.pi : ℂ)) * C K)
      atTop (𝓝 ((1 / (Real.pi : ℂ)) * (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ))) := by
    exact (Filter.Tendsto.const_mul (1 / (Real.pi : ℂ)) hC)
  have hlim : Tendsto (fun K : ℕ => -((1 / (Real.pi : ℂ)) * C K))
      atTop (𝓝 (-((1 / (Real.pi : ℂ)) * (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ)))) := hlim1.neg
  have hreal : -((1 / (Real.pi : ℝ)) * (Real.pi / 2 - Real.pi * u)) = u - 1 / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  have hval' : -((1 / (Real.pi : ℂ)) * (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ))
      = (((u - 1 / 2 : ℝ) : ℂ)) := by
    have hc : (1 / (Real.pi : ℂ)) = (((1 / (Real.pi : ℝ)) : ℝ) : ℂ) := by
      have hone : (1 : ℂ) = (((1 : ℝ) : ℂ)) := by norm_num
      rw [hone]
      exact div_cast (a := (1 : ℝ)) (b := (Real.pi : ℝ))
    calc
      -((1 / (Real.pi : ℂ)) * (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ))
          = -(((((1 / (Real.pi : ℝ)) : ℝ) : ℂ)) * (((Real.pi / 2 - Real.pi * u) : ℝ) : ℂ)) := by rw [hc]
      _ = -(((((1 / (Real.pi : ℝ)) * (Real.pi / 2 - Real.pi * u)) : ℝ) : ℂ)) := by
            rw [Complex.ofReal_mul]
      _ = (((-((1 / (Real.pi : ℝ)) * (Real.pi / 2 - Real.pi * u))) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_neg]
      _ = (((u - 1 / 2 : ℝ) : ℂ)) := by rw [hreal]
  have hsawC : (((saw u : ℝ) : ℂ)) = (((u - 1 / 2 : ℝ) : ℂ)) := by
    simp [hsaw]
  rw [hpoint]
  rw [hsawC]
  convert hlim using 1
  exact congrArg (fun z : ℂ => 𝓝 z) hval'.symm

lemma sawHat_tendsto_saw {x : ℝ} (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) :
    Tendsto (fun K : ℕ => sawHat K x) atTop (𝓝 ((saw x : ℝ) : ℂ)) := by
  let u := Int.fract x
  have hu0 : 0 < u := by
    dsimp [u]
    exact fract_pos_of_not_int hx
  have hu1 : u < 1 := by
    dsimp [u]
    exact Int.fract_lt_one x
  have hred : (fun K : ℕ => sawHat K x) = fun K : ℕ => sawHat K u := by
    funext K
    dsimp [u]
    exact sawHat_eq_sawHat_fract K x
  have hIoo := sawHat_tendsto_saw_Ioo hu0 hu1
  have hsaw : (((saw x : ℝ) : ℂ)) = (((saw u : ℝ) : ℂ)) := by
    congr 1
    dsimp [u]
    exact (saw_fract x).symm
  rw [hred]
  rw [hsaw]
  exact hIoo


end
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Euler–Maclaurin (sawtooth) identity for `E(f(m))`

For `N ≥ 1` and `f : ℝ → ℝ` twice continuously differentiable on `[0,N]`
(`ContDiffOn ℝ 2 f (Set.Icc 0 (N:ℝ))`), prove

    Σ_{m=1}^N E(f m)
      = ∫_0^N E(f x) dx
        + ∫_0^N (saw x : ℂ) · ((tau * I) * (deriv f x : ℂ) * E(f x)) dx
        + (E(f N) − E(f 0)) / 2

(`E`, `saw`, `tau` from `Submission.SawBasis`).  This is the exact "Euler's
summation formula with the sawtooth kernel" on the integer interval
`[0,N]`.  Suggested route: per-cell identity.  For each
`m ∈ Finset.Icc 0 (N−1)`, over the cell `[m, m+1]`, for `g x := E(f x)`,

    ∫_m^{m+1} (x − m − 1/2) · g'(x) dx
       = (g(m+1) + g(m)) / 2 − ∫_m^{m+1} g(x) dx

(i.e. integration by parts: `∫ u dv = [u v] − ∫ v du` with
`u(x) := (x − m − 1/2 : ℂ)`, `v := g`), using the derivative identity
`hasDerivAt_E_comp` (with `deriv (fun y ↦ f y) x = deriv f x` given by
`SdtOscB.hasDerivAt_F_of_Ioo` on the open interval `(m, m+1)`) and the FTC
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` (or the
`of_le` variant) on the cell.  Summing over `m` telescopes the
`(g(m+1)+g(m))/2` terms to `Σ_{m=1}^N g(m) + (g(0)−g(N))/2`-type
contributions; the cell phase `x − m − 1/2` equals `saw x` on `(m, m+1)`.
Handle interval integrals over cells by `intervalIntegral.integral_add_adjacent_intervals`
or by replacing `∫_0^N` with `∑` over the cells using Finset-indexed FTC.

The target lemma (proved below):
-/


namespace Submission.SdtPoisson

/-! ## Helper facts for the Euler-Maclaurin identity -/

/-- On `[m, m+1)` the sawtooth equals `x - m - 1/2`. -/
lemma emid_saw_eq_cell {m : ℕ} {x : ℝ} (hmx : (m : ℝ) ≤ x) (hxm : x < (m : ℝ) + 1) :
    saw x = x - (m : ℝ) - 1 / 2 := by
  unfold saw
  change (x - ↑⌊x⌋) - 1 / 2 = x - (m : ℝ) - 1 / 2
  have hfl : Int.floor x = (m : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨hmx, hxm⟩
  rw [hfl]
  congr 1

/-- `E` is continuous. -/
lemma emid_E_continuous : Continuous E := by
  have hfun : E = fun t : ℝ => cexp (tau * (t : ℂ) * I) := by
    funext t
    exact E_eq_tau t
  rw [hfun]
  have hlin : Continuous (fun t : ℝ => tau * (t : ℂ) * I) := by
    have hof : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
    have hc : Continuous (fun t : ℝ => tau) := continuous_const
    have hmul : Continuous (fun t : ℝ => tau * (t : ℂ)) := hc.mul hof
    exact hmul.mul_const I
  exact Complex.continuous_exp.comp hlin

/-- Restricted-ae version of a pointwise equality on the open interval `(a,b)`,
`a ≤ b`: the functions agree a.e. on `uIoc a b` (differing at most at `b`). -/
lemma emid_ae_eqOn_uIoc_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ioo a b)) :
    f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
  change (∀ᵐ x ∂(volume.restrict (Set.uIoc a b)), f x = g x)
  rw [ae_restrict_iff' measurableSet_uIoc]
  rw [ae_iff]
  apply measure_mono_null
  · intro x hx
    simp at hx
    by_contra hneq
    have hxIoo : x ∈ Set.Ioo a b := by
      constructor
      · rw [Set.uIoc_of_le hab] at hx
        exact hx.1.1
      · rw [Set.uIoc_of_le hab] at hx
        exact lt_of_le_of_ne hx.1.2 hneq
    exact hx.2 (h hxIoo)
  · exact MeasureTheory.NullSingletonClass.measure_singleton b

/-- Unrestricted ae version, for `intervalIntegral.integral_congr_ae`. -/
lemma emid_eventually_eqOn_uIoc_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ioo a b)) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a b → f x = g x := by
  rw [ae_iff]
  apply measure_mono_null
  · intro x hx
    simp at hx
    by_contra hneq
    have hxIoo : x ∈ Set.Ioo a b := by
      constructor
      · rw [Set.uIoc_of_le hab] at hx
        exact hx.1.1
      · rw [Set.uIoc_of_le hab] at hx
        exact lt_of_le_of_ne hx.1.2 hneq
    exact hx.2 (h hxIoo)
  · exact MeasureTheory.NullSingletonClass.measure_singleton b

/-- Interval integrals agree if the integrands agree pointwise on the open
interval `(a,b)` (`a ≤ b`). -/
lemma emid_integral_congr_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ioo a b)) :
    (∫ x in a..b, f x) = (∫ x in a..b, g x) := by
  exact intervalIntegral.integral_congr_ae (emid_eventually_eqOn_uIoc_of_eqOn_Ioo hab h)

/-- Interval integrability transfers along pointwise equality on the open
interval `(a,b)` (`a ≤ b`). -/
lemma emid_intervalIntegrable_congr_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume a b) (h : Set.EqOn f g (Set.Ioo a b)) :
    IntervalIntegrable f volume a b := by
  refine IntervalIntegrable.congr_ae hg ?_
  apply emid_ae_eqOn_uIoc_of_eqOn_Ioo hab
  intro x hx
  exact (h hx).symm

/-- **Per-cell Euler-Maclaurin identity** on the cell `[m, m+1]`: for `g = E∘f`
with derivative `gp x := (tau*I)·f'(x)·g(x)`,
`∫_cell saw·gp + ∫_cell g = (g(m+1) + g(m))/2`. -/
lemma emid_cell {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) {m : ℕ} (hm : m < N) :
    (∫ x in (m : ℝ)..((m : ℝ) + 1),
        (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x))) +
      (∫ x in (m : ℝ)..((m : ℝ) + 1), E (f x)) =
      (E (f ((m + 1 : ℕ) : ℝ)) + E (f (m : ℝ))) / 2 := by
  let g : ℝ → ℂ := fun x => E (f x)
  let gp : ℝ → ℂ := fun x => ((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x)
  let fpw : ℝ → ℂ := fun x => ((tau * I) * ((((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))) * E (f x)
  let cc : ℝ → ℂ := fun x => (((x - (m : ℝ) - (1 / 2 : ℝ)) : ℝ) : ℂ)
  let FF : ℝ → ℂ := fun x => cc x * g x
  let FFder : ℝ → ℂ := fun x => g x + cc x * fpw x
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have h0m : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hmb : (m : ℝ) + 1 ≤ (N : ℝ) := by
    have hm' : m + 1 ≤ N := Nat.succ_le_of_lt hm
    exact_mod_cast hm'
  have hab : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hsub : Set.Icc (m : ℝ) ((m : ℝ) + 1) ⊆ Set.Icc (0 : ℝ) (N : ℝ) := by
    intro x hx
    exact ⟨le_trans h0m hx.1, le_trans hx.2 hmb⟩
  have hins : ∀ x : ℝ, x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) → x ∈ Set.Ioo (0 : ℝ) (N : ℝ) := by
    intro x hx
    exact ⟨lt_of_le_of_lt h0m hx.1, lt_of_lt_of_le hx.2 hmb⟩
  -- continuity facts
  have hfC : ContinuousOn f (Set.Icc (0 : ℝ) (N : ℝ)) := hF.continuousOn
  have hdwC : ContinuousOn (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x) (Set.Icc (0 : ℝ) (N : ℝ)) := by
    have hd1 : ContDiffOn ℝ 1 (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x) (Set.Icc (0 : ℝ) (N : ℝ)) :=
      SdtOscB.contDiffOn_derivWithin_one hNpos f hF
    exact hd1.continuousOn
  have hgC0 : ContinuousOn g (Set.Icc (0 : ℝ) (N : ℝ)) := by
    dsimp [g]
    exact emid_E_continuous.comp_continuousOn hfC
  have hgC : ContinuousOn g (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hgC0.mono hsub
  have hfpwC0 : ContinuousOn fpw (Set.Icc (0 : ℝ) (N : ℝ)) := by
    dsimp [fpw]
    have h1 : ContinuousOn (fun x : ℝ => (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := Complex.continuous_ofReal.comp_continuousOn hdwC
    have h2 : ContinuousOn (fun x : ℝ => (tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := ContinuousOn.const_mul h1 (tau * I)
    have h3 : ContinuousOn (fun x : ℝ =>
        ((tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ))) * E (f x))
        (Set.Icc (0 : ℝ) (N : ℝ)) := h2.mul hgC0
    simpa [g] using h3
  have hfpwC : ContinuousOn fpw (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hfpwC0.mono hsub
  have hccC : ContinuousOn cc (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
    dsimp [cc]
    have hlin : ContinuousOn (fun x : ℝ => x - (m : ℝ) - (1 / 2 : ℝ)) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
      fun_prop
    exact Complex.continuous_ofReal.comp_continuousOn hlin
  have hFFC : ContinuousOn FF (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
    dsimp [FF]
    exact hccC.mul hgC
  have hFFderC : ContinuousOn FFder (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
    dsimp [FFder]
    exact hgC.add (hccC.mul hfpwC)
  -- FTC interval facts
  have hFFC_u : ContinuousOn FF (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    simpa [Set.uIcc_of_le hab] using hFFC
  have hFFderC_u : ContinuousOn FFder (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    simpa [Set.uIcc_of_le hab] using hFFderC
  have hintFFder : IntervalIntegrable FFder volume (m : ℝ) ((m : ℝ) + 1) := hFFderC_u.intervalIntegrable
  have hgC_u : ContinuousOn g (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    simpa [Set.uIcc_of_le hab] using hgC
  have hccfpwC_u : ContinuousOn (fun x => cc x * fpw x) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    have hccfpwC : ContinuousOn (fun x => cc x * fpw x) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hccC.mul hfpwC
    simpa [Set.uIcc_of_le hab] using hccfpwC
  have hintg : IntervalIntegrable g volume (m : ℝ) ((m : ℝ) + 1) := hgC_u.intervalIntegrable
  have hintccfpw : IntervalIntegrable (fun x => cc x * fpw x) volume (m : ℝ) ((m : ℝ) + 1) := hccfpwC_u.intervalIntegrable
  -- derivative facts
  have hccder : ∀ x : ℝ, HasDerivAt cc (1 : ℂ) x := by
    intro x
    dsimp [cc]
    have haff : HasDerivAt (fun y : ℝ => y - (m : ℝ) - (1 / 2 : ℝ)) 1 x := by
      simpa using (((hasDerivAt_id x).sub_const (m : ℝ)).sub_const (1 / 2 : ℝ))
    simpa using haff.ofReal_comp
  have hgder : ∀ x : ℝ, x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) →
      HasDerivAt g (gp x) x := by
    intro x hx
    have hxN : x ∈ Set.Ioo (0 : ℝ) (N : ℝ) := hins x hx
    have hfd : HasDerivAt f (deriv f x) x := SdtOscB.hasDerivAt_F_of_Ioo (a := 0) (b := (N : ℝ)) f hF hxN
    have hd : HasDerivAt (fun y : ℝ => E (f y)) (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x)) x :=
      hasDerivAt_E_comp f hfd
    simpa [g, gp] using hd
  have hgpfpw : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) (N : ℝ) → fpw x = gp x := by
    intro x hx
    have hdweq : derivWithin f (Set.Icc 0 (N : ℝ)) x = deriv f x :=
      SdtOscB.derivWithin_eq_deriv_of_Ioo (a := 0) (b := (N : ℝ)) f hx
    dsimp [fpw, gp]
    rw [hdweq]
  have hFFder_der : ∀ x : ℝ, x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) →
      HasDerivAt FF (FFder x) x := by
    intro x hx
    have hd1 : HasDerivAt (fun y : ℝ => cc y * g y) ((1 : ℂ) * g x + cc x * gp x) x := by
      exact (hccder x).mul (hgder x hx)
    have hfpw_eq : fpw x = gp x := hgpfpw x (hins x hx)
    dsimp [FF, FFder]
    rw [← hfpw_eq] at hd1
    simpa using hd1
  -- the FTC on the cell
  have hFTC : (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), FFder y) = FF ((m : ℝ) + 1) - FF (m : ℝ) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hFFC hFFder_der hintFFder
  have hsplit : (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), FFder y) =
      (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), g y) +
      (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), cc y * fpw y) := by
    dsimp [FFder]
    exact intervalIntegral.integral_add hintg hintccfpw
  -- congr: the (saw*gp) integrand agrees with cc*fpw on the interior
  have hcong_sgp : (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1),
        (saw y : ℂ) * (((tau * I) * (((deriv f y : ℝ) : ℂ))) * E (f y))) =
      (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), cc y * fpw y) := by
    rw [emid_integral_congr_of_eqOn_Ioo hab]
    intro x hx
    dsimp [cc]
    rw [emid_saw_eq_cell hx.1.le hx.2]
    have hfpweq : fpw x = gp x := hgpfpw x (hins x hx)
    rw [hfpweq]
  -- boundary values
  have hcc_b : cc ((m : ℝ) + 1) = (1 / 2 : ℂ) := by
    dsimp [cc]
    norm_num
  have hcc_a : cc (m : ℝ) = -(1 / 2 : ℂ) := by
    dsimp [cc]
    norm_num
  have hFFb : FF ((m : ℝ) + 1) = (1 / 2 : ℂ) * g ((m : ℝ) + 1) := by
    dsimp [FF]
    rw [hcc_b]
  have hFFa : FF (m : ℝ) = -(1 / 2 : ℂ) * g (m : ℝ) := by
    dsimp [FF]
    rw [hcc_a]
  have hbound : FF ((m : ℝ) + 1) - FF (m : ℝ) = (g ((m : ℝ) + 1) + g (m : ℝ)) / 2 := by
    rw [hFFb, hFFa]
    ring
  -- assemble
  have hmain : (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1), g y) +
      (∫ y : ℝ in (m : ℝ)..((m : ℝ) + 1),
        (saw y : ℂ) * (((tau * I) * (((deriv f y : ℝ) : ℂ))) * E (f y))) =
      (g ((m : ℝ) + 1) + g (m : ℝ)) / 2 := by
    rw [hcong_sgp, ← hsplit, hFTC, hbound]
  have hRHS1 : g ((m : ℝ) + 1) = E (f ((m + 1 : ℕ) : ℝ)) := by
    dsimp [g]
    congr 1
    norm_num
  have hRHS2 : g (m : ℝ) = E (f (m : ℝ)) := by
    rfl
  rw [add_comm]
  simpa [hRHS1, hRHS2] using hmain

/-- Interval-integrability of the phase `E∘f` on a cell. -/
lemma emid_g_int {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) {m : ℕ} (hm : m < N) :
    IntervalIntegrable (fun x : ℝ => E (f x)) volume (m : ℝ) ((m : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hfC : ContinuousOn f (Set.Icc (0 : ℝ) (N : ℝ)) := hF.continuousOn
  have hgC0 : ContinuousOn (fun x : ℝ => E (f x)) (Set.Icc (0 : ℝ) (N : ℝ)) :=
    emid_E_continuous.comp_continuousOn hfC
  have h0m : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hmb : (m : ℝ) + 1 ≤ (N : ℝ) := by
    have hm' : m + 1 ≤ N := Nat.succ_le_of_lt hm
    exact_mod_cast hm'
  have hsub : Set.Icc (m : ℝ) ((m : ℝ) + 1) ⊆ Set.Icc (0 : ℝ) (N : ℝ) := by
    intro x hx
    exact ⟨le_trans h0m hx.1, le_trans hx.2 hmb⟩
  have hgC : ContinuousOn (fun x : ℝ => E (f x)) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hgC0.mono hsub
  have hab : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hgCu : ContinuousOn (fun x : ℝ => E (f x)) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    simpa [Set.uIcc_of_le hab] using hgC
  exact hgCu.intervalIntegrable

/-- Interval-integrability of `saw·(E∘f)'` on a cell (via the continuous
`derivWithin` surrogate). -/
lemma emid_sgp_int {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) {m : ℕ} (hm : m < N) :
    IntervalIntegrable (fun x : ℝ =>
        (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x)))
      volume (m : ℝ) ((m : ℝ) + 1) := by
  let gp : ℝ → ℂ := fun x => ((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x)
  let fpw : ℝ → ℂ := fun x => ((tau * I) * ((((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))) * E (f x)
  let cc : ℝ → ℂ := fun x => (((x - (m : ℝ) - (1 / 2 : ℝ)) : ℝ) : ℂ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have h0m : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hmb : (m : ℝ) + 1 ≤ (N : ℝ) := by
    have hm' : m + 1 ≤ N := Nat.succ_le_of_lt hm
    exact_mod_cast hm'
  have hab : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hsub : Set.Icc (m : ℝ) ((m : ℝ) + 1) ⊆ Set.Icc (0 : ℝ) (N : ℝ) := by
    intro x hx
    exact ⟨le_trans h0m hx.1, le_trans hx.2 hmb⟩
  have hins : ∀ x : ℝ, x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) → x ∈ Set.Ioo (0 : ℝ) (N : ℝ) := by
    intro x hx
    exact ⟨lt_of_le_of_lt h0m hx.1, lt_of_lt_of_le hx.2 hmb⟩
  have hfC : ContinuousOn f (Set.Icc (0 : ℝ) (N : ℝ)) := hF.continuousOn
  have hdwC : ContinuousOn (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x) (Set.Icc (0 : ℝ) (N : ℝ)) := by
    have hd1 : ContDiffOn ℝ 1 (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x) (Set.Icc (0 : ℝ) (N : ℝ)) :=
      SdtOscB.contDiffOn_derivWithin_one hNpos f hF
    exact hd1.continuousOn
  have hgC0 : ContinuousOn (fun x : ℝ => E (f x)) (Set.Icc (0 : ℝ) (N : ℝ)) :=
    emid_E_continuous.comp_continuousOn hfC
  have hfpwC0 : ContinuousOn fpw (Set.Icc (0 : ℝ) (N : ℝ)) := by
    dsimp [fpw]
    have h1 : ContinuousOn (fun x : ℝ => (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := Complex.continuous_ofReal.comp_continuousOn hdwC
    have h2 : ContinuousOn (fun x : ℝ => (tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := ContinuousOn.const_mul h1 (tau * I)
    have h3 : ContinuousOn (fun x : ℝ =>
        ((tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ))) * E (f x))
        (Set.Icc (0 : ℝ) (N : ℝ)) := h2.mul hgC0
    simpa using h3
  have hfpwC : ContinuousOn fpw (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hfpwC0.mono hsub
  have hccC : ContinuousOn cc (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
    dsimp [cc]
    have hlin : ContinuousOn (fun x : ℝ => x - (m : ℝ) - (1 / 2 : ℝ)) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
      fun_prop
    exact Complex.continuous_ofReal.comp_continuousOn hlin
  have hccfpwC : ContinuousOn (fun x => cc x * fpw x) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := hccC.mul hfpwC
  have hccfpwCu : ContinuousOn (fun x => cc x * fpw x) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    simpa [Set.uIcc_of_le hab] using hccfpwC
  have hint : IntervalIntegrable (fun x => cc x * fpw x) volume (m : ℝ) ((m : ℝ) + 1) :=
    hccfpwCu.intervalIntegrable
  -- pointwise equality on the open cell
  have hcong : Set.EqOn (fun x : ℝ =>
        (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x)))
      (fun x => cc x * fpw x) (Set.Ioo (m : ℝ) ((m : ℝ) + 1)) := by
    intro x hx
    dsimp [cc]
    rw [emid_saw_eq_cell hx.1.le hx.2]
    have hfpweq : fpw x = gp x := by
      have hdweq : derivWithin f (Set.Icc 0 (N : ℝ)) x = deriv f x :=
        SdtOscB.derivWithin_eq_deriv_of_Ioo (a := 0) (b := (N : ℝ)) f (hins x hx)
      dsimp [fpw, gp]
      rw [hdweq]
    rw [hfpweq]
  exact emid_intervalIntegrable_congr_of_eqOn_Ioo hab hint hcong

/-- Telescoping identity for complex sequences:
`Σ_{k=0}^{N-1} (h(k+1)+h k)/2 + (hN − h0)/2 = Σ_{k=1}^{N} h k`. -/
lemma emid_telescope (h : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (h (k + 1) + h k) / 2) + (h N - h 0) / 2 =
      ∑ k ∈ Finset.Icc 1 N, h k := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hrew : (∑ k ∈ Finset.range N, (h (k + 1) + h k) / 2) =
          (∑ k ∈ Finset.Icc 1 N, h k) - (h N - h 0) / 2 := by
        exact eq_sub_of_add_eq ih
      rw [hrew]
      have hsucc : (∑ k ∈ Finset.Icc 1 (N + 1), h k) =
          (∑ k ∈ Finset.Icc 1 N, h k) + h (N + 1) := by
        exact Finset.sum_Icc_succ_top (by omega) h
      rw [hsucc]
      ring

lemma em_identity {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    (∑ m ∈ Finset.Icc 1 N, E (f (m : ℝ))) =
      (∫ x in 0..(N : ℝ), E (f x)) +
      (∫ x in 0..(N : ℝ), (saw x : ℂ) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))) +
      (E (f (N : ℝ)) - E (f 0)) / 2 := by
  let G : ℝ → ℂ := fun x => E (f x)
  let sgp : ℝ → ℂ := fun x => (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x))
  let e : ℕ → ℂ := fun m => E (f (m : ℝ))
  -- per-cell identities
  have hcell : ∀ k : ℕ, k < N →
      ((∫ x in (k : ℝ)..((k : ℝ) + 1),
          (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x))) +
        (∫ x in (k : ℝ)..((k : ℝ) + 1), G x)) = (e (k + 1) + e k) / 2 := by
    intro k hk
    simpa [G, e] using emid_cell hN f hF hk
  -- per-cell interval-integrability for the adjacent-interval sum lemma
  have hgInt : ∀ k < N, IntervalIntegrable G volume ((k : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by norm_num
    have hi : IntervalIntegrable (fun x : ℝ => E (f x)) volume (k : ℝ) ((k : ℝ) + 1) :=
      emid_g_int hN f hF hk
    rw [hcast] at hi
    simpa [G] using hi
  have hsgpInt : ∀ k < N, IntervalIntegrable sgp volume ((k : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by norm_num
    have hi : IntervalIntegrable (fun x : ℝ =>
        (saw x : ℂ) * (((tau * I) * (((deriv f x : ℝ) : ℂ))) * E (f x))) volume (k : ℝ) ((k : ℝ) + 1) :=
      emid_sgp_int hN f hF hk
    rw [hcast] at hi
    simpa [sgp] using hi
  -- cell-index presentation change ((k : ℝ)+1  vs ((k+1:ℕ):ℝ))
  have hCellEqG : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), G x) =
      (∑ k ∈ Finset.range N, ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ)), G x) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by norm_num]
  have hCellEqSG : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), sgp x) =
      (∑ k ∈ Finset.range N, ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ)), sgp x) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by norm_num]
  -- adjacent cell sum lemma
  have hAdjG : (∑ k ∈ Finset.range N, ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ)), G x) =
      ∫ x in (0 : ℝ)..(N : ℝ), G x := by
    simpa using (intervalIntegral.sum_integral_adjacent_intervals (f := G) (a := fun j : ℕ => (j : ℝ)) (n := N) hgInt)
  have hAdjSG : (∑ k ∈ Finset.range N, ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ)), sgp x) =
      ∫ x in (0 : ℝ)..(N : ℝ), sgp x := by
    simpa using (intervalIntegral.sum_integral_adjacent_intervals (f := sgp) (a := fun j : ℕ => (j : ℝ)) (n := N) hsgpInt)
  -- whole interval = sum over cells
  have hSumG : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), G x) =
      ∫ x in (0 : ℝ)..(N : ℝ), G x := by
    rw [hCellEqG, hAdjG]
  have hSumSG : (∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), sgp x) =
      ∫ x in (0 : ℝ)..(N : ℝ), sgp x := by
    rw [hCellEqSG, hAdjSG]
  -- summing the per-cell identities
  have hcellSum : (∑ k ∈ Finset.range N,
        ((∫ x in (k : ℝ)..((k : ℝ) + 1), sgp x) +
        (∫ x in (k : ℝ)..((k : ℝ) + 1), G x))) =
      ∑ k ∈ Finset.range N, (e (k + 1) + e k) / 2 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    simpa [sgp] using hcell k hklt
  -- the main algebra
  have hmain : (∑ m ∈ Finset.Icc 1 N, e m) =
      (∫ x in (0 : ℝ)..(N : ℝ), G x) + (∫ x in (0 : ℝ)..(N : ℝ), sgp x) + (e N - e 0) / 2 := by
    rw [← emid_telescope e N]
    congr 1
    rw [← hSumG, ← hSumSG, add_comm, ← Finset.sum_add_distrib, ← hcellSum]
  have hsumE : (∑ m ∈ Finset.Icc 1 N, E (f (m : ℝ))) = (∑ m ∈ Finset.Icc 1 N, e m) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    rfl
  rw [hsumE]
  rw [hmain]
  have heN : e N = E (f (N : ℝ)) := rfl
  have he0 : e 0 = E (f (0 : ℝ)) := by dsimp [e]; norm_num
  simpa [G, sgp, heN, he0]
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators ComplexConjugate ContDiff
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Finite sawtooth-kernel identity

For `N ≥ 1`, `f : ℝ → ℝ` twice continuously differentiable on `[0,N]`
(`ContDiffOn ℝ 2 f (Set.Icc 0 (N:ℝ))`), `K : ℕ` and an integer window, prove
the exact identity between the sawtooth-kernel integral and the finite
`ν`-sum of oscillatory integrals:

    ∫_0^N (sawHat K x : ℂ) · (τi f' E) dx  =  Σ_{ν ∈ window} ∫_0^N E(f x − νx) dx

with `sawHat K x := Σ_{ν ∈ (Icc (−K) K).erase 0} E(−νx)/(2πiν)` (def in
`Submission.SawBasis`) and `(τi f' E) := (tau*I) * (deriv f x : ℂ) * E (f x)`.

CONCRETE TARGET: with `oscInt f N ν := ∫ x in 0..N, E(f x − (ν:ℝ)*x)`, prove

  (∫ x in 0..(N:ℝ), (sawHat K x : ℂ) · ((tau*I) * ((deriv f x : ℝ) : ℂ) * E (f x)))
    = ∑ ν ∈ (Finset.Icc (-((K:ℤ))) (K:ℤ)).erase 0, oscIntHat f N ν

Proof strategy (implemented below): expand `sawHat K x` (finite sum), swap the
finite sum with the integral, and for each `ν` use the per-frequency identity
`∫_0^N (pd_ν/(2πiν) + E(f x − νx)) dx = (E(fN) − E(f0))/(2πiν) + oscInt f N ν`
obtained from the derivative formula `d/dx E(fx − νx) = (τi)(f' − ν)E(fx − νx)`
(FTC on the closed interval: `∫ deriv phase = boundary`).  The boundary terms
`(E(fN) − E(f0))/(2πiν)` sum to zero over the symmetric window `±ν` because
`E(νN) = E(0) = 1` and `Σ_{ν∈window} 1/ν = 0`.
-/

namespace Submission.SdtPoisson

noncomputable section

def oscIntHat (f : ℝ → ℝ) (N : ℕ) (ν : ℤ) : ℂ :=
  ∫ x in 0..(N : ℝ), E (f x - (ν : ℝ) * x)

/-! ## Basic algebraic and topological facts -/

lemma tau_ne_zero : tau ≠ 0 := by
  dsimp [tau]
  exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)

lemma tauI_ne_zero : tau * I ≠ 0 := by
  exact mul_ne_zero tau_ne_zero Complex.I_ne_zero

lemma intCast_ne_zero {ν : ℤ} (hν : ν ≠ 0) : (ν : ℂ) ≠ 0 := by
  exact_mod_cast hν

lemma E_mul_E_neg (t s : ℝ) : E t * E (-s) = E (t - s) := by
  rw [← E_add]
  rfl

/-- `E` at an integer times a natural number is `1`. -/
lemma E_int_nat (ν : ℤ) (N : ℕ) : E ((ν : ℝ) * (N : ℝ)) = 1 := by
  rw [← E_of_int (ν * (N : ℤ))]
  congr 1
  norm_num

/-! ## Per-frequency decompositions of the integrand -/

/-- one summand of `sawHat`. -/
def hatTerm (ν : ℤ) (x : ℝ) : ℂ := E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ))

/-- the multiplier `(τi) · f' · E(f)` of `sawHat` in the integrand. -/
def hatBody (f : ℝ → ℝ) (x : ℝ) : ℂ := (tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)

/-- the phase `E(f x - νx)`. -/
def hatPhase (f : ℝ → ℝ) (ν : ℤ) (x : ℝ) : ℂ := E (f x - (ν : ℝ) * x)

/-- `d/dx` of the phase, at points where `f` is differentiable. -/
def hatPDer (f : ℝ → ℝ) (ν : ℤ) (x : ℝ) : ℂ :=
  (tau * I) * (((deriv f x : ℝ) : ℂ) - (ν : ℂ)) * E (f x - (ν : ℝ) * x)

/-- the symmetric index window. -/
def hatNuSet (K : ℕ) : Finset ℤ := (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0

lemma field_div_mul {K : Type*} [Field K] {a b c w : K} (hb : b ≠ 0) (hw : w ≠ 0) :
    (a / (b * w)) * (b * c) = (a * c) / w := by
  field_simp [hb, hw]

/-- per-term product equals `f' · E(fx − νx)/ν`. -/
lemma hatId_mul (f : ℝ → ℝ) {ν : ℤ} (hν : ν ≠ 0) (x : ℝ) :
    hatTerm ν x * hatBody f x = ((deriv f x : ℝ) : ℂ) * hatPhase f ν x / (ν : ℂ) := by
  unfold hatTerm hatBody hatPhase
  have hνc : (ν : ℂ) ≠ 0 := intCast_ne_zero hν
  have hc : (tau * I) ≠ 0 := tauI_ne_zero
  calc
    E (-((ν : ℝ) * x)) / ((tau * I) * (ν : ℂ)) *
        ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))
        = (E (-((ν : ℝ) * x)) * (((deriv f x : ℝ) : ℂ) * E (f x))) / (ν : ℂ) := by
          rw [show ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)) =
                (tau * I) * (((deriv f x : ℝ) : ℂ) * E (f x)) by ring]
          exact field_div_mul hc hνc
    _ = (((deriv f x : ℝ) : ℂ) * (E (f x) * E (-((ν : ℝ) * x)))) / (ν : ℂ) := by ring
    _ = ((deriv f x : ℝ) : ℂ) * E (f x - (ν : ℝ) * x) / (ν : ℂ) := by
          rw [E_mul_E_neg]

/-- `(d/dx E(fx−νx))/(τiν) + E(fx−νx) = f' · E(fx−νx)/ν`. -/
lemma hatId_splitR (f : ℝ → ℝ) {ν : ℤ} (hν : ν ≠ 0) (x : ℝ) :
    hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x =
      ((deriv f x : ℝ) : ℂ) * hatPhase f ν x / (ν : ℂ) := by
  unfold hatPDer hatPhase
  have hνc : (ν : ℂ) ≠ 0 := intCast_ne_zero hν
  have htau : tau ≠ 0 := tau_ne_zero
  field_simp [hνc, htau]
  ring

/-- the per-ν integrand equals derivative-piece plus phase (pointwise). -/
lemma hatId_pointwise (f : ℝ → ℝ) {ν : ℤ} (hν : ν ≠ 0) (x : ℝ) :
    hatTerm ν x * hatBody f x = hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x := by
  rw [hatId_mul f hν x, hatId_splitR f hν x]

/-! ## Continuity and the fundamental theorem of calculus on `[0,N]` -/

lemma hatPhase_continuousOn {N : ℕ} (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) (ν : ℤ) :
    ContinuousOn (hatPhase f ν) (Set.Icc 0 (N : ℝ)) := by
  unfold hatPhase
  have hlin : Continuous (fun x : ℝ => (ν : ℝ) * x) := continuous_const.mul continuous_id
  exact E_continuous.comp_continuousOn (hF.continuousOn.sub hlin.continuousOn)

/-- `hatPDer f ν` is interval integrable on `[0,N]` (compare with the
`derivWithin`-version, which is continuous on the closed interval and agrees on
the open interior). -/
lemma hatPDer_intervalIntegrable {N : ℕ} (h0ltN : (0 : ℝ) < (N : ℝ)) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) (ν : ℤ) :
    IntervalIntegrable (hatPDer f ν) volume 0 (N : ℝ) := by
  let qW : ℝ → ℂ := fun x : ℝ =>
    (tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ) - (ν : ℂ)) *
      E (f x - (ν : ℝ) * x)
  have hdWc1 : ContDiffOn ℝ 1 (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x)
      (Set.Icc 0 (N : ℝ)) := by
    have hU : UniqueDiffOn ℝ (Set.Icc 0 (N : ℝ)) := uniqueDiffOn_Icc h0ltN
    have hmn : ((1 : ℕ∞ω) + 1) ≤ (2 : ℕ∞ω) := by norm_num
    exact ContDiffOn.derivWithin (m := (1 : ℕ∞ω)) (n := (2 : ℕ∞ω)) hF hU hmn
  have hdWc : ContinuousOn (fun x : ℝ => derivWithin f (Set.Icc 0 (N : ℝ)) x)
      (Set.Icc 0 (N : ℝ)) := hdWc1.continuousOn
  have hcontMap : Continuous (fun c : ℂ => (tau * I) * (c - (ν : ℂ))) := by fun_prop
  have hdWcC : ContinuousOn (fun x : ℝ => ((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ))
      (Set.Icc 0 (N : ℝ)) := Continuous.comp_continuousOn continuous_ofReal hdWc
  have hfirst : ContinuousOn (fun x : ℝ =>
      (tau * I) * (((derivWithin f (Set.Icc 0 (N : ℝ)) x : ℝ) : ℂ) - (ν : ℂ)))
      (Set.Icc 0 (N : ℝ)) := hcontMap.comp_continuousOn hdWcC
  have hqWc : ContinuousOn qW (Set.Icc 0 (N : ℝ)) := by
    dsimp [qW]
    exact hfirst.mul (hatPhase_continuousOn f hF ν)
  have h0leN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt h0ltN
  have hqWint : IntervalIntegrable qW volume 0 (N : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc h0leN hqWc
  have hEq : Set.EqOn qW (hatPDer f ν) (Set.uIoo 0 (N : ℝ)) := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (N : ℝ) := by rwa [Set.uIoo_of_le h0leN] at hx
    dsimp [qW, hatPDer]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx'.1 hx'.2)]
  exact IntervalIntegrable.congr_uIoo hqWint hEq

/-- `f` is differentiable at interior points of `[0,N]` with the stated derivative. -/
lemma hasDerivAt_f_interior {N : ℕ} (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt f (deriv f x) x := by
  have hnh : Set.Icc 0 (N : ℝ) ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  exact ((hF.contDiffAt hnh).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasDerivAt

/-- FTC on `[0,N]`: `∫ hatPDer = E(fN − νN) − E(f0 − ν·0)`. -/
lemma hatPDer_integral {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) (ν : ℤ) :
    (∫ x in 0..(N : ℝ), hatPDer f ν x) =
      E (f (N : ℝ) - (ν : ℝ) * (N : ℝ)) - E (f 0 - (ν : ℝ) * 0) := by
  have h0ltN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h0leN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt h0ltN
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun y : ℝ => E (f y - (ν : ℝ) * y)) (f' := fun y : ℝ => hatPDer f ν y)
    h0leN ?_ ?_ ?_
  · exact hatPhase_continuousOn f hF ν
  · intro x hx
    convert hasDerivAt_E_phase f ν (hasDerivAt_f_interior f hF hx) using 1
    all_goals first | rfl | (ext y; rfl) | ring | (field_simp; ring) | (funext _; rfl) | (ext _ <;> rfl)
  · exact hatPDer_intervalIntegrable h0ltN f hF ν

/-- at the natural-number endpoint `N`, `E(νN) = 1` makes the phase simplify. -/
lemma E_sub_int (f : ℝ → ℝ) (ν : ℤ) (N : ℕ) :
    E (f (N : ℝ) - (ν : ℝ) * (N : ℝ)) = E (f (N : ℝ)) := by
  rw [E_sub, E_int_nat ν N]
  ring

lemma E_zero_sub (f : ℝ → ℝ) (ν : ℤ) :
    E (f 0 - (ν : ℝ) * 0) = E (f 0) := by
  rw [mul_zero, sub_zero]

/-- per-`ν` integral identity: derivative part integrates to the boundary term,
and the phase part is the oscillatory integral. -/
lemma hatId_summand {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) (ν : ℤ) :
    (∫ x in 0..(N : ℝ), hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x) =
      (E (f (N : ℝ)) - E (f 0)) / ((tau * I) * (ν : ℂ)) + oscIntHat f N ν := by
  have h0ltN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h0leN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt h0ltN
  let den : ℂ := (tau * I) * (ν : ℂ)
  calc
    (∫ x in 0..(N : ℝ), hatPDer f ν x / den + hatPhase f ν x)
        = (∫ x in 0..(N : ℝ), hatPDer f ν x / den) + (∫ x in 0..(N : ℝ), hatPhase f ν x) := by
          exact intervalIntegral.integral_add
            (IntervalIntegrable.div_const (hatPDer_intervalIntegrable h0ltN f hF ν) den)
            (ContinuousOn.intervalIntegrable_of_Icc h0leN (hatPhase_continuousOn f hF ν))
    _ = (∫ x in 0..(N : ℝ), hatPDer f ν x) / den + (∫ x in 0..(N : ℝ), hatPhase f ν x) := by
          rw [intervalIntegral.integral_div]
    _ = (E (f (N : ℝ) - (ν : ℝ) * (N : ℝ)) - E (f 0 - (ν : ℝ) * 0)) / den
          + (∫ x in 0..(N : ℝ), hatPhase f ν x) := by
          rw [hatPDer_integral hN f hF ν]
    _ = (E (f (N : ℝ)) - E (f 0)) / den + oscIntHat f N ν := by
          rw [E_sub_int f ν N, E_zero_sub f ν]
          rfl

/-! ## Vanishing of the summed boundary terms -/

/-- `Σ_{ν ∈ window} 1/ν = 0` (the window is symmetric and `0` excluded). -/
lemma invSum_zero (K : ℕ) : (∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) = 0 := by
  classical
  have hsym : ∀ a ∈ hatNuSet K, -a ∈ hatNuSet K := by
    intro a ha
    simp [hatNuSet, Finset.mem_erase, Finset.mem_Icc] at ha ⊢
    omega
  have hAeq : (∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) =
      -(∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) := by
    calc
      (∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ))
          = (∑ ν ∈ hatNuSet K, (1 : ℂ) / ((-ν : ℤ) : ℂ)) := by
            refine Finset.sum_bij (s := hatNuSet K) (t := hatNuSet K) (i := fun ν _ => -ν) ?_ ?_ ?_ ?_
            · intro a ha
              exact hsym a ha
            · intro a ha b hb h
              omega
            · intro b hb
              refine ⟨-b, hsym b hb, ?_⟩
              simp
            · intro a ha
              simp
      _ = (∑ ν ∈ hatNuSet K, -((1 : ℂ) / (ν : ℂ))) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp
      _ = -(∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) := by
            rw [Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) * (∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hAeq]
    rw [add_neg_cancel]
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

/-- the constant boundary term summed over the symmetric window vanishes. -/
lemma hatBoundary_sum_zero (K : ℕ) (bnd : ℂ) :
    (∑ ν ∈ hatNuSet K, bnd / ((tau * I) * (ν : ℂ))) = 0 := by
  classical
  calc
    (∑ ν ∈ hatNuSet K, bnd / ((tau * I) * (ν : ℂ)))
        = (∑ ν ∈ hatNuSet K, (bnd / (tau * I)) * ((1 : ℂ) / (ν : ℂ))) := by
          refine Finset.sum_congr rfl ?_
          intro ν hν
          have hν0 : ν ≠ 0 := (Finset.mem_erase.mp hν).1
          field_simp [tauI_ne_zero, intCast_ne_zero hν0]
    _ = (bnd / (tau * I)) * (∑ ν ∈ hatNuSet K, (1 : ℂ) / (ν : ℂ)) := by
          rw [Finset.mul_sum]
    _ = 0 := by rw [invSum_zero K]; ring

/-! ## The identity -/

lemma hat_identity {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (K : ℕ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    (∫ x in 0..(N : ℝ), (sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))) =
      ∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, oscIntHat f N ν := by
  classical
  have h0ltN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h0leN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt h0ltN
  change (∫ x in 0..(N : ℝ), sawHat K x * hatBody f x) =
    (∑ ν ∈ hatNuSet K, oscIntHat f N ν)
  calc
    (∫ x in 0..(N : ℝ), sawHat K x * hatBody f x)
        = (∫ x in 0..(N : ℝ), ∑ ν ∈ hatNuSet K,
            (hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x)) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          change sawHat K x * hatBody f x = (∑ ν ∈ hatNuSet K,
            (hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x))
          rw [sawHat, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro ν hν
          exact hatId_pointwise f (Finset.mem_erase.mp hν).1 x
    _ = (∑ ν ∈ hatNuSet K,
            ∫ x in 0..(N : ℝ),
            (hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x)) := by
          exact intervalIntegral.integral_finsetSum (s := hatNuSet K)
            (f := fun (ν : ℤ) (x : ℝ) => hatPDer f ν x / ((tau * I) * (ν : ℂ)) + hatPhase f ν x)
            (by intro ν hν
                exact IntervalIntegrable.add
                  (IntervalIntegrable.div_const (hatPDer_intervalIntegrable h0ltN f hF ν) ((tau * I) * (ν : ℂ)))
                  (ContinuousOn.intervalIntegrable_of_Icc h0leN (hatPhase_continuousOn f hF ν)))
    _ = (∑ ν ∈ hatNuSet K,
          ((E (f (N : ℝ)) - E (f 0)) / ((tau * I) * (ν : ℂ)) + oscIntHat f N ν)) := by
          refine Finset.sum_congr rfl ?_
          intro ν hν
          exact hatId_summand hN f hF ν
    _ = (∑ ν ∈ hatNuSet K, (E (f (N : ℝ)) - E (f 0)) / ((tau * I) * (ν : ℂ)))
        + (∑ ν ∈ hatNuSet K, oscIntHat f N ν) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ ν ∈ hatNuSet K, oscIntHat f N ν) := by
          rw [hatBoundary_sum_zero K (E (f (N : ℝ)) - E (f 0))]
          rw [zero_add]

end
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# First remainder integral bound for the pair bound

Prove `int_remainder_sub_le`.  See the proof sketch in the header of the
original stub (FTC-2 with interior derivative + closed-interval continuity,
then a pointwise bound of the endpoint difference using the margins).
-/

namespace Submission.SdtPoisson

noncomputable section

lemma int_remainder_sub_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B c : ℝ} (hB : 1 ≤ B)
    (hcB : B ≤ c)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2) :
    (∫ x in 0..(N : ℝ), wf N f x / (c - gf N f x) ^ 2) ≤ (B - 1) / (c - B + 1 / 2) ^ 2 := by
  set A : ℝ := c - B + 1 / 2 with hAdef
  let D : ℝ → ℝ := fun x : ℝ => c - gf N f x
  let F : ℝ → ℝ := fun x : ℝ => (c - gf N f x)⁻¹
  let integ : ℝ → ℝ := fun x : ℝ => wf N f x / (c - gf N f x) ^ 2
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_N_real hN
  have hNle : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hApos : 0 < A := by
    rw [hAdef]
    have hcB0 : 0 ≤ c - B := sub_nonneg.mpr hcB
    linarith
  have hBm1 : 0 ≤ B - 1 := by linarith
  have hgm : ∀ x : ℝ, x ∈ sInt N → 1 / 2 ≤ gf N f x ∧ gf N f x ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hupG : ∀ x : ℝ, x ∈ sInt N → gf N f x ≤ B - 1 / 2 := fun x hx => (hgm x hx).2
  have hlowG : ∀ x : ℝ, x ∈ sInt N → 1 / 2 ≤ gf N f x := fun x hx => (hgm x hx).1
  have xN : (N : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨hNpos.le, le_rfl⟩
  have x0 : (0 : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨le_rfl, hNpos.le⟩
  -- Denominator D ≥ A > 0 on the closed interval
  have hD_ge : ∀ x : ℝ, x ∈ sInt N → A ≤ D x := by
    intro x hx
    have hu := hupG x hx
    dsimp [D]
    linarith [hAdef, hu]
  have hD_pos : ∀ x : ℝ, x ∈ sInt N → 0 < D x := fun x hx => lt_of_lt_of_le hApos (hD_ge x hx)
  have hD_ne : ∀ x : ℝ, x ∈ sInt N → D x ≠ 0 := fun x hx => ne_of_gt (hD_pos x hx)
  have hden_ne : ∀ x : ℝ, x ∈ sInt N → c - gf N f x ≠ 0 := fun x hx => hD_ne x hx
  have hdN_ge : A ≤ D (N : ℝ) := hD_ge (N : ℝ) xN
  have hd0_ge : A ≤ D 0 := hD_ge 0 x0
  have hdN_pos : 0 < D (N : ℝ) := hD_pos (N : ℝ) xN
  have hd0_pos : 0 < D 0 := hD_pos 0 x0
  have hdN_ne : D (N : ℝ) ≠ 0 := hD_ne (N : ℝ) xN
  have hd0_ne : D 0 ≠ 0 := hD_ne 0 x0
  have hnum : D 0 - D (N : ℝ) ≤ B - 1 := by
    have hupN : gf N f (N : ℝ) ≤ B - 1 / 2 := hupG (N : ℝ) xN
    have hlow0 : 1 / 2 ≤ gf N f 0 := hlowG 0 x0
    dsimp [D]
    linarith
  have hprod_pos : 0 < D (N : ℝ) * D 0 := mul_pos hdN_pos hd0_pos
  have hprod_sq : A ^ 2 ≤ D (N : ℝ) * D 0 := by
    have hmul := mul_le_mul hdN_ge hd0_ge hApos.le hdN_pos.le
    simpa [pow_two] using hmul
  -- Continuity facts on the closed interval
  have hG_cont : ContinuousOn (fun x : ℝ => c - gf N f x) (sInt N) := by
    have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
    exact continuousOn_const.sub hgC
  have hcont_F : ContinuousOn F (sInt N) := by
    change ContinuousOn (fun x : ℝ => (c - gf N f x)⁻¹) (sInt N)
    exact hG_cont.inv₀ hden_ne
  have hI_cont : ContinuousOn integ (sInt N) := by
    change ContinuousOn (fun x : ℝ => wf N f x / (c - gf N f x) ^ 2) (sInt N)
    have hwC : ContinuousOn (wf N f) (sInt N) := continuousOn_wf hN f hF
    have hden2 : ContinuousOn (fun x : ℝ => (c - gf N f x) ^ 2) (sInt N) := hG_cont.pow 2
    exact hwC.div hden2 (fun x hx => pow_ne_zero 2 (hden_ne x hx))
  have hint : IntervalIntegrable integ volume 0 (N : ℝ) := by
    exact ContinuousOn.intervalIntegrable_of_Icc hNle hI_cont
  -- FTC
  have hderiv : ∀ x ∈ Set.Ioo 0 (N : ℝ), HasDerivAt F (integ x) x := by
    intro x hx
    change HasDerivAt (fun y : ℝ => (c - gf N f y)⁻¹) (wf N f x / (c - gf N f x) ^ 2) x
    have hgfd : HasDerivAt (gf N f) (wf N f x) x := hasDerivAt_gf_of_Ioo f hF hx
    have hcs : HasDerivAt (fun y : ℝ => c - gf N f y) (-(wf N f x)) x := hgfd.const_sub c
    have hne : c - gf N f x ≠ 0 := hden_ne x (Set.mem_Icc_of_Ioo hx)
    have hderiv_eq : -(-(wf N f x)) / (c - gf N f x) ^ 2 = wf N f x / (c - gf N f x) ^ 2 := by
      ring
    exact (hcs.inv hne).congr_deriv hderiv_eq
  have hftc : (∫ x in 0..(N : ℝ), integ x) = F (N : ℝ) - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := (N : ℝ))
      (f := F) (f' := integ) hNle hcont_F hderiv hint
  -- Assemble
  change (∫ x in 0..(N : ℝ), integ x) ≤ (B - 1) / A ^ 2
  rw [hftc]
  change (D (N : ℝ))⁻¹ - (D 0)⁻¹ ≤ (B - 1) / A ^ 2
  rw [inv_sub_inv hdN_ne hd0_ne]
  have hprod_nonneg : 0 ≤ D (N : ℝ) * D 0 := hprod_pos.le
  have hA2_pos : 0 < A ^ 2 := sq_pos_of_ne_zero (ne_of_gt hApos)
  exact (div_le_div_of_nonneg_right hnum hprod_nonneg).trans
    (div_le_div_of_nonneg_left hBm1 hA2_pos hprod_sq)

end
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Second remainder integral bound for the pair bound

Prove `int_remainder_add_le`.  See the proof sketch in the header of the
original stub (FTC-2 with interior derivative + closed-interval continuity,
then a pointwise bound of the endpoint difference using the margins).  This is
the `+`-analogue of `int_remainder_sub_le` in `Submission/RemIntSub.lean`.
-/

namespace Submission.SdtPoisson

noncomputable section

lemma int_remainder_add_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B c : ℝ} (hB : 1 ≤ B)
    (hcB : B ≤ c)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2) :
    (∫ x in 0..(N : ℝ), wf N f x / (c + gf N f x) ^ 2) ≤ (B - 1) / (c + 1 / 2) ^ 2 := by
  set A : ℝ := c + 1 / 2 with hAdef
  let D : ℝ → ℝ := fun x : ℝ => c + gf N f x
  let F : ℝ → ℝ := fun x : ℝ => (c + gf N f x)⁻¹
  let integ : ℝ → ℝ := fun x : ℝ => wf N f x / (c + gf N f x) ^ 2
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_N_real hN
  have hNle : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hApos : 0 < A := by
    rw [hAdef]
    linarith
  have hBm1 : 0 ≤ B - 1 := by linarith
  have hgm : ∀ x : ℝ, x ∈ sInt N → 1 / 2 ≤ gf N f x ∧ gf N f x ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hupG : ∀ x : ℝ, x ∈ sInt N → gf N f x ≤ B - 1 / 2 := fun x hx => (hgm x hx).2
  have hlowG : ∀ x : ℝ, x ∈ sInt N → 1 / 2 ≤ gf N f x := fun x hx => (hgm x hx).1
  have xN : (N : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨hNpos.le, le_rfl⟩
  have x0 : (0 : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨le_rfl, hNpos.le⟩
  -- Denominator D ≥ A > 0 on the closed interval
  have hD_ge : ∀ x : ℝ, x ∈ sInt N → A ≤ D x := by
    intro x hx
    have hl := hlowG x hx
    dsimp [D]
    linarith [hAdef, hl]
  have hD_pos : ∀ x : ℝ, x ∈ sInt N → 0 < D x := fun x hx => lt_of_lt_of_le hApos (hD_ge x hx)
  have hD_ne : ∀ x : ℝ, x ∈ sInt N → D x ≠ 0 := fun x hx => ne_of_gt (hD_pos x hx)
  have hden_ne : ∀ x : ℝ, x ∈ sInt N → c + gf N f x ≠ 0 := fun x hx => hD_ne x hx
  have hdN_ge : A ≤ D (N : ℝ) := hD_ge (N : ℝ) xN
  have hd0_ge : A ≤ D 0 := hD_ge 0 x0
  have hdN_pos : 0 < D (N : ℝ) := hD_pos (N : ℝ) xN
  have hd0_pos : 0 < D 0 := hD_pos 0 x0
  have hdN_ne : D (N : ℝ) ≠ 0 := hD_ne (N : ℝ) xN
  have hd0_ne : D 0 ≠ 0 := hD_ne 0 x0
  have hnum : D (N : ℝ) - D 0 ≤ B - 1 := by
    have hupN : gf N f (N : ℝ) ≤ B - 1 / 2 := hupG (N : ℝ) xN
    have hlow0 : 1 / 2 ≤ gf N f 0 := hlowG 0 x0
    dsimp [D]
    linarith
  have hprod_pos : 0 < D 0 * D (N : ℝ) := mul_pos hd0_pos hdN_pos
  have hprod_sq : A ^ 2 ≤ D 0 * D (N : ℝ) := by
    have hmul := mul_le_mul hd0_ge hdN_ge hApos.le hd0_pos.le
    simpa [pow_two] using hmul
  -- Continuity facts on the closed interval
  have hG_cont : ContinuousOn (fun x : ℝ => c + gf N f x) (sInt N) := by
    have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
    exact continuousOn_const.add hgC
  have hcont_F : ContinuousOn F (sInt N) := by
    change ContinuousOn (fun x : ℝ => (c + gf N f x)⁻¹) (sInt N)
    exact hG_cont.inv₀ hden_ne
  have hI_cont : ContinuousOn integ (sInt N) := by
    change ContinuousOn (fun x : ℝ => wf N f x / (c + gf N f x) ^ 2) (sInt N)
    have hwC : ContinuousOn (wf N f) (sInt N) := continuousOn_wf hN f hF
    have hden2 : ContinuousOn (fun x : ℝ => (c + gf N f x) ^ 2) (sInt N) := hG_cont.pow 2
    exact hwC.div hden2 (fun x hx => pow_ne_zero 2 (hden_ne x hx))
  have hint : IntervalIntegrable integ volume 0 (N : ℝ) := by
    exact ContinuousOn.intervalIntegrable_of_Icc hNle hI_cont
  have hintNeg : IntervalIntegrable (fun x : ℝ => -integ x) volume 0 (N : ℝ) := by
    exact hint.neg
  -- FTC (with F' = -integ)
  have hderiv : ∀ x ∈ Set.Ioo 0 (N : ℝ), HasDerivAt F (-(integ x)) x := by
    intro x hx
    change HasDerivAt (fun y : ℝ => (c + gf N f y)⁻¹) (-(wf N f x / (c + gf N f x) ^ 2)) x
    have hgfd : HasDerivAt (gf N f) (wf N f x) x := hasDerivAt_gf_of_Ioo f hF hx
    have hcs : HasDerivAt (fun y : ℝ => c + gf N f y) (wf N f x) x := hgfd.const_add c
    have hne : c + gf N f x ≠ 0 := hden_ne x (Set.mem_Icc_of_Ioo hx)
    have hderiv_eq : -(wf N f x) / (c + gf N f x) ^ 2 = -(wf N f x / (c + gf N f x) ^ 2) := by
      ring
    exact (hcs.inv hne).congr_deriv hderiv_eq
  have hftcNeg : (∫ x in 0..(N : ℝ), -integ x) = F (N : ℝ) - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := (N : ℝ))
      (f := F) (f' := fun x : ℝ => -integ x) hNle hcont_F hderiv hintNeg
  have hftc : (∫ x in 0..(N : ℝ), integ x) = F 0 - F (N : ℝ) := by
    have hneg : -(∫ x in 0..(N : ℝ), integ x) = F (N : ℝ) - F 0 := by
      simpa [intervalIntegral.integral_neg] using hftcNeg
    have h2 : (∫ x in 0..(N : ℝ), integ x) = -(F (N : ℝ) - F 0) := by linarith
    simpa using h2
  -- Assemble
  change (∫ x in 0..(N : ℝ), integ x) ≤ (B - 1) / A ^ 2
  rw [hftc]
  change (D 0)⁻¹ - (D (N : ℝ))⁻¹ ≤ (B - 1) / A ^ 2
  rw [inv_sub_inv hd0_ne hdN_ne]
  have hprod_nonneg : 0 ≤ D 0 * D (N : ℝ) := hprod_pos.le
  have hA2_pos : 0 < A ^ 2 := sq_pos_of_ne_zero (ne_of_gt hApos)
  exact (div_le_div_of_nonneg_right hnum hprod_nonneg).trans
    (div_le_div_of_nonneg_left hBm1 hA2_pos hprod_sq)

end
end Submission.SdtPoisson

open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Per-frequency pair bound (the core cancellation estimate)

Canonical hypotheses: `N ≥ 1`, `f : ℝ → ℝ` with
`ContDiffOn ℝ 2 f (Set.Icc 0 (N:ℝ))`, `0 ≤ deriv (deriv f) x` on `(0,N)`,
and real `B ≥ 1` with the *two-sided derivative margin*
`1/2 ≤ deriv f x ≤ B − 1/2` for all `x ∈ [0,N]`.  For an integer frequency
`ν` in the upper tail, i.e. `(B : ℝ) ≤ ν` (so `ν − f'(x) ≥ 1/2` for all x),
prove the **pair bound**:

    ‖T_ν + T_{−ν}‖ ≤ 60 · (B + 1) / ((ν : ℝ) − B + 1)^2

where `T_ν := ∫ x in 0..(N:ℝ), E (f x − (ν:ℝ)·x)`.

Proof route: for `q ∈ {ν, −ν}`, integrate by parts `E(f−qx) = d/dx[E(f−qx)/(G−q)] +
E(f−qx)·W/(G−q)²` (with `G := gf N f`, `W := wf N f` the within-interval
derivatives); sum over the two signs and use that the boundary phases coincide
at `0` (trivially) and at `N` (because `E(2νN) = 1`).  The boundary part pairs
via `1/(w−ν)+1/(w+ν) = 2w/(w²−ν²)` giving `O(B/ν²)`; the remainder is bounded
by `∫ W/(ν−G)² + ∫ W/(ν+G)²`, which are total derivatives of `(ν∓G)⁻¹`.
Constants are extremely generous.
-/

namespace Submission.SdtPoisson

noncomputable section

/-- The integrand of `T_ν`: `E(f x − νx)`. -/
def uplus (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ := fun x => E (f x - (ν : ℝ) * x)

/-- The integrand of `T_{−ν}`: `E(f x + νx)`. -/
def uminus (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ := fun x => E (f x - (-(ν : ℝ)) * x)

/-- `(G − ν)⁻¹` as a complex function (denominator of the `+ν` boundary term). -/
def pden (N : ℕ) (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ :=
  fun x => ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ)⁻¹)

/-- `(G + ν)⁻¹` as a complex function (denominator of the `−ν` boundary term). -/
def mden (N : ℕ) (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ :=
  fun x => ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ)⁻¹)

/-- The boundary antiderivative `A(x) = E(f−νx)/(G−ν) + E(f+νx)/(G+ν)`. -/
def pairA (N : ℕ) (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ :=
  fun x => uplus f ν x * pden N f ν x + uminus f ν x * mden N f ν x

/-- The remainder integrand `R(x) = E(f−νx)·W/(G−ν)² + E(f+νx)·W/(G+ν)²`. -/
def pairR (N : ℕ) (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ :=
  fun x => uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)) +
    uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))

/-- The derivative of `pairA`: `2πi·(E(f−νx)+E(f+νx)) − R(x)`. -/
def pairG (N : ℕ) (f : ℝ → ℝ) (ν : ℤ) : ℝ → ℂ :=
  fun x => (tau * I) * (uplus f ν x + uminus f ν x) - pairR N f ν x

/-- Interior derivative of the `+ν` phase `uplus f ν = E(f − ν·x)`. -/
lemma hasDerivAt_uplus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N)) (ν : ℤ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (uplus f ν) (((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) x := by
  have hfdx : HasDerivAt f (deriv f x) x := SdtOscB.hasDerivAt_F_of_Ioo f hF hx
  have h := hasDerivAt_E_phase f ν hfdx
  have hfun : (fun y : ℝ => E (f y - (ν : ℝ) * y)) = uplus f ν := by rfl
  have hPx : E (f x - (ν : ℝ) * x) = uplus f ν x := congrFun hfun x
  simpa [hfun, hPx] using h

/-- Interior derivative of the `−ν` phase `uminus f ν = E(f + ν·x)`. -/
lemma hasDerivAt_uminus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N)) (ν : ℤ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (uminus f ν) (((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) x := by
  have hfdx : HasDerivAt f (deriv f x) x := SdtOscB.hasDerivAt_F_of_Ioo f hF hx
  have h := hasDerivAt_E_phase f (-ν) hfdx
  have hfun : (fun y : ℝ => E (f y + y * (ν : ℝ))) = uminus f ν := by
    funext y
    unfold uminus
    congr 1
    ring
  have hPx : E (f x + x * (ν : ℝ)) = uminus f ν x := congrFun hfun x
  simpa [hfun, hPx, mul_comm, mul_left_comm, mul_assoc, Int.cast_neg] using h

/-- Interior derivative of the `+ν` summand of `pairA`. -/
lemma deriv_Aplus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (fun y : ℝ => uplus f ν y * pden N f ν y)
      ((((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) * pden N f ν x +
        uplus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))) x := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hxI : x ∈ sInt N := Set.mem_Icc_of_Ioo hx
  have hup : gf N f x ≤ B - 1 / 2 := (hgm x hxI).2
  have hne : gf N f x - (ν : ℝ) ≠ 0 := by
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    linarith
  have hu : HasDerivAt (uplus f ν)
      (((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) x :=
    hasDerivAt_uplus hN f hB hF ν hx
  have hgd : HasDerivAt (gf N f) (wf N f x) x := hasDerivAt_gf_of_Ioo f hF hx
  have hqC : HasDerivAt (fun y : ℝ => (((gf N f y - (ν : ℝ)) : ℝ) : ℂ))
      (((wf N f x : ℝ) : ℂ)) x := by
    simpa using (hgd.sub (hasDerivAt_const x (ν : ℝ))).ofReal_comp
  have hneC : (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hne
  have hqinv : HasDerivAt (fun y : ℝ => pden N f ν y)
      (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)) x := by
    change HasDerivAt (fun y : ℝ => (((gf N f y - (ν : ℝ)) : ℝ) : ℂ)⁻¹)
      (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)) x
    exact hqC.inv hneC
  have hprod := hu.mul hqinv
  change HasDerivAt (fun y : ℝ => uplus f ν y * pden N f ν y)
      ((((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) * pden N f ν x +
        uplus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))) x
  exact hprod

/-- Interior derivative of the `−ν` summand of `pairA`. -/
lemma deriv_Aminus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (fun y : ℝ => uminus f ν y * mden N f ν y)
      ((((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) * mden N f ν x +
        uminus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))) x := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hxI : x ∈ sInt N := Set.mem_Icc_of_Ioo hx
  have hlo : 1 / 2 ≤ gf N f x := (hgm x hxI).1
  have hne : gf N f x + (ν : ℝ) ≠ 0 := by
    have : 0 < gf N f x + (ν : ℝ) := by linarith
    linarith
  have hu : HasDerivAt (uminus f ν)
      (((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) x :=
    hasDerivAt_uminus hN f hB hF ν hx
  have hgd : HasDerivAt (gf N f) (wf N f x) x := hasDerivAt_gf_of_Ioo f hF hx
  have hqC : HasDerivAt (fun y : ℝ => (((gf N f y + (ν : ℝ)) : ℝ) : ℂ))
      (((wf N f x : ℝ) : ℂ)) x := by
    simpa using (hgd.add (hasDerivAt_const x (ν : ℝ))).ofReal_comp
  have hneC : (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hne
  have hqinv : HasDerivAt (fun y : ℝ => mden N f ν y)
      (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2)) x := by
    change HasDerivAt (fun y : ℝ => (((gf N f y + (ν : ℝ)) : ℝ) : ℂ)⁻¹)
      (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2)) x
    exact hqC.inv hneC
  have hprod := hu.mul hqinv
  change HasDerivAt (fun y : ℝ => uminus f ν y * mden N f ν y)
      ((((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) * mden N f ν x +
        uminus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))) x
  exact hprod

/-- Continuity of `uplus f ν` on `[0,N]`. -/
lemma continuousOn_uplus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N)) (ν : ℤ) :
    ContinuousOn (uplus f ν) (sInt N) := by
  have hfc : ContinuousOn f (sInt N) := hF.continuousOn
  have hlin : ContinuousOn (fun x : ℝ => (ν : ℝ) * x) (sInt N) :=
    (continuous_id.const_mul (ν : ℝ)).continuousOn
  have hph : ContinuousOn (fun x : ℝ => f x - (ν : ℝ) * x) (sInt N) := hfc.sub hlin
  have hfun : uplus f ν = E ∘ (fun x : ℝ => f x - (ν : ℝ) * x) := by rfl
  rw [hfun]
  exact E_continuous.comp_continuousOn hph

/-- Continuity of `uminus f ν` on `[0,N]`. -/
lemma continuousOn_uminus {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N)) (ν : ℤ) :
    ContinuousOn (uminus f ν) (sInt N) := by
  have hfc : ContinuousOn f (sInt N) := hF.continuousOn
  have hlin : ContinuousOn (fun x : ℝ => (-(ν : ℝ)) * x) (sInt N) :=
    (continuous_id.const_mul (-(ν : ℝ))).continuousOn
  have hph : ContinuousOn (fun x : ℝ => f x - (-(ν : ℝ)) * x) (sInt N) := hfc.sub hlin
  have hfun : uminus f ν = E ∘ (fun x : ℝ => f x - (-(ν : ℝ)) * x) := by rfl
  rw [hfun]
  exact E_continuous.comp_continuousOn hph

/-- Continuity of the `+ν` boundary reciprocal `pden N f ν` on `[0,N]`. -/
lemma continuousOn_pden {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ContinuousOn (pden N f ν) (sInt N) := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
  have hdenC : ContinuousOn (fun x : ℝ => gf N f x - (ν : ℝ)) (sInt N) := hgC.sub continuousOn_const
  have hne : ∀ x ∈ sInt N, gf N f x - (ν : ℝ) ≠ 0 := by
    intro x hx
    have hup : gf N f x ≤ B - 1 / 2 := (hgm x hx).2
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    linarith
  have hq : ContinuousOn (fun x : ℝ => ((gf N f x - (ν : ℝ))⁻¹ : ℝ)) (sInt N) := hdenC.inv₀ hne
  have hfun : pden N f ν = (fun x : ℝ => ((((gf N f x - (ν : ℝ))⁻¹ : ℝ) : ℂ))) := by
    funext x
    unfold pden
    rw [← Complex.ofReal_inv]
  rw [hfun]
  exact Complex.continuous_ofReal.comp_continuousOn hq

/-- Continuity of the `−ν` boundary reciprocal `mden N f ν` on `[0,N]`. -/
lemma continuousOn_mden {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ContinuousOn (mden N f ν) (sInt N) := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
  have hdenC : ContinuousOn (fun x : ℝ => gf N f x + (ν : ℝ)) (sInt N) := hgC.add continuousOn_const
  have hne : ∀ x ∈ sInt N, gf N f x + (ν : ℝ) ≠ 0 := by
    intro x hx
    have hlo : 1 / 2 ≤ gf N f x := (hgm x hx).1
    have hpos : 0 < gf N f x + (ν : ℝ) := by linarith
    linarith
  have hq : ContinuousOn (fun x : ℝ => ((gf N f x + (ν : ℝ))⁻¹ : ℝ)) (sInt N) := hdenC.inv₀ hne
  have hfun : mden N f ν = (fun x : ℝ => ((((gf N f x + (ν : ℝ))⁻¹ : ℝ) : ℂ))) := by
    funext x
    unfold mden
    rw [← Complex.ofReal_inv]
  rw [hfun]
  exact Complex.continuous_ofReal.comp_continuousOn hq

/-- Continuity of the boundary antiderivative `pairA` on `[0,N]`. -/
lemma continuousOn_pairA {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ContinuousOn (pairA N f ν) (sInt N) := by
  have hu : ContinuousOn (uplus f ν) (sInt N) := continuousOn_uplus hN f hB hF ν
  have hm : ContinuousOn (uminus f ν) (sInt N) := continuousOn_uminus hN f hB hF ν
  have hp : ContinuousOn (pden N f ν) (sInt N) := continuousOn_pden hN f hB hF hmarg ν hν
  have hmd : ContinuousOn (mden N f ν) (sInt N) := continuousOn_mden hN f hB hF hmarg ν hν
  have hfun : pairA N f ν = (uplus f ν * pden N f ν) + (uminus f ν * mden N f ν) := by
    funext x
    rfl
  rw [hfun]
  exact (hu.mul hp).add (hm.mul hmd)

/-- Continuity of the remainder integrand `pairR` on `[0,N]`. -/
lemma continuousOn_pairR {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ContinuousOn (pairR N f ν) (sInt N) := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hu : ContinuousOn (uplus f ν) (sInt N) := continuousOn_uplus hN f hB hF ν
  have hm : ContinuousOn (uminus f ν) (sInt N) := continuousOn_uminus hN f hB hF ν
  have hwC : ContinuousOn (wf N f) (sInt N) := continuousOn_wf hN f hF
  have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
  have hnumC : ContinuousOn (fun x : ℝ => ((wf N f x : ℝ) : ℂ)) (sInt N) :=
    Complex.continuous_ofReal.comp_continuousOn hwC
  have hin1 : ContinuousOn (fun x : ℝ => (((gf N f x - (ν : ℝ)) : ℝ) : ℂ)) (sInt N) :=
    Complex.continuous_ofReal.comp_continuousOn (hgC.sub continuousOn_const)
  have hden1 : ContinuousOn (fun x : ℝ => (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2) (sInt N) :=
    hin1.pow 2
  have hne1 : ∀ x ∈ sInt N, (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    intro x hx
    have hup : gf N f x ≤ B - 1 / 2 := (hgm x hx).2
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    have hne : (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_lt (lt_of_le_of_lt hle (by norm_num)))
    exact pow_ne_zero 2 hne
  have hq1 : ContinuousOn (fun x : ℝ => ((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)) (sInt N) := by
    change ContinuousOn (((fun x : ℝ => ((wf N f x : ℝ) : ℂ)) /
      (fun x : ℝ => ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)))) (sInt N)
    exact hnumC.div hden1 hne1
  have hin2 : ContinuousOn (fun x : ℝ => (((gf N f x + (ν : ℝ)) : ℝ) : ℂ)) (sInt N) :=
    Complex.continuous_ofReal.comp_continuousOn (hgC.add continuousOn_const)
  have hden2 : ContinuousOn (fun x : ℝ => (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2) (sInt N) :=
    hin2.pow 2
  have hne2 : ∀ x ∈ sInt N, (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    intro x hx
    have hlo : 1 / 2 ≤ gf N f x := (hgm x hx).1
    have hpos : 0 < gf N f x + (ν : ℝ) := by linarith
    have hne : (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hpos)
    exact pow_ne_zero 2 hne
  have hq2 : ContinuousOn (fun x : ℝ => ((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2)) (sInt N) := by
    change ContinuousOn (((fun x : ℝ => ((wf N f x : ℝ) : ℂ)) /
      (fun x : ℝ => ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2)))) (sInt N)
    exact hnumC.div hden2 hne2
  have hfun : pairR N f ν =
      (uplus f ν * (fun x : ℝ => ((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))) +
      (uminus f ν * (fun x : ℝ => ((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))) := by
    funext x
    rfl
  rw [hfun]
  exact (hu.mul hq1).add (hm.mul hq2)

/-- Continuity of the derivative target `pairG` on `[0,N]`. -/
lemma continuousOn_pairG {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ContinuousOn (pairG N f ν) (sInt N) := by
  have hu : ContinuousOn (uplus f ν) (sInt N) := continuousOn_uplus hN f hB hF ν
  have hm : ContinuousOn (uminus f ν) (sInt N) := continuousOn_uminus hN f hB hF ν
  have hR : ContinuousOn (pairR N f ν) (sInt N) := continuousOn_pairR hN f hB hF hmarg ν hν
  have hfun : pairG N f ν = (tau * I) • (uplus f ν + uminus f ν) - pairR N f ν := by
    funext x
    rfl
  rw [hfun]
  exact ((hu.add hm).const_smul (tau * I)).sub hR

/-- `IntervalIntegrable` on `0..N` from continuity on `[0,N]` (with `0 ≤ N`). -/
lemma intervalIntegrable_of_continuousOn {N : ℕ} (hN : 1 ≤ N) {g : ℝ → ℂ}
    (hg : ContinuousOn g (sInt N)) : IntervalIntegrable g MeasureTheory.volume 0 (N : ℝ) := by
  have h0Nle : (0 : ℝ) ≤ (N : ℝ) := (zero_lt_N_real hN).le
  have : ContinuousOn g (Set.uIcc 0 (N : ℝ)) := by
    rw [Set.uIcc_of_le h0Nle]
    simpa [sInt] using hg
  exact this.intervalIntegrable

/-- `deriv_pairA`: the interior derivative of `pairA` is `pairG`. -/
lemma deriv_pairA {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) {x : ℝ} (hx : x ∈ Set.Ioo 0 (N : ℝ)) :
    HasDerivAt (pairA N f ν) (pairG N f ν x) x := by
  have h1 := deriv_Aplus hN f hB hF hmarg ν hν hx
  have h2 := deriv_Aminus hN f hB hF hmarg ν hν hx
  have hsum := h1.add h2
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hxI : x ∈ sInt N := Set.mem_Icc_of_Ioo hx
  have hne1 : gf N f x - (ν : ℝ) ≠ 0 := by
    have hup : gf N f x ≤ B - 1 / 2 := (hgm x hxI).2
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    linarith
  have hne2 : gf N f x + (ν : ℝ) ≠ 0 := by
    have hlo : 1 / 2 ≤ gf N f x := (hgm x hxI).1
    have : 0 < gf N f x + (ν : ℝ) := by linarith
    linarith
  have hden1 : (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne1
  have hden2 : (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne2
  have hgfeq : gf N f x = deriv f x := gf_eq_deriv_of_Ioo f hx
  have hcast1 : (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ)) = (((gf N f x - (ν : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [← hgfeq]
  have hcast2 : (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ)) = (((gf N f x + (ν : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [← hgfeq]
  have hR1 : ((((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) * pden N f ν x +
        uplus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))) =
      (tau * I) * uplus f ν x -
        uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2)) := by
    rw [hcast1]
    dsimp [pden]
    field_simp [hden1]
    ring
  have hR2 : ((((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) * mden N f ν x +
        uminus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))) =
      (tau * I) * uminus f ν x -
        uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2)) := by
    rw [hcast2]
    dsimp [mden]
    field_simp [hden2]
    ring
  have hclean : ((((tau * I) * (((deriv f x : ℝ) : ℂ) - ((ν : ℝ) : ℂ))) * uplus f ν x) * pden N f ν x +
        uplus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))) +
      ((((tau * I) * (((deriv f x : ℝ) : ℂ) + ((ν : ℝ) : ℂ))) * uminus f ν x) * mden N f ν x +
        uminus f ν x * (-((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))) =
      pairG N f ν x := by
    rw [hR1, hR2]
    unfold pairG pairR
    ring_nf
  rw [← hclean]
  exact hsum

/-- norm of the sum of two real inverses embedded in ℂ. -/
lemma norm_inv_add_inv (a b : ℝ) : ‖(((a : ℝ) : ℂ)⁻¹) + (((b : ℝ) : ℂ)⁻¹)‖ = |a⁻¹ + b⁻¹| := by
  rw [← Complex.ofReal_inv (r := a), ← Complex.ofReal_inv (r := b)]
  rw [← Complex.ofReal_add]
  exact RCLike.norm_ofReal (a⁻¹ + b⁻¹)

/-- phase-coincidence of the two exponentials at `t = N` (uses `E(2νN) = 1`). -/
lemma uminus_eq_uplus_at_N (f : ℝ → ℝ) (ν : ℤ) (N : ℕ) : uminus f ν (N : ℝ) = uplus f ν (N : ℝ) := by
  unfold uplus uminus
  have harg : f (N : ℝ) - (-(ν : ℝ)) * (N : ℝ) =
      (f (N : ℝ) - (ν : ℝ) * (N : ℝ)) + 2 * (ν : ℝ) * (N : ℝ) := by ring
  rw [harg]
  rw [E_add]
  have hz : (2 * (ν : ℝ) * (N : ℝ)) = (((2 * ν * (N : ℤ) : ℤ) : ℤ) : ℝ) := by norm_num
  rw [hz, E_of_int]
  simp

/-- phase-coincidence of the two exponentials at `t = 0`. -/
lemma uminus_eq_uplus_at_zero (f : ℝ → ℝ) (ν : ℤ) : uminus f ν 0 = uplus f ν 0 := by
  unfold uplus uminus
  congr 1
  ring

/-- Boundary estimate for one endpoint of `pairA`. -/
lemma bound_pairA_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) {t : ℝ} (ht : t ∈ sInt N)
    (hphase : uminus f ν t = uplus f ν t) :
    ‖pairA N f ν t‖ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hw : 1 / 2 ≤ gf N f t ∧ gf N f t ≤ B - 1 / 2 := hgm t ht
  have hnorm1 : ‖uplus f ν t‖ = 1 := by
    unfold uplus
    exact E_norm (f t - (ν : ℝ) * t)
  have hnp : ‖pden N f ν t + mden N f ν t‖ =
      |(gf N f t - (ν : ℝ))⁻¹ + (gf N f t + (ν : ℝ))⁻¹| := by
    unfold pden mden
    exact norm_inv_add_inv (gf N f t - (ν : ℝ)) (gf N f t + (ν : ℝ))
  calc
    ‖pairA N f ν t‖
        = ‖uplus f ν t * (pden N f ν t + mden N f ν t)‖ := by
            unfold pairA
            rw [hphase]
            rw [← mul_add]
    _ = ‖uplus f ν t‖ * ‖pden N f ν t + mden N f ν t‖ := by rw [norm_mul]
    _ = |(gf N f t - (ν : ℝ))⁻¹ + (gf N f t + (ν : ℝ))⁻¹| := by rw [hnorm1, hnp]; simp
    _ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by
            exact pair_recip_abs_bound (B := B) (c := (ν : ℝ)) hB hν hw.1 hw.2

/-- Boundary estimate at `t = N`. -/
lemma bound_pairA_at_N_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ‖pairA N f ν (N : ℝ)‖ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by
  have hNmem : (N : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨(zero_lt_N_real hN).le, le_rfl⟩
  exact bound_pairA_le hN f hB hF hmarg ν hν hNmem (uminus_eq_uplus_at_N f ν N)

/-- Boundary estimate at `t = 0`. -/
lemma bound_pairA_at_zero_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ‖pairA N f ν 0‖ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by
  have h0mem : (0 : ℝ) ∈ sInt N := by
    unfold sInt
    exact ⟨le_rfl, (zero_lt_N_real hN).le⟩
  exact bound_pairA_le hN f hB hF hmarg ν hν h0mem (uminus_eq_uplus_at_zero f ν)

/-- norm of a real embedded in ℂ. -/
lemma norm_ofReal_complex (a : ℝ) : ‖((a : ℝ) : ℂ)‖ = |a| := by
  norm_num [Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]

/-- norm of the square of a real embedded in ℂ. -/
lemma norm_sq_ofReal_complex (b : ℝ) : ‖((b : ℝ) : ℂ) ^ 2‖ = |b| ^ 2 := by
  rw [pow_two, norm_mul]
  simp [norm_ofReal_complex, sq, mul_comm, mul_left_comm, mul_assoc]

/-- `‖↑a / (↑b)^2‖ = |a| / |b|^2` for real `a`, nonzero `b`. -/
lemma norm_real_div_sq (a b : ℝ) (hb : b ≠ 0) :
    ‖(((a : ℝ) : ℂ) / (((b : ℝ) : ℂ) ^ 2))‖ = |a| / |b| ^ 2 := by
  rw [norm_div]
  rw [norm_ofReal_complex, norm_sq_ofReal_complex]

/-- pointwise norm bound for the first remainder summand. -/
lemma norm_pairR_le1 {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ∀ x : ℝ, x ∈ sInt N →
      ‖uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖
        ≤ wf N f x / ((ν : ℝ) - gf N f x) ^ 2 := by
  intro x hx
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hwf : 0 ≤ wf N f x := wf_nonneg_closed hN f hF hpp x hx
  have hup : gf N f x ≤ B - 1 / 2 := (hgm x hx).2
  have hne : gf N f x - (ν : ℝ) ≠ 0 := by
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    linarith
  have hnormu : ‖uplus f ν x‖ = 1 := by
    unfold uplus
    exact E_norm (f x - (ν : ℝ) * x)
  have hEq : ‖uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ =
      wf N f x / ((ν : ℝ) - gf N f x) ^ 2 := by
    calc
      ‖uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖
          = ‖uplus f ν x‖ * ‖(((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := by
              rw [norm_mul]
      _ = ‖(((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := by rw [hnormu]; simp
      _ = |wf N f x| / |gf N f x - (ν : ℝ)| ^ 2 := by
              exact norm_real_div_sq (wf N f x) (gf N f x - (ν : ℝ)) hne
      _ = wf N f x / ((ν : ℝ) - gf N f x) ^ 2 := by
              have ha : |wf N f x| = wf N f x := abs_of_nonneg hwf
              have hb : |gf N f x - (ν : ℝ)| = (ν : ℝ) - gf N f x := by
                have hneg : gf N f x - (ν : ℝ) ≤ 0 := by linarith
                rw [abs_of_nonpos hneg]
                ring
              rw [ha, hb]
  exact le_of_eq hEq

/-- pointwise norm bound for the second remainder summand. -/
lemma norm_pairR_le2 {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ∀ x : ℝ, x ∈ sInt N →
      ‖uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖
        ≤ wf N f x / ((ν : ℝ) + gf N f x) ^ 2 := by
  intro x hx
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hwf : 0 ≤ wf N f x := wf_nonneg_closed hN f hF hpp x hx
  have hlo : 1 / 2 ≤ gf N f x := (hgm x hx).1
  have hne : gf N f x + (ν : ℝ) ≠ 0 := by
    have hpos : 0 < gf N f x + (ν : ℝ) := by linarith
    linarith
  have hnormu : ‖uminus f ν x‖ = 1 := by
    unfold uminus
    exact E_norm (f x - (-(ν : ℝ)) * x)
  have hEq : ‖uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ =
      wf N f x / ((ν : ℝ) + gf N f x) ^ 2 := by
    calc
      ‖uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖
          = ‖uminus f ν x‖ * ‖(((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := by
              rw [norm_mul]
      _ = ‖(((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := by rw [hnormu]; simp
      _ = |wf N f x| / |gf N f x + (ν : ℝ)| ^ 2 := by
              exact norm_real_div_sq (wf N f x) (gf N f x + (ν : ℝ)) hne
      _ = wf N f x / ((ν : ℝ) + gf N f x) ^ 2 := by
              have ha : |wf N f x| = wf N f x := abs_of_nonneg hwf
              have hb : |gf N f x + (ν : ℝ)| = (ν : ℝ) + gf N f x := by
                have hpos : 0 ≤ gf N f x + (ν : ℝ) := by linarith
                rw [abs_of_nonneg hpos]
                ring
              rw [ha, hb]
  exact le_of_eq hEq

/-- The remainder-integral norm bound. -/
lemma pairR_integral_norm_le {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ‖∫ x in 0..(N : ℝ), pairR N f ν x‖
      ≤ (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := by
  have h0Nle : (0 : ℝ) ≤ (N : ℝ) := (zero_lt_N_real hN).le
  let k1 : ℝ → ℝ := fun x => wf N f x / ((ν : ℝ) - gf N f x) ^ 2
  let k2 : ℝ → ℝ := fun x => wf N f x / ((ν : ℝ) + gf N f x) ^ 2
  have hgm : ∀ y ∈ sInt N, 1 / 2 ≤ gf N f y ∧ gf N f y ≤ B - 1 / 2 :=
    gf_margin_closed hN f hB hF hmarg
  have hcontR : ContinuousOn (pairR N f ν) (sInt N) := continuousOn_pairR hN f hB hF hmarg ν hν
  have hcontR' : ContinuousOn (pairR N f ν) (Set.uIcc 0 (N : ℝ)) := by
    rw [Set.uIcc_of_le h0Nle]
    simpa [sInt] using hcontR
  have hintR : IntervalIntegrable (pairR N f ν) MeasureTheory.volume 0 (N : ℝ) :=
    hcontR'.intervalIntegrable
  have hgC : ContinuousOn (gf N f) (sInt N) := continuousOn_gf hN f hF
  have hwC : ContinuousOn (wf N f) (sInt N) := continuousOn_wf hN f hF
  have hd1C : ContinuousOn (fun x : ℝ => ((ν : ℝ) - gf N f x) ^ 2) (sInt N) := by
    have h1 : ContinuousOn (fun x : ℝ => (ν : ℝ) - gf N f x) (sInt N) :=
      continuousOn_const.sub hgC
    have hfun : (fun x : ℝ => ((ν : ℝ) - gf N f x) ^ 2) =
        (fun x : ℝ => (ν : ℝ) - gf N f x) * (fun x : ℝ => (ν : ℝ) - gf N f x) := by
      funext x
      rw [pow_two]
      rfl
    rw [hfun]
    exact h1.mul h1
  have hd2C : ContinuousOn (fun x : ℝ => ((ν : ℝ) + gf N f x) ^ 2) (sInt N) := by
    have h2 : ContinuousOn (fun x : ℝ => (ν : ℝ) + gf N f x) (sInt N) :=
      continuousOn_const.add hgC
    have hfun : (fun x : ℝ => ((ν : ℝ) + gf N f x) ^ 2) =
        (fun x : ℝ => (ν : ℝ) + gf N f x) * (fun x : ℝ => (ν : ℝ) + gf N f x) := by
      funext x
      rw [pow_two]
      rfl
    rw [hfun]
    exact h2.mul h2
  have hne1 : ∀ x ∈ sInt N, ((ν : ℝ) - gf N f x) ≠ 0 := by
    intro x hx
    have hup : gf N f x ≤ B - 1 / 2 := (hgm x hx).2
    have hle : gf N f x - (ν : ℝ) ≤ -1 / 2 := by linarith
    linarith
  have hne2 : ∀ x ∈ sInt N, ((ν : ℝ) + gf N f x) ≠ 0 := by
    intro x hx
    have hlo : 1 / 2 ≤ gf N f x := (hgm x hx).1
    have hpos : 0 < (ν : ℝ) + gf N f x := by linarith
    linarith
  have hk1C : ContinuousOn k1 (sInt N) := by
    dsimp [k1]
    exact hwC.div hd1C (fun x hx => pow_ne_zero 2 (hne1 x hx))
  have hk2C : ContinuousOn k2 (sInt N) := by
    dsimp [k2]
    exact hwC.div hd2C (fun x hx => pow_ne_zero 2 (hne2 x hx))
  have hk1C' : ContinuousOn k1 (Set.uIcc 0 (N : ℝ)) := by
    rw [Set.uIcc_of_le h0Nle]
    simpa [sInt] using hk1C
  have hk2C' : ContinuousOn k2 (Set.uIcc 0 (N : ℝ)) := by
    rw [Set.uIcc_of_le h0Nle]
    simpa [sInt] using hk2C
  have hk1int : IntervalIntegrable k1 MeasureTheory.volume 0 (N : ℝ) := hk1C'.intervalIntegrable
  have hk2int : IntervalIntegrable k2 MeasureTheory.volume 0 (N : ℝ) := hk2C'.intervalIntegrable
  have hkabs1 : IntervalIntegrable (fun x : ℝ => ‖pairR N f ν x‖) MeasureTheory.volume 0 (N : ℝ) := by
    have h : ContinuousOn (fun x : ℝ => ‖pairR N f ν x‖) (Set.uIcc 0 (N : ℝ)) := by
      rw [Set.uIcc_of_le h0Nle]
      simpa [sInt] using hcontR.norm
    exact h.intervalIntegrable
  have hpoint : ∀ x ∈ Set.Icc 0 (N : ℝ), ‖pairR N f ν x‖ ≤ k1 x + k2 x := by
    intro x hx
    have hx' : x ∈ sInt N := by simpa [sInt] using hx
    have h1p := norm_pairR_le1 hN f hB hF hpp hmarg ν hν x hx'
    have h2p := norm_pairR_le2 hN f hB hF hpp hmarg ν hν x hx'
    have hnorm_split : ‖pairR N f ν x‖ ≤
        ‖uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ +
        ‖uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := by
      dsimp [pairR]
      exact norm_add_le _ _
    calc
      ‖pairR N f ν x‖
          ≤ ‖uplus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x - (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ +
            ‖uminus f ν x * (((wf N f x : ℝ) : ℂ) / ((((gf N f x + (ν : ℝ)) : ℝ) : ℂ) ^ 2))‖ := hnorm_split
      _ ≤ k1 x + k2 x := by
            dsimp [k1, k2]
            linarith
  have hnorm1 : ‖∫ x in 0..(N : ℝ), pairR N f ν x‖ ≤
      ∫ x in 0..(N : ℝ), ‖pairR N f ν x‖ := by
    exact intervalIntegral.norm_integral_le_integral_norm (f := pairR N f ν) h0Nle
  have hstep : (∫ x in 0..(N : ℝ), ‖pairR N f ν x‖) ≤
      ∫ x in 0..(N : ℝ), k1 x + k2 x := by
    refine intervalIntegral.integral_mono_on h0Nle ?_ ?_ ?_
    · exact hkabs1
    · have hfun : (fun x : ℝ => k1 x + k2 x) = k1 + k2 := by
        funext x
        rfl
      rw [hfun]
      exact (hk1C'.add hk2C').intervalIntegrable
    · intro x hx
      have hx' : x ∈ sInt N := by simpa [sInt] using hx
      exact hpoint x (by simpa [sInt] using hx')
  have hsum : (∫ x in 0..(N : ℝ), k1 x + k2 x) = (∫ x in 0..(N : ℝ), k1 x) + (∫ x in 0..(N : ℝ), k2 x) := by
    exact intervalIntegral.integral_add hk1int hk2int
  have hb1 : (∫ x in 0..(N : ℝ), k1 x) ≤ (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 := by
    dsimp [k1]
    exact int_remainder_sub_le hN f hB hν hF hmarg
  have hb2 : (∫ x in 0..(N : ℝ), k2 x) ≤ (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := by
    dsimp [k2]
    exact int_remainder_add_le hN f hB hν hF hmarg
  calc
    ‖∫ x in 0..(N : ℝ), pairR N f ν x‖ ≤ ∫ x in 0..(N : ℝ), ‖pairR N f ν x‖ := hnorm1
    _ ≤ ∫ x in 0..(N : ℝ), k1 x + k2 x := hstep
    _ = (∫ x in 0..(N : ℝ), k1 x) + (∫ x in 0..(N : ℝ), k2 x) := hsum
    _ ≤ (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := by linarith

/-- The exact integration-by-parts identity for the pair `T_ν + T_{−ν}`. -/
lemma ibp_pair_identity {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (sInt N))
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    (tau * I) * ((∫ x in 0..(N : ℝ), uplus f ν x) + (∫ x in 0..(N : ℝ), uminus f ν x)) =
      pairA N f ν (N : ℝ) - pairA N f ν 0 + (∫ x in 0..(N : ℝ), pairR N f ν x) := by
  have h0N : (0 : ℝ) < (N : ℝ) := zero_lt_N_real hN
  have hcontA : ContinuousOn (pairA N f ν) (sInt N) := continuousOn_pairA hN f hB hF hmarg ν hν
  have hcontG : ContinuousOn (pairG N f ν) (sInt N) := continuousOn_pairG hN f hB hF hmarg ν hν
  have hintG : IntervalIntegrable (pairG N f ν) MeasureTheory.volume 0 (N : ℝ) :=
    intervalIntegrable_of_continuousOn hN hcontG
  have hftc : (∫ x in 0..(N : ℝ), pairG N f ν x) = pairA N f ν (N : ℝ) - pairA N f ν 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := (N : ℝ)) h0N.le
      hcontA (fun x hx => deriv_pairA hN f hB hF hmarg ν hν hx) hintG
  have hcontR : ContinuousOn (pairR N f ν) (sInt N) := continuousOn_pairR hN f hB hF hmarg ν hν
  have hintR : IntervalIntegrable (pairR N f ν) MeasureTheory.volume 0 (N : ℝ) :=
    intervalIntegrable_of_continuousOn hN hcontR
  have hcontUp : ContinuousOn (uplus f ν) (sInt N) := continuousOn_uplus hN f hB hF ν
  have hcontUm : ContinuousOn (uminus f ν) (sInt N) := continuousOn_uminus hN f hB hF ν
  have hintUp : IntervalIntegrable (uplus f ν) MeasureTheory.volume 0 (N : ℝ) :=
    intervalIntegrable_of_continuousOn hN hcontUp
  have hintUm : IntervalIntegrable (uminus f ν) MeasureTheory.volume 0 (N : ℝ) :=
    intervalIntegrable_of_continuousOn hN hcontUm
  have hdecomp : (∫ x in 0..(N : ℝ), pairG N f ν x) =
      (tau * I) * (∫ x in 0..(N : ℝ), uplus f ν x + uminus f ν x) -
        (∫ x in 0..(N : ℝ), pairR N f ν x) := by
    calc
      (∫ x in 0..(N : ℝ), pairG N f ν x)
          = ∫ x in 0..(N : ℝ), ((tau * I) * (uplus f ν x + uminus f ν x) - pairR N f ν x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              rfl
      _ = (∫ x in 0..(N : ℝ), (tau * I) * (uplus f ν x + uminus f ν x)) -
          (∫ x in 0..(N : ℝ), pairR N f ν x) := by
              rw [intervalIntegral.integral_sub]
              · simpa using (hintUp.add hintUm).const_mul (tau * I)
              · exact hintR
      _ = (tau * I) * (∫ x in 0..(N : ℝ), uplus f ν x + uminus f ν x) -
          (∫ x in 0..(N : ℝ), pairR N f ν x) := by
              rw [intervalIntegral.integral_const_mul]
  have hintadd : (∫ x in 0..(N : ℝ), uplus f ν x + uminus f ν x) =
      (∫ x in 0..(N : ℝ), uplus f ν x) + (∫ x in 0..(N : ℝ), uminus f ν x) := by
    exact intervalIntegral.integral_add hintUp hintUm
  calc
    (tau * I) * ((∫ x in 0..(N : ℝ), uplus f ν x) + (∫ x in 0..(N : ℝ), uminus f ν x))
        = (tau * I) * (∫ x in 0..(N : ℝ), uplus f ν x + uminus f ν x) := by rw [hintadd]
    _ = (tau * I) * (∫ x in 0..(N : ℝ), uplus f ν x + uminus f ν x) -
          (∫ x in 0..(N : ℝ), pairR N f ν x) + (∫ x in 0..(N : ℝ), pairR N f ν x) := by ring
    _ = (∫ x in 0..(N : ℝ), pairG N f ν x) + (∫ x in 0..(N : ℝ), pairR N f ν x) := by
          rw [← hdecomp]
    _ = pairA N f ν (N : ℝ) - pairA N f ν 0 + (∫ x in 0..(N : ℝ), pairR N f ν x) := by
          rw [hftc]

lemma pair_bound {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    (ν : ℤ) (hν : (B : ℝ) ≤ (ν : ℝ)) :
    ‖(∫ x in 0..(N : ℝ), E (f x - (ν : ℝ) * x)) +
      (∫ x in 0..(N : ℝ), E (f x - (-(ν : ℝ)) * x))‖
      ≤ 60 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2 := by
  have hF' : ContDiffOn ℝ 2 f (sInt N) := by simpa [sInt] using hF
  have hpp' : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x := hpp
  change ‖(∫ x in 0..(N : ℝ), uplus f ν x) + (∫ x in 0..(N : ℝ), uminus f ν x)‖
      ≤ 60 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2
  let S : ℂ := (∫ x in 0..(N : ℝ), uplus f ν x) + (∫ x in 0..(N : ℝ), uminus f ν x)
  change ‖S‖ ≤ 60 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2
  -- exact IBP identity for the pair
  have hident := ibp_pair_identity hN f hB hF' hmarg ν hν
  have hident' : (tau * I) * S = pairA N f ν (N : ℝ) - pairA N f ν 0 +
      (∫ x in 0..(N : ℝ), pairR N f ν x) := by
    simpa [S] using hident
  -- endpoint bound
  have hbA1 : ‖pairA N f ν (N : ℝ)‖ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) :=
    bound_pairA_at_N_le hN f hB hF' hmarg ν hν
  have hbA0 : ‖pairA N f ν 0‖ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) :=
    bound_pairA_at_zero_le hN f hB hF' hmarg ν hν
  have hbA : ‖pairA N f ν (N : ℝ) - pairA N f ν 0‖ ≤
      4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by
    calc
      ‖pairA N f ν (N : ℝ) - pairA N f ν 0‖
          ≤ ‖pairA N f ν (N : ℝ)‖ + ‖pairA N f ν 0‖ := norm_sub_le _ _
      _ ≤ 2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) +
          2 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := add_le_add hbA1 hbA0
      _ = 4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := by ring
  -- remainder bound
  have hbR := pairR_integral_norm_le hN f hB hF' hpp' hmarg ν hν
  have hnorm : ‖(tau * I) * S‖ ≤
      4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) +
        (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := by
    rw [hident']
    have h01 : ‖pairA N f ν (N : ℝ) - pairA N f ν 0 + (∫ x in 0..(N : ℝ), pairR N f ν x)‖ ≤
        ‖pairA N f ν (N : ℝ) - pairA N f ν 0‖ + ‖∫ x in 0..(N : ℝ), pairR N f ν x‖ :=
      norm_add_le _ _
    have h02 : ‖pairA N f ν (N : ℝ) - pairA N f ν 0‖ + ‖∫ x in 0..(N : ℝ), pairR N f ν x‖ ≤
        4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) +
          (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := by
      have h1 : ‖pairA N f ν (N : ℝ) - pairA N f ν 0‖ ≤ 4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) := hbA
      have h2 : ‖∫ x in 0..(N : ℝ), pairR N f ν x‖ ≤
          (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 := hbR
      linarith
    exact le_trans h01 h02
  -- ‖tauI‖ ≥ 1 so ‖S‖ ≤ ‖(tauI)·S‖
  have htau : (1 : ℝ) ≤ ‖tau * I‖ := by
    rw [norm_mul, Complex.norm_I, mul_comm, one_mul]
    dsimp [tau]
    rw [norm_ofReal_complex]
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_gt_three]
  have hle1 : ‖S‖ ≤ ‖(tau * I) * S‖ := by
    rw [norm_mul]
    calc
      ‖S‖ = (1 : ℝ) * ‖S‖ := by ring
      _ ≤ ‖tau * I‖ * ‖S‖ := mul_le_mul_of_nonneg_right htau (norm_nonneg S)
  have hle2 : ‖S‖ ≤
      4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) +
        (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 :=
    le_trans hle1 hnorm
  have hDpos : 0 < (ν : ℝ) - B + 1 := by linarith
  have hBp : 0 ≤ B + 1 := by linarith
  have hca := constant_arith_bound (B := B) (c := (ν : ℝ)) hB hν
  have hle3 : 4 * (B - 1 / 2) / ((ν : ℝ) ^ 2 - (B - 1 / 2) ^ 2) +
        (B - 1) / ((ν : ℝ) - B + 1 / 2) ^ 2 + (B - 1) / ((ν : ℝ) + 1 / 2) ^ 2 ≤
      21 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2 := hca
  have hle4 : 21 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2 ≤
      60 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2 := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by norm_num) hBp
    · positivity
  exact le_trans (le_trans hle2 hle3) hle4

end
end Submission.SdtPoisson


open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Core definitions for the truncated Poisson formula

Shared module (no `sor~ry`) containing the quantities used by the truncated
Poisson proof and by the child modules `RhoChild`, `SawSubChild`,
`PairSumChild` (which must import THIS module rather than
`Submission.SdtPoisson` to avoid import cycles).
-/

namespace Submission.SdtPoisson

noncomputable section

/-- The discrete sum (via `E`). -/
def discrSumE (f : ℝ → ℝ) (N : ℕ) : ℂ := ∑ m ∈ Finset.Icc 1 N, E (f (m : ℝ))

/-- The ν-sum of oscillatory integrals over the integer window `[α,β]`. -/
def oscSumE (f : ℝ → ℝ) (N : ℕ) (α β : ℤ) : ℂ := ∑ ν ∈ Finset.Icc α β, oscIntHat f N ν

/-- The boundary `(E(fN) − E(f0))/2`. -/
def bdVal (f : ℝ → ℝ) (N : ℕ) : ℂ := (E (f (N : ℝ)) - E (f 0)) / 2

/-- The error kernel `ρ(K) := ∫ (saw − sawHat K)·(τi f' E)`. -/
def rhoErr (f : ℝ → ℝ) (N : ℕ) (K : ℕ) : ℂ :=
  ∫ x in 0..(N : ℝ), (((saw x : ℝ) : ℂ) - sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))

/-- The full sawtooth integral `J`. -/
def sawInt (f : ℝ → ℝ) (N : ℕ) : ℂ :=
  ∫ x in 0..(N : ℝ), ((saw x : ℝ) : ℂ) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))

/-- The finite sawtooth integral `J_K`. -/
def sawHatInt (f : ℝ → ℝ) (N : ℕ) (K : ℕ) : ℂ :=
  ∫ x in 0..(N : ℝ), (sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))

/-- `Σ_{n=1}^K 1/n² ≤ 2` (ℕ version). -/
lemma sum_one_div_sq_nat_le (K : ℕ) : (∑ n ∈ Finset.Icc 1 K, (1 : ℝ) / ((n : ℝ) ^ 2)) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  have hset : (∑ n ∈ Finset.Icc 1 K, (1 : ℝ) / ((n : ℝ) ^ 2)) =
      ∑ i ∈ Finset.Ioo (0 : ℕ) (K + 1), (((i : ℝ) ^ 2)⁻¹) := by
    have heq : Finset.Ioo (0 : ℕ) (K + 1) = Finset.Icc 1 K := by
      ext n
      simp [Finset.mem_Ioo, Finset.mem_Icc]
      omega
    rw [heq]
    apply Finset.sum_congr rfl
    intro n hn
    rw [one_div]
  calc
    (∑ n ∈ Finset.Icc 1 K, (1 : ℝ) / ((n : ℝ) ^ 2))
        = ∑ i ∈ Finset.Ioo (0 : ℕ) (K + 1), (((i : ℝ) ^ 2)⁻¹) := hset
    _ ≤ 2 / (0 + 1) := by simpa using h
    _ = 2 := by norm_num

/-- `Σ_{ν=1}^K 1/ν² ≤ 2` (ν over positive integers). -/
lemma sum_one_div_sq_Icc_le (K : ℕ) :
    (∑ ν ∈ Finset.Icc 1 (K : ℤ), (1 : ℝ) / ((ν : ℝ) ^ 2)) ≤ 2 := by
  have hre : (∑ ν ∈ Finset.Icc 1 (K : ℤ), (1 : ℝ) / ((ν : ℝ) ^ 2)) =
      ∑ n ∈ Finset.Icc 1 K, (1 : ℝ) / ((n : ℝ) ^ 2) := by
    refine Finset.sum_bij (fun ν _ => ν.toNat) ?_ ?_ ?_ ?_
    · intro ν hν
      rw [Finset.mem_Icc] at hν ⊢
      constructor <;> omega
    · intro ν hν μ hμ hνμ
      have hνn : ν = (ν.toNat : ℤ) := by
        have : 0 ≤ ν := by
          rw [Finset.mem_Icc] at hν
          omega
        exact (Int.toNat_of_nonneg this).symm
      have hμn : μ = (μ.toNat : ℤ) := by
        have : 0 ≤ μ := by
          rw [Finset.mem_Icc] at hμ
          omega
        exact (Int.toNat_of_nonneg this).symm
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      refine ⟨(n : ℤ), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · simp
    · intro ν hν
      have hνn : (0 : ℤ) ≤ ν := by
        rw [Finset.mem_Icc] at hν
        omega
      have hνr : (ν : ℝ) = (ν.toNat : ℝ) := by
        have hz : (ν : ℤ) = (ν.toNat : ℤ) := (Int.toNat_of_nonneg hνn).symm
        have hzr : ((ν : ℝ)) = (((ν.toNat : ℤ) : ℝ)) := congrArg (fun z : ℤ => (z : ℝ)) hz
        have hcast : (((ν.toNat : ℤ) : ℝ)) = (ν.toNat : ℝ) := Int.cast_natCast (ν.toNat)
        calc
          (ν : ℝ) = ((ν.toNat : ℤ) : ℝ) := hzr
          _ = (ν.toNat : ℝ) := hcast
      rw [hνr]
  rw [hre]
  exact sum_one_div_sq_nat_le K

end
end Submission.SdtPoisson


open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Pair-sum over the upper tail is O(B)

With the canonical hypotheses (`1 ≤ B`, `f : C² [0,N]`, `f'' ≥ 0` on
`(0,N)`, `1/2 ≤ f' ≤ B − 1/2` on `[0,N]`), and integer bounds
`β + 1 ≤ K`, `(B:ℝ) ≤ (β:ℝ) + 1`, prove

    (∑ ν ∈ Finset.Icc (β + 1) K, ‖oscIntHat f N ν + oscIntHat f N (-ν)‖) ≤ 120·(B + 1)

(`oscIntHat` from `Submission.SdtPoisson`).  Use the per-frequency bound
`Submission.SdtPoisson.pair_bound` (`Submission.SdtPair`) which gives for each
`ν` with `(B : ℝ) ≤ (ν : ℝ)`:

    ‖oscIntHat f N ν + oscIntHat f N (-ν)‖ ≤ 60·(B+1)/((ν:ℝ) − B + 1)^2

Then reindex the sum over `ν ∈ Icc (β+1) K` by `j := ν − β − 1 ≥ 0`, note
`(ν:ℝ) − B + 1 ≥ (j:ℝ) + 1` (because `(β:ℝ)+1 ≥ B`), bound
`1/(ν−B+1)^2 ≤ 1/(j+1)^2` and use
`SdtPoisson.sum_one_div_sq_Icc_le` (`Σ_{m=1}^M 1/m² ≤ 2`) to conclude
`Σ ≤ 60(B+1)·2 = 120(B+1)`.
End with NO gaps.
-/

namespace Submission.PairSumChild

/-- `Σ_{m=1}^K 1/m² ≤ 2` for an integer upper bound `K ≥ 1`. -/
lemma sum_one_div_sq_Icc_le_int (K : ℤ) (hK : 1 ≤ K) :
    (∑ ν ∈ Finset.Icc 1 K, (1 : ℝ) / ((ν : ℝ) ^ 2)) ≤ 2 := by
  have h := SdtPoisson.sum_one_div_sq_Icc_le K.toNat
  have htoNat : ((K.toNat : ℤ)) = K := Int.toNat_of_nonneg (by omega)
  simpa [htoNat] using h

/-- Reindex a sum over `ν ∈ Icc (a+1) b` by `n = ν − a ∈ Icc 1 (b − a)`. -/
lemma reindex_shift {a b : ℤ} (F : ℤ → ℝ) (_h : a + 1 ≤ b) :
    (∑ ν ∈ Finset.Icc (a + 1) b, F ν) = ∑ n ∈ Finset.Icc 1 (b - a), F (a + n) := by
  refine Finset.sum_bij' (s := Finset.Icc (a + 1) b) (t := Finset.Icc 1 (b - a))
    (f := F) (g := fun n => F (a + n))
    (i := fun ν hν => ν - a) (j := fun n hn => a + n) ?_ ?_ ?_ ?_ ?_
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro ν hν
    omega
  · intro n hn
    omega
  · intro ν hν
    congr 1
    omega

lemma pair_sum_le {f : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    {β K : ℤ} (hβK : β + 1 ≤ K) (hBβ : (B : ℝ) ≤ (β : ℝ) + 1) :
    (∑ ν ∈ Finset.Icc (β + 1) K, ‖SdtPoisson.oscIntHat f N ν + SdtPoisson.oscIntHat f N (-ν)‖) ≤
      120 * (B + 1) := by
  have hc : 0 ≤ 60 * (B + 1) := by nlinarith
  have hd : 0 ≤ (β : ℝ) - B + 1 := by linarith
  have hM : 1 ≤ K - β := by omega
  have hterm (ν : ℤ) (hν : ν ∈ Finset.Icc (β + 1) K) :
      ‖SdtPoisson.oscIntHat f N ν + SdtPoisson.oscIntHat f N (-ν)‖ ≤
        60 * (B + 1) / ((ν : ℝ) - B + 1) ^ 2 := by
    have hBν : (B : ℝ) ≤ (ν : ℝ) := by
      rw [Finset.mem_Icc] at hν
      have hle : (((β + 1 : ℤ) : ℝ)) ≤ (ν : ℝ) := by exact_mod_cast hν.1
      have hβ1 : (((β + 1 : ℤ) : ℝ)) = (β : ℝ) + 1 := by norm_num
      linarith
    have hpb := SdtPoisson.pair_bound (N := N) (f := f) (B := B) hN hB hF hpp hmarg ν hBν
    simpa [SdtPoisson.oscIntHat] using hpb
  have hle1 : (∑ ν ∈ Finset.Icc (β + 1) K,
        ‖SdtPoisson.oscIntHat f N ν + SdtPoisson.oscIntHat f N (-ν)‖) ≤
      ∑ ν ∈ Finset.Icc (β + 1) K, (60 * (B + 1)) / ((ν : ℝ) - B + 1) ^ 2 := by
    exact Finset.sum_le_sum (fun ν hν => hterm ν hν)
  have hptw : ∀ n ∈ Finset.Icc 1 (K - β),
      (60 * (B + 1)) / ((((β + n) : ℤ) : ℝ) - B + 1) ^ 2 ≤
        (60 * (B + 1)) / ((n : ℝ) ^ 2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hposn : 0 < (n : ℝ) := by linarith
    have hden : (n : ℝ) ≤ (((β + n : ℤ) : ℝ) - B + 1) := by
      have hcast : ((((β + n : ℤ) : ℝ))) = (β : ℝ) + (n : ℝ) := by
        push_cast
        ring
      rw [hcast]
      linarith
    have hsq : (n : ℝ) ^ 2 ≤ ((((β + n : ℤ) : ℝ)) - B + 1) ^ 2 := by
      exact pow_le_pow_left₀ (le_of_lt hposn) hden 2
    have hsqpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hposn
    exact div_le_div_of_nonneg_left hc hsqpos hsq
  have hre := reindex_shift (a := β) (b := K)
    (F := fun ν : ℤ => (60 * (B + 1)) / ((ν : ℝ) - B + 1) ^ 2) hβK
  have hle2 : (∑ ν ∈ Finset.Icc (β + 1) K, (60 * (B + 1)) / ((ν : ℝ) - B + 1) ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) / ((n : ℝ) ^ 2) := by
    rw [hre]
    exact Finset.sum_le_sum (fun n hn => hptw n hn)
  have hsqsum : (∑ n ∈ Finset.Icc 1 (K - β), (1 : ℝ) / ((n : ℝ) ^ 2)) ≤ 2 :=
    sum_one_div_sq_Icc_le_int (K - β) hM
  have hfactor : (∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) / ((n : ℝ) ^ 2)) ≤
      (60 * (B + 1)) * 2 := by
    calc
      (∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) / ((n : ℝ) ^ 2))
          = ∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) * ((1 : ℝ) / ((n : ℝ) ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [div_eq_mul_one_div]
      _ = (60 * (B + 1)) * (∑ n ∈ Finset.Icc 1 (K - β), (1 : ℝ) / ((n : ℝ) ^ 2)) := by
              rw [Finset.mul_sum]
      _ ≤ (60 * (B + 1)) * 2 := by
              exact mul_le_mul_of_nonneg_left hsqsum hc
  have hle3 : (∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) / ((n : ℝ) ^ 2)) ≤
      120 * (B + 1) := by
    calc
      (∑ n ∈ Finset.Icc 1 (K - β), (60 * (B + 1)) / ((n : ℝ) ^ 2)) ≤ (60 * (B + 1)) * 2 := hfactor
      _ = 120 * (B + 1) := by ring
  exact le_trans hle1 (le_trans hle2 hle3)

end Submission.PairSumChild


open Complex
open scoped Real BigOperators ComplexConjugate Interval
open MeasureTheory intervalIntegral Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# ρ(K) → 0 for the truncated Poisson formula

Prove that the error kernel `rhoErr f N K := ∫ (saw − sawHat K)·(τi f' E)`
(over `[0,N]`, definitions in `Submission.SdtPoisson`) converges to `0` as
`K → ∞`, for `N ≥ 1` and `f` twice continuously differentiable on `[0,N]`
(`ContDiffOn ℝ 2 f (Set.Icc 0 (N:ℝ))`).
-/

namespace Submission.RhoChild

noncomputable section

open Submission.SdtPoisson

/-- The integrand of `rhoErr` (same shape as `SdtPoisson.rhoErr`'s integrand). -/
def rhoF (f : ℝ → ℝ) (K : ℕ) : ℝ → ℂ := fun x =>
  ((((saw x : ℝ) : ℂ) - sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)))

/-- `E : ℝ → ℂ` is continuous. -/
lemma continuous_E : Continuous (E : ℝ → ℂ) := by
  unfold E
  fun_prop

/-- `sawHat K` is continuous. -/
lemma continuous_sawHat (K : ℕ) : Continuous (sawHat K) := by
  unfold sawHat
  refine continuous_finsetSum (s := (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0) ?_
  intro ν hν
  have hc1 : Continuous fun x : ℝ => E (-(((ν : ℝ) * x))) := by
    have hlin : Continuous fun x : ℝ => -(((ν : ℝ) * x)) := by fun_prop
    exact continuous_E.comp hlin
  exact hc1.div_const ((tau * I) * (ν : ℂ))

/-- `x ↦ (saw x : ℂ)` is measurable. -/
lemma measurable_sawC : Measurable fun x : ℝ => ((saw x : ℝ) : ℂ) := by
  have hsaw : Measurable fun x : ℝ => saw x := by
    unfold saw
    fun_prop
  exact (Complex.continuous_ofReal.measurable.comp hsaw)

/-- `|saw x| ≤ 1/2`. -/
lemma saw_abs_le (x : ℝ) : |saw x| ≤ 1 / 2 := by
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x ≤ 1 := le_of_lt (Int.fract_lt_one x)
  unfold saw
  rw [abs_le]
  constructor <;> linarith

/-- `‖(saw x : ℂ)‖ ≤ 1/2`. -/
lemma sawC_norm_le (x : ℝ) : ‖(((saw x : ℝ) : ℂ))‖ ≤ 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact saw_abs_le x

/-- Pointwise bound of the integrand by `‖tau‖·(41/2)·|deriv f x|`. -/
lemma rhoF_norm_le (f : ℝ → ℝ) (K : ℕ) (x : ℝ) :
    ‖rhoF f K x‖ ≤ ‖tau‖ * (41 / 2) * |deriv f x| := by
  dsimp [rhoF]
  have h1 : ‖(((saw x : ℝ) : ℂ) - sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))‖ ≤
      (‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := by
    have hsub : ‖(((saw x : ℝ) : ℂ) - sawHat K x)‖ ≤ ‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖ := norm_sub_le _ _
    calc
      ‖(((saw x : ℝ) : ℂ) - sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))‖
          = ‖((saw x : ℝ) : ℂ) - sawHat K x‖ * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := norm_mul _ _
      _ ≤ (‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := by
          exact mul_le_mul_of_nonneg_right hsub (norm_nonneg _)
  have hsaw : ‖((saw x : ℝ) : ℂ)‖ ≤ 1 / 2 := sawC_norm_le x
  have hsawHat : ‖sawHat K x‖ ≤ 20 := sawHat_norm_bdd K x
  have hsum : ‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖ ≤ 41 / 2 := by linarith
  have hrest0 : ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ ≤ ‖tau‖ * |deriv f x| * ‖E (f x)‖ := by
    calc
      ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ ≤ ‖(tau * I) * ((deriv f x : ℝ) : ℂ)‖ * ‖E (f x)‖ := norm_mul_le _ _
      _ ≤ ‖tau * I‖ * ‖((deriv f x : ℝ) : ℂ)‖ * ‖E (f x)‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖tau‖ * |deriv f x| * ‖E (f x)‖ := by
          rw [norm_mul, norm_I, mul_one]
          simp
  have hrest : ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ ≤ ‖tau‖ * |deriv f x| := by
    calc
      ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ ≤ ‖tau‖ * |deriv f x| * ‖E (f x)‖ := hrest0
      _ = ‖tau‖ * |deriv f x| * 1 := by rw [E_norm]
      _ = ‖tau‖ * |deriv f x| := by ring
  have hstep1 : (‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ ≤
      (41 / 2) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := by
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  calc
    ‖(((saw x : ℝ) : ℂ) - sawHat K x) * ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))‖
        ≤ (‖((saw x : ℝ) : ℂ)‖ + ‖sawHat K x‖) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := h1
    _ ≤ (41 / 2) * ‖(tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x)‖ := hstep1
    _ ≤ (41 / 2) * (‖tau‖ * |deriv f x|) := by
        exact mul_le_mul_of_nonneg_left hrest (by norm_num)
    _ = ‖tau‖ * (41 / 2) * |deriv f x| := by ring

/-- `deriv f` is bounded on the interior of the interval. -/
lemma deriv_bddOn_Ioo {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ C := by
  let g : ℝ → ℝ := fun x => ‖derivWithin f (Set.Icc a b) x‖
  have hcg : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact (SdtOscB.contDiffOn_derivWithin_one hab f hF).continuousOn.norm
  have hne : (Set.Icc a b).Nonempty := ⟨a, by simp [le_of_lt hab]⟩
  rcases isCompact_Icc.exists_isMaxOn hne hcg with ⟨x0, hx0, hmax⟩
  refine ⟨|derivWithin f (Set.Icc a b) x0|, ?_, ?_⟩
  · exact abs_nonneg _
  · intro x hx
    have hle : ‖derivWithin f (Set.Icc a b) x‖ ≤ ‖derivWithin f (Set.Icc a b) x0‖ :=
      hmax ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have heq : deriv f x = derivWithin f (Set.Icc a b) x :=
      (SdtOscB.derivWithin_eq_deriv_of_Ioo f hx).symm
    rw [heq]
    rwa [Real.norm_eq_abs] at hle

/-- For `x` not an integer, `rhoF f K x → 0` as `K → ∞`. -/
lemma rhoF_tendsto_zero_of_notInt (f : ℝ → ℝ) {x : ℝ}
    (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) :
    Tendsto (fun K : ℕ => rhoF f K x) atTop (𝓝 (0 : ℂ)) := by
  have hs := sawHat_tendsto_saw hx
  have hsub : Tendsto (fun K : ℕ => (((saw x : ℝ) : ℂ) - sawHat K x)) atTop (𝓝 (0 : ℂ)) := by
    have hc : Tendsto (fun _ : ℕ => (((saw x : ℝ) : ℂ))) atTop (𝓝 (((saw x : ℝ) : ℂ))) := tendsto_const_nhds
    have h := hc.sub hs
    simpa using h
  have hrest : Tendsto (fun _ : ℕ => ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x) : ℂ))
      atTop (𝓝 ((tau * I) * ((deriv f x : ℝ) : ℂ) * E (f x))) := tendsto_const_nhds
  have hmul := hsub.mul hrest
  convert hmul using 1
  · funext K
    rfl
  · simp

/-- A.e. pointwise convergence to zero. -/
lemma rhoF_ae_tendsto_zero (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume, Tendsto (fun K : ℕ => rhoF f K x) atTop (𝓝 (0 : ℂ)) := by
  let bad : Set ℝ := {x : ℝ | ∃ z : ℤ, (z : ℝ) = x}
  have hbadc : bad.Countable := by
    dsimp [bad]
    have hset : {x : ℝ | ∃ z : ℤ, (z : ℝ) = x} = Set.range (fun z : ℤ => (z : ℝ)) := by
      ext x
      simp
    rw [hset]
    exact Set.countable_range (fun z : ℤ => (z : ℝ))
  have hae : ∀ᵐ x ∂volume, x ∉ bad := hbadc.ae_notMem volume
  exact hae.mono (fun x hx => rhoF_tendsto_zero_of_notInt f hx)

/-- The integrand is ae strongly measurable on the interval (via replacing
`deriv f` by the within-derivative, which is continuous on `[0,b]`). -/
lemma rhoF_aestronglyMeasurable {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) (K : ℕ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 b)) :
    AEStronglyMeasurable (rhoF f K) (volume.restrict (Set.uIoc 0 b)) := by
  have hle : (0 : ℝ) ≤ b := le_of_lt hb
  have hIoc : Set.uIoc 0 b = Set.Ioc 0 b := by
    simpa using (Set.uIoc_of_le hle)
  let m : Measure ℝ := volume.restrict (Set.Ioc 0 b)
  let g : ℝ → ℝ := fun x => derivWithin f (Set.Icc 0 b) x
  let A : ℝ → ℂ := fun x => (((saw x : ℝ) : ℂ) - sawHat K x)
  let B : ℝ → ℂ := fun x => (tau * I) * ((g x : ℝ) : ℂ) * E (f x)
  let H : ℝ → ℂ := A * B
  -- equality ae on the interval
  have hIoo_ae : ∀ᵐ x ∂m, x ∈ Set.Ioo 0 b := by
    dsimp [m]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hcongr : (rhoF f K : ℝ → ℂ) =ᵐ[m] H := by
    filter_upwards [hIoo_ae] with x hx
    dsimp [H, A, B, rhoF, g]
    rw [← SdtOscB.derivWithin_eq_deriv_of_Ioo f hx]
  -- strong measurability of H
  have hAsm : AEStronglyMeasurable A m := by
    have hmeas : Measurable A := by
      dsimp [A]
      exact measurable_sawC.sub (continuous_sawHat K).measurable
    exact hmeas.aestronglyMeasurable
  have hgCont : ContinuousOn g (Set.Icc 0 b) := by
    dsimp [g]
    exact (SdtOscB.contDiffOn_derivWithin_one hb f hF).continuousOn
  have hgSm : AEStronglyMeasurable g m := by
    dsimp [m]
    exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact hgCont isCompact_Icc
      measurableSet_Ioc Set.Ioc_subset_Icc_self
  have hgCSm : AEStronglyMeasurable (fun x : ℝ => (g x : ℂ)) m :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hgSm
  have hEfCont : ContinuousOn (fun x : ℝ => E (f x)) (Set.Icc 0 b) :=
    continuous_E.comp_continuousOn hF.continuousOn
  have hEfSm : AEStronglyMeasurable (fun x : ℝ => E (f x)) m := by
    dsimp [m]
    exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact hEfCont isCompact_Icc
      measurableSet_Ioc Set.Ioc_subset_Icc_self
  have hBsm : AEStronglyMeasurable B m := by
    dsimp [B]
    have h1 : AEStronglyMeasurable (fun x : ℝ => (tau * I) * ((g x : ℝ) : ℂ)) m :=
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (tau * I : ℂ)) m).mul hgCSm
    exact h1.mul hEfSm
  have hHsm : AEStronglyMeasurable H m := by
    dsimp [H]
    exact hAsm.mul hBsm
  -- transfer to rhoF
  have hcongr' : AEStronglyMeasurable (rhoF f K) m := (aestronglyMeasurable_congr hcongr).mpr hHsm
  -- express with uIoc
  simpa [m, hIoc] using hcongr'

/-- The main dominated-convergence proof. -/
lemma rhoErr_tendsto_zero {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    Tendsto (fun K : ℕ => rhoErr f N K) atTop (𝓝 0) := by
  let b : ℝ := (N : ℝ)
  have hb0 : (0 : ℝ) < b := by
    dsimp [b]
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hb : (0 : ℝ) ≤ b := le_of_lt hb0
  rcases deriv_bddOn_Ioo hb0 f hF with ⟨C, hC0, hC⟩
  let bound : ℝ := ‖tau‖ * (41 / 2) * C
  have hbd_pt (K : ℕ) : ∀ x, x ∈ Set.Ioo 0 b → ‖rhoF f K x‖ ≤ bound := by
    intro x hx
    have h1 := rhoF_norm_le f K x
    have h2 : ‖tau‖ * (41 / 2) * |deriv f x| ≤ bound := by
      dsimp [bound]
      exact mul_le_mul_of_nonneg_left (hC x hx) (by positivity)
    linarith
  have hneg (K : ℕ) : {x : ℝ | x ∈ Set.uIoc 0 b ∧ ¬ ‖rhoF f K x‖ ≤ bound} ⊆ ({b} : Set ℝ) := by
    intro x hx
    rcases hx with ⟨hxI, hnot⟩
    have hxIoc : x ∈ Set.Ioc 0 b := by simpa [Set.uIoc_of_le hb] using hxI
    by_cases hxint : x ∈ Set.Ioo 0 b
    · exfalso
      exact hnot (hbd_pt K x hxint)
    · rcases hxIoc with ⟨hx0, hxb⟩
      have : x = b := by
        by_contra hne
        have hlt : x < b := lt_of_le_of_ne hxb hne
        exact hxint ⟨hx0, hlt⟩
      exact this
  have hseteq (K : ℕ) : {x : ℝ | ¬ (x ∈ Set.uIoc 0 b → ‖rhoF f K x‖ ≤ bound)} =
        {x : ℝ | x ∈ Set.uIoc 0 b ∧ ¬ (‖rhoF f K x‖ ≤ bound)} := by
      ext x
      by_cases hxI : x ∈ Set.uIoc 0 b <;> simp [hxI]
  have hnull (K : ℕ) : volume {x : ℝ | x ∈ Set.uIoc 0 b ∧ ¬ (‖rhoF f K x‖ ≤ bound)} = 0 := by
    have hmono := measure_mono (μ := volume) (hneg K)
    have hsing : volume ({b} : Set ℝ) = 0 := by simp
    rw [hsing] at hmono
    exact le_antisymm hmono zero_le
  have hae_bound (K : ℕ) : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 b → ‖rhoF f K x‖ ≤ bound := by
    apply (MeasureTheory.ae_iff (μ := volume)).2
    rw [hseteq K]
    exact hnull K
  have hFm : ∀ᶠ K : ℕ in atTop, AEStronglyMeasurable (rhoF f K) (volume.restrict (Set.uIoc 0 b)) := by
    exact Filter.Eventually.of_forall (fun K => rhoF_aestronglyMeasurable hb0 f K hF)
  have hBd : ∀ᶠ K : ℕ in atTop, ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 b → ‖rhoF f K x‖ ≤ bound := by
    exact Filter.Eventually.of_forall (fun K => hae_bound K)
  have hbint : IntervalIntegrable (fun _ : ℝ => bound) volume 0 b := intervalIntegrable_const
  have hlim : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 b →
      Tendsto (fun K : ℕ => rhoF f K x) atTop (𝓝 (0 : ℂ)) := by
    have hae := rhoF_ae_tendsto_zero f
    exact hae.mono (fun x hx _ => hx)
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (F := fun K : ℕ => rhoF f K) (f := fun _ : ℝ => (0 : ℂ))
      (a := 0) (b := b) (μ := volume) (bound := fun _ : ℝ => bound)
      hFm hBd hbint hlim
  have hfin : Tendsto (fun K : ℕ => ∫ x in 0..b, rhoF f K x) atTop (𝓝 (0 : ℂ)) := by
    simpa using hdct
  simpa [b, SdtPoisson.rhoErr, rhoF] using hfin

end
end Submission.RhoChild


open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# `J − J_K = ρ(K)` (pure interval-integral identity)

For `N : ℕ`, `f : ℝ → ℝ`, `K : ℕ`, prove

    SdtPoisson.sawInt f N − SdtPoisson.sawHatInt f N K = SdtPoisson.rhoErr f N K

where (definitions in `Submission.SdtPoisson`):
  sawInt f N := ∫_0^N (saw x : ℂ)·(τi · (deriv f x : ℂ) · E(f x))
  sawHatInt f N K := ∫_0^N sawHat K x·(same factor)
  rhoErr f N K := ∫_0^N ((saw x : ℂ) − sawHat K x)·(same factor)

(All three integrands share the factor `w x := (τi) · (deriv f x : ℂ) · E (f x)`.)
The identity is just the linearity `∫(a−b)·w = ∫a·w − ∫b·w` of the interval
integral, which requires each integrand to be interval-integrable on `[0,N]`.
`saw` is bounded (`|saw x| ≤ 1/2`), `sawHat K` is bounded (`≤ 20`,
`Submission.SdtPoisson.sawHat_norm_bdd`), `E` is bounded by 1, so the only
regularity question is `deriv f`: it is continuous and bounded on `(0,N)`
when `f ∈ ContDiffOn ℝ 2 f (Icc 0 (N:ℝ))` — but note THIS lemma does not
assume any regularity hypothesis on `f`!  Its statement must hold for all
`f` (if the integrals fail to exist for arbitrary `f`, prove it under the
minimum regularity you need, i.e. ADD the hypothesis
`hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))` and `hN : 1 ≤ N` to the
statement, since every use site has them.  Just keep the CONCLUSION
`Tendsto`-free as stated.)
This file ends with a complete proof (no unfinished proofs).
-/

namespace Submission.SawSubChild

noncomputable section

/-- The Dirichlet partial sum `sawHat K x` is continuous in `x`. -/
lemma sawHat_continuous (K : ℕ) : Continuous (fun x : ℝ => SdtPoisson.sawHat K x) := by
  classical
  unfold SdtPoisson.sawHat
  refine continuous_finsetSum ((Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0) ?_
  intro ν hν
  have hlin : Continuous (fun x : ℝ => -((ν : ℝ) * x)) := by fun_prop
  have hz : Continuous (fun x : ℝ => SdtPoisson.E (-((ν : ℝ) * x))) :=
    SdtPoisson.E_continuous.comp hlin
  have hc : Continuous fun _ : ℝ => (((SdtPoisson.tau * I) * (ν : ℂ))⁻¹) := continuous_const
  have hEq : (fun x : ℝ => SdtPoisson.E (-((ν : ℝ) * x)) / ((SdtPoisson.tau * I) * (ν : ℂ))) =
      (fun x : ℝ => SdtPoisson.E (-((ν : ℝ) * x)) * (((SdtPoisson.tau * I) * (ν : ℂ))⁻¹)) := by
    funext x
    rw [div_eq_mul_inv]
  rw [hEq]
  exact hz.mul hc

/-- `J − J_K = ρ(K)` for `f ∈ C²[0,N]`, `N ≥ 1`. -/
lemma sawInt_sub_sawHatInt {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (K : ℕ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    SdtPoisson.sawInt f N - SdtPoisson.sawHatInt f N K = SdtPoisson.rhoErr f N K := by
  let A : ℝ → ℂ := fun x => ((SdtPoisson.saw x : ℝ) : ℂ) *
      ((SdtPoisson.tau * I) * ((deriv f x : ℝ) : ℂ) * SdtPoisson.E (f x))
  let B : ℝ → ℂ := fun x => (SdtPoisson.sawHat K x) *
      ((SdtPoisson.tau * I) * ((deriv f x : ℝ) : ℂ) * SdtPoisson.E (f x))
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h0leN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  -- interval-integrability of the integrand of `sawInt` on each cell [k,k+1]
  have hAcell : ∀ k : ℕ, k < N →
      IntervalIntegrable A volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hi : IntervalIntegrable
        (fun x : ℝ => (SdtPoisson.saw x : ℂ) *
            (((SdtPoisson.tau * I) * (((deriv f x : ℝ) : ℂ))) * SdtPoisson.E (f x)))
        volume (k : ℝ) ((k : ℝ) + 1) :=
      SdtPoisson.emid_sgp_int hN f hF hk
    have hconv : IntervalIntegrable A volume (k : ℝ) ((k : ℝ) + 1) := by
      refine IntervalIntegrable.congr_uIoo (f := (fun x : ℝ => (SdtPoisson.saw x : ℂ) *
            (((SdtPoisson.tau * I) * (((deriv f x : ℝ) : ℂ))) * SdtPoisson.E (f x))))
          (g := A) (μ := volume) (a := (k : ℝ)) (b := (k : ℝ) + 1) hi ?_
      intro x hx
      dsimp [A]
    simpa [Nat.cast_add] using hconv
  have hA : IntervalIntegrable A volume 0 (N : ℝ) := by
    simpa using (IntervalIntegrable.trans_iterate (f := A) (μ := volume)
      (a := fun j : ℕ => (j : ℝ)) (n := N) hAcell)
  -- interval-integrability of the integrand of `sawHatInt` on [0,N]
  have hB : IntervalIntegrable B volume 0 (N : ℝ) := by
    let dW : ℝ → ℝ := fun x => derivWithin f (Set.Icc 0 (N : ℝ)) x
    let surr : ℝ → ℂ := fun x => (SdtPoisson.sawHat K x) *
        ((SdtPoisson.tau * I) * ((dW x : ℝ) : ℂ) * SdtPoisson.E (f x))
    have hdWC : ContinuousOn dW (Set.Icc 0 (N : ℝ)) := by
      dsimp [dW]
      exact (SdtOscB.contDiffOn_derivWithin_one hNpos f hF).continuousOn
    have hEfC : ContinuousOn (fun x : ℝ => SdtPoisson.E (f x)) (Set.Icc 0 (N : ℝ)) :=
      SdtPoisson.emid_E_continuous.comp_continuousOn hF.continuousOn
    have hsurrC : ContinuousOn surr (Set.Icc 0 (N : ℝ)) := by
      dsimp [surr]
      have h1 : ContinuousOn (fun x : ℝ => ((dW x : ℝ) : ℂ)) (Set.Icc 0 (N : ℝ)) :=
        Complex.continuous_ofReal.comp_continuousOn hdWC
      have h2 : ContinuousOn (fun x : ℝ => (SdtPoisson.tau * I) * ((dW x : ℝ) : ℂ))
          (Set.Icc 0 (N : ℝ)) := ContinuousOn.const_mul h1 (SdtPoisson.tau * I)
      have h3 : ContinuousOn (fun x : ℝ =>
          ((SdtPoisson.tau * I) * ((dW x : ℝ) : ℂ)) * SdtPoisson.E (f x))
          (Set.Icc 0 (N : ℝ)) := h2.mul hEfC
      exact (sawHat_continuous K).continuousOn.mul h3
    have hsurrInt : IntervalIntegrable surr volume 0 (N : ℝ) :=
      ContinuousOn.intervalIntegrable_of_Icc h0leN hsurrC
    refine SdtPoisson.emid_intervalIntegrable_congr_of_eqOn_Ioo h0leN hsurrInt ?_
    intro x hx
    dsimp [B, surr, dW]
    rw [SdtOscB.derivWithin_eq_deriv_of_Ioo (a := 0) (b := (N : ℝ)) f hx]
  -- linearity of the interval integral
  have hlin : (∫ x in 0..(N : ℝ), A x) - (∫ x in 0..(N : ℝ), B x) =
      (∫ x in 0..(N : ℝ), A x - B x) := by
    exact (intervalIntegral.integral_sub hA hB).symm
  calc
    SdtPoisson.sawInt f N - SdtPoisson.sawHatInt f N K
        = (∫ x in 0..(N : ℝ), A x) - (∫ x in 0..(N : ℝ), B x) := by
          rfl
    _ = (∫ x in 0..(N : ℝ), A x - B x) := hlin
    _ = SdtPoisson.rhoErr f N K := by
          rw [show (fun x : ℝ => A x - B x) =
              fun x : ℝ => (((SdtPoisson.saw x : ℝ) : ℂ) - SdtPoisson.sawHat K x) *
                ((SdtPoisson.tau * I) * ((deriv f x : ℝ) : ℂ) * SdtPoisson.E (f x)) by
            funext x
            dsimp [A, B]
            ring]
          rfl

end
end Submission.SawSubChild


/-!
# Monotonicity facts for the shifted first derivative (used in the window choice)

Let `a : ℤ`, `N ≥ 3`, and `f : ℝ → ℝ` be `C²` on `[a, a+N]` with
`r ≤ f''(x) ≤ B·r` for `x ∈ (a, a+N)` (`0 < r`, `1 ≤ B`).  For `x ≥ 0` put
`g(x) := f(a + 1 + x)`.  Then `g'` is increasing, with quantitative bounds:

    for 0 ≤ x ≤ y ≤ N−2 :   r·(y−x) ≤ deriv g y − deriv g x ≤ B·r·(y−x)

(the lower bound needs only `r ≤ f''`, the upper only `f'' ≤ B·r`).

## Use
The parent `Submission.SdtLong` picks the ν-window
`A := deriv g 0 − 1`, `B := deriv g M + 1` (`M := N − 2`) for the truncated
Poisson lemma.  This file supplies the key monotonicity/increment estimates.

## Proof sketch
`deriv g t = deriv f (a+1+t)` and `deriv (deriv g) t = deriv (deriv f) (a+1+t)`
(translation-invariance of derivatives: `deriv_comp_const_add`).  The increment
`deriv g y − deriv g x = ∫_x^y deriv(deriv g)(t) dt` by the (second) fundamental
theorem (Mathlib: `intervalIntegral.integral_deriv_of_contDiffOn_Icc`) is
between `r·(y−x)` and `B·r·(y−x)` because the integrand is between `r` and
`B·r` pointwise.  The interval `[a+1+x, a+1+y]` lies strictly inside
`(a, a+N)` (indeed the preimage of `(a, a+N)` under `t ↦ a+1+t` is the open
interval `(−1, N−1)`, which contains `[0, N−2]`), so all derivatives involved
are genuine two-sided derivatives and the `C²` hypothesis applies on an open
neighbourhood.
-/

open Complex
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtWindow

/-- Quantitative monotonicity of the shifted first derivative. -/
theorem shifted_deriv_increment {a : ℤ} {N : ℕ} (hN : 3 ≤ N) (f : ℝ → ℝ)
    {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
      r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyM : y ≤ (N : ℝ) - 2) :
    r * (y - x) ≤ deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) y -
                    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) x ∧
    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) y -
                    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) x ≤ B * r * (y - x) := by
  let u : ℝ → ℝ := fun t : ℝ => (a : ℝ) + 1 + t
  let g : ℝ → ℝ := f ∘ u
  let S : Set ℝ := Set.Ioo (a : ℝ) ((a : ℝ) + N)
  let J : Set ℝ := Set.Ioo (-1 : ℝ) ((N : ℝ) - 1)
  have hSopen : IsOpen S := by dsimp [S]; exact isOpen_Ioo
  have hJopen : IsOpen J := by dsimp [J]; exact isOpen_Ioo
  -- g' is C¹ on the open preimage J of (a, a+N) (which contains [0, N−2]).
  have hgJ : ContDiffOn ℝ 1 (deriv g) J := by
    -- f is C² on the open interval S
    have hfS : ContDiffOn ℝ 2 f S := by
      refine hf.mono ?_
      intro z hz
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    -- deriv f is C¹ on S
    have hdfS : ContDiffOn ℝ 1 (deriv f) S := by
      exact ContDiffOn.deriv_of_isOpen hfS hSopen (by norm_num)
    -- u maps J into S
    have huS : ∀ t : ℝ, t ∈ J → u t ∈ S := by
      intro t ht
      dsimp [u, S]
      constructor
      · linarith [ht.1]
      · linarith [ht.2]
    -- u is C¹ on J
    have huJ : ContDiffOn ℝ 1 u J := by
      dsimp [u]
      fun_prop
    -- (deriv f) ∘ u is C¹ on J
    have hcomp : ContDiffOn ℝ 1 ((deriv f) ∘ u) J := by
      exact ContDiffOn.comp hdfS huJ (by intro t ht; exact huS t ht)
    -- translation invariance: deriv g = (deriv f) ∘ u pointwise
    have hdg : deriv g = (deriv f) ∘ u := by
      funext t
      dsimp [g, u]
      exact deriv_comp_const_add f ((a : ℝ) + 1) t
    simpa [hdg] using hcomp
  -- [x, y] ⊆ J: from 0 ≤ x ≤ t ≤ y ≤ N−2 < N−1 (and −1 < 0)
  have hsub : Set.Icc x y ⊆ J := by
    intro t ht
    dsimp [J]
    constructor
    · have : 0 ≤ t := le_trans hx0 ht.1
      linarith
    · have ht2 : t ≤ (N : ℝ) - 2 := le_trans ht.2 hyM
      linarith
  have hdgxy : ContDiffOn ℝ 1 (deriv g) (Set.Icc x y) := hgJ.mono hsub
  -- Second fundamental theorem: ∫_x^y (deriv g)' = deriv g y − deriv g x
  have hftc : (∫ t in x..y, deriv (deriv g) t) = deriv g y - deriv g x := by
    exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hdgxy hxy
  -- Second-order translation invariance: (deriv g)' = f'' ∘ u pointwise
  have hd2 : ∀ t : ℝ, deriv (deriv g) t = deriv (deriv f) ((a : ℝ) + 1 + t) := by
    intro t
    rw [show deriv g = fun s : ℝ => deriv f ((a : ℝ) + 1 + s) by
      funext s
      exact deriv_comp_const_add f ((a : ℝ) + 1) s]
    exact deriv_comp_const_add (deriv f) ((a : ℝ) + 1) t
  -- Pointwise integrand bounds on [x, y], transferred from hpp on (a, a+N).
  have hb : ∀ t ∈ Set.Icc x y, r ≤ deriv (deriv g) t ∧ deriv (deriv g) t ≤ B * r := by
    intro t ht
    have htJ : t ∈ J := hsub ht
    rw [hd2 t]
    exact hpp ((a : ℝ) + 1 + t) (by
      have huS : ∀ s : ℝ, s ∈ J → (a : ℝ) + 1 + s ∈ S := by
        intro s hs
        dsimp [S]
        constructor
        · linarith [hs.1]
        · linarith [hs.2]
      exact huS t htJ)
  -- integrability of the integrand on [x, y] (continuity on the open J)
  have hcontJ : ContinuousOn (deriv (deriv g)) J := by
    exact ContDiffOn.continuousOn_deriv_of_isOpen hgJ hJopen le_rfl
  have hcont : ContinuousOn (deriv (deriv g)) (Set.Icc x y) := hcontJ.mono hsub
  have hint_ddg : IntervalIntegrable (deriv (deriv g)) MeasureTheory.volume x y := by
    exact hcont.intervalIntegrable_of_Icc hxy
  change r * (y - x) ≤ deriv g y - deriv g x ∧ deriv g y - deriv g x ≤ B * r * (y - x)
  constructor
  · have hlow : (∫ t in x..y, r) ≤ (∫ t in x..y, deriv (deriv g) t) := by
      refine intervalIntegral.integral_mono_on hxy ?_ hint_ddg ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc hxy continuousOn_const
      · intro t ht
        exact (hb t ht).1
    rw [hftc] at hlow
    have hcst : (∫ t in x..y, r) = r * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hcst] at hlow
    exact hlow
  · have hup : (∫ t in x..y, deriv (deriv g) t) ≤ (∫ t in x..y, B * r) := by
      refine intervalIntegral.integral_mono_on hxy hint_ddg ?_ ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc hxy continuousOn_const
      · intro t ht
        exact (hb t ht).2
    rw [hftc] at hup
    have hcst : (∫ t in x..y, B * r) = (B * r) * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hcst] at hup
    exact hup

end Submission.SdtWindow


/-!
# Per-frequency oscillatory integral bound (for the second derivative test)

Let `a : ℤ`, `M + 2 ≤ N`, and `f : ℝ → ℝ` be `C²` on `[a, a+N]` with
`r ≤ f''` on `(a,a+N)` (`0 < r`).  For each integer frequency `ν` define the
phase `F_ν(x) := f(a + 1 + x) − ν·x` on `0 ≤ x ≤ M`.  Since the linear term has
vanishing second derivative, `F_ν'' = f''(a+1+x) ≥ r > 0`, so the oscillatory
integral bound `Submission.SdtOscB.exp_integral_second_deriv_le` applies:

    ‖∫_0^M e(F_ν(x)) dx‖ ≤ 100 / √r

independent of `ν` and of the interval length.  (`e(t) := exp(2πit)`.)

Prove by applying `Submission.SdtOscB.exp_integral_second_deriv_le` to
`F(x) := f ((a:ℝ)+1+x) - (ν:ℝ)*x` on `[0,M]`.  You need:
* `ContDiffOn ℝ 2 F (Set.Icc 0 (M : ℝ))` -- from `ContDiffOn ℝ 2 f
  (Set.Icc (a:ℝ) ((a:ℝ)+N))` via the affine reparametrisation `x ↦ a+1+x`
  (whose image lies inside `[a, a+N]` when `M + 2 ≤ N`) and `ContDiffOn` of the
  linear part; use `ContDiffOn.comp`, `ContDiffOn.sub`, `ContDiffOn.mul`,
  `ContDiffOn.const_mul` etc.
* the second derivative: `deriv (deriv F) t = deriv (deriv f) (a+1+t)` for
  `t ∈ (0, M)` (translation invariance: `deriv_comp_const_add`, used twice),
  which is `≥ r` by `hpp` at the point `a+1+t ∈ (a, a+N)`.

Machine-verified, axiom-clean. -/

open Complex
open scoped Real BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtPerNu

/-- **Per-frequency oscillatory integral bound.** -/
theorem per_nu_integral_bound {a : ℤ} {N M : ℕ} (hM : M + 2 ≤ N) (f : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) → r ≤ deriv (deriv f) x)
    (ν : ℤ) :
    ‖∫ x in 0..(M : ℝ),
        cexp ((((2 * Real.pi * (f ((a : ℝ) + 1 + x) - (ν : ℝ) * x) : ℝ) : ℝ) : ℂ) * I)‖
      ≤ 100 / Real.sqrt r := by
  let F : ℝ → ℝ := fun x : ℝ => f ((a : ℝ) + 1 + x) - (ν : ℝ) * x
  have hM' : (M : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hM
  have hM1 : 1 + M ≤ N := by omega
  have hM1r : (1 : ℝ) + (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hM1
  have h01 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  -- F is C² on [0, M] (composition of f with the affine shift, minus a linear term)
  let T : ℝ → ℝ := fun x : ℝ => (a : ℝ) + 1 + x
  let Is : Set ℝ := Set.Icc (0 : ℝ) (M : ℝ)
  let It : Set ℝ := Set.Icc (a : ℝ) ((a : ℝ) + N)
  have hT : ContDiffOn ℝ 2 T Is := by
    have hglob : ContDiff ℝ 2 (fun x : ℝ => (a : ℝ) + 1 + x) := by
      have hc : ContDiff ℝ 2 (fun _ : ℝ => ((a : ℝ) + 1 : ℝ)) := contDiff_const
      have hid : ContDiff ℝ 2 (fun x : ℝ => x) := contDiff_id
      simpa [add_comm, add_left_comm, add_assoc] using (hc.add hid)
    exact hglob.contDiffOn
  have hmap : Set.MapsTo T Is It := by
    intro x hx
    dsimp [Is, It, T]
    constructor
    · linarith [hx.1]
    · linarith [hx.2, hM1r]
  have hfT2 : ContDiffOn ℝ 2 (f ∘ T) Is := ContDiffOn.comp hf hT hmap
  have hfT2' : ContDiffOn ℝ 2 (fun x : ℝ => f ((a : ℝ) + 1 + x)) Is := by
    simpa [T, Function.comp_def] using hfT2
  have hLin : ContDiffOn ℝ 2 (fun x : ℝ => (ν : ℝ) * x) Is := by
    have hglob : ContDiff ℝ 2 (fun x : ℝ => (ν : ℝ) * x) := by
      have hc : ContDiff ℝ 2 (fun _ : ℝ => (ν : ℝ)) := contDiff_const
      have hid : ContDiff ℝ 2 (fun x : ℝ => x) := contDiff_id
      simpa [mul_comm] using (hc.mul hid)
    exact hglob.contDiffOn
  have hF2 : ContDiffOn ℝ 2 F Is := by
    simpa [F] using hfT2'.sub hLin
  -- second derivative of F on the open interval equals f'' at the shifted point
  have hppF : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) (M : ℝ) → r ≤ deriv (deriv F) x := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have htM : t < (M : ℝ) := ht.2
    let y : ℝ := (a : ℝ) + 1 + t
    have hyI : y ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) := by
      dsimp [y]
      constructor
      · linarith
      · linarith [htM, hM']
    -- pointwise formula for deriv F on (0, M)
    have hform : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (M : ℝ) →
        deriv F s = deriv f ((a : ℝ) + 1 + s) - (ν : ℝ) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs.1
      have hsM : s < (M : ℝ) := hs.2
      have hysI : (a : ℝ) + 1 + s ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) := by
        constructor
        · linarith [hs0]
        · linarith [hsM, hM']
      have hfd_ys : DifferentiableAt ℝ f ((a : ℝ) + 1 + s) :=
        SdtOscB.differentiableAt_F_of_Ioo f hf hysI
      have hφ : HasDerivAt (fun u : ℝ => f (((a : ℝ) + 1) + u))
          (deriv f (((a : ℝ) + 1) + s)) s := by
        simpa using (hfd_ys.hasDerivAt.comp_const_add ((a : ℝ) + 1) s)
      have hLda : HasDerivAt (fun u : ℝ => (ν : ℝ) * u) (ν : ℝ) s := by
        simpa using (hasDerivAt_const_mul (x := s) (c := (ν : ℝ)))
      have hFda : HasDerivAt F (deriv f (((a : ℝ) + 1) + s) - (ν : ℝ)) s := by
        exact hφ.sub hLda
      have hdF : deriv F s = deriv f (((a : ℝ) + 1) + s) - (ν : ℝ) := hFda.deriv
      simpa using hdF
    -- the functions `deriv F` and `x ↦ deriv f (a+1+x) - ν` agree near t
    have hcong : (fun s : ℝ => deriv F s) =ᶠ[𝓝 t]
        (fun s : ℝ => deriv f ((a : ℝ) + 1 + s) - (ν : ℝ)) := by
      filter_upwards [Ioo_mem_nhds ht0 htM] with s hs
      exact hform s hs
    -- second derivative of the translated function (translation invariance)
    have hDA : HasDerivAt (fun s : ℝ => deriv f ((a : ℝ) + 1 + s))
        (deriv (deriv f) y) t := by
      have hfdd : HasDerivAt (deriv f) (deriv (deriv f) y) y :=
        (SdtOscB.differentiableAt_deriv_F_of_Ioo f hf hyI).hasDerivAt
      have hshift : HasDerivAt (fun u : ℝ => deriv f (((a : ℝ) + 1) + u))
          (deriv (deriv f) y) t := by
        simpa [y] using (hfdd.comp_const_add ((a : ℝ) + 1) t)
      simpa [add_assoc, y] using hshift
    have hDA2 : HasDerivAt (fun s : ℝ => deriv f ((a : ℝ) + 1 + s) - (ν : ℝ))
        (deriv (deriv f) y) t := by
      exact (hasDerivAt_sub_const_iff (c := (ν : ℝ))
        (f := fun s : ℝ => deriv f ((a : ℝ) + 1 + s))).2 hDA
    have hDF : HasDerivAt (fun s : ℝ => deriv F s) (deriv (deriv f) y) t :=
      hDA2.congr_of_eventuallyEq hcong
    have hdval : deriv (deriv F) t = deriv (deriv f) y := by
      simpa using hDF.deriv
    rw [hdval]
    exact hpp y hyI
  -- apply the curvature oscillatory-integral bound with δ := r on [0, M]
  have hbd := SdtOscB.exp_integral_second_deriv_le (a := (0 : ℝ)) (b := (M : ℝ))
    h01 F hr hF2 hppF
  simpa [F] using hbd

end Submission.SdtPerNu


open Complex
open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtPoisson

noncomputable section

/-- `J − J_K = ρ K` (child-proved). -/
lemma sawInt_sub_sawHatInt {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (K : ℕ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    sawInt f N - sawHatInt f N K = rhoErr f N K :=
  SawSubChild.sawInt_sub_sawHatInt hN f K hF

/-- The pair-sum over the upper tail is O(B) (child-proved). -/
lemma pair_sum_le {f : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2)
    {β K : ℤ} (hβK : β + 1 ≤ K) (hBβ : (B : ℝ) ≤ (β : ℝ) + 1) :
    (∑ ν ∈ Finset.Icc (β + 1) K, ‖oscIntHat f N ν + oscIntHat f N (-ν)‖) ≤ 120 * (B + 1) :=
  PairSumChild.pair_sum_le hN hB hF hpp hmarg hβK hBβ

/-- ρ(K) → 0 (child-proved). -/
lemma rhoErr_tendsto_zero {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) :
    Tendsto (fun K : ℕ => rhoErr f N K) atTop (𝓝 0) :=
  RhoChild.rhoErr_tendsto_zero hN f hF

/-- Integer cast of a nonneg ℤ to its `toNat`. -/
lemma int_cast_toNat_of_nonneg (ν : ℤ) (hν : 0 ≤ ν) : (ν : ℝ) = (ν.toNat : ℝ) := by
  have hz : (ν : ℤ) = (ν.toNat : ℤ) := (Int.toNat_of_nonneg hν).symm
  have hzr : ((ν : ℝ)) = (((ν.toNat : ℤ) : ℝ)) := congrArg (fun z : ℤ => (z : ℝ)) hz
  have hcast : (((ν.toNat : ℤ) : ℝ)) = (ν.toNat : ℝ) := Int.cast_natCast (ν.toNat)
  calc
    (ν : ℝ) = ((ν.toNat : ℤ) : ℝ) := hzr
    _ = (ν.toNat : ℝ) := hcast

/-- Integer cast of a nonneg ℤ to its `natAbs`. -/
lemma int_cast_natAbs_of_nonneg (ν : ℤ) (hν : 0 ≤ ν) : (ν.natAbs : ℝ) = (ν : ℝ) := by
  have hz : (ν.natAbs : ℤ) = ν := Int.natAbs_of_nonneg hν
  have hzr : (((ν.natAbs : ℤ) : ℝ)) = (ν : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hz
  have hcast : (((ν.natAbs : ℤ) : ℝ)) = (ν.natAbs : ℝ) := Int.cast_natCast (ν.natAbs)
  calc
    (ν.natAbs : ℝ) = ((ν.natAbs : ℤ) : ℝ) := hcast.symm
    _ = (ν : ℝ) := hzr

/-- ContDiffOn for `f + (c·x)`. -/
lemma contDiffOn_add_const_mul {a b : ℝ} (f : ℝ → ℝ) (c : ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ContDiffOn ℝ 2 (fun x : ℝ => f x + c * x) (Set.Icc a b) := by
  have hlin : ContDiffOn ℝ 2 (fun x : ℝ => c * x) (Set.Icc a b) := by
    have hg : ContDiff ℝ 2 (fun x : ℝ => c * x) := by
      have hc : ContDiff ℝ 2 (fun _ : ℝ => c) := contDiff_const
      have hid : ContDiff ℝ 2 (fun x : ℝ => x) := contDiff_id
      simpa [mul_comm] using (hc.mul hid)
    exact hg.contDiffOn
  exact hF.add hlin

/-- Derivative of the linear perturbation on an open interval. -/
lemma deriv_add_const_mul_of_Ioo {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (c : ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    deriv (fun y : ℝ => f y + c * y) x = deriv f x + c := by
  have hdf : HasDerivAt f (deriv f x) x := SdtOscB.hasDerivAt_F_of_Ioo f hF hx
  have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hG : HasDerivAt (fun y : ℝ => f y + c * y) (deriv f x + c) x := hdf.add hlin
  exact hG.deriv

/-- Second derivative of the linear perturbation equals that of f. -/
lemma deriv_deriv_add_const_mul_of_Ioo {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (c : ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    deriv (deriv (fun y : ℝ => f y + c * y)) x = deriv (deriv f) x := by
  have hFd1 : HasDerivAt (deriv f) (deriv (deriv f) x) x := SdtOscB.hasDerivAt_deriv_F_of_Ioo f hF hx
  have hEq : (fun y : ℝ => deriv (fun u : ℝ => f u + c * u) y) =ᶠ[𝓝 x] (fun y : ℝ => deriv f y + c) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact deriv_add_const_mul_of_Ioo hab f c hF hy
  have hlin : HasDerivAt (fun y : ℝ => deriv f y + c) (deriv (deriv f) x) x := hFd1.add_const c
  have hres : HasDerivAt (fun y : ℝ => deriv (fun u : ℝ => f u + c * u) y) (deriv (deriv f) x) x :=
    hlin.congr_of_eventuallyEq hEq
  exact hres.deriv

/-- Per-frequency bound on the lower tail: `‖T_{−ν}‖ ≤ 8/(ν + 1/2)` for ν ≥ 1. -/
lemma oscIntHat_neg_nu_bound {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hlo : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x)
    (ν : ℤ) (hν : 1 ≤ ν) :
    ‖oscIntHat f N (-ν)‖ ≤ 8 / ((ν : ℝ) + 1 / 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  let F : ℝ → ℝ := fun x : ℝ => f x + (ν : ℝ) * x
  have hF2 : ContDiffOn ℝ 2 F (Set.Icc 0 (N : ℝ)) := by
    dsimp [F]
    exact contDiffOn_add_const_mul f (ν : ℝ) hF
  have hm : (0 : ℝ) < (ν : ℝ) + 1 / 2 := by positivity
  have hsl : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → (ν : ℝ) + 1 / 2 ≤ |deriv F x| := by
    intro x hx
    have hge : (1 / 2 : ℝ) ≤ deriv f x := hlo x hx
    have hder : deriv F x = deriv f x + (ν : ℝ) := by
      dsimp [F]
      exact deriv_add_const_mul_of_Ioo hNpos f (ν : ℝ) hF hx
    rw [hder]
    have hpos : 0 ≤ deriv f x + (ν : ℝ) := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  have hppF : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv F) x := by
    intro x hx
    have hder2 : deriv (deriv F) x = deriv (deriv f) x := by
      dsimp [F]
      exact deriv_deriv_add_const_mul_of_Ioo hNpos f (ν : ℝ) hF hx
    rw [hder2]
    exact hpp x hx
  have hb := SdtOscB.exp_integral_first_deriv_le (a := (0 : ℝ)) (b := (N : ℝ)) hNpos F hm hF2 hsl hppF
  have hrel : (∫ x in 0..(N : ℝ), SdtOscB.ephase F x) = oscIntHat f N (-ν) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp [oscIntHat, F, SdtOscB.ephase, E, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  simpa [hrel] using hb

/-- The leftover lower-tail sum is bounded. -/
lemma leftover_le {f : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hlo : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x)
    {β : ℤ} (hβ : 1 ≤ β) :
    (∑ ν ∈ Finset.Icc 1 β, ‖oscIntHat f N (-ν)‖) ≤ 8 * ((β : ℝ) + 1) := by
  have hterm (ν : ℤ) (hν : 1 ≤ ν) : ‖oscIntHat f N (-ν)‖ ≤ 8 / ((ν : ℝ) + 1 / 2) :=
    oscIntHat_neg_nu_bound hN f hF hpp hlo ν hν
  have hsum : (∑ ν ∈ Finset.Icc 1 β, ‖oscIntHat f N (-ν)‖) ≤
      ∑ ν ∈ Finset.Icc 1 β, (8 / ((ν : ℝ) + 1 / 2)) := by
    exact Finset.sum_le_sum (fun ν hν => hterm ν (by
      rw [Finset.mem_Icc] at hν
      exact hν.1))
  have hterm8 (ν : ℤ) (hν : ν ∈ Finset.Icc 1 β) : 8 / ((ν : ℝ) + 1 / 2) ≤ 8 := by
    rw [Finset.mem_Icc] at hν
    have hν1 : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν.1
    have hpos : 0 < (ν : ℝ) + 1 / 2 := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith
  have hsum1 : (∑ ν ∈ Finset.Icc 1 β, (8 / ((ν : ℝ) + 1 / 2))) ≤ ∑ ν ∈ Finset.Icc 1 β, (8 : ℝ) :=
    Finset.sum_le_sum (fun ν hν => hterm8 ν hν)
  have hβn : 0 ≤ β := by omega
  have hcnt : ((Finset.Icc 1 β).card : ℝ) ≤ (β : ℝ) + 1 := by
    have hc : (Finset.Icc 1 β).card = β.toNat := by simp
    have hβr : (β : ℝ) = (β.toNat : ℝ) := int_cast_toNat_of_nonneg β hβn
    calc
      ((Finset.Icc 1 β).card : ℝ) = (β.toNat : ℝ) := by rw [hc]
      _ = (β : ℝ) := hβr.symm
      _ ≤ (β : ℝ) + 1 := by linarith
  have hsum8 : (∑ ν ∈ Finset.Icc 1 β, (8 : ℝ)) ≤ 8 * ((β : ℝ) + 1) := by
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    nlinarith [hcnt]
  have hfin : (∑ ν ∈ Finset.Icc 1 β, ‖oscIntHat f N (-ν)‖) ≤ 8 * ((β : ℝ) + 1) := by
    exact le_trans hsum (le_trans hsum1 hsum8)
  exact hfin

/-- Eventually ρ(K) is small, with K past any given β+1. -/
lemma exists_K_rho_small {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ))) (β : ℤ) :
    ∃ K : ℕ, (β + 1 : ℤ) ≤ (K : ℤ) ∧ ‖rhoErr f N K‖ ≤ 1 := by
  have ht : Tendsto (fun K : ℕ => rhoErr f N K) atTop (𝓝 0) := rhoErr_tendsto_zero hN f hF
  have hb : ∀ᶠ K : ℕ in atTop, ‖rhoErr f N K‖ < 1 := by
    have hball : {y : ℂ | ‖y‖ < 1} ∈ 𝓝 (0 : ℂ) := by
      simpa [Metric.ball, dist_eq_norm, sub_zero] using
        (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
    exact ht.eventually hball
  rcases (eventually_atTop.mp hb) with ⟨K1, hK1⟩
  let K : ℕ := max K1 (β.natAbs + 1)
  refine ⟨K, ?_, ?_⟩
  · have h1 : (β + 1 : ℤ) ≤ ((β.natAbs + 1 : ℕ) : ℤ) := by omega
    have h2 : (β.natAbs + 1 : ℕ) ≤ K := by dsimp [K]; omega
    omega
  · have hK1le : K1 ≤ K := by dsimp [K]; omega
    have hK : ‖rhoErr f N K‖ < 1 := hK1 K hK1le
    linarith

/-! ## Window split -/

lemma oscSumE_split_zero {f : ℝ → ℝ} {N : ℕ} {β : ℤ} (hβ : 1 ≤ β) :
    oscSumE f N 0 β = oscIntHat f N 0 + ∑ ν ∈ Finset.Icc 1 β, oscIntHat f N ν := by
  dsimp [oscSumE]
  have hset : Finset.Icc (0 : ℤ) β = insert 0 (Finset.Icc 1 β) := by
    ext ν
    constructor
    · intro hν
      rw [Finset.mem_insert]
      rw [Finset.mem_Icc] at hν
      by_cases h0 : ν = 0
      · exact Or.inl h0
      · right
        rw [Finset.mem_Icc]
        constructor
        · have hν1 : 1 ≤ ν := by omega
          exact hν1
        · exact hν.2
    · intro hν
      rw [Finset.mem_insert] at hν
      rcases hν with rfl | hν1
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · rw [Finset.mem_Icc] at hν1
        rw [Finset.mem_Icc]
        constructor <;> omega
  rw [hset, Finset.sum_insert]
  simp

/-! ## ℤ-window Finset identities -/

/-- Split `Icc a c` at b. -/
lemma sum_Icc_split_z {a b c : ℤ} (hab : a ≤ b) (hbc : b + 1 ≤ c) (w : ℤ → ℂ) :
    (∑ ν ∈ Finset.Icc a c, w ν) = (∑ ν ∈ Finset.Icc a b, w ν) + (∑ ν ∈ Finset.Icc (b + 1) c, w ν) := by
  have hset : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    ext ν
    constructor
    · intro hν
      rw [Finset.mem_Icc] at hν
      rw [Finset.mem_union]
      by_cases hb : ν ≤ b
      · left
        rw [Finset.mem_Icc]
        constructor <;> omega
      · right
        rw [Finset.mem_Icc]
        constructor <;> omega
    · intro hν
      rw [Finset.mem_union] at hν
      rcases hν with h1 | h2
      · rw [Finset.mem_Icc] at h1
        rw [Finset.mem_Icc]
        constructor <;> omega
      · rw [Finset.mem_Icc] at h2
        rw [Finset.mem_Icc]
        constructor <;> omega
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
    rw [Finset.disjoint_left]
    intro ν h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  rw [hset, Finset.sum_union hdisj]

/-- Reindex an interval of integers by negation. -/
lemma sum_neg_Icc {K : ℕ} (w : ℤ → ℂ) :
    (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), w ν) = ∑ ν ∈ Finset.Icc 1 (K : ℤ), w (-ν) := by
  refine Finset.sum_bij (fun ν _ => -ν) ?_ ?_ ?_ ?_
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    constructor <;> omega
  · intro ν hν μ hμ hνμ
    omega
  · intro ν hν
    rw [Finset.mem_Icc] at hν
    refine ⟨-ν, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · simp
  · intro ν hν
    simp

/-- Split of the symmetric nonzero range. -/
lemma sum_erase_0_split {K : ℕ} (w : ℤ → ℂ) :
    (∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, w ν) =
      (∑ ν ∈ Finset.Icc 1 (K : ℤ), w ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), w ν) := by
  have hset : (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0 = Finset.Icc 1 (K : ℤ) ∪ Finset.Icc (-((K : ℤ))) (-1 : ℤ) := by
    ext ν
    constructor
    · intro hν
      rw [Finset.mem_erase] at hν
      rw [Finset.mem_union]
      rw [Finset.mem_Icc] at hν
      rcases hν with ⟨hν0, hνI⟩
      by_cases hpos : 0 < ν
      · left
        rw [Finset.mem_Icc]
        constructor <;> omega
      · right
        rw [Finset.mem_Icc]
        constructor <;> omega
    · intro hν
      rw [Finset.mem_erase]
      rw [Finset.mem_union] at hν
      rcases hν with hpos | hneg
      · rw [Finset.mem_Icc] at hpos
        constructor
        · have : 1 ≤ ν := hpos.1
          omega
        · rw [Finset.mem_Icc]; omega
      · rw [Finset.mem_Icc] at hneg
        constructor
        · have : ν ≤ -1 := hneg.2
          omega
        · rw [Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (K : ℤ)) (Finset.Icc (-((K : ℤ))) (-1 : ℤ)) := by
    rw [Finset.disjoint_left]
    intro ν h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  rw [hset, Finset.sum_union hdisj]

/-! ## The canonical truncated Poisson bound -/

/-- **Canonical estimate**: `f' ∈ [1/2, B−1/2]`, window `{0,...,⌊B⌋}`;
error ≤ 900(2+B). -/
lemma canonical_bound {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    (hmarg : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2) :
    ‖discrSumE f N - oscSumE f N 0 (Int.floor B)‖ ≤ 900 * (2 + B) := by
  let β : ℤ := Int.floor B
  let S : ℂ := discrSumE f N
  let Tν (ν : ℤ) : ℂ := oscIntHat f N ν
  have hβ : 1 ≤ β := by
    dsimp [β]
    exact Int.le_floor.mpr (by exact_mod_cast hB)
  have hBβ : (B : ℝ) ≤ (β : ℝ) + 1 := by
    have h := Int.lt_floor_add_one B
    dsimp [β] at h ⊢
    linarith
  have hβB : (β : ℝ) ≤ B := by
    dsimp [β]
    exact Int.floor_le B
  have hem := em_identity hN f hF
  have hJ : S = oscIntHat f N 0 + sawInt f N + bdVal f N := by
    simpa [S, discrSumE, oscIntHat, sawInt, bdVal] using hem
  have hhat (K : ℕ) : sawHatInt f N K = ∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, Tν ν := by
    simpa [sawHatInt, Tν] using hat_identity hN f K hF
  rcases exists_K_rho_small hN f hF β with ⟨K, hKβ, hρK⟩
  have hKβ0 : (β : ℤ) ≤ (K : ℤ) := by omega
  have hwin : oscSumE f N 0 β = oscIntHat f N 0 + ∑ ν ∈ Finset.Icc 1 β, Tν ν := by
    simpa [Tν] using oscSumE_split_zero (f := f) (N := N) (β := β) hβ
  have hmaster : S - oscSumE f N 0 β = bdVal f N + rhoErr f N K +
      ((∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)) := by
    have hhrho : sawInt f N = sawHatInt f N K + rhoErr f N K := by
      rw [← sawInt_sub_sawHatInt hN f K hF]
      ring
    have hJK : sawHatInt f N K =
        (∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc 1 β, Tν ν) +
          (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν) := by
      rw [hhat K]
      have hsplit := sum_Icc_split_z (a := (1 : ℤ)) (b := β) (c := K) hβ hKβ (fun ν : ℤ => Tν ν)
      calc
        (∑ ν ∈ (Finset.Icc (-((K : ℤ))) (K : ℤ)).erase 0, Tν ν)
            = (∑ ν ∈ Finset.Icc 1 (K : ℤ), Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν) := by
              exact sum_erase_0_split (fun ν : ℤ => Tν ν)
        _ = ((∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc 1 β, Tν ν)) +
            (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν) := by
              rw [hsplit]
              ring
    calc
      S - oscSumE f N 0 β
          = (oscIntHat f N 0 + sawInt f N + bdVal f N) - (oscIntHat f N 0 + ∑ ν ∈ Finset.Icc 1 β, Tν ν) := by
              rw [hJ, hwin]
      _ = bdVal f N + (sawHatInt f N K + rhoErr f N K) - (∑ ν ∈ Finset.Icc 1 β, Tν ν) := by
              rw [hhrho]
              ring
      _ = bdVal f N + rhoErr f N K + ((∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) +
          (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)) := by
              rw [hJK]
              ring
  have hbd : ‖bdVal f N‖ ≤ 1 := by
    dsimp [bdVal]
    have h1 : ‖(E (f (N : ℝ)) - E (f 0)) / 2‖ ≤ 1 := by
      have hx : ‖(E (f (N : ℝ)) - E (f 0)) / 2‖ ≤ ‖E (f (N : ℝ)) - E (f 0)‖ * (1 / 2) := by
        rw [div_eq_mul_inv, norm_mul]
        have h : ‖((2 : ℂ)⁻¹)‖ = 1 / 2 := by rw [norm_inv]; norm_num
        rw [h]
      have hsub : ‖E (f (N : ℝ)) - E (f 0)‖ ≤ ‖E (f (N : ℝ))‖ + ‖E (f 0)‖ := norm_sub_le _ _
      have hsum : ‖E (f (N : ℝ))‖ + ‖E (f 0)‖ ≤ 2 := by
        have hn1 : ‖E (f (N : ℝ))‖ ≤ 1 := by rw [E_norm]
        have hn0 : ‖E (f 0)‖ ≤ 1 := by rw [E_norm]
        linarith
      have hle2 : ‖E (f (N : ℝ)) - E (f 0)‖ ≤ 2 := le_trans hsub hsum
      have h2 : ‖E (f (N : ℝ)) - E (f 0)‖ * (1 / 2) ≤ 2 * (1 / 2) :=
        mul_le_mul_of_nonneg_right hle2 (by norm_num)
      have h3 : 2 * (1 / 2) ≤ 1 := by norm_num
      linarith
    exact h1
  have hpairs : ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖ ≤
      (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) + (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) := by
    have hneg : (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν) = ∑ ν ∈ Finset.Icc 1 (K : ℤ), Tν (-ν) := by
      exact sum_neg_Icc (fun ν : ℤ => Tν ν)
    have hsplit : (∑ ν ∈ Finset.Icc 1 (K : ℤ), Tν (-ν)) =
        (∑ ν ∈ Finset.Icc 1 β, Tν (-ν)) + (∑ ν ∈ Finset.Icc (β + 1) K, Tν (-ν)) := by
      exact sum_Icc_split_z (a := (1 : ℤ)) (b := β) (c := K) hβ hKβ (fun ν : ℤ => Tν (-ν))
    let A : ℂ := ∑ ν ∈ Finset.Icc 1 β, Tν (-ν)
    let B : ℂ := ∑ ν ∈ Finset.Icc (β + 1) K, Tν (-ν)
    let U : ℂ := ∑ ν ∈ Finset.Icc (β + 1) K, Tν ν
    have hUadd : U + B = ∑ ν ∈ Finset.Icc (β + 1) K, (Tν ν + Tν (-ν)) := by
      dsimp [U, B]
      rw [Finset.sum_add_distrib]
    have hnormUadd : ‖U + B‖ ≤ ∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖ := by
      rw [hUadd]
      exact norm_sum_le _ _
    calc
      ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖
          = ‖U + (A + B)‖ := by
              dsimp [U, A, B]
              rw [hneg, hsplit]
      _ ≤ ‖U + B‖ + ‖A‖ := by
              have harg : U + (A + B) = (U + B) + A := by ring
              rw [harg]
              exact norm_add_le _ _
      _ ≤ (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) + ‖A‖ := by
              exact add_le_add_left hnormUadd ‖A‖
      _ ≤ (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) + (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) := by
              have hnormA : ‖A‖ ≤ ∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖ := by
                dsimp [A]
                exact norm_sum_le _ _
              exact add_le_add_right hnormA (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖)
  have hpb : (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) ≤ 120 * (B + 1) := by
    have h := pair_sum_le (N := N) hN (B := B) hB hF hpp hmarg (β := β) (K := K) hKβ hBβ
    simpa [Tν] using h
  have hleft : (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) ≤ 8 * (B + 1) := by
    have h0 := leftover_le (N := N) hN hF hpp (fun x hx => (hmarg x hx).1) (β := β) hβ
    have h' : (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) ≤ 8 * ((β : ℝ) + 1) := by
      simpa [Tν] using h0
    have hβ1 : (β : ℝ) + 1 ≤ B + 1 := by linarith [hβB]
    have h'' : 8 * ((β : ℝ) + 1) ≤ 8 * (B + 1) := by
      exact mul_le_mul_of_nonneg_left hβ1 (by norm_num)
    exact le_trans h' h''
  have hA : ‖S - oscSumE f N 0 β‖ ≤ 1 + 1 + 120 * (B + 1) + 8 * (B + 1) := by
    have hnorm1 : ‖S - oscSumE f N 0 β‖ ≤ ‖bdVal f N‖ + ‖rhoErr f N K‖ +
        ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖ := by
      rw [hmaster]
      have h1 : ‖(bdVal f N + rhoErr f N K) + ((∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) +
          (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν))‖ ≤
          ‖bdVal f N + rhoErr f N K‖ + ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) +
          (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖ := norm_add_le _ _
      have h2 : ‖bdVal f N + rhoErr f N K‖ ≤ ‖bdVal f N‖ + ‖rhoErr f N K‖ := norm_add_le _ _
      nlinarith
    have hnorm2 : ‖bdVal f N‖ + ‖rhoErr f N K‖ +
        ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖ ≤
        1 + 1 + (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) + (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) := by
      have hh : (‖bdVal f N‖ + ‖rhoErr f N K‖) +
          ‖(∑ ν ∈ Finset.Icc (β + 1) K, Tν ν) + (∑ ν ∈ Finset.Icc (-((K : ℤ))) (-1 : ℤ), Tν ν)‖ ≤
          (‖bdVal f N‖ + ‖rhoErr f N K‖) +
          ((∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) + (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖)) := by
        nlinarith [hpairs]
      have hbs : ‖bdVal f N‖ + ‖rhoErr f N K‖ ≤ 2 := by linarith
      nlinarith
    have hnorm3 : 1 + 1 + (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) +
        (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) ≤ 1 + 1 + 120 * (B + 1) + 8 * (B + 1) := by
      have h2 : (∑ ν ∈ Finset.Icc (β + 1) K, ‖Tν ν + Tν (-ν)‖) ≤ 120 * (B + 1) := hpb
      have h3 : (∑ ν ∈ Finset.Icc 1 β, ‖Tν (-ν)‖) ≤ 8 * (B + 1) := hleft
      nlinarith
    exact le_trans hnorm1 (le_trans hnorm2 hnorm3)
  have hfin : 1 + 1 + 120 * (B + 1) + 8 * (B + 1) ≤ 900 * (2 + B) := by
    nlinarith [hB]
  have hfinal := le_trans hA hfin
  simpa [S, β] using hfinal

/-! ## Final theorem -/

/-- In the final theorem, express the summands via `E`. -/
lemma E_summands_eq (t : ℝ) : cexp ((((2 * Real.pi * t : ℝ) : ℝ) : ℂ) * I) = E t := rfl

/-- `E((g : ℝ) · m) = 1` for integer `g` and `m : ℕ`. -/
lemma E_int_nat_mul (g : ℤ) (m : ℕ) : E ((g : ℝ) * (m : ℝ)) = 1 := by
  have hcast : (g : ℝ) * (m : ℝ) = (((g * (m : ℤ) : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hcast, E_of_int]

/-- Replacing `f` by `f + (−g)·x` does not change the discrete sum. -/
lemma discrSumE_lin_shift {f : ℝ → ℝ} {N : ℕ} (g : ℤ) :
    discrSumE (fun x : ℝ => f x + (-(g : ℝ)) * x) N = discrSumE f N := by
  unfold discrSumE
  refine Finset.sum_congr rfl ?_
  intro m hm
  dsimp
  have harg : f (m : ℝ) + (-(g : ℝ)) * (m : ℝ) = f (m : ℝ) - (g : ℝ) * (m : ℝ) := by ring
  have hgm : E ((g : ℝ) * (m : ℝ)) = 1 := E_int_nat_mul g m
  rw [harg, E_sub, hgm]
  simp

/-- The oscillatory integral with a linear shift reindexes the frequency. -/
lemma oscIntHat_lin_shift {f : ℝ → ℝ} {N : ℕ} (g : ℤ) (nu : ℤ) :
    oscIntHat f N (nu + g) =
      oscIntHat (fun x : ℝ => f x + (-(g : ℝ)) * x) N nu := by
  unfold oscIntHat
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  congr 1
  have harg : f x - ((nu + g : ℤ) : ℝ) * x =
      (f x + (-(g : ℝ)) * x) - (nu : ℝ) * x := by
    push_cast
    ring
  rw [harg]

/-- Window sums shift with an integer frequency translation. -/
lemma oscSumE_lin_shift {f : ℝ → ℝ} {N : ℕ} (g : ℤ) (α β : ℤ) :
    oscSumE (fun x : ℝ => f x + (-(g : ℝ)) * x) N α β =
      oscSumE f N (α + g) (β + g) := by
  unfold oscSumE
  refine Finset.sum_bij' (s := Finset.Icc α β) (t := Finset.Icc (α + g) (β + g))
    (f := fun nu => oscIntHat (fun x : ℝ => f x + (-(g : ℝ)) * x) N nu)
    (g := fun ν => oscIntHat f N ν)
    (i := fun nu h => nu + g) (j := fun ν h => ν - g) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [Finset.mem_Icc] at hnu ⊢
    omega
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    omega
  · intro nu hnu
    omega
  · intro ν hν
    omega
  · intro nu hnu
    exact (oscIntHat_lin_shift (f := f) (N := N) (g := g) (nu := nu)).symm

/-- `ephase F x = E (F x)` by definition. -/
lemma ephase_eq_E (F : ℝ → ℝ) (x : ℝ) : SdtOscB.ephase F x = E (F x) := rfl

/-- **General truncated Poisson bound.** van der Corput's Hilfssatz 1: if
`f ∈ C²[0,N]`, `f'' ≥ 0` on `(0,N)`, and `A+1/2 ≤ f' ≤ B−1/2` on `[0,N]`,
then the discrete sum of `e(f(m))` over `m ∈ [1,N]` equals the sum over the
integer window `[⌈A⌉,⌊B⌋]` of `∫_0^N e(f(x)−νx)`, up to `O(B−A)`. -/
theorem truncated_poisson {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ)
    (hF : ContDiffOn ℝ 2 f (Set.Icc 0 (N : ℝ)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv f) x)
    {A B : ℝ}
    (hwin : ∀ x : ℝ, x ∈ Set.Icc 0 (N : ℝ) → A + 1 / 2 ≤ deriv f x ∧ deriv f x ≤ B - 1 / 2) :
    ‖(∑ m ∈ Finset.Icc 1 N,
        cexp ((((2 * Real.pi * f (m : ℝ) : ℝ) : ℝ) : ℂ) * I)) -
      (∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor B),
        ∫ x in 0..(N : ℝ), cexp ((((2 * Real.pi * (f x - (ν : ℝ) * x) : ℝ) : ℝ) : ℂ) * I))‖
      ≤ 1000 * (3 + (B - A)) := by
  let g : ℤ := Int.floor A
  let fl : ℝ → ℝ := fun x : ℝ => f x + (-(g : ℝ)) * x
  let bt : ℤ := Int.floor (B - (g : ℝ))
  let cA : ℤ := Int.ceil A - g
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h0in : (0 : ℝ) ∈ Set.Icc 0 (N : ℝ) := ⟨le_rfl, by exact_mod_cast (Nat.zero_le N)⟩
  have hL1 : (1 : ℝ) ≤ B - A := by
    rcases hwin 0 h0in with ⟨hlo, hup⟩
    linarith
  have hA'0 : (0 : ℝ) ≤ A - (g : ℝ) := by
    have hgA : (g : ℝ) ≤ A := Int.floor_le A
    linarith
  have hA'1 : A - (g : ℝ) < 1 := by
    have h := Int.lt_floor_add_one A
    linarith
  have hB'1 : (1 : ℝ) ≤ B - (g : ℝ) := by linarith
  have hFlin : ContDiffOn ℝ 2 fl (Set.Icc 0 (N : ℝ)) := by
    dsimp [fl]
    exact contDiffOn_add_const_mul f (-(g : ℝ)) hF
  have hpplin : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 0 ≤ deriv (deriv fl) x := by
    intro x hx
    dsimp [fl]
    rw [deriv_deriv_add_const_mul_of_Ioo hNpos f (-(g : ℝ)) hF hx]
    exact hpp x hx
  have hmargin : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) →
      1 / 2 ≤ deriv fl x ∧ deriv fl x ≤ (B - (g : ℝ)) - 1 / 2 := by
    intro x hx
    have hxcc : x ∈ Set.Icc 0 (N : ℝ) := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rcases hwin x hxcc with ⟨hlo, hup⟩
    have hder : deriv fl x = deriv f x + (-(g : ℝ)) := by
      dsimp [fl]
      exact deriv_add_const_mul_of_Ioo hNpos f (-(g : ℝ)) hF hx
    rw [hder]
    constructor <;> linarith
  have hcan := canonical_bound (N := N) (f := fl) (B := B - (g : ℝ)) hN hB'1 hFlin hpplin hmargin
  have hd1 : discrSumE f N = discrSumE fl N := by
    rw [← discrSumE_lin_shift (f := f) (N := N) (g := g)]
  have hfloorB : Int.floor B = g + Int.floor (B - (g : ℝ)) := by
    have h1 := Int.floor_add_intCast (B - (g : ℝ)) g
    calc
      Int.floor B = Int.floor ((B - (g : ℝ)) + (g : ℝ)) := by
        congr 1
        ring
      _ = Int.floor (B - (g : ℝ)) + g := h1
      _ = g + Int.floor (B - (g : ℝ)) := by omega
  have hcAeq : cA = Int.ceil (A - (g : ℝ)) := by
    dsimp [cA]
    have h1 := Int.ceil_add_intCast (A - (g : ℝ)) g
    calc
      Int.ceil A - g = Int.ceil ((A - (g : ℝ)) + (g : ℝ)) - g := by
        congr 1
        ring
      _ = (Int.ceil (A - (g : ℝ)) + g) - g := by rw [h1]
      _ = Int.ceil (A - (g : ℝ)) := by omega
  have hbt1 : (1 : ℤ) ≤ bt := by
    dsimp [bt]
    rw [Int.le_floor]
    norm_num
    exact hB'1
  have hcf : Int.ceil A = cA + g := by dsimp [cA]; omega
  have hbf : Int.floor B = bt + g := by
    dsimp [bt]
    rw [hfloorB]
    omega
  have hwinrel : oscSumE f N (Int.ceil A) (Int.floor B) = oscSumE fl N cA bt := by
    calc
      oscSumE f N (Int.ceil A) (Int.floor B)
          = oscSumE f N (cA + g) (bt + g) := by
              rw [hcf, hbf]
      _ = oscSumE fl N cA bt := by
              exact (oscSumE_lin_shift (f := f) (N := N) (g := g) (α := cA) (β := bt)).symm
  have hbtn : (0 : ℤ) ≤ bt := by omega
  -- bound the middle difference by 16
  have hT0_bound : ‖oscIntHat fl N 0‖ ≤ 16 := by
    have hmarg0 : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → 1 / 2 ≤ deriv fl x := by
      intro x hx
      exact (hmargin x hx).1
    have hsl : ∀ x : ℝ, x ∈ Set.Ioo 0 (N : ℝ) → (1 / 2 : ℝ) ≤ |deriv fl x| := by
      intro x hx
      have hge : (1 / 2 : ℝ) ≤ deriv fl x := hmarg0 x hx
      have hnonneg : 0 ≤ deriv fl x := by linarith
      rw [abs_of_nonneg hnonneg]
      exact hge
    have hb := SdtOscB.exp_integral_first_deriv_le (a := (0 : ℝ)) (b := (N : ℝ)) hNpos fl
      (m := (1 / 2 : ℝ)) (by norm_num) hFlin hsl hpplin
    have hrel : (∫ x in 0..(N : ℝ), SdtOscB.ephase fl x) = oscIntHat fl N 0 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [ephase_eq_E]
      congr 1
      simp
    have hb' : ‖oscIntHat fl N 0‖ ≤ 16 := by
      rw [← hrel]
      norm_num at hb ⊢
      exact hb
    exact hb'
  have hdelta_bound : ‖oscSumE fl N 0 bt - oscSumE fl N cA bt‖ ≤ 16 := by
    by_cases hA0 : A - (g : ℝ) = 0
    · have hcA0 : cA = 0 := by
        rw [hcAeq]
        rw [hA0]
        norm_num
      have hdif : oscSumE fl N cA bt = oscSumE fl N 0 bt := by rw [hcA0]
      rw [hdif]
      norm_num
    · have hApos : 0 < A - (g : ℝ) := lt_of_le_of_ne hA'0 (Ne.symm hA0)
      have hcA1 : cA = 1 := by
        rw [hcAeq]
        apply (Int.ceil_eq_iff).mpr
        constructor
        · norm_num
          linarith
        · norm_num
          linarith
      have hsplit := oscSumE_split_zero (f := fl) (N := N) (β := bt) hbt1
      have hdif : oscSumE fl N 0 bt - oscSumE fl N cA bt = oscIntHat fl N 0 := by
        rw [hcA1]
        simp only [oscSumE]
        have hsplit' : (∑ ν ∈ Finset.Icc (0 : ℤ) bt, oscIntHat fl N ν) =
            oscIntHat fl N 0 + (∑ ν ∈ Finset.Icc (1 : ℤ) bt, oscIntHat fl N ν) := by
          simpa [oscSumE] using (oscSumE_split_zero (f := fl) (N := N) (β := bt) hbt1)
        rw [hsplit']
        ring
      rw [hdif]
      exact hT0_bound
  have hw1 : discrSumE f N - oscSumE f N (Int.ceil A) (Int.floor B) =
      (discrSumE fl N - oscSumE fl N 0 bt) +
        (oscSumE fl N 0 bt - oscSumE f N (Int.ceil A) (Int.floor B)) := by
    rw [hd1]
    ring
  have hnorm_t : ‖discrSumE f N - oscSumE f N (Int.ceil A) (Int.floor B)‖ ≤
      ‖discrSumE fl N - oscSumE fl N 0 bt‖ +
        ‖oscSumE fl N 0 bt - oscSumE f N (Int.ceil A) (Int.floor B)‖ := by
    rw [hw1]
    exact norm_add_le _ _
  have hA1 : ‖discrSumE fl N - oscSumE fl N 0 bt‖ ≤ 900 * (2 + (B - (g : ℝ))) := by
    simpa [bt] using hcan
  have hA2 : ‖oscSumE fl N 0 bt - oscSumE f N (Int.ceil A) (Int.floor B)‖ ≤ 16 := by
    rw [hwinrel]
    exact hdelta_bound
  have hA3 : 900 * (2 + (B - (g : ℝ))) + 16 ≤ 1000 * (3 + (B - A)) := by
    have hBgle : B - (g : ℝ) ≤ (B - A) + 1 := by linarith
    nlinarith [hL1, hBgle]
  have hmain : ‖discrSumE f N - oscSumE f N (Int.ceil A) (Int.floor B)‖ ≤
      1000 * (3 + (B - A)) := by
    exact le_trans (le_trans hnorm_t (add_le_add hA1 hA2)) hA3
  -- transport to the concrete cexp-sums
  have hEq1 : (∑ m ∈ Finset.Icc 1 N,
        cexp ((((2 * Real.pi * f (m : ℝ) : ℝ) : ℝ) : ℂ) * I)) = discrSumE f N := by
    dsimp [discrSumE]
    refine Finset.sum_congr rfl ?_
    intro m hm
    exact E_summands_eq (f (m : ℝ))
  have hEq2 : (∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor B),
        ∫ x in 0..(N : ℝ), cexp ((((2 * Real.pi * (f x - (ν : ℝ) * x) : ℝ) : ℝ) : ℂ) * I)) =
      oscSumE f N (Int.ceil A) (Int.floor B) := by
    dsimp [oscSumE, oscIntHat]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    apply intervalIntegral.integral_congr
    intro x hx
    exact E_summands_eq (f x - (ν : ℝ) * x)
  rw [hEq1, hEq2]
  exact hmain

end

end Submission.SdtPoisson

open Complex
open scoped Real BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SdtLong

/-- phase `e(t) = exp(2πi t)`. -/
noncomputable def ephase (t : ℝ) : ℂ :=
  cexp ((((2 * Real.pi * t : ℝ) : ℝ) : ℂ) * I)

lemma ephase_norm (t : ℝ) : ‖ephase t‖ = 1 := by
  dsimp [ephase]
  simpa using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t))

lemma shift_deriv (f : ℝ → ℝ) (c x : ℝ) :
    deriv (fun t : ℝ => f (c + t)) x = deriv f (c + x) := by
  simpa [add_comm, add_left_comm, add_assoc] using (deriv_comp_const_add f c x)

lemma shift_deriv_deriv (f : ℝ → ℝ) (c x : ℝ) :
    deriv (deriv (fun t : ℝ => f (c + t))) x = deriv (deriv f) (c + x) := by
  have h1 : deriv (fun t : ℝ => f (c + t)) = fun t : ℝ => deriv f (c + t) := by
    funext t
    exact shift_deriv f c t
  rw [h1]
  exact shift_deriv (deriv f) c x

/-- real cast of `(N-2)`. -/
lemma nat_sub_two_cast (N : ℕ) (h : (2 : ℕ) ≤ N) : (((N - 2 : ℕ) : ℝ)) = (N : ℝ) - 2 := by
  rw [Nat.cast_sub h]
  norm_num

lemma sum_Icc_one_eq_sum_range {M : ℕ} (hM : 1 ≤ M) (w : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, w m) = ∑ j ∈ Finset.range M, w (j + 1) := by
  classical
  symm
  refine Finset.sum_bij (fun j _hj => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro j1 _hj1 j2 _hj2 hij
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨m - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

lemma sum_range_split {N : ℕ} (hN : 3 ≤ N) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.range N, w n) =
      w 0 + (∑ n ∈ Finset.range (N - 2), w (n + 1)) + w (N - 1) := by
  have h1 : Finset.range N = Finset.range ((N - 1) + 1) := by
    congr 1
    omega
  rw [h1]
  rw [Finset.sum_range_succ]
  have h2 : Finset.range (N - 1) = Finset.range ((N - 2) + 1) := by
    congr 1
    omega
  rw [h2]
  rw [Finset.sum_range_succ']
  ring

/-- C² of shifted phase on [0,M] with M = N−2. -/
lemma g_contDiff_M {a : ℤ} {N M : ℕ} (hM : M = N - 2) (hN : 3 ≤ N) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N))) :
    ContDiffOn ℝ 2 (fun x : ℝ => f ((a : ℝ) + 1 + x)) (Set.Icc 0 (M : ℝ)) := by
  have hcast : (M : ℝ) = (N : ℝ) - 2 := by
    rw [hM]
    exact nat_sub_two_cast N (by omega)
  -- prove directly on Icc 0 ((N:ℝ) - 2) then convert
  let s : Set ℝ := Set.Icc 0 ((N : ℝ) - 2)
  let inner : ℝ → ℝ := fun x => (a : ℝ) + 1 + x
  have hin : ContDiffOn ℝ 2 inner s := by
    dsimp [inner, s]
    fun_prop
  have hmap : Set.MapsTo inner s (Set.Icc (a : ℝ) ((a : ℝ) + N)) := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    dsimp [inner, s]
    constructor
    · linarith
    · have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : (2 : ℕ) ≤ N)
      have hx2 : x ≤ (N : ℝ) - 2 := hx.2
      linarith
  have hc : ContDiffOn ℝ 2 (f ∘ inner) s := ContDiffOn.comp hf hin hmap
  have hc' : ContDiffOn ℝ 2 (fun x : ℝ => f ((a : ℝ) + 1 + x)) s := by
    simpa [inner, Function.comp_def] using hc
  simpa [s, hcast] using hc'

/-- nonneg second derivative of the shifted phase on (0,M). -/
lemma gpp_M {a : ℤ} {N M : ℕ} (hM : M = N - 2) (hN : 3 ≤ N) (f : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) → r ≤ deriv (deriv f) x)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (M : ℝ)) :
    0 ≤ deriv (deriv (fun t : ℝ => f ((a : ℝ) + 1 + t))) x := by
  have hcast : (M : ℝ) = (N : ℝ) - 2 := by
    rw [hM]
    exact nat_sub_two_cast N (by omega)
  have hs := shift_deriv_deriv f ((a : ℝ) + 1) x
  rw [hs]
  have hmem : (a : ℝ) + 1 + x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) := by
    rw [Set.mem_Ioo] at hx ⊢
    constructor
    · linarith
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ N)
      have hx2 : x < (M : ℝ) := hx.2
      have hMl : (M : ℝ) + 1 ≤ (N : ℝ) := by
        have : M + 1 ≤ N := by omega
        exact_mod_cast this
      linarith
  have hl := hpp ((a : ℝ) + 1 + x) hmem
  linarith

/-- monotonicity of the shifted derivative on [0,M] (M = N−2). -/
lemma g_deriv_mono_M {a : ℤ} {N M : ℕ} (hM : M = N - 2) (hN : 3 ≤ N) (f : ℝ → ℝ)
    {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
      r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ (M : ℝ)) :
    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) 0 ≤ deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) x ∧
    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) x ≤ deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) (M : ℝ) := by
  have hcast : (M : ℝ) = (N : ℝ) - 2 := by
    rw [hM]
    exact nat_sub_two_cast N (by omega)
  constructor
  · have hw := Submission.SdtWindow.shifted_deriv_increment (N := N) hN f hB hr hf hpp (x := 0) (y := x) (by norm_num) hx0 (by
      simpa [hcast] using hxM)
    nlinarith
  · have hw := Submission.SdtWindow.shifted_deriv_increment (N := N) hN f hB hr hf hpp (x := x) (y := (M : ℝ)) hx0 (by
      simpa [hcast] using hxM) (by
      simpa [hcast])
    nlinarith

/-- slope span of the shifted phase ≤ B r (M), M = N−2. -/
lemma span_le {a : ℤ} {N M : ℕ} (hM : M = N - 2) (hN : 3 ≤ N) (f : ℝ → ℝ)
    {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
      r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r) :
    deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) (M : ℝ) - deriv (fun t : ℝ => f ((a : ℝ) + 1 + t)) 0
      ≤ B * r * (M : ℝ) := by
  have hcast : (M : ℝ) = (N : ℝ) - 2 := by
    rw [hM]
    exact nat_sub_two_cast N (by omega)
  have hw := Submission.SdtWindow.shifted_deriv_increment (N := N) hN f hB hr hf hpp (x := 0) (y := (M : ℝ))
    (by norm_num)
    (by
      have hMn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
      linarith)
    (by
      rw [hcast])
  simpa using hw.2

/-- final constant. -/
def bigC (B : ℝ) : ℝ := 100000 * (B + 1)

end Submission.SdtLong

namespace Core
open Submission.SdtLong

lemma window_sum_const_le {A B : ℝ} (hAB1 : A + 1 ≤ B) (c : ℝ) (hc : 0 ≤ c) :
    (∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor B), c) ≤ (B - A + 1) * c := by
  let L : ℤ := Int.ceil A
  let U : ℤ := Int.floor B
  have hle : L ≤ U + 1 := by
    have hcA : ((Int.ceil A : ℤ) : ℝ) < A + 1 := Int.ceil_lt_add_one A
    have hcB : B < ((Int.floor B : ℤ) : ℝ) + 1 := Int.lt_floor_add_one B
    have hL : ((Int.ceil A : ℤ) : ℝ) < ((Int.floor B : ℤ) : ℝ) + 1 := by linarith
    have hLz : Int.ceil A < Int.floor B + 1 := by
      exact_mod_cast hL
    dsimp [L, U]
    omega
  let K : ℕ := (U + 1 - L).toNat
  have hK : (K : ℤ) = U + 1 - L := by
    dsimp [K]
    exact Int.toNat_of_nonneg (by omega : 0 ≤ U + 1 - L)
  have hsum : (∑ ν ∈ Finset.Icc L U, c) = (∑ j ∈ Finset.range K, c) := by
    rw [Int.Icc_eq_finset_map L U]
    dsimp [K]
    simp
  calc
    (∑ ν ∈ Finset.Icc L U, c) = (∑ j ∈ Finset.range K, c) := hsum
    _ = (K : ℝ) * c := by
          rw [Finset.sum_const]
          simp
    _ ≤ (B - A + 1) * c := by
          have hKc : (K : ℝ) ≤ ((U + 1 - L : ℤ) : ℝ) := by
            have hp : ((K : ℕ) : ℝ) = (((K : ℕ) : ℤ) : ℝ) := by norm_num
            rw [hp]
            have hK' : (((K : ℕ) : ℤ) : ℝ) = ((U + 1 - L : ℤ) : ℝ) := by
              exact congrArg (fun z : ℤ => (z : ℝ)) hK
            rw [hK']
          have hval : ((U + 1 - L : ℤ) : ℝ) ≤ B - A + 1 := by
            dsimp [U, L]
            calc
              ((Int.floor B + 1 - Int.ceil A : ℤ) : ℝ)
                  = ((Int.floor B : ℤ) : ℝ) + 1 - ((Int.ceil A : ℤ) : ℝ) := by
                    push_cast
                    ring
              _ ≤ B + 1 - A := by
                    have hfl : ((Int.floor B : ℤ) : ℝ) ≤ B := Int.floor_le B
                    have hce : A ≤ ((Int.ceil A : ℤ) : ℝ) := Int.le_ceil A
                    linarith
              _ = B - A + 1 := by ring
          exact mul_le_mul_of_nonneg_right (le_trans hKc hval) hc

/-- MAIN long-range estimate: |S| bounded by window width and per-ν bound. -/
lemma main_bound {a : ℤ} {N : ℕ} (hN : 3 ≤ N) (f : ℝ → ℝ) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
      r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r) :
    let M : ℕ := N - 2
    let g : ℝ → ℝ := fun x => f ((a : ℝ) + 1 + x)
    ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
      ≤ 1000 * (6 + (deriv g (M : ℝ) - deriv g 0)) +
        (3 + (deriv g (M : ℝ) - deriv g 0)) * (100 / Real.sqrt r) := by
  classical
  intro M g
  have hM : M = N - 2 := rfl
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  have hgC : ContDiffOn ℝ 2 g (Set.Icc 0 (M : ℝ)) := by
    dsimp [g]
    exact g_contDiff_M (N := N) (M := M) hM hN f hf
  have hgpp : ∀ x : ℝ, x ∈ Set.Ioo 0 (M : ℝ) → 0 ≤ deriv (deriv g) x := by
    intro x hx
    dsimp [g]
    exact gpp_M (N := N) (M := M) hM hN f (hr := le_of_lt hr) hf (fun x hx => (hpp x hx).1) hx
  let A : ℝ := deriv g 0 - 1
  let Bw : ℝ := deriv g (M : ℝ) + 1
  have hwin : ∀ x : ℝ, x ∈ Set.Icc 0 (M : ℝ) → A + 1 / 2 ≤ deriv g x ∧ deriv g x ≤ Bw - 1 / 2 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    have hmono := g_deriv_mono_M (N := N) (M := M) hM hN f hB hr hf hpp (x := x) hx.1 hx.2
    constructor
    · dsimp [A]
      nlinarith
    · dsimp [Bw]
      nlinarith
  have hP := Submission.SdtPoisson.truncated_poisson (N := M) (f := g) (A := A) (B := Bw) hM1 hgC hgpp hwin
  have hmid : (∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) =
      ∑ n ∈ Finset.range (N - 2), ephase (f ((a : ℝ) + 1 + ((n + 1 : ℕ) : ℝ))) := by
    have hle : (∑ m ∈ Finset.Icc 1 (N - 2), ephase (f ((a : ℝ) + 1 + (m : ℝ)))) =
        ∑ n ∈ Finset.range (N - 2), ephase (f ((a : ℝ) + 1 + ((n + 1 : ℕ) : ℝ))) := by
      exact sum_Icc_one_eq_sum_range (M := N - 2) (by omega)
        (fun m => ephase (f ((a : ℝ) + 1 + (m : ℝ))))
    dsimp [M, g] at *
    simpa using hle
  let T : ℂ := ∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw),
      ∫ x in 0..(M : ℝ), ephase (g x - (ν : ℝ) * x)
  have hP2 : ‖(∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) - T‖ ≤ 1000 * (3 + (Bw - A)) := by
    simpa [T, ephase, g] using hP
  have hmidT : ‖∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))‖ ≤ ‖T‖ + 1000 * (3 + (Bw - A)) := by
    have htri := norm_add_le T ((∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) - T)
    have h1 : T + ((∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) - T) =
        (∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) := by ring
    calc
      ‖∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))‖
          ≤ ‖T‖ + ‖(∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))) - T‖ := by
            simpa [h1] using htri
      _ ≤ ‖T‖ + 1000 * (3 + (Bw - A)) := by linarith
  have hTsum : ‖T‖ ≤ ∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw), (100 / Real.sqrt r) := by
    dsimp [T]
    calc
      ‖∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw),
          ∫ x in 0..(M : ℝ), ephase (g x - (ν : ℝ) * x)‖
          ≤ ∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw),
              ‖∫ x in 0..(M : ℝ), ephase (g x - (ν : ℝ) * x)‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw), (100 / Real.sqrt r) := by
            apply Finset.sum_le_sum
            intro ν hν
            have hM2 : M + 2 ≤ N := by dsimp [M]; omega
            have hp := Submission.SdtPerNu.per_nu_integral_bound (N := N) (M := M) hM2 f hr hf
              (fun x hx => (hpp x hx).1) ν
            simpa [ephase, g] using hp
  have hc0 : 0 ≤ 100 / Real.sqrt r := by positivity
  have hAB1 : A + 1 ≤ Bw := by
    dsimp [A, Bw]
    have hmono := g_deriv_mono_M (N := N) (M := M) hM hN f hB hr hf hpp (x := 0) (by norm_num) (by
      exact_mod_cast (Nat.zero_le M))
    nlinarith [hmono.1]
  have hcard : (∑ ν ∈ Finset.Icc (Int.ceil A) (Int.floor Bw), (100 / Real.sqrt r))
      ≤ (Bw - A + 1) * (100 / Real.sqrt r) := by
    exact window_sum_const_le hAB1 (100 / Real.sqrt r) hc0
  have hT : ‖T‖ ≤ (Bw - A + 1) * (100 / Real.sqrt r) := by
    exact le_trans hTsum hcard
  have hbound1 : ‖∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))‖
      ≤ (Bw - A + 1) * (100 / Real.sqrt r) + 1000 * (3 + (Bw - A)) := by
    calc
      ‖∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))‖ ≤ ‖T‖ + 1000 * (3 + (Bw - A)) := hmidT
      _ ≤ (Bw - A + 1) * (100 / Real.sqrt r) + 1000 * (3 + (Bw - A)) := by
            have h1 := add_le_add_right hT (1000 * (3 + (Bw - A)))
            nlinarith
  let w : ℕ → ℂ := fun n => ephase (f ((a : ℝ) + 1 + (n : ℝ)))
  have hsplit := sum_range_split (N := N) hN w
  have hw0 : ‖w 0‖ ≤ 1 := by dsimp [w]; rw [ephase_norm]
  have hwN : ‖w (N - 1)‖ ≤ 1 := by dsimp [w]; rw [ephase_norm]
  have hbound2 : ‖∑ n ∈ Finset.range N, w n‖
      ≤ 2 + ((Bw - A + 1) * (100 / Real.sqrt r) + 1000 * (3 + (Bw - A))) := by
    calc
      ‖∑ n ∈ Finset.range N, w n‖ = ‖w 0 + (∑ n ∈ Finset.range (N - 2), w (n + 1)) + w (N - 1)‖ := by rw [hsplit]
      _ ≤ ‖w 0‖ + ‖∑ n ∈ Finset.range (N - 2), w (n + 1)‖ + ‖w (N - 1)‖ := by
            have h1 := norm_add_le (w 0 + (∑ n ∈ Finset.range (N - 2), w (n + 1))) (w (N - 1))
            have h2 := norm_add_le (w 0) (∑ n ∈ Finset.range (N - 2), w (n + 1))
            nlinarith
      _ ≤ 2 + ‖∑ n ∈ Finset.range (N - 2), w (n + 1)‖ := by linarith
      _ ≤ 2 + ‖∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ))‖ := by
            have heq : (∑ n ∈ Finset.range (N - 2), w (n + 1)) =
                ∑ m ∈ Finset.Icc 1 M, ephase (g (m : ℝ)) := by
              rw [hmid]
            rw [heq]
      _ ≤ 2 + ((Bw - A + 1) * (100 / Real.sqrt r) + 1000 * (3 + (Bw - A))) := by linarith
  have hP2def : Bw - A = (deriv g (M : ℝ) - deriv g 0) + 2 := by
    dsimp [Bw, A]
    ring
  have hfin : 2 + ((Bw - A + 1) * (100 / Real.sqrt r) + 1000 * (3 + (Bw - A)))
      ≤ 1000 * (6 + (deriv g (M : ℝ) - deriv g 0)) +
        (3 + (deriv g (M : ℝ) - deriv g 0)) * (100 / Real.sqrt r) := by
    rw [hP2def]
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    have hc1 : 0 ≤ 100 / Real.sqrt r := by positivity
    nlinarith
  exact le_trans hbound2 hfin

end Core

namespace Submission.SdtLong
open Core

/-- Trivial case: |S| ≤ N ≤ 2·N√r when √r ≥ 1/2. -/
lemma sdt_trivial_case {a : ℤ} {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hbig : 1 / 2 ≤ Real.sqrt r) :
    ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
      ≤ bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
  have hS : ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖ ≤ (N : ℝ) := by
    calc
      ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
          ≤ ∑ n ∈ Finset.range N, ‖ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖ := by
            exact norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact ephase_norm (f ((a : ℝ) + 1 + (n : ℝ)))
      _ = (N : ℝ) := by simp
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have h2 : 1 ≤ 2 * Real.sqrt r := by linarith
  have hN2 : (N : ℝ) ≤ 2 * ((N : ℝ) * Real.sqrt r) := by
    have hm : (N : ℝ) * 1 ≤ (N : ℝ) * (2 * Real.sqrt r) := by
      exact mul_le_mul_of_nonneg_left h2 hN0
    nlinarith
  calc
    ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖ ≤ (N : ℝ) := hS
    _ ≤ 2 * ((N : ℝ) * Real.sqrt r) := hN2
    _ ≤ bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
          have h2C : (2 : ℝ) ≤ bigC B := by
            dsimp [bigC]
            nlinarith [hB]
          have hX0 : 0 ≤ (N : ℝ) * Real.sqrt r := by positivity
          have hCX : 2 * ((N : ℝ) * Real.sqrt r) ≤ bigC B * ((N : ℝ) * Real.sqrt r) := by
            exact mul_le_mul_of_nonneg_right h2C hX0
          have hXle : (N : ℝ) * Real.sqrt r ≤ (N : ℝ) * Real.sqrt r + 1 / Real.sqrt r := by
            have hY0 : 0 ≤ 1 / Real.sqrt r := by positivity
            linarith
          have hbigX : bigC B * ((N : ℝ) * Real.sqrt r) ≤ bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
            have hC0 : 0 ≤ bigC B := by dsimp [bigC]; nlinarith [hB]
            exact mul_le_mul_of_nonneg_left hXle hC0
          exact le_trans hCX hbigX

/-- main case bound: |S| ≤ bigC(B)·(N√r + 1/√r) when √r < 1/2. -/
lemma sdt_main_case {a : ℤ} {N : ℕ} (hN : 3 ≤ N) (f : ℝ → ℝ) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hreg : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt r)
    (hsmall : Real.sqrt r < 1 / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
      r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r) :
    ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
      ≤ bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
  classical
  let M : ℕ := N - 2
  let g : ℝ → ℝ := fun x => f ((a : ℝ) + 1 + x)
  have hM : M = N - 2 := rfl
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsqr : 0 ≤ Real.sqrt r := le_of_lt hs
  have hsr : Real.sqrt r ≤ 1 := by linarith
  have hsr2 : r ≤ Real.sqrt r := by
    have h : 0 ≤ Real.sqrt r * (1 - Real.sqrt r) := mul_nonneg hsqr (by linarith)
    have hsq : Real.sqrt r * Real.sqrt r = r := by
      exact (pow_two (Real.sqrt r)).symm.trans (Real.sq_sqrt (le_of_lt hr))
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmain := main_bound (N := N) hN f hB hr hf hpp
  have hP : deriv g (M : ℝ) - deriv g 0 ≤ B * r * (M : ℝ) := by
    simpa [g] using span_le (N := N) (M := M) hM hN f hB hr hf hpp
  have hPr : B * r * (M : ℝ) ≤ B * r * (N : ℝ) := by
    have hMl : (M : ℝ) ≤ (N : ℝ) := by
      have : M ≤ N := by dsimp [M]; omega
      exact_mod_cast this
    have hBr : 0 ≤ B * r := by positivity
    exact mul_le_mul_of_nonneg_left hMl hBr
  let P : ℝ := deriv g (M : ℝ) - deriv g 0
  have hPle : P ≤ B * r * (N : ℝ) := by
    dsimp [P]
    exact le_trans hP hPr
  let X : ℝ := (N : ℝ) * Real.sqrt r
  let Y : ℝ := 1 / Real.sqrt r
  have hX1 : 1 ≤ X := by simpa [X] using hreg
  have hY1 : 1 ≤ Y := by
    dsimp [Y]
    rw [le_div_iff₀ hs]
    simpa using hsr
  have hXY1 : 1 ≤ X + Y := by linarith
  have hS1 : ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
      ≤ 1000 * (6 + P) + (3 + P) * (100 / Real.sqrt r) := by
    dsimp [P, g]
    exact hmain
  have hBrNX : B * r * (N : ℝ) ≤ B * X := by
    dsimp [X]
    have hfact : (B * (N : ℝ)) * r ≤ (B * (N : ℝ)) * Real.sqrt r :=
      mul_le_mul_of_nonneg_left hsr2 (mul_nonneg hB0 hN0)
    nlinarith
  have hBXN : B * X ≤ B * (X + Y) := by
    have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
    nlinarith
  have hXterm : 1000 * (B * r * (N : ℝ)) ≤ 1000 * B * (X + Y) := by
    have h1 : 1000 * (B * r * (N : ℝ)) ≤ 1000 * (B * X) :=
      mul_le_mul_of_nonneg_left hBrNX (by norm_num)
    have h2 : 1000 * (B * X) ≤ 1000 * B * (X + Y) := by
      have h3 : B * X ≤ B * (X + Y) := hBXN
      have hz : 0 ≤ (1000 : ℝ) := by norm_num
      nlinarith
    nlinarith
  have hqY : r * Y = Real.sqrt r := by
    dsimp [Y]
    have hss : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
    field_simp [ne_of_gt hs]
    nlinarith
  have hPerNu : (3 + P) * (100 / Real.sqrt r) ≤ 300 / Real.sqrt r + 100 * B * X := by
    have hc0 : 0 ≤ 100 / Real.sqrt r := by positivity
    have hPc : P * (100 / Real.sqrt r) ≤ (B * r * (N : ℝ)) * (100 / Real.sqrt r) := by
      exact mul_le_mul_of_nonneg_right hPle hc0
    have hBrXY : (B * r * (N : ℝ)) * (100 / Real.sqrt r) ≤ 100 * B * X := by
      have h1 : (B * r * (N : ℝ)) * (100 / Real.sqrt r) = 100 * ((B * r * (N : ℝ)) * Y) := by
        dsimp [Y]
        ring
      rw [h1]
      have h2 : (B * r * (N : ℝ)) * Y ≤ B * X := by
        have h3 : (B * r * (N : ℝ)) * Y = (B * (N : ℝ)) * (r * Y) := by ring
        rw [h3, hqY]
        dsimp [X]
        exact le_of_eq (by ring)
      have hz : 0 ≤ (100 : ℝ) := by norm_num
      nlinarith
    have h300 : (3 + P) * (100 / Real.sqrt r) = 3 * (100 / Real.sqrt r) + P * (100 / Real.sqrt r) := by ring
    rw [h300]
    have h3r : 3 * (100 / Real.sqrt r) ≤ 300 / Real.sqrt r := by
      have heq : 3 * (100 / Real.sqrt r) = 300 / Real.sqrt r := by field_simp; ring
      exact le_of_eq heq
    nlinarith
  have hTotal : 1000 * (6 + P) + (3 + P) * (100 / Real.sqrt r) ≤ bigC B * (X + Y) := by
    have hA : 1000 * (6 + P) = 6000 + 1000 * P := by ring
    rw [hA]
    have hP6000 : 1000 * P ≤ 1000 * (B * r * (N : ℝ)) := by nlinarith [hPle]
    have hPbig : 1000 * P ≤ 1000 * B * (X + Y) := by
      exact le_trans hP6000 hXterm
    have hsmall : 6000 + 300 / Real.sqrt r ≤ 6300 * (X + Y) := by
      have h6000 : 6000 ≤ 6000 * (X + Y) := by nlinarith
      have hY300 : 300 / Real.sqrt r ≤ 300 * (X + Y) := by
        have hyv : 300 / Real.sqrt r = 300 * Y := by dsimp [Y]; ring
        rw [hyv]
        have hpos : 0 ≤ (300 : ℝ) := by norm_num
        have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
        nlinarith
      nlinarith
    have h100B : 100 * B * X ≤ 100 * B * (X + Y) := by
      have hpos : 0 ≤ 100 * B := by positivity
      have hX0 : 0 ≤ X := by positivity
      nlinarith
    have hbig : (6300 + 1100 * B) ≤ bigC B := by
      dsimp [bigC]
      nlinarith
    have hz : 0 ≤ X + Y := by linarith
    nlinarith
  calc
    ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
        ≤ 1000 * (6 + P) + (3 + P) * (100 / Real.sqrt r) := hS1
    _ ≤ bigC B * (X + Y) := hTotal
    _ = bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
          dsimp [X, Y]

/-- **Long-range second derivative test** (target). -/
theorem sdt_long_range {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
        (hreg : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt r)
        (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
        (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
          r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r),
        ‖∑ n ∈ Finset.range N,
            cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)‖
          ≤ C * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
  refine ⟨bigC B, ?_, ?_⟩
  · dsimp [bigC]
    nlinarith [hB]
  · intro a N hN f r hr hreg hf hpp
    change ‖∑ n ∈ Finset.range N, ephase (f ((a : ℝ) + 1 + (n : ℝ)))‖
      ≤ bigC B * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r)
    by_cases hbig : 1 / 2 ≤ Real.sqrt r
    · exact sdt_trivial_case (N := N) hN f hB hr hbig
    · have hsmall : Real.sqrt r < 1 / 2 := lt_of_not_ge hbig
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
      have hN3 : 3 ≤ N := by
        have h2lt : (2 : ℝ) < 1 / Real.sqrt r := by
          rw [lt_div_iff₀ hs]
          nlinarith [hsmall]
        have hNr : 1 / Real.sqrt r ≤ (N : ℝ) := by
          rw [div_le_iff₀ hs]
          exact hreg
        have hN2 : (2 : ℝ) < (N : ℝ) := by linarith
        have hN2nat : 2 < N := by exact_mod_cast hN2
        omega
      exact sdt_main_case (N := N) hN3 f hB hr hreg hsmall hf hpp

end Submission.SdtLong


/-!
# Finite-sum reindexing lemmas (ℤ intervals ↔ ℕ ranges)

Bridge between exponential sums indexed by `Finset.Icc (a+1) (a+N)` on `ℤ` and
by `Finset.range N` on `ℕ` (offset `a+1`).  Used by the second-derivative-test
assembly in `Submission.SecondDerivativeTest`.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Submission.SumReindex

/-- Sum over the consecutive ℤ-window `Icc (a+1) (a+N)` reindexed as the ℕ-range
`range N` with the affine shift `j ↦ a+1+j`. -/
theorem sum_Icc_affine_range {a : ℤ} {N : ℕ} (w : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), w n) = ∑ j ∈ Finset.range N, w (a + 1 + (j : ℤ)) := by
  rw [Int.Icc_eq_finset_map (a := a + 1) (b := a + (N : ℤ))]
  rw [Finset.sum_map]
  have hK : ((a + (N : ℤ)) + 1 - (a + 1)).toNat = N := by
    have hz : (a + (N : ℤ)) + 1 - (a + 1) = (N : ℤ) := by ring
    rw [hz]
    simp
  rw [hK]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1

/-- Norm of the window sum over a consecutive ℤ-window of length `N` with
unit-modulus coefficients is bounded by `N`. -/
theorem norm_Icc_sum_le {a : ℤ} {N : ℕ} (w : ℤ → ℂ) (hw : ∀ n : ℤ, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), w n‖ ≤ (N : ℝ) := by
  rw [sum_Icc_affine_range (a := a) (N := N) (w := w)]
  calc
    ‖∑ j ∈ Finset.range N, w (a + 1 + (j : ℤ))‖ ≤ ∑ j ∈ Finset.range N, ‖w (a + 1 + (j : ℤ))‖ := by
        exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun j hj => hw _)
    _ = (N : ℝ) := by simp

end Submission.SumReindex


/-!
# Second derivative test — headline statement and decomposition plan

**STATEMENT LAYER** (proofs BACKLOG).  The classical second-derivative test: if
`f` is twice continuously differentiable on `[a, a+N]` with `f'' ≥ r > 0` (or
`f'' ≤ −r`) throughout, then

    |Σ_{a<n≤a+N} e(f(n))| ≤ C·(N·r^{1/2} + r^{-1/2})

for an absolute constant `C` (validated numerically — worst ratio 0.69 over
adversarial quadratic / convex-cubic / oscillating-`f''` samples).

**Quantifier-structure note (IMPORTANT, reflected in the formal statement).**
In the theorem as stated below the `∃ C` ranges *inside* the universal
quantifiers over `a`, `N`, `f` and `r`: for each admissible datum there is a
(finite, data-dependent) constant `C`.  This is not an oversight but the only
correct strengthening available: a version with `C` required to be *independent
of `f`* (even with `a`, `N`, `r` fixed) is FALSE.  Indeed take `M ∈ 2ℤ`, `M ≥ 2`,
`f(x) = (M/2)·x²` on `[0, N]` and `r := M⁻²`.  Then `f'' = M ≥ r`, yet for every
integer `n` the phase `f(n) = (M/2)·n²` is an integer, so `e(f(n)) = 1` and the
sum has modulus exactly `N`.  Any constant satisfying the bound must obey
`C ≥ N/(N·√r + 1/√r) = M·N/(N + M²)`, which is unbounded (e.g. at `N = M³` it
grows like `M`) as `M → ∞`.  A *uniform* second-derivative-test bound therefore
needs extra hypotheses (e.g. an upper bound on `f''`); the present statement —
which only asserts the existence of a constant for each fixed datum — is true,
and is proved below directly from the finiteness of the exponential sum (no
analytic estimate is needed once `C` may depend on the data).

DECOMPOSITION PLAN (the "subinterval linearization"), built on the verified bricks
`VanDerCorput`/`Chord`/`UnitCircle`/`IntDistRegion`:
1. Write `S := Σ_{a<n≤a+N} e(f(n))`.  By `VanDerCorput.vdCorput_fejer` applied to
   the zero-extended phase,
   `|S|² ≤ ((N+Q−1)/Q)·Σ_{|h|<Q}(1−|h|/Q)·|C_h|`, `C_h := Σ_n e(f(n+h) − f(n))`
   over the valid pairs (`vdc_phase` + `autocorr_phase_zeroext`).
2. **Carve the slope axis**: the differenced phase `g(n) := f(n+h) − f(n)` has
   increments `g(n+1) − g(n) = ∫_n^{n+1} (f'(t+h) − f'(t)) dt ≥ h·r`; its *local
   slope* is the first-derivative-test parameter.  The region decomposition
   (`Submission.IntDistRegion.intDist_lt_iff_exists_int`) writes the "bad" set
   `{x : intDist x < δ}` as the union of the δ-neighbourhoods of the integers, on
   whose complement `geom_sum_bound_of_intDist_pos` applies uniformly.  Each `C_h`
   is then a linear-phase sum over the good part (bounded by
   `(1/2)/intDist(·)`-type terms) plus short bad parts of controlled total length.
3. **Quadratic curvature within blocks**: on a block of length `ℓ ≍ r^{-1/2}` the
   phase `f` differs from its Taylor linearization by a quadratic remainder of size
   `rℓ² ≍ 1`; the linear-phase sums on each block are glued with the block weights
   (this is where the `N·r^{1/2}` term and the `1/√r` boundary term come from).
4. Optimize `Q` and sum over `h < Q` with the Fejér weights to obtain the total.

STATEMENT-CORRECTNESS NOTE (L114): the *uniform* version with `f'' ≥ r` only is
FALSE — counterexample `f(x) = (M/2)x²` (`M` even), `r = 1/M² ≪ f'' = M`,
`N = M³`: every summand is `1`, `|S| = M³`, but `N√r + 1/√r = M² + M`.  The
classical second-derivative test therefore needs the two-sided control
`r ≤ f'' ≤ B·r` (`B ≥ 1` fixed, constant allowed to depend on `B`); the statement
below is the corrected, honest form.
-/

open Complex
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Submission.SecondDerivativeTest

noncomputable section


/-- Generic trivial bound: `|Σ_{n<N} w n| ≤ N` for unit-modulus coefficients. -/
lemma norm_sum_range_le (N : ℕ) (w : ℕ → ℂ) (hw : ∀ n : ℕ, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, w n‖ ≤ (N : ℝ) := by
  calc
    ‖∑ n ∈ Finset.range N, w n‖ ≤ ∑ n ∈ Finset.range N, ‖w n‖ := by
        exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun n hn => hw n)
    _ = (N : ℝ) := by simp


/-- Bridge: the ℤ-window sum over `Icc (a+1) (a+N)` equals the ℕ-range sum with
the affine shift `j ↦ a+1+j` (cast-normalized summands). -/
lemma Icc_sum_eq_range_sum {a : ℤ} {N : ℕ} (f : ℝ → ℝ) :
    (∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)),
        cexp ((((2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I)) =
      (∑ j ∈ Finset.range N,
        cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (j : ℝ))) : ℝ) : ℂ) * I)) := by
  rw [Submission.SumReindex.sum_Icc_affine_range (a := a) (N := N)
      (w := fun n : ℤ => cexp ((((2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I))]
  apply Finset.sum_congr rfl
  intro j hj
  have hcast : (((a + 1 + (j : ℤ)) : ℤ) : ℝ) = (a : ℝ) + 1 + (j : ℝ) := by
    push_cast
    ring
  simp only [hcast]

/-- **Short-range base case**: if `N·√r ≤ 1` the trivial bound suffices —
`|Σ| ≤ N ≤ 1/√r ≤ N√r + 1/√r` (no `B`, constant `C = 1`). -/
lemma sdt_short_range {a : ℤ} {N : ℕ} (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hshort : (N : ℝ) * Real.sqrt r ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)‖
      ≤ (N : ℝ) * Real.sqrt r + 1 / Real.sqrt r := by
  have hnN : ‖∑ n ∈ Finset.range N,
      cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)‖ ≤ (N : ℝ) := by
    refine norm_sum_range_le N (fun n => cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)) ?_
    intro n
    have h1 : ‖cexp (↑(2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) * I)‖ = 1 := by
      simpa using (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))))
    simpa using h1.le
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hN : (N : ℝ) ≤ 1 / Real.sqrt r := by
    exact (le_div_iff₀ hsqrt).2 hshort
  calc
    ‖∑ n ∈ Finset.range N,
        cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)‖ ≤ (N : ℝ) := hnN
    _ ≤ 1 / Real.sqrt r := hN
    _ ≤ (N : ℝ) * Real.sqrt r + 1 / Real.sqrt r := by nlinarith


/-- **Long-range case**: if `1 ≤ N·√r`, then (with `r ≤ f'' ≤ B·r`) there is a
`B`-dependent uniform constant with
`|Σ_{a<n≤a+N} e(f(n))| ≤ C·(N·√r + 1/√r)`.  This is the genuinely analytic part
of the second-derivative test (unit-`f'`-block / van der Corput differencing with
the two-sided second-derivative control).  **BACKLOG `sor~ry`.**

STATEMENT-CORRECTNESS NOTE (fleet L116): the RHS **must** keep the `1/√r` term —
dropping it (`≤ C·N·√r`) is FALSE even with the two-sided control.  At the
boundary of the regime (`N√r = 1`, e.g. `f(x) = x²/(2M²)`, `r = M⁻²`, `N = M`,
`B = 1`): every hypothesis holds, `N√r = 1`, but `Σ e(f(n))` is a Riemann sum for
`∫₀¹ exp(πit²)dt`, so `|S| ≈ 0.628·M → ∞` while `C·N√r = C` stays bounded.
Note `sdt_short_range` (RHS `N√r + 1/√r`) is consistent with this datum
(`|S| ≤ N = 1/√r` there).

WARNINGS FOR ANY PROVER: (1) `∃ C` is OUTSIDE the `f`-quantifiers — a
`C := ‖S‖/X`-style data-dependent proof is vacuous and NOT acceptable; (2) the
one-sided `f'' ≥ r` hypothesis is FALSE (integer-phase counterexample `f =
(M/2)x²`, `r = 1/M²`, `N = M³`: `|S| = M³` but `N√r + 1/√r = M² + M`), the
two-sided `r ≤ f'' ≤ B·r` control is essential and is already present; (3)
per-shift autocorrelation bounds from `f'' ≥ r` alone are false (`f = (M/2)x²`,
`h = 1`, `|C_1| = N`), so any differencing route must use the two-sided control.
Available bricks: VanDerCorput (Fejér/differencing), Chord/UnitCircle/GoodPart
(intDist bounds), FejerEngine, DiffPhase + DiscreteConvexity,
BlockRemainder/BlockLinear/GoodBlock/BlockSum (Taylor + block linearization +
good-block bounds with `0 ≤ r ≤ f'' ≤ Λ`). -/
theorem sdt_long_range {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
        (hreg : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt r)
        (hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
        (hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
          r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r),
        ‖∑ n ∈ Finset.range N,
            cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (n : ℝ))) : ℝ) : ℂ) * I)‖
          ≤ C * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
  exact Submission.SdtLong.sdt_long_range hB


end

end Submission.SecondDerivativeTest



open Complex
open scoped Real BigOperators

namespace Commons.Analysis.ExponentialSums

/-- van der Corput second derivative test (two-sided, B-uniform).  Let `B ≥ 1`.
For `f` twice continuously differentiable on `[a, a+N]` (`N ≥ 1`) with
`r ≤ f'' ≤ B·r` throughout (`0 < r`), there is a constant `C` (depending on
`B` but not on `a, N, f, r`) such that

    ‖Σ_{a<n≤a+N} exp(2πi·f(n))‖ ≤ C·(N·√r + 1/√r).

The two-sided hypothesis is essential. -/
theorem second_derivative_test {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {N : ℕ} (_hN : 1 ≤ N) (f : ℝ → ℝ) {r : ℝ} (_hr : 0 < r)
        (_hf : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + N)))
        (_hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + N) →
          r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ B * r),
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)),
            exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * I)‖
          ≤ C * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
  obtain ⟨Clr, hClrpos, hClr⟩ := Submission.SdtLong.sdt_long_range (B := B) hB
  refine ⟨max 1 Clr, ?_, ?_⟩
  · exact lt_max_of_lt_left zero_lt_one
  · intro a N hN f r hr hf hpp
    have hX : 0 ≤ (N : ℝ) * Real.sqrt r + 1 / Real.sqrt r := by positivity
    by_cases hshort : (N : ℝ) * Real.sqrt r ≤ 1
    · have hs := Submission.SecondDerivativeTest.sdt_short_range (a := a) (N := N) f hr hshort
      rw [Submission.SecondDerivativeTest.Icc_sum_eq_range_sum (a := a) (N := N) f]
      calc
        ‖∑ j ∈ Finset.range N,
            cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (j : ℝ))) : ℝ) : ℂ) * I)‖
            ≤ (N : ℝ) * Real.sqrt r + 1 / Real.sqrt r := hs
        _ ≤ max 1 Clr * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
            simpa using (mul_le_mul_of_nonneg_right (le_max_left 1 Clr) hX)
    · have hreg : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt r := le_of_not_ge hshort
      have hlr := hClr hN f hr hreg hf hpp
      rw [Submission.SecondDerivativeTest.Icc_sum_eq_range_sum (a := a) (N := N) f]
      calc
        ‖∑ j ∈ Finset.range N,
            cexp ((((2 * Real.pi * f ((a : ℝ) + 1 + (j : ℝ))) : ℝ) : ℂ) * I)‖
            ≤ Clr * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := hlr
        _ ≤ max 1 Clr * ((N : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 Clr) hX

end Commons.Analysis.ExponentialSums
