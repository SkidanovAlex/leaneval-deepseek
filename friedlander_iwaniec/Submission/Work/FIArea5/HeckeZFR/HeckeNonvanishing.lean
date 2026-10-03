/-
# `Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing`

The elementary non-vanishing facts about the Hecke `L`-function of `ℚ(i)` that the zero-free
region chapter needs:

* `heckeLSeries_ne_zero_of_one_lt_re` — `L(s,ψ) ≠ 0` for `re s > 1`, from the absolutely
  convergent Euler product (`heckeLSeries_eulerProduct_hasProd`) together with the reciprocal
  local factor `heckeGp` and the local identity `heckeFp * heckeGp = 1`
  (`heckeL_inv_halfPlane`).
* `Lam_ne_zero_of_one_lt_re` — the same for an entire completion `Lam` of `LambdaHecke d chi m`:
  `Lam s = (4d/π)^s Γ(s+m/2) L(s,ψ)` for `re s > 1`
  (`Lam_eq_LambdaHecke_of_one_lt_re`), and `Γ` is zero-free on `re s > 1`, the exponential
  `(4d/π)^s` too.
* `Lam_zero_re_bounds` — **zeros of the completion lie in `-1 ≤ re s ≤ 1`**: `re u > 1` is
  excluded by the previous item, and `re u < -1` is excluded by reflecting in the functional
  equation `Lam s = W · conj (Lam (conj (1-s)))` to a point of real part `> 2`.

This last statement is the hypothesis needed by the Hadamard partial-fraction "rebasing" step:
the log-derivative of `Λ` at `σ + iγ` (`σ > 1`) dominates the one at `-1 + iγ` by `1/(σ - β)` for
a zero `β + iγ`, because every zero `u` of `Λ` satisfies `re u ∈ [-1, 1]`, so that
`re (1/(s-u) - 1/(s₁-u)) ≥ 0` for `s = σ + iγ`, `s₁ = -1 + iγ`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **`L(s,ψ) ≠ 0` for `re s > 1`.**  The Hecke `L`-series is the (absolutely convergent) Euler
product of the nonzero local factors `F_p`, and the reciprocal factors `G_p` multiply it to `1`. -/
theorem heckeLSeries_ne_zero_of_one_lt_re (chi : GaussianInt → ℂ) (k : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries chi k s ≠ 0 := by
  have hFp : Multipliable (fun p : Nat.Primes => heckeFp chi k p s) :=
    (heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs).multipliable
  have hGp : Multipliable (fun p : Nat.Primes => heckeGp chi k p s) :=
    multipliable_heckeGp chi k s hmul hb hs
  have h := Multipliable.tprod_mul hFp hGp
  rw [show (fun p : Nat.Primes => heckeFp chi k p s * heckeGp chi k p s) = fun _ => (1 : ℂ)
        from funext (fun p => heckeFp_mul_heckeGp chi k p s hmul h1 hb (by linarith)),
      tprod_one] at h
  have hL : (∏' p : Nat.Primes, heckeFp chi k p s) = heckeLSeries chi k s :=
    (heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs).tprod_eq
  rw [hL] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

/-- The shifted Gamma factor `Γ(s + m/2)` does not vanish for `re s > 0`. -/
lemma gamma_shift_ne_zero {m : ℕ} {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma (s + (m : ℂ) / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  have hdiv : ((m : ℂ) / 2).re = (m : ℝ) / 2 := by
    rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]
    simp [Complex.normSq_apply]
    ring
  rw [Complex.add_re, hdiv]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The exponential `(4d/π)^s` of the completed Hecke `L`-function does not vanish. -/
lemma stripX_cpow_ne_zero {d : ℕ} (hd : 1 ≤ d) (s : ℂ) : (stripX d) ^ s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (stripX_ne_zero hd))

/-- **The completion does not vanish in `re s > 1`.**  By the identity theorem the completion
agrees with `(4d/π)^s Γ(s+m/2) L(s,ψ)` on the whole half-plane `re s > 1`, and each factor
there is nonzero. -/
theorem Lam_ne_zero_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℕ}
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s)
    {s : ℂ} (hs : 1 < s.re) : Lam s ≠ 0 := by
  rw [Lam_eq_LambdaHecke_of_one_lt_re hd hAn hb hagree hs]
  rw [show LambdaHecke d chi m s
      = (stripX d) ^ s * Complex.Gamma (s + (m : ℂ) / 2) * heckeLSeries chi (m : ℤ) s
      from rfl]
  refine mul_ne_zero (mul_ne_zero (stripX_cpow_ne_zero hd s) ?_) ?_
  · exact gamma_shift_ne_zero (by linarith)
  · exact heckeLSeries_ne_zero_of_one_lt_re chi (m : ℤ) h1 hmul hb hs

/-- **Zeros of the completion lie in `[-1, 1]`.**  `re u > 1` is excluded by
`Lam_ne_zero_of_one_lt_re`; `re u < -1` is excluded by reflecting in the functional equation
(which sends `u` to a point of real part `> 2`). -/
theorem Lam_zero_re_bounds {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℕ} {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hFE : ∃ W : ℂ, W ≠ 0 ∧ ∀ s : ℂ, Lam s = W * star (Lam (star (1 - s))))
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s)
    {u : ℂ} (hu : Lam u = 0) : -1 ≤ u.re ∧ u.re ≤ 1 := by
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨W, hW0, hW⟩ := hFE
    have hu' : star (Lam (star (1 - u))) = 0 := by
      have := hW u
      rw [hu] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hW0
    have hz : Lam (star (1 - u)) = 0 := by
      have := congrArg star hu'
      simpa using this
    have hre : 1 < (star (1 - u)).re := by
      have h1u : (star (1 - u)).re = 1 - u.re := by
        simp [Complex.star_def, Complex.sub_re]
      rw [h1u]
      linarith
    exact Lam_ne_zero_of_one_lt_re hd hAn h1 hmul hb hagree hre hz
  · by_contra hlt
    push Not at hlt
    exact Lam_ne_zero_of_one_lt_re hd hAn h1 hmul hb hagree hlt hu

end

end Work.FIArea5.S16Hecke
