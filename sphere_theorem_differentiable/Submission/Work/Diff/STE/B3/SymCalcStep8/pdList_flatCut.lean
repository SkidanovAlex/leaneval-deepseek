import Mathlib
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.fourierCoeff_iterate_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdList_flatCut`: the Friedrichs cutoff commutes with the iterated partial derivatives

The cutoff `S_ε = flatCut ρ ε` is the Fourier multiplier with symbol `k ↦ ρ (ε k)` and the
iterated partial derivative `∂^l = pdList l` is the Fourier multiplier with symbol
`k ↦ ∏_{i ∈ l} 2π i kᵢ`.  Two Fourier multipliers commute, so

  `∂^l (S_ε u) = S_ε (∂^l u)`  for every smooth `1`-periodic `u`.

Formally the proof is a calculus computation:

* `pdList l (seriesFun γ) = seriesFun (dmulV l γ)` (`Work.Diff.STE.pdList_seriesFun`), where
  `dmulV l` is the coefficient-side version of `∂^l`;
* `fourierCoeff (pdList l u) = dmulV l (fourierCoeff u)` (`fourierCoeff_pdList` below, by
  induction on the list with `fourierCoeff_pd` and the Leibniz-free steps
  `contDiff_pd_of_contDiff_top` / `periodicIn_pd_of_differentiable`);
* `trunc ρ ε (dmulV l c) = dmulV l (trunc ρ ε c)` (`trunc_dmulV_comm` below, scalar multipliers
  commute pointwise).

The rapid decay required by `pdList_seriesFun` comes from
`summable_wt_pow_norm_fourierCoeff_of_contDiff` (smooth `1`-periodic functions have Fourier
coefficients decaying faster than any polynomial) together with
`Work.Diff.STE.B3.SymCalcStep1.summable_trunc_moment` (the truncated family inherits every
moment bound, since `‖ρ‖ ≤ 1`).
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open BigOperators

/-! ## Iterated derivatives: smoothness and periodicity -/

/-- `∂^l v = pdList l v` is smooth for every list `l` as soon as `v` is. -/
lemma pdList_contDiff_top {ι : Type*} [Fintype ι] [DecidableEq ι] {v : (ι → ℝ) → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (l : List ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList l v) := by
  induction l with
  | nil => simpa [Work.Diff.STE.pdList] using hv
  | cons i l ih =>
      simpa only [Work.Diff.STE.pdList, List.foldr_cons] using
        Work.Diff.STE.contDiff_pd_of_contDiff_top (i := i) ih

/-- `∂^l v` is `1`-periodic in every coordinate as soon as `v` is (the derivative of a periodic
smooth function is again periodic). -/
lemma pdList_periodic_one {ι : Type*} [Fintype ι] [DecidableEq ι] {v : (ι → ℝ) → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hper : Work.Diff.STE.Periodic1 v) (l : List ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pdList l v) := by
  induction l with
  | nil => simpa [Work.Diff.STE.pdList] using hper
  | cons i l ih =>
      intro j
      have hd : Differentiable ℝ (Work.Diff.STE.pdList l v) :=
        (pdList_contDiff_top hv l).differentiable (by simp)
      exact Work.Diff.STE.periodicIn_pd_of_differentiable j i hd (ih j)

/-! ## The Fourier coefficients of an iterated derivative -/

/-- **The Fourier multiplier of `∂^l`.**  For a smooth `1`-periodic `g`, the `k`-th Fourier
coefficient of `pdList l g` is `∏_{i ∈ l} 2π i kᵢ` times the `k`-th coefficient of `g`, i.e. the
multiplied family is `dmulV l (fourierCoeff g)`. -/
lemma fourierCoeff_pdList {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι)
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g)
    (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdList l g) k
      = Work.Diff.STE.dmulV l (Work.Diff.STE.fourierCoeff g) k := by
  induction l with
  | nil => simp [Work.Diff.STE.pdList, Work.Diff.STE.dmulV]
  | cons i l ih =>
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList l g) := pdList_contDiff_top hg l
      have hpe : Work.Diff.STE.PeriodicIn i (Work.Diff.STE.pdList l g) :=
        pdList_periodic_one hg hper l i
      have h1 : Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdList (i :: l) g) k
          = (2 * Real.pi * Complex.I * (k i : ℂ))
              * Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdList l g) k := by
        simpa only [Work.Diff.STE.pdList, List.foldr_cons] using
          Work.Diff.STE.fourierCoeff_pd i (Work.Diff.STE.pdList l g) k
            (hcd.of_le (by norm_num)) hpe
      rw [h1, ih, Work.Diff.STE.dmulV_cons]
      rfl

/-! ## Scalar multipliers commute -/

/-- `trunc ρ ε` (multiplication of the `k`-th coefficient by the scalar `ρ (ε k)`) commutes with
the multiplier `dmulV l` of an iterated derivative. -/
lemma trunc_dmulV_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c : (ι → ℤ) → ℂ) (l : List ι) :
    Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmulV l c)
      = Work.Diff.STE.dmulV l (Work.Diff.STE.trunc ρ ε c) := by
  funext k
  simp only [Work.Diff.STE.trunc, Work.Diff.STE.dmulV]
  ring

/-! ## The target -/

theorem pdList_flatCut {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (l : List ι) :
    Work.Diff.STE.pdList l (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.pdList l u) := by
  -- Rapid decay of the truncated coefficient family, the hypothesis of `pdList_seriesFun`.
  have hdec : ∀ N : ℕ, Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ N
        * ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff u) k‖) := fun N =>
    Work.Diff.STE.B3.SymCalcStep1.summable_trunc_moment ρ hρ ε N
      (Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff u hu hup N)
  -- Term by term differentiation of the cutoff series.
  have hL : Work.Diff.STE.pdList l (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
      = Work.Diff.STE.seriesFun
          (Work.Diff.STE.dmulV l
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff u))) :=
    funext (Work.Diff.STE.pdList_seriesFun l
      (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff u)) hdec)
  -- The cutoff of the derivative is the same series.
  have hcoeff : Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdList l u)
      = Work.Diff.STE.dmulV l (Work.Diff.STE.fourierCoeff u) :=
    funext fun k => fourierCoeff_pdList l u hu hup k
  have hR : Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.pdList l u)
      = Work.Diff.STE.seriesFun
          (Work.Diff.STE.dmulV l
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff u))) := by
    show Work.Diff.STE.seriesFun
        (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdList l u))) = _
    rw [hcoeff, trunc_dmulV_comm]
  rw [hL, hR]

end Work.Diff.STE.B3.SymCalcStep8
