import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_eq_iter_neg_lapC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Λ^k` is a *local* operator: the germ at `x` determines `Λ^k g x`

`Work.Diff.STE.B3.SymCalcStep5.lapPow k` (`= Λ^k`) is defined as the Fourier multiplier with symbol
`flatLam m ^ k`, i.e. through the *global* Fourier coefficients of `g`, so at first sight its value
at a point ought to depend on all of `g`.  It does not: on smooth `1`-periodic functions the
multiplier is the iterated flat Laplacian,

  `Λ^k g = (-Δ)^k g`   (`Work.Diff.STE.B3.SymCalcStep8.lapPow_eq_iter_neg_lapC`),

and a constant-coefficient differential operator is local: if two functions agree on a neighbourhood
of `x` then all their derivatives at `x` agree.  Hence

  `g₁ =ᶠ[𝓝 x] g₂  ⟹  Λ^k g₁ x = Λ^k g₂ x`,

which is the statement proved here.  This is the "`Λ^k` is a differential operator, not a genuine
multiplier" fact used whenever a localisation (a cutoff, a partition of unity, a chart change)
introduces a modification of `g` away from the point of interest.

The proof is the locality of `-Δ` pushed through the iteration:

* `pd_eventuallyEq` — the flat partial derivative `pd i f x = fderiv ℝ f x eᵢ` respects eventual
  equality (`Filter.EventuallyEq.fderiv` is the germ-locality of `fderiv`);
* `lapC_eventuallyEq` — so does `lapC = Σᵢ ∂ᵢ∂ᵢ` (finite sum of the `pd i ∘ pd i`);
* `iter_neg_lapC_eventuallyEq` — therefore so does every iterate `(fun w x ↦ -lapC w x)^[k]`;
* the target follows by rewriting both sides with `lapPow_eq_iter_neg_lapC` and taking the value at
  `x` (`Filter.EventuallyEq.eq_of_nhds`).
-/

namespace Work.Diff.STE.B3.VarCoef

open Filter

/-- **The flat partial derivative is local in the germ.**  If `f₁` and `f₂` agree on a
neighbourhood of `x` then so do their `i`-th partial derivatives
(`pd i f y = fderiv ℝ f y (Pi.single i 1)`), by `Filter.EventuallyEq.fderiv`. -/
lemma pd_eventuallyEq {ι : Type*} [DecidableEq ι] {f₁ f₂ : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (h : f₁ =ᶠ[nhds x] f₂) (i : ι) :
    Work.Diff.STE.pd i f₁ =ᶠ[nhds x] Work.Diff.STE.pd i f₂ := by
  have hd : fderiv ℝ f₁ =ᶠ[nhds x] fderiv ℝ f₂ := Filter.EventuallyEq.fderiv (𝕜 := ℝ) h
  filter_upwards [hd] with y hy
  simp only [Work.Diff.STE.pd]
  rw [hy]

/-- **The flat Laplacian `Δ = lapC = Σᵢ ∂ᵢ∂ᵢ` is local in the germ**: eventual equality of the
functions implies eventual equality of `lapC` applied to them (a finite sum of second flat partial
derivatives). -/
lemma lapC_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f₁ f₂ : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (h : f₁ =ᶠ[nhds x] f₂) :
    Work.Diff.STE.B3.SymCalc.lapC f₁ =ᶠ[nhds x] Work.Diff.STE.B3.SymCalc.lapC f₂ := by
  filter_upwards [Finset.eventually_all Finset.univ |>.2 (fun i (_ : i ∈ Finset.univ) =>
      pd_eventuallyEq (pd_eventuallyEq h i) i)] with y hy
  simp only [Work.Diff.STE.B3.SymCalc.lapC]
  exact Finset.sum_congr rfl (fun i _ => hy i (Finset.mem_univ i))

/-- **Every iterate of `w ↦ -Δ w` is local in the germ.**  By induction on `k`, using
`lapC_eventuallyEq` in the successor step. -/
lemma iter_neg_lapC_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {g₁ g₂ : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (h : g₁ =ᶠ[nhds x] g₂) :
    ((fun w : (ι → ℝ) → ℂ => fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC w x)^[k] g₁)
      =ᶠ[nhds x]
    ((fun w : (ι → ℝ) → ℂ => fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC w x)^[k] g₂) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hk : (fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC
        (((fun w : (ι → ℝ) → ℂ => fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC w x)^[k]) g₁) x)
        =ᶠ[nhds x]
        (fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC
        (((fun w : (ι → ℝ) → ℂ => fun x : ι → ℝ => - Work.Diff.STE.B3.SymCalc.lapC w x)^[k]) g₂) x) :=
      (lapC_eventuallyEq ih).neg
    simpa only [Function.iterate_succ_apply'] using hk

theorem lapPow_apply_eq_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (g₁ g₂ : (ι → ℝ) → ℂ) (x : ι → ℝ)
    (h : Filter.Eventually (fun y => g₁ y = g₂ y) (nhds x))
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hp₁ : Work.Diff.STE.Periodic1 g₁) (hp₂ : Work.Diff.STE.Periodic1 g₂) :
    Work.Diff.STE.B3.SymCalcStep5.lapPow k g₁ x
      = Work.Diff.STE.B3.SymCalcStep5.lapPow k g₂ x := by
  rw [Work.Diff.STE.B3.SymCalcStep8.lapPow_eq_iter_neg_lapC k g₁ h₁ hp₁ x,
      Work.Diff.STE.B3.SymCalcStep8.lapPow_eq_iter_neg_lapC k g₂ h₂ hp₂ x]
  exact (iter_neg_lapC_eventuallyEq k h).eq_of_nhds

end Work.Diff.STE.B3.VarCoef
