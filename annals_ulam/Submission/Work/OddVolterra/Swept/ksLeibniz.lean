import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs
import Submission.Work.Analysis.Abel.iteratedDeriv_rpow_sub

/-!
# The Leibniz expansion of the swept kernel

For a real exponent `p` and a kernel `A : ℝ → ℝ → ℝ`, the `j`-th partial `u`-derivative of
`u ↦ (σ - u)^p * A u σ` is, by the Leibniz rule and `iteratedDeriv_rpow_sub`, the finite
combination

`ks A p j x σ = ∑_{i ≤ j} lcoef j i p * (σ - x)^(p - i) * pder A (j - i) x σ`

(`lcoef j i p = (-1)^i C(j,i) (p)_i`, `pder A m x σ = ∂_u^m A(u,σ)|_{u=x}`,
all defined in `Submission/Work/Analysis/Abel/SweptKernelDefs`).

This file proves

* `ks_eq_iteratedDeriv` : that identity, off the diagonal `x < σ`;
* `deriv_ks` : its `x`-derivative, `∂_x (ks A p j x σ) = ks A p (j+1) x σ`;
* `differentiableAt_iteratedDeriv_of_contDiffOn` : a `ContDiffOn`-to-`DifferentiableAt`
  bridge for iterated derivatives, used by the swept-integral differentiation.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Swept

open Work.Analysis.Abel

/-- **The Leibniz expansion of the swept kernel.**
For `x < σ` and `A(·,σ)` smooth at `x`, the `j`-th iterated `u`-derivative at `u = x` of
`u ↦ (σ - u)^p * A u σ` is `ks A p j x σ`. -/
theorem ks_eq_iteratedDeriv {p : ℝ} {A : ℝ → ℝ → ℝ} {x σ : ℝ} (hxσ : x < σ)
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => A u σ) x) (j : ℕ) :
    ks A p j x σ = iteratedDeriv j (fun u : ℝ => (σ - u) ^ p * A u σ) x := by
  have hxne : σ - x ≠ 0 := ne_of_gt (sub_pos.mpr hxσ)
  have hpow : ContDiffAt ℝ ↑j (fun t : ℝ => t ^ p) (σ - x) :=
    Real.contDiffAt_rpow_const (Or.inl hxne)
  have hlin : ContDiffAt ℝ ⊤ (fun u : ℝ => σ - u) x := by fun_prop
  have hf : ContDiffAt ℝ ↑j (fun u : ℝ => (σ - u) ^ p) x := by
    have := hpow.comp x (hlin.of_le le_top)
    simpa [Function.comp_def] using this
  have hg : ContDiffAt ℝ ↑j (fun u : ℝ => A u σ) x := hA.of_le (by exact_mod_cast le_top)
  have hmul := iteratedDeriv_mul hf hg
  have hfun : (fun u : ℝ => (σ - u) ^ p * A u σ)
      = ((fun u : ℝ => (σ - u) ^ p) * fun u : ℝ => A u σ) := by
    funext u; rfl
  rw [hfun, hmul]
  rw [ks]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iteratedDeriv_rpow_sub hxσ i]
  rw [lcoef]
  simp only [pder]
  ring

/-- **The `x`-derivative of the Leibniz expansion.**
On the open set where `A` is smooth and off the diagonal, differentiating the expansion in the
first variable raises the order: `∂_x (ks A p j x σ) = ks A p (j+1) x σ`. -/
theorem deriv_ks {p : ℝ} {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {x σ : ℝ} (hxσ : x < σ) (hxU : (x, σ) ∈ U)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) U) (j : ℕ) :
    deriv (fun x' : ℝ => ks A p j x' σ) x = ks A p (j + 1) x σ := by
  set V : Set ℝ := {u : ℝ | (u, σ) ∈ U} ∩ Set.Iio σ with hV
  have hVopen : IsOpen V := by
    have h1 : IsOpen {u : ℝ | (u, σ) ∈ U} :=
      hU.preimage (continuous_id.prodMk continuous_const)
    exact h1.inter isOpen_Iio
  have hxV : x ∈ V := by simp [hV, hxU, hxσ]
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => A u σ) V := by
    have hcomp := hA.comp (g := fun q : ℝ × ℝ => A q.1 q.2)
      (f := fun u : ℝ => (u, σ)) (t := U) (s := V) (by fun_prop) (fun u hu => hu.1)
    have hfe : (fun q : ℝ × ℝ => A q.1 q.2) ∘ (fun u : ℝ => (u, σ)) = fun u => A u σ := by
      funext u; rfl
    rwa [hfe] at hcomp
  have hev : (fun x' : ℝ => ks A p j x' σ) =ᶠ[𝓝 x]
      (iteratedDeriv j (fun u : ℝ => (σ - u) ^ p * A u σ)) := by
    refine Filter.eventually_of_mem (hVopen.mem_nhds hxV) fun y hy => ?_
    exact ks_eq_iteratedDeriv hy.2 (hslice.contDiffAt (hVopen.mem_nhds hy)) j
  rw [hev.deriv_eq, ← iteratedDeriv_succ]
  exact (ks_eq_iteratedDeriv hxσ (hslice.contDiffAt (hVopen.mem_nhds hxV)) (j + 1)).symm

/-- **A `ContDiffOn`-to-`DifferentiableAt` bridge for iterated derivatives.**
If `f` is smooth on the open set `U` and `x ∈ U`, then the `j`-th iterated derivative of `f`
is differentiable at `x`. -/
theorem differentiableAt_iteratedDeriv_of_contDiffOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {x : ℝ} (hx : x ∈ U) (h : ContDiffOn ℝ (⊤ : ℕ∞) f U) (j : ℕ) :
    DifferentiableAt ℝ (iteratedDeriv j f) x := by
  have hlt : ((j : ℕ∞ω)) < (⊤ : ℕ∞) := by exact_mod_cast lt_top_iff_ne_top.mpr (by simp)
  have hdiffWithin : DifferentiableWithinAt ℝ (iteratedDerivWithin j f U) U x :=
    (h.differentiableOn_iteratedDerivWithin hlt hU.uniqueDiffOn) x hx
  have hAt : DifferentiableAt ℝ (iteratedDerivWithin j f U) x :=
    hdiffWithin.differentiableAt (hU.mem_nhds hx)
  refine hAt.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have hAt' : ContDiffAt ℝ (↑j : ℕ∞ω) f y :=
    (h.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  exact (iteratedDerivWithin_eq_iteratedDeriv hU.uniqueDiffOn hAt' hy).symm

end Work.OddVolterra.Swept
