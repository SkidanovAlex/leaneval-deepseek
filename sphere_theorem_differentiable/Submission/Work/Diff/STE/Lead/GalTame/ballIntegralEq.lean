import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-!
# `ballIntegralEq`: the `L²` energy of a jet only sees the support

This file proves that the `L²` norm squared of an iterated partial derivative `∂^β g` of a smooth
function `g : (Fin n → ℝ) → ℂ` which vanishes outside the ball of radius `r` has the same integral
over `Metric.ball 0 R` as over `Metric.ball 0 r`, for `r ≤ R`.

The proof has three independent pieces, each proved as a helper lemma here:

* `pdVec_eq_zero_of_lt_norm` — `∂^β g` vanishes on the **open** exterior `{r < ‖z‖}` of the
  `r`-ball.  Every partial derivative of a function vanishing on an open set vanishes there
  (`pd_eq_zero_of_lt_norm`), and iterating along the multi-index `β` gives the statement
  (`pdList_eq_zero_of_lt_norm`, then `List.ofFn` for `pdVec`).
* `mem_closure_of_le_norm` — the open exterior is dense in the **closed** exterior `{r ≤ ‖z‖}`:
  any point `z` with `r ≤ ‖z‖` is the limit of points of norm `> r` (here `0 < n` is used, to
  produce a non-zero vector in the case `z = 0`).  Hence, since `∂^β g` is continuous, it vanishes
  on the closed exterior as well.
* `integral_ball_eq_of_eq_zero_of_le_norm` — a purely measure-theoretic statement: a function
  vanishing on `{r ≤ ‖z‖}` has the same integral over `Metric.ball 0 R` and `Metric.ball 0 r` when
  `r ≤ R` (the indicator functions of the two balls agree pointwise).
-/

section Helpers

open MeasureTheory

/-- **A partial derivative of a function vanishing near `x` vanishes at `x`.** -/
lemma pd_eq_zero_of_eventuallyEq {ι : Type*} [DecidableEq ι] (i : ι) {f : (ι → ℝ) → ℂ}
    {x : ι → ℝ} (h : f =ᶠ[nhds x] (0 : (ι → ℝ) → ℂ)) : pd i f x = 0 := by
  have hfd : HasFDerivAt f (0 : (ι → ℝ) →L[ℝ] ℂ) x :=
    (h.hasFDerivAt_iff).mpr (hasFDerivAt_const (0 : ℂ) x)
  simp only [pd]
  rw [hfd.fderiv]
  simp

/-- **A partial derivative of a function vanishing on the open exterior of the `r`-ball vanishes
there.**  The exterior `{z | r < ‖z‖}` is open, hence a neighbourhood of each of its points. -/
lemma pd_eq_zero_of_lt_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (i : ι)
    {f : (ι → ℝ) → ℂ}
    (hf : ∀ z, r < ‖z‖ → f z = 0) : ∀ z, r < ‖z‖ → pd i f z = 0 := by
  intro z hz
  have h : f =ᶠ[nhds z] (0 : (ι → ℝ) → ℂ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
    exact hf y hy
  have hfd : HasFDerivAt f (0 : (ι → ℝ) →L[ℝ] ℂ) z :=
    (h.hasFDerivAt_iff).mpr (hasFDerivAt_const (0 : ℂ) z)
  simp only [pd]
  rw [hfd.fderiv]
  simp

/-- **Iterated partial derivatives of a function vanishing on the open exterior of the `r`-ball
vanish there** (induction on the list of directions). -/
lemma pdList_eq_zero_of_lt_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (t : List ι)
    (f : (ι → ℝ) → ℂ)
    (hf : ∀ z, r < ‖z‖ → f z = 0) : ∀ z, r < ‖z‖ → pdList t f z = 0 := by
  induction t generalizing f with
  | nil => simpa [pdList] using hf
  | cons i t ih =>
      intro z hz
      have h1 : pdList (i :: t) f = pd i (pdList t f) := by
        simp [pdList, List.foldr_cons]
      rw [h1]
      exact pd_eq_zero_of_lt_norm i (ih f hf) z hz

/-- **The multi-indexed iterated partial derivative `∂^β` of a function vanishing on the open
exterior of the `r`-ball vanishes there.** -/
lemma pdVec_eq_zero_of_lt_norm {n : ℕ} {r : ℝ} (m : ℕ) (β : Fin m → Fin n)
    (f : (Fin n → ℝ) → ℂ) (hf : ∀ z, r < ‖z‖ → f z = 0) :
    ∀ z, r < ‖z‖ → pdVec m β f z = 0 := by
  intro z hz
  simpa [pdVec] using pdList_eq_zero_of_lt_norm (List.ofFn β) f hf z hz

/-- **The open exterior of the `r`-ball is dense in the closed exterior.**  If `0 ≤ r ≤ ‖z‖` then
`z` is a limit of points of norm `> r`.  (`0 < n` is used only for the case `z = 0`, where a
non-zero vector is needed.) -/
lemma mem_closure_of_le_norm {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) {z : Fin n → ℝ}
    (hz : r ≤ ‖z‖) : z ∈ closure {y : Fin n → ℝ | r < ‖y‖} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hz0 : z = 0
  · subst hz0
    have hr0 : r = 0 := le_antisymm (by simpa using hz) hr
    refine ⟨(ε / 2) • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ)), ?_, ?_⟩
    · show r < ‖(ε / 2) • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ))‖
      rw [hr0, norm_pos_iff]
      exact smul_ne_zero (by positivity) (by simp)
    · rw [dist_zero_left]
      have hnorm : ‖(ε / 2) • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ))‖ = ε / 2 := by
        rw [norm_smul, Pi.norm_single, Real.norm_eq_abs, norm_one,
          abs_of_pos (by positivity)]
        ring
      rw [hnorm]
      linarith
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set δ : ℝ := min (ε / (2 * ‖z‖)) (1 / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact lt_min (by positivity) (by norm_num)
    refine ⟨(1 + δ) • z, ?_, ?_⟩
    · show r < ‖(1 + δ) • z‖
      have h1 : ‖(1 + δ) • z‖ = (1 + δ) * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [h1]
      nlinarith
    · rw [dist_eq_norm]
      have hsub : z - (1 + δ) • z = (-δ) • z := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      have h2 : δ ≤ ε / (2 * ‖z‖) := by rw [hδ]; exact min_le_left _ _
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith

/-- **The indicator functions of two concentric balls, of radii `r ≤ R`, agree after multiplication
by a function vanishing on the closed exterior of the `r`-ball.**  The two balls differ by the
shell `{r ≤ ‖z‖ < R}`, on which the function is zero. -/
lemma indicator_ball_eq_of_eq_zero_of_le_norm {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {r R : ℝ}
    (hRr : r ≤ R) (h : ∀ z, r ≤ ‖z‖ → φ z = 0) :
    (Metric.ball (0 : Fin n → ℝ) R).indicator φ
      = (Metric.ball (0 : Fin n → ℝ) r).indicator φ := by
  funext z
  by_cases hR : z ∈ Metric.ball (0 : Fin n → ℝ) R
  · rw [Set.indicator_of_mem hR]
    by_cases hr : z ∈ Metric.ball (0 : Fin n → ℝ) r
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hzr : r ≤ ‖z‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hr
        exact not_lt.mp hr
      rw [h z hzr]
  · rw [Set.indicator_of_notMem hR]
    by_cases hr : z ∈ Metric.ball (0 : Fin n → ℝ) r
    · rw [Set.indicator_of_mem hr]
      exfalso
      apply hR
      rw [Metric.mem_ball, dist_zero_right] at hr ⊢
      exact lt_of_lt_of_le hr hRr
    · rw [Set.indicator_of_notMem hr]

/-- **Integrals over two concentric balls agree for a function vanishing on the closed exterior of
the inner ball** (with `r ≤ R`).  Rewrite both sides as integrals over the whole space of the
indicator functions of the balls; those indicators agree pointwise. -/
lemma integral_ball_eq_of_eq_zero_of_le_norm {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {r R : ℝ}
    (hRr : r ≤ R) (h : ∀ z, r ≤ ‖z‖ → φ z = 0) :
    ∫ z in Metric.ball (0 : Fin n → ℝ) R, φ z = ∫ z in Metric.ball (0 : Fin n → ℝ) r, φ z := by
  rw [← MeasureTheory.integral_indicator (μ := volume)
        (s := Metric.ball (0 : Fin n → ℝ) R) measurableSet_ball (f := φ),
      ← MeasureTheory.integral_indicator (μ := volume)
        (s := Metric.ball (0 : Fin n → ℝ) r) measurableSet_ball (f := φ)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (fun z => congrFun (indicator_ball_eq_of_eq_zero_of_le_norm hRr h) z))

end Helpers

/-- **The integral of the `m`-th jet energy over a ball only sees the support.**

Let `0 < n`, let `g : (Fin n → ℝ) → ℂ` be a smooth function vanishing on the open exterior of the
ball of radius `r ≥ 0` (`g z = 0` whenever `r < ‖z‖`), and let `r ≤ R`.  Then the `L²` norm squared
of the `m`-th iterated partial derivative `∂^β g` has the same integral over the two balls:

  `∫ z in Metric.ball 0 R, ‖∂^β g z‖² = ∫ z in Metric.ball 0 r, ‖∂^β g z‖²`.

Indeed `∂^β g = 0` on the *open* exterior of the `r`-ball (each partial derivative of a function
vanishing on an open set vanishes there, by induction on the order), and `∂^β g` is continuous, so
`∂^β g = 0` on the closed exterior as well; the two balls differ by the shell
`{r ≤ ‖z‖ < R}`, on which the integrand vanishes identically, so the two integrals agree.  (One way
to finish: rewrite both sides as integrals over `ℝ^n` of the indicator functions of the balls; the
two indicators are equal, because on `ball 0 R \ ball 0 r` — which is contained in the closed
exterior of the `r`-ball — the integrand is `0`.)

The hypothesis `0 < n` is needed: for `n = 0` the space `Fin 0 → ℝ` is a point of volume `1` and the
vanishing hypothesis is vacuous. -/
theorem ballIntegralEq {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ∀ (g : (Fin n → ℝ) → ℂ) (r R : ℝ), 0 ≤ r → r ≤ R →
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g →
      (∀ z : Fin n → ℝ, r < ‖z‖ → g z = 0) →
      ∀ β : Fin m → Fin n,
      ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec m β g z‖ ^ 2
        = ∫ z in Metric.ball (0 : Fin n → ℝ) r, ‖Work.Diff.STE.pdVec m β g z‖ ^ 2 := by
  intro g r R hr hRr hg hv β
  -- `∂^β g` is continuous (the hypothesis is `C^∞`, in particular `C^m`).
  have hcont : Continuous (pdVec m β g) := continuous_pdVec m β g (hg.of_le (by simp))
  -- `∂^β g = 0` on the closed exterior of the `r`-ball: by continuity, from the open exterior.
  have hkey : ∀ z : Fin n → ℝ, r ≤ ‖z‖ → pdVec m β g z = 0 := by
    intro z hz
    have hcl : IsClosed {y : Fin n → ℝ | pdVec m β g y = 0} :=
      isClosed_singleton.preimage hcont
    exact hcl.closure_subset_iff.mpr
      (fun y hy => pdVec_eq_zero_of_lt_norm m β g hv y hy) (mem_closure_of_le_norm hn hr hz)
  exact integral_ball_eq_of_eq_zero_of_le_norm hRr
    (fun z hz => by rw [hkey z hz]; simp)

end Work.Diff.STE.Lead.GalTame
