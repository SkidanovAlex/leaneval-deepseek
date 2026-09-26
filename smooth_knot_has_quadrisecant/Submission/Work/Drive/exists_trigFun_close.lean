import Mathlib
import Submission.Work.Drive.trigFun

/-!
# Uniform approximation of a continuous `2π`-periodic function by trigonometric sums

The main result of this file, `Work.Drive.exists_trigFun_close`, states that every continuous
`h : ℝ → ℝ` with `h (t + 2 * π) = h t` can be approximated uniformly on all of `ℝ` by a finite
real trigonometric sum `q : TrigFun ℝ` (`q.toFun t = Σ k, cos (k t) • q.c k + sin (k t) • q.d k`).

The proof is the classical Stone–Weierstrass argument, run on the circle:

* `h` is identified with a continuous function on the additive circle `AddCircle (2 * π)` through
  `Function.Periodic.lift` (`AddCircle.liftIco` provides continuity);
* Mathlib's `span_fourier_closure_eq_top` says the `ℂ`-linear span of the characters
  `fourier n : C(AddCircle T, ℂ)` is dense, so a *finite* complex linear combination `∑ c k • fourier k`
  is uniformly `ε`-close to the complexification of `h`;
* taking real parts of such a combination is exactly the evaluation of a real trigonometric sum,
  built from the coefficients by `ofFinsupp` (`re_sum_smul_fourier`).
-/

namespace Work.Drive

open scoped Real

open TrigFun

noncomputable section

/-- The real trigonometric sum whose `cos`-coefficients are the real parts of `c` and whose
`sin`-coefficients are the negatives of the imaginary parts of `c`.

It is exactly the "real part" of the complex trigonometric sum `∑ k, c k • fourier k` on the
circle of period `2 * π`: see `re_sum_smul_fourier`. -/
def ofFinsupp (c : ℤ →₀ ℂ) : TrigFun ℝ :=
  ⟨c.mapRange Complex.re (by simp), c.mapRange (fun z => -z.im) (by simp)⟩

/-- Evaluation of a finitely supported sum of bundled continuous complex functions. -/
lemma finsupp_sum_apply_C {ι X : Type*} [TopologicalSpace X] (c : ι →₀ ℂ)
    (F : ι → ℂ → C(X, ℂ)) (x : X) :
    (c.sum F) x = c.sum (fun i a => F i a x) := by
  rw [Finsupp.sum, Finsupp.sum]
  exact ContinuousMap.sum_apply c.support (fun i => F i (c i)) x

/-- The real part of the complex trigonometric sum `∑ k, c k • fourier k` (evaluated on the
additive circle `AddCircle (2 * π)` at the class of `t`) is the real trigonometric sum
`(ofFinsupp c).toFun t`. -/
theorem re_sum_smul_fourier (c : ℤ →₀ ℂ) (t : ℝ) :
    ((c.sum (fun k a => a • fourier (T := 2 * Real.pi) k))
        (t : AddCircle (2 * Real.pi))).re = (ofFinsupp c).toFun t := by
  have key : ∀ (k : ℤ) (a : ℂ),
      ((a • fourier (T := 2 * Real.pi) k) (t : AddCircle (2 * Real.pi))).re
        = a.re * Real.cos ((k : ℝ) * t) - a.im * Real.sin ((k : ℝ) * t) := by
    intro k a
    rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_apply]
    have harg : (2 * ↑Real.pi * Complex.I * ↑k * ↑t / ↑(2 * Real.pi) : ℂ)
        = ↑((k : ℝ) * t) * Complex.I := by
      field_simp
      push_cast
      ring
    rw [harg, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have keyL : ((c.sum (fun k a => a • fourier (T := 2 * Real.pi) k))
        (t : AddCircle (2 * Real.pi))).re
      = c.support.sum (fun k =>
          (c k).re * Real.cos ((k : ℝ) * t) - (c k).im * Real.sin ((k : ℝ) * t)) := by
    rw [finsupp_sum_apply_C, Finsupp.sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun k _ => key k (c k)
  have keyR : (ofFinsupp c).toFun t
      = c.support.sum (fun k =>
          (c k).re * Real.cos ((k : ℝ) * t) - (c k).im * Real.sin ((k : ℝ) * t)) := by
    have h1 := Finsupp.sum_mapRange_index (f := Complex.re) (hf := by simp) (g := c)
      (h := fun k r => Real.cos ((k : ℝ) * t) • r) (by intro k; simp)
    have h2 := Finsupp.sum_mapRange_index (f := fun z : ℂ => -z.im) (hf := by simp) (g := c)
      (h := fun k r => Real.sin ((k : ℝ) * t) • r) (by intro k; simp)
    simp only [TrigFun.toFun, ofFinsupp]
    rw [h1, h2]
    rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_eq_mul]
    ring
  rw [keyL, keyR]

theorem exists_trigFun_close {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h (2 * Real.pi)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : TrigFun ℝ, ∀ t : ℝ, |q.toFun t - h t| < ε := by
  have hpi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  -- `h` as a continuous function on the circle `AddCircle (2 * π)`
  have hper : h 0 = h (2 * Real.pi) := by simpa using (hp 0).symm
  have hcont : Continuous (AddCircle.liftIco (2 * Real.pi) 0 h) :=
    AddCircle.liftIco_zero_continuous hper hc.continuousOn
  have hlift : AddCircle.liftIco (2 * Real.pi) 0 h = hp.lift := by
    funext x
    have h1 : AddCircle.liftIco (2 * Real.pi) 0 h x
        = h ((AddCircle.equivIco (2 * Real.pi) 0 x : Set.Ico 0 (0 + 2 * Real.pi)) : ℝ) := by
      conv_lhs => rw [← AddCircle.coe_equivIco (p := 2 * Real.pi) (a := 0) (y := x)]
      exact AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := 0)
        (AddCircle.equivIco (2 * Real.pi) 0 x).2
    have h2 : hp.lift x
        = h ((AddCircle.equivIco (2 * Real.pi) 0 x : Set.Ico 0 (0 + 2 * Real.pi)) : ℝ) := by
      conv_lhs => rw [← AddCircle.coe_equivIco (p := 2 * Real.pi) (a := 0) (y := x)]
      exact Function.Periodic.lift_coe hp _
    rw [h1, h2]
  have hcontLift : Continuous hp.lift := by rw [← hlift]; exact hcont
  let H : C(AddCircle (2 * Real.pi), ℝ) := ⟨hp.lift, hcontLift⟩
  have hH : ∀ t : ℝ, H (t : AddCircle (2 * Real.pi)) = h t := fun t =>
    Function.Periodic.lift_coe hp t
  -- complexification
  let Hc : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x => (H x : ℂ), Complex.continuous_ofReal.comp H.continuous⟩
  have hHc : ∀ t : ℝ, Hc (t : AddCircle (2 * Real.pi)) = (h t : ℂ) := fun t => by
    show (H (t : AddCircle (2 * Real.pi)) : ℂ) = (h t : ℂ)
    rw [hH t]
  -- density of the linear span of the characters
  have hmem : Hc ∈ (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨F, hFmem, hFdist⟩ := (Metric.mem_closure_iff.mp hmem) ε hε
  obtain ⟨c, hc_eq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hFmem
  refine ⟨ofFinsupp c, fun t => ?_⟩
  have hc_apply : F (t : AddCircle (2 * Real.pi))
      = (c.sum (fun k a => a • fourier (T := 2 * Real.pi) k)) (t : AddCircle (2 * Real.pi)) := by
    rw [hc_eq]
  have hre : (ofFinsupp c).toFun t = (F (t : AddCircle (2 * Real.pi))).re := by
    rw [hc_apply, ← re_sum_smul_fourier c t]
  have hdist_t : dist (F (t : AddCircle (2 * Real.pi))) (Hc (t : AddCircle (2 * Real.pi)))
      ≤ dist F Hc :=
    ContinuousMap.dist_apply_le_dist (f := F) (g := Hc) (t : AddCircle (2 * Real.pi))
  have hlt : dist (F (t : AddCircle (2 * Real.pi))) (Hc (t : AddCircle (2 * Real.pi))) < ε :=
    lt_of_le_of_lt hdist_t (by rwa [dist_comm] at hFdist)
  calc |(ofFinsupp c).toFun t - h t|
      = |((F (t : AddCircle (2 * Real.pi)) - Hc (t : AddCircle (2 * Real.pi))).re)| := by
        rw [hre, hHc t, Complex.sub_re, Complex.ofReal_re]
      _ ≤ ‖F (t : AddCircle (2 * Real.pi)) - Hc (t : AddCircle (2 * Real.pi))‖ :=
        Complex.abs_re_le_norm _
      _ = dist (F (t : AddCircle (2 * Real.pi))) (Hc (t : AddCircle (2 * Real.pi))) := by
        rw [dist_eq_norm]
      _ < ε := hlt

end

end Work.Drive
