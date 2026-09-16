import Mathlib
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_outside
import Submission.Commons.Analysis.Complex.rectZeroCount_le

open Complex Filter Function MeasureTheory intervalIntegral MeromorphicOn Set Topology
open scoped Real Interval Topology
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Commons.Analysis.Complex

lemma sub_zpow_diffAt {u x : ℂ} {n : ℤ} (hn : 0 ≤ n) :
    DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ n) x := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z - u) x := by fun_prop
  exact hlin.zpow (Or.inr hn)

lemma logDeriv_sub_zpow_cb {u x : ℂ} {n : ℤ} (hx : x ≠ u) :
    logDeriv (fun z : ℂ => (z - u) ^ n) x = (n : ℂ) * (1 / (x - u)) := by
  calc
    logDeriv (fun z : ℂ => (z - u) ^ n) x = (n : ℂ) * logDeriv (fun z : ℂ => z - u) x := by
      exact logDeriv_fun_zpow (by fun_prop) n
    _ = (n : ℂ) * (1 / (x - u)) := by
      congr 1
      rw [logDeriv_apply]
      rw [deriv_sub_const u]
      simp

/-- logDeriv of a canonical factorization over `closedBall 0 R`, at a point strictly inside
`ball 0 R` where `f` does not vanish. -/
lemma logDeriv_decompose_cb {f g : ℂ → ℂ} {R : ℝ}
    (hfdiff : Differentiable ℂ f)
    (hfac : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) R →
      f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ)) * g z)
    {x : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) R) (hfx : f x ≠ 0)
    (hgdiff : DifferentiableAt ℂ g x) (hg0 : g x ≠ 0) :
    logDeriv f x =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
        (1 / (x - u))) + logDeriv g x := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R) u
  let P : ℂ → ℂ := fun z => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfB) u
  have hxB : x ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hx
  have hdx : d x = 0 := by
    dsimp [d]
    by_cases hxB' : x ∈ Metric.closedBall (0 : ℂ) R
    · rw [MeromorphicOn.divisor_apply hfB.meromorphicOn hxB']
      have hord : meromorphicOrderAt f x = 0 :=
        meromorphicOrderAt_eq_zero_of_ne_zero (hfB x hxB') hfx
      simp [hord]
    · rw [MeromorphicOn.divisor_def]
      simp [hxB']
  let S : Finset ℂ := hsupp.toFinset
  have hS_coe : (S : Set ℂ) = support d := by
    exact hsupp.coe_toFinset
  have hP_fun : P = (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) := by
    funext z
    dsimp [P, S]
    have hsub : mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ (hsupp.toFinset : Set ℂ) := by
      intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : (z - u) ^ (d u) = 1 := by simp [hd0]
        exact hu this
      exact hsupp.mem_toFinset.mpr hd_ne
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (d u)) hsub]
  have hfac0 : ∀ u ∈ S, (x - u) ^ (d u) ≠ 0 := by
    intro u hu
    have hd_ne : d u ≠ 0 := by
      have huS : u ∈ (S : Set ℂ) := by simpa using hu
      rw [hS_coe] at huS
      exact huS
    have hx_ne : x ≠ u := by
      intro h
      have : d x = d u := by rw [h]
      exact hd_ne (by simpa [hdx] using this.symm)
    exact zpow_ne_zero (d u) (sub_ne_zero.mpr hx_ne)
  have hdiff : ∀ u ∈ S, DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ (d u)) x := by
    intro u hu
    exact sub_zpow_diffAt (hd_nonneg u)
  have hdiffP : DifferentiableAt ℂ P x := by
    rw [hP_fun]
    exact DifferentiableAt.fun_finsetProd (u := S) (f := fun u z : ℂ => (z - u) ^ (d u)) (x := x) hdiff
  have hfPg : f x = P x * g x := by
    simpa [P, d] using (hfac x hxB)
  have hP0 : P x ≠ 0 := by
    intro hP0
    apply hfx
    rw [hfPg, hP0, zero_mul]
  have hPg_eq_f : (fun z : ℂ => P z * g z) =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    simpa [P, d] using (hfac z (Metric.ball_subset_closedBall hz)).symm
  have hL2 : logDeriv f x = logDeriv (fun z : ℂ => P z * g z) x := by
    have hdv : deriv (fun z : ℂ => P z * g z) x = deriv f x := hPg_eq_f.deriv_eq
    rw [logDeriv_apply, logDeriv_apply]
    rw [← hdv]
    rw [hfPg]
  have hlogP : logDeriv P x = ∑ u ∈ S, (d u : ℂ) * (1 / (x - u)) := by
    calc
      logDeriv P x = logDeriv (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) x := by
        rw [hP_fun]
      _ = ∑ u ∈ S, logDeriv (fun z : ℂ => (z - u) ^ (d u)) x := by
        exact logDeriv_fun_prod hfac0 hdiff
      _ = ∑ u ∈ S, (d u : ℂ) * (1 / (x - u)) := by
        apply Finset.sum_congr rfl
        intro u hu
        calc
          logDeriv (fun z : ℂ => (z - u) ^ (d u)) x = (d u : ℂ) * logDeriv (fun z : ℂ => z - u) x := by
            exact logDeriv_fun_zpow (by fun_prop) (d u)
          _ = (d u : ℂ) * (1 / (x - u)) := by
            congr 1
            rw [logDeriv_apply]
            rw [deriv_sub_const u]
            simp
  have hL3 : logDeriv (fun z : ℂ => P z * g z) x = logDeriv P x + logDeriv g x := by
    exact logDeriv_fun_mul x hP0 hg0 hdiffP hgdiff
  have hfin_sum : (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * (1 / (x - u)))) =
      ∑ u ∈ S, (((d u : ℤ) : ℂ) * (1 / (x - u))) := by
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℂ) * (1 / (x - u)))) (s := S) ?_]
    · intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : ((d u : ℤ) : ℂ) * (1 / (x - u)) = 0 := by simp [hd0]
        exact hu this
      rw [hS_coe]
      exact hd_ne
  rw [hfin_sum]
  calc
    logDeriv f x = logDeriv P x + logDeriv g x := by
      rw [hL2, hL3]
    _ = (∑ u ∈ S, (d u : ℂ) * (1 / (x - u))) + logDeriv g x := by
      rw [hlogP]


/-! ## Rectangular boundary contour integral `rectB` -/

/-- Counterclockwise boundary integral of `h` over the rectangle with corners `z`,`w`,
written with the same side parametrisations as `rectIntegral_sub_inv_inside`. -/
noncomputable def rectB (h : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (z.im : ℂ) * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (w.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in z.im..w.im, h ((w.re : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in z.im..w.im, h ((z.re : ℂ) + (y : ℂ) * Complex.I))

/-- Boundary integral of `(s-u)⁻¹` is the residue combination of
`rectIntegral_sub_inv_inside`/`rectIntegral_sub_inv_outside`. -/
lemma rectB_sub_inv {z w u : ℂ} :
    rectB (fun s : ℂ => (s - u)⁻¹) z w =
    (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹) -
        (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹) +
        Complex.I • (∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) -
        Complex.I • (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) := by
  simp [rectB, smul_eq_mul]

/-- Boundary integral of `logDeriv g` vanishes when `logDeriv g` is complex differentiable on
the closed rectangle. -/
lemma rectB_logDeriv_eq_zero {g : ℂ → ℂ} {z w : ℂ}
    (hgdiff : DifferentiableOn ℂ (fun s : ℂ => logDeriv g s) (Complex.Rectangle z w)) :
    rectB (fun s : ℂ => logDeriv g s) z w = 0 := by
  simpa [rectB, smul_eq_mul, sub_eq_add_neg, add_assoc] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s : ℂ => logDeriv g s) z w hgdiff)

/-- Combine the four (signed) sums that arise after splitting each side integral of a sum. -/
lemma rectB_sum_four {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (Jb Jt Jr Jl : ι → ℂ) :
    ((∑ u ∈ S, a u * Jb u) - (∑ u ∈ S, a u * Jt u)) +
        Complex.I * (∑ u ∈ S, a u * Jr u) -
        Complex.I * (∑ u ∈ S, a u * Jl u) =
      ∑ u ∈ S, a u * ((Jb u - Jt u) + Complex.I * Jr u - Complex.I * Jl u) := by
  classical
  calc
    ((∑ u ∈ S, a u * Jb u) - (∑ u ∈ S, a u * Jt u)) +
        Complex.I * (∑ u ∈ S, a u * Jr u) -
        Complex.I * (∑ u ∈ S, a u * Jl u)
        = ((∑ u ∈ S, a u * Jb u) - (∑ u ∈ S, a u * Jt u)) +
            (Complex.I * (∑ u ∈ S, a u * Jr u) - Complex.I * (∑ u ∈ S, a u * Jl u)) := by
          ring
    _ = (∑ u ∈ S, (a u * Jb u - a u * Jt u)) +
          (Complex.I * (∑ u ∈ S, a u * Jr u) - Complex.I * (∑ u ∈ S, a u * Jl u)) := by
          rw [← Finset.sum_sub_distrib]
    _ = (∑ u ∈ S, (a u * Jb u - a u * Jt u)) +
          Complex.I * ((∑ u ∈ S, a u * Jr u) - (∑ u ∈ S, a u * Jl u)) := by
          ring
    _ = (∑ u ∈ S, (a u * Jb u - a u * Jt u)) +
          Complex.I * (∑ u ∈ S, (a u * Jr u - a u * Jl u)) := by
          rw [← Finset.sum_sub_distrib]
    _ = (∑ u ∈ S, (a u * Jb u - a u * Jt u)) + (∑ u ∈ S, Complex.I * (a u * Jr u - a u * Jl u)) := by
          rw [Finset.mul_sum]
    _ = ∑ u ∈ S, ((a u * Jb u - a u * Jt u) + Complex.I * (a u * Jr u - a u * Jl u)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ u ∈ S, a u * ((Jb u - Jt u) + Complex.I * Jr u - Complex.I * Jl u) := by
          apply Finset.sum_congr rfl
          intro u hu
          ring


/-- Decompose the bottom-side integral of `logDeriv f`. -/
lemma bottom_decomp {f g : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hzre : z.re < w.re)
    (hdecsum : ∀ x ∈ Set.Icc z.re w.re,
        logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I))
    (hint_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re)
    (hint_g : IntervalIntegrable (fun x : ℝ => logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I))
      volume z.re w.re) :
    (∫ x : ℝ in z.re..w.re, logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)) =
      (∑ u ∈ S, (((d u : ℤ) : ℂ) *
        (∫ x : ℝ in z.re..w.re, ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹)))) +
        (∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)) := by
  classical
  let c : ℂ → ℝ → ℂ := fun u x => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))
  let G : ℝ → ℂ := fun x => logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)
  have hEqOn : Set.EqOn (fun x : ℝ => logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
      (fun x : ℝ => (∑ u ∈ S, c u x) + G x) [[z.re, w.re]] := by
    intro x hx
    have hxI : x ∈ Set.Icc z.re w.re := by simpa [Set.uIcc_of_le hzre.le] using hx
    simpa [c, G] using (hdecsum x hxI)
  have hpt : (∑ u ∈ S, c u) = fun x : ℝ => ∑ u ∈ S, c u x := by
    funext x
    simp [Finset.sum_apply]
  have hint_sum : IntervalIntegrable (fun x : ℝ => ∑ u ∈ S, c u x) volume z.re w.re := by
    rw [← hpt]
    exact IntervalIntegrable.sum S (fun u hu => hint_u u hu)
  calc
    (∫ x : ℝ in z.re..w.re, logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
        = ∫ x : ℝ in z.re..w.re, (∑ u ∈ S, c u x) + G x := intervalIntegral.integral_congr hEqOn
    _ = (∫ x : ℝ in z.re..w.re, ∑ u ∈ S, c u x) + (∫ x : ℝ in z.re..w.re, G x) := by
        rw [intervalIntegral.integral_add]
        · simpa [c] using hint_sum
        · simpa [G] using hint_g
    _ = (∑ u ∈ S, ∫ x : ℝ in z.re..w.re, c u x) + (∫ x : ℝ in z.re..w.re, G x) := by
        rw [intervalIntegral.integral_finsetSum (s := S) (f := c) (fun u hu => hint_u u hu)]
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) *
          (∫ x : ℝ in z.re..w.re, ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹)))) +
          (∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [c, G]
        rw [intervalIntegral.integral_const_mul]

lemma top_decomp {f g : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hle : z.re ≤ w.re)
    (hdecsum : ∀ x ∈ Set.Icc z.re w.re,
        logDeriv f (((x : ℂ) + (w.im : ℂ) * Complex.I)) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g (((x : ℂ) + (w.im : ℂ) * Complex.I)))
    (hint_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re)
    (hint_g : IntervalIntegrable (fun x : ℝ => logDeriv g (((x : ℂ) + (w.im : ℂ) * Complex.I))) volume z.re w.re) :
    (∫ x : ℝ in z.re..w.re, logDeriv f (((x : ℂ) + (w.im : ℂ) * Complex.I))) =
      (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) +
        (∫ x : ℝ in z.re..w.re, logDeriv g (((x : ℂ) + (w.im : ℂ) * Complex.I))) := by
  classical
  let c : ℂ → ℝ → ℂ := fun u x => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))
  let G : ℝ → ℂ := fun x => logDeriv g (((x : ℂ) + (w.im : ℂ) * Complex.I))
  have hEqOn : Set.EqOn (fun x : ℝ => logDeriv f (((x : ℂ) + (w.im : ℂ) * Complex.I)))
      (fun x : ℝ => (∑ u ∈ S, c u x) + G x) [[z.re, w.re]] := by
    intro x hx
    have hxI : x ∈ Set.Icc z.re w.re := by simpa [Set.uIcc_of_le hle] using hx
    simpa [c, G] using (hdecsum x hxI)
  have hpt : (∑ u ∈ S, c u) = fun x : ℝ => ∑ u ∈ S, c u x := by
    funext x
    simp [Finset.sum_apply]
  have hint_sum : IntervalIntegrable (fun x : ℝ => ∑ u ∈ S, c u x) volume z.re w.re := by
    rw [← hpt]
    exact IntervalIntegrable.sum S (fun u hu => hint_u u hu)
  calc
    (∫ x : ℝ in z.re..w.re, logDeriv f (((x : ℂ) + (w.im : ℂ) * Complex.I)))
        = ∫ x : ℝ in z.re..w.re, (∑ u ∈ S, c u x) + G x := intervalIntegral.integral_congr hEqOn
    _ = (∫ x : ℝ in z.re..w.re, ∑ u ∈ S, c u x) + (∫ x : ℝ in z.re..w.re, G x) := by
        rw [intervalIntegral.integral_add]
        · simpa [c] using hint_sum
        · simpa [G] using hint_g
    _ = (∑ u ∈ S, ∫ x : ℝ in z.re..w.re, c u x) + (∫ x : ℝ in z.re..w.re, G x) := by
        rw [intervalIntegral.integral_finsetSum (s := S) (f := c) (fun u hu => hint_u u hu)]
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) +
          (∫ x : ℝ in z.re..w.re, logDeriv g (((x : ℂ) + (w.im : ℂ) * Complex.I))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [c, G]
        rw [intervalIntegral.integral_const_mul]

lemma right_decomp {f g : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hle : z.im ≤ w.im)
    (hdecsum : ∀ x ∈ Set.Icc z.im w.im,
        logDeriv f (((w.re : ℂ) + (x : ℂ) * Complex.I)) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g (((w.re : ℂ) + (x : ℂ) * Complex.I)))
    (hint_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im)
    (hint_g : IntervalIntegrable (fun x : ℝ => logDeriv g (((w.re : ℂ) + (x : ℂ) * Complex.I))) volume z.im w.im) :
    (∫ x : ℝ in z.im..w.im, logDeriv f (((w.re : ℂ) + (x : ℂ) * Complex.I))) =
      (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.im..w.im, (((w.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
        (∫ x : ℝ in z.im..w.im, logDeriv g (((w.re : ℂ) + (x : ℂ) * Complex.I))) := by
  classical
  let c : ℂ → ℝ → ℂ := fun u x => (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))
  let G : ℝ → ℂ := fun x => logDeriv g (((w.re : ℂ) + (x : ℂ) * Complex.I))
  have hEqOn : Set.EqOn (fun x : ℝ => logDeriv f (((w.re : ℂ) + (x : ℂ) * Complex.I)))
      (fun x : ℝ => (∑ u ∈ S, c u x) + G x) [[z.im, w.im]] := by
    intro x hx
    have hxI : x ∈ Set.Icc z.im w.im := by simpa [Set.uIcc_of_le hle] using hx
    simpa [c, G] using (hdecsum x hxI)
  have hpt : (∑ u ∈ S, c u) = fun x : ℝ => ∑ u ∈ S, c u x := by
    funext x
    simp [Finset.sum_apply]
  have hint_sum : IntervalIntegrable (fun x : ℝ => ∑ u ∈ S, c u x) volume z.im w.im := by
    rw [← hpt]
    exact IntervalIntegrable.sum S (fun u hu => hint_u u hu)
  calc
    (∫ x : ℝ in z.im..w.im, logDeriv f (((w.re : ℂ) + (x : ℂ) * Complex.I)))
        = ∫ x : ℝ in z.im..w.im, (∑ u ∈ S, c u x) + G x := intervalIntegral.integral_congr hEqOn
    _ = (∫ x : ℝ in z.im..w.im, ∑ u ∈ S, c u x) + (∫ x : ℝ in z.im..w.im, G x) := by
        rw [intervalIntegral.integral_add]
        · simpa [c] using hint_sum
        · simpa [G] using hint_g
    _ = (∑ u ∈ S, ∫ x : ℝ in z.im..w.im, c u x) + (∫ x : ℝ in z.im..w.im, G x) := by
        rw [intervalIntegral.integral_finsetSum (s := S) (f := c) (fun u hu => hint_u u hu)]
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.im..w.im, (((w.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
          (∫ x : ℝ in z.im..w.im, logDeriv g (((w.re : ℂ) + (x : ℂ) * Complex.I))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [c, G]
        rw [intervalIntegral.integral_const_mul]

lemma left_decomp {f g : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hle : z.im ≤ w.im)
    (hdecsum : ∀ x ∈ Set.Icc z.im w.im,
        logDeriv f (((z.re : ℂ) + (x : ℂ) * Complex.I)) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g (((z.re : ℂ) + (x : ℂ) * Complex.I)))
    (hint_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im)
    (hint_g : IntervalIntegrable (fun x : ℝ => logDeriv g (((z.re : ℂ) + (x : ℂ) * Complex.I))) volume z.im w.im) :
    (∫ x : ℝ in z.im..w.im, logDeriv f (((z.re : ℂ) + (x : ℂ) * Complex.I))) =
      (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.im..w.im, (((z.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
        (∫ x : ℝ in z.im..w.im, logDeriv g (((z.re : ℂ) + (x : ℂ) * Complex.I))) := by
  classical
  let c : ℂ → ℝ → ℂ := fun u x => (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))
  let G : ℝ → ℂ := fun x => logDeriv g (((z.re : ℂ) + (x : ℂ) * Complex.I))
  have hEqOn : Set.EqOn (fun x : ℝ => logDeriv f (((z.re : ℂ) + (x : ℂ) * Complex.I)))
      (fun x : ℝ => (∑ u ∈ S, c u x) + G x) [[z.im, w.im]] := by
    intro x hx
    have hxI : x ∈ Set.Icc z.im w.im := by simpa [Set.uIcc_of_le hle] using hx
    simpa [c, G] using (hdecsum x hxI)
  have hpt : (∑ u ∈ S, c u) = fun x : ℝ => ∑ u ∈ S, c u x := by
    funext x
    simp [Finset.sum_apply]
  have hint_sum : IntervalIntegrable (fun x : ℝ => ∑ u ∈ S, c u x) volume z.im w.im := by
    rw [← hpt]
    exact IntervalIntegrable.sum S (fun u hu => hint_u u hu)
  calc
    (∫ x : ℝ in z.im..w.im, logDeriv f (((z.re : ℂ) + (x : ℂ) * Complex.I)))
        = ∫ x : ℝ in z.im..w.im, (∑ u ∈ S, c u x) + G x := intervalIntegral.integral_congr hEqOn
    _ = (∫ x : ℝ in z.im..w.im, ∑ u ∈ S, c u x) + (∫ x : ℝ in z.im..w.im, G x) := by
        rw [intervalIntegral.integral_add]
        · simpa [c] using hint_sum
        · simpa [G] using hint_g
    _ = (∑ u ∈ S, ∫ x : ℝ in z.im..w.im, c u x) + (∫ x : ℝ in z.im..w.im, G x) := by
        rw [intervalIntegral.integral_finsetSum (s := S) (f := c) (fun u hu => hint_u u hu)]
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) * (∫ x : ℝ in z.im..w.im, (((z.re : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹))) +
          (∫ x : ℝ in z.im..w.im, logDeriv g (((z.re : ℂ) + (x : ℂ) * Complex.I))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [c, G]
        rw [intervalIntegral.integral_const_mul]


/-- Finite-support sum of `(d u) * (s-u)⁻¹` equals the sum over a Finset covering the support. -/
lemma finsum_inv_eq_sum {d : ℂ → ℤ} {S : Finset ℂ} (hS : ∀ u : ℂ, d u ≠ 0 → u ∈ S) (s : ℂ) :
    (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) = ∑ u ∈ S, (((d u : ℤ) : ℂ) * ((s - u)⁻¹)) := by
  classical
  rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) (s := S)]
  intro u hu
  have hdu : d u ≠ 0 := by
    by_contra hdu0
    apply hu
    simp [hdu0]
  exact hS u hdu


/-- Assemble the four side decompositions of `logDeriv f` into the rectangle boundary identity. -/
lemma rectB_decomp {f g : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hdec_b : ∀ x ∈ Set.Icc z.re w.re,
        logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I))
    (hdec_t : ∀ x ∈ Set.Icc z.re w.re,
        logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I))
    (hdec_r : ∀ y ∈ Set.Icc z.im w.im,
        logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I))
    (hdec_l : ∀ y ∈ Set.Icc z.im w.im,
        logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I) =
          (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) +
            logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I))
    (hint_b_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re)
    (hint_t_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re)
    (hint_r_u : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im)
    (hint_l_u : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im)
    (hint_b_g : IntervalIntegrable (fun x : ℝ => logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)) volume z.re w.re)
    (hint_t_g : IntervalIntegrable (fun x : ℝ => logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I)) volume z.re w.re)
    (hint_r_g : IntervalIntegrable (fun y : ℝ => logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im)
    (hint_l_g : IntervalIntegrable (fun y : ℝ => logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im) :
    rectB (logDeriv f) z w =
      (∑ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w)) +
        rectB (fun s : ℂ => logDeriv g s) z w := by
  classical
  let Jb : ℂ → ℂ := fun u => (∫ x : ℝ in z.re..w.re, ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))
  let Jt : ℂ → ℂ := fun u => (∫ x : ℝ in z.re..w.re, ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))
  let Jr : ℂ → ℂ := fun u => (∫ y : ℝ in z.im..w.im, ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))
  let Jl : ℂ → ℂ := fun u => (∫ y : ℝ in z.im..w.im, ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))
  have E_b :
      (∫ x : ℝ in z.re..w.re, logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * Jb u)) +
          (∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)) := by
    simpa [Jb] using
      (bottom_decomp S (d := d) hzre hdec_b hint_b_u hint_b_g)
  have E_t :
      (∫ x : ℝ in z.re..w.re, logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * Jt u)) +
          (∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I)) := by
    simpa [Jt] using
      (top_decomp S (d := d) hzre.le hdec_t hint_t_u hint_t_g)
  have E_r :
      (∫ y : ℝ in z.im..w.im, logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * Jr u)) +
          (∫ y : ℝ in z.im..w.im, logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I)) := by
    simpa [Jr] using
      (right_decomp S (d := d) hzim.le hdec_r hint_r_u hint_r_g)
  have E_l :
      (∫ y : ℝ in z.im..w.im, logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * Jl u)) +
          (∫ y : ℝ in z.im..w.im, logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I)) := by
    simpa [Jl] using
      (left_decomp S (d := d) hzim.le hdec_l hint_l_u hint_l_g)
  let Sb := ∑ u ∈ S, (((d u : ℤ) : ℂ) * Jb u)
  let St := ∑ u ∈ S, (((d u : ℤ) : ℂ) * Jt u)
  let Sr := ∑ u ∈ S, (((d u : ℤ) : ℂ) * Jr u)
  let Sl := ∑ u ∈ S, (((d u : ℤ) : ℂ) * Jl u)
  let Gb := ∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)
  let Gt := ∫ x : ℝ in z.re..w.re, logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I)
  let Gr := ∫ y : ℝ in z.im..w.im, logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I)
  let Gl := ∫ y : ℝ in z.im..w.im, logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I)
  calc
    rectB (logDeriv f) z w
        = ((Sb + Gb) - (St + Gt)) + Complex.I * (Sr + Gr) - Complex.I * (Sl + Gl) := by
          rw [show rectB (logDeriv f) z w = ((∫ x : ℝ in z.re..w.re,
                logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)) -
                (∫ x : ℝ in z.re..w.re, logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I))) +
                Complex.I * (∫ y : ℝ in z.im..w.im, logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)) -
                Complex.I * (∫ y : ℝ in z.im..w.im, logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)) by rfl]
          simp [Sb, St, Sr, Sl, Gb, Gt, Gr, Gl]
          rw [E_b, E_t, E_r, E_l]
    _ = (((Sb - St) + Complex.I * Sr) - Complex.I * Sl) + ((Gb - Gt) + Complex.I * Gr - Complex.I * Gl) := by
          ring
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) * (Jb u - Jt u + Complex.I * Jr u - Complex.I * Jl u))) +
          ((Gb - Gt) + Complex.I * Gr - Complex.I * Gl) := by
          rw [rectB_sum_four S (fun u : ℂ => ((d u : ℤ) : ℂ)) Jb Jt Jr Jl]
    _ = (∑ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w)) +
          rectB (fun s : ℂ => logDeriv g s) z w := by
          rfl


/-- Continuity of `(side x - u)⁻¹` along a side parametrised by a continuous `side`,
provided the pole is avoided on the interval. -/
lemma continuousOn_inv_comp_side {side : ℝ → ℂ} {u : ℂ} {a b : ℝ}
    (hcont : Continuous side) (hne : ∀ x ∈ Set.Icc a b, side x ≠ u) :
    ContinuousOn (fun x : ℝ => ((side x) - u)⁻¹) (Set.Icc a b) := by
  have hc : ContinuousOn (fun x : ℝ => side x - u) (Set.Icc a b) :=
    hcont.continuousOn.sub continuousOn_const
  refine ContinuousOn.inv₀ hc ?_
  intro x hx
  exact sub_ne_zero.mpr (hne x hx)

/-- Continuity of `logDeriv`-type analytic `hg` composed with a side parametrisation. -/
lemma continuousOn_logDeriv_comp_side {hg : ℂ → ℂ} {side : ℝ → ℂ} {a b R : ℝ}
    (hg_an : AnalyticOnNhd ℂ hg (Metric.ball (0 : ℂ) R))
    (hcont : Continuous side) (hside_ball : ∀ x ∈ Set.Icc a b, side x ∈ Metric.ball (0 : ℂ) R) :
    ContinuousOn (fun x : ℝ => hg (side x)) (Set.Icc a b) := by
  intro x hx
  exact ((hg_an (side x) (hside_ball x hx)).continuousAt.comp hcont.continuousAt).continuousWithinAt


/-- Rectangle boundary integral of `logDeriv f` equals the sum of residues of the (finite)
divisor-weighted poles, when `logDeriv f` decomposes on the ball `ball 0 R`. -/
lemma rectB_decomp_geom {f g : ℂ → ℂ} {z w : ℂ} {R : ℝ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s)
    (hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S)
    (hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R)
    (hzero : ∀ u : ℂ, u ∈ S → f u = 0)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0)
    (hg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R)) :
    rectB (logDeriv f) z w =
      ∑ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w) := by
  classical
  have hb_ball : ∀ x ∈ Set.Icc z.re w.re, ((x : ℂ) + (z.im : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) R := by
    intro x hx
    have hx1 : z.re ≤ x := (Set.mem_Icc.mp hx).1
    have hx2 : x ≤ w.re := (Set.mem_Icc.mp hx).2
    refine hball ((x : ℂ) + (z.im : ℂ) * Complex.I) ?_ ?_ ?_ ?_
    · simpa using hx1
    · simpa using hx2
    · simpa using (le_refl z.im)
    · simpa using hzim.le
  have hb_f : ∀ x ∈ Set.Icc z.re w.re, f ((x : ℂ) + (z.im : ℂ) * Complex.I) ≠ 0 := by
    intro x hx
    have hx1 : z.re ≤ x := (Set.mem_Icc.mp hx).1
    have hx2 : x ≤ w.re := (Set.mem_Icc.mp hx).2
    refine hfne ((x : ℂ) + (z.im : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inl (by simp)))) ?_ ?_ ?_ ?_
    · simpa using hx1
    · simpa using hx2
    · simpa using (le_refl z.im)
    · simpa using hzim.le
  have hb_ne : ∀ u ∈ S, ∀ x ∈ Set.Icc z.re w.re, ((x : ℂ) + (z.im : ℂ) * Complex.I) ≠ u := by
    intro u hu x hx hEq
    have hfu : f u = 0 := hzero u hu
    have hfs : f ((x : ℂ) + (z.im : ℂ) * Complex.I) ≠ 0 := hb_f x hx
    exact hfs (by simpa [hEq] using hfu)
  have hcont_b : Continuous (fun x : ℝ => ((x : ℂ) + (z.im : ℂ) * Complex.I)) := by fun_prop
  have hint_inv_b : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹)) volume z.re w.re := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      (continuousOn_inv_comp_side hcont_b (hb_ne u hu))
  have hint_b_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      ((continuousOn_const.mul (continuousOn_inv_comp_side hcont_b (hb_ne u hu))))
  have hint_b_g : IntervalIntegrable (fun x : ℝ => logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I)) volume z.re w.re := by
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      (continuousOn_logDeriv_comp_side hg_an hcont_b (hb_ball))
  have hdec_b : ∀ x ∈ Set.Icc z.re w.re,
      logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹))) + logDeriv g ((x : ℂ) + (z.im : ℂ) * Complex.I) := by
    intro x hx
    have h0 := hdec ((x : ℂ) + (z.im : ℂ) * Complex.I) (hb_ball x hx) (hb_f x hx)
    rwa [finsum_inv_eq_sum (d := d) hS_cov ((x : ℂ) + (z.im : ℂ) * Complex.I)] at h0
  have ht_ball : ∀ x ∈ Set.Icc z.re w.re, ((x : ℂ) + (w.im : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) R := by
    intro x hx
    have hx1 : z.re ≤ x := (Set.mem_Icc.mp hx).1
    have hx2 : x ≤ w.re := (Set.mem_Icc.mp hx).2
    refine hball ((x : ℂ) + (w.im : ℂ) * Complex.I) ?_ ?_ ?_ ?_
    · simpa using hx1
    · simpa using hx2
    · simpa using hzim.le
    · simpa using (le_refl w.im)
  have ht_f : ∀ x ∈ Set.Icc z.re w.re, f ((x : ℂ) + (w.im : ℂ) * Complex.I) ≠ 0 := by
    intro x hx
    have hx1 : z.re ≤ x := (Set.mem_Icc.mp hx).1
    have hx2 : x ≤ w.re := (Set.mem_Icc.mp hx).2
    refine hfne ((x : ℂ) + (w.im : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inr (by simp)))) ?_ ?_ ?_ ?_
    · simpa using hx1
    · simpa using hx2
    · simpa using hzim.le
    · simpa using (le_refl w.im)
  have ht_ne : ∀ u ∈ S, ∀ x ∈ Set.Icc z.re w.re, ((x : ℂ) + (w.im : ℂ) * Complex.I) ≠ u := by
    intro u hu x hx hEq
    have hfu : f u = 0 := hzero u hu
    have hfs : f ((x : ℂ) + (w.im : ℂ) * Complex.I) ≠ 0 := ht_f x hx
    exact hfs (by simpa [hEq] using hfu)
  have hcont_t : Continuous (fun x : ℝ => ((x : ℂ) + (w.im : ℂ) * Complex.I)) := by fun_prop
  have hint_inv_t : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹)) volume z.re w.re := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      (continuousOn_inv_comp_side hcont_t (ht_ne u hu))
  have hint_t_u : ∀ u ∈ S, IntervalIntegrable
      (fun x : ℝ => (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) volume z.re w.re := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      ((continuousOn_const.mul (continuousOn_inv_comp_side hcont_t (ht_ne u hu))))
  have hint_t_g : IntervalIntegrable (fun x : ℝ => logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I)) volume z.re w.re := by
    exact ContinuousOn.intervalIntegrable_of_Icc hzre.le
      (continuousOn_logDeriv_comp_side hg_an hcont_t (ht_ball))
  have hdec_t : ∀ x ∈ Set.Icc z.re w.re,
      logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹))) + logDeriv g ((x : ℂ) + (w.im : ℂ) * Complex.I) := by
    intro x hx
    have h0 := hdec ((x : ℂ) + (w.im : ℂ) * Complex.I) (ht_ball x hx) (ht_f x hx)
    rwa [finsum_inv_eq_sum (d := d) hS_cov ((x : ℂ) + (w.im : ℂ) * Complex.I)] at h0
  have hr_ball : ∀ y ∈ Set.Icc z.im w.im, ((w.re : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) R := by
    intro y hy
    have hy1 : z.im ≤ y := (Set.mem_Icc.mp hy).1
    have hy2 : y ≤ w.im := (Set.mem_Icc.mp hy).2
    refine hball ((w.re : ℂ) + (y : ℂ) * Complex.I) ?_ ?_ ?_ ?_
    · simpa using hzre.le
    · simpa using (le_refl w.re)
    · simpa using hy1
    · simpa using hy2
  have hr_f : ∀ y ∈ Set.Icc z.im w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy
    have hy1 : z.im ≤ y := (Set.mem_Icc.mp hy).1
    have hy2 : y ≤ w.im := (Set.mem_Icc.mp hy).2
    refine hfne ((w.re : ℂ) + (y : ℂ) * Complex.I) (Or.inr (Or.inl (by simp))) ?_ ?_ ?_ ?_
    · simpa using hzre.le
    · simpa using (le_refl w.re)
    · simpa using hy1
    · simpa using hy2
  have hr_ne : ∀ u ∈ S, ∀ y ∈ Set.Icc z.im w.im, ((w.re : ℂ) + (y : ℂ) * Complex.I) ≠ u := by
    intro u hu y hy hEq
    have hfu : f u = 0 := hzero u hu
    have hfs : f ((w.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := hr_f y hy
    exact hfs (by simpa [hEq] using hfu)
  have hcont_r : Continuous (fun y : ℝ => ((w.re : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hint_inv_r : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)) volume z.im w.im := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      (continuousOn_inv_comp_side hcont_r (hr_ne u hu))
  have hint_r_u : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      ((continuousOn_const.mul (continuousOn_inv_comp_side hcont_r (hr_ne u hu))))
  have hint_r_g : IntervalIntegrable (fun y : ℝ => logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im := by
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      (continuousOn_logDeriv_comp_side hg_an hcont_r (hr_ball))
  have hdec_r : ∀ y ∈ Set.Icc z.im w.im,
      logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) + logDeriv g ((w.re : ℂ) + (y : ℂ) * Complex.I) := by
    intro y hy
    have h0 := hdec ((w.re : ℂ) + (y : ℂ) * Complex.I) (hr_ball y hy) (hr_f y hy)
    rwa [finsum_inv_eq_sum (d := d) hS_cov ((w.re : ℂ) + (y : ℂ) * Complex.I)] at h0
  have hl_ball : ∀ y ∈ Set.Icc z.im w.im, ((z.re : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) R := by
    intro y hy
    have hy1 : z.im ≤ y := (Set.mem_Icc.mp hy).1
    have hy2 : y ≤ w.im := (Set.mem_Icc.mp hy).2
    refine hball ((z.re : ℂ) + (y : ℂ) * Complex.I) ?_ ?_ ?_ ?_
    · simpa using (le_refl z.re)
    · simpa using hzre.le
    · simpa using hy1
    · simpa using hy2
  have hl_f : ∀ y ∈ Set.Icc z.im w.im, f ((z.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy
    have hy1 : z.im ≤ y := (Set.mem_Icc.mp hy).1
    have hy2 : y ≤ w.im := (Set.mem_Icc.mp hy).2
    refine hfne ((z.re : ℂ) + (y : ℂ) * Complex.I) (Or.inl (by simp)) ?_ ?_ ?_ ?_
    · simpa using (le_refl z.re)
    · simpa using hzre.le
    · simpa using hy1
    · simpa using hy2
  have hl_ne : ∀ u ∈ S, ∀ y ∈ Set.Icc z.im w.im, ((z.re : ℂ) + (y : ℂ) * Complex.I) ≠ u := by
    intro u hu y hy hEq
    have hfu : f u = 0 := hzero u hu
    have hfs : f ((z.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := hl_f y hy
    exact hfs (by simpa [hEq] using hfu)
  have hcont_l : Continuous (fun y : ℝ => ((z.re : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hint_inv_l : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)) volume z.im w.im := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      (continuousOn_inv_comp_side hcont_l (hl_ne u hu))
  have hint_l_u : ∀ u ∈ S, IntervalIntegrable
      (fun y : ℝ => (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) volume z.im w.im := by
    intro u hu
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      ((continuousOn_const.mul (continuousOn_inv_comp_side hcont_l (hl_ne u hu))))
  have hint_l_g : IntervalIntegrable (fun y : ℝ => logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I)) volume z.im w.im := by
    exact ContinuousOn.intervalIntegrable_of_Icc hzim.le
      (continuousOn_logDeriv_comp_side hg_an hcont_l (hl_ball))
  have hdec_l : ∀ y ∈ Set.Icc z.im w.im,
      logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I) =
        (∑ u ∈ S, (((d u : ℤ) : ℂ) * ((((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))) + logDeriv g ((z.re : ℂ) + (y : ℂ) * Complex.I) := by
    intro y hy
    have h0 := hdec ((z.re : ℂ) + (y : ℂ) * Complex.I) (hl_ball y hy) (hl_f y hy)
    rwa [finsum_inv_eq_sum (d := d) hS_cov ((z.re : ℂ) + (y : ℂ) * Complex.I)] at h0

  have hlogdiff : DifferentiableOn ℂ (fun s : ℂ => logDeriv g s) (Complex.Rectangle z w) := by
    intro s hs
    have hsreI : s.re ∈ Set.Icc z.re w.re := by
      rw [← Set.uIcc_of_le hzre.le]
      exact (Complex.mem_reProdIm.mp hs).1
    have hsimI : s.im ∈ Set.Icc z.im w.im := by
      rw [← Set.uIcc_of_le hzim.le]
      exact (Complex.mem_reProdIm.mp hs).2
    have hsball : s ∈ Metric.ball (0 : ℂ) R := hball s hsreI.1 hsreI.2 hsimI.1 hsimI.2
    exact (hg_an s hsball).differentiableAt.differentiableWithinAt
  have hB0 : rectB (fun s : ℂ => logDeriv g s) z w = 0 :=
    rectB_logDeriv_eq_zero (g := g) hlogdiff
  have hdecAll := rectB_decomp S (d := d) hzre hzim
    hdec_b hdec_t hdec_r hdec_l
    hint_b_u hint_t_u hint_r_u hint_l_u
    hint_b_g hint_t_g hint_r_g hint_l_g
  rw [hB0] at hdecAll
  simpa using hdecAll


/-- Triangle inequality for the four-signed-term rectangle combination. -/
lemma norm_rect_comb {a b c d : ℂ} : ‖(a - b) + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc
    ‖(a - b) + c - d‖ ≤ ‖(a - b) + c‖ + ‖d‖ := norm_sub_le ((a - b) + c) d
    _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by nlinarith [norm_add_le (a - b) c]
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by nlinarith [norm_sub_le a b]

/-- Norm of the rectangle boundary integral of `h` is at most the sum of the four side
integrals of `‖h‖`. -/
lemma rectB_norm_le {h : ℂ → ℂ} {z w : ℂ} (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im) :
    ‖rectB h z w‖ ≤
      (∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
      (∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
      (∫ y : ℝ in z.im..w.im, ‖h ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
      (∫ y : ℝ in z.im..w.im, ‖h ((z.re : ℂ) + (y : ℂ) * Complex.I)‖) := by
  let A : ℂ := ∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (z.im : ℂ) * Complex.I)
  let B : ℂ := ∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (w.im : ℂ) * Complex.I)
  let C : ℂ := ∫ y : ℝ in z.im..w.im, h ((w.re : ℂ) + (y : ℂ) * Complex.I)
  let D : ℂ := ∫ y : ℝ in z.im..w.im, h ((z.re : ℂ) + (y : ℂ) * Complex.I)
  have h1 : ‖A - B + Complex.I * C - Complex.I * D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    simpa [norm_I] using
      (norm_rect_comb (a := A) (b := B) (c := Complex.I * C) (d := Complex.I * D))
  have hA : ‖A‖ ≤ ∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (z.im : ℂ) * Complex.I)‖ := by
    dsimp [A]
    exact intervalIntegral.norm_integral_le_integral_norm hzre
  have hB : ‖B‖ ≤ ∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
    dsimp [B]
    exact intervalIntegral.norm_integral_le_integral_norm hzre
  have hC : ‖C‖ ≤ ∫ y : ℝ in z.im..w.im, ‖h ((w.re : ℂ) + (y : ℂ) * Complex.I)‖ := by
    dsimp [C]
    exact intervalIntegral.norm_integral_le_integral_norm hzim
  have hD : ‖D‖ ≤ ∫ y : ℝ in z.im..w.im, ‖h ((z.re : ℂ) + (y : ℂ) * Complex.I)‖ := by
    dsimp [D]
    exact intervalIntegral.norm_integral_le_integral_norm hzim
  calc
    ‖rectB h z w‖ = ‖A - B + Complex.I * C - Complex.I * D‖ := by rfl
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := h1
    _ ≤ (∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
        (∫ x : ℝ in z.re..w.re, ‖h ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
        (∫ y : ℝ in z.im..w.im, ‖h ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
        (∫ y : ℝ in z.im..w.im, ‖h ((z.re : ℂ) + (y : ℂ) * Complex.I)‖) := by
          nlinarith



/-- The logarithmic derivative of a nonvanishing analytic function is analytic. -/
lemma analyticOnNhd_logDeriv_of {g : ℂ → ℂ} {ρ : ℝ}
    (hg_an : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ρ))
    (hg_nz : ∀ z ∈ Metric.ball (0 : ℂ) ρ, g z ≠ 0) :
    AnalyticOnNhd ℂ (fun z => logDeriv g z) (Metric.ball (0 : ℂ) ρ) := by
  intro z hz
  have hder : AnalyticAt ℂ (deriv g) z := (hg_an z hz).deriv
  have hq : AnalyticAt ℂ (fun w : ℂ => deriv g w / g w) z :=
    AnalyticAt.div hder (hg_an z hz) (hg_nz z hz)
  convert hq using 1
  funext w
  rw [logDeriv_apply]

/-- Residue of `(s-u)⁻¹` around the rectangle is `2πi` for `u` strictly inside. -/
lemma rectB_sub_inv_inside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectB (fun s : ℂ => (s - u)⁻¹) z w = (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
  rw [rectB_sub_inv]
  exact rectIntegral_sub_inv_inside hzre hzim huin

/-- Residue of `(s-u)⁻¹` around the rectangle vanishes for `u` strictly outside the
closed rectangle. -/
lemma rectB_sub_inv_outside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    rectB (fun s : ℂ => (s - u)⁻¹) z w = 0 := by
  rw [rectB_sub_inv]
  exact rectIntegral_sub_inv_outside hzre hzim huout

/-- **Argument-principle zero count in a rectangle, bounded by the four side integrals of
`|f'/f|`** (correct boundary hypothesis: `f` nonzero only on the *boundary* of the closed
rectangle, so zeros strictly inside are allowed and are the ones being counted).

`f : ℂ → ℂ` is entire, `f 0 ≠ 0`, the closed rectangle with corners `z`, `w`
(`z.re < w.re`, `z.im < w.im`) lies inside `ball 0 R`, and `f` does not vanish on the
*boundary* of the rectangle.  Then the weighted count of zeros strictly inside the open
rectangle, with multiplicity given by the divisor of `f` on `closedBall 0 R`, is at most
`(2π)⁻¹` times the sum of the four side integrals of `‖logDeriv f‖` over the boundary of the
rectangle.

This is NOT a vacuous statement: `f` may well vanish at points strictly inside the open
rectangle, and those zeros (weighted by their order) form the left-hand side.

Proof outline (argument principle, do NOT prove the LHS is zero):
(1) zeros strictly inside are finitely many and the divisor of `f` on `closedBall 0 R` at a
strictly-inside point equals its order there (adapt the divisor plumbing of
`Commons.NumberTheory.Linnik.logDeriv_circle_residue` / `Commons.Analysis.Complex.zeroFactor_g`,
which factor `f = P · g` over a ball with `P z = ∏ᶠ u, (z-u) ^ divisor u`); on a neighbourhood
of the *closed rectangle* factor the finitely many inside zeros out: `f = P · g` with
`g` holomorphic and nonzero on a neighbourhood of the closed rectangle.  Then on the boundary
`logDeriv f = ∑ᶠ u, (divisor u : ℂ) · (s-u)⁻¹ + logDeriv g`; `logDeriv g` integrates to `0`
over the rectangle boundary by `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`;
the rectangular integral of `(s-u)⁻¹` equals `2πi` when `u` is strictly inside (use
`Commons.Analysis.Complex.rectIntegral_sub_inv_inside` if it has been committed, otherwise
prove it internally, e.g. by the coordinate/principal-log computation sketched there) and `0`
when `u` is strictly outside (`Commons.Analysis.Complex.rectIntegral_sub_inv_outside`, already
committed).  This yields the exact identity
`count = (1/(2πi))·(rectangle boundary integral of logDeriv f)`.
(2) Bound: the norm of that contour integral is at most the sum of the four side integrals of
`‖logDeriv f‖` (triangle inequality over the four sides of the rectangle boundary integral,
each side integral's norm `≤` the integral of the norm of the integrand,
`intervalIntegral.norm_integral_le_of_norm_le`-style), giving the factor `1/(2π)`. -/
theorem rectZeroCount_boundary_le {f : ℂ → ℂ} {z w : ℂ} {R : ℝ}
    (hfdiff : Differentiable ℂ f) (hRpos : 0 < R) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hf0 : f 0 ≠ 0)
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ < R)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)) ≤
      (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
         (∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
         (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
         (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖)) := by
  classical
  let d : ℂ → ℤ := fun u => ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ)
  let INS : ℂ → Prop := fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  let L : ℝ := ∑ᶠ u : ℂ, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    intro s hs
    exact hfdiff.analyticAt s
  have hord : ∀ s : ℂ, s ∈ Metric.closedBall (0 : ℂ) R → meromorphicOrderAt f s ≠ ⊤ :=
    order_ne_top_on_closedBall (a := (0 : ℂ)) hRpos.le hfB hf0
  have hsupp0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)).support.Finite := by
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  rcases factor_pointwise (U := Metric.closedBall (0 : ℂ) R) hfB.meromorphicOn hord hsupp0 hfB with
    ⟨g, hg_an_cb, hg_nz_cb, hfac⟩
  have hsuppd : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  let S : Finset ℂ := hsuppd.toFinset
  have hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S := by
    intro u hu
    dsimp [S]
    exact (hsuppd.mem_toFinset).2 hu
  have hzero : ∀ u : ℂ, u ∈ S → f u = 0 := by
    intro u hu
    have hdu : d u ≠ 0 := by
      have huS : u ∈ (support d) := (hsuppd.mem_toFinset).1 (by simpa [S] using hu)
      simpa using huS
    exact divisor_ne_zero_imp_eq_zero_of_analyticOnNhd hfB hdu
  have hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R := by
    intro s h1 h2 h3 h4
    simpa [Metric.mem_ball, dist_eq_norm] using (hrect s h1 h2 h3 h4)
  have hg_an_ball : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) := by
    intro s hs
    exact hg_an_cb s (Metric.ball_subset_closedBall hs)
  have hg_nz_ball : ∀ s ∈ Metric.ball (0 : ℂ) R, g s ≠ 0 := by
    intro s hs
    exact hg_nz_cb s (Metric.ball_subset_closedBall hs)
  have hlogg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R) :=
    analyticOnNhd_logDeriv_of hg_an_ball hg_nz_ball
  have hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s := by
    intro s hs hfs
    simpa [d] using
      (logDeriv_decompose_cb (f := f) (g := g) (R := R) hfdiff hfac hs hfs
        (hg_an_cb s (Metric.ball_subset_closedBall hs)).differentiableAt
        (hg_nz_cb s (Metric.ball_subset_closedBall hs)))
  have hgeom := rectB_decomp_geom (f := f) (g := g) (z := z) (w := w) (R := R) S (d := d)
    hzre hzim hdec hS_cov hball hzero hfne hlogg_an
  -- classification of support points
  have hS_class : ∀ u : ℂ, u ∈ S →
      INS u ∨ (u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) := by
    intro u hu
    have hfu0 : f u = 0 := hzero u hu
    by_cases huCl : z.re ≤ u.re ∧ u.re ≤ w.re ∧ z.im ≤ u.im ∧ u.im ≤ w.im
    · have hnb : ¬(u.re = z.re ∨ u.re = w.re ∨ u.im = z.im ∨ u.im = w.im) := by
        intro hb
        exact (hfne u hb huCl.1 huCl.2.1 huCl.2.2.1 huCl.2.2.2) hfu0
      left
      refine ⟨lt_of_le_of_ne huCl.1 (fun h => hnb (Or.inl h.symm)),
        lt_of_le_of_ne huCl.2.1 (fun h => hnb (Or.inr (Or.inl h))),
        lt_of_le_of_ne huCl.2.2.1 (fun h => hnb (Or.inr (Or.inr (Or.inl h.symm)))),
        lt_of_le_of_ne huCl.2.2.2 (fun h => hnb (Or.inr (Or.inr (Or.inr h))))⟩
    · right
      by_cases h1 : u.re < z.re
      · exact Or.inl h1
      · by_cases h2 : w.re < u.re
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : u.im < z.im
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : w.im < u.im
            · exact Or.inr (Or.inr (Or.inr h4))
            · exfalso
              apply huCl
              refine ⟨le_of_not_gt h1, le_of_not_gt h2, le_of_not_gt h3, le_of_not_gt h4⟩
  -- LHS sum rewrite
  have hL_fin : L = ∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0)) := by
    dsimp [L]
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))) (s := S)]
    intro u hu
    have hdu : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [hd0]
    exact hS_cov u hdu
  have hL_nonneg : 0 ≤ L := by
    rw [hL_fin]
    apply Finset.sum_nonneg
    intro u hu
    have hdu : 0 ≤ (d u : ℤ) := (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfB) u
    have hin : 0 ≤ (if INS u then 1 else 0) := by by_cases h : INS u <;> simp [h]
    positivity
  -- residue evaluation
  have hres :
      rectB (logDeriv f) z w =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (L : ℂ) := by
    rw [hgeom]
    calc
      (∑ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w))
          = ∑ u ∈ S, (if INS u then (((d u : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) else 0) := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hINS : INS u
            · have hthis := rectB_sub_inv_inside (z := z) (w := w) (u := u) hzre hzim hINS
              rw [hthis]
              simp [hINS]
            · rcases hS_class u hu with hIN | hOUT
              · exact False.elim (hINS hIN)
              · have hthis := rectB_sub_inv_outside (z := z) (w := w) (u := u) hzre hzim hOUT
                rw [hthis]
                simp [hINS]
      _ = (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (∑ u ∈ S, (if INS u then ((d u : ℤ) : ℂ) else 0)) := by
            calc
              ∑ u ∈ S, (if INS u then (((d u : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) else 0)
                  = ∑ u ∈ S, ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
                      (if INS u then ((d u : ℤ) : ℂ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    by_cases hINS : INS u <;> simp [hINS] <;> ring
              _ = (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
                    (∑ u ∈ S, (if INS u then ((d u : ℤ) : ℂ) else 0)) := by
                    rw [← Finset.mul_sum]
      _ = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (L : ℂ) := by
            congr 1
            have hmid : (∑ u ∈ S, (if INS u then ((d u : ℤ) : ℂ) else 0)) = (L : ℂ) := by
              rw [hL_fin]
              change (∑ u ∈ S, (if INS u then ((d u : ℤ) : ℂ) else 0)) =
                (algebraMap ℝ ℂ) (∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0)))
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro u hu
              by_cases hINS : INS u <;> norm_num [hINS]
            exact hmid
  -- norm identity
  have hnormB : ‖rectB (logDeriv f) z w‖ = (2 : ℝ) * Real.pi * L := by
    rw [hres]
    have hnorm1 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
        simpa [Real.norm_eq_abs, abs_of_pos Real.pi_pos] using (norm_algebraMap ℝ ℂ Real.pi)
      have hI : ‖Complex.I‖ = 1 := by norm_num
      rw [h2, hpi, hI]
      ring
    calc
      ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (L : ℂ)‖ = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ * ‖(L : ℂ)‖ := by
        rw [norm_mul]
      _ = (2 * Real.pi) * ‖(L : ℂ)‖ := by rw [hnorm1]
      _ = (2 * Real.pi) * L := by
        congr 1
        have hLabs : ‖(L : ℂ)‖ = L := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hL_nonneg] using (norm_algebraMap ℝ ℂ L)
        rw [hLabs]
  -- norm bound
  have hbound := rectB_norm_le (h := logDeriv f) (z := z) (w := w) hzre.le hzim.le
  -- conclusion
  have h2pi_pos : 0 < (2 : ℝ) * Real.pi := by positivity
  have hcoef : 0 ≤ (1 : ℝ) / (2 * Real.pi) := le_of_lt (div_pos (by norm_num) h2pi_pos)
  have hL_le_B : L = (1 / (2 * Real.pi)) * ‖rectB (logDeriv f) z w‖ := by
    rw [hnormB]
    field_simp [ne_of_gt h2pi_pos]
  have hL_le : L ≤ (1 / (2 * Real.pi)) *
      ((∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
       (∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
       (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
       (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖)) := by
    calc
      L ≤ (1 / (2 * Real.pi)) * ‖rectB (logDeriv f) z w‖ := le_of_eq hL_le_B
      _ ≤ (1 / (2 * Real.pi)) *
          ((∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
           (∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
           (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
           (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖)) := by
            exact mul_le_mul_of_nonneg_left hbound hcoef
  simpa [L, INS, d] using hL_le
end Commons.Analysis.Complex
