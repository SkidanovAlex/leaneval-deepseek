import Mathlib
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Linnik


lemma analyticOnNhd_univ_of_differentiable {f : ℂ → ℂ} (hfdiff : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f univ := by
  intro z hz
  exact hfdiff.analyticAt z

lemma differentiableAt_sub_zpow {u x : ℂ} {n : ℤ} (hn : 0 ≤ n) :
    DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ n) x := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z - u) x := by fun_prop
  exact hlin.zpow (Or.inr hn)

lemma logDeriv_sub_zpow {u x : ℂ} {n : ℤ} (hx : x ≠ u) :
    logDeriv (fun z : ℂ => (z - u) ^ n) x = (n : ℂ) * (1 / (x - u)) := by
  calc
    logDeriv (fun z : ℂ => (z - u) ^ n) x = (n : ℂ) * logDeriv (fun z : ℂ => z - u) x := by
      exact logDeriv_fun_zpow (by fun_prop) n
    _ = (n : ℂ) * (1 / (x - u)) := by
      congr 1
      rw [logDeriv_apply]
      rw [deriv_sub_const u]
      simp

/-- Canonical factorization over an open neighbourhood of the closed ball, obtained by the identity
theorem from `zeroFactor_g`. -/
lemma factorization_open {f : ℂ → ℂ} {R : ℝ} (hRpos : 0 < R)
    (hfdiff : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hfc : ∀ u : ℂ, ‖u‖ = R → f u ≠ 0) :
    ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      AnalyticOnNhd ℂ g (ball (0 : ℂ) (R + ε)) ∧
      (∀ z ∈ ball (0 : ℂ) (R + ε), g z ≠ 0) ∧
      (∀ z, z ∈ ball (0 : ℂ) (R + ε) →
        f z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u)) * g z) := by
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u
  let P : ℂ → ℂ := fun z => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  rcases Commons.Analysis.Complex.zeroFactor_g (a := (0 : ℂ)) (R := R) hRpos hfB hf0
      (by intro u hu; exact hfc u (by simpa using hu)) with ⟨g, ε, hεpos, hg_an, hg_nz, hfeqB⟩
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfB) u
  let S : Finset ℂ := hsupp.toFinset
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
  have hP_diff : DifferentiableOn ℂ P (ball (0 : ℂ) (R + ε)) := by
    intro z hz
    rw [hP_fun]
    have hD : DifferentiableAt ℂ (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) z :=
      DifferentiableAt.fun_finsetProd (u := S) (f := fun u w : ℂ => (w - u) ^ (d u))
        (fun u hu => differentiableAt_sub_zpow (hd_nonneg u))
    exact hD.differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) (R + ε)) := by
    intro z hz
    exact (hg_an z hz).differentiableAt.differentiableWithinAt
  have hPg_diff : DifferentiableOn ℂ (fun z => P z * g z) (ball (0 : ℂ) (R + ε)) :=
    DifferentiableOn.mul hP_diff hg_diff
  have hPg_an : AnalyticOnNhd ℂ (fun z => P z * g z) (ball (0 : ℂ) (R + ε)) :=
    hPg_diff.analyticOnNhd Metric.isOpen_ball
  have hfU : AnalyticOnNhd ℂ f (ball (0 : ℂ) (R + ε)) := by
    intro z hz
    exact hfdiff.analyticAt z
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (R + ε) := by
    simpa [dist_eq_norm] using (show 0 < R + ε by linarith)
  have hPg_eq_f0 : f =ᶠ[𝓝 (0 : ℂ)] (fun z => P z * g z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hRpos] with z hz
    have hzB : z ∈ closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hz
    simpa [P, d] using hfeqB z hzB
  have heq : Set.EqOn f (fun z => P z * g z) (ball (0 : ℂ) (R + ε)) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hfU hPg_an isPreconnected_ball h0 hPg_eq_f0
  refine ⟨g, ε, hεpos, hg_an, hg_nz, ?_⟩
  intro z hz
  exact heq hz





/-- logDeriv of a canonical factorisation at an interior point of the factorisation domain. -/
lemma logDeriv_decompose {f g : ℂ → ℂ} {R ε : ℝ}
    (hfdiff : Differentiable ℂ f)
    (hfac : ∀ z, z ∈ ball (0 : ℂ) (R + ε) →
      f z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u)) * g z)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) (R + ε)) (hfx : f x ≠ 0)
    (hgdiff : DifferentiableAt ℂ g x) (hg0 : g x ≠ 0) :
    logDeriv f x =
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u : ℤ) : ℂ) * (1 / (x - u))) +
        logDeriv g x := by
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u
  let P : ℂ → ℂ := fun z => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfB) u
  have hdx : d x = 0 := by
    dsimp [d]
    by_cases hxB : x ∈ closedBall (0 : ℂ) R
    · rw [MeromorphicOn.divisor_apply hfB.meromorphicOn hxB]
      have hord : meromorphicOrderAt f x = 0 :=
        Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfB x hxB) hfx
      simp [hord]
    · rw [MeromorphicOn.divisor_def]
      simp [hxB]
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
    exact differentiableAt_sub_zpow (hd_nonneg u)
  have hdiffP : DifferentiableAt ℂ P x := by
    rw [hP_fun]
    exact DifferentiableAt.fun_finsetProd (u := S) (f := fun u z : ℂ => (z - u) ^ (d u)) (x := x) hdiff
  have hfPg : f x = P x * g x := by
    simpa [P, d] using (hfac x hx)
  have hP0 : P x ≠ 0 := by
    intro hP0
    apply hfx
    rw [hfPg, hP0, zero_mul]
  have hPg_eq_f : (fun z : ℂ => P z * g z) =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    simpa [P, d] using (hfac z hz).symm
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
        simpa only [Finset.prod_fn] using logDeriv_prod (f := fun u z => (z - u) ^ (d u)) hfac0 hdiff
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
    exact logDeriv_mul x hP0 hg0 hdiffP hgdiff
  have hfin_sum : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (x - u))) =
      ∑ u ∈ S, ((d u : ℤ) : ℂ) * (1 / (x - u)) := by
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (x - u))) (s := S) ?_]
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


end Commons.NumberTheory.Linnik


noncomputable section

namespace Commons.NumberTheory.Linnik

lemma mem_sphere_zero_iff_norm' {R : ℝ} {z : ℂ} : z ∈ sphere (0 : ℂ) R ↔ ‖z‖ = R := by
  exact mem_sphere_zero_iff_norm

lemma sub_inv_mul_inv_add {z u s : ℂ} (hzu : z ≠ u) (hzs : z ≠ s) (hus : u ≠ s) :
    (z - u)⁻¹ * (s - z)⁻¹ = (s - u)⁻¹ * ((z - u)⁻¹ + (s - z)⁻¹) := by
  field_simp [sub_ne_zero.mpr hzu, sub_ne_zero.mpr hzs, sub_ne_zero.mpr hus]
  ring

lemma norm_ne_of_lt {z u : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hu : ‖u‖ < R) : z ≠ u := by
  intro h
  have : ‖u‖ = R := by simpa [h] using hz
  nlinarith

lemma norm_ne_of_lt' {s z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hs : ‖s‖ < R) : s ≠ z := by
  intro h
  have : ‖s‖ = R := by simpa [h] using hz
  nlinarith

lemma inv_sub_neg {a b : ℂ} : (b - a)⁻¹ = -((a - b)⁻¹) := by
  rw [← neg_sub (a := a) (b := b), inv_neg]

-- integral of the rational function around the circle is zero when both poles are inside
lemma circleIntegral_mul_sub_inv {u s : ℂ} {R : ℝ} (hRpos : 0 < R) (hu : ‖u‖ < R)
    (hs : ‖s‖ < R) (hne : u ≠ s) :
    (∮ z in C(0, R), (z - u)⁻¹ * (s - z)⁻¹) = 0 := by
  have hsphere_id : Set.EqOn (fun z : ℂ => (z - u)⁻¹ * (s - z)⁻¹)
      (fun z : ℂ => (s - u)⁻¹ * ((z - u)⁻¹ + (s - z)⁻¹)) (sphere (0 : ℂ) R) := by
    intro z hz
    have hzu : z ≠ u := norm_ne_of_lt (mem_sphere_zero_iff_norm.mp hz) hu
    have hzs : z ≠ s := norm_ne_of_lt (mem_sphere_zero_iff_norm.mp hz) hs
    exact sub_inv_mul_inv_add hzu hzs hne
  have h1 : (∮ z in C(0, R), (z - u)⁻¹ * (s - z)⁻¹) =
      (∮ z in C(0, R), (s - u)⁻¹ * ((z - u)⁻¹ + (s - z)⁻¹)) := by
    exact circleIntegral.integral_congr hRpos.le hsphere_id
  have h2 : (∮ z in C(0, R), (s - u)⁻¹ * ((z - u)⁻¹ + (s - z)⁻¹)) =
      (s - u)⁻¹ * (∮ z in C(0, R), (z - u)⁻¹ + (s - z)⁻¹) := by
    rw [circleIntegral.integral_const_mul]
  have hcA : ContinuousOn (fun z : ℂ => (z - u)⁻¹) (sphere (0 : ℂ) R) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.mpr (norm_ne_of_lt (mem_sphere_zero_iff_norm.mp hz) hu)
  have hcB : ContinuousOn (fun z : ℂ => (s - z)⁻¹) (sphere (0 : ℂ) R) := by
    refine (continuousOn_const.sub continuousOn_id).inv₀ ?_
    intro z hz
    exact sub_ne_zero.mpr (norm_ne_of_lt' (mem_sphere_zero_iff_norm.mp hz) hs)
  have h3 : (∮ z in C(0, R), (z - u)⁻¹ + (s - z)⁻¹) =
      (∮ z in C(0, R), (z - u)⁻¹) + (∮ z in C(0, R), (s - z)⁻¹) := by
    rw [circleIntegral.integral_add]
    exacts [(hcA.circleIntegrable hRpos.le), (hcB.circleIntegrable hRpos.le)]
  have huB : u ∈ ball (0 : ℂ) R := by simpa [dist_eq_norm] using hu
  have hsB : s ∈ ball (0 : ℂ) R := by simpa [dist_eq_norm] using hs
  have h4 : (∮ z in C(0, R), (z - u)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    exact circleIntegral.integral_sub_inv_of_mem_ball huB
  have h5 : (∮ z in C(0, R), (s - z)⁻¹) = -(2 * (Real.pi : ℂ) * Complex.I) := by
    have htemp : (∮ z in C(0, R), (z - s)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball hsB
    have hEqOn : Set.EqOn (fun z : ℂ => (s - z)⁻¹) (fun z : ℂ => -((z - s)⁻¹)) (sphere (0 : ℂ) R) := by
      intro z hz
      exact inv_sub_neg
    calc
      (∮ z in C(0, R), (s - z)⁻¹) = (∮ z in C(0, R), -((z - s)⁻¹)) := by
        exact circleIntegral.integral_congr hRpos.le hEqOn
      _ = -(∮ z in C(0, R), (z - s)⁻¹) := by
        have hneg : (fun z : ℂ => -((z - s)⁻¹)) = fun z : ℂ => (-1 : ℂ) * (z - s)⁻¹ := by
          funext z
          ring
        rw [hneg, circleIntegral.integral_const_mul]
        ring
      _ = -(2 * (Real.pi : ℂ) * Complex.I) := by rw [htemp]
  calc
    (∮ z in C(0, R), (z - u)⁻¹ * (s - z)⁻¹) = (s - u)⁻¹ * (∮ z in C(0, R), (z - u)⁻¹ + (s - z)⁻¹) := by
      rw [h1, h2]
    _ = (s - u)⁻¹ * ((2 * (Real.pi : ℂ) * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I))) := by
      rw [h3, h4, h5]
    _ = 0 := by ring

end Commons.NumberTheory.Linnik


namespace Commons.NumberTheory.Linnik

/-- If the divisor of an analytic `f` is non-zero at `u`, then `f u = 0`. -/
lemma f_zero_of_divisor_ne_zero {f : ℂ → ℂ} {R : ℝ}
    (hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) {u : ℂ}
    (hd : (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u ≠ 0) : f u = 0 := by
  by_contra hfz
  have huB : u ∈ closedBall (0 : ℂ) R := by
    by_contra hout
    rw [MeromorphicOn.divisor_def] at hd
    simp [hout] at hd
  have hord : meromorphicOrderAt f u = 0 :=
    Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfB u huB) hfz
  have hdiv : MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u = 0 := by
    rw [MeromorphicOn.divisor_apply hfB.meromorphicOn huB]
    simp [hord]
  exact hd hdiv

/-- Divisor support inside the circle lies strictly inside, when `f` has no zeros on the circle. -/
lemma divisor_support_lt_radius {f : ℂ → ℂ} {R : ℝ} (hRpos : 0 < R)
    (hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hfc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0) {u : ℂ}
    (hd : (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u ≠ 0) : ‖u‖ < R := by
  have huRle : ‖u‖ ≤ R := by
    by_contra hgt
    have hout : u ∉ closedBall (0 : ℂ) R := by
      simp [dist_eq_norm, not_le, hgt]
    rw [MeromorphicOn.divisor_def] at hd
    simp [hout] at hd
  have huRne : ‖u‖ ≠ R := by
    intro h
    exact (hfc u h) (f_zero_of_divisor_ne_zero hfB hd)
  exact lt_of_le_of_ne huRle huRne

/-- The logarithmic derivative of a nonvanishing analytic function is analytic. -/
lemma analyticOnNhd_logDeriv_of {g : ℂ → ℂ} {ρ : ℝ} (hg_an : AnalyticOnNhd ℂ g (ball (0 : ℂ) ρ))
    (hg_nz : ∀ z ∈ ball (0 : ℂ) ρ, g z ≠ 0) :
    AnalyticOnNhd ℂ (fun z => logDeriv g z) (ball (0 : ℂ) ρ) := by
  intro z hz
  have hder : AnalyticAt ℂ (deriv g) z := (hg_an z hz).deriv
  have hq : AnalyticAt ℂ (fun w : ℂ => deriv g w / g w) z :=
    AnalyticAt.div hder (hg_an z hz) (hg_nz z hz)
  convert hq using 1
  funext w
  rw [logDeriv_apply]



/-- log-derivative residue identity over a circle (generic version). -/
lemma logDeriv_circle_residue_of {f : ℂ → ℂ} {R : ℝ} (hRpos : 0 < R)
    (hfdiff : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {s : ℂ} (hsR : ‖s‖ < R) (hfs : f s ≠ 0)
    (hfc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0) :
    deriv f s / f s =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * (1 / (s - u))) -
      (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ => (deriv f w / f w) * (1 / (s - w))) (0 : ℂ) R) := by
  classical
  rcases factorization_open hRpos hfdiff hf0 hfc with ⟨g, ε, hεpos, hg_an, hg_nz, hfac⟩
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u
  have hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  let S : Finset ℂ := hsupp.toFinset
  have hd_ne_iff_memS : ∀ u : ℂ, d u ≠ 0 ↔ u ∈ S := by
    intro u
    simpa [S] using (hsupp.mem_toFinset : u ∈ hsupp.toFinset ↔ u ∈ support d)
  have hsB2 : s ∈ ball (0 : ℂ) (R + ε) := by
    have : ‖s‖ < R + ε := by linarith
    simpa [dist_eq_norm] using this
  have hgdiff_s : DifferentiableAt ℂ g s := (hg_an s hsB2).differentiableAt
  have hg0_s : g s ≠ 0 := hg_nz s hsB2
  have hdec_s := logDeriv_decompose (f := f) (g := g) (R := R) (ε := ε) hfdiff hfac hsB2 hfs
    hgdiff_s hg0_s
  have hsphere_dec : ∀ w : ℂ, ‖w‖ = R →
      logDeriv f w = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
          (1 / (w - u))) + logDeriv g w := by
    intro w hw
    have hxw : w ∈ ball (0 : ℂ) (R + ε) := by
      have : ‖w‖ < R + ε := by linarith
      simpa [dist_eq_norm] using this
    have hfxw : f w ≠ 0 := hfc w hw
    have hgdiff_w : DifferentiableAt ℂ g w := (hg_an w hxw).differentiableAt
    have hg0_w : g w ≠ 0 := hg_nz w hxw
    exact logDeriv_decompose (f := f) (g := g) (R := R) (ε := ε) hfdiff hfac hxw hfxw
      hgdiff_w hg0_w
  let hloggAn : AnalyticOnNhd ℂ (fun z => logDeriv g z) (ball (0 : ℂ) (R + ε)) :=
    analyticOnNhd_logDeriv_of hg_an hg_nz
  let F₁ : ℂ → ℂ := fun w => (deriv f w / f w) * (1 / (s - w))
  let F₂ : ℂ → ℂ := fun w => ((∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
      (1 / (w - u))) + logDeriv g w) * (1 / (s - w))
  let Afun : ℂ → ℂ := fun w => logDeriv g w * (s - w)⁻¹
  let Bfun : ℂ → ℂ := fun w => ∑ u ∈ S, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
      ((w - u)⁻¹ * (s - w)⁻¹)
  let F₄ : ℂ → ℂ := fun w => Afun w + Bfun w
  have hF12 : Set.EqOn F₁ F₂ (sphere (0 : ℂ) R) := by
    intro w hw
    dsimp [F₁, F₂]
    rw [← logDeriv_apply f w]
    rw [hsphere_dec w (mem_sphere_zero_iff_norm.mp hw)]
  have hfin : ∀ w : ℂ, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
      (1 / (w - u))) = ∑ u ∈ S, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
      (1 / (w - u)) := by
    intro w
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
      (1 / (w - u))) (s := S) ?_]
    · intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * (1 / (w - u)) = 0 := by
          dsimp [d] at hd0
          simp [hd0]
        exact hu this
      exact (hd_ne_iff_memS u).1 hd_ne
  have hF23 : Set.EqOn F₂ F₄ (sphere (0 : ℂ) R) := by
    intro w hw
    dsimp [F₂, F₄, Afun, Bfun]
    rw [hfin w]
    rw [add_mul]
    rw [Finset.sum_mul]
    have hY : logDeriv g w * (1 / (s - w)) = logDeriv g w * (s - w)⁻¹ := by ring
    have hX : (∑ u ∈ S, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
        (1 / (w - u)) * (1 / (s - w))) =
        (∑ u ∈ S, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
          ((w - u)⁻¹ * (s - w)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring
    rw [hY, hX]
    rw [add_comm]
  have hsinv_cont : ContinuousOn (fun w : ℂ => (s - w)⁻¹) (sphere (0 : ℂ) R) := by
    refine (continuousOn_const.sub continuousOn_id).inv₀ ?_
    intro w hw
    exact sub_ne_zero.mpr (norm_ne_of_lt' (mem_sphere_zero_iff_norm.mp hw) hsR)
  have hlogg_cont : ContinuousOn (fun w : ℂ => logDeriv g w) (sphere (0 : ℂ) R) := by
    intro w hw
    have hwR : ‖w‖ = R := mem_sphere_zero_iff_norm.mp hw
    have hxw : w ∈ ball (0 : ℂ) (R + ε) := by
      have : ‖w‖ < R + ε := by linarith
      simpa [dist_eq_norm] using this
    exact ((hloggAn w hxw).continuousAt).continuousWithinAt
  have hAcont : ContinuousOn Afun (sphere (0 : ℂ) R) := by
    dsimp [Afun]
    exact hlogg_cont.mul hsinv_cont
  have hA_int : CircleIntegrable Afun (0 : ℂ) R := hAcont.circleIntegrable hRpos.le
  have hterm_cont : ∀ u ∈ S, ContinuousOn
      (fun w : ℂ => (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
        ((w - u)⁻¹ * (s - w)⁻¹)) (sphere (0 : ℂ) R) := by
    intro u hu
    have huR : ‖u‖ < R := by
      have hd_ne : d u ≠ 0 := (hd_ne_iff_memS u).2 (by
        have huS : u ∈ (S : Set ℂ) := by simpa using hu
        simpa [S] using huS)
      exact divisor_support_lt_radius hRpos hfB hfc (by simpa [d] using hd_ne)
    have h1 : ContinuousOn (fun w : ℂ => (w - u)⁻¹) (sphere (0 : ℂ) R) := by
      refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
      intro w hw
      exact sub_ne_zero.mpr (norm_ne_of_lt (mem_sphere_zero_iff_norm.mp hw) huR)
    exact (continuousOn_const.mul (h1.mul hsinv_cont))
  have hBcont : ContinuousOn Bfun (sphere (0 : ℂ) R) := by
    dsimp [Bfun]
    exact continuousOn_finset_sum S hterm_cont
  have hB_int : CircleIntegrable Bfun (0 : ℂ) R := hBcont.circleIntegrable hRpos.le
  have hterm_int : ∀ u ∈ S, CircleIntegrable
      (fun w : ℂ => (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
        ((w - u)⁻¹ * (s - w)⁻¹)) (0 : ℂ) R := by
    intro u hu
    exact (hterm_cont u hu).circleIntegrable hRpos.le
  -- value of A: the Cauchy contribution
  have hdlogg : DifferentiableOn ℂ (fun w => logDeriv g w) (closedBall (0 : ℂ) R) := by
    intro z hz
    have hzball : z ∈ ball (0 : ℂ) (R + ε) := by
      have hzR : ‖z‖ ≤ R := by simpa [dist_eq_norm] using hz
      have : ‖z‖ < R + ε := by linarith
      simpa [dist_eq_norm] using this
    exact ((hloggAn z hzball).differentiableAt).differentiableWithinAt
  have hs_ball : s ∈ ball (0 : ℂ) R := by simpa [dist_eq_norm] using hsR
  have hcv_raw := DifferentiableOn.circleIntegral_sub_inv_smul (f := fun w => logDeriv g w)
    (c := (0 : ℂ)) (R := R) (w := s) hdlogg hs_ball
  have hcv : (∮ z in C(0, R), logDeriv g z * (z - s)⁻¹) = (2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by
    have hconv : Set.EqOn (fun z : ℂ => logDeriv g z * (z - s)⁻¹)
        (fun z : ℂ => (z - s)⁻¹ • logDeriv g z) (sphere (0 : ℂ) R) := by
      intro z hz
      change logDeriv g z * (z - s)⁻¹ = (z - s)⁻¹ • logDeriv g z
      rw [smul_eq_mul]
      ring
    calc
      (∮ z in C(0, R), logDeriv g z * (z - s)⁻¹) = (∮ z in C(0, R), (z - s)⁻¹ • logDeriv g z) := by
        exact circleIntegral.integral_congr hRpos.le hconv
      _ = (2 * (Real.pi : ℂ) * Complex.I) • logDeriv g s := hcv_raw
      _ = (2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by rw [smul_eq_mul]
  have hAval : (∮ z in C(0, R), Afun z) = -(2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by
    dsimp [Afun]
    calc
      (∮ z in C(0, R), logDeriv g z * (s - z)⁻¹) = (∮ z in C(0, R), -(logDeriv g z * (z - s)⁻¹)) := by
        refine circleIntegral.integral_congr hRpos.le ?_
        intro z hz
        change logDeriv g z * (s - z)⁻¹ = -(logDeriv g z * (z - s)⁻¹)
        rw [inv_sub_neg]
        ring
      _ = -(∮ z in C(0, R), logDeriv g z * (z - s)⁻¹) := by
        have hneg : (fun z : ℂ => -(logDeriv g z * (z - s)⁻¹)) =
            fun z : ℂ => (-1 : ℂ) * (logDeriv g z * (z - s)⁻¹) := by
          funext z
          ring
        rw [hneg, circleIntegral.integral_const_mul]
        ring
      _ = -(2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by
        rw [hcv]
        ring
  have hBval : (∮ z in C(0, R), Bfun z) = 0 := by
    dsimp [Bfun]
    rw [circleIntegral.integral_fun_sum hterm_int]
    apply Finset.sum_eq_zero
    intro u hu
    have huR : ‖u‖ < R := by
      have hd_ne : d u ≠ 0 := (hd_ne_iff_memS u).2 (by
        have huS : u ∈ (S : Set ℂ) := by simpa using hu
        simpa [S] using huS)
      exact divisor_support_lt_radius hRpos hfB hfc (by simpa [d] using hd_ne)
    have hdu : (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u ≠ 0 := by
      simpa [d] using (hd_ne_iff_memS u).2 (by
        have huS : u ∈ (S : Set ℂ) := by simpa using hu
        simpa [S] using huS)
    have hfu0 : f u = 0 := f_zero_of_divisor_ne_zero hfB hdu
    have hus : u ≠ s := by
      intro h
      apply hfs
      rw [← h]
      exact hfu0
    calc
      (∮ z in C(0, R), (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
          ((z - u)⁻¹ * (s - z)⁻¹)) =
          (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) *
            (∮ z in C(0, R), (z - u)⁻¹ * (s - z)⁻¹) := by
        rw [circleIntegral.integral_const_mul]
      _ = (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * 0 := by
        congr 1
        exact circleIntegral_mul_sub_inv (u := u) (s := s) hRpos huR hsR hus
      _ = 0 := by simp
  have hJ : (∮ z in C(0, R), F₁ z) = -(2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by
    calc
      (∮ z in C(0, R), F₁ z) = (∮ z in C(0, R), F₂ z) := by
        exact circleIntegral.integral_congr hRpos.le hF12
      _ = (∮ z in C(0, R), F₄ z) := by
        exact circleIntegral.integral_congr hRpos.le hF23
      _ = (∮ z in C(0, R), Afun z) + (∮ z in C(0, R), Bfun z) := by
        dsimp [F₄]
        rw [circleIntegral.integral_add hA_int hB_int]
      _ = -(2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s + 0 := by rw [hAval, hBval]
      _ = -(2 * (Real.pi : ℂ) * Complex.I) * logDeriv g s := by simp
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast (Real.pi_ne_zero : Real.pi ≠ 0))) Complex.I_ne_zero
  have hsmul : ((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • (∮ z in C(0, R), F₁ z) = -logDeriv g s := by
    rw [hJ]
    rw [smul_eq_mul]
    field_simp [hne]
  calc
    deriv f s / f s = logDeriv f s := (logDeriv_apply f s).symm
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * (1 / (s - u))) +
        logDeriv g s := hdec_s
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * (1 / (s - u))) -
        (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • (∮ z in C(0, R), F₁ z)) := by
      rw [hsmul]
      ring




/-- log-derivative circle residue identity for the completed Dirichlet L-function. -/
theorem logDeriv_circle_residue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s : ℂ) (R : ℝ)
    (hRpos : 0 < R) (hsR : ‖s‖ < R)
    (hΛs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u))) -
      (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ =>
          (deriv (DirichletCharacter.completedLFunction χ) w /
            DirichletCharacter.completedLFunction χ w) * (1 / (s - w))) 0 R) := by
  let f : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hfdiff : Differentiable ℂ f := by
    dsimp [f]
    exact DirichletCharacter.differentiable_completedLFunction hχ
  have hf0 : f 0 ≠ 0 := by
    dsimp [f]
    exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  have hfs : f s ≠ 0 := by simpa [f] using hΛs
  have hfc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0 := by
    intro w hw
    simpa [f] using hcirc w hw
  have h := logDeriv_circle_residue_of (f := f) (R := R) hRpos hfdiff hf0 (s := s) hsR hfs hfc
  simpa [f] using h

end Commons.NumberTheory.Linnik
