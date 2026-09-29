import Mathlib
import Submission.Work.C17g.changeOrigin_ofScalars
import Submission.Work.C17g.binomial_tonelli

/-! # Vivanti–Pringsheim (generic form)

A power series with nonnegative coefficients converging on `|z| < R`, whose sum extends
holomorphically to a neighbourhood of `z = R`, converges on a larger disc.

The proof is the classical one.  Pick `r₀ = R - ε` with `ε = min (R/2) (δ/4)`, so that the disc
`ball r₀ (δ/2)` is contained in `ball R δ` and `ball r₀ ε ⊆ ball 0 R ∩ ball R δ`.  The glued
function is holomorphic on `ball r₀ (δ/2)`, so by Cauchy's theorem (`Complex.hasSum_taylorSeries_on_ball`)
its Taylor series at `r₀` converges on `ball r₀ (δ/2)`.  The `k`-th Taylor coefficient is the
`k`-th coefficient of the re-expansion of the power series at `r₀`, which by
`changeOrigin_ofScalars` equals `∑ₗ C(k+l,l) f(k+l) r₀ˡ ≥ 0`; and `Complex.hasSum_taylorSeries_on_ball`
shows that this series, evaluated at `t = (ε + δ/2)/2`, converges.  Since all terms are
nonnegative, Tonelli's theorem (`binomial_tonelli`) then gives convergence of `∑ₙ f(n) (r₀+t)ⁿ`
with `r₀ + t > R`.
-/

open Complex Metric
open scoped NNReal ENNReal BigOperators

namespace Work.C17g

theorem pringsheim (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (R : ℝ) (hR : 0 < R)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < R → Summable fun n => f n * r ^ n)
    (g : ℂ → ℂ) (δ : ℝ) (hδ : 0 < δ) (hg : DifferentiableOn ℂ g (ball (R : ℂ) δ))
    (hfg : ∀ z ∈ ball (R : ℂ) δ ∩ ball (0 : ℂ) R, HasSum (fun n => (f n : ℂ) * z ^ n) (g z)) :
    ∃ ρ : ℝ, R < ρ ∧ Summable fun n => f n * ρ ^ n := by
  -- ## the parameters
  set ε : ℝ := min (R / 2) (δ / 4) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεleR : ε ≤ R / 2 := min_le_left _ _
  have hεleδ : ε ≤ δ / 4 := min_le_right _ _
  have hεltδ : ε < δ / 2 := by linarith
  set r₀ : ℝ := R - ε with hr₀def
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; linarith
  have hr₀R : r₀ < R := by rw [hr₀def]; linarith
  have hRr₀ : R - r₀ = ε := by rw [hr₀def]; ring
  set t : ℝ := (ε + δ / 2) / 2 with htdef
  have htpos : 0 < t := by rw [htdef]; linarith
  have hεt : ε < t := by rw [htdef]; linarith
  have htlt : t < δ / 2 := by rw [htdef]; linarith
  have hRt : R < r₀ + t := by rw [hr₀def]; linarith
  refine ⟨r₀ + t, hRt, ?_⟩
  -- ## norms of real numbers viewed in `ℂ`
  have hnorm_real : ∀ a : ℝ, ‖((a : ℝ) : ℂ)‖ = |a| := fun a => by simp
  -- ## the power series with coefficients `c n = f n`
  set c : ℕ → ℂ := fun n => (f n : ℂ) with hcdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hpdef
  have hcnorm : ∀ n, ‖p n‖ = f n := by
    intro n
    rw [hpdef, FormalMultilinearSeries.ofScalars_norm, hcdef]
    simp [abs_of_nonneg (hf n)]
  have hrad : ENNReal.ofReal R ≤ p.radius := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hR.le]
    refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
    rw [ENNReal.coe_lt_coe] at hr
    have hr' : (r : ℝ) < R := by exact_mod_cast hr
    refine FormalMultilinearSeries.le_radius_of_summable p ?_
    simp only [hcnorm]
    exact hsum (r : ℝ) r.2 hr'
  have hpos : 0 < ENNReal.ofReal R := ENNReal.ofReal_pos.mpr hR
  have hF : HasFPowerSeriesOnBall p.sum p 0 (ENNReal.ofReal R) :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall p (lt_of_lt_of_le hpos hrad)).mono hpos hrad
  have hsum_eq : ∀ z : ℂ, p.sum z = ∑' n, c n * z ^ n := by
    intro z
    rw [FormalMultilinearSeries.sum, hpdef]
    exact tsum_congr (fun n => by rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul])
  -- ## change of origin to `r₀`
  have hrr : (↑‖(r₀ : ℂ)‖₊ : ENNReal) = ENNReal.ofReal r₀ := by
    have hnorm : ‖(r₀ : ℂ)‖ = r₀ := by
      rw [show ‖(r₀ : ℂ)‖ = |r₀| from by simp, abs_of_nonneg hr₀pos.le]
    have h1 : (‖(r₀ : ℂ)‖₊ : NNReal) = r₀.toNNReal := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ hr₀pos.le]
      simpa using hnorm
    rw [h1, ENNReal.ofReal]
  have hradq : ENNReal.ofReal R - (↑‖(r₀ : ℂ)‖₊ : ENNReal) = ENNReal.ofReal (R - r₀) := by
    rw [hrr, ← ENNReal.ofReal_sub R hr₀pos.le]
  have hlt : (↑‖(r₀ : ℂ)‖₊ : ENNReal) < ENNReal.ofReal R := by
    rw [hrr, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr₀pos.le]
    exact hr₀R
  have hq : HasFPowerSeriesOnBall p.sum (p.changeOrigin (r₀ : ℂ)) (r₀ : ℂ)
      (ENNReal.ofReal (R - r₀)) := by
    have h := hF.changeOrigin (y := (r₀ : ℂ)) hlt
    rw [zero_add, hradq] at h
    exact h
  have hdistR : dist (r₀ : ℂ) (R : ℂ) = ε := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, hnorm_real, abs_sub_comm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ R - r₀)]
    exact hRr₀
  have hdist0 : dist (r₀ : ℂ) (0 : ℂ) = r₀ := by
    rw [dist_eq_norm, sub_zero, hnorm_real, abs_of_nonneg hr₀pos.le]
  -- ## gluing: the disc is contained in the intersection where the two functions agree
  have hqg : HasFPowerSeriesOnBall g (p.changeOrigin (r₀ : ℂ)) (r₀ : ℂ)
      (ENNReal.ofReal (R - r₀)) := by
    refine hq.congr fun z hz => ?_
    rw [Metric.mem_eball] at hz
    have hzε : dist z (r₀ : ℂ) < ε := by
      have h := edist_lt_ofReal.mp hz
      rwa [hRr₀] at h
    have h1 : dist z (0 : ℂ) < R := by
      calc dist z (0 : ℂ) ≤ dist z (r₀ : ℂ) + dist (r₀ : ℂ) (0 : ℂ) := dist_triangle _ _ _
        _ < ε + r₀ := by rw [hdist0]; linarith
        _ = R := by rw [hr₀def]; ring
    have h2 : dist z (R : ℂ) < δ := by
      calc dist z (R : ℂ) ≤ dist z (r₀ : ℂ) + dist (r₀ : ℂ) (R : ℂ) := dist_triangle _ _ _
        _ < ε + ε := by rw [hdistR]; linarith
        _ ≤ δ := by linarith
    rw [hsum_eq z, hcdef]
    exact (hfg z ⟨h2, h1⟩).tsum_eq
  -- ## the Taylor coefficients of `g` at `r₀`
  have hcoeff : ∀ k : ℕ, (p.changeOrigin (r₀ : ℂ)) k (fun _ => 1)
      = (k.factorial : ℂ)⁻¹ * iteratedDeriv k g r₀ := by
    intro k
    have hs := HasFPowerSeriesOnBall.factorial_smul hqg (y := (1 : ℂ)) k
    rw [nsmul_eq_mul] at hs
    have hne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hs, inv_mul_cancel_left₀ hne]
  -- ## the Taylor series of `g` at `r₀` converges at `ρ = r₀ + t`
  have hgd : DifferentiableOn ℂ g (ball (r₀ : ℂ) (δ / 2)) := by
    refine hg.mono fun z hz => ?_
    rw [mem_ball] at hz ⊢
    calc dist z (R : ℂ) ≤ dist z (r₀ : ℂ) + dist (r₀ : ℂ) (R : ℂ) := dist_triangle _ _ _
      _ = dist z (r₀ : ℂ) + ε := by rw [hdistR]
      _ < δ / 2 + δ / 2 := by linarith [hεltδ]
      _ = δ := by ring
  have hzt : ((r₀ + t : ℝ) : ℂ) ∈ ball (r₀ : ℂ) (δ / 2) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, add_sub_cancel_left, hnorm_real,
      abs_of_nonneg htpos.le]
    exact htlt
  have hgtay := Complex.hasSum_taylorSeries_on_ball (f := g) (c := (r₀ : ℂ)) (r := δ / 2)
    hgd (z := ((r₀ + t : ℝ) : ℂ)) hzt
  have hqsum : Summable fun k => ((p.changeOrigin (r₀ : ℂ)) k (fun _ => 1)) * t ^ k := by
    refine hgtay.summable.congr fun k => ?_
    rw [hcoeff k]
    simp only [Complex.ofReal_add, add_sub_cancel_left]
    ring
  -- ## the coefficients are nonnegative reals, given by the binomial formula
  set d : ℕ → ℝ := fun k => ∑' l, ((k + l).choose l : ℝ) * f (k + l) * r₀ ^ l with hddef
  have hx₀ : (↑‖(r₀ : ℂ)‖₊ : ENNReal) < p.radius := lt_of_lt_of_le hlt hrad
  have hform : ∀ k : ℕ, HasSum (fun l : ℕ => ((k + l).choose l : ℂ) * c (k + l) * (r₀ : ℂ) ^ l)
      ((p.changeOrigin (r₀ : ℂ)) k (fun _ => 1)) := by
    intro k
    rw [hpdef]
    exact changeOrigin_ofScalars c hx₀
  have hterm : ∀ k l : ℕ, ((k + l).choose l : ℂ) * c (k + l) * (r₀ : ℂ) ^ l
      = ((((k + l).choose l : ℝ) * f (k + l) * r₀ ^ l : ℝ) : ℂ) := by
    intro k l
    simp [hcdef, Complex.ofReal_mul, Complex.ofReal_pow]
  have hinner : ∀ k, Summable fun l => ((k + l).choose l : ℝ) * f (k + l) * r₀ ^ l := by
    intro k
    rw [← Complex.summable_ofReal]
    exact ((hform k).summable).congr fun l => hterm k l
  have hqeq : ∀ k, (p.changeOrigin (r₀ : ℂ)) k (fun _ => 1) = (d k : ℂ) := by
    intro k
    rw [hddef, ← (hform k).tsum_eq, Complex.ofReal_tsum]
    exact tsum_congr fun l => hterm k l
  have hout : Summable fun k => d k * t ^ k := by
    rw [← Complex.summable_ofReal]
    exact hqsum.congr fun k => by rw [hqeq k, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- ## Tonelli + binomial
  exact binomial_tonelli f hf hr₀pos.le htpos.le hinner (by simpa only [hddef] using hout)

end Work.C17g
