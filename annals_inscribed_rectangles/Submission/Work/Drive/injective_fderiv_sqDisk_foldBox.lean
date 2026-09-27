import Mathlib
import Submission.Work.Drive.planeChain

/-!
# The folded square-to-disk parametrisation is an immersion on the open square

`Work.Drive.sqDisk` (`Submission/Work/Drive/squareDisk.lean`) is the classical square-to-disk map

> `sqDisk y = (a·√(1 − b²/2), b·√(1 − a²/2))`,  `a = 2 y 0 − 1`,  `b = 2 y 1 − 1`,

cut off by a smooth bump so that it is `C^∞` on all of `ℝ²`, and `Work.Drive.foldBox` folds the two
plane coordinates into `[0,1]` by `foldFun x = (1 − cos (π x))/2`.  This file proves that the
composite `sqDisk ∘ foldBox` is an **immersion at every point of the open square** `(0,1)²`:

`Work.Drive.injective_fderiv_sqDisk_foldBox`,
`fderiv ℝ (sqDisk ∘ foldBox) y` is injective for `y 0, y 1 ∈ (0,1)`.

This is the second factor of the chain rule `mfderiv (cls ∘ diskPlane Q) y = (mfderiv (cls ∘ Q)
(sqDisk (foldBox y))) ∘ mfderiv (sqDisk ∘ foldBox) y` of `Submission/Work/Drive/diskPlane_mfderiv.lean`
(`Work.Drive.injective_mfderiv_cls_diskPlane`).

The two ingredients of the derivative at an interior point `y` of the square are

* `d/dt (2·foldFun (y 0 + t u 0) − 1)|₀ = π sin (π y 0) · u 0`, and `π sin (π y 0) > 0` because
  `0 < y 0 < 1` (`foldFun` is strictly increasing on `(0,1)`), and
* the Jacobian of `sqDisk` in the square coordinates `(a, b)`,
  `det = 4 w(a)² w(b)² − a²b² = 2(2 − a² − b²)` with `w(x) = sqWeight x = √(1 − x²/2)`, which is
  positive for `a², b² < 1`.

So the derivative is injective, with determinant `(π sin (π y 0))(π sin (π y 1))·2(2 − a² − b²) > 0`.

The derivative is computed by restricting to the line `t ↦ y + t • u`:  the composite at `t` is
`g (y + t•u) = A t · w (B t) + i · B t · w (A t)` with `A t = 2 foldFun (y 0 + t u 0) − 1` and
`B t = 2 foldFun (y 1 + t u 1) − 1`; the two real equations obtained from
`fderiv ℝ g y u = 0` (`rval = 0`, `sval = 0`) then multiply to
`4 c₀c₁ u₀u₁ (1 − a²/2)(1 − b²/2) = a²b² c₀c₁ u₀u₁`, i.e. `2 c₀c₁ u₀u₁ (2 − a² − b²) = 0`, and the
coefficient is non-zero, so `u 0 = u 1 = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- Composing a real-valued `HasDerivAt` with a continuous linear map. -/
lemma hasDerivAt_clm_comp' {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ → F} {f' : F} {x : ℝ} (L : F →L[ℝ] G)
    (h : HasDerivAt f f' x) : HasDerivAt (fun t => L (f t)) (L f') x := by
  have h1 := (L.hasFDerivAt.comp x h.hasFDerivAt).hasDerivAt
  simpa [Function.comp_def, fderiv_apply_one_eq_deriv] using h1

lemma mk2_zero' : mk2 (0 : ℝ) 0 = (0 : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;> simp [mk2]

/-- The fold `foldFun x = (1 − cos (π x))/2` is strictly increasing on `(0,1)`: it maps that interval
into itself. -/
lemma foldFun_mem_Ioo' {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    foldFun x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hπ0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx.1
  have hπ1 : Real.pi * x < Real.pi := by nlinarith [hx.2, Real.pi_pos]
  have hc_lt1 : Real.cos (Real.pi * x) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := Real.pi * x) le_rfl
      (le_of_lt hπ1) hπ0
    simpa using this
  have hc_gt : -1 < Real.cos (Real.pi * x) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi * x) (y := Real.pi)
      (le_of_lt hπ0) le_rfl hπ1
    simpa using this
  unfold foldFun
  exact ⟨by linarith, by linarith⟩

/-- The derivative of the fold: `foldFun' = π sin (π ·)/2`. -/
lemma foldFun_hasDerivAt' (x : ℝ) :
    HasDerivAt foldFun (Real.pi * Real.sin (Real.pi * x) / 2) x := by
  have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi x := by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have h1 := (Real.hasDerivAt_cos (Real.pi * x)).comp x hlin
  simp only [Function.comp_def] at h1
  have h2 := ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub h1).div_const 2
  unfold foldFun
  convert h2 using 1 <;> (first | rfl | ring)

/-- The derivative of the smooth weight `sqWeight`: on `(-1,1)` it is `−b/(2√(1−b²/2))`, written
with `sqWeight` itself. -/
lemma sqWeight_hasDerivAt' {b : ℝ} (hb : |b| < 1) :
    HasDerivAt sqWeight (-b / (2 * sqWeight b)) b := by
  have hev : (fun x : ℝ => sqWeight x) =ᶠ[nhds b] (fun x => Real.sqrt (1 - x ^ 2 / 2)) := by
    have h1 : ∀ᶠ x : ℝ in nhds b, |x| < 1 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hb
    filter_upwards [h1] with x hx
    rw [sqWeight, sqBump_apply_eq_one (le_of_lt hx), one_mul]
  have hne : 1 - b ^ 2 / 2 ≠ 0 := by
    have hb2 : b ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg b) hb (by norm_num)
    linarith
  have h2 : HasDerivAt (fun x : ℝ => 1 - x ^ 2 / 2) (-b) b := by
    have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2) b b := by
      have h0 := (hasDerivAt_pow 2 b).div_const 2
      exact h0.congr_deriv (by ring)
    have h1 := h.const_sub (1 : ℝ)
    exact h1.congr_deriv (by ring)
  have h3 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2 / 2))
      (-b / (2 * Real.sqrt (1 - b ^ 2 / 2))) b := h2.sqrt hne
  rw [← sqWeight_eq_sqrt (le_of_lt hb)] at h3
  exact h3.congr_of_eventuallyEq hev

/-- **The folded square-to-disk parametrisation is an immersion on the open square.**
For `y` with `0 < y 0 < 1` and `0 < y 1 < 1`, the derivative of `sqDisk ∘ foldBox` at `y` is
injective.  (Its determinant is `π sin (π y 0) · π sin (π y 1) · 2(2 − a² − b²)` with
`a = 2 foldFun (y 0) − 1`, `b = 2 foldFun (y 1) − 1`, which is positive at an interior point.) -/
theorem injective_fderiv_sqDisk_foldBox (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.sqDisk (Work.Drive.foldBox y)) y) := by
  set g : EuclideanSpace ℝ (Fin 2) → ℂ := fun z => sqDisk (foldBox z) with hg_def
  have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    sqDisk_contDiff.comp (contDiff_iff_contDiffAt.mpr fun z =>
      contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff z))
  have hgdiff : DifferentiableAt ℝ g y := (hcont.contDiffAt).differentiableAt (by simp)
  have key : ∀ u : EuclideanSpace ℝ (Fin 2), fderiv ℝ g y u = 0 → u = 0 := by
    intro u hu
    set a : ℝ := 2 * foldFun (y 0) - 1 with ha_def
    set b : ℝ := 2 * foldFun (y 1) - 1 with hb_def
    set c0 : ℝ := Real.pi * Real.sin (Real.pi * (y 0)) / 2 with hc0_def
    set c1 : ℝ := Real.pi * Real.sin (Real.pi * (y 1)) / 2 with hc1_def
    have hy0' := foldFun_mem_Ioo' h0
    have hy1' := foldFun_mem_Ioo' h1
    have ha1 : |a| < 1 := by
      rw [ha_def]
      exact abs_lt.mpr ⟨by linarith [hy0'.1], by linarith [hy0'.2]⟩
    have hb1 : |b| < 1 := by
      rw [hb_def]
      exact abs_lt.mpr ⟨by linarith [hy1'.1], by linarith [hy1'.2]⟩
    have hc0 : 0 < c0 := by
      rw [hc0_def]
      have hπ0 : 0 < Real.pi * (y 0) := mul_pos Real.pi_pos h0.1
      have hπ1 : Real.pi * (y 0) < Real.pi := by nlinarith [h0.2, Real.pi_pos]
      have := Real.sin_pos_of_pos_of_lt_pi hπ0 hπ1
      positivity
    have hc1 : 0 < c1 := by
      rw [hc1_def]
      have hπ0 : 0 < Real.pi * (y 1) := mul_pos Real.pi_pos h1.1
      have hπ1 : Real.pi * (y 1) < Real.pi := by nlinarith [h1.2, Real.pi_pos]
      have := Real.sin_pos_of_pos_of_lt_pi hπ0 hπ1
      positivity
    -- the derivative of `g` along the line `t ↦ y + t • u`
    have hcomp0 : HasDerivAt (fun t : ℝ => g (y + t • u)) 0 0 := by
      have hline : HasDerivAt (fun t : ℝ => y + t • u) u 0 := by
        have h := (hasDerivAt_id (0 : ℝ)).smul_const u
        have h2 := h.const_add y
        exact h2.congr_deriv (by simp)
      have hh : HasFDerivAt g (fderiv ℝ g y) (y + (0 : ℝ) • u) := by
        simpa using hgdiff.hasFDerivAt
      have h := hh.comp_hasDerivAt 0 hline
      simp only [Function.comp_def] at h
      simpa [hu] using h
    set A : ℝ → ℝ := fun t => 2 * foldFun (y 0 + t * u 0) - 1 with hA_def
    set B : ℝ → ℝ := fun t => 2 * foldFun (y 1 + t * u 1) - 1 with hB_def
    have hA0 : A 0 = a := by rw [hA_def, ha_def]; simp
    have hB0 : B 0 = b := by rw [hB_def, hb_def]; simp
    have hA : HasDerivAt A (2 * (c0 * (u 0))) 0 := by
      rw [hA_def]
      have hlin : HasDerivAt (fun t : ℝ => y 0 + t * u 0) (u 0) 0 := by
        have h := ((hasDerivAt_id (0 : ℝ)).mul_const (u 0)).const_add (y 0)
        exact h.congr_deriv (by ring)
      have hpt : (fun t : ℝ => y 0 + t * u 0) 0 = y 0 := by simp
      have hfold : HasDerivAt foldFun (Real.pi * Real.sin (Real.pi * (y 0)) / 2)
          ((fun t : ℝ => y 0 + t * u 0) 0) := by
        rw [hpt]
        exact foldFun_hasDerivAt' (y 0)
      have hf : HasDerivAt (foldFun ∘ fun t : ℝ => y 0 + t * u 0)
          ((Real.pi * Real.sin (Real.pi * (y 0)) / 2) * (u 0)) 0 := hfold.comp 0 hlin
      have hf' : HasDerivAt (foldFun ∘ fun t : ℝ => y 0 + t * u 0) (c0 * (u 0)) 0 :=
        hf.congr_deriv (by rw [hc0_def])
      have h2 := (hf'.const_mul 2).sub_const 1
      simpa only [Function.comp_def] using h2
    have hB : HasDerivAt B (2 * (c1 * (u 1))) 0 := by
      rw [hB_def]
      have hlin : HasDerivAt (fun t : ℝ => y 1 + t * u 1) (u 1) 0 := by
        have h := ((hasDerivAt_id (0 : ℝ)).mul_const (u 1)).const_add (y 1)
        exact h.congr_deriv (by ring)
      have hpt : (fun t : ℝ => y 1 + t * u 1) 0 = y 1 := by simp
      have hfold : HasDerivAt foldFun (Real.pi * Real.sin (Real.pi * (y 1)) / 2)
          ((fun t : ℝ => y 1 + t * u 1) 0) := by
        rw [hpt]
        exact foldFun_hasDerivAt' (y 1)
      have hf : HasDerivAt (foldFun ∘ fun t : ℝ => y 1 + t * u 1)
          ((Real.pi * Real.sin (Real.pi * (y 1)) / 2) * (u 1)) 0 := hfold.comp 0 hlin
      have hf' : HasDerivAt (foldFun ∘ fun t : ℝ => y 1 + t * u 1) (c1 * (u 1)) 0 :=
        hf.congr_deriv (by rw [hc1_def])
      have h2 := (hf'.const_mul 2).sub_const 1
      simpa only [Function.comp_def] using h2
    set rval : ℝ := 2 * c0 * (u 0) * sqWeight b
      + a * (-b / (2 * sqWeight b) * (2 * (c1 * (u 1)))) with hrval_def
    set sval : ℝ := 2 * c1 * (u 1) * sqWeight a
      + b * (-a / (2 * sqWeight a) * (2 * (c0 * (u 0)))) with hsval_def
    -- the two real coordinates of the line derivative
    have hR : HasDerivAt (fun t : ℝ => A t * sqWeight (B t)) rval 0 := by
      rw [hrval_def]
      have hsq := sqWeight_hasDerivAt' hb1
      rw [← hB0] at hsq
      have hW : HasDerivAt (fun t : ℝ => sqWeight (B t))
          ((-b / (2 * sqWeight b)) * (2 * (c1 * (u 1)))) 0 := by
        have h := hsq.comp 0 hB
        simpa only [Function.comp_def, hB0] using h
      have h := hA.mul hW
      refine h.congr_deriv ?_
      rw [hA0, hB0]
      ring
    have hS : HasDerivAt (fun t : ℝ => B t * sqWeight (A t)) sval 0 := by
      rw [hsval_def]
      have hsq := sqWeight_hasDerivAt' ha1
      rw [← hA0] at hsq
      have hW : HasDerivAt (fun t : ℝ => sqWeight (A t))
          ((-a / (2 * sqWeight a)) * (2 * (c0 * (u 0)))) 0 := by
        have h := hsq.comp 0 hA
        simpa only [Function.comp_def, hA0] using h
      have h := hB.mul hW
      refine h.congr_deriv ?_
      rw [hB0, hA0]
      ring
    have hcompRS : HasDerivAt
        (fun t : ℝ => ((A t * sqWeight (B t) : ℝ) : ℂ)
          + ((B t * sqWeight (A t) : ℝ) : ℂ) * Complex.I)
        (((rval : ℝ) : ℂ) + ((sval : ℝ) : ℂ) * Complex.I) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => ((A t * sqWeight (B t) : ℝ) : ℂ))
          ((rval : ℝ) : ℂ) 0 := by
        simpa only [Complex.ofRealCLM_apply] using hasDerivAt_clm_comp' Complex.ofRealCLM hR
      have h2 : HasDerivAt (fun t : ℝ => ((B t * sqWeight (A t) : ℝ) : ℂ) * Complex.I)
          (((sval : ℝ) : ℂ) * Complex.I) 0 := by
        simpa only [Complex.ofRealCLM_apply] using
          (hasDerivAt_clm_comp' Complex.ofRealCLM hS).mul_const Complex.I
      exact h1.add h2
    have hfun : (fun t : ℝ => ((A t * sqWeight (B t) : ℝ) : ℂ)
          + ((B t * sqWeight (A t) : ℝ) : ℂ) * Complex.I) = fun t : ℝ => g (y + t • u) := by
      funext t
      simp only [hg_def, hA_def, hB_def]
      apply Complex.ext
      · simp [sqDisk_apply_re, foldBox]
      · simp [sqDisk_apply_im, foldBox]
    have hcompRS0 : HasDerivAt (fun t : ℝ => g (y + t • u))
        (((rval : ℝ) : ℂ) + ((sval : ℝ) : ℂ) * Complex.I) 0 :=
      hcompRS.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)
    have heq := hcomp0.unique hcompRS0
    have hrval : rval = 0 := by
      have := congrArg Complex.re heq
      simpa using this.symm
    have hsval : sval = 0 := by
      have := congrArg Complex.im heq
      simpa using this.symm
    have hwb : sqWeight b ^ 2 = 1 - b ^ 2 / 2 := sqWeight_sq (le_of_lt hb1)
    have hwa : sqWeight a ^ 2 = 1 - a ^ 2 / 2 := sqWeight_sq (le_of_lt ha1)
    have hwbne : sqWeight b ≠ 0 := ne_of_gt (sqWeight_pos (le_of_lt hb1))
    have hwane : sqWeight a ≠ 0 := ne_of_gt (sqWeight_pos (le_of_lt ha1))
    -- the two equations, cleared of denominators
    have hr : 2 * c0 * (u 0) * sqWeight b
        + a * (-b / (2 * sqWeight b) * (2 * (c1 * (u 1)))) = 0 := by
      rw [← hrval_def]
      exact hrval
    have hs : 2 * c1 * (u 1) * sqWeight a
        + b * (-a / (2 * sqWeight a) * (2 * (c0 * (u 0)))) = 0 := by
      rw [← hsval_def]
      exact hsval
    have E1 : 2 * c0 * (u 0) * (1 - b ^ 2 / 2) = a * b * (c1 * (u 1)) := by
      have hkey : (2 * c0 * (u 0) * sqWeight b
            + a * (-b / (2 * sqWeight b) * (2 * (c1 * (u 1))))) * (2 * sqWeight b) = 0 := by
        rw [hr, zero_mul]
      have hcalc : (2 * c0 * (u 0) * sqWeight b
            + a * (-b / (2 * sqWeight b) * (2 * (c1 * (u 1))))) * (2 * sqWeight b)
          = 4 * c0 * (u 0) * sqWeight b ^ 2 - 2 * a * b * (c1 * (u 1)) := by
        field_simp
        ring
      rw [hcalc, hwb] at hkey
      linarith
    have E2 : 2 * c1 * (u 1) * (1 - a ^ 2 / 2) = a * b * (c0 * (u 0)) := by
      have hkey : (2 * c1 * (u 1) * sqWeight a
            + b * (-a / (2 * sqWeight a) * (2 * (c0 * (u 0))))) * (2 * sqWeight a) = 0 := by
        rw [hs, zero_mul]
      have hcalc : (2 * c1 * (u 1) * sqWeight a
            + b * (-a / (2 * sqWeight a) * (2 * (c0 * (u 0))))) * (2 * sqWeight a)
          = 4 * c1 * (u 1) * sqWeight a ^ 2 - 2 * a * b * (c0 * (u 0)) := by
        field_simp
        ring
      rw [hcalc, hwa] at hkey
      linarith
    -- multiplying the two equations
    have ha2 : a ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg a) ha1 (by norm_num)
    have hb2 : b ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg b) hb1 (by norm_num)
    have hmul : (2 * c0 * (u 0) * (1 - b ^ 2 / 2)) * (2 * c1 * (u 1) * (1 - a ^ 2 / 2))
        = (a * b * (c1 * (u 1))) * (a * b * (c0 * (u 0))) := by rw [E1, E2]
    have hmain : c0 * c1 * (u 0) * (u 1) * (4 - 2 * a ^ 2 - 2 * b ^ 2) = 0 := by
      nlinarith [hmul]
    have hpos : 0 < 4 - 2 * a ^ 2 - 2 * b ^ 2 := by nlinarith [ha2, hb2]
    have hcoef : 0 < c0 * c1 * (4 - 2 * a ^ 2 - 2 * b ^ 2) := by positivity
    have hu01 : (u 0) * (u 1) = 0 := by
      have h' : ((u 0) * (u 1)) * (c0 * c1 * (4 - 2 * a ^ 2 - 2 * b ^ 2)) = 0 := by
        nlinarith [hmain]
      exact (mul_eq_zero.mp h').resolve_right (ne_of_gt hcoef)
    have hu0 : u 0 = 0 := by
      rcases mul_eq_zero.mp hu01 with h | h
      · exact h
      · have hz : 2 * c0 * (u 0) * (1 - b ^ 2 / 2) = 0 := by
          have := E1
          rw [h] at this
          simpa using this
        have hfac : (u 0) * (2 * c0 * (1 - b ^ 2 / 2)) = 0 := by nlinarith [hz]
        have hne : (2 * c0 * (1 - b ^ 2 / 2)) ≠ 0 := by
          have h2 : 0 < 1 - b ^ 2 / 2 := by nlinarith [hb2]
          positivity
        exact (mul_eq_zero.mp hfac).resolve_right hne
    have hu1 : u 1 = 0 := by
      rcases mul_eq_zero.mp hu01 with h | h
      · have hz : 2 * c1 * (u 1) * (1 - a ^ 2 / 2) = 0 := by
          have := E2
          rw [h] at this
          simpa using this
        have hfac : (u 1) * (2 * c1 * (1 - a ^ 2 / 2)) = 0 := by nlinarith [hz]
        have hne : (2 * c1 * (1 - a ^ 2 / 2)) ≠ 0 := by
          have h2 : 0 < 1 - a ^ 2 / 2 := by nlinarith [ha2]
          positivity
        exact (mul_eq_zero.mp hfac).resolve_right hne
      · exact h
    rw [← mk2_eta u, hu0, hu1]
    exact mk2_zero'
  have hinj : Function.Injective (fderiv ℝ g y) := by
    intro v w hvw
    have hsub : fderiv ℝ g y (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (key (v - w) hsub)
  exact hinj

end

end Work.Drive
