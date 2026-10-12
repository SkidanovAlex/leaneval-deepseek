import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseFixB1S.pcDefs
import Submission.Work.BoseFixB3.CS.ae_eval_mem_interior_acube
import Submission.Work.BoseFixR.SmoothApproxGradient
import Submission.Work.BoseKinLoc.Momentum.coord_trunc_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.profHatCube_moments`

The two moments of the cube cutoff's cosine profile

    `(2π)⁻³ ∫_p (profHatCube M p)² = 1`,
    `(2π)⁻³ ∫_p ‖p‖² (profHatCube M p)² = ∫_z ‖gradient (chiSmall M) z‖²`

(`profHatCube M p = ∫_z chiSmall M z · cos⟪p,z⟫`), for every `M ≥ 1`.

## Route

`chiSmall M` is the (normalised) pure tensor product `cSmall M · ∏_j φ(z_j)` with `φ = ζ^M`
(`pcDefs`), so everything runs through the 1D factor:

* `pcKinFT_chiSmall_eq`: `chiSmall M` is real and even, so `kinFT (chiSmall M : ℂ) p` is real and
  equals `profHatCube M p`;
* `pcKinFT_prod`: the tensor Fubini `kinFT (∏_j g_j(z_j)) p = ∏_j ft1 (g_j) (p_j)`;
* `pcFt1IBP`: 1D integration by parts, `ft1 φ' = i·y·ft1 φ` for the a.e. derivative
  `φ' = phiCDeriv M`;
* `pcKinFT_deriv`: hence the derivative rule
  `kinFT (∂_k chiSmall M) p = i·p_k·kinFT (chiSmall M) p` for the *explicit* partial derivative
  `∂_k chiSmall M = cSmall M·phiCDeriv M (z_k)·∏_{i≠k}φ(z_i)` — no smoothness needed, so the
  Lipschitz case `M = 1` is covered;
* `pcAeGradCoord` (delegated): the a.e. identification of the gradient coordinates with those
  explicit partials;
* assembly with Plancherel (`kinFT_sq_of_memLp`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. Elementary support facts for the 1D factor -/

/-- `phiC M` vanishes for `|x| ≥ 1/2` (for `M ≥ 1`). -/
lemma phiC_eq_zero_of_half_le {M : ℕ} (hM : 1 ≤ M) {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    phiC M x = 0 := by
  rw [phiC]
  have hMne : M ≠ 0 := by omega
  have hcos : Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  rcases lt_or_eq_of_le hx with h | h
  · rw [zeta1d_of_one_half_lt h, zero_pow hMne]
  · have hx' : x = 1 / 2 ∨ x = -(1 / 2) := by
      rw [eq_comm] at h
      exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp h
    rcases hx' with rfl | rfl
    · rw [zeta1d_of_abs_le (by norm_num), hcos, zero_pow hMne]
    · rw [zeta1d_neg, zeta1d_of_abs_le (by norm_num), hcos, zero_pow hMne]

/-- `phiCDeriv M` vanishes for `|x| ≥ 1/2`. -/
lemma phiCDeriv_eq_zero_of_half_le {M : ℕ} {x : ℝ} (hx : 1 / 2 ≤ |x|) : phiCDeriv M x = 0 := by
  rw [phiCDeriv]
  exact if_neg (not_lt.mpr hx)

/-- The interior derivative formula: on `|x| < 1/2`, `phiCDeriv M x` is the derivative of
`phiC M` (which equals `cos(π·)^M` there). -/
lemma phiCDeriv_eq {M : ℕ} {x : ℝ} (hx : |x| < 1 / 2) :
    phiCDeriv M x
      = (M : ℝ) * (Real.cos (Real.pi * x)) ^ (M - 1) * (-(Real.sin (Real.pi * x) * Real.pi)) := by
  rw [phiCDeriv, if_pos hx]
  ring

/-! ## 1. The `p`-convention transform of the cube bump is its cosine profile -/

/-- The Fourier transform of the cube bump is its real cosine profile: `chiSmall M` is real and
even, so the sine part of `kinFT` vanishes.  (Cube analogue of `Work.OneBodyKin.kinFT_chi_eq`.) -/
theorem pcKinFT_chiSmall_eq (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    kinFT (fun z : E3 => (chiSmall M z : ℂ)) p = (profHatCube M p : ℂ) := by
  have hcont : Continuous (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)) := by
    apply Continuous.mul
    · apply Complex.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
    · exact Complex.continuous_ofReal.comp (chiSmall_continuous hM)
  have hcs : HasCompactSupport (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)) := by
    refine (chiSmall_hasCompactSupport hM).mono (fun y hy => ?_)
    intro hchi
    exact hy (by simp [hchi])
  have hf : Integrable (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)) volume :=
    hcont.integrable_of_hasCompactSupport hcs
  have hexp : ∀ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      = ((Real.cos (inner ℝ p y) : ℝ) : ℂ) - ((Real.sin (inner ℝ p y) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ))
          = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hpt : ∀ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)
      = ((chiSmall M y * Real.cos (inner ℝ p y) : ℝ) : ℂ)
        + ((-(chiSmall M y * Real.sin (inner ℝ p y)) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [hexp y]
    push_cast
    ring
  have hre_pt : ∀ y : E3, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)).re
      = chiSmall M y * Real.cos (inner ℝ p y) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him_pt : ∀ y : E3, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chiSmall M y : ℂ)).im
      = -(chiSmall M y * Real.sin (inner ℝ p y)) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [kinFT]
  change (∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      * (chiSmall M y : ℂ)) = (profHatCube M p : ℂ)
  apply Complex.ext
  · have hre : (∫ y : E3,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (chiSmall M y : ℂ)).re
        = ∫ y : E3,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (chiSmall M y : ℂ)).re := by
      have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
      simpa using this.symm
    rw [hre]
    rw [show (∫ y : E3,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
              * (chiSmall M y : ℂ)).re)
          = ∫ y : E3, chiSmall M y * Real.cos (inner ℝ p y) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ hre_pt]
    simp [profHatCube]
  · have him : (∫ y : E3,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (chiSmall M y : ℂ)).im
        = ∫ y : E3,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (chiSmall M y : ℂ)).im := by
      have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hf
      simpa using this.symm
    rw [him]
    rw [show (∫ y : E3,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
              * (chiSmall M y : ℂ)).im)
          = ∫ y : E3, -(chiSmall M y * Real.sin (inner ℝ p y)) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ him_pt]
    rw [MeasureTheory.integral_neg]
    have hzero : (∫ y : E3,
        chiSmall M y * Real.sin (inner ℝ p y)) = 0 := by
      have hinv := MeasureTheory.integral_neg_eq_self
        (fun y : E3 => chiSmall M y * Real.sin (inner ℝ p y))
        (volume : Measure ℝ³)
      have hshift : (∫ y : E3,
            (fun y : E3 => chiSmall M y * Real.sin (inner ℝ p y)) (-y))
          = -(∫ y : E3,
              chiSmall M y * Real.sin (inner ℝ p y)) := by
        rw [← MeasureTheory.integral_neg]
        apply integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun y => by
          simp only [inner_neg_right, Real.sin_neg, chiSmall_even hM]
          ring)
      rw [hshift] at hinv
      linarith
    rw [hzero, neg_zero]
    simp

/-! ## 2. The tensor Fubini for `kinFT` -/

/-- **Fubini in product form for the `p`-convention transform**:
`kinFT (∏_j g_j(z_j)) p = ∏_j ft1 (g_j) (p_j)`.  No integrability hypothesis is needed (both
sides are Bochner integrals, and Mathlib's product Fubini is unconditional). -/
theorem pcKinFT_prod (g : Fin 3 → ℝ → ℂ) (p : E3) :
    kinFT (fun z : E3 => ∏ j : Fin 3, g j (z.ofLp j)) p
      = ∏ j : Fin 3, ft1 (g j) (p.ofLp j) := by
  rw [kinFT]
  have hinner : ∀ z : E3, ((inner ℝ p z : ℝ) : ℂ)
      = ∑ j : Fin 3, ((p.ofLp j * z.ofLp j : ℝ) : ℂ) := by
    intro z
    rw [PiLp.inner_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show inner ℝ (p.ofLp j) (z.ofLp j) = z.ofLp j * p.ofLp j from by simp]
    push_cast
    ring
  have hpt : ∀ z : E3, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ∏ j : Fin 3, g j (z.ofLp j)
      = ∏ j : Fin 3,
          Complex.exp (-(Complex.I * ((p.ofLp j * z.ofLp j : ℝ) : ℂ))) * g j (z.ofLp j) := by
    intro z
    rw [hinner z]
    rw [show -(Complex.I * (∑ j : Fin 3, ((p.ofLp j * z.ofLp j : ℝ) : ℂ)))
        = ∑ j : Fin 3, -(Complex.I * ((p.ofLp j * z.ofLp j : ℝ) : ℂ)) from by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]]
    rw [Complex.exp_sum, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    Work.BoseKinLoc.Momentum.integral_euclidean_prod
      (fun j s => Complex.exp (-(Complex.I * ((p.ofLp j * s : ℝ) : ℂ))) * g j s)]
  refine Finset.prod_congr rfl fun j _ => ?_
  apply integral_congr_ae
  filter_upwards with s
  rw [Complex.ofReal_mul]

/-! ## 3. The mass moment -/

theorem pcProfHatCube_mass_eq (M : ℕ) (hM : 1 ≤ M) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, (profHatCube M p) ^ 2) = 1 := by
  have hcont : Continuous (fun z : E3 => (chiSmall M z : ℂ)) :=
    Complex.continuous_ofReal.comp (chiSmall_continuous hM)
  have hcs : HasCompactSupport (fun z : E3 => (chiSmall M z : ℂ)) :=
    (chiSmall_hasCompactSupport hM).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hmem1 : MemLp (fun z : E3 => (chiSmall M z : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr (hcont.integrable_of_hasCompactSupport hcs)
  have hmem2 : MemLp (fun z : E3 => (chiSmall M z : ℂ)) 2 volume :=
    hcont.memLp_of_hasCompactSupport hcs
  have hPL := (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hmem1 hmem2).2
  have hpt : ∀ p : E3, (profHatCube M p) ^ 2
      = ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
    intro p
    rw [pcKinFT_chiSmall_eq M hM p, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have hpt2 : ∀ z : E3, ‖(chiSmall M z : ℂ)‖ ^ 2 = (chiSmall M z) ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hPL,
    integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact chiSmall_L2 hM

lemma pcNorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [norm_nonneg (((r : ℝ) : ℂ)), abs_nonneg r]

lemma measurable_phiCDeriv (M : ℕ) : Measurable (phiCDeriv M) := by
  have hs : MeasurableSet {x : ℝ | |x| < 1 / 2} :=
    measurableSet_lt measurable_abs measurable_const
  have hc : Measurable fun x : ℝ =>
      (M : ℝ) * (Real.cos (Real.pi * x)) ^ (M - 1) * (-(Real.pi * Real.sin (Real.pi * x))) := by
    fun_prop
  exact Measurable.ite hs hc measurable_const

lemma setIntegral_Icc_eq_intervalIntegral_C (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ) :
    ∫ x in Set.Icc a b, g x = ∫ x in a..b, g x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- 1D integration by parts: `ft1 φ' = i·y·ft1 φ`. -/
theorem pcFt1IBP (M : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    ft1 (fun x : ℝ => (phiCDeriv M x : ℂ)) y
      = Complex.I * (y : ℂ) * ft1 (fun x : ℝ => (phiC M x : ℂ)) y := by
  set u : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * (y * x : ℂ))) with hu
  set v : ℝ → ℂ := fun x => (phiC M x : ℂ) with hv
  set v' : ℝ → ℂ := fun x => (phiCDeriv M x : ℂ) with hv'
  set u' : ℝ → ℂ := fun x => -(Complex.I * (y : ℂ)) * u x with hu'
  have hab : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hu_cont : ContinuousOn u (Set.uIcc (-(1 / 2)) (1 / 2)) := by
    rw [hu]
    exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-(Complex.I * (y * x : ℂ)))).continuousOn
  have hv_cont : ContinuousOn v (Set.uIcc (-(1 / 2)) (1 / 2)) := by
    rw [hv]
    exact (Complex.continuous_ofReal.comp (zeta1d_continuous.pow M)).continuousOn
  have hu_deriv : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (y : ℂ) * (t : ℂ)) ((y : ℂ) * 1) x :=
      (HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul (y : ℂ)
    have h2 : HasDerivAt (fun t : ℝ => Complex.I * ((y : ℂ) * (t : ℂ)))
        (Complex.I * ((y : ℂ) * 1)) x := h1.const_mul Complex.I
    have h3 : HasDerivAt (fun t : ℝ => -(Complex.I * ((y : ℂ) * (t : ℂ))))
        (-(Complex.I * ((y : ℂ) * 1))) x := h2.neg
    have h4 : HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * ((y : ℂ) * (t : ℂ)))))
        (Complex.exp (-(Complex.I * ((y : ℂ) * (x : ℂ)))) * (-(Complex.I * ((y : ℂ) * 1)))) x :=
      (Complex.hasDerivAt_exp (-(Complex.I * ((y : ℂ) * (x : ℂ))))).comp x h3
    have h5 : HasDerivAt u (u' x) x := by
      rw [hu, hu']
      convert h4 using 1
      ring
    exact h5
  have hv_deriv : ∀ x ∈ Set.Ioo (min (-(1 / 2)) (1 / 2)) (max (-(1 / 2)) (1 / 2)),
      HasDerivAt v (v' x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hx' : |x| < 1 / 2 := by
      rw [Set.mem_Ioo] at hx
      rw [abs_lt]
      exact hx
    have hval : (M : ℝ) * (Real.cos (Real.pi * x)) ^ (M - 1)
          * (-(Real.sin (Real.pi * x)) * Real.pi) = phiCDeriv M x := by
      simp only [phiCDeriv, if_pos hx']
      ring
    have hraw := HasDerivAt.ofReal_comp (zeta1d_pow_hasDerivAt_of_abs_lt (M := M) x hx')
    rw [hval] at hraw
    have hfun : (fun t : ℝ => ((zeta1d t ^ M : ℝ) : ℂ)) = v := by
      funext t
      simp only [hv, phiC]
    rw [hfun] at hraw
    exact hraw
  have hu'_int : IntervalIntegrable u' volume (-(1 / 2)) (1 / 2) := by
    rw [hu']
    exact (by fun_prop : Continuous fun x : ℝ =>
      -(Complex.I * (y : ℂ)) * u x).intervalIntegrable _ _
  have hv'_int : IntervalIntegrable v' volume (-(1 / 2)) (1 / 2) := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?_ ?_ ((M : ℝ) * Real.pi) ?_
    · rw [Set.uIoc_of_le hab, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact (Complex.measurable_ofReal.comp (measurable_phiCDeriv M)).aestronglyMeasurable
    · filter_upwards with x
      rw [hv', pcNorm_ofReal]
      exact abs_phiCDeriv_le M x
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := u) (v := v) (u' := u') (v' := v') hu_cont hv_cont
    (fun x hx => hu_deriv x) (fun x hx => hv_deriv x hx) hu'_int hv'_int
  have hva0 : phiC M (-(1 / 2)) = 0 := phiC_eq_zero_of_half_le hM (by norm_num)
  have hvb0 : phiC M (1 / 2) = 0 := phiC_eq_zero_of_half_le hM (by norm_num)
  have hva : v (-(1 / 2)) = 0 := by simp only [hv, hva0, Complex.ofReal_zero]
  have hvb : v (1 / 2) = 0 := by simp only [hv, hvb0, Complex.ofReal_zero]
  have hA : ft1 (fun x : ℝ => (phiCDeriv M x : ℂ)) y
      = ∫ x in (-(1 / 2))..(1 / 2), u x * v' x := by
    have h1 : ft1 (fun x : ℝ => (phiCDeriv M x : ℂ)) y = ∫ x : ℝ, u x * v' x := by
      simp only [ft1, hu, hv']
    have h2 : ∀ x ∉ Set.Icc (-(1 / 2)) (1 / 2), u x * v' x = 0 := by
      intro x hx
      have hvx : v' x = 0 := by
        simp only [hv', phiCDeriv]
        refine congrArg Complex.ofReal (if_neg ?_)
        intro hlt
        rw [abs_lt] at hlt
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx <;> linarith [hlt.1, hlt.2]
      rw [hvx, mul_zero]
    have h3 : ∫ x in Set.Icc (-(1 / 2)) (1 / 2), u x * v' x = ∫ x : ℝ, u x * v' x :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (volume : Measure ℝ)) h2
    rw [setIntegral_Icc_eq_intervalIntegral_C (-(1 / 2)) (1 / 2) hab] at h3
    rw [h1, ← h3]
  have hB : ft1 (fun x : ℝ => (phiC M x : ℂ)) y
      = ∫ x in (-(1 / 2))..(1 / 2), u x * v x := by
    have h1 : ft1 (fun x : ℝ => (phiC M x : ℂ)) y = ∫ x : ℝ, u x * v x := by
      simp only [ft1, hu, hv]
    have h2 : ∀ x ∉ Set.Icc (-(1 / 2)) (1 / 2), u x * v x = 0 := by
      intro x hx
      have hvx : v x = 0 := by
        simp only [hv]
        refine congrArg Complex.ofReal (phiC_eq_zero_of_half_le hM ?_)
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hvx, mul_zero]
    have h3 : ∫ x in Set.Icc (-(1 / 2)) (1 / 2), u x * v x = ∫ x : ℝ, u x * v x :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (volume : Measure ℝ)) h2
    rw [setIntegral_Icc_eq_intervalIntegral_C (-(1 / 2)) (1 / 2) hab] at h3
    rw [h1, ← h3]
  have hU : (∫ x in (-(1 / 2))..(1 / 2), u' x * v x)
      = ∫ x in (-(1 / 2))..(1 / 2), (-(Complex.I * (y : ℂ))) * (u x * v x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    rw [hu']
    ring
  rw [hA, hB, hibp, hva, hvb, hU]
  simp only [mul_zero, sub_zero, zero_sub]
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ## 5. The explicit partial derivatives and the derivative rule -/

/-- The explicit `k`-th partial derivative of `chiSmall M`:
`cSmall M · φ'(z_k) · ∏_{i≠k} φ(z_i)`. -/
noncomputable def pcD (M : ℕ) (k : Fin 3) (z : E3) : ℝ :=
  cSmall M * phiCDeriv M (z.ofLp k) * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)

/-- The coordinate factor with the `k`-th slot replaced by `cSmall M · φ'`. -/
noncomputable def pcG (M : ℕ) (k : Fin 3) : Fin 3 → ℝ → ℂ :=
  fun j x => if j = k then ((cSmall M * phiCDeriv M x : ℝ) : ℂ) else ((phiC M x : ℝ) : ℂ)

lemma pcG_self (M : ℕ) (k : Fin 3) (x : ℝ) :
    pcG M k k x = ((cSmall M * phiCDeriv M x : ℝ) : ℂ) := by
  simp [pcG]

lemma pcG_ne {M : ℕ} {k j : Fin 3} (hjk : j ≠ k) (x : ℝ) :
    pcG M k j x = ((phiC M x : ℝ) : ℂ) := by
  simp [pcG, hjk]

lemma pcD_eq_prod (M : ℕ) (k : Fin 3) (z : E3) :
    ((pcD M k z : ℝ) : ℂ) = ∏ j : Fin 3, pcG M k j (z.ofLp j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin 3 => pcG M k j (z.ofLp j))
    (Finset.mem_univ k)]
  rw [pcG_self, pcD]
  have hprod : (∏ j ∈ Finset.univ.erase k, pcG M k j (z.ofLp j))
      = ((∏ j ∈ Finset.univ.erase k, phiC M (z.ofLp j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    exact pcG_ne (Finset.mem_erase.mp hj).1 (z.ofLp j)
  rw [hprod, Complex.ofReal_mul]

/-- **The derivative rule** for the explicit partial derivative `pcD M k` of the cube bump:
`kinFT (∂_k chiSmall M) p = i·p_k·kinFT (chiSmall M) p`.  No smoothness of `chiSmall M` is used
(the proof goes through the tensor Fubini `pcKinFT_prod` and the 1D integration by parts
`pcFt1IBP`), so it covers the Lipschitz case `M = 1`. -/
theorem pcKinFT_pcD (M : ℕ) (hM : 1 ≤ M) (k : Fin 3) (p : E3) :
    kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p
      = Complex.I * (p.ofLp k : ℂ) * kinFT (fun z : E3 => (chiSmall M z : ℂ)) p := by
  have hL : (fun z : E3 => ((pcD M k z : ℝ) : ℂ))
      = fun z : E3 => ∏ j : Fin 3, pcG M k j (z.ofLp j) := funext (pcD_eq_prod M k)
  have hchi : kinFT (fun z : E3 => (chiSmall M z : ℂ)) p
      = (cSmall M : ℂ) * ∏ j : Fin 3, ft1 (fun x : ℝ => ((phiC M x : ℝ) : ℂ))
          (p.ofLp j) := by
    have h1 : (fun z : E3 => (chiSmall M z : ℂ))
        = fun z : E3 =>
            (cSmall M : ℂ) * (∏ j : Fin 3, ((phiC M (z.ofLp j) : ℝ) : ℂ)) := by
      funext z
      rw [chiSmall_eq_cSmall_mul M z, chiSmallBase_eq_prod, Complex.ofReal_mul,
        Complex.ofReal_prod]
    rw [h1]
    have h2 : kinFT (fun z : E3 =>
          (cSmall M : ℂ) * (∏ j : Fin 3, ((phiC M (z.ofLp j) : ℝ) : ℂ))) p
        = (cSmall M : ℂ) * kinFT (fun z : E3 =>
            ∏ j : Fin 3, ((phiC M (z.ofLp j) : ℝ) : ℂ)) p := by
      rw [kinFT]
      rw [show (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((cSmall M : ℂ) * ∏ j : Fin 3, ((phiC M (z.ofLp j) : ℝ) : ℂ)))
          = fun z : E3 => (cSmall M : ℂ) *
              (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                ∏ j : Fin 3, ((phiC M (z.ofLp j) : ℝ) : ℂ)) from by
        funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rfl
    rw [h2]
    rw [pcKinFT_prod (fun j : Fin 3 => fun x : ℝ => ((phiC M x : ℝ) : ℂ)) p]
  have hfac : ft1 (pcG M k k) (p.ofLp k)
      = (cSmall M : ℂ) * (Complex.I * (p.ofLp k : ℂ)
          * ft1 (fun x : ℝ => ((phiC M x : ℝ) : ℂ)) (p.ofLp k)) := by
    have hg : pcG M k k = fun x : ℝ => ((cSmall M * phiCDeriv M x : ℝ) : ℂ) :=
      funext (pcG_self M k)
    rw [hg, ft1]
    rw [show (fun x : ℝ => Complex.exp (-(Complex.I * (p.ofLp k * x : ℂ))) *
            ((cSmall M * phiCDeriv M x : ℝ) : ℂ))
        = fun x : ℝ => (cSmall M : ℂ) *
            (Complex.exp (-(Complex.I * (p.ofLp k * x : ℂ))) *
              ((phiCDeriv M x : ℝ) : ℂ)) from by
      funext x
      rw [Complex.ofReal_mul]
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [ft1]
    exact pcFt1IBP M hM (p.ofLp k)
  have htail : (∏ j ∈ Finset.univ.erase k, ft1 (pcG M k j) (p.ofLp j))
      = ∏ j ∈ Finset.univ.erase k,
          ft1 (fun x : ℝ => ((phiC M x : ℝ) : ℂ)) (p.ofLp j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [show pcG M k j = fun x : ℝ => ((phiC M x : ℝ) : ℂ) from
      funext (pcG_ne (Finset.mem_erase.mp hj).1)]
  rw [hL, pcKinFT_prod, hchi,
    ← Finset.mul_prod_erase Finset.univ (fun j : Fin 3 => ft1 (pcG M k j) (p.ofLp j))
      (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ
      (fun j : Fin 3 => ft1 (fun x : ℝ => ((phiC M x : ℝ) : ℂ)) (p.ofLp j))
      (Finset.mem_univ k),
    hfac, htail]
  ring

/-! ## 6. The a.e. identification of the gradient coordinates -/

/-- `ζ^M` is differentiable at every `y ≠ ±1/2` (for `M ≥ 1`). -/
lemma differentiableAt_zeta1d_pow {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : |y| ≠ 1 / 2) :
    DifferentiableAt ℝ (fun x : ℝ => zeta1d x ^ M) y := by
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · exact (zeta1d_pow_hasDerivAt_of_abs_lt (M := M) y hlt).differentiableAt
  · have h0 : (fun x : ℝ => zeta1d x ^ M) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have hnhd : {x : ℝ | 1 / 2 < |x|} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hgt
      filter_upwards [hnhd] with x hx
      rw [zeta1d_of_one_half_lt hx, zero_pow (by omega : M ≠ 0)]
    exact (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0

/-- The a.e. derivative of `ζ^M` is `phiCDeriv M`. -/
lemma deriv_zeta1d_pow_of_ne_half {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : |y| ≠ 1 / 2) :
    deriv (fun x : ℝ => zeta1d x ^ M) y = phiCDeriv M y := by
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · rw [(zeta1d_pow_hasDerivAt_of_abs_lt (M := M) y hlt).deriv, phiCDeriv_eq hlt]
    ring
  · have h0 : (fun x : ℝ => zeta1d x ^ M) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have hnhd : {x : ℝ | 1 / 2 < |x|} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hgt
      filter_upwards [hnhd] with x hx
      rw [zeta1d_of_one_half_lt hx, zero_pow (by omega : M ≠ 0)]
    rw [Filter.EventuallyEq.deriv_eq h0, deriv_const,
      phiCDeriv_eq_zero_of_half_le (le_of_lt hgt)]

/-- **The a.e. gradient coordinates of the cube bump**: off the finite union of hyperplanes
`{|z_j| = 1/2}`, the `k`-th coordinate of the gradient of `chiSmallBase M` is the explicit
partial derivative `φ'(z_k)·∏_{i≠k}φ(z_i)`. -/
theorem pcAeGradCoord (M : ℕ) (hM : 1 ≤ M) :
    ∀ᵐ z : E3 ∂(volume : Measure E3), ∀ k : Fin 3,
      (gradient (chiSmallBase M) z).ofLp k
        = phiCDeriv M (z.ofLp k) * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) := by
  have hBad : (volume : Measure E3) {z : E3 | ∃ j : Fin 3, |z.ofLp j| = 1 / 2} = 0 := by
    rw [show {z : E3 | ∃ j : Fin 3, |z.ofLp j| = 1 / 2}
        = ⋃ j : Fin 3, {z : E3 | |z.ofLp j| = 1 / 2} from by
      ext z; simp]
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    have h1 : {z : E3 | |z.ofLp j| = 1 / 2}
        = {z : E3 | z.ofLp j = 1 / 2} ∪ {z : E3 | z.ofLp j = -(1 / 2)} := by
      ext z
      rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq,
        abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [h1]
    exact MeasureTheory.measure_union_null
      (Work.BoseFixB3.CS.volume_coord_eq_zero j (1 / 2))
      (Work.BoseFixB3.CS.volume_coord_eq_zero j (-(1 / 2)))
  have key : ∀ z : E3, (∀ j : Fin 3, |z.ofLp j| ≠ 1 / 2) → ∀ k : Fin 3,
      (gradient (chiSmallBase M) z).ofLp k
        = phiCDeriv M (z.ofLp k) * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) := by
    intro z hz k
    have hdg : ∀ j : Fin 3, DifferentiableAt ℝ (fun w : E3 => phiC M (w.ofLp j)) z := by
      intro j
      refine DifferentiableAt.comp (x := z) (g := fun y : ℝ => zeta1d y ^ M)
        (f := fun w : E3 => (Submission.BoseGases.coordCLM j) w) ?_ ?_
      · exact differentiableAt_zeta1d_pow hM (hz j)
      · exact ContinuousLinearMap.differentiableAt _
    have hsingle : ∀ j : Fin 3,
        fderiv ℝ (fun w : E3 => phiC M (w.ofLp j)) z (Submission.BoseGases.kcStdBasis k)
          = if j = k then deriv (fun y : ℝ => zeta1d y ^ M) (z.ofLp j) else 0 := by
      intro j
      have hdφ : DifferentiableAt ℝ (fun y : ℝ => zeta1d y ^ M) (z.ofLp j) :=
        differentiableAt_zeta1d_pow hM (hz j)
      have hcomp : fderiv ℝ (fun w : E3 => phiC M (w.ofLp j)) z
          = fderiv ℝ (fun y : ℝ => zeta1d y ^ M) (z.ofLp j) ∘SL Submission.BoseGases.coordCLM j := by
        rw [show (fun w : E3 => phiC M (w.ofLp j))
              = (fun y : ℝ => zeta1d y ^ M) ∘ (⇑(Submission.BoseGases.coordCLM j)) from rfl,
          fderiv_comp (𝕜 := ℝ) z (g := fun y : ℝ => zeta1d y ^ M) hdφ
            (ContinuousLinearMap.differentiableAt (Submission.BoseGases.coordCLM j)),
          ContinuousLinearMap.fderiv]
        rfl
      rw [hcomp, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul,
        show (Submission.BoseGases.coordCLM j) (Submission.BoseGases.kcStdBasis k)
            = if j = k then (1 : ℝ) else 0 from by
          rw [show (Submission.BoseGases.coordCLM j) (Submission.BoseGases.kcStdBasis k)
              = (Submission.BoseGases.kcStdBasis k).ofLp j from rfl,
            Submission.BoseGases.kcStdBasis, PiLp.single_apply]]
      split_ifs with h
      · rw [one_mul]
      · rw [zero_mul]
    have hprod : fderiv ℝ (chiSmallBase M) z (Submission.BoseGases.kcStdBasis k)
        = ∑ j : Fin 3, (∏ i ∈ Finset.univ.erase j, phiC M (z.ofLp i))
            * fderiv ℝ (fun w : E3 => phiC M (w.ofLp j)) z
                (Submission.BoseGases.kcStdBasis k) := by
      rw [show chiSmallBase M
            = fun w : E3 => ∏ j ∈ Finset.univ, (fun w : E3 => phiC M (w.ofLp j)) w from by
        funext w
        rw [chiSmallBase_eq_prod]]
      rw [fderiv_finset_prod (u := Finset.univ)
        (g := fun j : Fin 3 => fun w : E3 => phiC M (w.ofLp j)) (fun i _ => hdg i)]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsum : fderiv ℝ (chiSmallBase M) z (Submission.BoseGases.kcStdBasis k)
        = deriv (fun y : ℝ => zeta1d y ^ M) (z.ofLp k)
            * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) := by
      rw [hprod, Finset.sum_eq_single k]
      · rw [hsingle k, if_pos rfl]
        ring
      · intro j _ hjk
        rw [hsingle j, if_neg (fun h : j = k => hjk h), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hgf : (gradient (chiSmallBase M) z).ofLp k
        = fderiv ℝ (chiSmallBase M) z (Submission.BoseGases.kcStdBasis k) := by
      rw [← inner_gradient_left (f := chiSmallBase M) (x := z)
        (y := Submission.BoseGases.kcStdBasis k),
        show Submission.BoseGases.kcStdBasis k = EuclideanSpace.single k (1 : ℝ) from rfl,
        EuclideanSpace.inner_single_right]
      simp
    rw [hgf, hsum, deriv_zeta1d_pow_of_ne_half hM (hz k)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hBad
  intro z hz
  push_neg at hz
  obtain ⟨k, hk⟩ := hz
  by_contra hcon
  rw [Set.mem_setOf_eq] at hcon
  rw [not_exists] at hcon
  exact hk (key z hcon k)

/-! ## 7. The a.e. gradient of the normalised bump and the second moment -/

/-- The a.e. constant-multiple rule for the gradient. -/
lemma ae_gradient_const_mul (c : ℝ) {g : E3 → ℝ}
    (h : ∀ᵐ z : E3 ∂(volume : Measure E3), DifferentiableAt ℝ g z) :
    ∀ᵐ z : E3 ∂(volume : Measure E3),
      gradient (fun w : E3 => c * g w) z = c • gradient g z := by
  filter_upwards [h] with z hz
  rw [Work.BoseFixR.gradient_eq_toDual_symm, Work.BoseFixR.gradient_eq_toDual_symm,
    fderiv_const_mul hz c, map_smul]

/-- `chiSmallBase M` is a.e. differentiable (off the finite union of hyperplanes
`{|z_j| = 1/2}`). -/
lemma ae_differentiableAt_chiSmallBase (M : ℕ) (hM : 1 ≤ M) :
    ∀ᵐ z : E3 ∂(volume : Measure E3), DifferentiableAt ℝ (chiSmallBase M) z := by
  have hBad : (volume : Measure E3) {z : E3 | ∃ j : Fin 3, |z.ofLp j| = 1 / 2} = 0 := by
    rw [show {z : E3 | ∃ j : Fin 3, |z.ofLp j| = 1 / 2}
        = ⋃ j : Fin 3, {z : E3 | |z.ofLp j| = 1 / 2} from by
      ext z; simp]
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    have h1 : {z : E3 | |z.ofLp j| = 1 / 2}
        = {z : E3 | z.ofLp j = 1 / 2} ∪ {z : E3 | z.ofLp j = -(1 / 2)} := by
      ext z
      rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq,
        abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [h1]
    exact MeasureTheory.measure_union_null
      (Work.BoseFixB3.CS.volume_coord_eq_zero j (1 / 2))
      (Work.BoseFixB3.CS.volume_coord_eq_zero j (-(1 / 2)))
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hBad
  intro z hz
  by_contra hcon
  rw [Set.mem_setOf_eq] at hcon
  rw [not_exists] at hcon
  refine hz ?_
  rw [show chiSmallBase M
      = fun w : E3 => ∏ j ∈ Finset.univ, (fun w : E3 => phiC M (w.ofLp j)) w from by
    funext w
    rw [chiSmallBase_eq_prod]]
  refine (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun j : Fin 3 => fun w : E3 => phiC M (w.ofLp j))
    (g' := fun j : Fin 3 => fderiv ℝ (fun w : E3 => phiC M (w.ofLp j)) z) ?_).differentiableAt
  intro j _
  refine (DifferentiableAt.comp (x := z) (g := fun y : ℝ => zeta1d y ^ M)
    (f := fun w : E3 => (Submission.BoseGases.coordCLM j) w)
    (differentiableAt_zeta1d_pow hM (hcon j))
    (ContinuousLinearMap.differentiableAt _)).hasFDerivAt

/-- The `k`-th coordinate of the a.e. gradient of the normalised cube bump. -/
theorem pcAeGradCoord_chiSmall (M : ℕ) (hM : 1 ≤ M) :
    ∀ᵐ z : E3 ∂(volume : Measure E3), ∀ k : Fin 3,
      (gradient (chiSmall M) z).ofLp k = pcD M k z := by
  have h1 : ∀ᵐ z : E3 ∂(volume : Measure E3),
      gradient (fun w : E3 => cSmall M * chiSmallBase M w) z
        = cSmall M • gradient (chiSmallBase M) z :=
    ae_gradient_const_mul (cSmall M) (ae_differentiableAt_chiSmallBase M hM)
  filter_upwards [h1, pcAeGradCoord M hM] with z hz hz2
  intro k
  rw [show chiSmall M = fun w : E3 => cSmall M * chiSmallBase M w from
    funext fun w => chiSmall_eq_cSmall_mul M w]
  rw [hz, PiLp.smul_apply, smul_eq_mul, hz2 k, pcD]
  ring

/-- **The second moment** `(2π)⁻³∫‖p‖² profHatCube² = ∫‖∇ chiSmall M‖²`. -/
theorem pcProfHatCube_moment_eq (M : ℕ) (hM : 1 ≤ M) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2)
      = ∫ z : E3, ‖gradient (chiSmall M) z‖ ^ 2 := by
  -- the explicit partial derivatives are measurable
  have hmeas : ∀ k : Fin 3, Measurable (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
    intro k
    refine Complex.measurable_ofReal.comp ?_
    rw [show pcD M k = fun z : E3 => cSmall M * phiCDeriv M (z.ofLp k)
        * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) from rfl]
    refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
    · exact (measurable_phiCDeriv M).comp (by fun_prop)
    · refine Finset.measurable_prod _ fun i _ => ?_
      exact (zeta1d_continuous.pow M).measurable.comp (by fun_prop)
  -- they vanish outside the unit ball
  have hsupp : ∀ k : Fin 3, ∀ z : E3, 1 < ‖z‖ → pcD M k z = 0 := by
    intro k z hz
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, 1 / 2 < |z.ofLp i| := by
      by_contra hcon
      rw [not_exists] at hcon
      have hle : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j => le_of_not_gt (hcon j)
      have hsq : ‖z‖ ^ 2 ≤ 3 * (1 / 2) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc ∑ j, ‖z.ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, (1 / 2) ^ 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hle j) 2
          _ = 3 * (1 / 2) ^ 2 := by simp
      have h3 : (3 : ℝ) * (1 / 2) ^ 2 < 1 ^ 2 := by norm_num
      nlinarith [norm_nonneg z, hsq, h3]
    rw [pcD]
    by_cases hik : i = k
    · subst hik
      rw [phiCDeriv_eq_zero_of_half_le (le_of_lt hi), mul_zero, zero_mul]
    · have hzi : phiC M (z.ofLp i) = 0 := phiC_eq_zero_of_half_le hM (le_of_lt hi)
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) hzi]
      ring
  -- hence they lie in `L¹ ∩ L²` (bounded, compactly supported)
  have hMemLp : ∀ k : Fin 3, MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 1 volume
      ∧ MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 2 volume := by
    intro k
    have hcont_supp : ∀ z : E3, 1 < ‖z‖ → ((pcD M k z : ℝ) : ℂ) = 0 :=
      fun z hz => by rw [hsupp k z hz, Complex.ofReal_zero]
    have hcs : HasCompactSupport (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) 1) (isClosed_tsupport _) ?_
      refine closure_minimal ?_ isClosed_closedBall
      intro z hz
      simp only [Function.mem_support, ne_eq] at hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      by_contra h
      exact hz (by simp [hcont_supp z (lt_of_not_ge h)])
    have hbound : ∀ᵐ z : E3 ∂(volume : Measure E3),
        ‖((pcD M k z : ℝ) : ℂ)‖ ≤ |cSmall M| * ((M : ℝ) * Real.pi) := by
      filter_upwards with z
      rw [pcNorm_ofReal, pcD, abs_mul, abs_mul]
      have hprod : |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_phiC_le_one M _)
      calc |cSmall M| * |phiCDeriv M (z.ofLp k)|
              * |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)|
          ≤ |cSmall M| * ((M : ℝ) * Real.pi) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (abs_phiCDeriv_le M _) (abs_nonneg _)) hprod
              (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
        _ = |cSmall M| * ((M : ℝ) * Real.pi) := by ring
    exact ⟨hcs.memLp_of_bound (hmeas k).aestronglyMeasurable _ hbound,
      hcs.memLp_of_bound (hmeas k).aestronglyMeasurable _ hbound⟩
  -- Plancherel for each explicit partial derivative
  have hPL : ∀ k : Fin 3, ((2 * Real.pi) ^ 3)⁻¹
      * (∫ p : E3, ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2)
      = ∫ z : E3, (pcD M k z) ^ 2 := by
    intro k
    have h := (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hMemLp k).1 (hMemLp k).2).2
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖((pcD M k z : ℝ) : ℂ)‖ ^ 2 = (pcD M k z) ^ 2
    rw [pcNorm_ofReal, sq_abs]
  -- integrability of the real kernels
  have hInt : ∀ k : Fin 3, Integrable (fun z : E3 => (pcD M k z) ^ 2) := by
    intro k
    have h := (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hmeas k).aestronglyMeasurable).mp (hMemLp k).2
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    show ‖((pcD M k z : ℝ) : ℂ)‖ ^ 2 = (pcD M k z) ^ 2
    rw [pcNorm_ofReal, sq_abs]
  -- the left-hand side as the sum of the Plancherel integrals
  have hLHS : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2)
      = ∑ k : Fin 3, ∫ z : E3, (pcD M k z) ^ 2 := by
    have hpt : ∀ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2
        = ∑ k : Fin 3, ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2 := by
      intro p
      have hχ : (profHatCube M p) ^ 2
          = ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
        rw [pcKinFT_chiSmall_eq M hM p, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      rw [hχ]
      rw [show ‖p‖ ^ 2 = ∑ k : Fin 3, (p.ofLp k) ^ 2 from by
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.norm_eq_abs, sq_abs]]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pcKinFT_pcD M hM k p]
      have hnorm : ‖Complex.I * (p.ofLp k : ℂ)
            * kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2
          = (p.ofLp k) ^ 2 * ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
        rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_I, one_pow, one_mul,
          pcNorm_ofReal, sq_abs]
      rw [hnorm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => hPL k
    · intro k _
      exact (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hMemLp k).1 (hMemLp k).2).1
  -- the right-hand side as the same sum
  have hRHS : (∫ z : E3, ‖gradient (chiSmall M) z‖ ^ 2)
      = ∑ k : Fin 3, ∫ z : E3, (pcD M k z) ^ 2 := by
    have hpt : ∀ᵐ z : E3 ∂(volume : Measure E3),
        ‖gradient (chiSmall M) z‖ ^ 2 = ∑ k : Fin 3, (pcD M k z) ^ 2 := by
      filter_upwards [pcAeGradCoord_chiSmall M hM] with z hz
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.norm_eq_abs, sq_abs, hz k]
    rw [integral_congr_ae hpt, MeasureTheory.integral_finsetSum]
    intro k _
    exact hInt k
  rw [hLHS, hRHS]

/-! ## 4. The target -/

theorem profHatCube_moments (M : ℕ) (hM : 1 ≤ M) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          (∫ z : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiSmall M z * Real.cos (inner ℝ p z)) ^ 2) = 1
      ∧ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : EuclideanSpace ℝ (Fin 3),
            ‖p‖ ^ 2 * (∫ z : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.chiSmall M z * Real.cos (inner ℝ p z)) ^ 2)
        = ∫ z : EuclideanSpace ℝ (Fin 3), ‖gradient (Submission.BoseGases.chiSmall M) z‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa only [profHatCube] using pcProfHatCube_mass_eq M hM
  · simpa only [profHatCube] using pcProfHatCube_moment_eq M hM

end Work.BoseFixB1S
