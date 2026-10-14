import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.EllipticEst.remov.wsPzBounds
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Local.slice5_vweight_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

/-! ## Elementary facts about `Iθ` and the weight `sEta` -/

private lemma Iθ_eq : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl

private lemma Iθ_measurable : MeasurableSet Work.Spaces.Iθ := by
  rw [Iθ_eq]; exact measurableSet_Icc

private lemma Iθ_volume_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Iθ_eq, Real.volume_Icc]; exact ENNReal.ofReal_lt_top

private lemma Iθ_volume_ne_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ :=
  Iθ_volume_lt_top.ne

private lemma volume_real_Iθ : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [Measure.real_def, Iθ_eq, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]

private lemma volume_real_Ioo {a b : ℝ} (hab : a ≤ b) :
    (volume : Measure ℝ).real (Set.Ioo a b) = b - a := by
  rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]

/-- Integrability of a constant on `Iθ`. -/
private lemma integrableOn_const_Iθ (c : ℝ) :
    MeasureTheory.IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
  MeasureTheory.IntegrableOn.of_bound Iθ_volume_lt_top aestronglyMeasurable_const |c|
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs])

/-- `sin (2θ) ≥ 0` on the open interval. -/
private lemma sin_two_nonneg_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Iθ_eq] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Almost everywhere on `Iθ` the point lies in the open interval. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [Iθ_eq, Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost everywhere on `Iθ`, `1 ≤ sEta θ`. -/
private lemma ae_one_le_sEta_Iθ :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, 1 ≤ Work.FTS.EllipticEst.sEta θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact one_le_sEta_Ioo hθ

/-! ## Interval integrals inside `Iθ` -/

/-- Interval integrals over a subinterval of `Iθ` are dominated by the integral over `Iθ`. -/
private lemma abs_intervalIntegral_le_Iθ {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => |f s|) Work.Spaces.Iθ) {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) :
    |∫ s in a..b, f s| ≤ ∫ s in Work.Spaces.Iθ, |f s| := by
  have hmain : ∀ {u v : ℝ}, u ≤ v → u ∈ Work.Spaces.Iθ → v ∈ Work.Spaces.Iθ →
      |∫ s in u..v, f s| ≤ ∫ s in Work.Spaces.Iθ, |f s| := by
    intro u v huv hu hv
    have hsub : Set.Ioo u v ⊆ Work.Spaces.Iθ := by
      intro x hx
      rw [Iθ_eq] at hu hv ⊢
      exact ⟨le_trans hu.1 (le_of_lt hx.1), le_trans (le_of_lt hx.2) hv.2⟩
    have h1 : |∫ s in Set.Ioo u v, f s| ≤ ∫ s in Set.Ioo u v, |f s| := by
      have h := MeasureTheory.norm_integral_le_integral_norm (f := f)
        (μ := (volume : Measure ℝ).restrict (Set.Ioo u v))
      simpa only [Real.norm_eq_abs] using h
    rw [intervalIntegral.integral_of_le huv, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine le_trans h1 ?_
    refine MeasureTheory.setIntegral_mono_set hint
      (Eventually.of_forall fun x => abs_nonneg _) ?_
    filter_upwards with x hx using hsub hx
  rcases le_total a b with hab | hba
  · exact hmain hab ha hb
  · rw [intervalIntegral.integral_symm, abs_neg]
    exact hmain hba hb ha

/-- Interval integrability on a subinterval of `Iθ`, from integrability on `Iθ`. -/
private lemma intervalIntegrable_of_integrableOn_Iθ {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn g Work.Spaces.Iθ) {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) :
    IntervalIntegrable g volume a b := by
  rw [Iθ_eq] at ha hb
  constructor
  · refine hint.mono_set fun x hx => ?_
    rw [Iθ_eq]
    exact ⟨le_trans ha.1 hx.1.le, le_trans hx.2 hb.2⟩
  · refine hint.mono_set fun x hx => ?_
    rw [Iθ_eq]
    exact ⟨le_trans hb.1 hx.1.le, le_trans hx.2 ha.2⟩

/-! ## Pointwise bounds coming from `∫ |u''|` -/

/-- On the open interval, `u` is differentiable. -/
private lemma differentiableAt_of_mem_Ioo {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ u x :=
  (hu2.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)

/-- `deriv u` is continuous on the open interval. -/
private lemma continuousOn_deriv_Ioo {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun x => deriv u x) (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx
  have hc2 : ContDiffAt ℝ 2 u x := hu2.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hcd : ContDiffAt ℝ 1 (deriv u) x := contDiffAt_deriv_of_succ (n := 1) (by simpa using hc2)
  exact hcd.continuousAt.continuousWithinAt

/-- Rolle + FTC: on the open interval, `|u'|` is bounded by `∫_{Iθ} |u''|`. -/
lemma deriv_abs_le_integral_second (u : ℝ → ℝ)
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hucont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn (fun s => |deriv (deriv u) s|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv u) s| := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero (a := (0 : ℝ)) (b := Real.pi / 2)
    (by linarith [Real.pi_pos]) hucont (hu0.trans hu1.symm)
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    have hc2 : ContDiffAt ℝ 2 u x := hu2.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have h1 : DifferentiableAt ℝ (deriv u) x := by
      have h := differentiableAt_iteratedDeriv_of_le (N := 2) (k := 1) hc2 (by norm_num)
      rwa [iteratedDeriv_one] at h
    exact h1.hasDerivAt
  have h_int_d2 : MeasureTheory.IntegrableOn (fun s => deriv (deriv u) s) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono (g := fun s => |deriv (deriv u) s|) hint
      ((measurable_deriv (deriv u)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp)
  have hξI : ξ ∈ Work.Spaces.Iθ := by
    rw [Iθ_eq]; exact ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := by
    rw [Iθ_eq]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hFTC : ∫ s in ξ..θ, deriv (deriv u) s = deriv u θ - deriv u ξ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hderiv2 x ⟨lt_of_lt_of_le hξ.1 h1, lt_of_le_of_lt h2 hθ.2⟩
      · exact hderiv2 x ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hξ.2⟩
    · exact intervalIntegrable_of_integrableOn_Iθ h_int_d2 hξI hθI
  rw [hξ0, sub_zero] at hFTC
  calc |deriv u θ| = |∫ s in ξ..θ, deriv (deriv u) s| := by rw [hFTC]
    _ ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv u) s| :=
        abs_intervalIntegral_le_Iθ hint hξI hθI

/-- FTC on `[θ, π/2]`: `|u θ| ≤ (π/2 - θ) * ∫_{Iθ} |u''|`. -/
lemma abs_le_sub_mul_integral (u : ℝ → ℝ)
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hucont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn (fun s => |deriv (deriv u) s|) Work.Spaces.Iθ)
    (hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ| ≤ (Real.pi / 2 - θ) * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) := by
  set A : ℝ := ∫ s in Work.Spaces.Iθ, |deriv (deriv u) s| with hA
  have hA0 : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg Iθ_measurable (fun x _ => abs_nonneg _)
  intro θ hθ
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have hFTC : ∫ s in θ..(Real.pi / 2), deriv u s = u (Real.pi / 2) - u θ := by
    refine intervalIntegral.integral_deriv_eq_sub_uIoo ?_ ?_ ?_
    · refine hucont.mono fun x hx => ?_
      rw [Set.uIcc_of_le hθ2.le] at hx
      exact ⟨le_trans hθ.1.le hx.1, hx.2⟩
    · intro x hx
      rw [Set.uIoo_of_le hθ2.le] at hx
      exact differentiableAt_of_mem_Ioo hu2 ⟨lt_trans hθ.1 hx.1, hx.2⟩
    · refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hθ2.le
        ((continuousOn_deriv_Ioo hu2).mono fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩) A
        fun x hx => by
          rw [hA]; exact hderiv x ⟨lt_trans hθ.1 hx.1, hx.2⟩
  rw [hu1, zero_sub] at hFTC
  have hbound : |∫ s in θ..(Real.pi / 2), deriv u s| ≤ A * (Real.pi / 2 - θ) := by
    rw [intervalIntegral.integral_of_le hθ2.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hvol : (volume : Measure ℝ) (Set.Ioo θ (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hbd : ∀ x ∈ Set.Ioo θ (Real.pi / 2), ‖deriv u x‖ ≤ A := by
      intro x hx
      rw [Real.norm_eq_abs, hA]
      exact hderiv x ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol hbd
    rw [volume_real_Ioo hθ2.le] at h
    calc |∫ s in Set.Ioo θ (Real.pi / 2), deriv u s|
        = ‖∫ s in Set.Ioo θ (Real.pi / 2), deriv u s‖ := by rw [Real.norm_eq_abs]
      _ ≤ A * (Real.pi / 2 - θ) := h
  calc |u θ| = |∫ s in θ..(Real.pi / 2), deriv u s| := by rw [hFTC]; simp
    _ ≤ A * (Real.pi / 2 - θ) := hbound
    _ = (Real.pi / 2 - θ) * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) := by rw [hA]; ring

/-- `(u/cos)² ≤ 100 · ∫_{Iθ} (u'')² sEta`. -/
lemma div_cos_sq_le_M (u : ℝ → ℝ)
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hucont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hM : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (u θ / Real.cos θ) ^ 2 ≤ 100 * (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  set I : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hIdef
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  -- integrability of `u''²`
  have h_int_sq : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono (g := fun θ =>
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) hM
      ((measurable_deriv (deriv u)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_one_le_sEta_Iθ] with θ hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_trans zero_le_one hθ))]
    nlinarith [sq_nonneg (deriv (deriv u) θ), hθ]
  have h_le_I : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2) ≤ I := by
    rw [hIdef]
    refine MeasureTheory.integral_mono_ae h_int_sq hM ?_
    filter_upwards [ae_one_le_sEta_Iθ] with θ hθ
    nlinarith [sq_nonneg (deriv (deriv u) θ), hθ]
  -- integrability of `|u''|`
  have h_int_abs : MeasureTheory.IntegrableOn (fun θ => |deriv (deriv u) θ|)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 + 1) Work.Spaces.Iθ :=
      h_int_sq.add (integrableOn_const_Iθ 1)
    refine MeasureTheory.Integrable.mono (g := fun θ => (deriv (deriv u) θ) ^ 2 + 1) h1
      ((measurable_deriv (deriv u)).abs.aestronglyMeasurable) ?_
    filter_upwards with θ
    have hnn : (0 : ℝ) ≤ (deriv (deriv u) θ) ^ 2 + 1 := by positivity
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hnn]
    nlinarith [sq_nonneg (deriv (deriv u) θ), abs_nonneg (deriv (deriv u) θ),
      sq_abs (deriv (deriv u) θ)]
  -- Cauchy–Schwarz
  have hCS : (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ|) ^ 2
      ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2) := by
    haveI hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      rw [isFiniteMeasure_restrict]; exact Iθ_volume_ne_top
    have h_int_sq' : MeasureTheory.Integrable (fun θ => (deriv (deriv u) θ) ^ 2)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := h_int_sq
    have h1 : MemLp (fun θ => |deriv (deriv u) θ|) 2
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        ((measurable_deriv (deriv u)).abs.aestronglyMeasurable)).mpr
        (by simpa [sq_abs] using h_int_sq')
    have h2 : MemLp (fun _ : ℝ => (1 : ℝ)) 2
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := memLp_const 1
    have hcs := Work.Spaces.cs_integral h1 h2
    have hone : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, volume_real_Iθ]
    calc (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ|) ^ 2
        = (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ| * 1) ^ 2 := by simp
      _ ≤ (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ| ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) := hcs
      _ = (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2) := by
        rw [show (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 by simpa using hone]
        simp only [sq_abs]
        ring
  -- the two pointwise bounds
  have hderiv_le := deriv_abs_le_integral_second u hu2 hucont hu0 hu1 h_int_abs
  have hfun_le := abs_le_sub_mul_integral u hu2 hucont hu1 h_int_abs hderiv_le
  have hA0 : 0 ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv u) s| :=
    MeasureTheory.setIntegral_nonneg Iθ_measurable (fun x _ => abs_nonneg _)
  have h2pi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hstep : (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) ^ 2 ≤ (Real.pi / 2) * I :=
    le_trans hCS (mul_le_mul_of_nonneg_left h_le_I h2pi)
  intro θ hθ
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hJ : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2])
      (by linarith [hθ.1])
    rw [Real.sin_pi_div_two_sub] at h
    have h2 : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
    calc Real.pi / 2 - θ = Real.pi / 2 * (2 / Real.pi) * (Real.pi / 2 - θ) := by rw [h2, one_mul]
      _ = Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) := by ring
      _ ≤ Real.pi / 2 * Real.cos θ := mul_le_mul_of_nonneg_left h (by positivity)
  have habs : |u θ / Real.cos θ|
      ≤ Real.pi / 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) := by
    rw [abs_div, abs_of_pos hcos_pos, div_le_iff₀ hcos_pos]
    calc |u θ| ≤ (Real.pi / 2 - θ) * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) :=
          hfun_le θ hθ
      _ ≤ (Real.pi / 2 * Real.cos θ) * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) :=
          mul_le_mul_of_nonneg_right hJ hA0
      _ = Real.pi / 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) * Real.cos θ := by ring
  have hsq : (u θ / Real.cos θ) ^ 2
      ≤ (Real.pi / 2) ^ 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) ^ 2 := by
    rw [show (Real.pi / 2) ^ 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) ^ 2
        = (Real.pi / 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|)) ^ 2 by ring,
      sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2 *
        (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|))]
    exact habs
  have h3 : (Real.pi / 2) ^ 2 * ((Real.pi / 2) * I) ≤ 100 * I := by
    have hpi3 : (Real.pi / 2) ^ 3 ≤ 100 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    rw [show (Real.pi / 2) ^ 2 * ((Real.pi / 2) * I) = (Real.pi / 2) ^ 3 * I by ring]
    nlinarith [hpi3, hI0]
  calc (u θ / Real.cos θ) ^ 2
      ≤ (Real.pi / 2) ^ 2 * (∫ s in Work.Spaces.Iθ, |deriv (deriv u) s|) ^ 2 := hsq
    _ ≤ (Real.pi / 2) ^ 2 * ((Real.pi / 2) * I) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ ≤ 100 * I := h3
    _ = 100 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) := by rw [hIdef]

/-! ## Two algebraic pointwise bounds -/

/-- The `(u/cos)²` term with the weight `sin(2θ)^{4-γ}` is dominated by `4 u²`. -/
lemma div_cos_sq_mul_rpow_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u : ℝ → ℝ}
    (hu1 : u (Real.pi / 2) = 0) :
    ∀ θ ∈ Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.sin (2 * θ) ^ (4 - γ) ≤ 4 * (u θ) ^ 2 := by
  have hγpos : (0 : ℝ) < 4 - γ := by linarith
  intro θ hθ
  rw [Iθ_eq] at hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθπ | hθπ
    · -- interior point
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθπ⟩)
      have hsin2 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθπ, Real.pi_pos])
      have hsin2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hpow : Real.sin (2 * θ) ^ (4 - γ) ≤ Real.sin (2 * θ) ^ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin2 hsin2le (by linarith : (2:ℝ) ≤ 4 - γ)
        rwa [Real.rpow_two] at h
      calc (u θ / Real.cos θ) ^ 2 * Real.sin (2 * θ) ^ (4 - γ)
          ≤ (u θ / Real.cos θ) ^ 2 * Real.sin (2 * θ) ^ 2 :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = (u θ) ^ 2 * (2 * Real.sin θ) ^ 2 := by
            rw [Real.sin_two_mul]; field_simp
        _ ≤ (u θ) ^ 2 * 4 := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            nlinarith [Real.sin_sq_le_one θ]
        _ = 4 * (u θ) ^ 2 := by ring
    · subst hθπ
      rw [Real.cos_pi_div_two, hu1, zero_div]
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, Real.zero_rpow hγpos.ne']
      norm_num
  · subst hθ0
    rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero, Real.zero_rpow hγpos.ne', mul_zero]
    positivity

/-- The `(∂_θ(u/cos))²` term with the weight `sin(2θ)^{4-γ}` is dominated by `8(u')² + 8(u/cos)²`. -/
lemma vprime_pointwise_I (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hd : DifferentiableAt ℝ u θ) :
    (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.sin (2 * θ) ^ (4 - γ)
      ≤ 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2 := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hle1 : Real.sin (2 * θ) ^ (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin2.le hsin2le (by linarith)
  have hsplit : Real.sin (2 * θ) ^ (4 - γ)
      = Real.sin (2 * θ) ^ (2 : ℝ) * Real.sin (2 * θ) ^ (2 - γ) := by
    rw [← Real.rpow_add hsin2]
    rw [show (2 : ℝ) + (2 - γ) = 4 - γ by ring]
  have hd' : deriv (fun θ' => u θ' / Real.cos θ') θ
      = deriv u θ / Real.cos θ + u θ * Real.sin θ / Real.cos θ ^ 2 := by
    change deriv (u / Real.cos) θ = deriv u θ / Real.cos θ + u θ * Real.sin θ / Real.cos θ ^ 2
    have h := (hd.hasDerivAt.div (Real.hasDerivAt_cos θ) (ne_of_gt hcos)).deriv
    rw [h]
    rw [show deriv u θ * Real.cos θ - u θ * -Real.sin θ
      = deriv u θ * Real.cos θ + u θ * Real.sin θ by ring]
    field_simp
  have hstep2 : (deriv u θ / Real.cos θ + u θ * Real.sin θ / Real.cos θ ^ 2)
      * Real.sin (2 * θ) = 2 * deriv u θ * Real.sin θ
        + 2 * (u θ / Real.cos θ) * Real.sin θ ^ 2 := by
    rw [Real.sin_two_mul]; field_simp
  have hstep3 : (2 * deriv u θ * Real.sin θ + 2 * (u θ / Real.cos θ) * Real.sin θ ^ 2) ^ 2
      ≤ 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2 := by
    have hs2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hs4 : Real.sin θ ^ 4 ≤ 1 := by nlinarith [hs2, sq_nonneg (Real.sin θ ^ 2)]
    have hx : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
    have hy : 0 ≤ (u θ / Real.cos θ) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (2 * deriv u θ * Real.sin θ - 2 * (u θ / Real.cos θ) * Real.sin θ ^ 2)]
  calc (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * Real.sin (2 * θ) ^ (4 - γ)
      = (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          (Real.sin (2 * θ) ^ (2 : ℝ) * Real.sin (2 * θ) ^ (2 - γ)) := by rw [hsplit]
    _ ≤ (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
          * Real.sin (2 * θ) ^ (2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc Real.sin (2 * θ) ^ (2 : ℝ) * Real.sin (2 * θ) ^ (2 - γ)
            ≤ Real.sin (2 * θ) ^ (2 : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hsin2.le 2)
          _ = Real.sin (2 * θ) ^ (2 : ℝ) := by ring
    _ = ((deriv u θ / Real.cos θ + u θ * Real.sin θ / Real.cos θ ^ 2)
          * Real.sin (2 * θ)) ^ 2 := by
        rw [hd', Real.rpow_two]; ring
    _ ≤ 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2 := by
        rw [hstep2]; exact hstep3

/-! ## The target -/

theorem slice5_vweight_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) ∧
      (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro u hu2 hucont hu0 hu1 hM hB hA
  set M : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hMdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hAdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable (fun θ _ => sq_nonneg _)
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable (fun θ _ => sq_nonneg _)
  -- the pointwise bound on `(u/cos)²`
  have hGpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (u θ / Real.cos θ) ^ 2 ≤ 100 * M := by
    intro θ hθ
    have h := div_cos_sq_le_M u hu2 hucont hu0 hu1 hM θ hθ
    rw [hMdef]
    exact h
  -- integrability of `θ ↦ (u θ / cos θ)²`
  have hG_int : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound Iθ_volume_lt_top ?_ (100 * M) ?_
    · exact ((MeasureTheory.AEStronglyMeasurable.div₀
        (hucont.aestronglyMeasurable Iθ_measurable)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2)
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hGpt θ hθ
  have hG_bound : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2) ≤ 100 * M * (Real.pi / 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2)
        ≤ ∫ _θ in Work.Spaces.Iθ, 100 * M := by
          refine MeasureTheory.integral_mono_ae hG_int (integrableOn_const_Iθ (100 * M)) ?_
          filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
          exact hGpt θ hθ
      _ = 100 * M * (Real.pi / 2) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, volume_real_Iθ]
          ring
  -- the weight is a.e.-strongly measurable on `Iθ`
  have hw_aesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
      (Real.continuous_sin.measurable.comp
        (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable
  -- integrability of the `(u/cos)²` integrand
  have hFu_int : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono (g := fun θ => 4 * (u θ) ^ 2) (hA.const_mul 4) ?_ ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ hw_aesm
      exact ((MeasureTheory.AEStronglyMeasurable.div₀
        (hucont.aestronglyMeasurable Iθ_measurable)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2)
    · filter_upwards [MeasureTheory.ae_restrict_mem Iθ_measurable] with θ hθ
      have h := div_cos_sq_mul_rpow_le γ hγ1 hγ2 hu1 θ hθ
      have hnn1 : (0 : ℝ) ≤ (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) (4 - γ))
      have hnn2 : (0 : ℝ) ≤ 4 * (u θ) ^ 2 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
      exact h
  -- integrability of the `(∂_θ(u/cos))²` integrand
  have hFv_int : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2) Work.Spaces.Iθ :=
      (hB.const_mul 8).add (hG_int.const_mul 8)
    refine MeasureTheory.Integrable.mono (g := fun θ =>
      8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2) hdom ?_ ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ hw_aesm
      exact (measurable_deriv (fun θ' => u θ' / Real.cos θ')).pow_const 2 |>.aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have h := vprime_pointwise_I γ hγ1 hγ2 hθ (differentiableAt_of_mem_Ioo hu2 hθ)
      have hnn1 : (0 : ℝ) ≤ (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Ioo hθ) (4 - γ))
      have hnn2 : (0 : ℝ) ≤ 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
      exact h
  -- the two integral bounds
  have hFu_bound : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) ≤ 4 * A := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, 4 * (u θ) ^ 2 := by
          refine MeasureTheory.integral_mono_ae hFu_int (hA.const_mul 4) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem Iθ_measurable] with θ hθ
          exact div_cos_sq_mul_rpow_le γ hγ1 hγ2 hu1 θ hθ
      _ = 4 * A := by
          rw [MeasureTheory.integral_const_mul, hAdef]
  have hFv_bound : (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ 8 * B + 8 * (100 * M * (Real.pi / 2)) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => 8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2) Work.Spaces.Iθ :=
      (hB.const_mul 8).add (hG_int.const_mul 8)
    calc (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, (8 * (deriv u θ) ^ 2 + 8 * (u θ / Real.cos θ) ^ 2) := by
          refine MeasureTheory.integral_mono_ae hFv_int hdom ?_
          filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
          exact vprime_pointwise_I γ hγ1 hγ2 hθ (differentiableAt_of_mem_Ioo hu2 hθ)
      _ = 8 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + 8 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2) := by
          rw [MeasureTheory.integral_add (hB.const_mul 8) (hG_int.const_mul 8),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = 8 * B + 8 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2) := by rw [hBdef]
      _ ≤ 8 * B + 8 * (100 * M * (Real.pi / 2)) := by linarith [hG_bound]
  have hpi : 400 * Real.pi ≤ 2000 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hFu_int
  · exact hFv_int
  · calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ 4 * A := hFu_bound
      _ ≤ 2000 * (M + B + A) := by linarith
  · calc (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ 8 * B + 8 * (100 * M * (Real.pi / 2)) := hFv_bound
      _ ≤ 2000 * (M + B + A) := by nlinarith [hpi, hM0, hB0, hA0, Real.pi_pos]

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.remov.weakSliceRegular` (same namespaces), so importing both was a duplicate-declaration error.
-- The names stay available to every consumer through the import above.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Helper lemmas

The proof of the target consists in applying the one-dimensional boundedness lemma
`Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta` (boundedness of a slice and of its
`θ`-derivative from the weighted `L²`-integrability of the slice's second derivative) to the two
slices `θ ↦ Ψ z θ` and `θ ↦ ∂_zΨ(z,θ)`, whose second `θ`-derivatives are the slots
`∂_θθΨ` resp. `∂_z∂_θθΨ` of the `ℋ^k`-membership hypotheses (`k ≥ 2`).  The only structural
input is the Clairaut identity `∂_θθ ∂_zΨ = ∂_z ∂_θθΨ` on the open quadrant. -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- **Clairaut at order `3` for the slices of a `C^∞` function on the open quadrant**:
`∂_θθ (∂_z f) = ∂_z (∂_θθ f)` on `Q0`.

This is two applications of the Clairaut identity `Work.Spaces.pz_pth_comm`
(one for `f`, one for `Work.Spaces.pth f`), transported across the `θ`-derivative by the
locality of `deriv` on the open interval. -/
theorem pthIter2_pz_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz f)))
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 f)))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- `∂_θ (∂_θ ∂_z f) = ∂_θ (∂_z ∂_θ f)` at `(z,θ)`
  have hstep1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ := by
    have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
      exact (Work.Spaces.pz_pth_comm (f := f)
        ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))).of_le (by simp))).symm
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') θ
    rw [hev.deriv_eq]
  -- `∂_θ (∂_z ∂_θ f) = ∂_z (∂_θ ∂_θ f)` at `(z,θ)`: this is Clairaut for `∂_θ f`
  have hstep2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) z θ :=
    (Work.Spaces.pz_pth_comm (f := Work.Spaces.pth f)
      (((smoothOpen_pthIter hf 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))).of_le (by simp))).symm
  show Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [hstep1, hstep2]

/-- **Boundedness of a slice and of its derivative from the weighted `L²`-bound on the second
derivative.**  If `u` is `C²` on the open interval, the second `θ`-derivative of `u` agrees there
with `v`, and `v²·sEta` is integrable on `Iθ`, then `u` and `u'` are bounded on the open
interval.  (The route is the one of `abs_le_of_sq_mul_sEta`: `v²·sEta` integrable forces
`v ∈ L¹` because `sEta ≥ 1`, and an oscillation bound plus one more integration bounds `u'` and
`u`.) -/
theorem exists_bdd_of_sq_mul_sEta {u v : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv (deriv u) θ = v θ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  have hae : (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hv θ hθ]
  exact Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm (hint.congr hae.symm)

/-- The eight endpoint values, at the two ends of the angular interval, of the four functions
occurring in `weakSliceBounds` (the slice `Ψ(z,·)` and its three partials).  Nothing is assumed
about `Ψ` for `θ < 0`, so these are simply real numbers to be absorbed into the constant `M`;
their finite sum is what enters `M`. -/
noncomputable def endVals (z : ℝ) (Ψ : ℝ → ℝ → ℝ) : Finset ℝ :=
  {|Ψ z 0|, |Work.Spaces.pth Ψ z 0|, |Work.Spaces.pz Ψ z 0|,
    |Work.Spaces.pz (Work.Spaces.pth Ψ) z 0|, |Ψ z (Real.pi / 2)|,
    |Work.Spaces.pth Ψ z (Real.pi / 2)|, |Work.Spaces.pz Ψ z (Real.pi / 2)|,
    |Work.Spaces.pz (Work.Spaces.pth Ψ) z (Real.pi / 2)|}

/-- **Pointwise bounds on the angular slices of a weak datum.**

For every `z > 0` the four functions `θ ↦ Ψ(z,θ)`, `θ ↦ ∂_θΨ(z,θ)`, `θ ↦ ∂_zΨ(z,θ)` and
`θ ↦ ∂_z∂_θΨ(z,θ)` are bounded on the angular interval `Iθ = [0,π/2]`.

The bounds on the open interval are those of `exists_bdd_of_sq_mul_sEta`, applied to the two
slices `u = Ψ(z,·)` and `u = ∂_zΨ(z,·)`: their second `θ`-derivatives are the slots
`∂_θθΨ` and `∂_z∂_θθΨ` of `Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)` (available because
`k ≥ 2`), and `∂_θθ∂_zΨ = ∂_z∂_θθΨ` is Clairaut (`pthIter2_pz_eqOn`).  At the two endpoints the
values are those of an arbitrary function `Ψ : ℝ → ℝ → ℝ` (nothing is assumed for `θ < 0`), so
they are simply absorbed into the constant `M`. -/
theorem weakSliceBounds {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Ψ z θ| ≤ M ∧
      |Work.Spaces.pth Ψ z θ| ≤ M ∧
      |Work.Spaces.pz Ψ z θ| ≤ M ∧
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ| ≤ M := by
  intro z hz
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hS 2
  -- ## The two `ℋ^k`-slots as honest `L²(sEta)` statements on the slice `z`
  have hI0 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    simpa [Work.FTS.EllipticEst.sEta]
      using Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hB h.memB 0 (by omega) hz
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 := Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hB h.memB 1 (by omega) hz
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iθ := h1.const_mul _
    refine h2.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.FTS.EllipticEst.sEta]
    field_simp
  -- ## The two slices and their second `θ`-derivatives
  have hu1 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.curry_θ hz).of_le (by simp)
  have hu2 : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.pz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.pz.curry_θ hz).of_le (by simp)
  have hv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => Ψ z θ')) θ = Work.Spaces.pthIter 2 Ψ z θ := by
    intro θ hθ
    show Work.Spaces.pthIter 2 Ψ z θ = Work.Spaces.pthIter 2 Ψ z θ
    rfl
  have hv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => Work.Spaces.pz Ψ z θ')) θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := by
    intro θ hθ
    show Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
    exact pthIter2_pz_eqOn hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  obtain ⟨C1, hC1pos, hC1⟩ := exists_bdd_of_sq_mul_sEta hu1 hv1 hI0
  obtain ⟨C2, hC2pos, hC2⟩ := exists_bdd_of_sq_mul_sEta hu2 hv2 hI2
  -- ## Assembly: the interior constant plus the eight endpoint values
  have hA0 : 0 ≤ max C1 C2 := hC1pos.le.trans (le_max_left _ _)
  have hVnn : ∀ y ∈ endVals z Ψ, 0 ≤ y := by
    intro y hy
    simp only [endVals, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h | h <;> · rw [h]; positivity
  have hT0 : 0 ≤ (endVals z Ψ).sum id := Finset.sum_nonneg hVnn
  refine ⟨max C1 C2 + (endVals z Ψ).sum id, add_nonneg hA0 hT0, ?_⟩
  intro θ hθ
  have hmid : max C1 C2 ≤ max C1 C2 + (endVals z Ψ).sum id := le_add_of_nonneg_right hT0
  have hEnd : ∀ x ∈ endVals z Ψ, x ≤ max C1 C2 + (endVals z Ψ).sum id := by
    intro x hx
    exact (Finset.single_le_sum hVnn hx).trans (le_add_of_nonneg_left hA0)
  rcases eq_or_lt_of_le hθ.1 with h0 | h0lt
  · subst h0
    exact ⟨hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals]),
      hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals])⟩
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpit
    · subst hpi
      exact ⟨hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals]),
        hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals])⟩
    · -- interior point: use the two boundedness statements
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0lt, hpit⟩
      have hb1 := hC1 θ hθ'
      have hb2 := hC2 θ hθ'
      have hcomm : deriv (fun θ' : ℝ => Work.Spaces.pz Ψ z θ') θ
          = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := by
        show Work.Spaces.pth (Work.Spaces.pz Ψ) z θ
          = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ
        exact (Work.Spaces.pz_pth_comm (f := Ψ)
          ((hS.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
            (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))).of_le (by simp))).symm
      exact ⟨(hb1.2.trans (le_max_left C1 C2)).trans hmid,
        (hb1.1.trans (le_max_left C1 C2)).trans hmid,
        (hb2.2.trans (le_max_right C1 C2)).trans hmid,
        ((hcomm ▸ hb2.1).trans (le_max_right C1 C2)).trans hmid⟩

end Work.FTS.EllipticEst.remov.SourceBound
end
