import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the angular weight `σ θ = sin(2θ)^{-η}` and the
constraint profile `ψ θ = sin θ cos²θ` -/

/-- The constraint profile `ψ θ = sin θ cos²θ` of the solvability condition. -/
private def psi (θ : ℝ) : ℝ := Real.sin θ * Real.cos θ ^ 2

private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private lemma sEta_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

private lemma sEta_zero_left : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

private lemma sEta_zero_right : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

private lemma sEta_integrableOn :
    Integrable (Work.FTS.EllipticEst.sEta) (volume.restrict Iθ) :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

private lemma psi_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ psi θ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  show 0 ≤ Real.sin θ * Real.cos θ ^ 2
  exact mul_nonneg hs (sq_nonneg _)

private lemma psi_zero_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : psi θ = 0 := by
  have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
    rcases lt_or_eq_of_le hθ.1 with hlt | heq
    · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt (fun hgt => h ⟨hlt, hgt⟩)))
    · exact Or.inl heq.symm
  rcases hcases with h0 | hpi
  · rw [h0]
    show Real.sin 0 * Real.cos 0 ^ 2 = 0
    simp
  · rw [hpi]
    show Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0
    rw [Real.cos_pi_div_two]
    ring

private lemma psi_continuous : Continuous psi := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

private lemma psi_integrableOn : Integrable (fun θ : ℝ => psi θ) (volume.restrict Iθ) :=
  psi_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- `∫₀^{π/2} sin θ cos²θ dθ = 1/3`, by the fundamental theorem of calculus
with the antiderivative `θ ↦ -cos³θ/3`. -/
private lemma psi_integral : (∫ θ in Iθ, psi θ) = 1 / 3 := by
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (psi θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.cos θ) ^ 2) (Real.cos θ) := by
      simpa using hasDerivAt_pow 3 (Real.cos θ)
    refine ((h2.comp θ h1).neg.div_const 3).congr_deriv ?_
    rw [psi]
    ring
  have hInt : IntervalIntegrable psi volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (by linarith [Real.pi_pos])).mpr
      (MeasureTheory.IntegrableOn.mono_set psi_integrableOn
        (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  have hFTC : ∫ t in (0 : ℝ)..(Real.pi / 2), psi t
      = (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (Real.pi / 2)
        - (fun t : ℝ => -((Real.cos t) ^ 3) / 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hInt
  calc (∫ θ in Iθ, psi θ) = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), psi θ := by
        rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2), psi t :=
        (intervalIntegral.integral_of_le (by linarith [Real.pi_pos])).symm
    _ = 1 / 3 := by
        rw [hFTC]
        change -((Real.cos (Real.pi / 2)) ^ 3) / 3 - (-((Real.cos 0) ^ 3) / 3) = 1 / 3
        norm_num [Real.cos_pi_div_two, Real.cos_zero]

/-! ## The fundamental theorem of calculus on the open interval -/

/-- **Increment bound.**  A `C¹` function on the open interval has increments bounded by the
total mass of `|f'|` over `Iθ`. -/
private lemma abs_sub_le_integral_abs_deriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ))
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hab : a ≤ b) :
    |f a - f b| ≤ ∫ θ in Iθ, |deriv f θ| := by
  have hsub : Set.Icc a b ⊆ Iθ := fun x hx =>
    ⟨le_trans (le_of_lt ha.1) hx.1, le_trans hx.2 (le_of_lt hb.2)⟩
  have hIoo : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have h1 : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.IntegrableOn.mono_set hint hsub
  have h2 : Integrable (fun θ : ℝ => deriv f θ) (volume.restrict (Set.Icc a b)) :=
    h1.mono' (measurable_deriv f).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simp [Real.norm_eq_abs]))
  have hII : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) hab).mpr
      (MeasureTheory.IntegrableOn.mono_set h2 (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hf.differentiableOn (by norm_num)).hasDerivAt
      (isOpen_Ioo.mem_nhds ⟨(hIoo x hx).1, (hIoo x hx).2⟩)
  have hFTC : ∫ x in a..b, deriv f x = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII
  rw [abs_sub_comm]
  calc |f b - f a| = |∫ x in a..b, deriv f x| := by rw [hFTC]
    _ ≤ ∫ x in a..b, |deriv f x| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume)
            (f := fun x : ℝ => deriv f x) hab
    _ = ∫ x in Set.Ioc a b, |deriv f x| := intervalIntegral.integral_of_le hab
    _ ≤ ∫ x in Iθ, |deriv f x| := by
        refine MeasureTheory.setIntegral_mono_set (μ := volume)
          (f := fun x : ℝ => |deriv f x|) (s := Set.Ioc a b) (t := Iθ) hint ?_ ?_
        · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => abs_nonneg (deriv f x))
        · exact Filter.Eventually.of_forall (fun x hx => hsub ⟨le_of_lt hx.1, hx.2⟩)

/-! ## The constraint implies an `L¹` bound on the function -/

/-- **The constraint bounds `f` pointwise.**  If the moment `∫_θ f ψ` of a `C¹` function on the
open interval vanishes (`ψ = sin θ cos²θ` has `∫_θ ψ = 1/3 > 0`), then
`|f t| ≤ ∫_θ |f'|` for every interior `t`. -/
private lemma abs_le_integral_abs_deriv_of_constraint {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ))
    (hintf : Integrable (fun θ : ℝ => f θ * psi θ) (volume.restrict Iθ))
    (hzero : (∫ θ in Iθ, f θ * psi θ) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |f t| ≤ ∫ θ in Iθ, |deriv f θ| := by
  have hincr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f t - f θ| ≤ ∫ θ in Iθ, |deriv f θ| := by
    intro θ hθ
    rcases le_total t θ with hle | hle
    · exact abs_sub_le_integral_abs_deriv hf hint ht hθ hle
    · exact (abs_sub_comm (f t) (f θ)).trans_le (abs_sub_le_integral_abs_deriv hf hint hθ ht hle)
  have hftpsi : Integrable (fun θ : ℝ => f t * psi θ) (volume.restrict Iθ) :=
    psi_integrableOn.const_mul (f t)
  have hId : (∫ θ in Iθ, (f t * psi θ - f θ * psi θ)) = f t * (∫ θ in Iθ, psi θ) := by
    rw [MeasureTheory.integral_sub hftpsi hintf, MeasureTheory.integral_const_mul, hzero]
    ring
  have hpt : ∀ θ ∈ Iθ,
      |f t * psi θ - f θ * psi θ| ≤ (∫ θ in Iθ, |deriv f θ|) * psi θ := by
    intro θ hθ
    by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hnn : 0 ≤ psi θ := psi_nonneg hθ
      have habs : |psi θ| = psi θ := abs_of_nonneg hnn
      rw [show f t * psi θ - f θ * psi θ = (f t - f θ) * psi θ by ring, abs_mul, habs]
      exact mul_le_mul_of_nonneg_right (hincr θ hθo) hnn
    · rw [psi_zero_of_not_mem_Ioo hθ hθo]
      simp
  have hchain : |f t| * (1 / 3) ≤ (∫ θ in Iθ, |deriv f θ|) * (1 / 3) := by
    have h13 : |(1 : ℝ) / 3| = 1 / 3 := abs_of_pos (by norm_num)
    have h2 : |∫ θ in Iθ, (f t * psi θ - f θ * psi θ)| = |f t| * (1 / 3) := by
      rw [hId, psi_integral, abs_mul, h13]
    calc |f t| * (1 / 3) = |∫ θ in Iθ, (f t * psi θ - f θ * psi θ)| := h2.symm
      _ ≤ ∫ θ in Iθ, |f t * psi θ - f θ * psi θ| := by
          simpa only [Real.norm_eq_abs] using
            MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
              (f := fun θ : ℝ => f t * psi θ - f θ * psi θ)
      _ ≤ ∫ θ in Iθ, (∫ θ in Iθ, |deriv f θ|) * psi θ := by
          refine MeasureTheory.integral_mono_ae (hftpsi.sub hintf).abs
            (psi_integrableOn.const_mul _) ?_
          exact ae_restrict_of_forall_mem measurableSet_Icc hpt
      _ = (∫ θ in Iθ, |deriv f θ|) * (1 / 3) := by
          rw [MeasureTheory.integral_const_mul, psi_integral]
  nlinarith [hchain]

/-! ## The constrained σ-Poincaré inequality -/

theorem SigmaPoincare : ∃ C : ℝ, 0 < C ∧
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => f θ * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, f θ * Real.sin θ * Real.cos θ ^ 2) = 0 →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal C
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) := by
  -- the weight is integrable with positive mass
  have hSpos : 0 < ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := by
    have h3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ))
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_mono_ae
        (μ := volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
        (f := fun _ : ℝ => (1 : ℝ)) (g := Work.FTS.EllipticEst.sEta)
        (MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
          (C := (1 : ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp))
        (MeasureTheory.IntegrableOn.mono_set sEta_integrableOn
          (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hz : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
      have h := Real.rpow_le_rpow_of_nonpos hpos hle hz
      simpa only [Work.FTS.EllipticEst.sEta, Real.one_rpow] using h
    have h4 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.setIntegral_mono_set (μ := volume)
        (f := Work.FTS.EllipticEst.sEta) (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (t := Iθ)
        sEta_integrableOn ?_ ?_
      · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => sEta_nonneg hx)
      · exact Filter.Eventually.of_forall (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have h5 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one, sub_zero]
    linarith [h3, h4, h5, Real.pi_pos]
  refine ⟨(Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ), ?_, ?_⟩
  · exact mul_pos (by linarith [Real.pi_pos]) hSpos
  · intro f hf hintf hzero
    -- rewrite the statement's integrands using `psi`
    have hintf' : Integrable (fun θ : ℝ => f θ * psi θ) (volume.restrict Iθ) := hintf
    have hzero' : (∫ θ in Iθ, f θ * psi θ) = 0 := by
      have h0 : (∫ θ in Iθ, f θ * psi θ) = ∫ θ in Iθ, f θ * Real.sin θ * Real.cos θ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by
          show f θ * psi θ = f θ * Real.sin θ * Real.cos θ ^ 2
          rw [psi]; ring))
      rw [h0, hzero]
    by_cases hQ : (∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) = ⊤
    · -- the right hand side is `⊤`
      rw [hQ, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
        (mul_pos (by linarith [Real.pi_pos]) hSpos))]
      exact le_top
    · -- the right hand side is finite
      have hmeas : AEStronglyMeasurable (fun θ : ℝ => (deriv f θ) ^ 2)
          (volume.restrict Iθ) :=
        ((measurable_deriv f).pow_const 2).aestronglyMeasurable
      have hnn : 0 ≤ᵐ[volume.restrict Iθ] (fun θ : ℝ => (deriv f θ) ^ 2) :=
        ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _)
      have hQint : Integrable (fun θ : ℝ => (deriv f θ) ^ 2) (volume.restrict Iθ) :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := volume.restrict Iθ)
          hmeas hnn).mp hQ
      have hQeq : ENNReal.ofReal (∫ θ in Iθ, (deriv f θ) ^ 2)
          = ∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQint hnn
      -- `|f'|` is integrable
      have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Iθ) := by
        haveI : IsFiniteMeasure (volume.restrict Iθ) :=
          MeasureTheory.isFiniteMeasure_restrict.mpr
            (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        exact MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
      have hmaj : Integrable (fun θ : ℝ => (deriv f θ) ^ 2 + 1) (volume.restrict Iθ) :=
        hQint.add hconst
      have habsint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ) := by
        refine hmaj.mono'
          (by simpa only [Real.norm_eq_abs] using
            (measurable_deriv f).norm.aestronglyMeasurable) ?_
        exact Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (deriv f x))]
          nlinarith [sq_abs (deriv f x), sq_nonneg (|deriv f x| - 1 / 2)])
      -- Cauchy–Schwarz turns the `L¹` bound into an `L²` bound
      have hA2 : (∫ θ in Iθ, |deriv f θ|) ^ 2
          ≤ (Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2) := by
        have hvol : (∫ θ in Iθ, (1 : ℝ)) = Real.pi / 2 := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
            Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
            smul_eq_mul, mul_one, sub_zero]
        have hu : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Iθ) := by
          haveI : IsFiniteMeasure (volume.restrict Iθ) :=
            MeasureTheory.isFiniteMeasure_restrict.mpr
              (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          exact MeasureTheory.memLp_const (1 : ℝ)
        have hv : MemLp (fun θ : ℝ => |deriv f θ|) 2 (volume.restrict Iθ) := by
          rw [memLp_two_iff_integrable_sq (μ := volume.restrict Iθ)
            (f := fun θ : ℝ => |deriv f θ|)
            (by simpa only [Real.norm_eq_abs] using
              (measurable_deriv f).norm.aestronglyMeasurable)]
          simpa only [sq_abs] using hQint
        have hcs := Work.Spaces.cs_integral (s := Iθ) (u := fun _ : ℝ => (1 : ℝ))
          (v := fun θ : ℝ => |deriv f θ|) hu hv
        simp only [one_mul, one_pow, sq_abs] at hcs
        rw [hvol] at hcs
        exact hcs
      have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |f t| ≤ ∫ θ in Iθ, |deriv f θ| :=
        fun t ht => abs_le_integral_abs_deriv_of_constraint hf habsint hintf' hzero' ht
      -- pointwise comparison of the weighted integrands
      have hpt : ∀ θ ∈ Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
        intro θ hθ
        by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
        · have hSnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg hθ
          have hAnn : 0 ≤ ∫ θ in Iθ, |deriv f θ| :=
            MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg (deriv f x))
          have hAnn' : |(∫ θ in Iθ, |deriv f θ|)| = ∫ θ in Iθ, |deriv f θ| :=
            abs_of_nonneg hAnn
          have hft : (f θ) ^ 2 ≤ (∫ θ in Iθ, |deriv f θ|) ^ 2 := by
            refine (sq_le_sq).mpr ?_
            simpa only [hAnn'] using hbound θ hθo
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hft hSnn)
        · have hz : Work.FTS.EllipticEst.sEta θ = 0 := by
            have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
              rcases lt_or_eq_of_le hθ.1 with hlt | heq
              · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt (fun hgt => hθo ⟨hlt, hgt⟩)))
              · exact Or.inl heq.symm
            rcases hcases with h0 | hpi
            · rw [h0, sEta_zero_left]
            · rw [hpi, sEta_zero_right]
          rw [hz, mul_zero, mul_zero]
      have hstep1 : (∫⁻ θ in Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ∫⁻ θ in Iθ,
              ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
                * Work.FTS.EllipticEst.sEta θ) :=
        MeasureTheory.lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hpt)
      have hint2 : Integrable
          (fun θ : ℝ => (∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (volume.restrict Iθ) :=
        sEta_integrableOn.const_mul _
      have hnn2 : 0 ≤ᵐ[volume.restrict Iθ]
          (fun θ : ℝ => (∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
        ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
      have hstep2 : (∫⁻ θ in Iθ,
            ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
              * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2,
          MeasureTheory.integral_const_mul]
      have hSnn : 0 ≤ ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := le_of_lt hSpos
      have hkey : (∫ θ in Iθ, |deriv f θ|) ^ 2 * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
          ≤ ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫ θ in Iθ, (deriv f θ) ^ 2) := by
        have h1 : (∫ θ in Iθ, |deriv f θ|) ^ 2 * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
            ≤ ((Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2))
                * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_right hA2 hSnn
        have h2 : ((Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2))
              * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
            = ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫ θ in Iθ, (deriv f θ) ^ 2) := by ring
        rw [h2] at h1
        exact h1
      have hstep3 : (∫⁻ θ in Iθ,
            ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ENNReal.ofReal ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) := by
        have hCnn : 0 ≤ (Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ) :=
          mul_nonneg (by linarith [Real.pi_pos]) hSnn
        rw [hstep2, ← hQeq, ← ENNReal.ofReal_mul hCnn]
        exact ENNReal.ofReal_le_ofReal hkey
      exact hstep1.trans hstep3

end

end Work.FTS.EllipticEst.Honest
