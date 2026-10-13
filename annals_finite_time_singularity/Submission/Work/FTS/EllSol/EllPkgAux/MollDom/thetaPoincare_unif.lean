import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thetaPoincare

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Uniform weighted angular Poincaré inequality with vanishing mean.**

The sibling `thetaPoincare` proves the estimate with a constant depending on `f`; the proof
there in fact uses the *same* explicit constant `10000 * (π/2) + 1` for every `f`, so the
quantifier can be exchanged.  We simply repeat that argument with the constant fixed in
advance.

For `f` differentiable on the open interval `(0, π/2)` with derivative `f'`, with `(f')²`
and `f` integrable on `Iθ = [0, π/2]` and vanishing (unweighted) mean over `Iθ`, the
weighted square of `f` against the angular weight `thEta θ = sin(2θ)^{-η}` is controlled
by the *unweighted* `L²`-norm of the derivative, with a constant independent of `f`.

Proof.  By the mean-zero Poincaré sup bound (`Honest.PthCore.mean_zero_sup_bound`) every
interior value obeys `|f θ| ≤ K := ∫_{Iθ} |f'|` (the increment form
`f θ = (π/2)⁻¹ ∫_{Iθ} (f θ - f t) dt` of the vanishing mean together with the fundamental
theorem of calculus on the intervals between `θ` and `t`).  Hence
`thEta θ * (f θ)² ≤ K² * thEta θ` a.e. on `Iθ`, and integrating against the weight
(`∫_{Iθ} thEta ≤ 10⁴`) gives `∫_{Iθ} thEta f² ≤ 10⁴ K²`.  Finally Cauchy–Schwarz on `Iθ`
turns `K = ∫_{Iθ} |f'|` into `K² ≤ (π/2) ∫_{Iθ} (f')²`. -/
theorem thetaPoincare_unif : ∃ C : ℝ, 0 < C ∧ ∀ {f f' : ℝ → ℝ},
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ) →
    MeasureTheory.IntegrableOn (fun θ => (f' θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, f θ) = 0 →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ C * ∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2 := by
  refine ⟨10000 * (Real.pi / 2) + 1, by positivity, ?_⟩
  intro f f' hd hf'int hfint hmean
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hlt : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- interval integrability of `f` on `[0, π/2]`
  have hIf : IntervalIntegrable f volume (0 : ℝ) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hfint
  -- on the open interval the derivative of `f` is `f'`
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv f θ = f' θ :=
    fun θ hθ => (hd θ hθ).deriv
  have haeeq : deriv f =ᵐ[volume.restrict Work.Spaces.Iθ] f' := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => deriv f θ = f' θ) (fun θ hθ => hderiv θ hθ)
    exact h
  have hvol_lt : volume (Work.Spaces.Iθ) < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable f' (volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv f).aestronglyMeasurable.congr haeeq
  -- `f'` is integrable on `Iθ` (its square is, and `Iθ` has finite measure)
  have hIf' : IntegrableOn f' Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.H2W.integrableOn_of_sq_integrableOn haesm hvol_lt hf'int
  have hIntf' : IntervalIntegrable f' volume (0 : ℝ) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hIf'
  -- the vanishing mean as an interval integral
  have hmeanz : (∫ x in (0 : ℝ)..(Real.pi / 2), f x) = 0 := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hmean
  -- the mean-zero sup bound
  have hsup : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f x| ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), |f' t| :=
    Work.FTS.EllipticEst.Honest.PthCore.mean_zero_sup_bound (a := 0) (b := Real.pi / 2)
      hlt hd hIf hIntf' hmeanz
  set K : ℝ := ∫ t in (0 : ℝ)..(Real.pi / 2), |f' t| with hK
  have hKnn : 0 ≤ K := by
    rw [hK, intervalIntegral.integral_of_le hle]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K ^ 2 := by
    intro θ hθ
    have h1 : |f θ| ≤ K := by rw [hK]; exact hsup θ hθ
    calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- the pointwise bound holds a.e. on `Iθ`
  have haept : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2 ≤ Work.FTS.EllipticEst.thEta θ * K ^ 2 := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.thEta θ * K ^ 2)
      (fun θ hθ => mul_le_mul_of_nonneg_left (hpt θ hθ)
        (Work.FTS.EllipticEst.thEta_nonneg (Set.Ioo_subset_Icc_self hθ)))
    exact h
  have hWint : IntegrableOn Work.FTS.EllipticEst.thEta Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hRHSint : IntegrableOn (fun θ => Work.FTS.EllipticEst.thEta θ * K ^ 2) Work.Spaces.Iθ :=
    hWint.mul_const (K ^ 2)
  -- measurability of the weighted integrand
  have hcont : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt
  have hsin_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id)
  have hw_cont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) _
    exact hsin_cont.rpow_const (fun x hx => Or.inl (ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos]))))
  have hg_cont : ContinuousOn (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hw_cont.mul (hcont.pow 2)
  have hres : volume.restrict (Work.Spaces.Iθ)
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm
  have hAESM : AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [hres]
    exact hg_cont.aestronglyMeasurable measurableSet_Ioo
  have hLHSint : IntegrableOn (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      Work.Spaces.Iθ := by
    refine hRHSint.mono' hAESM ?_
    filter_upwards [haept, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ hmem
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hmem) (sq_nonneg _))]
    exact hθ
  have hmono : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * K ^ 2 :=
    MeasureTheory.integral_mono_ae hLHSint hRHSint haept
  have hval : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * K ^ 2)
      = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ) * K ^ 2 :=
    MeasureTheory.integral_mul_const (K ^ 2) _
  have hbound1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ 10000 * K ^ 2 := by
    have h1 := hmono
    rw [hval] at h1
    exact h1.trans
      (mul_le_mul_of_nonneg_right Work.FTS.EllipticEst.integrableOn_thEta.2 (sq_nonneg K))
  -- Cauchy–Schwarz: `K² ≤ (π/2) ∫ (f')²`
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul,
      mul_one, sub_zero]
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
    haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr hvol_lt.ne
    exact MeasureTheory.memLp_const (1 : ℝ)
  have hmemabs : MemLp (fun θ : ℝ => |f' θ|) 2 (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ : ℝ => |f' θ|) (by simpa only [Real.norm_eq_abs] using haesm.norm)]
    have h2 : Integrable (fun θ : ℝ => (|f' θ|) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
      rw [show (fun θ : ℝ => (|f' θ|) ^ 2) = (fun θ : ℝ => (f' θ) ^ 2)
        from funext (fun θ => sq_abs (f' θ))]
      exact hf'int
    exact h2
  have hKabs : K = ∫ θ in Work.Spaces.Iθ, |f' θ| := by
    rw [hK, intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  have hcs : K ^ 2 ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) := by
    have h := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) (u := fun _ : ℝ => (1 : ℝ))
      (v := fun θ : ℝ => |f' θ|) hmem1 hmemabs
    simp only [one_mul, one_pow, sq_abs] at h
    rw [hvol] at h
    rw [← hKabs] at h
    exact h
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ 10000 * K ^ 2 := hbound1
    _ ≤ 10000 * ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = (10000 * (Real.pi / 2)) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) := by ring
    _ ≤ (10000 * (Real.pi / 2) + 1) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hBnn

end Work.FTS.EllSol.EllPkgAux.MollDom
