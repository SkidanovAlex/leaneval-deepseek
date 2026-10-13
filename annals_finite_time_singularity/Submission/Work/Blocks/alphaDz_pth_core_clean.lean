import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

/-!
# The `α D_z ∂_θ` interpolation core

This file contains the target `Work.Blocks.alphaDz_pth_core_clean` together with the small
vocabulary layer (`sig`, `mixI`, `ddI`, `ttI`, `dI`, `mixLin`, `Honest`) in which the analytic
interpolation lemma that the proof consumes (`Work.Blocks.interp_core`) is phrased.

Mathematically the target is the *interpolation* estimate of the paper's §7,

`α² ∫∫ (D_z∂_θG)² w² σ_η ≤ C (α⁴ ∫∫ (D_z²G)² w² σ_η + ∫∫ (∂_θ²G)² w² σ_η
                              + α² ∫∫ (D_zG)² w² σ_η)`,

applied summand by summand to the `z`-family of the weighted `ℋ^k`-integrand of `D_z∂_θV` with
`G := D_z^j V`, plus the algebraic treatment of the mixed (`D_θ`) family.
-/

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The angular weight `σ_η(θ) = sin(2θ)^{-η}` (written out rather than imported so that this
module only depends on `Mathlib` and the two definitional modules). -/
noncomputable def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The weighted energy `∫∫ (D_z∂_θG)² w² σ_η` of a pair of functions (an iterated integral,
as in the paper). -/
noncomputable def mixI (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ

/-- The weighted energy `∫∫ (D_z²G)² w² σ_η`. -/
noncomputable def ddI (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ

/-- The weighted energy `∫∫ (∂_θ²G)² w² σ_η`. -/
noncomputable def ttI (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ

/-- The weighted energy `∫∫ (D_zG)² w² σ_η`. -/
noncomputable def dI (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ

/-- The `lintegral` form of the left hand side of the interpolation: this is the honest
value of `∫∫ (D_z∂_θG)² w² σ_η`, and it is `≤ (mixI G)`-compatible through
`integral_eq_lintegral_of_nonneg_ae`.  Working with it avoids all questions of
integrability of the left-hand side. -/
noncomputable def mixLin (G : ℝ → ℝ → ℝ) : ENNReal :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
    (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)

/-- The honesty package of the interpolation's right hand side: the three functionals
`ddI`, `ttI`, `dI` are honest both slicewise (in `θ`, for every `z ∈ Iz`) and after
integration in `z`. -/
noncomputable def Honest (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz

/-! ## Elementary facts about the weights -/

theorem w_zero : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]

theorem sig_pos {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) : 0 < sig θ := by
  rw [sig]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) _

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig]; exact Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem sig_zero_left : sig 0 = 0 := by
  rw [sig, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by norm_num [Work.Spaces.eta])]

theorem sig_zero_right : sig (Real.pi / 2) = 0 := by
  rw [sig, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
    Real.zero_rpow (by norm_num [Work.Spaces.eta])]

theorem gam_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem Wt_zero_left {α : ℝ} (hα : 0 < α) (z : ℝ) : Work.Spaces.Wt α z 0 = 0 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.gam]; intro h; linarith), mul_zero]

theorem Wt_zero_right {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Work.Spaces.Wt α z (Real.pi / 2) = 0 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta,
    show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
    Real.zero_rpow (by rw [Work.Spaces.gam]; intro h; linarith), mul_zero]

theorem Wt_zero_z (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  rw [Work.Spaces.Wt, w_zero, zero_mul]

/-! ## Commutation of `∂_θ` with the `D_z`-iterates on the open quadrant -/

/-- `∂_θ (D_z g) = D_z (∂_θ g)` at a point where `g` is `C²`. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz g z θ') θ
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    (Work.Spaces.pz_pth_comm hg).symm
  rw [h1, h3]
  rfl

/-- `D_z^j (D_z g) = D_z^{j+1} g`. -/
theorem DzIter_succ_apply (j : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz g) = Work.Spaces.DzIter (j + 1) g := by
  induction j with
  | zero => rfl
  | succ j ih =>
      calc Work.Spaces.DzIter (j + 1) (Work.Spaces.Dz g)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dz g)) := rfl
        _ = Work.Spaces.Dz (Work.Spaces.DzIter (j + 1) g) := by rw [ih]
        _ = Work.Spaces.DzIter (j + 1 + 1) g := rfl

/-- A `C^∞`-on-the-open-quadrant function is `C²` at every point of the open quadrant. -/
theorem SmoothOpen.contDiffAt_two {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  ((hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.EllipticEst.Q0).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩))).of_le
    (by simp [Work.Stability.smoothOrder])

theorem SmoothOpen.DzIter_contDiffAt_two {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) (z, θ) :=
  SmoothOpen.contDiffAt_two (hf.DzIter j) hz hθ hθ'

/-- `∂_θ` commutes with the `D_z`-iterates on the open quadrant. -/
theorem pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ :=
        pth_Dz_apply (SmoothOpen.DzIter_contDiffAt_two hf j hz hθ hθ')
      have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := by
        have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z' θ)
            =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, hθ'⟩)
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j + 1) f)) (z, θ)
          = Function.uncurry (Work.Spaces.DzIter (j + 1) (Work.Spaces.pth f)) (z, θ)
      simp only [Function.uncurry]
      rw [show Work.Spaces.DzIter (j + 1) f
            = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
          hstep, hcongr]
      rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))
            = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.pth f)) from
            (DzIter_succ_apply j (Work.Spaces.pth f)).symm]
      rw [DzIter_succ_apply j (Work.Spaces.pth f)]

/-! ## The `lintegral` presentation of a weighted energy -/

/-- The `lintegral`-based value of an angular integrand `h`: this is the honest value of the
iterated integral `∫_z ∫_θ h`, and it agrees with the iterated *Bochner* integral whenever the
latter is honest (both are then `(∫⁻_z ofReal (∫_θ h)).toReal`). -/
noncomputable def LI (h : ℝ → ℝ → ℝ) : ℝ :=
  (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, h z θ)).toReal

theorem LI_nonneg (h : ℝ → ℝ → ℝ) : 0 ≤ LI h := ENNReal.toReal_nonneg

/-- For a nonnegative angular integrand the `lintegral` presentation is the iterated integral. -/
theorem LI_eq_integral {h : ℝ → ℝ → ℝ} (hnn : ∀ z θ, 0 ≤ h z θ)
    (hmeas : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, h z θ) (volume.restrict Work.Spaces.Iz)) :
    LI h = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, h z θ :=
  (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => hnn z θ) hmeas).symm

/-- `ofReal` of a finite sum of nonnegative terms, inside a `lintegral`. -/
theorem lintegral_ofReal_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ)
    (hmeas : ∀ i ∈ s, AEMeasurable (fun z : ℝ => ENNReal.ofReal (g i z))
      (volume.restrict Work.Spaces.Iz))
    (hnn : ∀ z i, 0 ≤ g i z) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∑ i ∈ s, g i z))
      = ∑ i ∈ s, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (g i z) := by
  rw [show (fun z : ℝ => ENNReal.ofReal (∑ i ∈ s, g i z))
      = fun z => ∑ i ∈ s, ENNReal.ofReal (g i z) from by
    funext z
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn z i)]
  exact MeasureTheory.lintegral_finsetSum' s hmeas

/-- `(∑ a_i).toReal ≤ ∑ a_i.toReal` for a finite sum of `ℝ≥0∞` numbers. -/
theorem toReal_sum_le {ι : Type*} (s : Finset ι) (a : ι → ENNReal) :
    (∑ i ∈ s, a i).toReal ≤ ∑ i ∈ s, (a i).toReal := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact le_trans ENNReal.toReal_add_le (add_le_add le_rfl ih)

/-- At `z = 0` the radial weight vanishes and with it every summand of the `ℋ^k`-integrand. -/
theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, w_zero, zero_div, mul_zero, Work.Spaces.Wt,
    Work.Spaces.wTheta, zero_mul]
  simp

/-- **The `ℋ^k`-square is bounded by the sum of the `lintegral`-values of the summands of its
integrand.**  `sl i` are the summands (the `D_z`-summands and the mixed `D_θ`-summands). -/
theorem HkSq_le_sum_LI {α : ℝ} {k n : ℕ} (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (sl : ℕ → ℝ → ℝ → ℝ)
    (hsl_cont : ∀ i, ContinuousOn (Function.uncurry (sl i)) Work.FTS.EllipticEst.Q0)
    (hsl_nn : ∀ i z θ, 0 ≤ sl i z θ)
    (hsl_zero : ∀ i θ, sl i 0 θ = 0)
    (hmem : Work.Spaces.HkMem α k f)
    (hdecomp : ∀ z θ, Work.Spaces.HkIntegrand α k f z θ = ∑ i ∈ Finset.range n, sl i z θ) :
    Work.Spaces.HkSq α k f ≤ ∑ i ∈ Finset.range n, LI (sl i) := by
  classical
  have hsm := (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf
  rw [Work.FTS.EllipticEst.HkSq_eq_lintegral α k f hsm]
  have hIz_meas : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have haesm : ∀ i, AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, sl i z θ) (volume.restrict Work.Spaces.Iz) := fun i =>
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hsl_cont i)).integral_prod_right'
  have hmeas : ∀ i ∈ Finset.range n, AEMeasurable
      (fun z : ℝ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, sl i z θ))
      (volume.restrict Work.Spaces.Iz) := fun i _ => (haesm i).aemeasurable.ennreal_ofReal
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ ∑ i ∈ Finset.range n, ∫ θ in Work.Spaces.Iθ, sl i z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have h0 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k f θ
      rw [h0, integral_zero]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [show (fun θ : ℝ => sl i 0 θ) = fun _ => (0 : ℝ) from funext (hsl_zero i),
        integral_zero]
    · have hstep : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range n, sl i z θ)
          ≤ ∑ i ∈ Finset.range n, ∫ θ in Work.Spaces.Iθ, sl i z θ := by
        by_cases h : IntegrableOn (fun θ : ℝ => ∑ i ∈ Finset.range n, sl i z θ)
            Work.Spaces.Iθ
        · have hEach : ∀ i ∈ Finset.range n, IntegrableOn (fun θ : ℝ => sl i z θ)
              Work.Spaces.Iθ := by
            intro i hi
            refine Integrable.mono' h ((Work.Spaces.aesm_slice_of_continuousOn_Qd _
              (hsl_cont i) hzpos)) ?_
            rw [ae_restrict_iff' hIθ_meas]
            exact Eventually.of_forall fun θ _ => by
              rw [Real.norm_of_nonneg (hsl_nn i z θ)]
              exact Finset.single_le_sum (fun j _ => hsl_nn j z θ) hi
          rw [MeasureTheory.integral_finsetSum (Finset.range n) hEach]
        · rw [MeasureTheory.integral_undef h]
          exact Finset.sum_nonneg fun i _ => integral_nonneg fun θ => hsl_nn i z θ
      calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          = ∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range n, sl i z θ := by
            rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
                = fun θ => ∑ i ∈ Finset.range n, sl i z θ from funext (hdecomp z)]
        _ ≤ _ := hstep
  have hbase_fin : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact ENNReal.ofReal_ne_top
  have hslot_le : ∀ i ∈ Finset.range n, (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, sl i z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro i hi
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [ae_restrict_iff' hIz_meas]
    refine Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => hsl_nn i z θ)
      (hmem.1 z hz) (Filter.Eventually.of_forall fun θ => ?_)
    rw [hdecomp z θ]
    exact Finset.single_le_sum (fun j _ => hsl_nn j z θ) hi
  have hsum_fin : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ θ in Work.Spaces.Iθ, sl i z θ)) ≠ ⊤ := by
    rw [lintegral_ofReal_sum _ _ hmeas (fun z i => integral_nonneg fun θ => hsl_nn i z θ)]
    exact (ENNReal.sum_lt_top.mpr fun i hi =>
      lt_of_le_of_lt (hslot_le i hi) (lt_top_iff_ne_top.mpr hbase_fin)).ne
  calc (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)).toReal
      ≤ (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∑ i ∈ Finset.range n,
            ∫ θ in Work.Spaces.Iθ, sl i z θ)).toReal :=
        ENNReal.toReal_mono hsum_fin (by
          refine MeasureTheory.lintegral_mono_ae ?_
          rw [ae_restrict_iff' hIz_meas]
          exact Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal (hpt z hz))
    _ = (∑ i ∈ Finset.range n, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, sl i z θ)).toReal := by
        rw [lintegral_ofReal_sum _ _ hmeas (fun z i => integral_nonneg fun θ => hsl_nn i z θ)]
    _ ≤ _ := toReal_sum_le _ _
    _ = ∑ i ∈ Finset.range n, LI (sl i) := rfl

theorem alphaDz_pth_core_clean (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by sorry

end Work.Blocks
