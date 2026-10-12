import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.HighMass.Base
import Submission.Work.BoseFixB3.HighMassAux.lowMult_pairing
import Submission.Work.BoseFixB3.HighMassAux.parseval_L1L2
import Submission.Work.BoseFixB3.HighMassAux.plancherel_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass` — the one-body weighted Plancherel bound

`oneBody_box_le`: for `κ > 0`, `ℓ > 0` and a measurable `Ψ` bounded on the box,

`∫_{Λ}(Ψ − f_L(√−Δ)(θΨ))² ≤ (2π)⁻³ ∫_p (1 − f(‖p‖/κ))²·‖kinFT(θΨ)(p)‖²`,

the one-body content of FS `eq:QLs_giveNplusH` (`Q̄_LQ̄_L^* ≤ n_+^H`).  The proof is the
weak/duality argument: with `u = Ψ − f_L(√−Δ)Ψ` and the test function `φ = 1_Λ·u`, the
pairing identities `parseval_L1L2` (position/momentum pairing) and `lowMult_pairing`
(the multiplier pairing) compute `∫_Λ u² = (2π)⁻³∫_p Re(conj(kinFT φ)(1−f_L)kinFT(θΨ))`,
and Cauchy–Schwarz with `plancherel_L1L2` (for `φ`) closes the argument.

`oneBody_le_momForm`: the same bound with the `momForm` cut-off `1_{(d⁻²ℓ⁻¹,∞)}`, for both
`κ = (d²ℓ)⁻¹ > 0` (the pointwise symbol bound `one_sub_sq_le_momProj`) and `κ = 0`
(the degenerate case, where the multiplier formula degenerates and the identity
`momForm = ∫_Λ(mean-free part)²` is used instead).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMass

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix Work.BSKinetic
open Work.BoseFixB3.HighMassAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `lowMult` is bounded by the weighted `L¹`-norm of its symbol. -/
lemma abs_lowMult_le {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) {Ψ : ℝ³ → ℝ}
    (hΨc : Integrable (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ))) (x : ℝ³) :
    |lowMult fc κ ℓ Ψ x| ≤ ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, |fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
  have hcont : Continuous (kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ))) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hΨc
  have hgcont : Continuous (fun p : ℝ³ => fc.f (‖p‖ / κ)) :=
    fc.smooth.continuous.comp (continuous_norm.div_const κ)
  have hcsn : HasCompactSupport (fun p : ℝ³ => |fc.f (‖p‖ / κ)|) :=
    (lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ).comp_left
      (g := fun r : ℝ => |r|) (by simp)
  have hmaj : Integrable (fun p : ℝ³ => |fc.f (‖p‖ / κ)| *
      ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) :=
    Continuous.integrable_of_hasCompactSupport (hgcont.abs.mul hcont.norm) hcsn.mul_right
  have h1 : lowMult fc κ ℓ Ψ x
      = ((2 * π) ^ 3)⁻¹ * (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    rw [show lowMult fc κ ℓ Ψ x = ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³,
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re from rfl,
      Complex.re_ofReal_mul]
  have hpt : ∀ p : ℝ³, ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖
      = |fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
    intro p
    rw [norm_mul, norm_mul]
    have h2 : ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 := by
      rw [show Complex.I * (inner ℝ p x : ℂ) = ((inner ℝ p x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [h2, one_mul]
    rw [show ‖((fc.f (‖p‖ / κ) : ℝ) : ℂ)‖ = |fc.f (‖p‖ / κ)| from RCLike.norm_ofReal _]
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Complex.abs_re_le_norm _) ?_
  refine le_trans (norm_integral_le_integral_norm _) ?_
  exact integral_mono (hmaj.congr (Eventually.of_forall fun p => (hpt p).symm)) hmaj
    (fun p => le_of_eq (hpt p))

/-- The exponential kernel `(p,y) ↦ exp(c·⟪p,y⟫)` is measurable. -/
lemma measurable_exp_inner (c : ℂ) :
    Measurable (fun q : ℝ³ × ℝ³ => Complex.exp (c * (inner ℝ q.1 q.2 : ℂ))) :=
  (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_inner))).measurable

/-- The swapped exponential kernel `(x,p) ↦ exp(c·⟪p,x⟫)` is measurable. -/
lemma measurable_exp_inner_swap (c : ℂ) :
    Measurable (fun q : ℝ³ × ℝ³ => Complex.exp (c * (inner ℝ q.2 q.1 : ℂ))) := by
  have h : (fun q : ℝ³ × ℝ³ => Complex.exp (c * (inner ℝ q.2 q.1 : ℂ)))
      = fun q : ℝ³ × ℝ³ => Complex.exp (c * (inner ℝ q.1 q.2 : ℂ)) := by
    funext q
    rw [real_inner_comm]
  rw [h]
  exact measurable_exp_inner c

/-- The cut-off multiplier formula with a general measurable profile is a.e. strongly
measurable (it is a continuous function of the `p`-integral of a jointly measurable
integrand). -/
lemma aestronglyMeasurable_lowMult {fc : LowCut} {κ ℓ : ℝ} {Ψ : ℝ³ → ℝ}
    (hΨm : Measurable Ψ) :
    AEStronglyMeasurable (fun x : ℝ³ => lowMult fc κ ℓ Ψ x) volume := by
  have hΨc : Measurable (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (hΨm.indicator (acube_measurable ℓ))
  -- `kinFT` of a measurable profile is strongly measurable
  have hkin : StronglyMeasurable (kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ))) := by
    refine StronglyMeasurable.integral_prod_right ?_
    rw [show Function.uncurry (fun p y : ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          (((acube ℓ).indicator Ψ y : ℝ) : ℂ))
        = fun q : ℝ³ × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))) *
          (((acube ℓ).indicator Ψ q.2 : ℝ) : ℂ) from rfl]
    refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
    · have hfun : (fun q : ℝ³ × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))))
          = fun q : ℝ³ × ℝ³ => Complex.exp ((-Complex.I) * (inner ℝ q.1 q.2 : ℂ)) := by
        funext q
        rw [neg_mul]
      rw [hfun]
      exact measurable_exp_inner (-Complex.I)
    · exact hΨc.comp measurable_snd
  -- the joint integrand of `lowMult`
  have hjoint : StronglyMeasurable (Function.uncurry (fun x p : ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p)) := by
    refine Measurable.stronglyMeasurable ?_
    rw [show Function.uncurry (fun x p : ℝ³ =>
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p)
        = fun q : ℝ³ × ℝ³ => (Complex.exp (Complex.I * (inner ℝ q.2 q.1 : ℂ)) *
            ((fc.f (‖q.2‖ / κ) : ℝ) : ℂ)) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) q.2 from rfl]
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · exact measurable_exp_inner_swap Complex.I
      · refine Complex.continuous_ofReal.measurable.comp ?_
        exact ((fc.smooth.continuous.comp
          ((continuous_norm.comp continuous_snd).div_const κ)).measurable)
    · exact hkin.measurable.comp measurable_snd
  have hInt : StronglyMeasurable (fun x : ℝ³ => ∫ p : ℝ³,
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    StronglyMeasurable.integral_prod_right hjoint
  have heq : (fun x : ℝ³ => lowMult fc κ ℓ Ψ x)
      = fun x : ℝ³ => ((2 * π) ^ 3)⁻¹ * (∫ p : ℝ³,
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    funext x
    rw [show lowMult fc κ ℓ Ψ x = ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³,
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re from rfl,
      Complex.re_ofReal_mul]
  rw [heq]
  exact Continuous.comp_aestronglyMeasurable
    (g := fun z : ℂ => ((2 * π) ^ 3)⁻¹ * z.re) (by fun_prop) hInt.aestronglyMeasurable

/-! ## The one-body weighted Plancherel bound -/

/-- The `L¹`-bound for the cut-off multiplier appearing in `oneBody_box_le`. -/
def oneBodyB (fc : LowCut) (κ ℓ : ℝ) (Ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, |fc.f (‖p‖ / κ)| *
    ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖

lemma abs_lowMult_le' {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) {Ψ : ℝ³ → ℝ}
    (hΨc : Integrable (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ))) (x : ℝ³) :
    |lowMult fc κ ℓ Ψ x| ≤ oneBodyB fc κ ℓ Ψ :=
  abs_lowMult_le hκ hΨc x

/-- **The one-body weighted Plancherel bound (FS `eq:QLs_giveNplusH`, one-body level)**:
for `κ > 0` and a measurable profile bounded on the box,

`∫_{Λ}(Ψ − f_L(√−Δ)θΨ)² ≤ (2π)⁻³ ∫_p (1 − f(‖p‖/κ))²‖kinFT(θΨ)(p)‖²`.

Proof: the weak/duality argument.  With `u = Ψ − f_L(√−Δ)θΨ` and `φ = 1_Λ·u`, the
pairing identities `parseval_L1L2` and `lowMult_pairing` give
`∫_Λ u² = (2π)⁻³∫_p Re(conj(kinFT φ)(1−f_L)kinFT(θΨ))`, and Cauchy–Schwarz together with
`plancherel_L1L2` (applied to `φ`) bounds the right side by `(2π)^{-3/2}√(∫_Λu²)·√Q`. -/
theorem oneBody_box_le {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {Ψ : ℝ³ → ℝ} (hΨm : Measurable Ψ) {C : ℝ} (hΨb : ∀ x ∈ acube ℓ, |Ψ x| ≤ C) :
    ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2
      ≤ ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
  classical
  have hbox : MeasurableSet (acube ℓ) := acube_measurable ℓ
  have hboxfin : (volume (acube ℓ)) < ⊤ := acube_lt_top ℓ hℓ.le
  have hcs : HasCompactSupport (fun p : ℝ³ => fc.f (‖p‖ / κ)) :=
    lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ
  have hΨL1 : MeasureTheory.IntegrableOn Ψ (acube ℓ) := by
    refine MeasureTheory.IntegrableOn.of_bound hboxfin
      (hΨm.aestronglyMeasurable.restrict) C ?_
    exact ae_restrict_of_forall_mem hbox (fun x hx => hΨb x hx)
  have hΨcInt : Integrable (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) :=
    (((hΨL1.integrable_indicator hbox))).ofReal
  -- the box is nonempty
  have h0box : (0 : ℝ³) ∈ acube ℓ :=
    mem_acube_of_norm_le hℓ.le (by rw [norm_zero]; linarith [hℓ])
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (Ψ 0)) (hΨb 0 h0box)
  have hBnn : 0 ≤ oneBodyB fc κ ℓ Ψ := by
    rw [oneBodyB]
    exact mul_nonneg (by positivity)
      (integral_nonneg fun p => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hTbd : ∀ x : ℝ³, |lowMult fc κ ℓ Ψ x| ≤ oneBodyB fc κ ℓ Ψ :=
    fun x => abs_lowMult_le' hκ hΨcInt x
  set B : ℝ := oneBodyB fc κ ℓ Ψ with hBdef
  set D : ℝ := C + B with hDdef
  have hBnn' : 0 ≤ B := hBdef ▸ hBnn
  have hDnn : 0 ≤ D := by rw [hDdef]; linarith
  -- the test function `φ = 1_Λ(Ψ - f_L θΨ)`
  set φ : ℝ³ → ℝ := (acube ℓ).indicator (fun x : ℝ³ => Ψ x - lowMult fc κ ℓ Ψ x) with hφdef
  have hφae : AEStronglyMeasurable φ volume :=
    ((hΨm.aestronglyMeasurable.sub (aestronglyMeasurable_lowMult hΨm))).indicator hbox
  have hφsupp : ∀ x : ℝ³, x ∉ acube ℓ → φ x = 0 := by
    intro x hx; rw [hφdef, Set.indicator_of_notMem hx]
  have hφb : ∀ x ∈ acube ℓ, |φ x| ≤ D := by
    intro x hx
    rw [hφdef, Set.indicator_of_mem hx]
    have h1 : |Ψ x - lowMult fc κ ℓ Ψ x| ≤ |Ψ x| + |lowMult fc κ ℓ Ψ x| := abs_sub _ _
    have h2 : |Ψ x| ≤ C := hΨb x hx
    have h3 : |lowMult fc κ ℓ Ψ x| ≤ B := hBdef ▸ hTbd x
    have h4 : C + B = D := hDdef.symm
    linarith
  have hφb' : ∀ x : ℝ³, |φ x| ≤ D := by
    intro x
    by_cases hx : x ∈ acube ℓ
    · exact hφb x hx
    · rw [hφsupp x hx, abs_zero]; exact hDnn
  have hmajint : Integrable (fun x : ℝ³ => D * (acube ℓ).indicator (fun _ => (1 : ℝ)) x) := by
    have h1 : Integrable ((acube ℓ).indicator (fun _ : ℝ³ => D)) :=
      (MeasureTheory.integrableOn_const (μ := volume) (s := acube ℓ) (C := D)
        (ne_of_lt hboxfin)).integrable_indicator hbox
    have hcongr : (fun x : ℝ³ => D * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
        = (acube ℓ).indicator (fun _ : ℝ³ => D) := by
      funext x
      by_cases hx : x ∈ acube ℓ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rwa [hcongr]
  have hφint : Integrable φ := by
    refine Integrable.mono' hmajint hφae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ acube ℓ
    · rw [Set.indicator_of_mem hx]
      simpa using hφb x hx
    · rw [hφsupp x hx, abs_zero, Set.indicator_of_notMem hx, mul_zero]
  have hφcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (acube_compact hℓ) fun x hx => hφsupp x hx
  -- integrability of the standard majorants
  have hmajind (c : ℝ) :
      Integrable (fun x : ℝ³ => c * (acube ℓ).indicator (fun _ => (1 : ℝ)) x) := by
    have h1 : Integrable ((acube ℓ).indicator (fun _ : ℝ³ => c)) :=
      (MeasureTheory.integrableOn_const (μ := volume) (s := acube ℓ) (C := c)
        (ne_of_lt hboxfin)).integrable_indicator hbox
    have hcongr : (fun x : ℝ³ => c * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
        = (acube ℓ).indicator (fun _ : ℝ³ => c) := by
      funext x
      by_cases hx : x ∈ acube ℓ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rwa [hcongr]
  -- `L¹`/`L²` facts
  have hsuppφ : Function.support φ ⊆ acube ℓ := fun x hx => by
    by_contra hx'
    exact hx (hφsupp x hx')
  have hφmem2 : MemLp φ 2 volume := by
    rw [memLp_two_iff_integrable_sq hφae]
    refine Integrable.mono'
      (g := fun x : ℝ³ => D ^ 2 * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
      (hmajind (D ^ 2)) (hφae.pow 2) (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ acube ℓ
    · simp only [Set.indicator_of_mem hx, mul_one]
      rw [abs_of_nonneg (sq_nonneg (φ x))]
      have h1 := pow_le_pow_left₀ (abs_nonneg (φ x)) (hφb' x) 2
      rwa [sq_abs] at h1
    · simp [hφsupp x hx, Set.indicator_of_notMem hx]
  have hφmem1 : MemLp φ 1 volume := memLp_one_iff_integrable.mpr hφint
  have hindmem1 : MemLp (fun z : ℝ³ => (acube ℓ).indicator Ψ z) 1 volume :=
    memLp_one_iff_integrable.mpr (hΨL1.integrable_indicator hbox)
  have hindae : AEStronglyMeasurable (fun z : ℝ³ => (acube ℓ).indicator Ψ z) volume :=
    hΨm.aestronglyMeasurable.indicator hbox
  have hindmem2 : MemLp (fun z : ℝ³ => (acube ℓ).indicator Ψ z) 2 volume := by
    rw [memLp_two_iff_integrable_sq hindae]
    refine Integrable.mono'
      (g := fun x : ℝ³ => (max C 0) ^ 2 * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
      (hmajind ((max C 0) ^ 2)) (hindae.pow 2) (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ acube ℓ
    · simp only [Set.indicator_of_mem hx, mul_one]
      rw [abs_of_nonneg (sq_nonneg (Ψ x))]
      have h1 : |Ψ x| ≤ max C 0 := le_trans (hΨb x hx) (le_max_left C 0)
      have h2 := pow_le_pow_left₀ (abs_nonneg (Ψ x)) h1 2
      rwa [sq_abs] at h2
    · simp [Set.indicator_of_notMem hx]
  -- the two pairing identities
  have hI1 : ∫ x, φ x * Ψ x
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (starRingEnd ℂ
            (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    have h1 := parseval_L1L2 (u := φ) (v := fun z : ℝ³ => (acube ℓ).indicator Ψ z)
      hφmem1 hφmem2 hindmem1 hindmem2
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ acube ℓ
    · rw [Set.indicator_of_mem hx]
    · simp [hφsupp x hx, Set.indicator_of_notMem hx]
  have hI2 : ∫ x, φ x * lowMult fc κ ℓ Ψ x
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (starRingEnd ℂ
            (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re :=
    lowMult_pairing hℓ hφint hφcs hΨL1 hcs
  -- integrability of the two products
  have hintφΨ : Integrable (fun x : ℝ³ => φ x * Ψ x) := by
    refine Integrable.mono'
      (g := fun x : ℝ³ => D * C * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
      (hmajind (D * C)) (hφae.mul hΨm.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ acube ℓ
    · simp only [Set.indicator_of_mem hx, mul_one]
      rw [abs_mul]
      have h1 : |φ x| ≤ D := hφb x hx
      have h2 : |Ψ x| ≤ C := hΨb x hx
      nlinarith [abs_nonneg (φ x), abs_nonneg (Ψ x)]
    · simp [hφsupp x hx, Set.indicator_of_notMem hx]
  have hintφT : Integrable (fun x : ℝ³ => φ x * lowMult fc κ ℓ Ψ x) := by
    refine Integrable.mono'
      (g := fun x : ℝ³ => D * B * (acube ℓ).indicator (fun _ => (1 : ℝ)) x)
      (hmajind (D * B)) (hφae.mul (aestronglyMeasurable_lowMult hΨm))
      (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ acube ℓ
    · simp only [Set.indicator_of_mem hx, mul_one]
      rw [abs_mul]
      have h1 : |φ x| ≤ D := hφb x hx
      have h2 : |lowMult fc κ ℓ Ψ x| ≤ B := hBdef ▸ hTbd x
      nlinarith [abs_nonneg (φ x), abs_nonneg (lowMult fc κ ℓ Ψ x)]
    · simp [hφsupp x hx, Set.indicator_of_notMem hx]
  -- the momentum-side integrability
  have hMemφc : MemLp (fun z : ℝ³ => (φ z : ℂ)) 2 volume := hφmem2.ofReal
  have hMemΨc : MemLp (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) 2 volume :=
    hindmem2.ofReal
  have hIntφc : Integrable (fun z : ℝ³ => (φ z : ℂ)) :=
    (memLp_one_iff_integrable.mp hφmem1).ofReal
  have hMemkφ : MemLp (kinFT (fun z : ℝ³ => (φ z : ℂ))) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hIntφc hMemφc
  have hMemkΨ : MemLp (kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ))) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hΨcInt hMemΨc
  have hAint' : Integrable (fun p : ℝ³ => starRingEnd ℂ
      (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    (hMemkφ.star).integrable_mul hMemkΨ
  have hAint : Integrable (fun p : ℝ³ => (starRingEnd ℂ
      (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re) := hAint'.re
  have hBint : Integrable (fun p : ℝ³ => (starRingEnd ℂ
      (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re) := by
    have h1 : Integrable (fun p : ℝ³ => starRingEnd ℂ
        (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p *
            ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) := by
      refine Integrable.mul_bdd (c := 1) hAint' ?_ ?_
      · exact ((Complex.continuous_ofReal.comp
          (fc.smooth.continuous.comp (continuous_norm.div_const κ))).aestronglyMeasurable)
      · refine Eventually.of_forall fun p => ?_
        beta_reduce
        simpa using lowcut_abs_le_one fc (‖p‖ / κ)
    refine h1.re.congr (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [show starRingEnd ℂ (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p
        = starRingEnd ℂ (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p *
              ((fc.f (‖p‖ / κ) : ℝ) : ℂ) from by ring]
    rfl
  -- the test-function form of the left side
  have hstep : ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2
      = ∫ x, φ x * (Ψ x - lowMult fc κ ℓ Ψ x) := by
    rw [← integral_indicator hbox]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ acube ℓ
    · rw [Set.indicator_of_mem hx, hφdef, Set.indicator_of_mem hx]
      ring
    · simp [Set.indicator_of_notMem hx, hφdef]
  -- the combined identity
  have hcombine : ∫ x, φ x * (Ψ x - lowMult fc κ ℓ Ψ x)
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (starRingEnd ℂ
            (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    have hsplit : (∫ x, φ x * (Ψ x - lowMult fc κ ℓ Ψ x))
        = (∫ x, φ x * Ψ x) - ∫ x, φ x * lowMult fc κ ℓ Ψ x := by
      have h1 : (∫ x, φ x * (Ψ x - lowMult fc κ ℓ Ψ x))
          = ∫ x, (φ x * Ψ x - φ x * lowMult fc κ ℓ Ψ x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        beta_reduce
        ring
      rw [h1, integral_sub hintφΨ hintφT]
    rw [hsplit, hI1, hI2, ← mul_sub]
    congr 1
    rw [← integral_sub hAint hBint]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [← Complex.sub_re]
    congr 1
    ring
  -- integrability of the combined integrand
  have hCint : Integrable (fun p : ℝ³ => (starRingEnd ℂ
      (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) * (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re) := by
    have h1 : Integrable (fun p : ℝ³ => starRingEnd ℂ
        (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p *
            (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ))) := by
      refine Integrable.mul_bdd (c := 2) hAint' ?_ ?_
      · exact ((continuous_const.sub (Complex.continuous_ofReal.comp
          (fc.smooth.continuous.comp (continuous_norm.div_const κ)))).aestronglyMeasurable)
      · refine Eventually.of_forall fun p => ?_
        beta_reduce
        have h2 := lowcut_abs_le_one fc (‖p‖ / κ)
        have h3 := lowcut_nonneg fc (‖p‖ / κ)
        rw [show (1 : ℂ) - ((fc.f (‖p‖ / κ) : ℝ) : ℂ) = (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) by
          push_cast; ring]
        rw [show ‖(((1 - fc.f (‖p‖ / κ)) : ℝ) : ℂ)‖ = |1 - fc.f (‖p‖ / κ)| from
          RCLike.norm_ofReal _]
        rw [abs_le]
        have h4 := (abs_le.mp h2)
        constructor <;> linarith [h4.1, h4.2]
    have h2 : (fun p : ℝ³ => (starRingEnd ℂ
        (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) * (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re)
        = (fun p : ℝ³ => (starRingEnd ℂ
              (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
                kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p *
                  (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ))).re) := by
      funext p
      congr 1
      ring
    rw [h2]
    exact h1.re
  -- the norm bound
  have hnorm : ∀ p : ℝ³, (starRingEnd ℂ (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
      (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re
      ≤ ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ * |1 - fc.f (‖p‖ / κ)| *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
    intro p
    refine le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) ?_)
    rw [starRingEnd_apply, norm_mul, norm_mul, norm_star]
    rw [show ((1 : ℂ) - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) = (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) by
      push_cast; ring]
    rw [show ‖(((1 - fc.f (‖p‖ / κ)) : ℝ) : ℂ)‖ = |1 - fc.f (‖p‖ / κ)| from RCLike.norm_ofReal _]
  have hbase : Integrable (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ *
      ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) := by
    refine hAint'.norm.congr (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [starRingEnd_apply, norm_mul, norm_star]
  have hnormInt : Integrable (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ *
      |1 - fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) := by
    have h1 : Integrable (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ *
          |1 - fc.f (‖p‖ / κ)|) := by
      refine Integrable.mul_bdd (c := 2) hbase ?_ ?_
      · exact ((continuous_const.sub (fc.smooth.continuous.comp
          (continuous_norm.div_const κ))).abs).aestronglyMeasurable
      · refine Eventually.of_forall fun p => ?_
        beta_reduce
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        have h2 := lowcut_abs_le_one fc (‖p‖ / κ)
        have h4 := (abs_le.mp h2)
        have h3 := lowcut_nonneg fc (‖p‖ / κ)
        constructor <;> linarith [h4.1, h4.2]
    refine h1.congr (Eventually.of_forall fun p => ?_)
    beta_reduce
    ring
  have hCbound : ∫ p : ℝ³, (starRingEnd ℂ (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
      (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re
      ≤ ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ * |1 - fc.f (‖p‖ / κ)| *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ :=
    integral_mono hCint hnormInt hnorm
  -- Cauchy–Schwarz
  have hCS : ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ *
        (|1 - fc.f (‖p‖ / κ)| *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖)
      ≤ (∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ p : ℝ³, (|1 - fc.f (‖p‖ / κ)| *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) ^ 2) ^ (1 / 2 : ℝ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
      Real.HolderConjugate.two_two
      (f := fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖)
      (g := fun p : ℝ³ => |1 - fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖)
      (Eventually.of_forall fun p => norm_nonneg _)
      (Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (by simpa using hMemkφ.norm) ?_
    · simpa using h
    · refine MemLp.of_le (g := fun p : ℝ³ =>
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) ?_ ?_ ?_
      · simpa using hMemkΨ.norm
      · have hc : AEStronglyMeasurable (fun p : ℝ³ => |1 - fc.f (‖p‖ / κ)|) volume :=
          ((continuous_const.sub (fc.smooth.continuous.comp
            (continuous_norm.div_const κ))).abs).aestronglyMeasurable
        exact hc.mul (hMemkΨ.aestronglyMeasurable.norm)
      · refine Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (norm_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have h2 := lowcut_abs_le_one fc (‖p‖ / κ)
        have h4 : |1 - fc.f (‖p‖ / κ)| ≤ 1 := by
          have h5 := (abs_le.mp h2)
          have h3 := lowcut_nonneg fc (‖p‖ / κ)
          rw [abs_le]; constructor <;> linarith [h5.1, h5.2]
        exact mul_le_of_le_one_left (norm_nonneg _) h4
  -- the two identified factors
  have hAeq : ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ ^ 2
      = (2 * π) ^ 3 * ∫ x : ℝ³, φ x ^ 2 := by
    have h1 : MemLp (fun z : ℝ³ => (φ z : ℂ)) 1 volume :=
      memLp_one_iff_integrable.mpr hIntφc
    have h := plancherel_L1L2 h1 hMemφc
    have h2 : (∫ x : ℝ³, ‖((φ x : ℂ))‖ ^ 2) = ∫ x : ℝ³, φ x ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [show ‖((φ x : ℝ) : ℂ)‖ = |φ x| from RCLike.norm_ofReal _, sq_abs]
    have h5 := congrArg (fun t : ℝ => (2 * π) ^ 3 * t) h
    rw [h2] at h5
    have h3 : (2 * π) ^ 3 ≠ 0 := by positivity
    rwa [← mul_assoc, mul_inv_cancel₀ h3, one_mul] at h5
  have hBeq : ∫ p : ℝ³, (|1 - fc.f (‖p‖ / κ)| *
        ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) ^ 2
      = ∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [mul_pow, sq_abs]
  have hphi2 : ∫ x : ℝ³, φ x ^ 2 = ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2 := by
    rw [hstep]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ acube ℓ
    · rw [hφdef, Set.indicator_of_mem hx]; ring
    · rw [hφdef, Set.indicator_of_notMem hx]; ring
  -- the arithmetic
  have hAnn : 0 ≤ ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hQnn : 0 ≤ ∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
      ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2 :=
    integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLV : (∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (starRingEnd ℂ
            (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
          kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    rw [hstep]
    exact hcombine
  have hAeq2 : ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ ^ 2
      = (2 * π) ^ 3 * ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2 := by
    rw [hAeq, hphi2]
  have hchain : (∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
      ≤ ((2 * π) ^ 3)⁻¹ * (√((2 * π) ^ 3 *
            ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
          √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) := by
    nth_rewrite 1 [hLV]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∫ p : ℝ³, (starRingEnd ℂ (kinFT (fun z : ℝ³ => (φ z : ℂ)) p) *
          (1 - ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) *
            kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re
        ≤ ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ * |1 - fc.f (‖p‖ / κ)| *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := hCbound
      _ = ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ *
            (|1 - fc.f (‖p‖ / κ)| *
              ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          beta_reduce
          ring
      _ ≤ (∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (φ z : ℂ)) p‖ ^ 2) ^ (1 / 2 : ℝ) *
            (∫ p : ℝ³, (|1 - fc.f (‖p‖ / κ)| *
              ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖) ^ 2) ^ (1 / 2 : ℝ) := hCS
      _ = √((2 * π) ^ 3 * ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
            √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
              ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2) := by
          rw [hAeq2, hBeq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hct : ((2 * π) ^ 3)⁻¹ * √((2 * π) ^ 3) = (√((2 * π) ^ 3))⁻¹ := by
    have hx : √((2 * π) ^ 3) * √((2 * π) ^ 3) = (2 * π) ^ 3 :=
      Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (2 * π) ^ 3)
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_assoc, hx, inv_mul_cancel₀ (by positivity : ((2 * π) ^ 3 : ℝ) ≠ 0)]
  have hfin : (∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
      ≤ (√((2 * π) ^ 3))⁻¹ * (√(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
          √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) := by
    refine le_trans hchain (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2 * π) ^ 3)]
    rw [show ((2 * π) ^ 3)⁻¹ * (√((2 * π) ^ 3) *
          √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
          √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2))
        = ((2 * π) ^ 3)⁻¹ * √((2 * π) ^ 3) *
          (√(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
            √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
              ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) from by
          ring, hct]
  by_cases hA0 : (∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) = 0
  · rw [hA0]; exact mul_nonneg (by positivity) hQnn
  · have hApos : 0 < ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2 :=
      lt_of_le_of_ne hAnn (Ne.symm hA0)
    have hsA : 0 < √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) :=
      Real.sqrt_pos.mpr hApos
    have h1 : √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
          √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
        ≤ ((√((2 * π) ^ 3))⁻¹ * √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) *
          √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) := by
      calc √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
            √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
          = ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2 := Real.mul_self_sqrt hAnn
        _ ≤ (√((2 * π) ^ 3))⁻¹ * (√(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) *
              √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
                ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) := hfin
        _ = ((√((2 * π) ^ 3))⁻¹ * √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
              ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) *
            √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2) := by ring
    have h2 : √(∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2)
        ≤ (√((2 * π) ^ 3))⁻¹ * √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2) :=
      le_of_mul_le_mul_right h1 hsA
    have hsq : ∫ x in acube ℓ, (Ψ x - lowMult fc κ ℓ Ψ x) ^ 2
        ≤ ((√((2 * π) ^ 3))⁻¹ * √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) ^ 2 := by
      rw [← Real.sq_sqrt hAnn]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    have hsq2 : ((√((2 * π) ^ 3))⁻¹ * √(∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2)) ^ 2
        = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 *
            ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (2 * π) ^ 3),
        Real.sq_sqrt hQnn]
    rwa [hsq2] at hsq

end Work.BoseFixB3.HighMass
