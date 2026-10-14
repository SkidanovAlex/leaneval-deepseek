import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.FaStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option autoImplicit false

/-- The angular integral of a pointwise bound that is constant in `θ`:
`∫⁻_θ ∈ Iθ, ofReal d ≤ ofReal d · volume Iθ`. -/
theorem lintegral_const_le_ofReal {d : ℝ} (_hd : 0 ≤ d) :
    (∫⁻ _θ in Work.Spaces.Iθ, ENNReal.ofReal d)
      = ENNReal.ofReal d * ENNReal.ofReal (π / 2) := by
  rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]

/-- **The `r`-step with an explicit profile.**  If `|K θ · N r θ| ≤ c r · M r` pointwise on
the open quadrant, `(M r)² ≤ C · Ψ r` on `r > 0`, `c` is nonnegative, `r ↦ r⁻¹c r` is
square-integrable and `Ψ` is integrable (and nonnegative), then

  `Fa N ≤ ofReal ((π/2) · √C · (∫Ψ)^{1/2} · (∫(r⁻¹c)²)^{1/2})`.

The factor `π/2` is the angular volume; it is kept explicit so that the caller can choose
its own (harmless) numerical over-estimate. -/
theorem Fa_le_of_profile {N : ℝ → ℝ → ℝ} {c M Ψ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hMnn : ∀ r, 0 ≤ M r) (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)))
    (hcmeas : AEMeasurable (fun r => r⁻¹ * c r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hcint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * c r) ^ 2) (Set.Ioi (0 : ℝ)))
    (hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ C * Ψ r)
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ c r * M r) :
    Work.FTS.Nonlinear.Pieces.Fa N
      ≤ ENNReal.ofReal (Real.pi / 2 * (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2))) := by
  -- ### the θ-step: the pointwise bound is constant in θ
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hcm : 0 ≤ c r * M r := mul_nonneg (hc r hr0) (hMnn r)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |Work.Spaces.K θ * N r θ| ≤ ENNReal.ofReal (c r * M r) :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ENNReal.ofReal_le_ofReal (hpt r hr0 θ hθ))
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c r * M r) :=
          MeasureTheory.lintegral_mono_ae hae
      _ = ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2) :=
          lintegral_const_le_ofReal hcm
  -- ### the extension of `r ↦ r⁻¹c r` to all of `ℝ`, used by `outer_gen`
  set θw : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun r => r⁻¹ * c r) with hθwdef
  have hθwmem : ∀ r ∈ Set.Ioi (0 : ℝ), θw r = r⁻¹ * c r := by
    intro r hr
    rw [hθwdef, Set.indicator_of_mem hr]
  have hwnn : ∀ r, 0 ≤ θw r := by
    intro r
    by_cases hr : r ∈ Set.Ioi (0 : ℝ)
    · rw [hθwmem r hr]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hr)) (hc r hr)
    · rw [hθwdef, Set.indicator_of_notMem hr]
  have hwmeas : AEMeasurable θw (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcmeas.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact (hθwmem r hr).symm)
  have hwint : MeasureTheory.IntegrableOn (fun r => (θw r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hcint
      (fun r hr => by rw [hθwmem r hr]) measurableSet_Ioi
  have hMle' : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (M r) ^ 2 ≤ C * Ψ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact hMle r hr
  have houter := outer_gen hC hwnn hMnn hΨnn hwmeas hΨmeas hwint hΨint hMle'
  rw [Work.FTS.Nonlinear.Pieces.Fa]
  -- ### the chain
  have h1 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_right (hinner r hr) _
  have h2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
          * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hcr : 0 ≤ c r := hc r hr0
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    rw [ENNReal.ofReal_mul hcr]
    calc ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r) * ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2))
        = (ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c r))
            * (ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2)) := by ring
      _ = ENNReal.ofReal (r⁻¹ * c r)
            * (ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2)) := by
            rw [ENNReal.ofReal_mul hinv]
      _ = ENNReal.ofReal (π / 2)
            * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := by ring
  have h3 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
        * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)))
      = ENNReal.ofReal (π / 2) * ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h4 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r))
      ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2)) := by
    have hcong : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
        = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      rw [hθwmem r hr]
    have hsq : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      exact congrArg (fun x => x ^ 2) (hθwmem r hr)
    rw [← hcong, ← hsq]
    exact houter
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)) := h1
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
          * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := h2
    _ = ENNReal.ofReal (π / 2) * ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) := h3
    _ ≤ ENNReal.ofReal (π / 2) * ENNReal.ofReal (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2)) :=
        mul_le_mul_right h4 _
    _ = ENNReal.ofReal (Real.pi / 2 * (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.Linv_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.LinvFlat.Linv_abs_le`

`Linv h` is the `σ`-normalised zero-moment Dirichlet inverse of `L₀`: with `μ = sin²θ cos³θ`,

  `Linv h θ = -μ(θ)⁻¹ ∫_0^θ μ(θ') h(θ') / sin 2θ' dθ'`.

On `(0, π/2)` the quotient inside the integral is `sin θ' cos²θ' / 2 · h θ'` (both sides vanish
where `sin 2θ' = 0`), so

  `|Linv h θ| = |N(θ)| / (2 sin²θ cos³θ)`,  `N(θ) = ∫_0^θ h · sinCos2`.

Two estimates bound `N`: directly, `|N(θ)| ≤ K ∫_0^θ sinCos2 = K (1 - cos³θ) / 3`; and, using the
zero-moment hypothesis `∫_0^{π/2} h · sinCos2 = 0` together with the additivity of the interval
integral, `|N(θ)| ≤ K ∫_θ^{π/2} sinCos2 = K cos³θ / 3`.  Splitting at `θ = π/4` and using
`cos θ ≥ 1/2` there (`cos θ ≥ 1 - 2θ/π`) resp. `sin θ ≥ 1/2` for `θ ≥ π/4` (`sin θ ≥ 2θ/π`) gives
`|Linv h θ| ≤ 4K` for every `θ ∈ (0, π/2)`.

(The declaration `Submission.Work.FTS.PhiStar.LinvI_solves` is not imported: it is currently
mid-edit by its owner and does not build.  Nothing of it is used here.)
-/

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 800000

/-! ## Elementary facts -/

/-- `sinCos2` is nonnegative on the open quadrant. -/
private lemma sinCos2_nonneg {t : ℝ} (ht : t ∈ Set.Ioo 0 (π/2)) :
    0 ≤ Work.Elliptic.sinCos2 t := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos]))
    (sq_nonneg _)

/-- The integrand of `Linv` is `sin θ cos²θ / 2 · h θ` (identically: both sides vanish at the
endpoints, where `sin 2θ = 0`). -/
private lemma integrand_eq (h : ℝ → ℝ) (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = (1 / 2) * (h t * Work.Elliptic.sinCos2 t) := by
  rw [Work.Elliptic.sinCos2, Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · by_cases hc : Real.cos t = 0
    · simp [hc]
    · field_simp

/-- Unfolding of `Linv` in terms of the (finite) integral `∫_0^θ h · sinCos2`. -/
private lemma Linv_eq (h : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv h θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
          ((1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t)) := by
  have hint : (∫ θ' in (0 : ℝ)..θ,
        Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ')
      = (1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t := by
    rw [intervalIntegral.integral_congr (fun t _ => integrand_eq h t),
        intervalIntegral.integral_const_mul]
  simp only [Work.FTS.PhiStar.Linv]
  rw [hint]

/-! ## Integrability and the pointwise vs. weight comparison -/

/-- The moment integrand is interval integrable on every subinterval of `[0, π/2]`. -/
private lemma intervalIntegrable_moment {h : ℝ → ℝ}
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π/2) (hab : a ≤ b) :
    IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine hint.mono_set ?_
  intro t ht
  exact ⟨le_trans ha ht.1.le, le_trans ht.2 hb⟩

/-- The key comparison: on any subinterval of `[0, π/2]`, `|∫ h · sinCos2| ≤ K ∫ sinCos2`. -/
private lemma interval_bound {h : ℝ → ℝ} {K : ℝ}
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |h θ| ≤ K)
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π/2) (hab : a ≤ b) :
    |∫ t in a..b, h t * Work.Elliptic.sinCos2 t| ≤ K * ∫ t in a..b, Work.Elliptic.sinCos2 t := by
  have hf : IntervalIntegrable (fun t => |h t * Work.Elliptic.sinCos2 t|) volume a b :=
    (intervalIntegrable_moment hint ha hb hab).abs
  have hg : IntervalIntegrable (fun t => K * Work.Elliptic.sinCos2 t) volume a b :=
    (continuous_const.mul (by unfold Work.Elliptic.sinCos2; fun_prop)).intervalIntegrable a b
  have hpoint : ∀ x ∈ Set.Ioo a b,
      |h x * Work.Elliptic.sinCos2 x| ≤ K * Work.Elliptic.sinCos2 x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (π/2) := ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hnn : 0 ≤ Work.Elliptic.sinCos2 x := sinCos2_nonneg hx'
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hbd x hx') hnn
  calc |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ ∫ t in a..b, |h t * Work.Elliptic.sinCos2 t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * Work.Elliptic.sinCos2 t :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab hf hg hpoint
    _ = K * ∫ t in a..b, Work.Elliptic.sinCos2 t := intervalIntegral.integral_const_mul K _

/-! ## The weight integral -/

private lemma hasDerivAt_prim (y : ℝ) :
    HasDerivAt (fun x => -(Real.cos x ^ 3) / 3) (Real.sin y * Real.cos y ^ 2) y := by
  have h1 := (Real.hasDerivAt_cos y).pow 3
  have h2 := h1.const_mul (-(1 / 3) : ℝ)
  convert h2 using 1
  · funext x; simp only [Pi.pow_apply]; ring
  · ring_nf

/-- `∫_a^b sin t cos²t dt = (cos³a - cos³b)/3`. -/
private lemma integral_sinCos2 (a b : ℝ) :
    ∫ t in a..b, Work.Elliptic.sinCos2 t = (Real.cos a ^ 3 - Real.cos b ^ 3) / 3 := by
  have hcont : IntervalIntegrable (fun t => Real.sin t * Real.cos t ^ 2) volume a b :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(Real.cos x ^ 3) / 3)
    (f' := fun x => Real.sin x * Real.cos x ^ 2)
    (fun x _ => hasDerivAt_prim x) hcont
  change ∫ t in a..b, Real.sin t * Real.cos t ^ 2 = _
  rw [h]
  ring

/-- The zero-moment hypothesis, transported to the interval `0..π/2`. -/
private lemma moment_zero {h : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∫ t in (0 : ℝ)..(π/2), h t * Work.Elliptic.sinCos2 t = 0 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π/2)] at hmom
  exact hmom

/-! ## The bound -/


end Work.FTS.PhiStar.LinvFlat
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- The growing indicial exponent `p = 2m/α`. -/
def radP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The (positive) decaying indicial exponent `q = (2m+5)/α`, i.e. `s⁻ = -q`. -/
def radQ (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The normalising constant `K = 1/(α(4m+5))` of the Green function. -/
def radK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The "inner" part of the Green function, in rescaled form:
`Φ z = ∫₀¹ c(zu)·u^{q-1} du`. -/
def radPhi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1)

/-- The "outer" part of the Green function, in rescaled form:
`Ψ z = ∫_{u>1} c(zu)·u^{-p-1} du`. -/
def radPsi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)


/-! ### Elementary side facts -/

theorem radP_pos {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) : 0 < radP α m := by
  have h : (0 : ℝ) < 2 * (m : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  simp only [radP]; exact div_pos h hα

theorem radQ_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < radQ α m := by
  have h : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
  simp only [radQ]; exact div_pos h hα

/-- `p = 2m/α ≥ 10` for `α ≤ 1/5`, `m ≥ 1`. -/
theorem ten_le_radP {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    10 ≤ radP α m := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [radP]
  rw [le_div_iff₀ hα]
  nlinarith [hα5, hmr]

/-- `q = (2m+5)/α ≥ 35` for `α ≤ 1/5`, `m ≥ 1`. -/
theorem thirtyfive_le_radQ {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    35 ≤ radQ α m := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [radQ]
  rw [le_div_iff₀ hα]
  nlinarith [hα5, hmr]

/-- `(4m+5)/α = p + q`, the total indicial gap. -/
theorem radP_add_radQ {α : ℝ} (hα : 0 < α) (m : ℕ) :
    radP α m + radQ α m = (4 * (m : ℝ) + 5) / α := by
  simp only [radP, radQ]; field_simp; ring


theorem radK_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < radK α m := by
  simp only [radK]; positivity


end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.phiAj_smooth2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## General order bookkeeping -/

/-- The derivative of a `C^∞` function is `C^∞`. -/
theorem contDiffAt_infty_deriv {f : ℝ → ℝ} {z : ℝ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (deriv f) z :=
  h.derivWithin (m := ∞) (by simp)

/-- A `C^∞` function has `C^∞` iterated derivatives. -/
theorem contDiffAt_infty_iteratedDeriv {f : ℝ → ℝ} {z : ℝ} (k : ℕ)
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact contDiffAt_infty_deriv ih

/-! ## The first iterate `𝒜φ = phiA α` -/

/-- **`𝒜φ` is `C^n` at every `z > 0`, for every order `n`** (in particular `C^∞`).  Proof: the
explicit rational form `Basic.phiA_eq` is a sum of two quotients whose denominators `(1+z)^4`,
`(1+z)^3` are nonvanishing for `z > 0`. -/
theorem contDiffAt_phiA_of (α : ℝ) (n : ℕ∞ω) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ n (Work.FTS.VocabO.phiA α) z := by
  have hz1 : z ≠ -1 := by linarith
  have hF : ContDiffAt ℝ n (fun z : ℝ =>
      4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4
        + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3) z := by
    have hden : (1 + z) ^ 4 ≠ 0 := by
      have : 1 + z ≠ 0 := by linarith
      positivity
    have hden3 : (1 + z) ^ 3 ≠ 0 := by
      have : 1 + z ≠ 0 := by linarith
      positivity
    refine (ContDiffAt.div ?_ (((contDiffAt_const (c := (1 : ℝ))).add contDiffAt_id).pow 4)
      hden).add (ContDiffAt.div ?_ (((contDiffAt_const (c := (1 : ℝ))).add
        contDiffAt_id).pow 3) hden3)
    · exact (((contDiffAt_const (c := (4 * α))).mul (contDiffAt_id.pow 2)).mul
        (contDiffAt_id.sub contDiffAt_const))
    · exact (((contDiffAt_const (c := (2 * (5 + α)))).mul contDiffAt_id).mul
        (contDiffAt_const.sub contDiffAt_id))
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  have hy1 : y ≠ -1 := by
    simp only [Set.mem_Ioi] at hy
    linarith
  exact Work.FTS.PhiStar.phiA_eq α y hy1

/-- `𝒜φ` is `C^∞` at every `z > 0`. -/
theorem contDiffAt_phiA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Work.FTS.VocabO.phiA α) z :=
  contDiffAt_phiA_of α ∞ hz

/-! ## The second iterate `𝒜²φ = phiAj 2 α` -/


/-! ## The requested statement -/


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Clauses =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS IsDynEqOn IsDynGSolWith IsDynEq
  galFun galFam Slab)
open Work.FTS.Nonlin (Xn RegQ)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.FTS.VocabO2 (StarPkgo2)
open Work.Coercivity (LGammaT HkIPStep H1IP wip)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed pth pzIter DthIter DzIter)

set_option autoImplicit false
set_option linter.unusedVariables false
/-! ## The level-six clauses

The design asks for the k = 6 versions of the interface clauses consumed by the S2 Gronwall
argument.  The level-four originals are `OpenPkg.N4Norm'` (product, `l12H`, `wprod`, `wtoh`)
and `VocabO.T2Clause`/`T3Clause` (transport).  We restate the ones the persistence proof
needs, in the **corrected `HQo`-based** form (interior `C^∞` + honesty, no `SmoothQuad`):
the honest strong solutions of the route have `z^{2/α}`-type behaviour at the axis and are not
`C^∞` through `z = 0`, so the `RegQ`-based level-four clauses are uninhabited by them. -/

/-- **`N6Norm` — the `ℋ⁶` norm-level interface** (the k = 6 restatement of the product and
`L₁₂` clauses of `OpenPkg.N4Norm'`).

* `prod` is the `ℋ⁶` product rule (the k = 6 version of `HProdQ`, tex 1086); the loss
  `α^{-1/2}` is the one of the paper's level-four estimate, with `Xi` absorbing the (larger)
  constants of level six;
* `l12H` is the `ℋ⁶`-continuity of the angular average `L₁₂` (the k = 6 version of `L12HQ`,
  tex 1119) — the operator averages in `θ` against a bounded kernel, so it is lossless at
  every order;
* `fkH` is the `ℋ⁶` control of the angular moment `FK` (the k = 6 version of the same-named
  clause of `N4Norm'`), needed by the `N`-piece of the right-hand side. -/
structure N6Norm (Xi Cpow α₂ : ℝ) : Prop where
  pos : 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂
  /-- the `ℋ⁶` product rule; the paper's level-four form has the `α^{-1/2}`-loss, which is why
  the exponent is left free here (smaller exponents are stronger claims). -/
  prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
    H6Mem α (fun z θ => f z θ * g z θ) ∧
    Xn6 α (fun z θ => f z θ * g z θ) ≤ Xi * α ^ (-Cpow) * Xn6 α f * Xn6 α g
  /-- `L₁₂` maps the `ℋ⁶`-class into itself.  (Proved for `Cpow = 0` in
  `Submission/Work/FTS/StrongPersist/N6_L12H.lean`.) -/
  l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 6 g → Work.Construction.L12 g 0 = 0 →
    H6Mem α (fun z θ => Work.Construction.L12 g z) ∧
    Xn6 α (fun z θ => Work.Construction.L12 g z) ≤ Xi * α ^ (-Cpow) * Xn6 α g
  /-- the angular moment `FK g` is an `ℋ⁶`-function controlled by `Xn6 α g`. -/
  fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 6 g → Work.Construction.L12 g 0 = 0 →
    H6Mem α (fun z _ => Work.Construction.FK g z) ∧
    Xn6 α (fun z _ => Work.Construction.FK g z) ≤ Xi * α ^ (-Cpow) * Xn6 α g

/-- The level-six restatement of the transport clause `VocabO.T2Clause`: the pairing of a
coefficient `f` times `D_z g` against `g`, with the angular liveness of the coefficient
measured by the flat norm `CoefTh`.  At level six the `g`-side carries order-seven honesty
(`HkMem α 7 g`), exactly as the level-four clause asks `HkMem α 5 g` for the `D_z`-slot. -/
def T2Clause6 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → H6Mem α f → CoefThMem 1 f →
    HQo α 6 g → Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Xn6 α f + CoefTh 1 f) * Xn6 α g ^ 2

/-- The level-six restatement of `VocabO.T3Clause`: the same transport clause with a
`𝒲^{6,∞}`-coefficient. -/
def T3Clause6 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f → CoefThMem 5 f →
    HQo α 6 g → Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 6 f + CoefTh 5 f) * Xn6 α g ^ 2

/-- The level-six restatement of `T1Q` (transport with `D_θ` and an `ℋ⁶`-coefficient). -/
def T1Clause6 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn6 α f * Xn6 α g ^ 2

/-- **`N6Trans` — the transport clauses at level six.**  This is the k = 6 restatement of
`OpenPkg.N4Extra'`'s `t1`/`t2`/`t3`, in the corrected `HQo`-based form. -/
structure N6Trans (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- `T1Q` at level six. -/
  t1 : T1Clause6 IP α₂ Ct
  /-- `T2S` at level six (flat angular coefficient). -/
  t2 : T2Clause6 IP α₂ Ct
  /-- `T3S` at level six (`𝒲^{6,∞}`-coefficient). -/
  t3 : T3Clause6 IP α₂ Ct

/-- **`H6Coer` — the level-six inner-product package** (the k = 6 restatement of the clauses
`IsHkIP`/`UnifIP`/`CoerData2` consumed by the a-priori estimate).

* `nonneg`, `add`, `smul` are the structural clauses of the paper's inductively built inner
  product (the concrete `IP6` is an integral functional, so they hold for it);
* `cs` is Cauchy–Schwarz against the honest `ℋ⁶`-norm;
* `lo`/`up` are the comparability of the diagonal with the `ℋ⁶` norm squared.

**There is no coercivity field.**  The design `FTS_HARD_DESIGN.md` (C) rules that `H6Coer.coer`
(`cc·|f|²_{ℋ⁶} ≤ IP (𝓛_Γ^T f) f`) is *not needed* and is likely **false** for `IP6 1 … 1` (the
unit-step balance of `CoercivityFix`); the level-six energy estimate only consumes the one-sided
bound `H6Lin` (`Defs.lean`), which is a different — and provable — statement.  The `pos` field
still carries a constant `cc` only for uniformity with the other level packages. -/
structure H6Coer (IP : ℝ → Fn → Fn → ℝ) (α₂ cc CC : ℝ) : Prop where
  pos : 0 < cc ∧ 0 < CC ∧ 0 < α₂
  /-- the diagonal is nonnegative. -/
  nonneg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 6 f → 0 ≤ IP α f f
  /-- additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, HQo α 6 f₁ → HQo α 6 f₂ → HQo α 6 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), HQo α 6 f → HQo α 6 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Cauchy–Schwarz against the honest `ℋ⁶`-norm. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
    |IP α f g| ≤ CC * Xn6 α f * Xn6 α g
  /-- the `ℋ⁶`-norm squared is dominated by the diagonal. -/
  lo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f → Sq6 α f ≤ IP α f f
  /-- the diagonal is dominated by the `ℋ⁶`-norm squared. -/
  up : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f → IP α f f ≤ CC * Sq6 α f

/-! ## The level-six pairing bound for the right-hand side -/

/-- **(C) the one-sided level-six bound replacing `H6Coer.coer`.**  `H6Lin IP α₂ CL` is the
statement that the level-six pairing of the linear part `linPart α f = -𝓛_Γ^T f` against `f` is
bounded above by `CL·|f|²_{ℋ⁶}`, on the class `H6Adm α f` with order-seven honesty.  It is *not*
a coercivity statement (no lower bound, no sign) — the design `FTS_HARD_DESIGN.md` (C) shows that
coercivity for `IP6 1 … 1` is likely *false* (the unit-step balance of `CoercivityFix`), while
this one-sided form is what the level-six energy estimate actually consumes.  Proof (about 1.5K
lines, not done here): the base-level integration by parts plus the commutators `[D_z, 𝓛]`,
`[D_θ, 𝓛]`, using the level-six transport clauses T1–T3₆ and `l12H`.

**The class is `H6Adm`, and this is essential** (design line 37).  With only `HQo α 6 f` the
clause is **false**: the nonlocal term `L₁₂` of `𝓛_Γ^T` is a functional of `f` whose zero mode
`L₁₂(f)(0)` is *not* controlled by `HQo α 6`, and the θ-independent family
`f_p(z,θ) = z^p e^{-z}(1+z)^{-6}` (`2 < p < 3`) satisfies `HQo α 6` and `HkMem α 7` while the
pairing `IP6 (linPart α f_p) f_p / |f_p|²_{ℋ⁶}` blows up as `p → 2⁺`
(`Submission/Work/FTS/StrongPersist/H6Lin_refute.lean`, sorry-free, with the structural identity
`IP6 1 … 1 α u (θ-independent v) = Σ_{j ≤ 5} C(5,j)·H1IP α (D_z^j u) (D_z^j v)`).
`H6Adm` excludes that family by `VanishTheta` and `l12 : L₁₂ f 0 = 0`. -/
def H6Lin (IP : ℝ → Fn → Fn → ℝ) (α₂ CL : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f → Work.Spaces.HkMem α 7 f →
    IP α (fun z θ => -(Work.Coercivity.LGammaT α f z θ)) f ≤ CL * Work.Spaces.HkSq α 6 f

/-- **The elliptic package at order `k`, for the *perturbation* part of the split.**  `EllPkgK α k
Ce f Φg` says that `Φg` solves the corrected elliptic law with source `f` and that the transported
residual's `ℛ`-, `U`- and `V`-components are `ℋᵏ`-functions bounded by `Ce·|f|_{ℋᵏ}`.  This is
`VocabO.EllPkgGo`'s `R`/`U`/`V`-part at order `k`, and it is the half of the elliptic data that
*is* satisfiable -- the star part (`StarPkgo α Cs Φs`) carries the `F_*`-terms, whose `Rop` is
`O(z)` so that `(Rop·w)² ~ z^{-2}` and no honest `ℋᵏ`-membership holds for them (design
`FTS_HARD_DESIGN.md` (C)). -/
structure EllPkgK (α : ℝ) (k : ℕ) (Ce : ℝ) (f Φg : Fn) : Prop where
  sol : IsBslSolPos α f Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg)) ∧
    HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ Ce * HkNorm α k f
  U : HQo α k (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ∧
    HkNorm α k (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ≤ Ce * HkNorm α k f
  V : HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α f Φg)) ∧
    HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ Ce * HkNorm α k f

/-- **(C) The split elliptic context at level six.**  This replaces the earlier single-structure
`Ell6Data`, which was **unsatisfiable**: it priced the transported residual by `Xn α (F_* + f)`,
and `F_* ∉ ℋ⁴`, so the bound collapsed (`Xn α (F_*+f) = 0` by the junk convention); moreover the
star part's `Rop` is `O(z)`, so even `HkMem α 4 (Rop α (PhiTil α (F_*+f) Φ))` fails.  The
decomposition is the one `Open2.PairData2` uses: the stream function splits as

`Φ = Φ_s + E f`,   `Φ_s` the star solution (`StarPkgo2`), `E` the *linear* elliptic solution
operator of the Class C chapter (`ExistsEllSolC`), `E f` the perturbation solution (`EllPkgK`).

`Φ_s` is a fixed profile (the star part does not move with the evolution); `E` is the linear
operator supplied by the elliptic layer. -/
structure Ell6Ctx (α Ce Cs : ℝ) (E : Fn → Fn) (Φs f Φ : Fn) : Prop where
  /-- the star half: the fixed stream function of `F_*`. -/
  hstar : StarPkgo2 α Cs Φs
  /-- the perturbation half: the linear elliptic solution at the modulation. -/
  hell : EllPkgK α 6 Ce f (E f)
  /-- the decomposition of the total stream function. -/
  hsum : Φ = fun z θ => Φs z θ + E f z θ
  /-- **The level-four elliptic package for the perturbation solution.**  This is the first
  conjunct of the elliptic layer's `ExistsEllSolC` (`Work.FTS.VocabO.EllPkgGo α Ce f (E f)`, the
  same `Ce` and the same `E`), and it is what turns the `ℋ⁶`-priced residual `EllPkgK α 6` — which
  is *unbounded* in `HkNorm α 6 f` on the class `{H6Adm α f ∧ HkNorm α 4 f ≤ M}` — into a pricing
  by the `ℋ⁴` data `M` that the level-six rows need.

  Concretely (lead's ruling of 17:10): `EllPkgGo` prices `Rop(Φ̃_f)`, `Uop(Φ̃_f)/sin 2θ`,
  `Vop(Φ̃_f)` by `Ce·HkNorm α 4 f ≤ Ce·M` at level **four**, and the open-quadrant pointwise
  (Agmon) bound `SupOpenH2`
  (`HQo α 2 h → |h z θ| ≤ C α^{-1/2} HkNorm α 2 h` on `Q0`, a *provable* lemma of this chapter, see
  `H6Pair6Aux/` and `SupOpenH2.lean`) upgrades it to the *pointwise* size
  `|Rop(Φ̃_f)| ≤ K α^{-1/2} Ce (1+M)` — which is the form the rows consume
  (`ResidPtOfGo`).  Deriving that pointwise bound from `EllPkgK α 6` alone is *impossible*, so the
  level-four package (not a raw pointwise field) is the right interface: it is supplied verbatim by
  the elliptic layer, and the bridge to the pointwise form is proved once, here. -/
  hgo : Work.FTS.VocabO.EllPkgGo α Ce f (E f)

/-- **The level-six star clause package.**  The star half of `Ell6Ctx` is
`Work.FTS.VocabO2.StarPkgo2 α Cs Φs`, which is the *level-four* package of the sibling area: its
five quantitative fields bound the five star fields by `WlInfMem α 4` / `WlInf α 4 ≤ Cs α`
(`WlInf` being the paper's `𝒲^{l,∞}`-norm of `Spaces/Defs.lean`).

The `k = 6` rows of `H6Pair` need the same five fields at **order six**: a Leibniz expansion of
order six puts six derivatives on *every* factor of a product, so the `ℋ⁶` slots of `u · v`
involve `D_z^6u` and `mixed 6 ·` of `u`, and `WlInfMem α 4` does not control those.  The
level-six context therefore carries the order-six data here.

Nothing is lost or added to the mathematics: `StarPkg6` *extends* `StarPkgo2`, so the
order-four fields are carried along.  (The order-six bounds do imply the order-four ones, since
`WlInf α l` is a sum of nonnegative suprema over a set of slots growing with `l`, but the
`StarPkgo2` fields are kept explicitly to avoid any `SupFinite` side condition.)  The package is
*derivable* from the sibling area's analysis target
`Work.FTS.PhiStar.StarCore` (`core : FlatW 7 (Ycheck α Φs) (Cs α)`) by the order-six lift of
`Work.FTS.PhiStar.wlInf_of_zeroOff`, exactly as `Work.FTS.PhiStar.StarPkgo2OfCore` obtains
`StarPkgo2`; the delegated lemma `StarPkg6.of_starCore` performs that lift. -/
structure StarPkg6 (α Cs : ℝ) (Φs : Fn) : Prop
    extends Work.FTS.VocabO2.StarPkgo2 α Cs Φs where
  /-- the `ℛ`-field `((z+1)/z)·ℛ(Φ̃_*)` at order six (rows 10, 11 of the paper's list). -/
  RW6 : Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ Cs * α
  /-- the `V`-field `V(Φ̃_*)` at order six. -/
  VW6 : Work.Spaces.WlInfMem α 6 (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ∧
    Work.Spaces.WlInf α 6 (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ≤ Cs * α
  /-- the weighted `V`-field `((z+1)/z)·V(Φ̃_*)` at order six. -/
  VzW6 : Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      ≤ Cs * α
  /-- the `U/ sin 2θ`-field at order six. -/
  UsW6 : Work.Spaces.WlInfMem α 6
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) ≤ Cs * α
  /-- the weighted `U/ sin 2θ`-field `((z+1)/z)·U(Φ̃_*)/sin 2θ` at order six. -/
  UszW6 : Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ≤ Cs * α

/-- **The splitting clause of the level-six pairing.**  `H6Split IP α f rhs` says that the pairing
is additive across the sum `linPart α f + rhs` of the equation's two sides, evaluated at `f`.

This is the *satisfiable* replacement of the earlier hypothesis `HQo α 6 (linPart α f)`: that
statement demands `SmoothOpen (𝓛_Γ^T f)`, which is **false** for honest `H6Adm` data (the
nonlocal term forces the angular moment `z ↦ ∫_θ K(θ)f(z,θ)dθ` to be `C^∞` on `(0,∞)`, which a
fixed-order weighted class does not give; see `NOTES_L3_lin_FALSE.md` and the sibling
refutations `NOTES_Rop_Hk_le_FALSE.md`, `NOTES_pthU_EllResid_certs_FALSE.md`).  By contrast
`H6Split` is a statement about the *integrals* defining `IP6` — it only needs the slots of
`linPart α f` to be integrable, which is what `H6Lin`/`L3Data.lin` supply — and it is therefore
inhabited for the concrete pairing. -/
def H6Split (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (f rhs : Fn) : Prop :=
  IP α (linPart α f + rhs) f = IP α (linPart α f) f + IP α rhs f

/-- **The context of the level-six pairing bound**: the slice `g(·,·,τ)` is in the level-six
coercivity class with `ℋ⁴`-norm bounded by `M` and order-seven honesty, the pairing splits
across the two sides of the equation, the nonlinear side `gRHS(…, g(τ))` is honest, and the
elliptic side is controlled by the *split* context `Ell6Ctx`. -/
structure L6Ctx (IP : ℝ → Fn → Fn → ℝ) (α M Ce Cs : ℝ) (E : Fn → Fn) (Φs : Fn) (g Φ : Fam)
    (τ : ℝ) : Prop where
  /-- the slice is in the level-six coercivity class (honest `ℋ⁶`, angular vanishing, axis
  vanishing and the `L₁₂`-projector condition). -/
  hreg : H6Adm α (slice g τ)
  /-- order-seven honesty of the slice: what `H6Lin` and the level-six transport clauses T2/T3
  take as their hypothesis on the `g`-side. -/
  h7 : Work.Spaces.HkMem α 7 (slice g τ)
  /-- the a-priori `ℋ⁴` bound. -/
  hbdd : Xn α (slice g τ) ≤ M
  /-- the pairing splits across the two sides of the equation (`H6Split`).  This replaces the
  unsatisfiable `HQo α 6 (linPart α (slice g τ))`; see `H6Split`. -/
  hsplit : H6Split IP α (slice g τ) (dynRHS α Φ g τ)
  /-- the *nonlinear* side `gRHS(…, g(τ))` of the equation is in the honest `ℋ⁶`-class. -/
  hrhs : HQo α 6 (dynRHS α Φ g τ)
  /-- the elliptic a-priori data of the stream function, in the split form. -/
  hell : Ell6Ctx α Ce Cs E Φs (slice g τ) (slice Φ τ)
  /-- the **level-six star data**: the order-six lift of `Ell6Ctx.hstar` (which is the level-four
  package `StarPkgo2`).  It is what the `k = 6` rows of `H6Pair` consume; see `StarPkg6` for why
  the order-four star data does not suffice at level six, and
  `StarPkg6.of_starCore` for its supply from the sibling area's `PhiStar.StarCore`. -/
  hstar6 : StarPkg6 α Cs Φs

/-- **`H6Pair` — the level-six pairing bound for the nonlinear right-hand side.**  This is the
coarse form in which the k = 6 versions of the rows (the per-piece estimates of
`FTS/NonlinRows`, the §Modulation estimates of the paper) are consumed by the persistence
argument: pairing `dynRHS` against `g` at level six costs at most
`(1+|Ce|+|Cs|)⁴ (1 + Xn₄)⁴ (1 + |g|²_{ℋ⁶})`, with a deliberately generous `α`-power — the sharp
rows give `α^{-1/2}`-type bounds, which imply the form below for `α ≤ 1`.

**The elliptic factor `(1+|Ce|+|Cs|)⁴` is not cosmetic.**  `Ce` (the perturbation constant of
`EllPkgK`) and `Cs` (the star constant of `StarPkgo2`) occur only in the *hypothesis* `L6Ctx`;
a conclusion uniform in them would be false for large constants (the residual `Rop/Uop/Vop` is
multiplied by the profile `F = F_* + f` and by the star fields), while a conclusion *without*
the factor is degenerate for small ones (`Ce = 0` forces the residual to vanish identically, so
the class collapses — see the analysis in `Degen/PkgKZeroCollapse.lean`).  Pricing the elliptic
data polynomially, as below, is the honest coarse form (the sharp estimates are quadratic in
that data, and the fourth power dominates). -/
structure H6Pair (IP : ℝ → Fn → Fn → ℝ) (α₂ Ce Cp : ℝ) : Prop where
  pos : 0 < Cp ∧ 0 < α₂
  pair : ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs : ℝ) (E : Fn → Fn) (Φs : Fn), 0 ≤ τ →
    L6Ctx IP α M Ce Cs E Φs g Φ τ →
    |IP α (dynRHS α Φ g τ) (slice g τ)|
      ≤ Cp * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
          * (1 + Sq6 α (slice g τ))

/-- **The level-six energy identity.**  Differentiating the `ℋ⁶`-energy along the flow and
substituting the equation (`gdot = dynLin + dynRHS` on the open quadrant) identifies the
derivative of `τ ↦ IP (slice g τ) (slice g τ)`; the continuity of that function on `[0,T]` is
the second analytic ingredient of the a-priori estimate.  Both are *regularity* statements
about the solution, independent of any bound. -/
structure H6EnergyDeriv (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (Φ g : Fam) (T : ℝ) : Prop where
  cont : ContinuousOn (fun τ => IP α (slice g τ) (slice g τ)) (Set.Icc 0 T)
  deriv : ∀ τ, 0 ≤ τ → τ < T →
    HasDerivWithinAt (fun s => IP α (slice g s) (slice g s))
      (2 * IP α (dynLin α g τ + dynRHS α Φ g τ) (slice g τ)) (Set.Ici 0) τ

/-! ## The two summands of the right-hand side, and the level-three package (S6) -/

/-- The right-hand side of the `g`-equation as a function of the profile: by `rfl`,
`dynRHS α Φ g τ = rhsOf α (muDyn α Φ g τ) (lamDyn α Φ g τ) (Ftau α g τ) (slice Φ τ) (slice g τ)`. -/
abbrev rhsOf (α μ lam : ℝ) (F Φ f : Fn) : Fn := Work.Construction.gRHS α μ lam F Φ f

theorem dynRHS_eq_rhsOf (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    dynRHS α Φ g τ = rhsOf α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
      (Work.Construction.Ftau α g τ) (slice Φ τ) (slice g τ) := rfl

/-- **The level-three operator package of S6.**  S6 asks for
`‖dynLin + dynRHS‖_{ℋ³} ≤ C(Xn₄)`.  The two summands are a *linear* second-order operator in
`f = slice g τ` (the paper's `𝓛_Γ^T`) and the nonlinear right-hand side (quadratic in `f`, in
`F_* + f` and in the elliptic solution `Φ`); the two fields below are the level-three
statement of the corresponding estimates, in the `HQo`-based class of honest solutions.

The power `(1 + M)⁴` is deliberately lossy (the sharp estimates are quadratic in `M`); it is
the coarse form in which the norm-level rows are consumed. -/
structure L3Data (α₂ Ce C3 Cpow : ℝ) : Prop where
  /-- `Cpow` is the exponent of the `α`-loss of the nonlinear clause: `gRHS` contains the term
  `(1/α)L₁₂(f)·f`, which forces `|gRHS|_{ℋ³} ≳ 1/α`, so the estimate *cannot* have an
  `α`-independent constant as `α → 0⁺` (a scaling argument of the reviewer). -/
  pos : 0 < C3 ∧ 0 < α₂ ∧ 0 ≤ Cpow
  /-- the linear part: `linPart α f = -𝓛_Γ^T f` lies in `ℋ³` with a bound by the `ℋ⁴` norm of `f`.

  Two features of this clause are the result of the mandatory reviews and must not be "simplified"
  back:

  * the **class** is `H6Adm α f`, not `HQo α 4 f`: with `L₁₂(f)(0) ≠ 0` the nonlocal term of
    `𝓛_Γ^T` behaves like `(2Γ(θ)/c)L₁₂(f)(0)·z` at the axis, whose weighted square against
    `w ~ (1+z)²/z²` behaves like `z^{-2}` — not integrable; the same happens for the local term
    when `f(0,θ) ≠ 0`.  Both are excluded by `H6Adm` (`axis`, `l12`), the class the paper's
    estimate (tex 1277) is stated for and the class S2 supplies for the slices of a strong
    solution;
  * the **conclusion is `HkMem` only, not `HQo`**: `SmoothOpen (𝓛_Γ^T f)` is **false** for honest
    `H6Adm` data.  Its nonlocal term has the smooth non-vanishing factor `2zΓ(θ)/(c(1+z)²)`, so it
    forces the angular moment `z ↦ ∫_θ K(θ)f(z,θ)dθ` to be `C^∞` on `(0,∞)`, which a
    weighted-integral class at a fixed order cannot give; a pinched datum of the form
    `θ^{29/2}/(θ²+(z-z₀)²)` is a counterexample (see
    `Submission/Work/FTS/StrongPersist/NOTES_L3_lin_FALSE.md`, refuted by the delegated prover).
    The smoothness of the two sides of the equation is supplied by the caller — in the strong
    route it is the level-three instance of the `SmoothOpen` clauses of `Open3.EqExtra`. -/
  lin : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f →
    HkMem α 3 (linPart α f) ∧ HkNorm α 3 (linPart α f) ≤ C3 * (1 + Xn α f) ^ 4
  /-- the nonlinear part: the right-hand side is `ℋ³` and controlled by the `ℋ⁴` norm of the
  profile together with the elliptic a-priori data.  (The class is `H6Adm`, like `lin`: `gRHS`
  contains the angular moments `L₁₂ f`, and `L₁₂(f)(0) ≠ 0` makes the weighted `ℋ³`-integral of
  the `(1/α)L₁₂ f·f` term diverge at the axis — the same mechanism as for `𝓛_Γ^T`.)

  The source of the elliptic law is pinned to the profile itself, `F = F_* + f` (i.e.
  `Ftau α f`), and **not** left free: `Ell6Data` is scale-invariant in `(F, Φ)` (its bounds are
  *ratios*), while `gRHS` is quadratic in `(F, Φ)`, so a free `F` would make the bound false.

  The pricing is deliberately lossy, and it is the result of two reviews:

  * the factor `(1 + |Ce| + |Cs|)⁴` is *not* cosmetic.  `gRHS` is quadratic in the elliptic data
    (the residual `Rop/Uop/Vop` of `Φ`, whose size is `Ce`, and the star fields, whose size is
    `Cs`), so a constant uniform in `(Ce, Cs)` is false for large constants, while a constant
    *without* the factor is degenerate for small ones (`Ce = 0` forces the transported residual
    to vanish identically, so the class collapses — see
    `Submission/Work/FTS/StrongPersist/Degen/PkgKZeroCollapse.lean`).  Any polynomial pricing is
    honest; the fourth power is more than enough;
  * the factor `(1 + Xn6 α f)²` is *not* cosmetic either, and it is the correction of the first
    version of this clause: `EllPkgK α 6` prices the transported residual by `Ce · HkNorm α 6 f`,
    and there is **no** relation between `Xn6 α f` and `Xn α f = HkNorm α 4 f` (a family
    `N^{-4}φ(z)sin(Nz)ψ(θ)` with `∫_θ K ψ = 0` has `Xn α f ≍ 1` and `Xn6 α f ≍ N²` while all
    `H6Adm` fields hold).  Since `gRHS` contains those residual fields *linearly*, the honest
    price of `|gRHS|_{ℋ³}` is polynomial in `(1+Ce+Cs)^4 (1+M)^4` **and** carries the factor
    `(1 + Xn6 α f)`.  (`Xn6 α f` is *not* independent data: it is bounded by S2's persistence
    bound `C6 = C6(Xn α f, T)`, which is why the composed estimate is still
    `≤ C(Xn₄)` — see `Dbd.dbd_of_eq` and the discussion there.)

  The `α`-power `α^{-Cpow}` is unavoidable: `gRHS` contains `(1/α)L₁₂(f)·f`. -/
  rhs : ∀ α ∈ Set.Ioc 0 α₂, ∀ (E : Fn → Fn) (Φs Φ f : Fn) (Cs μ lam M : ℝ),
    Ell6Ctx α Ce Cs E Φs f Φ → H6Adm α f → Xn α f ≤ M →
    |μ| ≤ 1 / 2 → |lam| ≤ 1 →
    HkMem α 3 (rhsOf α μ lam (Work.Construction.Ftot α f) Φ f) ∧
    HkNorm α 3 (rhsOf α μ lam (Work.Construction.Ftot α f) Φ f)
      ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2



end Work.FTS.StrongPersist
end
end
