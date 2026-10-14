import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# `F_*(F)·sin 2θ ∈ ℋ^k` for an open-quadrant smooth source `F`

This module proves

  `Work.FTS.EllipticEst.HkMem_FstarSin_open`:
for `0 < α ≤ 1`, a source `F` which is `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen F`) and lies in the weighted space
`ℋ^k` (`Work.Spaces.HkMem α k F`), the angular moment `F_*(F)(z) = ∫_θ F(z,θ) sinθcos²θ dθ`
multiplied by the angular profile `sin 2θ` lies again in `ℋ^k`.

This is the open-quadrant analogue of `Work.FTS.EllipticEst.HkMem_FstarSin`
(`Fstar_sin_HkMem_HkNorm.lean`), which assumes the much stronger `Work.Spaces.SmoothNbhd F`.

## The route

* `F_*(F)(z)·sin 2θ` is a product `R(z)·χ(θ)` of a radial and an angular factor, so the two
  product rules `D_z^j (R(z)χ(θ)) = (rDzIter j R)(z)·χ(θ)` (`DzIter_mul_of_radial`) and
  `D_θ^i (R(z)χ(θ)) = R(z)·(D_θ^i χ)(0,θ)` (`DthIter_mul_of_angular`) turn the `ℋ^k`-integrand
  of the target into an explicit sum in which only the radial iterates `rDzIter j R` and the
  angular profiles `sinIter i = D_θ^i(sin 2θ)` occur (`HkIntegrand_GbarSin_eq`).
* The angular profiles are bounded against the weight (`sinIter_weight_bound`), which gives the
  pointwise bound `HkIntegrand α k (F_*·sin 2θ) z θ ≤ K·w(z)²·Σ_{j≤k}(rDzIter j F_* z)²` with
  `K` independent of `α`, of `F` and of the point (`HkIntegrand_FstarSin_le`).
* The radial iterates are the angular moments of the radial derivatives of `F`:
  `rDzIter j (F_*(F)) = F_*(D_z^j F)` on `(0,∞)` for `j ≤ k - 1` and a.e. for `j = k`
  (`rDzIter_Fstar_eq`, `rDzIter_Fstar_ae`).  This is an induction whose step is the fundamental
  theorem of calculus applied to the chain relation
  `F_*(D_z^j F) z - F_*(D_z^j F) s = ∫_{s}^{z} F_*(D_z^{j+1}F) r / r dr`
  (`GbarSin.FstarDzIter_chain_open`), the a.e. statement at the top level coming from the
  Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`).
* Cauchy–Schwarz on the angular slice bounds each moment by a single summand of the
  `ℋ^k`-integrand of `F` (`FstarDzIter_sq_mul_w_le_open`), and those summands are dominated by
  the `θ`-integral of that integrand, which is integrable by hypothesis (`hmem`).

The two halves of `HkMem` are then obtained directly: the `θ`-slices of the target integrand are
bounded (by the explicit form above) hence integrable for every `z ∈ Iz`, and the `z`-integral of
the slices is a.e. dominated by a constant multiple of the slice-integral of the source's
`ℋ^k`-integrand, which is integrable.
-/

/-! ## Elementary facts -/

/-- `F_*(D_z^j F)` is `PsiInt F j`, definitionally. -/
theorem PsiInt_eq_Fstar_DzIter (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    PsiInt F j z = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z := rfl

/-- `(0,∞)` and `Iz = [0,∞)` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  exact Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici


/-- `sinθcos²θ` is continuous on `Iθ`. -/
theorem continuousOn_sinCos2_Iθ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The `j`-th weighted `L²`-slice of the source,
`A_j(z) = ∫_θ (D_z^j F(z,θ)·w(z)/sin(2θ)^{η/2})² dθ`. -/
noncomputable def AjF (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

@[simp] theorem AjF_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    AjF F j z = ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

theorem AjF_nonneg (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : 0 ≤ AjF F j z :=
  integral_nonneg fun θ => sq_nonneg _

/-! ## The weighted slices `A_j` and the angular moments -/

/-- The `j`-th summand of the `ℋ^k`-integrand is dominated by the whole `ℋ^k`-integrand. -/
theorem AjF_le_HkIntegrand_integral (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AjF F j z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
  rw [AjF_apply]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
    (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F z θ j hj)

/-- The weighted slice `A_j` is a.e. strongly measurable. -/
theorem AjF_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (AjF F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j F p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
    (hF.continuousOn_summand j).pow 2
  have h := aestronglyMeasurable_integral_Itheta_Q0
    (fun z θ : ℝ => (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    hg (fun _ : ℝ => (1 : ℝ)) continuousOn_const
  show AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (volume.restrict (Set.Ioi 0))
  simpa only [mul_one] using h

/-- The angular moment `z ↦ F_*(D_z^j F)(z)` is a.e. strongly measurable. -/
theorem PsiInt_aesm (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (fun z => PsiInt F j z) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry (Work.Spaces.DzIter j F)) Q0 :=
    (hF.DzIter j).continuousOn
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F) hg
    Work.Elliptic.sinCos2 continuousOn_sinCos2_Iθ
  show AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ) (volume.restrict (Set.Ioi 0))
  simpa only [PsiInt, mul_one] using h

/-- The slice functional `A_j` is integrable on `(0,∞)`. -/
theorem AjF_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (AjF F j) (Set.Ioi 0) := by
  have hmaj : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  refine hmaj.mono' (AjF_aesm α k F hF j) ?_
  show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
    ‖AjF F j z‖ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  have hzI : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
  rw [Real.norm_of_nonneg (AjF_nonneg F j z)]
  exact AjF_le_HkIntegrand_integral α k F hmem j hj hzI

/-! ## Cauchy–Schwarz for the angular moment -/

/-- The Cauchy–Schwarz bound `(F_*(D_z^j F) z)² w(z)² ≤ (π/2)A_j(z)`, in the form of a bound
on the absolute value of the moment. -/
theorem PsiInt_sqrt_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    |PsiInt F j z| ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := by
  have hsq : (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * AjF F j z := by
    rw [PsiInt_eq_Fstar_DzIter, AjF_apply]
    exact FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
  have hA0 : 0 ≤ AjF F j z := AjF_nonneg F j z
  have hw0 : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hdiv : (PsiInt F j z) ^ 2 ≤ ((π / 2) * AjF F j z) / (Work.Spaces.w z) ^ 2 :=
    (le_div_iff₀ (pow_pos hw0 2)).mpr hsq
  have hTnn : 0 ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := by positivity
  have hTsq : (Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2
      = ((π / 2) * AjF F j z) / (Work.Spaces.w z) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hA0]
  have hU2 : (PsiInt F j z) ^ 2
      ≤ (Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2 := by
    rw [hTsq]; exact hdiv
  calc |PsiInt F j z| = Real.sqrt ((PsiInt F j z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2) :=
        Real.sqrt_le_sqrt hU2
    _ = Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := Real.sqrt_sq hTnn

/-! ## Continuity of the angular moments -/

/-- **Continuity of the angular moments.**  For `j + 1 ≤ k` the moment `F_*(D_z^j F)` is
continuous on `(0,∞)`: by the chain relation it is the primitive of `F_*(D_z^{j+1}F)/r`, which
obeys the weighted square-root bound with the integrable majorant `A_{j+1}`. -/
theorem PsiInt_continuousOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => PsiInt F j z) (Set.Ioi 0) := by
  refine continuousOn_of_primitive_of_sqrt_bound (u := fun z => PsiInt F j z)
    (v := fun z => PsiInt F (j + 1) z) (A := AjF F (j + 1))
    (AjF_integrableOn α k F hF hmem (j + 1) hj) ?_ ?_
  · intro r hr
    exact PsiInt_sqrt_bound α k F hF hmem (j + 1) hj hr
  · intro s z hs hsz
    exact Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz

/-! ## Local integrability of the moment density `F_*(D_z^j F)/r` -/

/-- `F_*(D_z^j F)(r)/r` is integrable on `(0,b)` for `b > 0`: the weighted square-root
bound `√x ≤ 1 + x` and the integrability of `A_j` give an `L¹` majorant. -/
theorem PsiInt_div_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r => PsiInt F j r / r) (Set.Ioo 0 b) := by
  have hsub : Set.Ioo (0 : ℝ) b ⊆ Set.Ioi (0 : ℝ) := fun x hx => hx.1
  -- the majorant `√(π/2)·(1 + A_j)` on `(0,b)`
  have hAint : IntegrableOn (AjF F j) (Set.Ioo 0 b) :=
    (AjF_integrableOn α k F hF hmem j hj).mono_set hsub
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 b) := by
    refine integrableOn_const ?_
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmaj : IntegrableOn (fun r => Real.sqrt (π / 2) * (1 + AjF F j r)) (Set.Ioo 0 b) :=
    (hconst.add hAint).const_mul (Real.sqrt (π / 2))
  have haesm : AEStronglyMeasurable (fun r => PsiInt F j r / r)
      (volume.restrict (Set.Ioo 0 b)) :=
    ((PsiInt_aesm F hF j).mono_measure (Measure.restrict_mono hsub le_rfl)).mul
      (measurable_id.inv.aestronglyMeasurable)
  refine Integrable.mono' hmaj haesm ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun r hr => ?_
  have hr0 : 0 < r := hr.1
  have hbd := PsiInt_sqrt_bound α k F hF hmem j hj hr0
  have hA0 : 0 ≤ AjF F j r := AjF_nonneg F j r
  have hsqrt : Real.sqrt (AjF F j r) ≤ 1 + AjF F j r := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hwr : (Work.Spaces.w r * r)⁻¹ = r / (1 + r) ^ 2 := by
    rw [Work.Spaces.w]; field_simp
  have hratio : r / (1 + r) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hr0.le]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
  calc |PsiInt F j r| / r
      ≤ (Real.sqrt (π / 2) * Real.sqrt (AjF F j r) / Work.Spaces.w r) / r :=
        div_le_div_of_nonneg_right hbd hr0.le
    _ = Real.sqrt (π / 2) * Real.sqrt (AjF F j r) * (r / (1 + r) ^ 2) := by
        rw [div_div, div_eq_mul_inv, hwr]
    _ ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j r) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ Real.sqrt (π / 2) * (1 + AjF F j r) := by
        have := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (π / 2))
        linarith [this]

/-! ## The extended density and its local integrability -/


/-! ## Differentiation of the angular moments in the interior -/

/-- **The derivative of the angular moments.**  For `j + 2 ≤ k` the moment `F_*(D_z^j F)` is
differentiable at every `z > 0` with derivative `F_*(D_z^{j+1}F)(z)/z`: its increments are the
integral of `F_*(D_z^{j+1}F)(r)/r` (the chain relation) and that density is continuous at `z`
because `F_*(D_z^{j+1}F)` is continuous (`j + 2 ≤ k`). -/
theorem hasDerivAt_PsiInt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun u => PsiInt F j u) (PsiInt F (j + 1) z / z) z := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hchain : ∀ s u : ℝ, 0 < s → s ≤ u →
      PsiInt F j u - PsiInt F j s = ∫ r in s..u, PsiInt F (j + 1) r / r :=
    fun s u hs hsu => GbarSin.FstarDzIter_chain_open α k F hF hmem j (by omega) hs hsu
  have hcont : ContinuousOn (fun r => PsiInt F (j + 1) r / r) (Set.Ioi 0) :=
    (PsiInt_continuousOn α k F hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun r hr => ne_of_gt hr)
  have hmeas : StronglyMeasurableAtFilter (fun r => PsiInt F (j + 1) r / r) (𝓝 z) volume :=
    _root_.AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((PsiInt_aesm F hF (j + 1)).mul measurable_id.inv.aestronglyMeasurable)
      (isOpen_Ioi.mem_nhds hz)
  have hint : IntervalIntegrable (fun r => PsiInt F (j + 1) r / r) volume a z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le haz.le]
    exact (PsiInt_div_integrableOn α k F hF hmem (j + 1) (by omega) (b := 2 * z)
      (by linarith)).mono_set (fun x hx => ⟨by linarith [ha0, hx.1], by linarith [hx.2, hz]⟩)
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun u : ℝ => PsiInt F j u) =ᶠ[𝓝 z]
      (fun u => (∫ r in a..u, PsiInt F (j + 1) r / r) + PsiInt F j a) := by
    filter_upwards [Ioi_mem_nhds haz] with u hu
    have h := hchain a u ha0 hu.le
    linarith
  exact (hderiv.add_const _).congr_of_eventuallyEq hev

/-! ## The a.e. derivative identity (Lebesgue differentiation) -/


/-! ## The radial iterates of the moment are the angular moments -/



/-! ## Measurability of the radial powers `x ↦ x ^ c` -/

/-- The real power function `x ↦ x ^ c` is measurable (for every real exponent). -/
theorem measurable_rpow_const (c : ℝ) : Measurable (fun x : ℝ => x ^ c) := by
  have hsplit : (fun x : ℝ => x ^ c) = fun x => if 0 ≤ x then
      (if x = 0 then (if c = 0 then 1 else 0) else Real.exp (Real.log x * c))
      else Real.exp (Real.log x * c) * Real.cos (c * Real.pi) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, Real.rpow_def_of_nonneg hx]
    · rw [if_neg hx, Real.rpow_def_of_neg (lt_of_not_ge hx)]
  rw [hsplit]
  refine Measurable.ite measurableSet_Ici ?_ ?_
  · refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)
  · exact (Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)).mul measurable_const

/-- `θ ↦ sin(2θ)^c` is measurable. -/
theorem measurable_sin_two_rpow (c : ℝ) : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) :=
  (measurable_rpow_const c).comp (by fun_prop)

/-! ## The pointwise `ℋ^k`-integrand bound for a radial profile times `sin 2θ` -/


/-! ## Measurability of the `ℋ^k`-integrand of `R(z)·sin 2θ` (fixed `z`) -/


/-! ## The `θ`-slices of the target integrand are integrable -/


/-! ## Almost everywhere strong measurability of the radial iterates of `F_*` -/


/-! ## Joint a.e. strong measurability of the target integrand -/



/-! ## The a.e. bound on the slice-integral of the target -/



/-! ## Item two of `ℋ^k`-membership: integrability of the `z`-integral of the slices -/



end Work.FTS.EllipticEst
