import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.Elliptic.DivSinPerZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the angular interval

Everything below is one-dimensional `θ`-calculus on `Iθ = [0, π/2]`.  The open interval
`(0, π/2)` differs from `Iθ` by two points, so almost-everywhere statements can be checked
on the open interval, where the slices are smooth. -/




/-! ## Continuity of the slices and of the weights -/








/-! ## The integral of a finite sum of nonnegative functions -/



/-! ## A sorry-free weighted Hardy inequality

`Work.Elliptic.DivSinHardy` (which the termwise bounds `DivSinTermwise` rest on) is currently
`:= by sorry`, so a proof that calls it inherits `sorryAx`.  For that reason the inequality is
re-proved here, via the sharp weighted Hardy inequality `sharp_hardy_sin_two` and the `η = 0`
case of `sin_l2_weight_bound` (a Poincaré inequality for slices vanishing at `θ = 0`):

  `∫ h²/s^{2+η} ≤ 1/(1+η)² ∫ (h')²/s^η + C(∫h² + ∫(h')²)
              ≤ 1/(1+η)² ∫ (h')²/s^η + C(K₀+1) ∫ (h')²/s^η`,

the last step using `∫h² ≤ K₀∫(h')²` and the pointwise comparison `(h')² ≤ (h')²/s^η`
(valid because `0 < sin(2θ) ≤ 1` on `(0, π/2)`). -/








/-! ## The per-`z` comparison -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The radial profile is controlled by its `sin (2θ)`-multiple

The main theorem of this file: for every `k` there is `C > 0`, independent of `α ∈ (0,1/4]`
and of the radial profile `Λ`, with

`|Λ|_{ℋ^k} ≤ C · |Λ · sin 2θ|_{ℋ^k}`.

The proof is assembled in `Radial` (see `radialAuxBase`, `radialAuxAng`, `radialAuxInt`,
`radialAuxHk`): the `θ`-integral of `HkIntegrand α k (Λ)` is `Φ z · A_η` and that of
`HkIntegrand α k (Λ · sin 2θ)` is `Φ z · A_{2-η} + W α k Λ z` with `W ≥ 0` and
`W ≤ (∑_i B(α,i)) · Φ`, so that both `HkSq`s are controlled by the single number
`∫_z Φ z`.  The case distinction on `Integrable Φ` handles the junk value `0` that the
Bochner integral assigns to non-integrable functions.
-/

namespace Work.FTS.EllSol.PkgK5

/-- On `[0,∞)` the point `0` is negligible. -/
theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi 0 := by
  have h0 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h0] with z hz
  exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hz),
    fun h => by simpa only [Work.Spaces.Iz, Set.mem_Ici] using h.le⟩

theorem radialHkNorm_le_sinMul (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Λ : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) →
      Work.Spaces.HkNorm α k (fun z θ => Λ z)
        ≤ C * Work.Spaces.HkNorm α k (fun z θ => Λ z * Real.sin (2 * θ)) := by
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound k
  have hAeta : 0 < Radial.Aeta :=
    Radial.sin_rpow_pos (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  have hAeta2 : 0 < Radial.Aeta2 :=
    Radial.sin_rpow_pos (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  refine ⟨Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1, by positivity, ?_⟩
  intro α Λ hα hα1 hΛ
  have hWcont : ContinuousOn (fun z => Radial.W α k Λ z) (Set.Ioi 0) :=
    Radial.continuousOn_W α k Λ hΛ
  have hinner0 : ∀ z ∈ Set.Ioi 0,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
        = Radial.Phi k Λ z * Radial.Aeta := fun z hz => Radial.thetaIntegral_radial α k Λ hΛ hz
  have hinner1 : ∀ z ∈ Set.Ioi 0,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
        = Radial.Phi k Λ z * Radial.Aeta2 + Radial.W α k Λ z :=
    fun z hz => Radial.thetaIntegral_sinMul α k Λ hα hα1 hΛ hz
  have hSq0 : Work.Spaces.HkSq α k (fun z θ => Λ z)
      = ∫ z in Set.Ioi 0, Radial.Phi k Λ z * Radial.Aeta := by
    rw [Work.Spaces.HkSq, MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioi.measurableSet hinner0)
  have hSq1 : Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))
      = ∫ z in Set.Ioi 0, (Radial.Phi k Λ z * Radial.Aeta2 + Radial.W α k Λ z) := by
    rw [Work.Spaces.HkSq, MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioi.measurableSet hinner1)
  by_cases hΦint : Integrable (fun z => Radial.Phi k Λ z) (volume.restrict (Set.Ioi 0))
  · -- Case 1: `Φ` is integrable, so both `HkSq`s are controlled by `∫ Φ`.
    have hA2int : Integrable (fun z => Radial.Phi k Λ z * Radial.Aeta2)
        (volume.restrict (Set.Ioi 0)) := Integrable.mul_const hΦint _
    have hWint : Integrable (fun z => Radial.W α k Λ z) (volume.restrict (Set.Ioi 0)) := by
      refine MeasureTheory.Integrable.mono'
        (Integrable.const_mul hΦint (∑ i ∈ Finset.range (k + 1), Radial.Bcoef α i))
        (hWcont.aestronglyMeasurable isOpen_Ioi.measurableSet) ?_
      filter_upwards with z
      rw [Real.norm_of_nonneg (Radial.W_nonneg α k Λ z)]
      exact Radial.W_le_sum_Bcoef_mul_Phi α k Λ z
    have h1 : Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)
        ≤ Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ)) := by
      rw [hSq1, MeasureTheory.integral_add hA2int hWint]
      have h2 : 0 ≤ ∫ z in Set.Ioi 0, Radial.W α k Λ z :=
        MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_of_all _
          (fun z => Radial.W_nonneg α k Λ z))
      rw [MeasureTheory.integral_mul_const]
      linarith
    have h0 : Work.Spaces.HkSq α k (fun z θ => Λ z)
        = Radial.Aeta * (∫ z in Set.Ioi 0, Radial.Phi k Λ z) := by
      rw [hSq0, MeasureTheory.integral_mul_const]; ring
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, h0]
    have hsplit : Radial.Aeta * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)
        = (Radial.Aeta / Radial.Aeta2)
          * (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hAeta2)]
    rw [hsplit, Real.sqrt_mul (by positivity : 0 ≤ Radial.Aeta / Radial.Aeta2)]
    have hsqrt : Real.sqrt (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z))
        ≤ Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
      Real.sqrt_le_sqrt h1
    have h0le : Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ)))
        ≤ (Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) := by
      have h2 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
        Real.sqrt_nonneg _
      nlinarith [h2]
    calc Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z))
        ≤ Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) := h0le
  · -- Case 2: `Φ` is not integrable, so `HkSq α k (Λ) = 0` (junk value of the integral).
    have hnot : ¬ Integrable (fun z => Radial.Phi k Λ z * Radial.Aeta)
        (volume.restrict (Set.Ioi 0)) := by
      intro hc
      have hc' : Integrable (fun z => Radial.Aeta * Radial.Phi k Λ z)
          (volume.restrict (Set.Ioi 0)) :=
        Integrable.congr hc (Filter.Eventually.of_forall (fun z => by ring))
      exact hΦint ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hAeta)) _).mp hc')
    have h0 : Work.Spaces.HkSq α k (fun z θ => Λ z) = 0 := by
      rw [hSq0, MeasureTheory.integral_undef hnot]
    rw [Work.Spaces.HkNorm, h0, Real.sqrt_zero]
    exact mul_nonneg (by positivity)
      (Real.sqrt_nonneg (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))))

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.residualTendstoZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

open MeasureTheory Filter
open scoped BigOperators

/-- **The residual of the truncated angular mode series tends to zero in `L²(Iθ, cos θ dθ)`.**

For a slice `ψ` with `∫_{Iθ} ψ² cos θ < ∞` (and `ψ` a.e. strongly measurable), the partial
sums of its expansion in the Dirichlet eigenbasis `eFam m` of `Lzero`
(`eFam m θ = cos θ · gC (2m+1) (sin θ)`, orthogonal for the weight `cos θ dθ`) converge to `ψ`
in `L²(Iθ, cos θ dθ)`.

This is the combination of the two standard facts about the truncated expansion:

* Pythagoras (`Work.EllipticEst.ModalSolution.eFam_pythagoras`): the residual is the `L²`-norm
  defect
  `∫ (ψ - Σ_{m≤N} c_m e_m)² cos = ∫ ψ² cos - Σ_{m≤N} c_m² ∫ e_m² cos`,
  `c_m = cmode m (fun _ θ' => ψ θ') 0`;
* Parseval (`Work.EllipticEst.ModalSolution.eFam_parseval`): the defect itself tends to `0`,
  `Σ_{m≤N} c_m² ∫ e_m² cos → ∫ ψ² cos`.

Both are applied to the `z`-independent slice `fun _ θ' => ψ θ'` at `z = 0`, for which
`(fun _ θ' => ψ θ') 0 = ψ` definitionally. -/
theorem residualTendstoZero (ψ : ℝ → ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      Filter.atTop (nhds 0) := by
  have hmeas' : MeasureTheory.AEStronglyMeasurable ((fun _ θ' => ψ θ') 0)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hmeas
  have hz' : MeasureTheory.IntegrableOn
      (fun θ => (fun _ θ' => ψ θ') 0 θ ^ 2 * Real.cos θ) Work.Spaces.Iθ := hz
  -- Pythagoras identifies the residual with the `L²`-norm defect.
  have hkey : (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = fun N : ℕ => (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    funext N
    exact Work.EllipticEst.ModalSolution.eFam_pythagoras
      (fun _ θ' => ψ θ') 0 N hmeas' hz'
  rw [hkey]
  -- Parseval says the defect tends to the full `L²`-mass, so the residual tends to `0`.
  have h1 : Filter.Tendsto (fun _ : ℕ => (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ))
      Filter.atTop (nhds (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ)) :=
    tendsto_const_nhds
  have h2 := h1.sub (Work.EllipticEst.ModalSolution.eFam_parseval
    (fun _ θ' => ψ θ') 0 hmeas' hz')
  simpa using h2

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupOpenH2Z =====
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

set_option autoImplicit false

/-! ## The squared `L²` norm of an angular slice -/

/-- `L2slice f z = ∫_{Iθ} f z θ ^ 2`, the squared `L²(Iθ)` norm of the slice `θ ↦ f z θ`. -/
def L2slice (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, f z θ ^ 2

theorem L2slice_nonneg (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ L2slice f z :=
  integral_nonneg fun _ => sq_nonneg _

/-! ## A.e. strong measurability of the slices and of the joint integrands -/

/-- A function of two variables which is continuous on the open quadrant is a.e. strongly
measurable for the product of the restrictions of Lebesgue measure to `(0,∞)` and `Iθ`. -/
theorem aesm_uncurry_Ioi {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hself : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) := Filter.EventuallyEq.refl _ _
  have hprod : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := MeasureTheory.Measure.set_prod_ae_eq hself hθ
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable (Function.uncurry g)
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-- Same statement with `(0,∞)` replaced by a half-open interval `(a,b]`, `0 < a`. -/
theorem aesm_uncurry_box_Ioc {g : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hzb : Set.Ioc a b =ᵐ[volume] Set.Ioo a b := (MeasureTheory.Ioo_ae_eq_Ioc).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hprod : ((Set.Ioc a b) ×ˢ Work.Spaces.Iθ) =ᵐ[volume.prod volume]
      ((Set.Ioo a b) ×ˢ Set.Ioo 0 (π / 2)) := MeasureTheory.Measure.set_prod_ae_eq hzb hθ
  have hsub : (Set.Ioo a b) ×ˢ (Set.Ioo 0 (π / 2)) ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) :=
    fun p hp => ⟨lt_of_lt_of_le ha hp.1.1.le, hp.2⟩
  have hUm : MeasurableSet ((Set.Ioo a b) ×ˢ (Set.Ioo 0 (π / 2))) :=
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable (Function.uncurry g)
      ((volume.prod volume).restrict ((Set.Ioo a b) ×ˢ (Set.Ioo 0 (π / 2)))) :=
    (hg.mono hsub).aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-- The map `z ↦ ∫_{Iθ} Φ z θ ^ 2` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_L2slice {Φ : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioi 0)) := by
  have hpow : ContinuousOn (Function.uncurry fun z θ => Φ z θ ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hcont.pow 2
  exact (aesm_uncurry_Ioi hpow).integral_prod_right'

/-! ## The fundamental theorem of calculus in `z`, slicewise in `θ` -/

/-- For `θ ∈ (0,π/2)` the slice `s ↦ Φ s θ` is differentiable on `(0,∞)` with derivative
`Φ' · θ`, hence `(Φ · θ)²` has derivative `2 Φ Φ'` and the fundamental theorem of calculus
applies on `[a,b]`. -/
theorem slice_sq_ftc {Φ Φ' : ℝ → ℝ → ℝ} {θ a b : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hderiv : ∀ z ∈ Set.Ioi 0, HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z) :
    ∫ s in a..b, 2 * Φ s θ * Φ' s θ = Φ b θ ^ 2 - Φ a θ ^ 2 := by
  have hsub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]
    exact fun s hs => lt_of_lt_of_le ha hs.1
  have hder : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun z' => Φ z' θ ^ 2) (2 * Φ s θ * Φ' s θ) s := by
    intro s hs
    have hs0 : s ∈ Set.Ioi (0 : ℝ) := hsub hs
    refine ((hderiv s hs0).pow 2).congr_deriv ?_
    ring
  have hmap : ContinuousOn (fun s : ℝ => (s, θ)) (Set.uIcc a b) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hcs : ContinuousOn (fun s : ℝ => Φ s θ) (Set.uIcc a b) :=
    hcont.comp hmap fun s hs => ⟨hsub hs, hθ⟩
  have hcs' : ContinuousOn (fun s : ℝ => Φ' s θ) (Set.uIcc a b) :=
    hcont'.comp hmap fun s hs => ⟨hsub hs, hθ⟩
  have hint : IntervalIntegrable (fun s => 2 * Φ s θ * Φ' s θ) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn (fun s => (2 : ℝ) * Φ s θ * Φ' s θ) _
    exact (continuousOn_const.mul hcs).mul hcs'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint

/-- The one-sided form used below: for `0 < a ≤ b` and `θ ∈ (0,π/2)`,
`Φ a θ² - Φ b θ² ≤ 2 ∫_a^b |Φ s θ · Φ' s θ|`. -/
theorem slice_abs_le_ftc {Φ Φ' : ℝ → ℝ → ℝ} {θ a b : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hderiv : ∀ z ∈ Set.Ioi 0, HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z) :
    Φ a θ ^ 2 - Φ b θ ^ 2 ≤ 2 * ∫ s in a..b, |Φ s θ * Φ' s θ| := by
  have h1 := slice_sq_ftc (Φ := Φ) (Φ' := Φ') hθ ha hab hcont hcont' hderiv
  have h2 : -(∫ s in a..b, 2 * Φ s θ * Φ' s θ)
      ≤ ∫ s in a..b, |2 * Φ s θ * Φ' s θ| :=
    le_trans (neg_le_abs _) (intervalIntegral.abs_integral_le_integral_abs hab)
  have h3 : ∫ s in a..b, |2 * Φ s θ * Φ' s θ| = 2 * ∫ s in a..b, |Φ s θ * Φ' s θ| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (2 : ℝ) * Φ s θ * Φ' s θ = 2 * (Φ s θ * Φ' s θ) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-! ## Integrability of the slices on a compact sub-interval of `(0,∞)` -/

/-- `L2slice Φ` is integrable on `(a,b]` when `s ↦ L2slice Φ s / s` is integrable on
`(0,∞)`: on `(a,b]` one has `L2slice Φ s = s · (L2slice Φ s / s) ≤ b · (…)`. -/
theorem integrableOn_L2slice_div {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFm : AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioi 0)))
    (hFint : IntegrableOn (fun z : ℝ => L2slice Φ z / z) (Set.Ioi 0)) :
    IntegrableOn (L2slice Φ) (Set.Ioc a b) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
  have hg : Integrable (fun s : ℝ => b * (L2slice Φ s / s)) (volume.restrict (Set.Ioc a b)) :=
    (hFint.mono_set hsub).integrable.const_mul b
  have hfm : AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioc a b)) :=
    hFm.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine hg.mono' hfm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := hsub hs
  have hdiv : 0 ≤ L2slice Φ s / s := div_nonneg (L2slice_nonneg Φ s) hs0.le
  rw [Real.norm_of_nonneg (L2slice_nonneg Φ s)]
  calc L2slice Φ s = (L2slice Φ s / s) * s := (div_mul_cancel₀ _ (ne_of_gt hs0)).symm
    _ ≤ (L2slice Φ s / s) * b := mul_le_mul_of_nonneg_left hs.2 hdiv
    _ = b * (L2slice Φ s / s) := by ring

/-- `L2slice Φ` is integrable on `(a,b]` when `s ↦ L2slice Φ s · s` is integrable on
`(0,∞)`: on `(a,b]` one has `L2slice Φ s = (L2slice Φ s · s)/s ≤ (…)/a`. -/
theorem integrableOn_L2slice_mul {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFm : AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioi 0)))
    (hFint : IntegrableOn (fun z : ℝ => L2slice Φ z * z) (Set.Ioi 0)) :
    IntegrableOn (L2slice Φ) (Set.Ioc a b) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
  have hg : Integrable (fun s : ℝ => (L2slice Φ s * s) / a) (volume.restrict (Set.Ioc a b)) :=
    (hFint.mono_set hsub).integrable.div_const a
  have hfm : AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioc a b)) :=
    hFm.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine hg.mono' hfm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := hsub hs
  have hnum : 0 ≤ L2slice Φ s * s := mul_nonneg (L2slice_nonneg Φ s) hs0.le
  rw [Real.norm_of_nonneg (L2slice_nonneg Φ s)]
  calc L2slice Φ s = (L2slice Φ s * s) / s := (mul_div_cancel_right₀ _ (ne_of_gt hs0)).symm
    _ ≤ (L2slice Φ s * s) / a := div_le_div_of_nonneg_left hnum ha (le_of_lt hs.1)

/-- The elementary `√(ab) ≤ (a+b)/2` for `a,b ≥ 0`. -/
theorem sqrt_mul_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha b]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.mul_self_sqrt ha,
    Real.mul_self_sqrt hb]

/-- The elementary AM–GM estimate `|ab| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul, ← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  linarith

/-! ## The one-dimensional Agmon input -/

/-- **Agmon's inequality in the radial variable.**  For every `x ≥ z₀ > 0`,

  `F z₀ ≤ F x + 2 ∫_{z₀}^{x} √(F s · G s)`,

where `F z = ∫_{Iθ} Φ z θ²` and `G z = ∫_{Iθ} Φ' z θ²`. -/
theorem key_ineq {Φ Φ' : ℝ → ℝ → ℝ} {z₀ x : ℝ} (hz₀ : 0 < z₀) (hz₀x : z₀ ≤ x)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0,
      HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z)
    (hFin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Φ z θ ^ 2) Work.Spaces.Iθ)
    (hGin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Φ' z θ ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0)) :
    L2slice Φ z₀ ≤ L2slice Φ x
      + 2 * ∫ s in z₀..x, Real.sqrt (L2slice Φ s * L2slice Φ' s) := by
  have hx : 0 < x := lt_of_lt_of_le hz₀ hz₀x
  have hFint' : IntegrableOn (fun z : ℝ => L2slice Φ z / z) (Set.Ioi 0) := by
    simpa only [L2slice] using hFint
  have hGint' : IntegrableOn (fun z : ℝ => L2slice Φ' z * z) (Set.Ioi 0) := by
    simpa only [L2slice] using hGint
  have hFml : AEStronglyMeasurable (L2slice Φ) (volume.restrict (Set.Ioi 0)) :=
    aesm_L2slice hcont
  have hGml : AEStronglyMeasurable (L2slice Φ') (volume.restrict (Set.Ioi 0)) :=
    aesm_L2slice hcont'
  have hFs : IntegrableOn (L2slice Φ) (Set.Ioc z₀ x) :=
    integrableOn_L2slice_div hz₀ hFml hFint'
  have hGs : IntegrableOn (L2slice Φ') (Set.Ioc z₀ x) :=
    integrableOn_L2slice_mul hz₀ hGml hGint'
  -- the dominating function `(F + G)/2` on `(z₀,x]`
  have hdom : Integrable (fun s : ℝ => (L2slice Φ s + L2slice Φ' s) / 2)
      (volume.restrict (Set.Ioc z₀ x)) := (hFs.integrable.add hGs.integrable).div_const 2
  -- a.e. in `θ`: the angular interval agrees with the open interval
  have hae_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    have hEq : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
    rw [hEq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- continuity of `|Φ · Φ'|` on the open quadrant
  have habs : ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 * Φ' p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hcont.mul hcont'
    exact h1.abs
  have hAEbox : AEStronglyMeasurable (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      ((volume.restrict (Set.Ioc z₀ x)).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_uncurry_box_Ioc (g := fun s θ => |Φ s θ * Φ' s θ|) hz₀ habs
  -- integrability in `θ` of the partial integral over `s` (Cauchy–Schwarz + AM–GM)
  have hIntS : IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|)
      (Set.Ioc z₀ x) := by
    refine hdom.mono' hAEbox.integral_prod_right' ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := lt_trans hz₀ hs.1
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    have hcs := SupZ.sliceCS (Φ := Φ) (Φ' := Φ') hs0 hcont hcont' (hFin s hs0) (hGin s hs0)
    have ham := sqrt_mul_le_half_add (L2slice_nonneg Φ s) (L2slice_nonneg Φ' s)
    simpa only [L2slice] using le_trans hcs ham
  -- the square root is integrable on `(z₀,x]` as well
  have hSQ : IntegrableOn (fun s : ℝ => Real.sqrt (L2slice Φ s * L2slice Φ' s))
      (Set.Ioc z₀ x) := by
    refine hdom.mono' ?_ ?_
    · have hsub' : Set.Ioc z₀ x ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_trans hz₀ hz.1
      have h1 : AEStronglyMeasurable (fun s : ℝ => L2slice Φ s * L2slice Φ' s)
          (volume.restrict (Set.Ioc z₀ x)) :=
        (hFml.mono_measure (Measure.restrict_mono hsub' le_rfl)).mul
          (hGml.mono_measure (Measure.restrict_mono hsub' le_rfl))
      exact h1.aemeasurable.sqrt.aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun s _ => ?_
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact sqrt_mul_le_half_add (L2slice_nonneg Φ s) (L2slice_nonneg Φ' s)
  have hFθ : Integrable (fun θ : ℝ => Φ z₀ θ ^ 2) (volume.restrict Work.Spaces.Iθ) := hFin z₀ hz₀
  have hFx : Integrable (fun θ : ℝ => Φ x θ ^ 2) (volume.restrict Work.Spaces.Iθ) := hFin x hx
  -- the `θ`-partial integrability of `|Φ Φ'|`, via Tonelli for the nonnegative integrand
  have hIntB : Integrable (fun θ : ℝ => ∫ s in z₀..x, |Φ s θ * Φ' s θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have hsliceAbs : ∀ᵐ s ∂(volume.restrict (Set.Ioc z₀ x)),
        Integrable (fun θ : ℝ => |Φ s θ * Φ' s θ|) (volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 < s := lt_trans hz₀ hs.1
      have hsm : AEStronglyMeasurable (fun θ : ℝ => Φ s θ) (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ) hcont hs0
      have hsm' : AEStronglyMeasurable (fun θ : ℝ => Φ' s θ) (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hcont' hs0
      refine ((hFin s hs0).add (hGin s hs0)).div_const 2 |>.mono'
        (hsm.mul hsm').aemeasurable.abs.aestronglyMeasurable ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => ?_
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact abs_mul_le_half_add_sq (Φ s θ) (Φ' s θ)
    obtain ⟨hprod, -⟩ := Work.Spaces.integrable_prod_of_iterated
      (μ := volume.restrict (Set.Ioc z₀ x)) (ν := volume.restrict Work.Spaces.Iθ)
      (G := fun s θ => |Φ s θ * Φ' s θ|) (fun s θ => abs_nonneg _) hAEbox hsliceAbs
      hIntS.integrable
    refine (hprod.swap.integral_prod_left).congr ?_
    filter_upwards with θ
    exact (intervalIntegral.integral_of_le hz₀x).symm
  -- the swap of the two integrations (delegated: `SupZ.swap_abs`)
  have hswap : (∫ θ in Work.Spaces.Iθ, ∫ s in z₀..x, |Φ s θ * Φ' s θ|)
      = ∫ s in z₀..x, ∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ| :=
    SupZ.swap_abs hz₀ hz₀x hcont hcont' hFin hGin hFint hGint
  have hsub : L2slice Φ z₀ - L2slice Φ x = ∫ θ in Work.Spaces.Iθ, (Φ z₀ θ ^ 2 - Φ x θ ^ 2) := by
    rw [L2slice, L2slice]
    exact (MeasureTheory.integral_sub hFθ hFx).symm
  have hmono : (∫ θ in Work.Spaces.Iθ, (Φ z₀ θ ^ 2 - Φ x θ ^ 2))
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * ∫ s in z₀..x, |Φ s θ * Φ' s θ|) := by
    refine MeasureTheory.integral_mono_ae (hFθ.sub hFx) (hIntB.const_mul 2) ?_
    filter_upwards [hae_Ioo] with θ hθ
    exact slice_abs_le_ftc hθ hz₀ hz₀x hcont hcont' fun z hz => hderiv θ hθ z hz
  have htwo : (∫ θ in Work.Spaces.Iθ, (2 * ∫ s in z₀..x, |Φ s θ * Φ' s θ|))
      = 2 * ∫ θ in Work.Spaces.Iθ, (∫ s in z₀..x, |Φ s θ * Φ' s θ|) :=
    MeasureTheory.integral_const_mul 2 _
  have hfour : (∫ s in z₀..x, (∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|))
      ≤ ∫ s in z₀..x, Real.sqrt (L2slice Φ s * L2slice Φ' s) := by
    rw [intervalIntegral.integral_of_le hz₀x, intervalIntegral.integral_of_le hz₀x]
    refine MeasureTheory.setIntegral_mono_on hIntS hSQ measurableSet_Ioc fun s hs => ?_
    exact SupZ.sliceCS (lt_trans hz₀ hs.1) hcont hcont'
      (hFin s (lt_trans hz₀ hs.1)) (hGin s (lt_trans hz₀ hs.1))
  linarith [hsub, hmono, htwo, hswap, hfour]

/-! ## The target -/

theorem SupOpenH2Z {Φ Φ' : ℝ → ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hΦcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0,
      HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z)
    (hFin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Φ z θ ^ 2) Work.Spaces.Iθ)
    (hGin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Φ' z θ ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0)) :
    (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2)
      ≤ 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
        + (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) := by
  have hkey : ∀ x ∈ Set.Ioi z₀, L2slice Φ z₀ ≤ L2slice Φ x
      + 2 * ∫ s in z₀..x, Real.sqrt (L2slice Φ s * L2slice Φ' s) :=
    fun x hx => key_ineq hz₀ (le_of_lt hx) hΦcont hΦcont' hderiv hFin hGin hFint hGint
  have hmain := Work.FTS.StrongPersist.SupZ.weightedAgmonAbstract hz₀
    (aesm_L2slice hΦcont) (aesm_L2slice hΦcont')
    (fun z _ => L2slice_nonneg Φ z) (fun z _ => L2slice_nonneg Φ' z)
    (by simpa only [L2slice] using hFint) (by simpa only [L2slice] using hGint) hkey
  simpa only [L2slice] using hmain

end Work.FTS.StrongPersist
end
end
