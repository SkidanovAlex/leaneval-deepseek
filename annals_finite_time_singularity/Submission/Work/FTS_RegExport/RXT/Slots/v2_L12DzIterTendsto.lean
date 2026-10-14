import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Slots
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.L12Add
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTAux1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c (sKer Qext)

/-! ## Elementary integral conversions -/

theorem intervalIntegral_Iθ_eq (f : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(Real.pi / 2), f s) = ∫ s in Iθ, f s := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm

theorem integrableOn_uIoc_of_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn f (Set.Icc a b)) : IntegrableOn f (Set.uIoc a b) := by
  rw [Set.uIoc_of_le hab]
  exact h.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc


/-- A kernel supported in `(-δ, δ)` reduces the whole-line integral to `[a,b]`. -/
theorem full_eq_interval_zmoll (K : ℝ → ℝ) (R : ℝ → ℝ) {δ σ a b : ℝ} (hδ0 : 0 ≤ δ)
    (hvan : ∀ x : ℝ, δ < |x| → K x = 0) (ha : a ≤ σ - δ) (hb : σ + δ ≤ b) :
    (∫ t : ℝ, K (σ - t) * R t) = ∫ t in a..b, K (σ - t) * R t := by
  have hab : a ≤ b := le_trans ha (by linarith)
  have hzero' : ∀ t : ℝ, t ∉ Set.Icc a b → K (σ - t) * R t = 0 := by
    intro t ht
    rw [Set.mem_Icc, not_and_or] at ht
    have h : δ < |σ - t| := by
      rcases ht with h | h
      · rw [not_le] at h
        rw [abs_of_pos (by linarith)]
        linarith
      · rw [not_le] at h
        rw [abs_of_neg (by linarith)]
        linarith
    rw [hvan _ h, zero_mul]
  have h1 : (∫ t : ℝ, K (σ - t) * R t) = ∫ t in Set.Icc a b, K (σ - t) * R t := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun t : ℝ => K (σ - t) * R t) (s := Set.Icc a b)]
    exact fun t ht => hzero' t ht
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- A function continuous on the open angular quadrant is jointly measurable, so its angular
integral is a.e. strongly measurable in the radial variable. -/
theorem aesm_param_Iθ (Y : ℝ × ℝ → ℝ)
    (hY : ContinuousOn Y (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable (fun t : ℝ => ∫ s in Iθ, Y (t, s)) volume := by
  have h1 : AEStronglyMeasurable Y
      ((volume : Measure ℝ).prod (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
    have h2 : AEStronglyMeasurable Y
        (((volume : Measure ℝ).prod volume).restrict
          (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hY.aestronglyMeasurable (μ := volume) (MeasurableSet.univ.prod measurableSet_Ioo)
    rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ] at h2
    exact h2
  have h3 := h1.integral_prod_right'
  refine h3.congr ?_
  filter_upwards with t
  exact (MeasureTheory.setIntegral_congr_set (f := fun s => Y (t, s))
    (μ := volume) MeasureTheory.Ioo_ae_eq_Icc)

/-- A product of something tending to `0` with something eventually bounded tends to `0`. -/
theorem tendsto_mul_zero {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ}
    (hf : Tendsto f l (𝓝 0)) (hg : ∀ᶠ s in l, |g s| ≤ c) :
    Tendsto (fun s => f s * g s) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  refine squeeze_zero' (g := fun s => ‖f s‖ * max c 0)
    (Filter.Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
  · filter_upwards [hg] with s hs
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans hs (le_max_left _ _)) (abs_nonneg _)
  · have h := hf.mul_const (max c 0)
    simpa using h

/-! ## Differentiating the folded angular integral in `θ` -/

theorem inner_hasDerivAt {K K' : ℝ → ℝ → ℝ} {C : ℝ} {G : ℝ → ℝ → ℝ} {w θ : ℝ}
    (hKc : ∀ x : ℝ, Continuous (fun s : ℝ => K x s))
    (hK'c : ∀ x : ℝ, Continuous (fun s : ℝ => K' x s))
    (hbound : ∀ x s : ℝ, |K' x s| ≤ C)
    (hKdiff : ∀ x s : ℝ, HasDerivAt (fun y : ℝ => K y s) (K' x s) x)
    (hGc : ContinuousOn (fun s : ℝ => G w s) Iθ) :
    HasDerivAt (fun x : ℝ => ∫ s in Iθ, K x s * G w s)
      (∫ s in Iθ, K' θ s * G w s) θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hGcIcc : ContinuousOn (fun s : ℝ => G w s) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    rw [Set.uIcc_of_le hle]; exact hGc
  have hGaesm : AEStronglyMeasurable (fun s : ℝ => G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) := by
    rw [Set.uIoc_of_le hle]
    exact (hGc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hGabs : ContinuousOn (fun s : ℝ => |G w s|) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := hGcIcc.abs
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable (fun s : ℝ => K x s * G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    Filter.Eventually.of_forall fun x => (hKc x).aestronglyMeasurable.restrict.mul hGaesm
  have hF_int : IntervalIntegrable (fun s : ℝ => K θ s * G w s) volume 0 (Real.pi / 2) :=
    ((hKc θ).continuousOn.mul hGcIcc).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ => K' θ s * G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    (hK'c θ).aestronglyMeasurable.restrict.mul hGaesm
  have hbound_ae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ x ∈ (Set.univ : Set ℝ), ‖K' x s * G w s‖ ≤ C * |G w s| := by
    refine Filter.Eventually.of_forall fun s _ x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x s) (abs_nonneg _)
  have hbound_int : IntervalIntegrable (fun s : ℝ => C * |G w s|) volume 0 (Real.pi / 2) :=
    (hGabs.const_mul C).intervalIntegrable
  have hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => K y s * G w s) (K' x s * G w s) x := by
    refine Filter.Eventually.of_forall fun s _ x _ => ?_
    exact (hKdiff x s).mul_const _
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := Real.pi / 2) (bound := fun s : ℝ => C * |G w s|)
    (F := fun x s : ℝ => K x s * G w s) (F' := fun x s : ℝ => K' x s * G w s)
    (x₀ := θ) (s := Set.univ) Filter.univ_mem hF_meas hF_int hF'_meas hbound_ae hbound_int hdiff
  have hfun : (fun x : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2), K x s * G w s)
      = fun x : ℝ => ∫ s in Iθ, K x s * G w s :=
    funext fun x => intervalIntegral_Iθ_eq _
  have hval : (∫ s in (0 : ℝ)..(Real.pi / 2), K' θ s * G w s) = ∫ s in Iθ, K' θ s * G w s :=
    intervalIntegral_Iθ_eq _
  rw [hfun, hval] at hmain
  exact hmain

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# The *uniform* radial product bound for `HkIntegrand` (row 24, radial piece)

`hkIntegrand_prod_le_rad_uniform` is the pointwise `ℋ⁴`-integrand bound for the product
`R(z)·h(z,θ)` of a *radial* function with a general function, with a constant that is
**universal**: it does not depend on `α` or on the radial size `M`:

  `HkIntegrand α 4 (R·h) z θ ≤ C · (M · HkIntegrand α 4 h z θ
     + (D_z^4 R)² w(z)² σ(θ) · Qg h θ)`,

where `M` bounds `(D_z^b R)²` for `b ≤ 3` and `Qg h θ = ∫_z (D_z h(z,θ))² w(z)² dz`.
The third hypothesis `hQh` is the radial Hardy bound `(h z θ)² ≤ Qg h θ`, which is what
lets the single slot `b = 4` of the Leibniz expansion be absorbed into the second
summand (that slot is only non-vacuous in the term `D_z^4(R·h)`, where `D_z^4 R` multiplies
`h` itself).

The proof is the Cauchy–Schwarz computation: expand the two Leibniz sums supplied as
hypotheses, apply `(∑ F_b)² ≤ card · ∑ F_b²`, and bound every summand either by
`M · HkIntegrand α 4 h` (all slots with `b ≤ 3`) or — for the single slot `b = 4` — by
`(D_z^4 R)² w² σ · Qg h` via `hQh` and `light_sq`.  No smoothness of `R` or `h` is used,
so the argument applies to the concrete nonlinear data.

The three slot lemmas below are the computation of the sibling
`RNP24/hkIntegrand_prod_le_rad` (whose explicit witness is already independent of `α` and
`M`); they are reproduced here so that the present module is self-contained and its
`C = 4194304` is manifest.  (The module deliberately imports only `radial_prod`: nothing
from `Pieces.Ctx` is used by the statement or the proof.)
-/


/-! ## The three slot estimates -/

/-- **One pure `D_z`-slot of the product, `i ≤ 3`.**  Every radial derivative has order
`b ≤ 3`, hence is controlled by `M`. -/
private theorem light_slot_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
    {i : ℕ} (hi : i ≤ 3) {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z) :
    (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ := by
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hDz' := hDz i (by omega) z hzI θ hθ
  set F : ℕ → ℝ := fun b => (i.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z
        * (Work.Spaces.DzIter (i - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))) with hF
  have hkey : Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))
      = ∑ b ∈ Finset.range (i+1), F b := by
    rw [hDz', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i+1)) (f := F)
  have hcard : ((Finset.range (i+1)).card : ℝ) = (i:ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcard5 : ((Finset.range (i+1)).card : ℝ) ≤ 5 := by
    rw [hcard]; exact_mod_cast (by omega : i + 1 ≤ 5)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hterm : ∀ b ∈ Finset.range (i+1),
      F b ^ 2 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbi hi
    have hib : i - b ≤ 4 := by omega
    have h1 : ((i.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := i) (b := b) (by omega)
      have h0 : (0:ℝ) ≤ ((i.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
    have h3 : (Work.Spaces.DzIter (i-b) h z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
        ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ (i-b) hib
    have hprod : (Work.Elliptic.DzdIter b R z)^2
          * (Work.Spaces.DzIter (i-b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
        ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 : ((i.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (i-b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2)
        ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
      mul_le_mul h1 hprod (by positivity) (by norm_num)
    rw [hF]
    have hgoal : ((i.choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.DzIter (i - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))))) ^ 2
        = ((i.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (i-b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (i+1), F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
    calc (∑ b ∈ Finset.range (i+1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (i+1), (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (i+1)).card : ℝ)
            * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          have h0 : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard5 h0
  nlinarith [hcs, hcard5, hsum, hM0, hHnn]

/-- **The top pure `D_z`-slot of the product, `i = 4`.**  The summand in which all four
`D_z`-derivatives fall on `R` pairs `D_z^4 R` with `h` itself, which is controlled by the
radial Hardy bound `(h z θ)² ≤ Qg h θ` supplied by the caller. -/
private theorem light_slot_four_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z)
    (hQh : ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ) :
    (Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ
        + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
  have hsin : 0 < Real.sin (2*θ) := Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hθ
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hDz4 := hDz 4 (by norm_num) z hzI θ hθ
  set F : ℕ → ℝ := fun b => ((4:ℕ).choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z
        * (Work.Spaces.DzIter (4 - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))) with hF
  have hkey : Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))
      = ∑ b ∈ Finset.range 5, F b := by
    rw [hDz4, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range 5) (f := F)
  have hcard : ((Finset.range 5).card : ℝ) = 5 := by rw [Finset.card_range]; norm_num
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg
      (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hQgnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ :=
    Work.FTS.Nonlinear.RadialProd.Qg_nonneg h θ
  have hSnn : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
      * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    have h1 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg (mul_nonneg h1 hsmEnn) hQgnn
  have hterm : ∀ b ∈ Finset.range 5, F b ^ 2
      ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
    intro b hb
    have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : (((4:ℕ).choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := 4) (b := b) (by norm_num)
      have h0 : (0:ℝ) ≤ (((4:ℕ).choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    rw [hF]
    have hgoal : (((4:ℕ).choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.DzIter (4 - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))))) ^ 2
        = (((4:ℕ).choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (4 - b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2) := by ring
    rw [hgoal]
    rcases (by omega : b ≤ 3 ∨ b = 4) with hb3 | hb4'
    · have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
      have h3 : (Work.Spaces.DzIter (4 - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ (4 - b) (by omega)
      have hprod : (Work.Elliptic.DzdIter b R z)^2
            * (Work.Spaces.DzIter (4 - b) h z θ
                * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
        mul_le_mul h2 h3 (sq_nonneg _) hM0
      have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hsecond : 0 ≤ 256 * ((Work.Elliptic.DzdIter 4 R z)^2
          * (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg h θ) :=
        mul_nonneg (by norm_num) hSnn
      linarith [hprod2, hsecond]
    · subst hb4'
      have h3 : (Work.Spaces.DzIter (4 - 4) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          = (h z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2 := by
        norm_num
      have hls : (h z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          = (h z θ)^2 * (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
        Work.FTS.Nonlinear.RadialProd.light_sq (h z θ) z θ hsin
      have hQg' : (h z θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ := hQh z hzI
      have hw : 0 ≤ (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
        mul_nonneg (sq_nonneg _) hsmEnn
      have hkey4 : (Work.Elliptic.DzdIter 4 R z)^2
            * (Work.Spaces.DzIter (4 - 4) h z θ
                * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
              * Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
        have hI4 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 := sq_nonneg _
        rw [h3, hls]
        have hstep : (h z θ)^2 * ((Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ
              * ((Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ) :=
          mul_le_mul_of_nonneg_right hQg' hw
        have hstep2 := mul_le_mul_of_nonneg_left hstep hI4
        nlinarith [hstep2]
      have hprod2 := mul_le_mul h1 hkey4 (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hfirst : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
        mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
      linarith [hprod2, hfirst]
  have hsum : (∑ b ∈ Finset.range 5, F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by
    calc (∑ b ∈ Finset.range 5, F b ^ 2)
        ≤ ∑ _b ∈ Finset.range 5, (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := Finset.sum_le_sum hterm
      _ = ((Finset.range 5).card : ℝ) * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by rw [hcard]
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  nlinarith [hcs, hcard, hsum, hMHnn, hSnn]

/-- **One mixed slot of the product.**  Since `i ≥ 1`, `j ≤ 3` and every radial derivative
in the Leibniz sum has order `b ≤ j ≤ 3`, so `M` controls all of them. -/
private theorem heavy_slot_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z) :
    (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ)^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ := by
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hj3 : j ≤ 3 := by omega
  have hMx' := hMx i j hi hij z hzI θ hθ
  set F : ℕ → ℝ := fun b => (j.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z * (Work.Spaces.mixed (j - b) i h z θ
        * Work.Spaces.Wt α z θ)) with hF
  have hkey : Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), F b := by
    rw [hMx', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := F)
  have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 5 := by
    rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 5)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hterm : ∀ b ∈ Finset.range (j + 1),
      F b ^ 2 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbj hj3
    have h1 : ((j.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := j) (b := b) (by omega)
      have h0 : (0:ℝ) ≤ ((j.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
    have h3 : (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2
        ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ i (j - b) hi (by omega)
    have hprod : (Work.Elliptic.DzdIter b R z)^2
          * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2
        ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
    rw [hF]
    have hgoal : ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ))) ^ 2
        = ((j.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (j + 1), F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (j + 1)).card : ℝ)
            * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          have h0 : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard h0
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  nlinarith [hcs, hcard, hsum, hMHnn]

/-- **The uniform radial product bound.**  There is a universal constant `C` (independent
of `α` and of the radial bound `M`) with the pointwise `ℋ⁴`-integrand estimate for
`R(z)·h(z,θ)`. -/
theorem hkIntegrand_prod_le_rad_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {α M : ℝ}, 0 ≤ M → ∀ {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
      (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
      (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
      (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ))
      {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z)
      (hQh : ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ),
      Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
        ≤ C * (M * Work.Spaces.HkIntegrand α 4 h z θ
            + (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
              * Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
  refine ⟨4194304, by norm_num, ?_⟩
  intro α M hM0 R h hM hDz hMx θ z hθ hz hQh
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg
      (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hQgnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ :=
    Work.FTS.Nonlinear.RadialProd.Qg_nonneg h θ
  have hSnn : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
      * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    have h1 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg (mul_nonneg h1 hsmEnn) hQgnn
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  rw [Work.Spaces.HkIntegrand]
  -- the pure `D_z`-sum
  have hZ : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
      ≤ 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
          * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    rw [Finset.sum_range_succ (fun i => (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2) 4]
    have hlow : (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
        ≤ 4 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
      calc (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 4, (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            Finset.sum_le_sum fun i hi => light_slot_le_M hM0 hM hDz
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hθ hz
        _ = 4 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have htop : (Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2
        ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ
          + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ :=
      light_slot_four_le_M hM0 hM hDz hθ hz hQh
    linarith [hlow, htop, hSnn, hMHnn]
  -- the mixed sum
  have hMsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 25 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    have hinner : ∀ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
      intro i hi
      calc (∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
          ≤ ∑ _j ∈ Finset.range 5, (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [ite_eq_left hc]
              exact heavy_slot_le_M hM0 hM hMx hc.1 hc.2 hθ hz
            · rw [ite_eq_right hc]
              exact mul_nonneg (mul_nonneg (by norm_num) hM0) hHnn
        _ = 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range 5, (5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hinner
      _ = 25 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  nlinarith [hZ, hMsum, hMHnn, hSnn]

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A *uniform in `α`* angular mass bound for the `Γ²`-weight of the nonlinear estimates

The lemma of this file is the angular mass estimate

`∫_{Iθ} Γ(θ)² (α + sin 2θ)² sin(2θ)^{-γ(α)} dθ ≤ M`  for all `0 < α ≤ 1`,

with `Γ(θ) = (sin θ cos²θ)^{α/3}`, `γ(α) = 1 + α/10` (`Work.Spaces.Gam`, `Work.Spaces.gam`)
and the angular weight `sin(2θ)^{-γ} = Work.FTS.Nonlinear.RadialProd.smG α`.

## Why the extra factor `(α + sin 2θ)²` is what makes the constant uniform

The companion estimate `Work.FTS.LocData.angMaj_mem` gives only the `α`-dependent bound

`∫_{Iθ} Γ² sin(2θ)^{-γ} ≤ 3000/(17α)`,

which *diverges* as `α ↓ 0` (near `θ = 0` the integrand is `θ^{17α/30-1}`).  The factor
`(α + sin 2θ)²` of this file vanishes quadratically where `sin 2θ ≪ α`, exactly cancelling
the divergence: with `X = sin 2θ` and `s = 17α/30 - 1 = 2α/3 - γ(α) ∈ (-1,0]`,

* `GamSq_sin_neg_gam_le` gives `Γ² X^{-γ} ≤ 2^{-2α/3} X^s`, hence
* `Γ² (α+X)² X^{-γ} ≤ X^s (α+X)² = α² X^s + 2α X^{s+1} + X^{s+2} ≤ α² X^s + 2α + 1`,
* and `∫_{Iθ} X^s ≤ 3000/(17α)` (`Work.Spaces.sin_two_rpow`) so that the dangerous term
  contributes `α²·3000/(17α) = 3000α/17 ≤ 3000/17`.

The numerical constant `M = 1000` is generous: the sum is at most `3000/17 + 6 ≤ 206`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

/-! ## The pointwise domination

`Γ²(α+X)²X^{-γ} ≤ α²X^{17α/30-1} + 2α + 1`, where `X = sin 2θ`.  The `α²` in front of the
singular term `X^{s}` is what makes the subsequent integral uniform in `α`. -/
theorem gamWeightPt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1) := by
  set X : ℝ := Real.sin (2 * θ) with hXdef
  set s : ℝ := 17 * α / 30 - 1 with hsdef
  have hX0 : 0 ≤ X := by
    rw [hXdef, Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
  have hX1 : X ≤ 1 := by rw [hXdef]; exact Real.sin_le_one _
  have hs1 : 0 ≤ s + 1 := by rw [hsdef]; linarith
  have hne1 : s + 1 ≠ 0 := by rw [hsdef]; linarith
  have hb2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
  -- the companion bound `Γ² X^{-γ} ≤ 2^{-2α/3} X^s`
  have hbase : Work.Spaces.Gam α θ ^ 2 * X ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * X ^ s := by
    rw [hXdef, hsdef]
    exact Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hXs : 0 ≤ X ^ s := Real.rpow_nonneg hX0 s
  -- `X^s X ≤ 1`, `(X^s X) X ≤ 1`
  have hA : X ^ (s + 1) = X ^ s * X := by
    rw [Real.rpow_add' hX0 hne1, Real.rpow_one X]
  have h1 : X ^ s * X ≤ 1 := by rw [← hA]; exact Real.rpow_le_one hX0 hX1 hs1
  have h3 : (X ^ s * X) * X ≤ 1 := by
    have := mul_le_mul h1 hX1 hX0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  -- the `X`-part of the bound
  have hkey : X ^ s * (α + X) ^ 2 ≤ α ^ 2 * X ^ s + (2 * α + 1) := by
    have e1 : (2 * α) * (X ^ s * X) ≤ (2 * α) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have e0 : X ^ s * (α + X) ^ 2
        = α ^ 2 * X ^ s + (2 * α) * (X ^ s * X) + (X ^ s * X) * X := by ring
    rw [e0]
    linarith
  -- assemble
  have hstep1 : Work.Spaces.Gam α θ ^ 2 * (α + X) ^ 2 * X ^ (-(Work.Spaces.gam α))
      ≤ (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2 := by
    calc Work.Spaces.Gam α θ ^ 2 * (α + X) ^ 2 * X ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.Gam α θ ^ 2 * X ^ (-(Work.Spaces.gam α))) * (α + X) ^ 2 := by ring
      _ ≤ (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2 :=
          mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
  have hstep2 : (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2
      ≤ α ^ 2 * X ^ s + (2 * α + 1) := by
    have hpos : 0 ≤ X ^ s * (α + X) ^ 2 := mul_nonneg hXs (sq_nonneg _)
    calc (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2
        = 2 ^ (-(2 * α / 3)) * (X ^ s * (α + X) ^ 2) := by ring
      _ ≤ X ^ s * (α + X) ^ 2 := mul_le_of_le_one_left hpos hb2
      _ ≤ α ^ 2 * X ^ s + (2 * α + 1) := hkey
  exact le_trans hstep1 hstep2

/-! ## The integral of the dominating function

`∫_{Iθ} (α² sin(2θ)^{17α/30-1} + (2α+1)) ≤ 1000`: the singular part contributes
`α²·3000/(17α) = 3000α/17 ≤ 3000/17`, the constant contributes `(2α+1)π/2 ≤ 6`. -/
theorem gamWeightDom (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1)) ≤ 1000 := by
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1)
    (by linarith) (by linarith)
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hf1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) Work.Spaces.Iθ :=
    hIntS.const_mul _
  have hf2 : MeasureTheory.IntegrableOn (fun _ : ℝ => (2 * α + 1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (2 * α + 1))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol2 : ∫ θ in Work.Spaces.Iθ, (2 * α + 1 : ℝ) = (2 * α + 1) * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
    ring
  constructor
  · exact hf1.add hf2
  · have hsum : ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1)
        = α ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
          + (2 * α + 1) * (Real.pi / 2) := by
      rw [MeasureTheory.integral_add hf1 hf2, MeasureTheory.integral_const_mul, hvol2]
    rw [hsum]
    have h1 : α ^ 2 * (3000 / (17 * α)) ≤ 200 := by
      have he : α ^ 2 * (3000 / (17 * α)) = 3000 * α / 17 := by field_simp
      rw [he]
      nlinarith [hα1]
    have h2 : (2 * α + 1) * (Real.pi / 2) ≤ 6 := by
      have hp : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
      have ha : 2 * α + 1 ≤ 3 := by linarith
      have h0 : (0 : ℝ) ≤ 2 * α + 1 := by linarith
      nlinarith [mul_le_mul ha hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
        (by norm_num : (0 : ℝ) ≤ 3)]
    have hmb : α ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        ≤ α ^ 2 * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hBdS' (sq_nonneg α)
    linarith

/-! ## The main lemma -/

theorem gamWeightInt :
    ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ M := by
  refine ⟨1000, by norm_num, fun α hα hα1 => ?_⟩
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hdom := gamWeightDom α hα hα1
  -- the a.e. pointwise domination
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    rw [Work.FTS.Nonlinear.RadialProd.smG]
    exact gamWeightPt α hα hα1 hθ
  -- measurability of the integrand
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam, Work.FTS.Nonlinear.RadialProd.smG]
    fun_prop
  have hfint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ :=
    hdom.1.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Work.FTS.Nonlinear.RadialProd.smG_nonneg h2))]
      exact h1)
  exact ⟨hfint, le_trans (MeasureTheory.integral_mono_ae hfint hdom.1 hpt) hdom.2⟩

end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The radial profile `hKer²` of row 23, in `ℋ⁴` -/

/-- The radial profile `hKer(z)² = z²/(1+z)⁴` of row 23. -/
private noncomputable def hk2 (z : ℝ) : ℝ := (Work.Spaces.hKer z) ^ 2

private lemma hk2_apply (z : ℝ) : hk2 z = z ^ 2 / (1 + z) ^ 4 := by
  rw [hk2, Work.Spaces.hKer_apply, div_pow]
  congr 1
  ring

/-! ### The polynomial numerators of the `D_z`-iterates -/

private noncomputable def q1 : ℝ → ℝ := fun z => 2 - 2 * z
private noncomputable def q2 : ℝ → ℝ := fun z => 4 - 12 * z + 4 * z ^ 2
private noncomputable def q3 : ℝ → ℝ := fun z => 8 - 52 * z + 52 * z ^ 2 - 8 * z ^ 3
private noncomputable def q4 : ℝ → ℝ :=
  fun z => 16 - 196 * z + 416 * z ^ 2 - 196 * z ^ 3 + 16 * z ^ 4

/-- The closed forms of the `D_z`-iterates of `hKer²`:
`D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`, with `q_0 = 1`. -/
private noncomputable def gfun : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 4
  | 1 => fun z => z ^ 2 * q1 z / (1 + z) ^ 5
  | 2 => fun z => z ^ 2 * q2 z / (1 + z) ^ 6
  | 3 => fun z => z ^ 2 * q3 z / (1 + z) ^ 7
  | _ => fun z => z ^ 2 * q4 z / (1 + z) ^ 8

private lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z ((hasDerivAt_id z).const_add 1)
  convert h using 1
  all_goals first
    | (funext w; simp only [Function.comp_apply, id_eq])
    | ring

private lemma hasDerivAt_q1 (z : ℝ) : HasDerivAt q1 (-2) z := by
  have h := ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub ((hasDerivAt_id z).const_mul 2))
  convert h using 1
  all_goals first
    | (funext w; simp only [q1, Pi.sub_apply, Pi.mul_apply, id_eq])
    | ring

private lemma hasDerivAt_q2 (z : ℝ) : HasDerivAt q2 (8 * z - 12) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h := (((hasDerivAt_const (x := z) (c := (4 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 12)).add (h1.const_mul 4))
  convert h using 1
  all_goals first
    | (funext w; simp only [q2, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q3 (z : ℝ) : HasDerivAt q3 (-24 * z ^ 2 + 104 * z - 52) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have h := ((((hasDerivAt_const (x := z) (c := (8 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 52)).add (h1.const_mul 52)).sub (h2.const_mul 8))
  convert h using 1
  all_goals first
    | (funext w; simp only [q3, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q4 (z : ℝ) :
    HasDerivAt q4 (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by simpa using hasDerivAt_pow 4 z
  have h := (((((hasDerivAt_const (x := z) (c := (16 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 196)).add (h1.const_mul 416)).sub (h2.const_mul 196)).add
      (h3.const_mul 16))
  convert h using 1
  all_goals first
    | (funext w; simp only [q4, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma deriv_g0_val (z : ℝ) (hz : 0 < z) :
    ((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2
      = z * q1 z / (1 + z) ^ 5 := by
  rw [q1]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g1_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1)))
        / ((1 + z) ^ 5) ^ 2
      = z * q2 z / (1 + z) ^ 6 := by
  rw [q1, q2]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g2_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1)))
        / ((1 + z) ^ 6) ^ 2
      = z * q3 z / (1 + z) ^ 7 := by
  rw [q2, q3]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g3_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1)))
        / ((1 + z) ^ 7) ^ 2
      = z * q4 z / (1 + z) ^ 8 := by
  rw [q3, q4]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma hasDerivAt_g0 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4) (z * q1 z / (1 + z) ^ 5) z := by
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4)
      (((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2) z :=
    hnum.div (hasDerivAt_one_add_pow 4 z) (by positivity)
  rw [deriv_g0_val z hz] at h
  exact h

private lemma hasDerivAt_g1 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5) (z * q2 z / (1 + z) ^ 6) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5)
      (((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1))) / ((1 + z) ^ 5) ^ 2) z :=
    (hp.mul (hasDerivAt_q1 z)).div (hasDerivAt_one_add_pow 5 z) (by positivity)
  rw [deriv_g1_val z hz] at h
  exact h

private lemma hasDerivAt_g2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6) (z * q3 z / (1 + z) ^ 7) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6)
      (((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1))) / ((1 + z) ^ 6) ^ 2) z :=
    (hp.mul (hasDerivAt_q2 z)).div (hasDerivAt_one_add_pow 6 z) (by positivity)
  rw [deriv_g2_val z hz] at h
  exact h

private lemma hasDerivAt_g3 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7) (z * q4 z / (1 + z) ^ 8) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7)
      (((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1))) / ((1 + z) ^ 7) ^ 2) z :=
    (hp.mul (hasDerivAt_q3 z)).div (hasDerivAt_one_add_pow 7 z) (by positivity)
  rw [deriv_g3_val z hz] at h
  exact h


private lemma dzStep1 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 1) (z * q2 z / (1 + z) ^ 6) z :=
  hasDerivAt_g1 hz

private lemma dzStep2 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 2) (z * q3 z / (1 + z) ^ 7) z :=
  hasDerivAt_g2 hz

private lemma dzStep3 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 3) (z * q4 z / (1 + z) ^ 8) z :=
  hasDerivAt_g3 hz

/-! ### The closed forms of the `D_z`-iterates -/

private lemma dz0 : Set.EqOn (Work.Elliptic.DzdIter 0 hk2) (gfun 0) (Set.Ioi 0) := by
  intro z hz
  show hk2 z = z ^ 2 / (1 + z) ^ 4
  exact hk2_apply z

private lemma dz1 : Set.EqOn (Work.Elliptic.DzdIter 1 hk2) (gfun 1) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 0 hk2) z = z ^ 2 * q1 z / (1 + z) ^ 5
  rw [show Work.Elliptic.DzdIter 0 hk2 = hk2 from rfl,
    (Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall hk2_apply)),
    (hasDerivAt_g0 hz).deriv]
  ring

private lemma dz2 : Set.EqOn (Work.Elliptic.DzdIter 2 hk2) (gfun 2) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 1 hk2) z = z ^ 2 * q2 z / (1 + z) ^ 6
  rw [show deriv (Work.Elliptic.DzdIter 1 hk2) z = deriv (gfun 1) z from
      (dz1.deriv isOpen_Ioi) hz,
    (dzStep1 hz).deriv]
  ring

private lemma dz3 : Set.EqOn (Work.Elliptic.DzdIter 3 hk2) (gfun 3) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 2 hk2) z = z ^ 2 * q3 z / (1 + z) ^ 7
  rw [show deriv (Work.Elliptic.DzdIter 2 hk2) z = deriv (gfun 2) z from
      (dz2.deriv isOpen_Ioi) hz,
    (dzStep2 hz).deriv]
  ring

private lemma dz4 : Set.EqOn (Work.Elliptic.DzdIter 4 hk2) (gfun 4) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 3 hk2) z = z ^ 2 * q4 z / (1 + z) ^ 8
  rw [show deriv (Work.Elliptic.DzdIter 3 hk2) z = deriv (gfun 3) z from
      (dz3.deriv isOpen_Ioi) hz,
    (dzStep3 hz).deriv]
  ring

private lemma dzIter_hk2_eqOn (i : ℕ) (hi : i ≤ 4) :
    Set.EqOn (Work.Elliptic.DzdIter i hk2) (gfun i) (Set.Ioi 0) := by
  interval_cases i
  · exact dz0
  · exact dz1
  · exact dz2
  · exact dz3
  · exact dz4

/-! ### The coefficient bounds -/

private lemma q1_le (z : ℝ) (hz : 0 ≤ z) : |q1 z| ≤ 2 * (1 + z) := by
  rw [q1, abs_le]
  constructor <;> linarith

private lemma q2_le (z : ℝ) (hz : 0 ≤ z) : |q2 z| ≤ 12 * (1 + z) ^ 2 := by
  rw [q2, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz]

private lemma q3_le (z : ℝ) (hz : 0 ≤ z) : |q3 z| ≤ 52 * (1 + z) ^ 3 := by
  rw [q3, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

private lemma q4_le (z : ℝ) (hz : 0 ≤ z) : |q4 z| ≤ 416 * (1 + z) ^ 4 := by
  rw [q4, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

/-- The radial density of `ℋ⁴` of `hKer²`: `Rint hKer² z ≤ 865280/(1+z)^4`. -/
private lemma Rint_hk2_le {z : ℝ} (hz : 0 < z) :
    Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 / (1 + z) ^ 4 := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h1z : 0 < 1 + z := by linarith
  have hterm : ∀ i ∈ Finset.range 5,
      (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 173056 / (1 + z) ^ 4 := by
    intro i hi
    have hi4 : i ≤ 4 := by
      have := Finset.mem_range.mp hi
      omega
    have heq := dzIter_hk2_eqOn i hi4 hz
    rw [heq]
    interval_cases i
    · -- i = 0
      show (z ^ 2 / (1 + z) ^ 4) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2 ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 / (1 + z) ^ 4) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = 1 / (1 + z) ^ 4 := by
        field_simp
        try ring
      rw [hn]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1z]
    · -- i = 1
      show (z ^ 2 * q1 z / (1 + z) ^ 5) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q1 z / (1 + z) ^ 5) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q1 z) ^ 2 / (1 + z) ^ 6 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q1 z) ^ 2 ≤ (2 * (1 + z)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q1 z)) (q1_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q1 z) ^ 2 / (1 + z) ^ 6 ≤ (2 * (1 + z)) ^ 2 / (1 + z) ^ 6 := by gcongr
        _ = 4 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 2
      show (z ^ 2 * q2 z / (1 + z) ^ 6) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q2 z / (1 + z) ^ 6) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q2 z) ^ 2 / (1 + z) ^ 8 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q2 z) ^ 2 ≤ (12 * (1 + z) ^ 2) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q2 z)) (q2_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q2 z) ^ 2 / (1 + z) ^ 8 ≤ (12 * (1 + z) ^ 2) ^ 2 / (1 + z) ^ 8 := by gcongr
        _ = 144 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 3
      show (z ^ 2 * q3 z / (1 + z) ^ 7) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q3 z / (1 + z) ^ 7) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q3 z) ^ 2 / (1 + z) ^ 10 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q3 z) ^ 2 ≤ (52 * (1 + z) ^ 3) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q3 z)) (q3_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q3 z) ^ 2 / (1 + z) ^ 10 ≤ (52 * (1 + z) ^ 3) ^ 2 / (1 + z) ^ 10 := by gcongr
        _ = 2704 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 4
      show (z ^ 2 * q4 z / (1 + z) ^ 8) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q4 z / (1 + z) ^ 8) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q4 z) ^ 2 / (1 + z) ^ 12 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q4 z) ^ 2 ≤ (416 * (1 + z) ^ 4) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q4 z)) (q4_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q4 z) ^ 2 / (1 + z) ^ 12 ≤ (416 * (1 + z) ^ 4) ^ 2 / (1 + z) ^ 12 := by gcongr
        _ = 173056 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := le_refl _
  calc Work.FTS.Nonlinear.RadialProd.Rint hk2 z
      = ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        rfl
    _ ≤ ∑ _i ∈ Finset.range 5, 173056 / (1 + z) ^ 4 := Finset.sum_le_sum hterm
    _ = 865280 / (1 + z) ^ 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring


/-! ### Smoothness, measurability and integrability of the density -/

private lemma smoothQuad_hKer :
    Work.FTS.LocData.SmoothQuad (fun z (_ : ℝ) => Work.Spaces.hKer z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Spaces.hKer p.1)
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
  have h : (fun p : ℝ × ℝ => Work.Spaces.hKer p.1) = fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2 := by
    funext p; exact Work.Spaces.hKer_apply p.1
  rw [h]
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_fst
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    exact ((contDiffOn_const.add contDiffOn_fst)).pow 2
  exact hnum.div hden (fun p hp => by
    have hp1 : (-1 : ℝ) < p.1 := hp.1
    have h1 : (0 : ℝ) < 1 + p.1 := by linarith
    positivity)

private lemma smoothQuad_hk2 : Work.FTS.LocData.SmoothQuad (fun z (_ : ℝ) => hk2 z) := by
  have h1 : (fun z (_ : ℝ) => hk2 z)
      = fun z _ => Work.Spaces.hKer z * Work.Spaces.hKer z := by
    funext z θ; rw [hk2]; ring
  rw [h1]
  exact Work.FTS.LocData.smoothQuad_mul smoothQuad_hKer smoothQuad_hKer

private lemma aesm_Rint_hk2 : AEStronglyMeasurable (Work.FTS.Nonlinear.RadialProd.Rint hk2)
    (volume.restrict Work.Spaces.Iz) := by
  have hsum : Work.FTS.Nonlinear.RadialProd.Rint hk2
      = ∑ i ∈ Finset.range 5,
          (fun z => (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    simp only [Work.FTS.Nonlinear.RadialProd.Rint, Finset.sum_apply]
  rw [hsum]
  exact Finset.aestronglyMeasurable_sum _
    (fun i hi => Work.FTS.Nonlinear.RadialProd.aesm_DzdIter_sq_w_sq hk2 smoothQuad_hk2 i)

private lemma inv_one_add_le_one {z : ℝ} (hz : 0 ≤ z) : 1 / (1 + z) ≤ 1 := by
  have h : 0 < 1 + z := by linarith
  rw [div_le_one h]; linarith

private lemma inv_one_add_pow_le {z : ℝ} (hz : 0 ≤ z) :
    (1 / (1 + z)) ^ 4 ≤ (1 / (1 + z)) ^ 2 := by
  have h4 : 1 / (1 + z) ≤ 1 := inv_one_add_le_one hz
  have h5 : 0 ≤ 1 / (1 + z) := div_nonneg zero_le_one (by linarith)
  have h6 : (1 / (1 + z)) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ h5 h4 2
    simpa using this
  calc (1 / (1 + z)) ^ 4 = (1 / (1 + z)) ^ 2 * (1 / (1 + z)) ^ 2 := by ring
    _ ≤ 1 * (1 / (1 + z)) ^ 2 := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = (1 / (1 + z)) ^ 2 := by ring

private lemma inv_one_add_mul_eq {z : ℝ} :
    (865280 : ℝ) / (1 + z) ^ 4 = 865280 * (1 / (1 + z)) ^ 4 := by
  rw [div_eq_mul_inv, one_div, inv_pow]

/-- The pointwise domination of the radial density, valid on all of `Iz`. -/
private lemma Rint_hk2_le' {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 * (1 / (1 + z)) ^ 2 := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have h : Work.FTS.Nonlinear.RadialProd.Rint hk2 0 = 0 := by
      rw [Work.FTS.Nonlinear.RadialProd.Rint, Work.Spaces.w]
      simp
    rw [h]
    positivity
  · have h1 : Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 / (1 + z) ^ 4 :=
      Rint_hk2_le hpos
    rw [inv_one_add_mul_eq] at h1
    exact h1.trans
      (mul_le_mul_of_nonneg_left (inv_one_add_pow_le (le_of_lt hpos)) (by norm_num))

private lemma integrable_Rint_hk2 : MeasureTheory.IntegrableOn
    (Work.FTS.Nonlinear.RadialProd.Rint hk2) Work.Spaces.Iz := by
  have hI : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (1 + z)) ^ 2) (Set.Ioi 0) :=
    Work.FTS.H2.InvOneAddSq.1
  have hI' : MeasureTheory.IntegrableOn (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      Work.Spaces.Iz := by
    show Integrable (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hI.const_mul 865280
  refine hI'.mono' aesm_Rint_hk2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.Rint_nonneg hk2 z)]
  exact Rint_hk2_le' hz

/-- The radial quantity `Rr hKer²` is bounded by `1730560`. -/
private lemma Rr_hk2_le : Work.FTS.Nonlinear.RadialProd.Rr hk2 ≤ 1730560 := by
  have hI : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (1 + z)) ^ 2) (Set.Ioi 0) :=
    Work.FTS.H2.InvOneAddSq.1
  have hI' : MeasureTheory.IntegrableOn (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      Work.Spaces.Iz := by
    show Integrable (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hI.const_mul 865280
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => Work.FTS.Nonlinear.RadialProd.Rint_nonneg hk2 z)
    hI' (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => Rint_hk2_le' hz))
  have hval : (∫ z in Work.Spaces.Iz, 865280 * (1 / (1 + z)) ^ 2)
      = 865280 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  rw [hval] at hmain
  have h2' : (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact Work.FTS.H2.InvOneAddSq.2
  calc Work.FTS.Nonlinear.RadialProd.Rr hk2
      = ∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint hk2 z := rfl
    _ ≤ 865280 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 := hmain
    _ ≤ 865280 * 2 := mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ = 1730560 := by norm_num

private lemma Kth_le : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10000 := by
  have h1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).2
  have h3 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [h3] at h
  norm_num at h
  show (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10000
  exact h

/-- **The radial input `hkerSq_radial` of row 23.** -/
theorem hkerSq_radial_alt :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ≤ C := by
  refine ⟨Real.sqrt (1730560 * 10000) + 1, by positivity, ?_⟩
  intro α hα hα1
  have hswap : (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) = fun z (_ : ℝ) => hk2 z := by
    funext z θ; rw [hk2]
  rw [hswap]
  constructor
  · -- `HkMem`
    constructor
    · -- the `θ`-slices
      intro z hz
      have h1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
      have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
      have h3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
        (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).1
      have h4 : MeasureTheory.Integrable
          (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) :=
        h3.const_mul _
      have hslice : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
            * Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ := by
        refine h4.congr (Filter.Eventually.of_forall fun θ => ?_)
        simp only [Work.FTS.Nonlinear.RadialProd.smE]
      refine hslice.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      show Work.FTS.Nonlinear.RadialProd.Rint hk2 z * Work.FTS.Nonlinear.RadialProd.smE θ
        = Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => hk2 z) z θ
      rw [Work.Elliptic.HkIntegrand_rad α 4 hk2 z hθ, Work.FTS.Nonlinear.RadialProd.Rint,
        Finset.sum_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.smE]
      rw [Finset.sum_mul, Finset.sum_mul]
    · -- the `z`-integral of the slices
      have hcongr : (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => hk2 z) z θ)
          = fun z => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
              * Work.FTS.Nonlinear.RadialProd.Kth :=
        funext fun z => Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad α hk2 z
      rw [hcongr]
      exact integrable_Rint_hk2.mul_const _
  · -- the `Xn` bound
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq]
    have hK0 : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth :=
      le_trans (by norm_num) Work.FTS.Nonlinear.RadialProd.one_le_Kth
    have hstep : Work.FTS.Nonlinear.RadialProd.Rr hk2 * Work.FTS.Nonlinear.RadialProd.Kth
        ≤ 1730560 * 10000 :=
      mul_le_mul Rr_hk2_le Kth_le hK0 (by norm_num)
    refine (Real.sqrt_le_sqrt hstep).trans ?_
    linarith [Real.sqrt_nonneg (1730560 * 10000)]

end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.BmodeCoeff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "Idm" => Work.FTS.EllipticEst.Lzero1
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "GB" => Work.FTS.VocabO.GamBar
local notation "λm" => Work.FTS.PhiStar.Gegenbauer.lam

theorem integrableOn_Iθ_of_continuous {f : ℝ → ℝ} (hf : ContinuousOn f Iθ) : IntegrableOn f Iθ := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (show IsCompact Iθ from isCompact_Icc) hf
  exact integrableOn_Iθ_of_bound (hf.aestronglyMeasurable measurableSet_Iθ) (C := C) (fun θ hθ => by
    have h := hC θ hθ
    rwa [Real.norm_eq_abs] at h)

/-- The main coefficient identity: `λ_m · (ψ, e_m) = (Γ̄, e_m)` on `Iθ`. -/
theorem coeff_eq (χ : ℝ → ℝ → ℝ)
    (hχc : ∀ δ : ℝ, 0 < δ → ContDiff ℝ 2 (χ δ))
    (hχ1 : ∀ δ : ℝ, 0 < δ → ∀ θ ∈ Set.Icc δ (Real.pi / 2 - δ), χ δ θ = 1)
    (hχ0 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℝ → ℝ} (hang : AngModel α ψ) (m : ℕ)
    (hlimA : Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
      atTop (nhds (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)))
    (hlimC : Tendsto (fun n : ℕ => ∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
      atTop (nhds (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ)))
    (hlimB : Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ *
        (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
          - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)
      atTop (nhds 0)) :
    λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ := by
  have hmain : ∀ n : ℕ,
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
            - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
            + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ) = 0 := by
    intro n
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    let e : ℝ → ℝ := fun θ => eF m θ
    let G : ℝ → ℝ := fun θ => GB α θ
    let V : ℝ → ℝ := fun θ => χ δ θ * e θ
    let CD : ℝ → ℝ := fun θ => -(deriv (deriv (χ δ)) θ * e θ)
      - 2 * (deriv (χ δ) θ * deriv e θ) + Real.tan θ * deriv (χ δ) θ * e θ
    change λm m * (∫ θ in Iθ, ψ θ * χ δ θ * e θ * Real.cos θ)
        - (∫ θ in Iθ, G θ * χ δ θ * e θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * CD θ * Real.cos θ) = 0
    have hδpos : 0 < δ := by dsimp only [δ]; positivity
    have hδle : δ ≤ 1 := by
      dsimp only [δ]
      rw [div_le_one (by positivity : (0:ℝ) < (n:ℝ) + 1)]
      have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hcpos : 0 < δ / 2 := by linarith
    have hcd : δ / 2 < Real.pi / 2 - δ / 2 := by
      linarith [Real.pi_gt_three, hδle]
    have hdlt : Real.pi / 2 - δ / 2 < Real.pi / 2 := by linarith
    have hf : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) :=
      hang.smooth.of_le (by simp [Work.Stability.smoothOrder])
    have hVc : ContDiffOn ℝ 2 V (Set.Ioo 0 (Real.pi / 2)) := by
      dsimp only [V]
      exact (hχc δ hδpos).contDiffOn.mul (contDiff_eF m).contDiffOn
    have hV0 : ∀ θ, θ ∉ Set.Icc (δ / 2) (Real.pi / 2 - δ / 2) → V θ = 0 := by
      intro θ hθ
      dsimp only [V]
      rw [hχ0 δ hδpos θ (fun hm => hθ (Set.Ioo_subset_Icc_self hm)), zero_mul]
    have hibp := ibp_Iθ (u := ψ) (v := V) hcpos hcd hdlt hf hVc hV0
    have hpt : ∀ θ ∈ Iθ,
        (ψ θ * Idm V θ - Idm ψ θ * V θ) * Real.cos θ
          = (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ + ψ θ * CD θ) * Real.cos θ := by
      intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0]
        have hψ0 : ψ 0 = 0 := hang.bdry0
        have he0 : e 0 = 0 := by dsimp only [e]; exact eF_zero m
        have hG0 : G 0 = 0 := by dsimp only [G]; exact GamBar_zero hα
        have hVz : V 0 = 0 := by dsimp only [V]; rw [he0, mul_zero]
        rw [hψ0, hVz, he0, hG0]
        dsimp only [CD]
        ring
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · rw [h2]
          simp [Real.cos_pi_div_two]
        · have hcos : Real.cos θ ≠ 0 :=
            ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h0, Real.pi_pos], h2⟩)
          have hVeq : V θ = χ δ θ * e θ := rfl
          have hχe : Idm (fun t => χ δ t * e t) θ
              = χ δ θ * Idm e θ + (-(deriv (deriv (χ δ)) θ * e θ)
                  - 2 * (deriv (χ δ) θ * deriv e θ) + Real.tan θ * deriv (χ δ) θ * e θ) :=
            lzero1_mul_eq (hχc δ hδpos) (contDiff_eF m) hcos
          have hee : Idm e θ = λm m * e θ := by
            have h2' : Idm e θ = Work.Elliptic.Lzero (fun _ θ' => eF m θ') 0 θ :=
              (congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (eF m) 0)) θ
            rw [h2']
            exact Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0
          have hψψ : Idm ψ θ = G θ := by
            dsimp only [G]; exact hang.eq θ ⟨h0, h2⟩
          have hVe : V θ = χ δ θ * e θ := rfl
          rw [hVe, hχe, hee, hψψ]
          dsimp only [CD]
          ring
    have hkey : (∫ θ in Iθ, (ψ θ * Idm V θ - Idm ψ θ * V θ) * Real.cos θ)
        = ∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ
            + ψ θ * CD θ) * Real.cos θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Iθ hpt
    have hcontψ : ContinuousOn ψ Iθ := hang.cont
    have hcontχ : ContinuousOn (χ δ) Iθ := (hχc δ hδpos).continuous.continuousOn
    have hconte : ContinuousOn e Iθ := by
      dsimp only [e]; exact (contDiff_eF m).continuous.continuousOn
    have hcontG : ContinuousOn G Iθ := by
      dsimp only [G]; exact continuousOn_GamBar α hα hα1
    have hcontDχ : ContinuousOn (deriv (χ δ)) Iθ :=
      ((hχc δ hδpos).continuous_deriv (by norm_num)).continuousOn
    have hcontD2χ : ContinuousOn (deriv (deriv (χ δ))) Iθ := by
      have h1 : ContDiff ℝ 1 (deriv (χ δ)) := (hχc δ hδpos).deriv'
      exact (h1.continuous_deriv (by norm_num)).continuousOn
    have hcontDe : ContinuousOn (deriv e) Iθ := by
      dsimp only [e]
      exact ((contDiff_eF m).continuous_deriv (by norm_num)).continuousOn
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) Iθ := Real.continuous_sin.continuousOn
    have hcosc : ContinuousOn (fun θ : ℝ => Real.cos θ) Iθ := Real.continuous_cos.continuousOn
    -- integrability of the two pieces
    have hint1 : IntegrableOn (fun θ => (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ)
        * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous
        (((continuousOn_const.mul (hcontψ.mul hcontχ |>.mul hconte))).sub
          (hcontG.mul hcontχ |>.mul hconte) |>.mul hcosc)
    have hCDeq : ∀ θ ∈ Iθ, ψ θ * CD θ * Real.cos θ
        = ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ))
            * Real.cos θ + ψ θ * (Real.sin θ * deriv (χ δ) θ * e θ) := by
      intro θ hθ
      rcases eq_or_ne (Real.cos θ) 0 with hc | hc
      · have heθ : e θ = 0 := by
          dsimp only [e]
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · rw [← h0]; exact eF_zero m
          · rcases eq_or_lt_of_le hθ.2 with h2 | h2
            · rw [h2]; exact eF_pi m
            · exact absurd hc (ne_of_gt (Real.cos_pos_of_mem_Ioo
                ⟨by linarith [h0, Real.pi_pos], h2⟩))
        dsimp only [CD]
        rw [hc, heθ]
        ring
      · have htan : Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ
            = Real.sin θ * deriv (χ δ) θ * e θ := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp
        dsimp only [CD]
        rw [show ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ)
              + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ
            = ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ)) * Real.cos θ
              + ψ θ * (Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ) from by ring,
          htan]
    have hint2' : IntegrableOn (fun θ => ψ θ * (-(deriv (deriv (χ δ)) θ * e θ)
        - 2 * (deriv (χ δ) θ * deriv e θ)) * Real.cos θ
        + ψ θ * (Real.sin θ * deriv (χ δ) θ * e θ)) Iθ :=
      integrableOn_Iθ_of_continuous
        ((hcontψ.mul (((hcontD2χ.mul hconte).neg).sub (hcontDχ.mul hcontDe |>.const_mul 2))).mul
            hcosc |>.add (hcontψ.mul (hsin.mul hcontDχ |>.mul hconte)))
    have hint2 : IntegrableOn (fun θ => ψ θ * CD θ * Real.cos θ) Iθ := by
      refine hint2'.congr_fun (fun θ hθ => ?_) measurableSet_Iθ
      exact (hCDeq θ hθ).symm
    -- splitting
    have hsplit1 : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ
          + ψ θ * CD θ) * Real.cos θ)
        = (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
          + (∫ θ in Iθ, ψ θ * CD θ * Real.cos θ) := by
      rw [show (fun θ => (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ + ψ θ * CD θ)
            * Real.cos θ)
          = fun θ => ((λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
            + (ψ θ * CD θ * Real.cos θ) from by funext θ; ring]
      rw [integral_add hint1 hint2]
    have hsplit2 : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
        = λm m * (∫ θ in Iθ, ψ θ * χ δ θ * e θ * Real.cos θ)
          - (∫ θ in Iθ, G θ * χ δ θ * e θ * Real.cos θ) := by
      have hP : IntegrableOn (fun θ => λm m * (ψ θ * χ δ θ * e θ * Real.cos θ)) Iθ :=
        integrableOn_Iθ_of_continuous
          (continuousOn_const.mul ((hcontψ.mul hcontχ |>.mul hconte) |>.mul hcosc))
      have hQ : IntegrableOn (fun θ => G θ * χ δ θ * e θ * Real.cos θ) Iθ :=
        integrableOn_Iθ_of_continuous ((hcontG.mul hcontχ |>.mul hconte) |>.mul hcosc)
      have hcongr : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
          = ∫ θ in Iθ, ((λm m * (ψ θ * χ δ θ * e θ * Real.cos θ))
              - (G θ * χ δ θ * e θ * Real.cos θ)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => by ring)
      rw [hcongr, integral_sub hP hQ, integral_const_mul]
    rw [hkey] at hibp
    rw [hsplit1] at hibp
    rw [hsplit2] at hibp
    exact hibp
  have hL1 : Tendsto (fun n : ℕ =>
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ))) :=
    (hlimA.const_mul (λm m)).sub hlimC
  have hL2 : Tendsto (fun n : ℕ =>
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
            - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
            + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) + 0)) :=
    hL1.add hlimB
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) + 0)) := by
    refine hL2.congr' ?_
    filter_upwards with n
    exact hmain n
  have hfin := tendsto_nhds_unique hzero tendsto_const_nhds
  linarith [hfin]

/-- The `L²(cos θ dθ)` norm of `e_m` is at least `(2m+1)/2`. -/
theorem eFam_norm_ge (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / 2 ≤ ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
  have h2 : (0:ℝ) < 2 := by norm_num
  have h3 : (0:ℝ) < 4 * (m:ℝ) + 5 := by positivity
  rw [div_le_iff₀ h2]
  rw [show ((2 * (m:ℝ) + 2) * (2 * (m:ℝ) + 3)) / (4 * (m:ℝ) + 5) * 2
      = (2 * ((2 * (m:ℝ) + 2) * (2 * (m:ℝ) + 3))) / (4 * (m:ℝ) + 5) from by ring]
  rw [le_div_iff₀ h3]
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  nlinarith [hm0]

theorem int_cos_Iθ : (∫ θ in Iθ, Real.cos θ) = 1 := by
  rw [← iota_eq]
  rw [integral_cos]
  norm_num


end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.ResolventSetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- **The per-mode resolvent identity**: `λ_m · radGreen α m c z = c z + A (radGreen α m c) z`,
where `A a := α²z²a'' + α(5+α)za'`. -/
theorem radGreen_resolvent (α : ℝ) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hα : 0 < α) (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 *
            deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
  have h := Work.FTS.PhiStar.Radial.radGreen_solves hα m hc h0 h0' hinf z hz
  have h' : Work.FTS.PhiStar.Radial.lamR m
        * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
    linarith [h]
  exact h'


end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-! A finite sum `∑_{k<n} F k` agreeing with `g` on the open quadrant transfers both
`ℋ⁴`-membership and the `ℋ⁴`-norm bound to `g`, at the price of the factor `√(2^n)` of
`Work.FTS.GalFields.RHS.HkNorm_finset_sum_le`.  Please put the declaration in namespace
`Work.FTS.StrongEps.ClassCRHS` (file
`Submission/Work/FTS/StrongEps/ClassCRHS/HkSumOpenClosure.lean`), as the sibling
`StarAtomsFK` does, so it is usable as
`Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure`.

Route (all tools already on disk): `HkMem α 4 g` follows from
`Work.FTS.LocData.HkMem_of_majorant α 4` applied to `g` with the majorant
`M z θ = (2:ℝ)^n * ∑ k ∈ Finset.range n, HkIntegrand α 4 (F k) z θ` — slices and `z`-integral
integrable from `hm`; domination at interior points from `hag` +
`Work.FTS.EllipticEst.HkIntegrand_congr` + `HkIntegrand_finset_sum_le`, at `z = 0` from
`Work.FTS.LocData.HkIntegrand_zero_fst`, at `sin (2θ) = 0` from
`Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts` (nonnegativity of `M` from
`HkIntegrand_nonneg`). The norm bound is `HkNorm_finset_sum_le` together with
`HkSq_congr_open α 4 hag` (`Xn α g = HkNorm α 4 g` definitionally). -/
theorem HkSumOpenClosure {α : ℝ} (hα : 0 < α) {n : ℕ} {g : Work.FTS.Galerkin.Fn}
    {F : ℕ → Work.FTS.Galerkin.Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsm : ∀ k ∈ Finset.range n, Work.FTS.EllipticEst.SmoothOpen (F k))
    (hm : ∀ k ∈ Finset.range n, Work.Spaces.HkMem α 4 (F k))
    (hag : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      g z θ = ∑ k ∈ Finset.range n, F k z θ) :
    Work.Spaces.HkMem α 4 g ∧
      Work.FTS.Nonlin.Xn α g ≤ Real.sqrt ((2 : ℝ) ^ n) * ∑ k ∈ Finset.range n,
        Work.FTS.Nonlin.Xn α (F k) := by
  classical
  set M : ℝ → ℝ → ℝ := fun z θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
      Work.Spaces.HkIntegrand α 4 (F k) z θ with hM
  have hMnn : ∀ z θ : ℝ, 0 ≤ M z θ := by
    intro z θ
    show 0 ≤ (2 : ℝ) ^ n * ∑ k ∈ Finset.range n, Work.Spaces.HkIntegrand α 4 (F k) z θ
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => Work.Spaces.HkIntegrand_nonneg α 4 (F k) z θ)
  -- ### membership
  have hmem : Work.Spaces.HkMem α 4 g := by
    refine Work.FTS.LocData.HkMem_of_majorant (f := g) (M := M) α 4 hcont ?_ ?_ ?_
    · -- integrable `θ`-slices of the majorant
      intro z hz
      show IntegrableOn (fun θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 4 (F k) z θ) Work.Spaces.Iθ
      have hsum : Integrable (fun θ : ℝ => ∑ k ∈ Finset.range n,
          Work.Spaces.HkIntegrand α 4 (F k) z θ) (volume.restrict Work.Spaces.Iθ) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).1 z hz)
      exact hsum.const_mul _
    · -- integrable `z`-integral of the majorant
      show IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 4 (F k) z θ) Work.Spaces.Iz
      have hsum : Integrable (fun z : ℝ => ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).2)
      have hbase : Integrable (fun z : ℝ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) := hsum.const_mul _
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
      intro k hk
      exact (hm k hk).1 z hz
    · -- pointwise domination on the closed quadrant
      intro z hz θ hθ
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
        exact hMnn 0 θ
      · by_cases hs : Real.sin (2 * θ) = 0
        · rw [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 4 g hα hs]
          exact hMnn z θ
        · have hθpos : 0 < θ := by
            rcases lt_or_eq_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h | h
            · exact h
            · exact absurd (by rw [← h, mul_zero, Real.sin_zero]) hs
          have hθlt : θ < Real.pi / 2 := by
            rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring,
                Real.sin_pi]) hs
          have hgeq : Work.Spaces.HkIntegrand α 4 g z θ
              = Work.Spaces.HkIntegrand α 4
                  (fun z θ => ∑ k ∈ Finset.range n, F k z θ) z θ :=
            Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4)
              (fun z θ hz hθ hlt => hag z θ hz hθ hlt) z θ hzpos hθpos hθlt
          rw [hgeq]
          have hle := Work.FTS.GalFields.RHS.HkIntegrand_finset_sum_le α 4 hα
            (Finset.range n) hsm z hz θ hθ
          simp only [Finset.card_range] at hle
          exact hle
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hXn : Work.FTS.Nonlin.Xn α g
      = Work.Spaces.HkNorm α 4 (fun z θ => ∑ k ∈ Finset.range n, F k z θ) := by
    show Work.Spaces.HkNorm α 4 g = _
    rw [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 4 hag,
      Work.Spaces.HkNorm]
  rw [hXn]
  simpa only [Finset.card_range] using
    Work.FTS.GalFields.RHS.HkNorm_finset_sum_le α 4 hα (Finset.range n) hsm hm

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.RadHkMemXn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-- **A radial profile with the decay `|D_z^i r| ≤ C z²/(1+z)³` (`i ≤ 4`) is an `ℋ⁴`-function,
uniformly in `α ∈ (0,1]`.**

Because `r` depends on `z` only, every mixed slot `D_z^j D_θ^i r` with `i ≥ 1` vanishes, so the
`ℋ⁴`-integrand reduces to the pure `D_z`-sum (`Work.Elliptic.HkIntegrand_rad`).  The weight
`w(z) = (1+z)²/z²` converts the hypothesis into the bound `|D_z^i r · w| ≤ C/(1+z)`, whence
`Rint r ≤ 5 (C/(1+z))²` pointwise; the last quantity is integrable on `[0,∞)` with integral at
most `2` (`Work.FTS.H2.InvOneAddSq`).  Consequently `HkSq α 4 r ≤ 10 C² K_θ` with
`K_θ = ∫_θ sin(2θ)^{-η}`, independently of `α`, and `HkNorm = √(HkSq) ≤ √(10 C² K_θ)`. -/
theorem RadHkMemXn {r : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (h : ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C * z ^ 2 / (1 + z) ^ 3) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ C' := by
  -- ### Step 1: the pointwise slot bound `(D_z^i r)² w² ≤ (C/(1+z))²` on `Iz`.
  have hslot : ∀ (i : ℕ), i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (C / (1 + z)) ^ 2 := by
    intro i hi z hz
    have hz0 : 0 ≤ z := hz
    have habs := h i hi z hz0
    have hsq : (Work.Elliptic.DzdIter i r z) ^ 2 ≤ (C * z ^ 2 / (1 + z) ^ 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Work.Spaces.w z))
    rcases eq_or_lt_of_le hz0 with hz' | hz'
    · rw [← hz']
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, div_one]
      exact sq_nonneg C
    · refine hprod.trans (le_of_eq ?_)
      rw [Work.Spaces.w]
      field_simp
  -- ### Step 2: `Rint r = Σ_{i≤4} (D_z^i r)² w²` is pointwise bounded by `5 (C/(1+z))²`.
  have hRint_le : ∀ z ∈ Work.Spaces.Iz,
      Work.FTS.Nonlinear.RadialProd.Rint r z ≤ 5 * (C / (1 + z)) ^ 2 := by
    intro z hz
    rw [Work.FTS.Nonlinear.RadialProd.Rint]
    calc ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ∑ _i ∈ Finset.range 5, (C / (1 + z)) ^ 2 :=
          Finset.sum_le_sum (fun i hi =>
            hslot i (by have := Finset.mem_range.mp hi; omega) z hz)
      _ = 5 * (C / (1 + z)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ### Step 3: the dominating function is integrable on `Iz`.
  have hg_int : IntegrableOn (fun z : ℝ => 5 * (C / (1 + z)) ^ 2) Work.Spaces.Iz := by
    have h1 : MeasureTheory.Integrable (fun z : ℝ => 5 * C ^ 2 * (1 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul _
    have h2 : MeasureTheory.Integrable (fun z : ℝ => 5 * (C / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      h1.congr (Filter.Eventually.of_forall fun z => by ring)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
    exact h2
  -- ### Step 4: `Rint r` is a.e. strongly measurable on `Iz`.
  have hRint_aesm : AEStronglyMeasurable (Work.FTS.Nonlinear.RadialProd.Rint r)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hr_aesm : AEStronglyMeasurable r (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h1 : AEStronglyMeasurable r (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioi
      rwa [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h1
    have hw_aesm : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (by
        have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
          funext z; rw [Work.Spaces.w]
        rw [hfun]
        fun_prop : Measurable fun z : ℝ => (Work.Spaces.w z) ^ 2).aestronglyMeasurable
    rw [show (Work.FTS.Nonlinear.RadialProd.Rint r)
        = ∑ i ∈ Finset.range 5,
            (fun z : ℝ => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        from by
          funext z
          rw [Work.FTS.Nonlinear.RadialProd.Rint, Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    by_cases hi0 : i = 0
    · subst hi0
      have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter 0 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => (r z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        funext z
        rw [Work.Elliptic.DzdIter_zero]
      rw [hfun]
      exact (hr_aesm.pow 2).mul hw_aesm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hmeas : Measurable (Work.Elliptic.DzdIter (k + 1) r) := by
        have hfun : Work.Elliptic.DzdIter (k + 1) r
            = fun z : ℝ => z * deriv (Work.Elliptic.DzdIter k r) z := rfl
        rw [hfun]
        exact measurable_id.mul (measurable_deriv _)
      exact ((hmeas.aestronglyMeasurable).pow 2).mul hw_aesm
  -- ### Step 5: `Rint r` is integrable on `Iz` and `Rr r ≤ 10 C²`.
  have hRint_int : IntegrableOn (Work.FTS.Nonlinear.RadialProd.Rint r) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hg_int hRint_aesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.Rint_nonneg r z)]
    exact hRint_le z hz
  have hRr_le : Work.FTS.Nonlinear.RadialProd.Rr r ≤ 10 * C ^ 2 := by
    have hmono : (∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint r z)
        ≤ ∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2 :=
      MeasureTheory.integral_mono_ae hRint_int hg_int
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hRint_le)
    have hval : (∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2) ≤ 10 * C ^ 2 := by
      have hIoi : (∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2)
          = ∫ z in Set.Ioi (0 : ℝ), 5 * (C / (1 + z)) ^ 2 :=
        MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
      rw [hIoi]
      have hstep : (∫ z in Set.Ioi (0 : ℝ), 5 * (C / (1 + z)) ^ 2)
          = (5 * C ^ 2) * ∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun z => by ring)
      rw [hstep]
      have hnn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2 :=
        MeasureTheory.integral_nonneg fun z => sq_nonneg _
      nlinarith [Work.FTS.H2.InvOneAddSq.2, hnn, sq_nonneg C]
    rw [Work.FTS.Nonlinear.RadialProd.Rr]
    exact hmono.trans hval
  -- ### Step 6: `HkSq α 4 r` and `Xn α r` are bounded independently of `α`.
  have hKth_nonneg : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth := by
    have := Work.FTS.Nonlinear.RadialProd.one_le_Kth
    linarith
  have hHkSq_le : ∀ α : ℝ, Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z)
      ≤ 10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth := by
    intro α
    rw [Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq α r]
    exact mul_le_mul_of_nonneg_right hRr_le hKth_nonneg
  -- ### Assembly.
  refine ⟨max 1 (Real.sqrt (10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth)),
    lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro α hα
  constructor
  · -- `HkMem α 4 (fun z _ => r z)`
    have hsin_int : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
        Work.Spaces.eta_lt_one).1
    constructor
    · -- the `θ`-slices are integrable
      intro z _hz
      have hconst : IntegrableOn
          (fun θ : ℝ => ((∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i r z) ^ 2)
            * (Work.Spaces.w z) ^ 2) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ :=
        hsin_int.const_mul _
      refine hconst.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      rw [Work.Elliptic.HkIntegrand_rad α 4 r z hθ]
    · -- the `z`-integral of the `θ`-integrals is integrable
      refine (hRint_int.mul_const Work.FTS.Nonlinear.RadialProd.Kth).congr
        (Filter.Eventually.of_forall fun z => ?_)
      exact (Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad α r z).symm
  · -- the norm bound
    have hsq := hHkSq_le α
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z))
        ≤ Real.sqrt (10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth) := Real.sqrt_le_sqrt hsq
    exact h1.trans (le_max_right 1 _)

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_sq_div_small_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

/-! ## The open-class helpers of `L12f_sq_div_small`

This file re-proves, in the *open* smoothness class `Work.FTS.EllipticEst.SmoothOpen f`
(`C^∞` on the open quadrant `(0,∞) × (0,π/2)`), the chain of
`Work.FTS.CoercivityFix.Coer1T` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`)
that yields `intA` of `HardyHyp` on `(0,1]`:

* `slice_sq_integrableOn_open` — the squared angular slice is `L¹` on `Iθ`;
* `B4_sqrt_aesm_open`, `B4_sqrt_aesm_mono_open` — a.e. strong measurability of `s ↦ √(B4 α f s)`;
* `dens_abs_le_open` — the pointwise density bound `|L₁₂dens(K,f,s)| ≤ √3·s/(1+s)²·√(B4 α f s)`;
* `L12f_abs_le_prim_open` — `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s√(B4 α f s)` for `0 < z ≤ 1`;
* `L12f_sq_div_z4_integrableOn_Ioc_open` — `(L₁₂ f z)²/z⁴ ∈ L¹((0,1])`;
* `L12f_sq_div_small_open` — `(L₁₂ f z)²/z^{2j} ∈ L¹((0,1])` for `j ≤ 2`.

The only `SmoothQuad` inputs of the original chain are the joint continuity of the
`ℋ⁴`-integrand (here `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) and the
density bound; everything else already needs no smoothness hypothesis. -/

/-- The squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`, for a datum
`f` that is `C^∞` on the open quadrant and lies in `ℋ⁴`.

This is the open-class analogue of `Work.FTS.H2.l12q_slice_sq_integrableOn` (equivalently of
the private `Work.FTS.MeridianDyn.Bridge.Pieces.slice_sq_integrableOn`).  For a.e. `θ ∈ Iθ`
(all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w z ≥ 1`, so
`(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`. -/
theorem slice_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      hsm.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- A.e. strong measurability of `s ↦ B4 α f s = ∫_θ HkIntegrand α 4 f s θ` on `Iz`, from
`C^∞` on the open quadrant: the joint integrand is continuous there
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) hence a.e. strongly measurable
(`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini gives the measurability of the partial
integral.  The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_aesm`. -/
theorem B4_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    (hsm.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm`. -/
theorem B4_sqrt_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (B4_aesm_open α hsm)

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm_mono`. -/
theorem B4_sqrt_aesm_mono_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (MeasureTheory.volume.restrict u) :=
  (B4_sqrt_aesm_open α hsm).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`: the `L₁₂`-density
obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`, from `SmoothOpen f`. -/
theorem dens_abs_le_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_integrableOn_open α hsm hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2) :=
          Real.sqrt_le_sqrt hint
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
            / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s) _
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3
            * (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2)
            * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_prim`:
`|L₁₂ f z| ≤ √3 ∫_{(0,z]} s √(B4 α f s)` for `0 < z ≤ 1`. -/
theorem L12f_abs_le_prim_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3
        * ∫ s in Set.Ioc 0 z, s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hrepr : Work.Coercivity.L12f f z = -(∫ s in Set.Ioc 0 z, G s) := by
    rw [Work.FTS.CoercivityFix.Coer1T.L12f_eq_neg_prim hint hl12 hz,
      intervalIntegral.integral_of_le hz.le]
  rw [hrepr, abs_neg]
  -- the majorant `maj s = √3 * (s * √(B4 s))`
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hmaj_aesm : AEStronglyMeasurable
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((continuous_id.aestronglyMeasurable.mul (B4_sqrt_aesm_mono_open α hsm hu)).const_mul
      (Real.sqrt 3))
  -- the majorant is integrable
  have hBint : MeasureTheory.IntegrableOn (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (Set.Ioc 0 z) :=
    (Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmaj_bound : ∀ s ∈ Set.Ioc 0 z,
      Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      ≤ (Real.sqrt 3 / 2) * (1 + Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    intro s hs
    have hBs : 0 ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s :=
      Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s
    have hle1 : s ≤ 1 := le_trans hs.2 hz1
    have hs0 : 0 < s := hs.1
    have hsqrt_le : Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
        ≤ (1 + Work.FTS.CoercivityFix.Coer1T.B4 α f s) / 2 := by
      nlinarith [Real.sq_sqrt hBs, sq_nonneg (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) - 1)]
    have hsle : s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
        ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
      nlinarith [hle1, hs0, Real.sqrt_nonneg (Work.FTS.CoercivityFix.Coer1T.B4 α f s)]
    nlinarith [hsqrt_le, hsle, Real.sqrt_nonneg 3]
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)))
      (Set.Ioc 0 z) :=
    ((hconst.add hBint).const_mul (Real.sqrt 3 / 2)).mono' hmaj_aesm
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
        rw [Real.norm_of_nonneg (by
          have hx0 : 0 < x := hx.1
          positivity)]
        exact hmaj_bound x hx))
  -- the pointwise domination of `G`
  have hG_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 z)), ‖G s‖
      ≤ Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have h1 := dens_abs_le_open α hsm hmem hs0
    have h2 : s / (1 + s) ^ 2 ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg s, le_of_lt hs0]
    rw [Real.norm_eq_abs]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
          * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := h1
      _ ≤ Real.sqrt 3 * s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := by ring
  have hbd := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hG_bd
  rw [Real.norm_eq_abs] at hbd
  calc |∫ s in Set.Ioc 0 z, G s|
      ≤ ∫ s in Set.Ioc 0 z,
          Real.sqrt 3 * (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) := hbd
    _ = Real.sqrt 3
          * ∫ s in Set.Ioc 0 z, s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
        rw [MeasureTheory.integral_const_mul]

/-- The open-class analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_z4_integrableOn_Ioc`:
`(L₁₂ f z)²/z⁴` is integrable on `(0,1]`. -/
theorem L12f_sq_div_z4_integrableOn_Ioc_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4)
      (Set.Ioc 0 1) := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) with hΨdef
  have hPsi : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Set.Ioc 0 1) := by
    refine ((Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set
      (fun t ht => ht.1)).congr_fun (fun s hs => ?_) measurableSet_Ioc
    have hs0 : s ≠ 0 := ne_of_gt hs.1
    show Work.FTS.CoercivityFix.Coer1T.B4 α f s
      = (s * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2 / s ^ 2
    rw [mul_pow, Real.sq_sqrt (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s)]
    field_simp
  have hHT := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable Ψ hPsi).1
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹) (volume.restrict (Set.Ioc 0 1)) := by
    have hmeas : Measurable (fun z : ℝ => (z ^ 4)⁻¹) :=
      (continuous_pow 4).measurable.inv
    exact hmeas.aestronglyMeasurable.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
      (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4) (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  have hHT3 : MeasureTheory.IntegrableOn
      (fun z => 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)) (Set.Ioc 0 1) := hHT.const_mul 3
  refine hHT3.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h1 := L12f_abs_le_prim_open α hsm hmem hint hl12 hz.1 hz1
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have hkey : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have habs := abs_le.mp h1
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ 4
      ≤ 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4) := by
        rw [show 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)
            = (3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2) / z ^ 4 by ring]
        exact div_le_div_of_nonneg_right hkey (by positivity)

/-- `intA` of `HardyHyp` on `(0,1]` in the *open* class: `(L₁₂ f)²/z^{2j} ∈ L¹((0,1])` for `j ≤ 2`, from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_small` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), together with its private helpers `L12f_sq_div_z4_integrableOn_Ioc` and `L12f_abs_le_prim` re-proved in the open class (put them in the same file); the only uses of `SmoothQuad` in that chain are the a.e. strong measurability of `s ↦ √(B4 α f s)` (from `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le`, whose open version follows from the slice `L²`-domination by `HkIntegrand` (`Work.Spaces.sq_le_HkIntegrand_z`) and continuity of the slice on the open interval (`Work.Spaces.aesm_slice_of_continuousOn_Qd`; cf. the private `slice_sq_integrableOn` of `MeridianDyn/Bridge/Pieces/sliceK_integrableOn_of_continuousOn.lean`).  The Hardy-type input `Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable`, `cs_one`, `L12f_eq_neg_prim`, `L12f_aesm_mono` need no smoothness. -/
theorem L12f_sq_div_small_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioc 0 1) := by
  have h4 := L12f_sq_div_z4_integrableOn_Ioc_open α hsm hmem hint hl12 hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioc 0 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h4.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have : ((2 * j : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) := by
      have h2 : 2 * j ≤ 4 := by omega
      exact_mod_cast h2
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact this
  have hzj : z ^ 4 ≤ z ^ (2 * (j : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz1 h2j
  have hpos : 0 < z ^ (2 * (j : ℝ)) := Real.rpow_pos_of_pos hz.1 _
  have hpos4 : 0 < z ^ 4 := pow_pos hz.1 4
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hpos))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 4 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hpos4 hzj
    _ = _ := rfl

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Subtraction rule for the mixed operator `D_z^j D_θ^i` at finite regularity

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`, and
`Work.FTS.EllipticEst.Q0 = (0,∞) × (0,π/2)` is the open quadrant of the elliptic estimates.

The statement proved here is the *subtraction* (linearity) rule

  `D_z^j D_θ^i (A - B) = D_z^j D_θ^i A - D_z^j D_θ^i B`   on `Q0`, for `i + j ≤ 4`,

for two functions `A`, `B` that are only `C^4` on `Q0` (not `C^∞`, and not smooth on a
neighbourhood of the *closed* quadrant): the downstream strong-`ε` estimates work with the
honest finite-order class, so the additivity lemma of the workspace stated for `C^∞` data
(`Work.FTS.EllipticEst.SmoothOpen.mixed_add`) does not apply and the finite-order version is
needed.

Route.  Write `A - B = A + (-B)` and use the finite-order *additivity* lemma

* `Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin` : `mixed_add` for data that are only
  `C^m` on `Q0`, at orders `i + j ≤ m`,

together with the fact, recorded in `Submission/Work/FTS/StrongEps/mixed_const_mul.lean`, that
every iterate of `D_z`, `D_θ` (hence `mixed`) is *unconditionally* scalar homogeneous —
`deriv` satisfies `deriv_const_mul_field`, so homogeneity needs no differentiability
hypothesis at all.  Taking the scalar `-1` gives `mixed j i (fun z θ => -(B z θ)) =
- mixed j i B`, and the result follows.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps

/-- `∂_z` commutes with negation.  Unconditional: `deriv_const_mul_field` at the scalar `-1`
gives the result even where the function is not differentiable (there both sides are `0`). -/
theorem pz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -(f z θ)) = fun z θ => -(Work.Spaces.pz f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, pz_const_mul (-1) f]
  funext z θ; ring

/-- Every `D_θ`-iterate commutes with negation (unconditional). -/
theorem DthIter_neg (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => -(f z θ))
      = fun z θ => -(Work.Spaces.DthIter i f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, DthIter_const_mul (-1) f i]
  funext z θ; ring

/-- Every `D_z`-iterate commutes with negation (unconditional). -/
theorem DzIter_neg (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => -(f z θ))
      = fun z θ => -(Work.Spaces.DzIter j f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, DzIter_const_mul (-1) f j]
  funext z θ; ring

/-- `mixed` commutes with negation, i.e. scalar homogeneity at the scalar `-1`
(unconditional; no smoothness hypothesis is needed). -/
theorem mixed_neg {j i : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    Work.Spaces.mixed j i (fun z' θ' => -(f z' θ')) z θ
      = -(Work.Spaces.mixed j i f z θ) := by
  simp only [Work.Spaces.mixed, DthIter_neg f i, DzIter_neg (Work.Spaces.DthIter i f) j]

theorem mixed_sub_of_contDiffOn_four {j i : ℕ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hji : j + i ≤ 4) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hA : ContDiffOn ℝ 4 (Function.uncurry A) Work.FTS.EllipticEst.Q0)
    (hB : ContDiffOn ℝ 4 (Function.uncurry B) Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  -- `-B` is again `C^4` on the open quadrant
  have hBneg : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => -(B z θ)))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => -(B z θ))
        = fun p : ℝ × ℝ => -(Function.uncurry B p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact hB.neg
  -- the index bound in the shape expected by `mixed_add_fin`
  have hij : i + j ≤ 4 := by rw [Nat.add_comm i j]; exact hji
  -- rewrite `A - B` as `A + (-B)`
  have hfun : (fun z θ => A z θ - B z θ) = fun z θ => A z θ + -(B z θ) := by
    funext z θ; ring
  rw [hfun]
  -- finite-order additivity for `C^4` data on the open quadrant
  rw [Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := A)
        (g := fun z' θ' => -(B z' θ')) hA hBneg j i hij z θ hz hθ.1 hθ.2]
  -- homogeneity at the scalar `-1`
  rw [mixed_neg]
  ring

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Degen.FstarSqAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# Auxiliary estimates for `FstarHkSqZeroSmooth`

The pointwise and slicewise estimates of the `ℋ⁴`-integrand of the self-similar profile
`F_* = α(Γ/c)·2z/(1+z)²`, with the general-`α` angular jet bound
`Work.FTS.StrongPersist.Degen.DthIterGamGen` as the only analytic input.  Split off from
`FstarHkSqZeroSmooth` for file-size reasons.
-/

/-! ## Elementary angular and `rpow` facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma div_rpow_sq (A w s e : ℝ) :
    (A * (w / s ^ e)) ^ 2 = (A * w) ^ 2 * ((s ^ e) ^ 2)⁻¹ := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  ring


lemma w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (by positivity) (by positivity)

/-! ## The smoothness of the self-similar profile -/

theorem smoothOpen_Fstar (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
  (Work.FTS.LocData.SmoothQuad_Fstar α).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)

/-! ## The radial factor of `F_*`: `D_z^i F_* = (α/c)·Γ·Φ_i` with `Φ_i` free of `θ` -/






/-! ## The `ℋ⁴`-integrand of `F_*` bounded by the angular majorant `angMaj` -/




end Work.FTS.StrongPersist.Degen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Locality and commutation on an open set

`D_z` and `D_θ` are local operators, and they commute at every point at which the datum is
`C²` (Clairaut).  The lemmas below spell this out for an arbitrary *open* set `V` on which
the datum is `C^∞` in the genuine smooth order `Work.Stability.smoothOrder` — which is
exactly the shape of the hypothesis `Work.FTS.EllipticEst.SmoothOpen` at `V = Q0`. -/

/-- Two functions agreeing on an open set have the same `D_z`-iterates there. -/
private lemma DzIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b F))
      (Function.uncurry (Work.Spaces.DzIter b G)) V := by
  induction b with
  | zero => exact h
  | succ n ih =>
      intro y hy
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2
      rw [hpz]

/-- On an open set on which `g` is `C^∞`, `D_z` commutes with every iterate of `D_θ`. -/
private theorem DzDthIterCommOn_open {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- On an open set on which `g` is `C^∞`, `D_z^b` commutes with `D_θ^a`. -/
private theorem DzIterDthIterCommOn_open {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_open hV (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-- `D_z^qD_θ^p (D_z^bD_θ^a g) = D_z^{q+b}D_θ^{p+a} g` at every point of an open set on
which `g` is `C^∞`. -/
private theorem mixed_mixed_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (q p b a : ℕ)
    {z θ : ℝ} (hy : (z, θ) ∈ V) :
    Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (q + b) (p + a) g z θ := by
  have hX : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DthIter a g)) V :=
    Work.FTS.LocData.contDiffOn_DthIter hV hg a
  have hcommEq : Set.EqOn
      (Function.uncurry
        (Work.Spaces.DthIter p (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))))
      (Function.uncurry
        (Work.Spaces.DzIter b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g))))
      V := (DzIterDthIterCommOn_open hV hX b p).symm
  have h1 : Work.Spaces.DzIter q
        (Work.Spaces.DthIter p (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))) z θ
      = Work.Spaces.DzIter q
        (Work.Spaces.DzIter b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g))) z θ :=
    (DzIter_congr_of_isOpen hV hcommEq q) hy
  simp only [Work.Spaces.mixed]
  rw [h1, ← Work.Spaces.DzIter_add_right q b (Work.Spaces.DthIter p (Work.Spaces.DthIter a g)),
    Work.Spaces.DthIter_add_right p a g]

/-- The same identity on the open quadrant, in the shape used by the pointwise estimate. -/
private theorem mixed_mixed_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (q p b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (q + b) (p + a) g z θ :=
  mixed_mixed_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hg q p b a
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

/-! ## Vanishing of the integrand on the boundary of the domain -/

/-- At `sin(2θ) = 0` the `ℋ^k`-integrand vanishes for every `f`: the `1/sin(2θ)^{η/2}` of
the first sum and the `Wt = w·sin(2θ)^{-γ/2}` of the second are both `0`. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have hgam : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- At `z = 0` the `ℋ^k`-integrand vanishes for every `f`, because the radial weight
`w = (1+z)²/z²` is `0` there (Lean's totalised division). -/
private lemma HkIntegrand_apply_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hw0, zero_div, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [Work.Spaces.Wt, hw0, zero_mul, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The pointwise domination -/

/-- **Every summand of `HkIntegrand α k (D_z^bD_θ^a g)` is a summand of
`HkIntegrand α (a+b+k) g`.**  The pure `D_z`-summands of the left-hand side are the
`D_z`-shifted pure summands of the right-hand side when `a = 0`, and the mixed summands
`(D_z^{p+b}D_θ^a g · Wt)²` when `a ≥ 1`; in both cases the weight
`w/sin(2θ)^{η/2} ≤ Wt` has to be paid only when a `D_θ` falls on the datum.  The mixed
summands of the left-hand side are shifted by the commutativity of the two operators. -/
private theorem hkIntegrand_mixed_shift_aux (α : ℝ) (hα : 0 < α) (k a b : ℕ)
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
        ≤ Work.Spaces.HkIntegrand α (a + b + k) g z θ := by
  intro z hzI θ hθ
  have hz0le : (0 : ℝ) ≤ z := hzI
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α hα k (Work.Spaces.mixed b a g) hsin,
      HkIntegrand_eq_zero_of_sin α hα (a + b + k) g hsin]
  · -- the radial boundary `z = 0`: the left-hand integrand vanishes
    rcases eq_or_lt_of_le hz0le with hzo | hz
    · have h0 : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ = 0 := by
        rw [← hzo]
        exact HkIntegrand_apply_zero α k (Work.Spaces.mixed b a g) θ
      rw [h0]
      exact Work.Spaces.HkIntegrand_nonneg α (a + b + k) g z θ
    · -- the interior of the domain
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact absurd (by rw [← h]; simp) hsin
        · exact h
      have hθ1 : θ < π / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hsin
      set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
      set W : ℝ := Work.Spaces.Wt α z θ with hW
      have hHW : H ^ 2 ≤ W ^ 2 := by
        rw [hH, hW]; exact Work.Spaces.H_le_Wt α hα z θ hzI hθ
      -- The `(D_θ`-order, `D_z`-order)`-indexed building block of the two integrands.
      set T : ℕ × ℕ → ℝ := fun x =>
        if x.1 = 0 then (Work.Spaces.DzIter x.2 g z θ * H) ^ 2
        else (Work.Spaces.mixed x.2 x.1 g z θ * W) ^ 2 with hT
      have hTnn : ∀ x, 0 ≤ T x := by
        rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
      -- The index sets of the two sums of the right-hand side.
      set R1 : Finset (ℕ × ℕ) := (Finset.range (a + b + k + 1)).image (fun q => ((0 : ℕ), q))
        with hR1def
      set R2 : Finset (ℕ × ℕ) :=
        ((Finset.range (a + b + k + 1)) ×ˢ (Finset.range (a + b + k + 1))).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ a + b + k) with hR2def
      -- The index sets of the two sums of the left-hand side, shifted into the right-hand side.
      set S1 : Finset (ℕ × ℕ) := (Finset.range (k + 1)).image (fun p => (a, p + b)) with hS1def
      set S2 : Finset (ℕ × ℕ) :=
        (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)).image
            (fun x : ℕ × ℕ => (x.1 + a, x.2 + b)) with hS2def
      have hR1 : (∑ x ∈ R1, T x)
          = ∑ q ∈ Finset.range (a + b + k + 1), (Work.Spaces.DzIter q g z θ * H) ^ 2 := by
        rw [hR1def]
        have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q))
            (↑(Finset.range (a + b + k + 1)) : Set ℕ) := by
          intro x _ y _ h; simpa using h
        rw [Finset.sum_image (f := T) hinj]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        simp only [hT]; simp
      have hR2 : (∑ x ∈ R2, T x)
          = ∑ p ∈ Finset.range (a + b + k + 1), ∑ q ∈ Finset.range (a + b + k + 1),
              (if 1 ≤ p ∧ p + q ≤ a + b + k
                then (Work.Spaces.mixed q p g z θ * W) ^ 2 else 0) := by
        rw [hR2def, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        simp only [hT]
        by_cases hc : 1 ≤ p ∧ p + q ≤ a + b + k
        · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
        · rw [if_neg hc, if_neg hc]
      have hLHSunfold : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
          = (∑ p ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter p (Work.Spaces.mixed b a g) z θ * H) ^ 2)
            + ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
                (if 1 ≤ p ∧ p + q ≤ k
                  then (Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ * W) ^ 2
                  else 0) := by
        simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
      have hRHSunfold : Work.Spaces.HkIntegrand α (a + b + k) g z θ
          = (∑ q ∈ Finset.range (a + b + k + 1), (Work.Spaces.DzIter q g z θ * H) ^ 2)
            + ∑ p ∈ Finset.range (a + b + k + 1), ∑ q ∈ Finset.range (a + b + k + 1),
                (if 1 ≤ p ∧ p + q ≤ a + b + k
                  then (Work.Spaces.mixed q p g z θ * W) ^ 2 else 0) := by
        simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
      -- The first sum of the left-hand side sits on `S1`.
      have hS1 : (∑ p ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter p (Work.Spaces.mixed b a g) z θ * H) ^ 2)
          ≤ ∑ x ∈ S1, T x := by
        rw [hS1def]
        have hinj : Set.InjOn (fun p : ℕ => (a, p + b)) (↑(Finset.range (k + 1)) : Set ℕ) := by
          intro x _ y _ h; simpa using h
        rw [Finset.sum_image (f := T) hinj]
        refine Finset.sum_le_sum (fun p _ => ?_)
        simp only [hT]
        by_cases ha : a = 0
        · subst ha
          rw [if_pos rfl, Work.Spaces.mixed_zero_right,
            ← Work.Spaces.DzIter_add_right p b g]
        · rw [if_neg (by omega : ¬ a = 0)]
          have hDz : Work.Spaces.DzIter p (Work.Spaces.mixed b a g)
              = Work.Spaces.mixed (p + b) a g := by
            simp only [Work.Spaces.mixed]; rw [Work.Spaces.DzIter_add_right]
          rw [hDz]
          nlinarith [hHW, sq_nonneg (Work.Spaces.mixed (p + b) a g z θ)]
      -- The second sum of the left-hand side equals the sum on `S2`.
      have hS2 : (∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
            (if 1 ≤ p ∧ p + q ≤ k
              then (Work.Spaces.mixed q p (Work.Spaces.mixed b a g) z θ * W) ^ 2 else 0))
          = ∑ x ∈ S2, T x := by
        rw [hS2def]
        have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
            (↑(((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
              (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)) : Set (ℕ × ℕ)) := by
          intro x _ y _ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
        rw [Finset.sum_image (f := T) hinj, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        dsimp only
        by_cases hc : 1 ≤ p ∧ p + q ≤ k
        · rw [if_pos hc, if_pos hc]
          simp only [hT]
          rw [if_neg (by omega : ¬ p + a = 0)]
          rw [mixed_mixed_Q0 hg q p b a hz hθ0 hθ1]
        · rw [if_neg hc, if_neg hc]
      have hdisjS : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hS1def, Finset.mem_image] at hx1
        obtain ⟨p, _, rfl⟩ := hx1
        rw [hS2def, Finset.mem_image] at hx2
        obtain ⟨y, hy, hxy⟩ := hx2
        rw [Finset.mem_filter] at hy
        simp only [Prod.mk.injEq] at hxy
        have hy1 : 1 ≤ y.1 := hy.2.1
        omega
      have hdisjR : Disjoint R1 R2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hR1def, Finset.mem_image] at hx1
        obtain ⟨q, _, rfl⟩ := hx1
        rw [hR2def, Finset.mem_filter] at hx2
        have h := hx2.2.1
        simp only at h
        omega
      have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
        intro x hx
        rw [Finset.mem_union] at hx ⊢
        rcases hx with hx | hx
        · rw [hS1def, Finset.mem_image] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          rw [Finset.mem_range] at hp
          by_cases ha : a = 0
          · left
            rw [hR1def, Finset.mem_image]
            exact ⟨p + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
          · right
            rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
              Finset.mem_range]
            dsimp only
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
        · rw [hS2def, Finset.mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
          right
          rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          dsimp only
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      rw [hLHSunfold, hRHSunfold, ← hR1, ← hR2]
      calc _ ≤ (∑ x ∈ S1, T x) + (∑ x ∈ S2, T x) := add_le_add hS1 (le_of_eq hS2)
        _ = ∑ x ∈ S1 ∪ S2, T x := (Finset.sum_union hdisjS).symm
        _ ≤ ∑ x ∈ R1 ∪ R2, T x :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
        _ = (∑ x ∈ R1, T x) + (∑ x ∈ R2, T x) := Finset.sum_union hdisjR

/-- **The shifted `ℋ^k`-integrand of a mixed derivative** (the requested statement): for a
datum which is `C^∞` on the open quadrant and every `z ∈ [0,∞)`, `θ ∈ [0,π/2]`,

  `HkIntegrand α k (D_z^bD_θ^a g) z θ ≤ HkIntegrand α (k+a+b) g z θ`. -/
theorem HkIntegrand_mixed_shift (α : ℝ) (hα : 0 < α) (k a b : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.mixed b a g) z θ
        ≤ Work.Spaces.HkIntegrand α (k + a + b) g z θ := by
  intro z hz θ hθ
  have h := hkIntegrand_mixed_shift_aux α hα k a b hg z hz θ hθ
  rwa [show a + b + k = k + a + b from by omega] at h

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6TP.coefThGain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6TP


end Work.FTS.StrongPersist.N6TP
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux.singleSlotCutBoundMine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux

set_option maxHeartbeats 1200000

theorem singleSlotCutBoundMine {q Kf B : ℝ} {z : ℝ} {f Y : ℝ → ℝ → ℝ} {chi : ℝ → ℝ → ℝ}
    (hq0 : 0 ≤ q) (hKf0 : 0 ≤ Kf) (hB0 : 0 ≤ B) (hz : 0 < z)
    (hχsm : ∀ ζ : ℝ, ContDiff ℝ (⊤ : ℕ∞) (chi ζ))
    (hχnn : ∀ ζ θ : ℝ, 0 ≤ chi ζ θ)
    (hχle : ∀ ζ θ : ℝ, chi ζ θ ≤ 1)
    (hχone : ∀ ζ θ : ℝ, 0 < ζ → ζ ≤ θ → θ ≤ π / 2 - ζ → chi ζ θ = 1)
    (hχz0l : ∀ ζ θ : ℝ, 0 < ζ → θ ≤ ζ / 2 → chi ζ θ = 0)
    (hχz0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 ≤ θ → chi ζ θ = 0)
    (hχd0l : ∀ ζ θ : ℝ, 0 < ζ → θ < ζ / 2 → deriv (chi ζ) θ = 0)
    (hχd0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 < θ → deriv (chi ζ) θ = 0)
    (hχbd : ∀ ζ : ℝ, 0 < ζ → ∀ θ : ℝ, |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B)
    (hFcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (π / 2)))
    (hVcd : ContDiffOn ℝ 1 (fun θ => Y z θ) (Set.Ioo 0 (π / 2)))
    (hFb : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf)
    (hWq : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf)
    (hVint : MeasureTheory.IntegrableOn (fun θ => (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ4 : ζ ≤ 1 / 4) :
    |∫ θ in Work.Spaces.Iθ, chi ζ θ * ((Real.sin (2 * θ)) ^ (-q) * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ)|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  have hζ2' : 2 * ζ ≤ π / 2 := by linarith [Real.pi_gt_three, hζ4]
  have hχmid : ∀ θ ∈ Set.Ioo ζ (π / 2 - ζ), deriv (chi ζ) θ = 0 := by
    intro θ hθ
    have hev : chi ζ =ᶠ[𝓝 θ] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hχone ζ θ' hζ (le_of_lt hθ'.1) (le_of_lt hθ'.2)
    exact Work.H2.T1Q.deriv_eq_zero_of_eventuallyEq_one hev
  have hindnn : ∀ θ : ℝ, 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
      + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    linarith
  have hsd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv (chi ζ) θ|
      ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) := by
    intro θ hθ
    by_cases h1 : θ < ζ / 2
    · rw [hχd0l ζ θ hζ h1, mul_zero, abs_zero]
      exact mul_nonneg hB0 (hindnn θ)
    by_cases h2 : π / 2 - ζ / 2 < θ
    · rw [hχd0r ζ θ hζ h2, mul_zero, abs_zero]
      exact mul_nonneg hB0 (hindnn θ)
    by_cases h3 : θ ≤ 2 * ζ
    · have hA : θ ∈ Set.Ioc 0 (2 * ζ) := ⟨by linarith, h3⟩
      have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        have ha : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
          Set.indicator_of_mem hA _
        have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun _ => (1 : ℝ)) θ := by
          by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
        rw [ha]; linarith
      calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hχbd ζ hζ θ
        _ = B * 1 := by ring
        _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
            mul_le_mul_of_nonneg_left hind hB0
    · have h3' : 2 * ζ < θ := not_le.mp h3
      by_cases h4 : π / 2 - 2 * ζ < θ
      · have hA : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2) :=
          ⟨h4, by linarith [not_lt.mp h2, Real.pi_pos]⟩
        have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          have hb : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
            Set.indicator_of_mem hA _
          have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
            by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
            · simp [Set.indicator_of_mem hm]
            · simp [Set.indicator_of_notMem hm]
          rw [hb]; linarith
        calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hχbd ζ hζ θ
          _ = B * 1 := by ring
          _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
              mul_le_mul_of_nonneg_left hind hB0
      · have hmid : deriv (chi ζ) θ = 0 :=
          hχmid θ ⟨by linarith, by linarith [not_lt.mp h4]⟩
        rw [hmid, mul_zero, abs_zero]
        exact mul_nonneg hB0 (hindnn θ)
  have hFb' : ∀ θ ∈ Set.Ioo 0 (π / 2), |f z θ| ≤ Kf := fun θ hθ => hFb θ hθ.1 hθ.2
  have hWq' : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf :=
    fun θ hθ => hWq θ hθ.1 hθ.2
  have hIBP := Work.FTS.StrongPersist.N6Trans.T1SixAux.ibpCutoff_nonneg (q := q) (δ := ζ / 2)
    hq0 (χ := chi ζ) (hf := fun θ => f z θ) (hv := fun θ => Y z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos])
    (fun θ hθ => hχz0l ζ θ hζ hθ) (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hVcd
  have h := Work.H2.T1Q.slotBound_cutoff (q := q) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := chi ζ) (F := fun θ => f z θ) (V := fun θ => Y z θ)
    hKf0 hB0 hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ) hsd hFb' hWq' hVint
    hIBP.1 hIBP.2
  have hconv : (∫ θ in Work.Spaces.Iθ, chi ζ θ * ((Real.sin (2 * θ)) ^ (-q) * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ))
      = ∫ θ in Work.Spaces.Iθ, chi ζ θ * (f z θ
          * (Real.sin (2 * θ) * deriv (fun θ' => Y z θ') θ) * Y z θ
          * (Real.sin (2 * θ)) ^ (-q)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hconv]
  exact h

end Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.L12_Fstar_add_c4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-- **Additivity of `L₁₂` over `F_* + u`** at every `z ≥ 0`, for a datum that is `C^4` on the open
quadrant and lies in `ℋ⁴`. -/
theorem L12_Fstar_add_c4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 u) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z := by
  -- `C^4` on the open quadrant gives continuity there, which is all the certificates use
  have hcont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0 := hu.continuousOn
  -- the angular slice of `u`: `s > z ≥ 0`, so `s > 0` and the `HkMem`-Cauchy–Schwarz applies
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * u s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hcont hmem s
        (lt_of_le_of_lt hz hs)
  -- the density of `u`: integrable on `(0,∞)`, hence on the smaller `(z,∞)` since `z ≥ 0`
  have hdens : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K u) (Set.Ioi z) :=
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem).mono_set
      (Set.Ioi_subset_Ioi hz)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := u)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    hdens).1

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

theorem v2_L12DzIterTendsto {C0 : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hC0 : 0 ≤ C0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (F n)) Work.FTS.EllipticEst.Q0)
    (hG : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ (n : ℕ) (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (F n) z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hconv : ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a G z θ))) :
    ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0)) := by
  intro j hj z hz
  -- the pointwise bound, in the `JetBnd` package
  have hbndJet : ∀ n : ℕ, JetBnd C0 (F n) := fun n => hbnd n
  have hbndG : JetBnd C0 G :=
    JetBnd.of_tendsto hbndJet (fun b a hab => hconv b a (by omega))
  -- continuity of the density of `L₁₂`, for every datum of the slot's class
  have hcontD : ∀ f : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      JetBnd C0 f → ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0) := by
    intro f hf hb
    refine ContinuousOn.congr (s := Set.Ioi 0)
      (f := fun s => Work.Elliptic.Qang f 0 s / s)
      (g := fun s => Work.Elliptic.L12dens f s) ?_ ?_
    · intro s hs
      exact ((QangZeroDeriv_jet hC0 hf hb hs).continuousAt.div continuousAt_id
        (ne_of_gt hs)).continuousWithinAt
    · intro s _
      exact Work.Elliptic.L12dens_eq_Qang_div f s
  -- the angular-moment tower, for every datum of the slot's class
  have hkey : ∀ f : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      JetBnd C0 f →
      Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 f z) z 0 = L12jet f j z := by
    intro f hf hb
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 f z) j z 0]
    exact dzdIter_L12_jet hC0 hf hb
      (fun w hw => QangZeroDeriv_jet hC0 hf hb hw)
      (fun w hw => QangOneDeriv_jet hC0 hf hb hw)
      (fun w hw => Construction_L12_hasDerivAt_jet hC0 hb (hcontD f hf hb) hw) hj hz
  have hFL : (fun n : ℕ => Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
      = fun n : ℕ => L12jet (F n) j z := funext fun n => hkey (F n) (hF n) (hbndJet n)
  have hGL : Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0 = L12jet G j z :=
    hkey G hG hbndG
  rw [hFL, hGL]
  -- the four levels
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · -- `j = 0`: the radial dominated convergence
    change Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 G z))
    have hconvL : ∀ s : ℝ, 0 < s →
        Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (F n) s) Filter.atTop
          (nhds (Work.Elliptic.L12dens G s)) := by
      intro s hs
      have hq := (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 0) (by norm_num) hs).div_const s
      rw [show (fun n : ℕ => Work.Elliptic.Qang (F n) 0 s / s)
            = fun n : ℕ => Work.Elliptic.L12dens (F n) s from
            funext fun n => (Work.Elliptic.L12dens_eq_Qang_div (F n) s).symm,
          show Work.Elliptic.Qang G 0 s / s = Work.Elliptic.L12dens G s from
            (Work.Elliptic.L12dens_eq_Qang_div G s).symm] at hq
      exact hq
    have hmeasn : ∀ n : ℕ, AEStronglyMeasurable (fun s => Work.Elliptic.L12dens (F n) s)
        (volume.restrict (Set.Ioi z)) :=
      fun n => ((hcontD (F n) (hF n) (hbndJet n)).mono
        (Set.Ioi_subset_Ioi hz.le)).aestronglyMeasurable measurableSet_Ioi
    exact L12Tendsto_dens hC0 hbndJet hmeasn hconvL hz
  · -- `j = 1`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 0 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 0 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 0) (by norm_num) hz).neg
  · -- `j = 2`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 1 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 1 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 1) (by norm_num) hz).neg
  · -- `j = 3`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 2 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 2 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 2) (by norm_num) hz).neg

end Work.FTS_RegExport.RXT.Slots
end
