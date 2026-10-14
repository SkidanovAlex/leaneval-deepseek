import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.pinHardy
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.momentChainAe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_of_outer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "HkInt" => Work.Spaces.HkIntegrand
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## The angular weight of the mixed slots and its elementary properties -/

/-- The angular weight `sin(2θ)^{-γ}` of the mixed slots, `γ = 1 + α/10` (the square of the
angular factor of `W = w · w_θ`). -/
noncomputable def gamWt (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem sEta_contOn : ContinuousOn sEta (Set.Ioo 0 (π / 2)) := by
  rw [show sEta = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hx))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn

theorem gamWt_nonneg_Ioo (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ gamWt α θ := by
  rw [gamWt]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem gamWt_contOn (α : ℝ) : ContinuousOn (gamWt α) (Set.Ioo 0 (π / 2)) := by
  rw [show gamWt α = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hx))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn

/-- **The square of the full weight `W = w · w_θ`**: `(W α z θ)² = (w z)² sin(2θ)^{-γ}`. -/
theorem Wt_sq_eq_gamWt (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * gamWt α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, gamWt, mul_pow, h1]

/-! ## The level-`0` form of the two families of summands -/

/-- **The `D_z`-summand is `(w z)²` times its `η`-form**: the level-`0` identity
`HkIntegrand α 0 g = (w z)² · (σ θ · g²)`, `σ = sin(2θ)^{-η}`, read backwards. -/
theorem zp_id {F : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) := by
  rw [← slm_HkIntegrand_zero_profile (0 : ℝ) (Work.Spaces.DzIter i F) z θ,
    slm_HkIntegrand_zero_radial (0 : ℝ) (Work.Spaces.DzIter i F) hθ]

/-- **The mixed summand is `(w z)²` times its `γ`-form**: `(g · W)² = (w z)² · (sin(2θ)^{-γ} g²)`. -/
theorem mp_id (α : ℝ) {F : ℝ → ℝ → ℝ} (j i : ℕ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := by
  rw [mul_pow, Wt_sq_eq_gamWt α hθ]
  ring

/-! ## The integrand as a sum of `τ`-forms -/

/-- The level-`k` integrand, written as the `(w z)²`-multiple of a finite sum of the `τ`-forms
`τ θ · h z θ²` to which the slice-mass upgrade applies term by term. -/
noncomputable def pieceSum (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 *
          (if 1 ≤ i ∧ i + j ≤ k then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0)

/-- **The integrand is `pieceSum`.** -/
theorem HkInt_eq_pieceSum (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Iθ) :
    HkInt α k F z θ = pieceSum α k F z θ := by
  simp only [Work.Spaces.HkIntegrand, pieceSum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => zp_id i hθ
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]
      exact mp_id α j i hθ
    · rw [if_neg hc, if_neg hc, mul_zero]

/-- At `z = 0` the radial weight vanishes, so the whole integrand does. -/
theorem HkInt_zero (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) : HkInt α k F 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]
  simp

/-! ## The angular interval rewriting -/

/-- The two restricted measures on the angular intervals agree (`(0,π/2)` and `[0,π/2]`
differ by two null points). -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))

/-! ## Honest integrability of a `τ`-form from finiteness of its mass -/

theorem integrableOn_of_lt_top {g : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z)
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2)))
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (h : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤) :
    IntegrableOn (fun θ => τ θ * (g z θ) ^ 2) (Set.Ioo 0 (π / 2)) := by
  have hcont : ContinuousOn (fun θ => τ θ * (g z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
    hτc.mul ((hg.curry_θ hz).continuousOn.pow 2)
  have hnnae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))]
      fun θ => τ θ * (g z θ) ^ 2 := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))), 0 ≤ τ θ * (g z θ) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => mul_nonneg (hτ θ hθ) (sq_nonneg _)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (hcont.aestronglyMeasurable measurableSet_Ioo) hnnae).mp (ne_of_lt h)

/-! ## Finite sums of integrable functions -/

theorem integrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {μ : Measure ℝ}
    (h : ∀ i ∈ s, Integrable (f i) μ) : Integrable (fun θ => ∑ i ∈ s, f i θ) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_zero ℝ ℝ μ)
  | insert a s ha ih =>
      have hsum : (fun θ : ℝ => ∑ i ∈ insert a s, f i θ)
          = fun θ => f a θ + ∑ i ∈ s, f i θ := by
        funext θ
        exact Finset.sum_insert ha
      rw [hsum]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The pointwise dominations by the level-`(k+1)` integrand -/

/-- For `z > 0` the `η`-form of the `i`-th `D_z`-derivative is at most the level-`(k+1)`
integrand, as soon as `i ≤ k + 1`. -/
theorem sEta_mul_sq_le_HkInt {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {i : ℕ} (hi : i ≤ k + 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2 ≤ HkInt α (k + 1) F z θ := by
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hnn : 0 ≤ sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2 :=
    mul_nonneg (sEta_nonneg_Ioo hθ) (sq_nonneg _)
  calc sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2
      = 1 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) := (one_mul _).symm
    _ ≤ (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (slm_one_le_w hz)) hnn
    _ = (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        (zp_id i hθI).symm
    _ ≤ HkInt α (k + 1) F z θ := Work.Spaces.sq_le_HkIntegrand_z α (k + 1) F z θ i hi

/-- For `z > 0` the `γ`-form of `D_z^j D_θ^i F` is at most the level-`(k+1)` integrand, as soon
as `1 ≤ i` and `i + j ≤ k + 1`. -/
theorem gamWt_mul_sq_le_HkInt {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k + 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 ≤ HkInt α (k + 1) F z θ := by
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hnn : 0 ≤ gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 :=
    mul_nonneg (gamWt_nonneg_Ioo α hθ) (sq_nonneg _)
  calc gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2
      = 1 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := (one_mul _).symm
    _ ≤ (Work.Spaces.w z) ^ 2 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (slm_one_le_w hz)) hnn
    _ = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := (mp_id α j i hθI).symm
    _ ≤ HkInt α (k + 1) F z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α (k + 1) F z θ i j hi hij

/-! ## The outer bounds of the two families, from the level-`(k+1)` bound -/

/-- The outer bound of the `η`-form of `D_z^i F`, from the level-`(k+1)` outer bound. -/
theorem zOuter0 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k + 1) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfin1 ENNReal.ofReal_lt_top)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall fun z hz => lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun θ hθ =>
          ENNReal.ofReal_le_ofReal (sEta_mul_sq_le_HkInt (α := α) (k := k) (F := F)
            hi hz hθ)
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_Iθ_eq_Ioo
          (fun θ => ENNReal.ofReal (HkInt α (k + 1) F z θ))).symm

/-- The outer bound of the `η`-form of the radial derivative `z ∂_z (D_z^i F) = D_z^{i+1} F`. -/
theorem zOuter1 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) ^ 2)) < ⊤ := by
  have hDz : ∀ z θ : ℝ, z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ
      = Work.Spaces.DzIter (i + 1) F z θ := fun z θ => rfl
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) ^ 2))
      = (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter (i + 1) F z θ) ^ 2)) from by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact lintegral_congr fun θ => by rw [hDz z θ]]
  exact zOuter0 (k := k) hfin1 (i := i + 1) (by omega)

/-- The outer bound of the `γ`-form of `D_z^j D_θ^i F`. -/
theorem mOuter0 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k + 1) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfin1 ENNReal.ofReal_lt_top)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall fun z hz => lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun θ hθ =>
          ENNReal.ofReal_le_ofReal (gamWt_mul_sq_le_HkInt (α := α) (k := k) (F := F)
            hi (by omega) hz hθ)
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_Iθ_eq_Ioo
          (fun θ => ENNReal.ofReal (HkInt α (k + 1) F z θ))).symm

/-- The outer bound of the `γ`-form of the radial derivative
`z ∂_z (D_z^j D_θ^i F) = D_z^{j+1} D_θ^i F`. -/
theorem mOuter1 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ
          * (z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2)) < ⊤ := by
  have hDz : ∀ z θ : ℝ, z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ
      = Work.Spaces.mixed (j + 1) i F z θ := fun z θ => rfl
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2))
      = (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed (j + 1) i F z θ) ^ 2)) from by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact lintegral_congr fun θ => by rw [hDz z θ]]
  exact mOuter0 (k := k) hfin1 (i := i) (j := j + 1) hi (by omega)

/-! ## The every-`z` finiteness of the two families

These are the two instantiations of the general slice-mass upgrade `piece_mass_lt_top`: the datum
`g` is one of the weighted derivatives, the weight `τ` one of the two angular weights, and the
two outer bounds come from `zOuter0`/`zOuter1` resp. `mOuter0`/`mOuter1`. -/

theorem zMass_lt_top {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2)) < ⊤ :=
  piece_mass_lt_top (hg := hF.DzIter i) (hτc := sEta_contOn)
    (hτ := fun _ hθ => sEta_nonneg_Ioo hθ) (zOuter0 hfin1 (by omega)) (zOuter1 hfin1 hi)

theorem mMass_lt_top {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)) < ⊤ :=
  piece_mass_lt_top (hg := hF.mixed j i) (hτc := gamWt_contOn α)
    (hτ := fun _ hθ => gamWt_nonneg_Ioo α hθ)
    (mOuter0 hfin1 hi (by omega)) (mOuter1 hfin1 hi hij)

/-! ## The main transfer -/

theorem HkMem_of_outer {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) ≤ ENNReal.ofReal C₀)
    (hslmeas1 : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas1 : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) ≤ ENNReal.ofReal C₁) :
    Work.Spaces.HkMem α k F := by
  -- the two families of `τ`-forms are honest at every `z > 0`
  have hZ : ∀ i ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
    fun i hi z hz => integrableOn_of_lt_top (hsm.DzIter i) hz sEta_contOn
      (fun _ hθ => sEta_nonneg_Ioo hθ) (zMass_lt_top hsm hfin1 hi z hz)
  have hM : ∀ i j, 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)
        (Set.Ioo 0 (π / 2)) :=
    fun i j hi hij z hz => integrableOn_of_lt_top (hsm.mixed j i) hz (gamWt_contOn α)
      (fun _ hθ => gamWt_nonneg_Ioo α hθ) (mMass_lt_top hsm hfin1 hi hij z hz)
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes and the integrand is identically zero
      rw [show (fun θ : ℝ => HkInt α k F z θ) = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact HkInt_zero α k F θ]
      exact integrableOn_zero
    · -- `z > 0`: `pieceSum` is a finite sum of honest `τ`-forms
      have hA : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        integrable_finset_sum' _ fun i hi =>
          (hZ i (by have h := Finset.mem_range.mp hi; omega) z hzpos).const_mul _
      have hterm : ∀ i j : ℕ,
          Integrable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            (if 1 ≤ i ∧ i + j ≤ k
              then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
            (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) := by
        intro i j
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · have heq : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
              (if 1 ≤ i ∧ i + j ≤ k
                then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
              = fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
                  (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := by
            funext θ
            rw [if_pos hc]
          rw [heq]
          exact (hM i j hc.1 (by omega) z hzpos).const_mul _
        · have heq : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
              (if 1 ≤ i ∧ i + j ≤ k
                then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
              = fun _ : ℝ => (0 : ℝ) := by
            funext θ
            rw [if_neg hc, mul_zero]
          rw [heq]
          exact integrable_zero ℝ ℝ _
      have hB : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
            ∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 *
                (if 1 ≤ i ∧ i + j ≤ k
                  then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        integrable_finset_sum' _ fun i hi => integrable_finset_sum' _ fun j hj => hterm i j
      have hsum : Integrable (fun θ : ℝ => pieceSum α k F z θ)
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) := by
        simp only [pieceSum]
        exact hA.add hB
      have hHk : Integrable (fun θ : ℝ => HkInt α k F z θ)
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        hsum.congr (by
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact (HkInt_eq_pieceSum α k (F := F) (z := z) (θ := θ)
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).symm)
      show Integrable (fun θ : ℝ => HkInt α k F z θ) (MeasureTheory.volume.restrict Iθ)
      rw [← restrict_Iθ_eq_restrict_Ioo]
      exact hHk
  · -- the outer conjunct: a.e. integrability, upgraded from `(0,∞)` to `[0,∞)`
    have houter : IntegrableOn (fun z => ∫ θ in Iθ, HkInt α k F z θ) (Set.Ioi 0) :=
      (Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral_k hC₀ hslmeas hfin0 hmeas).2
    refine houter.congr_set_ae ?_
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.GroupCmpK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `w(z) ≠ 0` for `z > 0`. -/
private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  rw [Work.Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))

/-- **The comparison of the `j`-th slice group.**  For `z > 0` the `θ`-integral of the `j`-th
slice group of the quotient `Φ/sin 2θ` is integrable and bounded by a universal multiple of the
`θ`-integral of the `j`-th slice group of `∂_θΦ`. -/
theorem groupCmpK (k : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen Φ →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2))) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
    ∀ z : ℝ, 0 < z → z ∈ Work.Spaces.Iz → ∀ j : ℕ, j ≤ k →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j
          (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j
            (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ)
          ≤ K * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j
              (Work.Spaces.pth Φ) z θ) := by
  obtain ⟨Cη, hCηpos, hetab⟩ := Work.FTS.H2.DivQ.sliceBoundEta
  obtain ⟨Cm, hCmpos, hmixb⟩ := mixedSlotBoundGenK k
  refine ⟨Cη + Cm * (k : ℝ), ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg hCηpos (mul_nonneg hCmpos.le (Nat.cast_nonneg k))
  · intro α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j hj
    have hwz : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hzpos
    have hwz2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    obtain ⟨hsmj, ht0j, ht1j, hDenηj, hDenγj⟩ := sliceData hSO hsl ht0 ht1 hmem hα hz hzpos j hj
    set U : ℝ → ℝ → ℝ := fun z' θ' => Φ z' θ' / Real.sin (2 * θ') with hUdef
    -- ## the pure summand
    have hPint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j U z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
      obtain ⟨hI, -⟩ := hetab (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hsmj ht0j ht1j hDenηj
      refine (hI.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Pslot_eq j Φ hθ)] with θ hθ
      exact hθ.symm
    have hPbnd : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      obtain ⟨-, hB⟩ := hetab (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hsmj ht0j ht1j hDenηj
      have hae : (fun θ : ℝ => (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
        filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Pslot_eq j Φ hθ)] with θ hθ
        exact hθ
      have hze : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Zdata_eq j Φ hSO hzpos hθ hwz)] with θ hθ
        rw [hθ]
        field_simp
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (Work.Spaces.w z) ^ 2 * (Cη * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            mul_le_mul_of_nonneg_left hB hwz2
        _ = Cη * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by ring
        _ = Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
            rw [MeasureTheory.integral_const_mul]
        _ = Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            rw [MeasureTheory.integral_congr_ae hze]
    -- ## the mixed summands
    have hMint : ∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
        Work.Spaces.Iθ := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      have hik : i ≤ k := by omega
      obtain ⟨hI, -⟩ := hmixb α (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hα hα1 hsmj ht0j ht1j
        hDenηj i hi1 hik (fun m hm1 hmi => hDenγj m hm1 (by omega))
      refine (hI.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Mslot_eq α hα i j Φ hSO hzpos hθ)]
        with θ hθ
      exact hθ.symm
    have hMbnd : ∀ i ∈ Finset.Icc 1 (k - j),
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
          ≤ Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      have hik : i ≤ k := by omega
      obtain ⟨-, hB⟩ := hmixb α (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hα hα1 hsmj ht0j ht1j
        hDenηj i hi1 hik (fun m hm1 hmi => hDenγj m hm1 (by omega))
      have hae : (fun θ : ℝ => (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((Work.Elliptic.Dth1Iter i
                (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Mslot_eq α hα i j Φ hSO hzpos hθ)]
          with θ hθ
        exact hθ
      have hZ : (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Zdata_eq j Φ hSO hzpos hθ hwz)] with θ hθ
        exact hθ
      have hM : ∀ m ∈ Finset.Icc 1 i,
          (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (fun θ' : ℝ =>
              deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            = ((Work.Spaces.w z) ^ 2)⁻¹ * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
        intro m hm
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Mdata_eq α hα m j Φ hSO hzpos hθ hwz)] with θ hθ
        exact hθ
      have hsum : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
              Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ∑ m ∈ Finset.Icc 1 i,
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
              * Work.Spaces.Wt α z θ) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m hm => hM m hm)
      have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hB hwz2) ?_
      have hgoal : (Work.Spaces.w z) ^ 2 * (Cm *
            ((∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
                    Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
          = Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
        rw [hZ, hsum]
        refine mul_left_cancel₀ (ne_of_gt hCmpos) ?_
        field_simp
      exact hgoal.le
    -- ## the slice group comparison
    -- ## the slice group comparison
    have hZint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j
        (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_zSummand α k hSO.pth hmem j hj hz
    have hMintR : ∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ
          * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      exact Work.FTS.EllipticEst.integrableOn_mixedSummand α k hSO.pth hmem i j hi1
        (by omega) hz
    have hvalL : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j U z θ)
        = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m U z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      have hsg : (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j U z θ)
          = fun θ : ℝ => (Work.Spaces.DzIter j U z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        funext θ
        simp only [Work.FTS.EllipticEst.sliceGroup]
      rw [hsg, MeasureTheory.integral_add hPint (MeasureTheory.integrable_finsetSum _ hMint),
        MeasureTheory.integral_finsetSum _ hMint]
    have hvalR : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ)
        = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      have hsg : (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j
            (Work.Spaces.pth Φ) z θ)
          = fun θ : ℝ => (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        funext θ
        simp only [Work.FTS.EllipticEst.sliceGroup]
      rw [hsg, MeasureTheory.integral_add hZint (MeasureTheory.integrable_finsetSum _ hMintR),
        MeasureTheory.integral_finsetSum _ hMintR]
    have h2 : (∑ i ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2))
        ≤ Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hMnn : ∀ m ∈ Finset.Icc 1 (k - j), 0 ≤ (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) :=
        fun m _ => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hinner : ∀ i ∈ Finset.Icc 1 (k - j),
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ Cm * ((∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
        intro i hi
        have h3 := hMbnd i hi
        have hsub : Finset.Icc 1 i ⊆ Finset.Icc 1 (k - j) := fun m hm => by
          obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
          exact Finset.mem_Icc.mpr ⟨hm1, by have := (Finset.mem_Icc.mp hi).2; omega⟩
        have h4 : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
            ≤ ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hMnn m ‹_›)
        exact h3.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h4) hCmpos.le)
      calc (∑ i ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2))
          ≤ ∑ _i ∈ Finset.Icc 1 (k - j), Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := Finset.sum_le_sum hinner
        _ = ((Finset.Icc 1 (k - j)).card : ℝ) * (Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
            have hXnn : 0 ≤ (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
                + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                      * Work.Spaces.Wt α z θ) ^ 2) := add_nonneg hZnn (Finset.sum_nonneg hMnn)
            have hcard : ((Finset.Icc 1 (k - j)).card : ℝ) ≤ (k : ℝ) := by
              have h1 : (Finset.Icc 1 (k - j)).card ≤ k := by
                rw [Nat.card_Icc]
                omega
              exact_mod_cast h1
            have hstep : ((Finset.Icc 1 (k - j)).card : ℝ) * Cm ≤ Cm * (k : ℝ) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left hcard hCmpos.le
            nlinarith [hstep, hXnn]
    refine ⟨hPint.add (MeasureTheory.integrable_finsetSum _ hMint), ?_⟩
    rw [hvalL, hvalR]
    have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hMnn : 0 ≤ ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) :=
      Finset.sum_nonneg fun m _ => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hK' : Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
        ≤ (Cη + Cm * (k : ℝ)) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      nlinarith [hZnn, hMnn, hCηpos, hCmpos, Nat.cast_nonneg (α := ℝ) k]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m U z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2)) := add_le_add hPbnd h2
      _ ≤ (Cη + Cm * (k : ℝ)) * ((∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := hK'
end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAuxB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine
namespace CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The θ-slice bridge -/

/-- Off the support window of `χ k` the derivative of `χ k` vanishes (the cut-off is locally
zero there). -/
lemma deriv_chi_eq_zero_of_supp {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {z : ℝ} (hz : 0 < z)
    (hout : z < cA k ∨ cB k < z) : deriv (χ k) z = 0 := by
  have hev : χ k =ᶠ[𝓝 z] fun _ : ℝ => 0 := by
    rcases hout with h | h
    · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) (cA k) from ⟨hz, h⟩)]
        with y hy
      exact hχ.supp k y hy.1 (Or.inl hy.2.le)
    · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (cB k) (2 * z - cB k)
          from ⟨h, by linarith⟩)] with y hy
      exact hχ.supp k y (by linarith [hy.1, cB_pos k]) (Or.inr hy.1.le)
  rw [hev.deriv_eq, deriv_const]

lemma bridge_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} (θ : ℝ) :
    (∫ z in Work.Spaces.Iz, cutRho (z, θ) * χ k z * cutXi G (z, θ) * cutD2 G (z, θ))
      = Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ)) := by
  have hb := Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
    (fun z => cutRho (z, θ) * χ k z * cutXi G (z, θ) * cutD2 G (z, θ))
    (fun z hz hout => by
      have hχz : χ k z = 0 := hχ.supp k z hz
        (hout.elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
      simp [hχz])
  rw [hb, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun z _ => ?_)
  simp only [cutRho]
  ring

lemma bridge_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} (θ : ℝ) :
    (∫ z in Work.Spaces.Iz,
        (z * deriv (χ k) z) * cutRho (z, θ) * cutPs G (z, θ) * cutD2 G (z, θ))
      = Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ)) := by
  have hb := Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
    (fun z => (z * deriv (χ k) z) * cutRho (z, θ) * cutPs G (z, θ) * cutD2 G (z, θ))
    (fun z hz hout => by
      have hdχ : deriv (χ k) z = 0 := deriv_chi_eq_zero_of_supp hχ k hz hout
      simp [hdχ])
  rw [hb, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun z _ => ?_)
  simp only [cutRho]
  ring

end CutBk
end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.weakSolExists_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 3200000

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR


end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.QmSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Filter Topology

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

/-- The Gegenbauer family is of class `C⁸` (the order used by `QmSmooth`; the version
`contDiff_gC` in `Gegenbauer.gC_ode` gives only `C³`).  Same two-step induction as there, run at
order `8`: the recurrence expresses `gC (n+2)` by `mul`, `sub` and division by the constant
`n+2`, all of which preserve the order. -/
theorem contDiff_gC_eight : ∀ n : ℕ, ContDiff ℝ 8 (Work.FTS.PhiStar.Gegenbauer.gC n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x
      * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
      - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-- `eFam m = cos θ · gC (2m+1) (sin θ)` is of class `C⁸`. -/
theorem contDiff_eFam_eight (m : ℕ) :
    ContDiff ℝ 8 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  show ContDiff ℝ 8 (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.contDiff_cos.mul ((contDiff_gC_eight (2 * m + 1)).comp Real.contDiff_sin)

/-- `s2 θ = sin 2θ` is of class `C⁸`. -/
theorem contDiff_s2_eight : ContDiff ℝ 8 Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl]
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- `sin 2θ` does not vanish on `(0, π/2)`, so the defining quotient of `Qm m` is legitimate
there. -/
theorem s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  refine ne_of_gt ?_
  rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem QmSmooth :
    (∀ m : ℕ, ContDiffOn ℝ 8 (Work.FTS.PhiStar.FlatWAux.Qm m) (Set.Ioo 0 (Real.pi / 2))) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Work.FTS.PhiStar.FlatWAux.Qm 0 θ = 3 / 2) ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        iteratedDeriv r (Work.FTS.PhiStar.FlatWAux.Qm 0) θ = 0) := by
  have hs2ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Construction.s2 θ ≠ 0 :=
    fun θ hθ => s2_ne_zero_of_mem_Ioo hθ
  -- the `m = 0` mode is the constant `3/2` on the open interval
  have hconst : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.PhiStar.FlatWAux.Qm 0 θ = 3 / 2 := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have heFam : Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = Real.cos θ * (3 * Real.sin θ) := by
      show Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * 0 + 1) (Real.sin θ)
        = Real.cos θ * (3 * Real.sin θ)
      rw [show (2 * 0 + 1 : ℕ) = 1 from rfl,
        show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    show Work.FTS.PhiStar.Gegenbauer.eFam 0 θ / Work.Construction.s2 θ = 3 / 2
    rw [heFam, show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl, Real.sin_two_mul]
    have hne : (2 : ℝ) * Real.sin θ * Real.cos θ ≠ 0 := by positivity
    field_simp
  refine ⟨?_, hconst, ?_⟩
  · intro m
    have hmain : ContDiffOn ℝ 8 (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
        / Work.Construction.s2 θ) (Set.Ioo 0 (Real.pi / 2)) :=
      ((contDiff_eFam_eight m).contDiffOn).div contDiff_s2_eight.contDiffOn hs2ne
    show ContDiffOn ℝ 8 (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      / Work.Construction.s2 θ) (Set.Ioo 0 (Real.pi / 2))
    exact hmain
  · intro r hr θ hθ
    -- on the neighbourhood `(0, π/2)` of `θ`, the function `Qm 0` is the constant `3/2`
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have heq : Work.FTS.PhiStar.FlatWAux.Qm 0 =ᶠ[𝓝 θ] (fun _ : ℝ => (3 : ℝ) / 2) :=
      Filter.eventuallyEq_of_mem hmem (fun y hy => hconst y hy)
    have h1 : iteratedDeriv r (Work.FTS.PhiStar.FlatWAux.Qm 0) θ
        = iteratedDeriv r (fun _ : ℝ => (3 : ℝ) / 2) θ :=
      (heq.iteratedDeriv r).eq_of_nhds
    rw [h1, iteratedDeriv_const]
    simp [Nat.one_le_iff_ne_zero.mp hr]

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ModeMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

noncomputable section

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeMajorant`

The `m`-series of the error term of the flat `W`-expansion, with the three `ψ`-dependent
constants (`Cd` for the coefficient decay, `CRG` for the rescaled radial bound, `CQ` for the
angular mode bound) stripped off, is summable with a bound proportional to `Cd · CRG · CQ`.

Writing `λ_m = lam m = 2m(2m+5)` and `q_m = √(2m+1)`, the `m`-th term of the series is

`Cd / (λ_m q_m) · λ_m^{-J} · (CRG / λ_m) · (CQ · (2m+1)²)`
  `= Cd · CRG · CQ · λ_m^{-(J+2)} · q_m^{-1} · (2m+1)²`,

i.e. `Cd·CRG·CQ` times the *shape function*

`F m = (λ_m √(2m+1))⁻¹ · (λ_m⁻¹)^J · λ_m⁻¹ · (2m+1)²`,

which is what we define below.  Since `λ_m ≥ 4m²` and `(2m+1)² ≤ 9m²` for `m ≥ 1`, and `J = 8`,

`F m = (2m+1)² / (λ_m^10 · √(2m+1)) ≤ 9m² / (4m²)^10 ≤ ((m+1)²)⁻¹`   (`m ≥ 1`),

so `F` is dominated by the summable comparison series `Σ_m ((m+1)²)⁻¹`; the constant of the
statement is then `K = ∑' m, F m` (the supremum, not a numerical value, so no sharp constant is
needed anywhere).  The term `m = 0` contributes `0` because `λ_0 = 0`.
-/

/-- The shape of the `m`-th term of the mode majorant, with the constants `Cd, CRG, CQ`
stripped off. -/
private def F (m : ℕ) : ℝ :=
  (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
    * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (2 * (m : ℝ) + 1) ^ 2

/-- `lam m = 2m(2m+5)` is nonnegative. -/
private lemma lam_nonneg_prv (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

/-- The shape function is nonnegative. -/
private lemma F_nonneg (m : ℕ) : 0 ≤ F m := by
  have hA : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg_prv m
  simp only [F]
  positivity

/-- At `m = 0` the eigenvalue vanishes and the term is `0`. -/
private lemma F_zero : F 0 = 0 := by
  simp only [F, J, Work.FTS.PhiStar.Gegenbauer.lam]
  norm_num

/-- The basic lower bound `4m² ≤ λ_m` for `m ≥ 1`. -/
private lemma four_mul_sq_le_lam {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith

/-- For `m ≥ 1` the shape function is bounded by `((m+1)²)⁻¹`. -/
private lemma F_le_pos {m : ℕ} (hm : 1 ≤ m) : F m ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hMnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hA4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := four_mul_sq_le_lam hm
  have hS1 : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hc : (2 * (m : ℝ) + 1) ^ 2 ≤ 9 * (m : ℝ) ^ 2 := by nlinarith
  -- the term is `(2m+1)² / (λ_m^10 √(2m+1))`
  have hF : F m = (2 * (m : ℝ) + 1) ^ 2
      / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    simp only [F, J]
    rw [mul_inv, inv_pow]
    ring_nf
  rw [hF]
  -- the denominator is at least `(4m²)^10`
  have hden : (4 * (m : ℝ) ^ 2) ^ 10 * 1
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h4 : (4 * (m : ℝ) ^ 2) ^ 10 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hA4 10
    have h5 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := by positivity
    calc (4 * (m : ℝ) ^ 2) ^ 10 * 1 = (4 * (m : ℝ) ^ 2) ^ 10 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := h4
      _ = (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hS1 h5
  have hstep1 : (2 * (m : ℝ) + 1) ^ 2
        / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) :=
    div_le_div₀ (by positivity) hc (by positivity) hden
  have hstep2' : 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
    have ha2 : (9 * (m : ℝ) ^ 2) * ((m : ℝ) + 1) ^ 2
        ≤ (9 * (m : ℝ) ^ 2) * (4 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    have hpow : (4 * (m : ℝ) ^ 2) ^ 10 = 4 ^ 10 * (m : ℝ) ^ 20 := by ring
    have hM20 : (m : ℝ) ^ 4 ≤ (m : ℝ) ^ 20 := pow_le_pow_right₀ h1 (by norm_num)
    have ha4 : 9 * (m : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) ≤ 4 ^ 10 * (m : ℝ) ^ 20 := by
      have h3 : 9 * (m : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) = 36 * (m : ℝ) ^ 4 := by ring
      rw [h3]
      nlinarith [hM20, pow_nonneg hMnn 4]
    rw [hpow]
    linarith [ha2, ha4]
  have hstep2 : 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
    simpa only [one_div] using hstep2'
  linarith [hstep1, hstep2]

/-- The shape function is bounded by `((m+1)²)⁻¹` for every `m`. -/
private lemma F_le (m : ℕ) : F m ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [F_zero]
    norm_num
  · exact F_le_pos hm

/-- The comparison series `Σ_m ((m+1)²)⁻¹` is summable. -/
private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-- The shape function is summable. -/
private lemma summable_F : Summable F :=
  Summable.of_nonneg_of_le F_nonneg F_le summable_inv_sq_shift

/-- The `m`-th term of the majorant is `Cd·CRG·CQ` times the shape function. -/
private lemma term_eq (Cd CRG CQ : ℝ) (m : ℕ) :
    Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
        * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
        * (CQ * (2 * (m : ℝ) + 1) ^ 2)
      = Cd * CRG * CQ * F m := by
  simp only [F, J, div_eq_mul_inv]
  ring

theorem ModeMajorant : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (Cd CRG CQ : ℝ), 0 ≤ Cd → 0 ≤ CRG → 0 ≤ CQ →
      Summable (fun m : ℕ =>
          Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CQ * (2 * (m : ℝ) + 1) ^ 2)) ∧
      (∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CQ * (2 * (m : ℝ) + 1) ^ 2))
        ≤ K * Cd * CRG * CQ := by
  refine ⟨∑' m : ℕ, F m, tsum_nonneg F_nonneg, ?_⟩
  intro Cd CRG CQ _ _ _
  have hEq : ∀ m : ℕ,
      Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CQ * (2 * (m : ℝ) + 1) ^ 2)
        = Cd * CRG * CQ * F m := fun m => term_eq Cd CRG CQ m
  constructor
  · exact (summable_F.mul_left (Cd * CRG * CQ)).congr (fun m => (hEq m).symm)
  · rw [tsum_congr hEq, tsum_mul_left]
    have hcomm : Cd * CRG * CQ * (∑' m : ℕ, F m)
        = (∑' m : ℕ, F m) * Cd * CRG * CQ := by ring
    rw [hcomm]

end

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false

/-- The `m`-th coefficient of the eigenfunction series of `chia ψ j`, i.e.
`bco ψ j m = bmode m ψ · (lam m)⁻¹ ^ j`.  For `j ≥ 1` the `m = 0` coefficient vanishes
(`lam 0 = 0`), and for `j = 0` the series is the `eFam`-expansion of `ψ` itself. -/
def bco (ψ : ℝ → ℝ) (j m : ℕ) : ℝ :=
  Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j

/-- The `j = 0` coefficient is the `bmode` coefficient of `ψ`. -/
@[simp] theorem bco_zero (ψ : ℝ → ℝ) (m : ℕ) :
    bco ψ 0 m = Work.FTS.PhiStar.Series.bmode m ψ := by
  simp only [bco, pow_zero, mul_one]

/-- The `m = 0` coefficient vanishes for `j ≥ 1`, because `lam 0 = 0`. -/
theorem bco_apply_zero (ψ : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) : bco ψ j 0 = 0 := by
  have hlam : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    norm_num
  simp only [bco, hlam, inv_zero, zero_pow (by omega : j ≠ 0), mul_zero]

/-- On the open interval, `chia ψ j` (`j ≥ 1`) is the `eFam`-series with coefficients
`bco ψ j`. -/
theorem chia_eq_tsum_bco (ψ : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.PhiStar.FlatWAux.chia ψ j θ
      = ∑' m : ℕ, bco ψ j m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
  simpa only [bco] using Work.FTS.PhiStar.FlatWAux.chia_eq_tsum ψ k hθ

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm`

Absolute summability of the resummed angular series `Σ_m b_m λ_m^{-j} Q_m(θ)`,
`b_m = bmode m ψ`, `λ_m = lam m = 2m(2m+5)`, `Q_m = eFam m / sin 2θ`, for `j ≥ 1` and
`θ ∈ (0, π/2)`.

The three inputs are the coefficient decay `hdec`, the angular growth `hgr` and the vanishing
`m = 0` coefficient `hb0`.

The proof reduces to the already established summability of `Σ_m (b_m/λ_m) e_m(θ)` with a
summable majorant (`Series.Deleg.mode_series_summable`, whose growth hypothesis `(m+1)^{3/2}`
is implied by the linear growth `2m+1` used here), together with the elementary observation
that for `m ≥ 1` the reciprocal power `λ_m^{-j}` (`j ≥ 1`) is dominated by `λ_m^{-1}`: the
fact that `Q_m = e_m / sin 2θ` only contributes the constant factor `(sin 2θ)^{-1}`.
-/

/-- On the open interval the divisor `sin 2θ` of the divided angular mode is positive. -/
private lemma s2_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_pos
    (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

/-- The eigenvalue `λ_m = 2m(2m+5)` is positive for `m ≥ 1`. -/
private lemma lam_pos_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (0 : ℝ) < (m : ℝ) := by linarith
  have h3 : (0 : ℝ) < 2 * (m : ℝ) + 5 := by linarith
  have h := mul_pos (mul_pos two_pos h2) h3
  simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using h

/-- The eigenvalue `λ_m = 2m(2m+5)` is at least `1` for `m ≥ 1`. -/
private lemma one_le_lam_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4 : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h5 : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by linarith
  have h6 : (0 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h' : (1 : ℝ) ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5) :=
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * (m : ℝ)) * (2 * (m : ℝ) + 5) := mul_le_mul h4 h5 (by norm_num) h6
  simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using h'

/-- The linear growth hypothesis `|e_m| ≤ C (2m+1)` implies the growth `|e_m| ≤ 3C (m+1)^{3/2}`
used by `Series.Deleg.mode_series_summable`. -/
private lemma eFam_growth_three_halves {Cg : ℝ} (hCg : 0 < Cg)
    (hgr : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ 3 * Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
  intro m θ' hθ'
  have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpow : (2 * (m : ℝ) + 1) ≤ 3 * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
    have h1 : ((m : ℝ) + 1) ^ (1 : ℝ) ≤ ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
    rw [Real.rpow_one] at h1
    nlinarith
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ Cg * (2 * (m : ℝ) + 1) := hgr m θ' hθ'
    _ ≤ Cg * (3 * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hCg)
    _ = 3 * Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by ring

theorem summable_bmode_lam_inv_pow_Qm (ψ : ℝ → ℝ) (θ : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1)) :
    Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * Work.FTS.PhiStar.FlatWAux.Qm m θ) := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  -- the summable majorant of the mode series `Σ_m (b_m/λ_m) e_m(θ)`
  obtain ⟨M, hMnn, hMsum, hMbd⟩ :=
    (Work.FTS.PhiStar.Series.Deleg.mode_series_summable ψ ⟨Cd, hCd, hdec⟩
      ⟨3 * Cg, by linarith, eFam_growth_three_halves hCg hgr⟩).1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs2 : 0 < Work.Construction.s2 θ := s2_pos_of_mem_Ioo hθ
  refine Summable.of_norm_bounded (g := fun m : ℕ => M m / Work.Construction.s2 θ)
    (hMsum.div_const (Work.Construction.s2 θ)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    simp only [zero_mul, abs_zero]
    exact div_nonneg (hMnn 0) (le_of_lt hs2)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lam_pos_of_one_le hm1
    have hinvnn : 0 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ :=
      le_of_lt (inv_pos.mpr hLpos)
    -- `λ_m^{-j} ≤ λ_m^{-1}` for `j ≥ 1`
    have hpowle : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := by
      have h := pow_le_pow_of_le_one hinvnn
        (inv_le_one_of_one_le₀ (one_le_lam_of_one_le hm1)) hj
      simpa using h
    have hMstep : |Work.FTS.PhiStar.Series.bmode m ψ
          * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M m := by
      have h := hMbd m θ hθI
      rwa [div_eq_mul_inv] at h
    calc |Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        = |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          simp only [Work.FTS.PhiStar.FlatWAux.Qm, abs_mul, abs_pow, abs_div,
            abs_of_nonneg hinvnn, abs_of_pos hs2]
          ring
      _ ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs2)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowle (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.FTS.PhiStar.Series.bmode m ψ * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hinvnn]
      _ ≤ M m / Work.Construction.s2 θ :=
          div_le_div_of_nonneg_right hMstep (le_of_lt hs2)

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.NodeAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.NodeAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm
local notation "lam" => Work.FTS.PhiStar.Gegenbauer.lam
local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-! ## Uniform bounds on the mode coefficients -/

lemma lam_eq (m : ℕ) : lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := by
  rw [Work.FTS.PhiStar.Gegenbauer.lam]

lemma eNorm_ge_one (m : ℕ) : 1 ≤ eNorm m := by
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith

/-- The arithmetic core: `(1+λ_m)𝔄_m` is comparable to `(4m+5)²m` (the quotient tends to `1/4`;
`4` is a generous constant). -/
lemma arith_ratio {m : ℕ} (hm : 1 ≤ m) :
    (1 + lam m) * eNorm m ≤ 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts, lam_eq]
  have hpos : (0 : ℝ) < 4 * (m : ℝ) + 5 := by linarith
  rw [div_eq_mul_inv]
  have hkey : (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
      ≤ 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5) := by
    have h3 : (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
        ≤ 4 * (4 * (m : ℝ) + 5) ^ 3 * (m : ℝ) := by
      nlinarith [sq_nonneg ((m : ℝ) - 1), sq_nonneg ((m : ℝ) ^ 2 - 1),
        sq_nonneg ((m : ℝ) ^ 3 - 1)]
    calc _ ≤ 4 * (4 * (m : ℝ) + 5) ^ 3 * (m : ℝ) := h3
      _ = 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5) := by ring
  calc (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5))
        * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) * (4 * (m : ℝ) + 5)⁻¹)
      = (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
          * (4 * (m : ℝ) + 5)⁻¹ := by ring
    _ ≤ (4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5)) * (4 * (m : ℝ) + 5)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by field_simp

/-- **Bessel's inequality in the form used below**: `Σ_m ∫_0^∞ (cmode m F)² < ∞`. -/
lemma cmode_sq_summable {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    Summable (fun m : ℕ => ∫ t in Set.Ioi 0, (cmode m F t) ^ 2) := by
  have hnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 :=
    fun m => integral_nonneg (fun t => sq_nonneg _)
  have hIF : (0 : ℝ) ≤ ∫ p in Q0, F p.1 p.2 ^ 2 := integral_nonneg (fun p => sq_nonneg _)
  have hg : Summable (fun m : ℕ => eNorm m * ∫ t in Set.Ioi 0, (cmode m F t) ^ 2) := by
    refine summable_of_sum_range_le (c := ∫ p in Q0, F p.1 p.2 ^ 2)
      (fun m => mul_nonneg (Work.EllipticEst.ModalSolution.eNorm_pos m).le (hnn m))
      (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simpa using hIF
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
      simpa using Work.FTS.H2.ModalSolR.coeffL2_sum_le hsm hL2 k
  exact Summable.of_nonneg_of_le hnn (fun m => le_mul_of_one_le_left (hnn m) (eNorm_ge_one m)) hg

/-- **The pointwise coefficient bound** for `m ≥ 1` (squared form). -/
lemma acoeff_sq_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {m : ℕ} (hm : 1 ≤ m) {z : ℝ} (hz : 0 < z) :
    (acoeff α m F z) ^ 2 ≤ (∫ t in Set.Ioi 0, (cmode m F t) ^ 2) * z ^ (-(1 : ℝ))
      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hDnn : 0 ≤ ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have h := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm
    (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m) hz
  have hden : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
    mul_pos (mul_pos hα (by linarith)) (Real.sqrt_pos.mpr hm0)
  set Y : ℝ := Real.sqrt (∫ t in Set.Ioi 0, (cmode m F t) ^ 2) * z ^ (-(1 / 2) : ℝ)
      / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) with hYdef
  have hY : 0 ≤ Y :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hz.le _)) hden.le
  have h1 : acoeff α m F z ≤ Y := (abs_le.mp h).2
  have h2 : -Y ≤ acoeff α m F z := (abs_le.mp h).1
  have hsq : (acoeff α m F z) ^ 2 ≤ Y ^ 2 := by
    have h3 : 0 ≤ Y + acoeff α m F z := by linarith
    have hprod : 0 ≤ (Y - acoeff α m F z) * (Y + acoeff α m F z) := mul_nonneg (by linarith) h3
    nlinarith [hprod]
  refine le_trans hsq (le_of_eq ?_)
  rw [hYdef, div_pow, mul_pow, mul_pow, Real.sq_sqrt hDnn, Real.sq_sqrt hm0.le,
    show (z ^ (-(1 / 2) : ℝ)) ^ 2 = z ^ (-(1 : ℝ)) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
      norm_num]
  ring

/-! ## The uniform tail estimate -/

/-- **The tail of the mode series is small, uniformly in `z` and `θ`.**  For `0 < c < d < π/2`
there are `K > 0` and a null sequence `b` with
`|ψ_N(z,θ) − ψ_M(z,θ)| ≤ K·z^{-1/2}·(b N + b M)` for every `z > 0` and `θ ∈ [c,d]`. -/
lemma psiTrunc_tail_uniform {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {c d : ℝ} (hcd : c < d) (hc0 : 0 < c) (hd : d < π / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ b : ℕ → ℝ, (∀ N, 0 ≤ b N) ∧ Tendsto b atTop (nhds 0) ∧
      ∀ (N M : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Icc c d →
        |psiTrunc α F N z θ - psiTrunc α F M z θ| ≤ K * z ^ (-(1 / 2) : ℝ) * (b N + b M) := by
  obtain ⟨K, hK0, hK⟩ := Work.EllipticEst.ModalSolution.psiTrunc_tail_bound (α := α) hcd hc0 hd
  set D : ℕ → ℝ := fun m => ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 with hDdef
  have hDnn : ∀ m : ℕ, 0 ≤ D m := fun m => integral_nonneg (fun t => sq_nonneg _)
  have hDsum : Summable D := cmode_sq_summable hsm hL2
  set b : ℕ → ℝ := fun N => Real.sqrt ((∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) with hbdef
  have hbnn : ∀ N : ℕ, 0 ≤ b N := fun N => Real.sqrt_nonneg _
  have hbsq : ∀ N : ℕ, (b N) ^ 2 = (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m := by
    intro N
    have h : 0 ≤ (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m :=
      sub_nonneg.mpr (hDsum.sum_le_tsum _ (fun i _ => hDnn i))
    rw [hbdef]
    exact Real.sq_sqrt h
  have hb : Tendsto b atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), D m) atTop (nhds (∑' m, D m)) :=
      hDsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ => (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) atTop
        (nhds ((∑' m, D m) - ∑' m, D m)) := tendsto_const_nhds.sub h1
    have h3 : Tendsto (fun N : ℕ => (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) atTop
        (nhds 0) := by simpa using h2
    have h4 := Real.continuous_sqrt.continuousAt.tendsto.comp h3
    simpa only [hbdef, Function.comp_def, Real.sqrt_zero] using h4
  have hkey : ∀ (N M : ℕ), M ≤ N → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Icc c d →
      |psiTrunc α F N z θ - psiTrunc α F M z θ| ≤ K * (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by
    intro N M hMN z θ hz hθ
    have h1 := hK z θ M N hθ hMN
    have hsum_eq : (∑ m ∈ Finset.Icc (M + 1) N,
            (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
              * (acoeff α m F z) ^ 2)
        + (∑ m ∈ Finset.Icc (M + 1) N, (lam m
            * (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ'))
              * (acoeff α m F z) ^ 2)
        = ∑ m ∈ Finset.Icc (M + 1) N, (1 + lam m)
            * (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
            * (acoeff α m F z) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsum_eq] at h1
    have hterm : ∀ m ∈ Finset.Icc (M + 1) N,
        (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m := by
      intro m hm
      have hm1 : 1 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
      have hcoef := acoeff_sq_le hα hα1 hsm hL2 hm1 hz
      have hratio := arith_ratio hm1
      have hfac : 0 ≤ (1 + lam m) * eNorm m := by
        refine mul_nonneg ?_ (Work.EllipticEst.ModalSolution.eNorm_pos m).le
        have : (0 : ℝ) ≤ lam m := by rw [lam_eq]; positivity
        linarith
      have hquot : 0 ≤ D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) :=
        div_nonneg (mul_nonneg (hDnn m) (Real.rpow_nonneg hz.le _)) (by positivity)
      calc (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ (1 + lam m) * eNorm m
              * (D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hcoef hfac
        _ ≤ (4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))
              * (D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_right hratio hquot
        _ = (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m := by
            field_simp
    have hPQ : ∑ m ∈ Finset.Icc (M + 1) N,
          (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
        ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2 := by
      calc ∑ m ∈ Finset.Icc (M + 1) N, (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ ∑ m ∈ Finset.Icc (M + 1) N, (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m :=
            Finset.sum_le_sum hterm
        _ = (4 / α ^ 2) * z ^ (-(1 : ℝ)) * ∑ m ∈ Finset.Icc (M + 1) N, D m := by
            rw [Finset.mul_sum]
        _ ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hbsq M]
            have hIccIco : (Finset.Icc (M + 1) N : Finset ℕ) = Finset.Ico (M + 1) (N + 1) := by
              ext k
              simp only [Finset.mem_Icc, Finset.mem_Ico]
              omega
            rw [hIccIco, Finset.sum_Ico_eq_sub _ (by omega : M + 1 ≤ N + 1)]
            exact sub_le_sub_right (hDsum.sum_le_tsum _ (fun i _ => hDnn i)) _
    have hsqrt : Real.sqrt ((4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2)
        = (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by
      rw [show (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2
            = (4 / α ^ 2) * (z ^ (-(1 : ℝ)) * (b M) ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.rpow_nonneg hz.le _)]
      have h1 : Real.sqrt (4 / α ^ 2) = 2 / α := by
        rw [show (4 / α ^ 2 : ℝ) = (2 / α) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have h2 : Real.sqrt (z ^ (-(1 : ℝ))) = z ^ (-(1 / 2) : ℝ) := by
        rw [show (z ^ (-(1 : ℝ))) = (z ^ (-(1 / 2) : ℝ)) ^ 2 by
              rw [sq, ← Real.rpow_add hz]; norm_num,
          Real.sqrt_sq (Real.rpow_nonneg hz.le _)]
      have h3 : Real.sqrt ((b M) ^ 2) = b M := Real.sqrt_sq (hbnn M)
      rw [h1, h2, h3]
      ring
    calc |psiTrunc α F N z θ - psiTrunc α F M z θ|
        ≤ K * Real.sqrt (∑ m ∈ Finset.Icc (M + 1) N,
              (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2) := h1
      _ ≤ K * Real.sqrt ((4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hPQ) hK0.le
      _ = K * (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by rw [hsqrt]; ring
  refine ⟨K * (2 / α), mul_pos hK0 (by positivity), b, hbnn, hb, fun N M z θ hz hθ => ?_⟩
  rcases le_total M N with hMN | hNM
  · refine le_trans (hkey N M hMN z θ hz hθ) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hbnn N]
  · rw [abs_sub_comm]
    refine le_trans (hkey M N hNM z θ hz hθ) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hbnn M]

end Work.FTS.PhiStar.Honesty.NodeAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.bmode_decay15 =====
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

theorem bmode_decay15 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
  obtain ⟨χ, K₁, K₂, hK₁, hK₂, hχc, hχbnd, hχ1, hχ0, hχd, hχdd, hχsupp⟩ := exists_bmcut_supp
  refine ⟨100, by norm_num, fun α ψ hα hα5 hang m hm => ?_⟩
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Ae, Be, hAe₀, hBe₀, hAe, hAe2, hBe⟩ := exists_eFam_bounds m
  have hsmallψ := exists_layer_small ψ hang.cont hang.bdry0 hang.bdry1
  have hAe' : ∀ θ ∈ Iθ, |eF m θ * Real.cos θ| ≤ Ae := by
    intro θ hθ
    have h1 := hAe2 θ hθ
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    have h2 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, hsin0, sq_nonneg (Real.cos θ)]
    calc |eF m θ * Real.cos θ| ≤ Ae * Real.sin θ * Real.cos θ ^ 2 := h1
      _ = Ae * (Real.sin θ * Real.cos θ ^ 2) := by ring
      _ ≤ Ae * 1 := mul_le_mul_of_nonneg_left h2 (le_of_lt hAe₀)
      _ = Ae := mul_one _
  have hlimA := bmcut_chi_tendsto χ Ae hAe₀ m ψ hang.cont
    (fun δ hδ => (hχc δ hδ).continuous) hχ0 hχ1
    (fun δ hδ θ => (hχbnd δ hδ θ).1) (fun δ hδ θ => (hχbnd δ hδ θ).2) hAe'
  have hlimC := bmcut_chi_tendsto χ Ae hAe₀ m (fun θ => GB α θ)
    (continuousOn_GamBar α hα hα1) (fun δ hδ => (hχc δ hδ).continuous) hχ0 hχ1
    (fun δ hδ θ => (hχbnd δ hδ θ).1) (fun δ hδ θ => (hχbnd δ hδ θ).2) hAe'
  have hlimB := bmcut_commutator_tendsto χ K₁ K₂ Ae Be hK₁ hK₂ hAe₀ hBe₀ hχd hχdd hχsupp m
    hAe hAe2 hBe ψ hsmallψ
  have hkey := coeff_eq χ hχc hχ1 hχ0 α hα hα1 hang m hlimA hlimC hlimB
  have hN := Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m
  have hNge := eFam_norm_ge m hm
  have hsqrtc : ContinuousOn (fun θ => Real.sqrt (Real.cos θ)) Iθ :=
    (Real.continuous_sqrt.comp Real.continuous_cos).continuousOn
  have hGc : ContinuousOn (fun θ => GB α θ) Iθ := continuousOn_GamBar α hα hα1
  have hEc : ContinuousOn (fun θ => eF m θ) Iθ := (contDiff_eF m).continuous.continuousOn
  have hcs := sq_integral_mul_le (fun θ => GB α θ * Real.sqrt (Real.cos θ))
    (fun θ => eF m θ * Real.sqrt (Real.cos θ))
    (integrableOn_Iθ_of_continuous ((hGc.mul hsqrtc).pow 2))
    (integrableOn_Iθ_of_continuous ((hGc.mul hsqrtc).mul (hEc.mul hsqrtc)))
    (integrableOn_Iθ_of_continuous ((hEc.mul hsqrtc).pow 2))
  have hI1 : (∫ θ in Iθ, (GB α θ * Real.sqrt (Real.cos θ)) * (eF m θ * Real.sqrt (Real.cos θ)))
      = ∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hs : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
      rw [← sq, Real.sq_sqrt hc]
    calc (GB α θ * Real.sqrt (Real.cos θ)) * (eF m θ * Real.sqrt (Real.cos θ))
        = GB α θ * eF m θ * (Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ)) := by ring
      _ = GB α θ * eF m θ * Real.cos θ := by rw [hs]
  have hI2 : (∫ θ in Iθ, (eF m θ * Real.sqrt (Real.cos θ)) ^ 2)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hc]
  have hI3 : (∫ θ in Iθ, (GB α θ * Real.sqrt (Real.cos θ)) ^ 2)
      = ∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hc]
  rw [hI1, hI2, hI3] at hcs
  have hG2 : (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) ≤ (45 / 4) ^ 2 := by
    have hb : ∀ θ ∈ Iθ, GB α θ ^ 2 * Real.cos θ ≤ (45 / 4) ^ 2 * Real.cos θ := by
      intro θ hθ
      have h1 : |GB α θ| ≤ 45 / 4 := GamBar_abs_le α hα hα1 hθ
      have h2 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have h3 : GB α θ ^ 2 ≤ (45 / 4) ^ 2 := by
        nlinarith [abs_le.mp h1]
      exact mul_le_mul_of_nonneg_right h3 h2
    have hP : IntegrableOn (fun θ => GB α θ ^ 2 * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous ((hGc.pow 2).mul Real.continuous_cos.continuousOn)
    have hQ : IntegrableOn (fun θ => (45 / 4) ^ 2 * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous (continuousOn_const.mul Real.continuous_cos.continuousOn)
    have hmono := MeasureTheory.setIntegral_mono_on hP hQ measurableSet_Iθ hb
    calc (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) ≤ ∫ θ in Iθ, (45 / 4) ^ 2 * Real.cos θ := hmono
      _ = (45 / 4) ^ 2 * (∫ θ in Iθ, Real.cos θ) := by rw [integral_const_mul]
      _ = (45 / 4) ^ 2 := by rw [int_cos_Iθ, mul_one]
  have hcs' : (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * (45 / 4) ^ 2 := by
    have hNp : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith [hNge, hm1]
    calc (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
        ≤ (∫ θ in Iθ, GB α θ ^ 2 * Real.cos θ) * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := hcs
      _ ≤ (45 / 4) ^ 2 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) :=
          mul_le_mul_of_nonneg_right hG2 (le_of_lt hNp)
      _ = (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * (45 / 4) ^ 2 := by ring
  have hKle : |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ|
      ≤ (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have hNpos : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith [hNge, hm1]
    have h1 : (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) ^ 2
        ≤ ((45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
      nlinarith [hcs']
    have h2 := sq_le_sq.mp h1
    exact h2.trans_eq (abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hNpos : 0 < ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by linarith [hNge, hm1]
  have hlam : 0 < λm m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith [hm1]
  have hstep3 : (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
      * Real.sqrt (2 * (m : ℝ) + 1) ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have h2m : 2 * (m : ℝ) + 1 ≤ 2 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by linarith [hNge]
    have hs2 : ((45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)) ^ 2
        ≤ (100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (m:ℝ) + 1),
        Real.sq_sqrt (le_of_lt hNpos)]
      nlinarith [h2m]
    have hle : (45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)
        ≤ 100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
      have h := sq_le_sq.mp hs2
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
    calc (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * Real.sqrt (2 * (m : ℝ) + 1)
        = Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * ((45 / 4) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
      _ ≤ Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * (100 * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) := by
          refine mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      _ = 100 * (Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)) := by ring
      _ = 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
          rw [← sq, Real.sq_sqrt (le_of_lt hNpos)]
  have hK : |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ|
      = λm m * |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| := by
    rw [← hkey, abs_mul, abs_of_pos hlam]
  have hstep4 : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m * Real.sqrt (2 * (m : ℝ) + 1)
      ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := by
    have h1 : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m
        = |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ| := by
      rw [hK]; ring
    rw [h1]
    calc |∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ| * Real.sqrt (2 * (m : ℝ) + 1)
        ≤ ((45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ))
          * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hKle (Real.sqrt_nonneg _)
      _ = (45 / 4) * Real.sqrt (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
          * Real.sqrt (2 * (m : ℝ) + 1) := by ring
      _ ≤ 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := hstep3
  have hfinal : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ|
        / (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
      ≤ 100 / (λm m * Real.sqrt (2 * (m : ℝ) + 1)) := by
    have hpos : (0:ℝ) < λm m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hlam (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2 * (m : ℝ) + 1))
    have hposN : (0:ℝ) < λm m * Real.sqrt (2 * (m : ℝ) + 1)
        * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) := mul_pos hpos hNpos
    rw [div_le_iff₀ hNpos]
    rw [show 100 / (λm m * Real.sqrt (2 * (m : ℝ) + 1))
          * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
        = 100 * (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) / (λm m * Real.sqrt (2 * (m : ℝ) + 1))
        from by ring]
    rw [le_div_iff₀ hpos]
    have hassoc : |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * (λm m * Real.sqrt (2 * (m : ℝ) + 1))
        = |∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ| * λm m * Real.sqrt (2 * (m : ℝ) + 1) := by
      ring
    rw [hassoc]
    exact hstep4
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ := iota_eq _
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := iota_eq _
  show |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
      ≤ 100 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
  rw [show Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
        / (∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ) from rfl, hnum, hden,
    abs_div, abs_of_pos hNpos]
  exact hfinal

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hkMem_three_of_slot_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ³`-membership and `ℋ³`-bound of a slot-wise limit

`Work.FTS.StrongEps.HkMem_of_tendsto` proves this descent statement for a limit `f` which is
itself assumed `C³` on the open quadrant.  The regularity of `f` is used there **only** through
the measurability of the limit integrand (`aesm_slice_HkIntegrand_of_contDiffOn` /
`aesm_integral_HkIntegrand_of_contDiffOn`).  Here the regularity hypothesis on `f` is dropped:
the measurability is recovered from the *slot-wise convergence* of the approximants, each of
which is `C^∞` on the open quadrant.

The route is the Fatou engine `Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice`:

* the open quadrant `Q0` is conull for `dz dθ` on `Iz × Iθ`, so the boundary values of `f`
  (about which nothing is known) are irrelevant; on `Q0` every slot of `f` is a pointwise limit
  of slots of `fs n`, and these are continuous there, whence
  `Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0` gives the joint a.e. measurability of
  `HkIntegrand α 3 f` (a finite sum of squares of slots), hence — via
  `AEStronglyMeasurable.integral_prod_right'` — the a.e. measurability of its `θ`-integral;
* `Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo` gives the a.e. measurability of each
  angular slice (at `z = 0` the integrand vanishes identically);
* the pointwise convergence of the slots on `Q0` upgrades to that of the integrand
  (`HkIntegrand_tendsto_of_mixed`), which on the conull set `Ioo 0 (π/2)` turns the `liminf`
  domination into an equality.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real Topology

namespace Work.FTS.StrongEps.E5G

set_option maxHeartbeats 800000

theorem hkMem_three_of_slot_tendsto {α R : ℝ} {fs : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hfs : ∀ n : ℕ, Work.Spaces.HkMem α 3 (fs n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 3 (fs n) ≤ R)
    (hsm : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (fs n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i f z θ)))
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (fs n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 3 f ∧ Work.Spaces.HkNorm α 3 f ≤ R := by
  classical
  -- the approximants are `C³` (indeed `C^∞`) on the open quadrant
  have hsm3 : ∀ n : ℕ, ContDiffOn ℝ (3 : ℕ) (Function.uncurry (fs n)) Work.FTS.EllipticEst.Q0 :=
    fun n => hsm n 3
  -- slot-wise convergence upgrades to convergence of the `ℋ³`-integrand, on `Q0`
  have hconvInt : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.HkIntegrand α 3 (fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α 3 f z θ)) :=
    fun z θ hzθ => Work.FTS.StrongEps.HkIntegrand_tendsto_of_mixed
      (α := α) (k := 3) (F := f) (Fs := fs) (z := z) (θ := θ)
      (fun j i hji => hconv j i hji z θ hzθ)
  -- continuity of the angular slice of the integrand of an approximant, for `z > 0`
  have hsliceCont : ∀ (n : ℕ) (z : ℝ), 0 < z →
      ContinuousOn (fun θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ) (Set.Ioo 0 (π / 2)) := by
    intro n z hzpos
    have hc := Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 3 (fs n) (hsm3 n)
    have hcomp := hc.comp (f := fun θ : ℝ => (z, θ)) (s := Set.Ioo 0 (π / 2))
      (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
    simpa [Function.comp_def] using hcomp
  -- joint a.e. measurability of the integrand of the limit, as a pointwise limit on `Q0`
  have hEM : AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 3 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0
      (un := fun n z θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ)
      (u := fun z θ => Work.Spaces.HkIntegrand α 3 f z θ)
      (fun n => Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 3 (fs n) (hsm3 n))
      hconvInt
  -- hence the a.e. strong measurability of its `θ`-integral
  have houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hEM.aestronglyMeasurable.integral_prod_right'
  -- and of each angular slice
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 3 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · exact (Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo
        (un := fun n θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ)
        (u := fun θ => Work.Spaces.HkIntegrand α 3 f z θ)
        (fun n => hsliceCont n z hzpos)
        (fun θ hθ => hconvInt z θ ⟨hzpos, hθ.1, hθ.2⟩)).aestronglyMeasurable
    · subst hz0
      rw [show (fun θ => Work.Spaces.HkIntegrand α 3 f 0 θ) = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 f θ]
      exact aestronglyMeasurable_const
  -- the `liminf` domination of the limit integrand by the approximants, a.e. in `θ`
  have hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 3 f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α 3 (fs n) z θ) Filter.atTop := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · -- the endpoints `0`, `π/2` are null, and on the open interval the integrand converges
      have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
        (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
          (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (π / 2)))).symm
      rw [hμ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hc := hconvInt z θ ⟨hzpos, hθ.1, hθ.2⟩
      rw [hc.liminf_eq]
    · subst hz0
      filter_upwards with θ
      rw [Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 f θ,
        show (fun n : ℕ => Work.Spaces.HkIntegrand α 3 (fs n) 0 θ) = fun _ : ℕ => (0 : ℝ) from
          funext fun n => Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 (fs n) θ,
        Filter.liminf_const]
  -- the uniform `ℋ³`-bounds of the approximants, as squared norms
  have hbSq : ∀ n : ℕ, Work.Spaces.HkSq α 3 (fs n) ≤ R ^ 2 := by
    intro n
    have hsq : Work.Spaces.HkSq α 3 (fs n) = Work.Spaces.HkNorm α 3 (fs n) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 3 (fs n))]
    rw [hsq]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 3 (fs n)) (hb n) 2
  -- Fatou, twice
  obtain ⟨hmemf, hsqle⟩ := Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
    (α := α) (k := 3) (f := f) (fs := fs) (C := R ^ 2) (sq_nonneg R)
    hfs hbSq hsl houter hae hz
  refine ⟨hmemf, ?_⟩
  have hR0 : 0 ≤ R := le_trans (Work.Spaces.HkNorm_nonneg α 3 (fs 0)) (hb 0)
  calc Work.Spaces.HkNorm α 3 f = Real.sqrt (Work.Spaces.HkSq α 3 f) := rfl
    _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = R := Real.sqrt_sq hR0

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.morrey_step_level =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

-- Route note.  This is the level-`k` version of the PROVED conditional Morrey step
-- `Work.FTS.StrongEps.LocUnif.mixed_morrey_step`
-- (`Submission/Work/FTS/StrongEps/LocUnif/mixed_morrey_step.lean`).  Transcribe that file
-- verbatim with exactly two changes: the level `6` becomes `k` (every occurrence is just
-- `HkSq α 6 F` → `HkSq α k F`, and `HkMem α 6 F` → `HkMem α k F`), and the slot bound
-- `j + i ≤ 4` becomes `j + i + 2 ≤ k` in both `hrect` and the conclusion.  The hypotheses
-- `hFmem` and `hji` are never used inside the original proof (check: `hFmem` does not occur
-- after the signature, `hji` only at the single `hrect j i hji` call), so the transcription is
-- fully mechanical; all imports of the original file carry over.  Do NOT try to derive it from
-- the level-6 original: `HkSq α k F` and `HkMem α k F` are not available at level 6.
theorem morrey_step_level {χ : ℝ × ℝ → ℝ} {F : ℝ → ℝ → ℝ} {α C C₀ M Km : ℝ}
    {a b c d a' b' c' d' : ℝ} (k : ℕ)
    (hmor : ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q| ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ))
    (hKmnn : 0 ≤ Km) (hα : 0 < α) (hC₀nn : 0 ≤ C₀) (hCpos : 0 < C)
    (hχC2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ) (hχnn : ∀ x, 0 ≤ χ x)
    (hχle1 : ∀ x, χ x ≤ 1)
    (hχone : ∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1)
    (hχzero : ∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0)
    (hMfd1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M) (hMfd2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M)
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α k F)
    (hFbd : Work.Spaces.HkNorm α k F ≤ C₀)
    (hrect : ∀ (j i : ℕ), j + i + 2 ≤ k →
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F)) :
    ∀ (j i : ℕ), j + i + 2 ≤ k → ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
        |Work.Spaces.mixed j i F p.1 p.2 - Work.Spaces.mixed j i F q.1 q.2|
          ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
  intro j i hji p hp q hq
  have hisOpen : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  -- the uncurried slot and the rectangle
  set G : ℝ × ℝ → ℝ := Function.uncurry (Work.Spaces.mixed j i F) with hGdef
  set s : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c' d' with hsdef
  have hsc : IsClosed s := isClosed_Icc.prod isClosed_Icc
  have hscm : MeasurableSet s := hsc.measurableSet
  have hkomp : IsCompact s := isCompact_Icc.prod isCompact_Icc
  -- `G` is `C²` on the open quadrant
  have hG2 : ContDiffOn ℝ 2 G Work.FTS.EllipticEst.Q0 := by
    have h := (hFsm.mixed j i).of_le Work.FTS.StrongEps.LocUnif.two_le_smoothOrder
    simpa only [hGdef] using h
  have hG1 : ContDiffOn ℝ 1 G Work.FTS.EllipticEst.Q0 := hG2.of_le (by norm_num)
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ G) Work.FTS.EllipticEst.Q0 :=
    hG2.fderiv_of_isOpen hisOpen (by norm_num)
  -- integrability on the rectangle, from continuity
  have hI0 : IntegrableOn (fun x : ℝ × ℝ => (G x) ^ 2) s :=
    ((hG2.continuousOn.mono hsub).pow 2).integrableOn_compact hkomp
  have hI1 : IntegrableOn (fun x : ℝ × ℝ => ‖fderiv ℝ G x‖ ^ 2) s := by
    have hcont := (hfd1.continuousOn.mono hsub).norm.pow 2
    exact hcont.integrableOn_compact hkomp
  -- the four basis entries of `D²G`, as functions of the point, and their sum `E`
  set A : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hAdef
  set B : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) x.1 x.2 with hBdef
  set Cc : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) x.1 x.2 with hCcdef
  set D : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hDdef
  set E : ℝ × ℝ → ℝ := fun x => ‖A x‖ + ‖B x‖ + ‖Cc x‖ + ‖D x‖ with hEdef
  have hI2 : IntegrableOn (fun x : ℝ × ℝ => E x ^ 2) s := by
    have hAc := (((hFsm.mixed j i).pz).pz).continuousOn
    have hBc := (((hFsm.mixed j i).pth).pz).continuousOn
    have hCc' := (((hFsm.mixed j i).pz).pth).continuousOn
    have hDc := (((hFsm.mixed j i).pth).pth).continuousOn
    have hE := ((((hAc.norm.add hBc.norm).add hCc'.norm).add hDc.norm)).mono hsub
    exact (hE.pow 2).integrableOn_compact hkomp
  have hIA : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIB : IntegrableOn (fun x : ℝ × ℝ => (B x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIC : IntegrableOn (fun x : ℝ × ℝ => (Cc x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hID : IntegrableOn (fun x : ℝ × ℝ => (D x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  -- `E` dominates the operator norm of the second derivative
  have hEbd : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ E x := by
    intro x hx
    have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
    have h := Work.FTS.StrongEps.LocUnif.norm_fderiv_fderiv_le_basis
      (G := Work.Spaces.mixed j i F) hisOpen hG2 hxQ
    simpa only [hEdef, hAdef, hBdef, hCcdef, hDdef, Real.norm_eq_abs,
      Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  -- the rectangle bounds of the hypothesis
  obtain ⟨hmix, hpz1, hpth1, hpz2, hpzpth, hpthpz, hpth2⟩ := hrect j i hji
  -- the `L²`-bound of the slot itself on the rectangle
  have hAg : ∫ x in s, (G x) ^ 2 ≤ C * Work.Spaces.HkSq α k F := by
    have hr : ∫ x in s, (G x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := G)
        (a := a') (b := b') (c := c') (d := d') hI0
      simpa only [hGdef, Function.uncurry] using h
    rw [hr]; exact hmix
  -- the `L²`-bound of the four second basis entries
  have hA2 : ∫ x in s, (A x) ^ 2 ≤ C * Work.Spaces.HkSq α k F := by
    have heq : ∫ x in s, (A x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := A)
        (a := a') (b := b') (c := c') (d := d') hIA
      simpa only [hAdef] using h
    rw [heq]
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hpz2
  have hB2 : ∫ x in s, (B x) ^ 2 ≤ C * Work.Spaces.HkSq α k F := by
    have heq : ∫ x in s, (B x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := B)
        (a := a') (b := b') (c := c') (d := d') hIB
      simpa only [hBdef] using h
    rw [heq]; exact hpzpth
  have hC2 : ∫ x in s, (Cc x) ^ 2 ≤ C * Work.Spaces.HkSq α k F := by
    have heq : ∫ x in s, (Cc x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := Cc)
        (a := a') (b := b') (c := c') (d := d') hIC
      simpa only [hCcdef] using h
    rw [heq]; exact hpthpz
  have hD2 : ∫ x in s, (D x) ^ 2 ≤ C * Work.Spaces.HkSq α k F := by
    have heq : ∫ x in s, (D x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := D)
        (a := a') (b := b') (c := c') (d := d') hID
      simpa only [hDdef] using h
    rw [heq]
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hpth2
  -- hence `∫_s E² ≤ 16 C |F|²`
  have hE2 : ∫ x in s, E x ^ 2 ≤ 16 * C * Work.Spaces.HkSq α k F := by
    have hpt : ∀ x ∈ s, E x ^ 2
        ≤ 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := by
      intro x hx
      have h := Work.FTS.StrongLWP.Sobolev.eqc_sq_add4_le ‖A x‖ ‖B x‖ ‖Cc x‖ ‖D x‖
      simpa only [hEdef, Real.norm_eq_abs, sq_abs] using h
    have h12 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2) s := hIA.add hIB
    have h123 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2) s :=
      h12.add hIC
    have h1234 : IntegrableOn (fun x : ℝ × ℝ =>
        (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) s := h123.add hID
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)) s := h1234.const_mul 4
    have hmono : ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
        (ae_restrict_of_forall_mem hscm hpt)
    have sA : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2) = (∫ x in s, (A x) ^ 2) + ∫ x in s, (B x) ^ 2 :=
      integral_add hIA hIB
    have sB : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2)) + ∫ x in s, (Cc x) ^ 2 :=
      integral_add h12 hIC
    have sC : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)) + ∫ x in s, (D x) ^ 2 :=
      integral_add h123 hID
    have sD : ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_const_mul 4 _
    have hsum4 : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        ≤ (((C * Work.Spaces.HkSq α k F) + C * Work.Spaces.HkSq α k F)
            + C * Work.Spaces.HkSq α k F) + C * Work.Spaces.HkSq α k F := by
      rw [sC, sB, sA]
      linarith [hA2, hB2, hC2, hD2]
    calc ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := hmono
      _ = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := sD
      _ ≤ 4 * ((((C * Work.Spaces.HkSq α k F) + C * Work.Spaces.HkSq α k F)
            + C * Work.Spaces.HkSq α k F) + C * Work.Spaces.HkSq α k F) :=
          mul_le_mul_of_nonneg_left hsum4 (by norm_num)
      _ = 16 * C * Work.Spaces.HkSq α k F := by ring
  -- the `L²`-bound of the first derivative
  have hD1 : ∫ x in s, ‖fderiv ℝ G x‖ ^ 2 ≤ 4 * C * Work.Spaces.HkSq α k F := by
    have hpt : ∀ x ∈ s, ‖fderiv ℝ G x‖ ^ 2
        ≤ 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by
      intro x hx
      have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
      have hdiff : DifferentiableAt ℝ G x :=
        (hG2.contDiffAt (hisOpen.mem_nhds hxQ)).differentiableAt (by norm_num)
      have e1 : (fderiv ℝ G x) (1, 0)
          = Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pz_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have e2 : (fderiv ℝ G x) (0, 1)
          = Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pth_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have hop := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum (fderiv ℝ G x)
      rw [e1, e2, Real.norm_eq_abs, Real.norm_eq_abs] at hop
      have h1 : ‖fderiv ℝ G x‖ ^ 2
          ≤ (|Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
              + |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
      have h2 := Work.FTS.StrongLWP.Sobolev.eqc_sq_add2_le
        |Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
        |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|
      rw [sq_abs, sq_abs] at h2
      exact h1.trans h2
    have hIpz : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pz).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hIpth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pth).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)) s :=
      (hIpz.add hIpth).const_mul 2
    have hzp : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α k F := by
      have heq : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpz
      rw [heq]; exact hpz1
    have hthp : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α k F := by
      have heq : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpth
      rw [heq]; exact hpth1
    have hIpzth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := hIpz.add hIpth
    have sA : ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = (∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
          + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2 :=
      integral_add hIpz hIpth
    have sB : ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
      integral_const_mul 2 _
    calc ∫ x in s, ‖fderiv ℝ G x‖ ^ 2
        ≤ ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
            (ae_restrict_of_forall_mem hscm hpt)
      _ = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := sB
      _ = 2 * ((∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
            + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by rw [sA]
      _ ≤ 2 * ((C * Work.Spaces.HkSq α k F) + C * Work.Spaces.HkSq α k F) := by
          linarith [hzp, hthp]
      _ = 4 * C * Work.Spaces.HkSq α k F := by ring
  -- the cutoff product
  have hv2 : ContDiff ℝ 2 (fun x : ℝ × ℝ => χ x * G x) :=
    Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two
      hsc hsub hisOpen hχC2 hχzero hG2
  have hvcs : HasCompactSupport (fun x : ℝ × ℝ => χ x * G x) :=
    Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul (χ := χ) (g := G) hχcs
  -- Morrey's inequality for `χ · G`
  have hm := hmor (fun x : ℝ × ℝ => χ x * G x) hv2 hvcs p q
  -- the two `L²`-norms appearing in Morrey's inequality
  have hA : ∫ x : ℝ × ℝ, (χ x * G x) ^ 2 ≤ C * Work.Spaces.HkSq α k F :=
    (Work.FTS.StrongLWP.Sobolev.eqc_integral_mul_sq_le hχzero hχle1 hχnn hscm hI0).trans hAg
  have hB : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
      ≤ 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α k F := by
    have hM0 : ∀ x : ℝ × ℝ, ‖χ x‖ ≤ 1 := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hgd : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ G y := fun y hy =>
      (hG2.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hgd2 : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
      (hfd1.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hbd := Work.FTS.StrongLWP.Sobolev.eqc_integral_fderiv_fderiv_mul_sq_le
      (χ := χ) (g := G) (s := s) (U := Work.FTS.EllipticEst.Q0)
      (M0 := 1) (M1 := M) (M2 := M) (E := E)
      hχC2 hsc hχzero hM0 hMfd1 hMfd2 hisOpen hsub hgd hgd2 hEbd hI0 hI1 hI2
    have hstep : 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
          + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
          + M ^ 2 * (∫ x in s, (G x) ^ 2))
        ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α k F)
          + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α k F)
          + M ^ 2 * (C * Work.Spaces.HkSq α k F)) := by
      have a1 := mul_le_mul_of_nonneg_left hE2 (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
      have a2 := mul_le_mul_of_nonneg_left hD1 (sq_nonneg (2 * M))
      have a3 := mul_le_mul_of_nonneg_left hAg (sq_nonneg M)
      linarith
    calc ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
        ≤ 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
            + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
            + M ^ 2 * (∫ x in s, (G x) ^ 2)) := hbd
      _ ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α k F)
            + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α k F)
            + M ^ 2 * (C * Work.Spaces.HkSq α k F)) := hstep
      _ = 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α k F := by ring
  -- the square-root comparison
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hQnn : 0 ≤ 3 * C * (16 + 17 * M ^ 2) := by positivity
  have hsum : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
      ≤ 2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
          ≤ Real.sqrt (C * Work.Spaces.HkSq α k F) := Real.sqrt_le_sqrt hA
        _ = Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α k F) := Real.sqrt_mul hCnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hQnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ,
          ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ,
            ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
          ≤ Real.sqrt (3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α k F) :=
            Real.sqrt_le_sqrt hB
        _ = Real.sqrt (3 * C * (16 + 17 * M ^ 2)) * Real.sqrt (Work.Spaces.HkSq α k F) :=
            Real.sqrt_mul hQnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hCnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  -- the values at `p` and `q` inside the inner rectangle
  have hGp : G p = Work.Spaces.mixed j i F p.1 p.2 := rfl
  have hGq : G q = Work.Spaces.mixed j i F q.1 q.2 := rfl
  have hχp : χ p = 1 := hχone p.1 hp.1 p.2 hp.2
  have hχq : χ q = 1 := hχone q.1 hq.1 q.2 hq.2
  have hvp : (fun x : ℝ × ℝ => χ x * G x) p = Work.Spaces.mixed j i F p.1 p.2 := by
    simp only [hχp, hGp, one_mul]
  have hvq : (fun x : ℝ × ℝ => χ x * G x) q = Work.Spaces.mixed j i F q.1 q.2 := by
    simp only [hχq, hGq, one_mul]
  -- assemble
  have hd0 : 0 ≤ dist p q ^ (1 / 2 : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hfin : |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
      ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
    calc |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
        ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ,
                ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) := hm
      _ ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)
            * dist p q ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hKmnn) hd0
  rw [hvp, hvq] at hfin
  exact hfin

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SZML2.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

noncomputable section

set_option autoImplicit false

/-! ## The quotient `Ψ = Φ / sin 2θ` and the two slice functionals attached to it -/

/-- The quotient `Ψ = Φ / sin 2θ`.  (The totalised division patches `{sin 2θ = 0}` with
the value `0`, which is harmless everywhere below.) -/
def psi (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Work.Construction.s2 θ

/-- The `(i,j) = (0,0)` slot `∫_θ Ψ² w² sin(2θ)^{-η}` of the `ℋ^6`-integrand of `Ψ`. -/
def slot0 (Φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The `θ`-slice of the `ℋ^6`-integrand of `Ψ = psi Φ`. -/
def sliceHk (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (psi Φ) z θ

@[simp] lemma psi_apply (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    psi Φ z θ = Φ z θ / Work.Construction.s2 θ := rfl

@[simp] lemma slot0_apply (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    slot0 Φ z = ∫ θ in Work.Spaces.Iθ,
      (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

@[simp] lemma sliceHk_apply (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceHk α Φ z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (psi Φ) z θ := rfl

/-! ## Elementary facts about `sin 2θ`, `η` and the weight `w` -/

lemma eta_pos' : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

lemma two_add_eta_pos : (0 : ℝ) < 2 + Work.Spaces.eta := by
  have := eta_pos'; linarith

/-- `sin 2θ ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin 2θ > 0` on the open interval `(0,π/2)`. -/
lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) := by
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- `z > 0` lies in `Iz = [0,∞)`. -/
lemma mem_Iz_of_pos {z : ℝ} (hz : 0 < z) : z ∈ Work.Spaces.Iz := le_of_lt hz

/-- `z ∈ (0,∞)` lies in `Iz = [0,∞)`. -/
lemma mem_Iz_of_mem_Ioi {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) : z ∈ Work.Spaces.Iz :=
  le_of_lt (show (0 : ℝ) < z from hz)

/-- `w(z) ≥ 1` for `z > 0`. -/
lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h := one_le_w hz
  nlinarith [h]

lemma w_sq_pos {z : ℝ} (hz : 0 < z) : 0 < (Work.Spaces.w z) ^ 2 :=
  lt_of_lt_of_le one_pos (one_le_w_sq hz)

/-- The weight identity `w(z)² = (1+z)⁴/z⁴`. -/
lemma w_sq_eq {z : ℝ} : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul]

/-- `z^{-4} = (z⁴)^{-1}` for `z ≥ 0`. -/
lemma rpow_neg_four {z : ℝ} (hz : 0 ≤ z) : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
  have hcast : z ^ (4 : ℕ) = z ^ (4 : ℝ) :=
    (Real.rpow_natCast (x := z) (n := 4)).symm
  rw [hcast, ← Real.rpow_neg hz (4 : ℝ)]

lemma sliceEnergy_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceEnergy Φ z := by
  rw [sliceEnergy]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

lemma slot0_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ slot0 Φ z :=
  integral_nonneg fun θ => sq_nonneg _

lemma sliceHk_nonneg {α : ℝ} (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceHk α Φ z :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 (psi Φ) z θ

/-- `√t ≤ t + 1` for `t ≥ 0`. -/
lemma sqrt_le_add_one {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ t + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [ht]

/-! ## The two pointwise identities at the heart of the reduction -/

/-- `Φ² · sin(2θ)^{-(2+η)} = Ψ² · sin(2θ)^{-η}`; the identity holds at the endpoints too,
where both sides vanish. -/
lemma Phi_sq_rootWeight_eq {Φ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Φ z θ ^ 2 * rootWeight θ
      = (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ' hθ
  rw [rootWeight, psi, Work.Construction.s2]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (show (-(2 + Work.Spaces.eta)) ≠ 0 by
        have := two_add_eta_pos; linarith),
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by
        have := eta_pos'; linarith)]
    ring
  · have hcast : (Real.sin (2 * θ)) ^ (2 : ℕ) = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
      (Real.rpow_natCast (x := Real.sin (2 * θ)) (n := 2)).symm
    rw [show (-(2 + Work.Spaces.eta)) = (-2 : ℝ) + (-Work.Spaces.eta) by ring,
      Real.rpow_add h (-2 : ℝ) (-Work.Spaces.eta), div_pow, div_eq_mul_inv, hcast,
      ← Real.rpow_neg (le_of_lt h) (2 : ℝ)]
    ring

/-- `(Ψ w / sin(2θ)^{η/2})² = w² · Ψ² · sin(2θ)^{-η}`. -/
lemma slot0_integrand_eq (Φ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ' hθ
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (show (Work.Spaces.eta / 2) ≠ 0 by
        have := eta_pos'; linarith), div_zero, mul_zero, pow_two, mul_zero,
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by
        have := eta_pos'; linarith), mul_zero, mul_zero]
  · have hcast : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
        = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) :=
      (Real.rpow_natCast (x := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) (n := 2)).symm
    have h1 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ)
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_mul (le_of_lt h) (Work.Spaces.eta / 2) (2 : ℝ)]
      congr 1
      ring
    rw [mul_pow, div_pow, div_eq_mul_inv, hcast, h1,
      ← Real.rpow_neg (le_of_lt h) Work.Spaces.eta]
    ring

/-- `slot0 Φ z = w(z)² · sliceEnergy Φ z`. -/
lemma slot0_eq_w_sq_sliceEnergy (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    slot0 Φ z = (Work.Spaces.w z) ^ 2 * sliceEnergy Φ z := by
  have h1 : slot0 Φ z = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
      * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    rw [slot0_apply]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => slot0_integrand_eq Φ z hθ)
  rw [h1, MeasureTheory.integral_const_mul]
  congr 1
  rw [sliceEnergy]
  exact setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => (Phi_sq_rootWeight_eq (Φ := Φ) (z := z) hθ).symm)

/-! ## Dominating `sliceEnergy` by the `(0,0)` slot of the `ℋ^6`-form -/

/-- The `(0,0)` slot is one of the summands of `HkIntegrand`. -/
lemma slot0_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    slot0 Φ z ≤ sliceHk α Φ z := by
  rw [slot0_apply, sliceHk_apply]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hHk.1 z hz) (Eventually.of_forall fun θ => ?_)
  exact Work.Spaces.sq_le_HkIntegrand_z α 6 (psi Φ) z θ 0 (by norm_num)

/-- `sliceEnergy ≤ sliceHk` for `z > 0`, because `w(z)² ≥ 1`. -/
lemma sliceEnergy_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    sliceEnergy Φ z ≤ sliceHk α Φ z := by
  have hzIz : z ∈ Work.Spaces.Iz := by show (0 : ℝ) ≤ z; exact le_of_lt hz
  have hA0 : 0 ≤ slot0 Φ z := slot0_nonneg Φ z
  have hW : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
  have hWpos : 0 < (Work.Spaces.w z) ^ 2 := w_sq_pos hz
  have hsplit : (Work.Spaces.w z) ^ 2 * sliceEnergy Φ z = slot0 Φ z :=
    (slot0_eq_w_sq_sliceEnergy Φ z).symm
  calc sliceEnergy Φ z
      = ((Work.Spaces.w z) ^ 2 * sliceEnergy Φ z) / (Work.Spaces.w z) ^ 2 := by
        rw [mul_div_cancel_left₀ _ (ne_of_gt hWpos)]
    _ = slot0 Φ z / (Work.Spaces.w z) ^ 2 := by rw [hsplit]
    _ ≤ slot0 Φ z := by
        rw [div_le_iff₀ hWpos]
        nlinarith
    _ ≤ sliceHk α Φ z := slot0_le_sliceHk hHk hzIz

/-- `sliceEnergy Φ z · z^{-4} ≤ sliceHk α Φ z` for `z > 0`, because `w(z)² = (1+z)⁴/z⁴`. -/
lemma sliceEnergy_mul_rpow_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    sliceEnergy Φ z * z ^ (-4 : ℝ) ≤ sliceHk α Φ z := by
  have hzIz : z ∈ Work.Spaces.Iz := by show (0 : ℝ) ≤ z; exact le_of_lt hz
  have hz0 : (0 : ℝ) < z := hz
  have hWpos : 0 < (Work.Spaces.w z) ^ 2 := w_sq_pos hz
  have hsl : sliceEnergy Φ z = slot0 Φ z / (Work.Spaces.w z) ^ 2 := by
    rw [eq_div_iff (ne_of_gt hWpos), mul_comm]
    exact (slot0_eq_w_sq_sliceEnergy Φ z).symm
  have hzpow : (0 : ℝ) < z ^ 4 := by positivity
  have h1zpow : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have h1z4 : z ^ 4 ≠ 0 := ne_of_gt hzpow
  have h1z1 : (1 + z) ^ 4 ≠ 0 := ne_of_gt h1zpow
  have key : sliceEnergy Φ z * z ^ (-4 : ℝ) = slot0 Φ z / (1 + z) ^ 4 := by
    rw [hsl, w_sq_eq, rpow_neg_four (le_of_lt hz)]
    field_simp
  rw [key]
  refine le_trans ?_ (slot0_le_sliceHk hHk hzIz)
  rw [div_le_iff₀ h1zpow]
  have hge : 1 ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith [slot0_nonneg Φ z, hge]

end

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.dth_Phi1_wip_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Product-measure bookkeeping (local copies of the private helpers of `WipLSelf`) -/

/-- The restriction of the plane Lebesgue measure to `I_z ×ˢ I_θ` is the product of the two
restricted measures. -/
private theorem volume_restrict_prod_loc :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact (MeasureTheory.Measure.prod_restrict _ _).symm

/-- `IntegrableOn` on the quadrant is `Integrable` against the product of the two restricted
measures. -/
private theorem integrableOn_prod_iff_loc {g : ℝ → ℝ → ℝ} :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ↔ MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [MeasureTheory.IntegrableOn, volume_restrict_prod_loc]
  rfl

theorem dth_Phi1_wip_le {u : ℝ → ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q)) u u := by
  set m : MeasureTheory.Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hm
  -- ## 0.  Integrability of the three integrands required by `wip_Dth_ibp`,
  --        with the weight `Φ₁ = w²/(1+z)`.
  have hUtil : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hU1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hUtil).congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hT1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 / (1 + z)) * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hT).congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hU2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  -- ## 1.  The same three integrands on the product measure, together with the
  --        `cos`-weighted one (obtained by domination, `|cos| ≤ 1`).
  have hFint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q)) m := by
    rw [hm]
    exact (integrableOn_prod_iff_loc (g := fun z θ => u z θ ^ 2
      * ((Work.Spaces.w z) ^ 2 / (1 + z)) * (Real.sin (2 * θ)) ^ (-q))).mp hU1
  have hGint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q))) m := by
    rw [hm]
    refine ((integrableOn_prod_iff_loc (g := fun z θ => u z θ * u z θ
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))).mp hU2).congr ?_
    filter_upwards with p
    ring
  have hcos : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.cos (2 * p.2)) m :=
    (Real.measurable_cos.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable
  have hEint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)) m := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
          * (Real.sin (2 * p.2)) ^ (-q) * Real.cos (2 * p.2)) m :=
      hFint.aestronglyMeasurable.mul hcos
    refine hFint.norm.mono' ?_ ?_
    · refine haesm.congr ?_
      filter_upwards with p
      ring
    · filter_upwards with p
      have hA : |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)|
          ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| := by
        rw [abs_mul]
        calc |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))|
              * |Real.cos (2 * p.2)|
            ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| := mul_one _
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |(u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * Real.cos (2 * p.2)) * (Real.sin (2 * p.2)) ^ (-q)|
          = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * Real.cos (2 * p.2)| * |(Real.sin (2 * p.2)) ^ (-q)| := abs_mul _ _
        _ ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))|
              * |(Real.sin (2 * p.2)) ^ (-q)| :=
            mul_le_mul_of_nonneg_right hA (abs_nonneg _)
        _ = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * (Real.sin (2 * p.2)) ^ (-q)| := (abs_mul _ _).symm
  have hE1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (integrableOn_prod_iff_loc (g := fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
      * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))).mpr hEint
  -- ## 2.  The angular integration by parts.
  have hIBP : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) :=
    Work.FTS.StrongPersist.H6Aux.R.wip_Dth_ibp
      (Φ := fun z => (Work.Spaces.w z) ^ 2 / (1 + z)) (q := q) hs hU1 hT1 hE1
  -- ## 3.  The a.e. weight facts on the quadrant.
  have hpos : ∀ᵐ p ∂m, 0 < p.1 := by
    rw [hm]; exact Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos
  have hφnn : ∀ᵐ p ∂m, 0 ≤ (Work.Spaces.w p.1) ^ 2 / (1 + p.1) := by
    filter_upwards [hpos] with p hp
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hφle : ∀ᵐ p ∂m, (Work.Spaces.w p.1) ^ 2 / (1 + p.1)
      ≤ (Work.Spaces.w p.1) ^ 2 := by
    filter_upwards [hpos] with p hp
    have h1 : (0 : ℝ) < 1 + p.1 := by linarith
    rw [div_le_iff₀ h1]
    nlinarith [sq_nonneg (Work.Spaces.w p.1), hp]
  have hσnn : ∀ᵐ p ∂m, 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := by
    have hθ : ∀ᵐ p ∂m, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [hm]; exact Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
    filter_upwards [hθ] with p hp
    exact Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1])
      (by linarith [hp.2, Real.pi_pos])).le _
  -- ## 4.  The comparison of the `cos`-weighted integrand with the two dominating ones.
  have hcomp1 : (∫ p, |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)| ∂m)
      ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q) ∂m := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hFint ?_
    filter_upwards [hφnn, hσnn] with p hφ hσ
    have hAnn : 0 ≤ u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) :=
      mul_nonneg (sq_nonneg _) hφ
    have hA : |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
          * Real.cos (2 * p.2)|
        ≤ u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) := by
      rw [abs_mul, abs_of_nonneg hAnn]
      calc (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)))
            * |Real.cos (2 * p.2)|
          ≤ (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hAnn
        _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) := mul_one _
    calc |(u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)) * (Real.sin (2 * p.2)) ^ (-q)|
        = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)| * |(Real.sin (2 * p.2)) ^ (-q)| := abs_mul _ _
      _ ≤ (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)))
            * |(Real.sin (2 * p.2)) ^ (-q)| :=
          mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q) := by rw [abs_of_nonneg hσ]
  have hcomp2 : (∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q) ∂m)
      ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q)) ∂m := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [hφnn, hσnn] with p hφ hσ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hφ) hσ
    · filter_upwards [hφle, hσnn] with p hφ hσ
      calc u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q)
          = u p.1 p.2 ^ 2 * (((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * (Real.sin (2 * p.2)) ^ (-q)) := by ring
        _ ≤ u p.1 p.2 ^ 2 * (((Work.Spaces.w p.1) ^ 2)
              * (Real.sin (2 * p.2)) ^ (-q)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ hσ) (sq_nonneg _)
        _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) := by ring
  -- ## 5.  The right-hand side of the integration by parts, on the product measure.
  set A : ℝ := ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m with hA
  have hTconv : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
        * ∫ θ in Work.Spaces.Iθ,
            Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) = A := by
    have hstep1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2)
        = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
            * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      dsimp only
      ring
    have hE2 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => (Real.cos (2 * θ) * u z θ) * u z θ
          * ((Work.Spaces.w z) ^ 2 / (1 + z) * (Real.sin (2 * θ)) ^ (-q))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine hE1.congr ?_
      filter_upwards with p
      dsimp only [Function.uncurry]
      ring
    have hstep2 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
          * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u
        = ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m := by
      rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u hE2]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      ring
    rw [hstep1, hstep2, hA]
  -- ## 6.  The integral of the absolute value is bounded by the two dominating integrals.
  have hfin : |A| ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q)) ∂m := by
    rw [hA]
    calc |∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m|
        ≤ ∫ p, |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)| ∂m :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q) ∂m := hcomp1
      _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q)) ∂m := hcomp2
  -- ## 7.  Assembly.
  have habs : |q - 1| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  calc Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := hIBP
    _ = (q - 1) * A := by rw [hTconv]
    _ ≤ |(q - 1) * A| := le_abs_self _
    _ = |q - 1| * |A| := by rw [abs_mul]
    _ ≤ 1 * |A| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    _ = |A| := one_mul _
    _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-q)) ∂m := hfin
    _ = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-q)) u u := by
        rw [show (∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) ∂m)
            = ∫ p, u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) ∂m from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
        exact (Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-q)) u u hU2).symm

end

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS_EllLimOK.VopTransfer.mixed_le_of_Vop_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

theorem mixed_le_of_Vop_jets : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ (Ψ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen Ψ →
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun s => Real.cos s * Ψ z s)
      (𝓝[<] (π / 2)) (𝓝 0)) →
    (∀ j l : ℕ, j + l ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j l (Work.Construction.Vop Ψ) z θ| ≤ K) →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i Ψ z θ| ≤ C * K := by
  classical
  -- ## the universal angular coefficient bounds
  obtain ⟨A, hAnn, hAb⟩ := exists_LopIter_bound (fun θ : ℝ => Real.sin (2 * θ))
    (by intro k; fun_prop) 3
  obtain ⟨B, hBnn, hBb⟩ := exists_LopIter_bound (fun θ : ℝ => 2 * Real.sin θ ^ 2)
    (by intro k; fun_prop) 3
  have hB1 : 1 ≤ B := by
    have h := hBb 0 (by norm_num) (π / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩
    simp only [Work.FTS.EllipticEst.LopIter, Function.iterate_zero, id_eq] at h
    rw [Real.sin_pi_div_two] at h
    norm_num at h
    linarith
  -- ## the level constants
  let D : ℕ → ℝ := fun n =>
    Nat.rec (motive := fun _ => ℝ) 2 (fun k Dk => (2 : ℝ) ^ k * A + B * ((2 : ℝ) ^ k * Dk)) n
  have hD0 : D 0 = 2 := rfl
  have hDs : ∀ k, D (k + 1) = (2 : ℝ) ^ k * A + B * ((2 : ℝ) ^ k * D k) := fun k => rfl
  have hDnn : ∀ n, 0 ≤ D n := by
    intro n
    induction n with
    | zero => rw [hD0]; norm_num
    | succ k ih =>
        rw [hDs k]
        have h1 : 0 ≤ (2 : ℝ) ^ k * A := mul_nonneg (by positivity) hAnn
        have h2 : 0 ≤ B * ((2 : ℝ) ^ k * D k) := mul_nonneg hBnn (mul_nonneg (by positivity) ih)
        linarith
  have hDmono : ∀ n, D n ≤ D (n + 1) := by
    intro n
    rw [hDs n]
    have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hB2 : (1 : ℝ) ≤ (2 : ℝ) ^ n * B := one_le_mul_of_one_le_of_one_le h2n hB1
    have hAn : 0 ≤ (2 : ℝ) ^ n * A := mul_nonneg (by positivity) hAnn
    nlinarith [hDnn n, mul_le_mul_of_nonneg_right hB2 (hDnn n)]
  have hDle : ∀ m n, m ≤ n → D m ≤ D n := fun m n h =>
    (monotone_nat_of_le_succ hDmono : Monotone D) h
  refine ⟨1 + D 0 + D 1 + D 2 + D 3 + D 4, by linarith [hDnn 0, hDnn 1, hDnn 2, hDnn 3, hDnn 4],
    ?_⟩
  intro K hK Ψ hsm hbd hjets
  have hVsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := smoothOpen_vop hsm
  -- ## the reconstruction
  have hrec : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Real.cos θ * Ψ z θ = -(∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s) := by
    intro z θ hz hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    have hcont : ContinuousOn (fun s : ℝ => Real.cos s * Work.Construction.Vop Ψ z s)
        (Set.Ioo θ (π / 2)) := by
      have hslice : ContinuousOn (fun s : ℝ => Work.Construction.Vop Ψ z s)
          (Set.Ioo θ (π / 2)) := by
        intro s hs
        have hs' : (z, s) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, lt_trans hθ.1 hs.1, hs.2⟩
        have hc : ContinuousAt (Function.uncurry (Work.Construction.Vop Ψ)) (z, s) :=
          hVsm.continuousOn.continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hs')
        exact (hc.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      exact (Real.continuous_cos.continuousOn).mul hslice
    have hint : IntervalIntegrable (fun s => Real.cos s * Work.Construction.Vop Ψ z s)
        volume θ (π / 2) := by
      constructor
      · refine MeasureTheory.IntegrableOn.of_bound ?hfin ?haesm K ?hb'
        · exact measure_Ioc_lt_top
        · rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
          exact hcont.aestronglyMeasurable measurableSet_Ioo
        · rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := θ) (b := π / 2)]
            with s hs
          intro hsmem
          obtain ⟨hs1, hs2⟩ := hs.mpr hsmem
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Work.FTS_EllLimOK.cos_pos_of_mem_Ioo
            ⟨lt_trans hθ.1 hs1, hs2⟩)]
          have hVk : |Work.Construction.Vop Ψ z s| ≤ K :=
            hjets 0 0 (by norm_num) z s hz ⟨lt_trans hθ.1 hs1, hs2⟩
          simpa using mul_le_mul (Real.cos_le_one s) hVk (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      · refine integrableOn_empty.mono_set ?_
        intro s hs
        rw [Set.mem_Ioc] at hs
        linarith [hs.1, hθ.2]
    have hsliceC : ContinuousAt (fun s : ℝ => Real.cos s * Ψ z s) θ := by
      have hc : ContinuousAt (Function.uncurry Ψ) (z, θ) :=
        hsm.continuousOn.continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
      have h1 : ContinuousAt (fun s : ℝ => Ψ z s) θ :=
        hc.comp (continuousAt_const.prodMk continuousAt_id)
      exact Real.continuous_cos.continuousAt.mul h1
    have hvr := Work.FTS_EllLimOK.Vop_reconstruct (Ψ := Ψ) (z := z) (θ := θ) hθ ?_ hint ?_
      (hbd z hz)
    · rw [hvr]
      field_simp
    · intro s hs
      exact ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨lt_trans hθ.1 hs.1, hs.2⟩) |>.hasDerivAt
    · exact hsliceC.tendsto.mono_left nhdsWithin_le_nhds
  -- ## the z-derivative chain
  have hchain : ∀ j, j ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ
        = -(∫ s in θ..(π / 2),
            Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s) := by
    intro j
    induction j with
    | zero => intro _ z θ hz hθ; exact hrec z θ hz hθ
    | succ j ih =>
        intro hj z θ hz hθ
        have hji : j ≤ 4 := by omega
        have hIH := ih hji
        have hEqOn : Set.EqOn
            (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ)))
            (Function.uncurry (fun z θ => -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s)))
            Work.FTS.EllipticEst.Q0 := by
          intro p hp
          rcases p with ⟨z', θ'⟩
          obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact hIH z' θ' hz' ⟨hθ'1, hθ'2⟩
        have hpz := Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
        -- the parametrised-differentiation input
        have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
        have hsub : Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)
            ⊆ Work.FTS.EllipticEst.Q0 := by
          intro p hp
          obtain ⟨hp1, hp2⟩ := hp
          exact Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨by linarith [hp1.1, hz], lt_trans hθ.1 hp2.1, hp2.2⟩
        have hW : ContinuousOn
            (Function.uncurry (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)))
            (Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)) :=
          ((hVsm.DzIter j).continuousOn).mono hsub
        have hW' : ContinuousOn
            (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ))))
            (Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)) :=
          (((hVsm.DzIter j).pz).continuousOn).mono hsub
        have hWb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ s ∈ Set.Ioo θ (π / 2),
            |Work.Spaces.DzIter j (Work.Construction.Vop Ψ) x s| ≤ max K (2 * K / z) := by
          intro x hx s hs
          exact le_trans (hjets j 0 (by omega) x s (by linarith [hx.1, hz])
            ⟨lt_trans hθ.1 hs.1, hs.2⟩) (le_max_left _ _)
        have hW'b : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ s ∈ Set.Ioo θ (π / 2),
            |Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s|
              ≤ max K (2 * K / z) := by
          intro x hx s hs
          have hxpos : 0 < x := by linarith [hx.1, hz]
          have hDz : Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s
              = Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) x s / x := by
            have h := hjets (j + 1) 0 (by omega) x s hxpos ⟨lt_trans hθ.1 hs.1, hs.2⟩
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz] at h ⊢
            field_simp
          rw [hDz, abs_div, abs_of_pos hxpos]
          refine le_trans (div_le_div_of_nonneg_right
            (hjets (j + 1) 0 (by omega) x s hxpos ⟨lt_trans hθ.1 hs.1, hs.2⟩) hxpos.le) ?_
          have hxle : z / 2 ≤ x := le_of_lt hx.1
          have h2 : K / x ≤ 2 * K / z := by
            have h3 : K / x ≤ K / (z / 2) :=
              div_le_div_of_nonneg_left hK (by linarith) hxle
            have h4 : K / (z / 2) = 2 * K / z := by
              field_simp
            linarith [h3, h4.le]
          exact le_trans h2 (le_max_right _ _)
        have hderiv : ∀ s ∈ Set.Ioo θ (π / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
            HasDerivAt (fun x' => Work.Spaces.DzIter j (Work.Construction.Vop Ψ) x' s)
              (Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s) x := by
          intro s hs x hx
          exact (hVsm.DzIter j).hasDerivAt_slice ⟨lt_trans hθ.1 hs.1, hs.2⟩
            (by linarith [hx.1, hz])
        have hDiff := derivUnderIntegralIoo (W := Work.Spaces.DzIter j (Work.Construction.Vop Ψ))
          (W' := Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)))
          (θ := θ) (C := max K (2 * K / z)) hθ isOpen_Ioo hzmem hW hW' hWb hW'b hderiv
        have hFpz : Work.Spaces.pz (fun z θ => -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s)) z θ
            = -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) z s) := by
          have hneg := hDiff.neg
          have hfun : (fun z' : ℝ => -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s))
              = Neg.neg (fun z' : ℝ => ∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s) := by
            funext z'; rfl
          show deriv (fun z' : ℝ => -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s)) z
            = -(∫ s in θ..(π / 2), Real.cos s * deriv (fun z' : ℝ =>
                Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s) z)
          rw [hfun]
          exact hneg.deriv
        show z * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ)) z θ
            = -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) z s)
        rw [hpz, hFpz]
        rw [show -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) z s)
            = -(∫ s in θ..(π / 2), z * (Real.cos s
                * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) z s)) from by
          congr 1
          refine intervalIntegral.integral_congr fun s _ => ?_
          simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
          ring]
        rw [intervalIntegral.integral_const_mul]
        ring
  -- ## level 0
  have hbound0 : ∀ j, j ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.DzIter j Ψ z θ| ≤ 2 * K := by
    intro j hj z θ hz hθ
    have hcos := Work.FTS_EllLimOK.cos_pos_of_mem_Ioo hθ
    have h1 := hchain j hj z θ hz hθ
    have h2 : |Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ|
        ≤ K * (π / 2 - θ) := by
      rw [h1, abs_neg]
      have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := θ) (b := π / 2) (C := K)
        (f := fun s => Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s) ?_
      · rw [Real.norm_eq_abs] at hkey
        rw [abs_of_pos (by linarith [hθ.2] : (0:ℝ) < π / 2 - θ)] at hkey
        exact hkey
      · intro s hs
        rw [Set.uIoc_of_le (le_of_lt hθ.2)] at hs
        obtain ⟨hs1, hs2⟩ := hs
        have hsnn : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hs1, hθ.1, Real.pi_pos], hs2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsnn]
        rcases eq_or_lt_of_le hs2 with hsp | hsp
        · rw [hsp, Real.cos_pi_div_two, zero_mul]
          exact hK
        · simpa using mul_le_mul (Real.cos_le_one s)
            (hjets j 0 (by omega) z s hz ⟨lt_trans hθ.1 hs1, hsp⟩)
            (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h3 : Work.Spaces.DzIter j Ψ z θ
        = Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ / Real.cos θ := by
      rw [DzIter_theta_const_mul (fun θ => Real.cos θ) Ψ j z θ hz hθ]
      field_simp
    rw [h3, abs_div, abs_of_pos hcos]
    have ht : π / 2 - θ ≤ (π / 2) * Real.cos θ := by
      have hsin : Real.sin (π / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
      have hmul := Real.mul_le_sin (x := π / 2 - θ) (by linarith [hθ.2]) (by linarith [hθ.1])
      rw [hsin] at hmul
      have h2 : (π / 2) * (2 / Real.pi * (π / 2 - θ)) = π / 2 - θ := by
        field_simp
      calc π / 2 - θ = (π / 2) * (2 / Real.pi * (π / 2 - θ)) := h2.symm
        _ ≤ (π / 2) * Real.cos θ := mul_le_mul_of_nonneg_left hmul (by linarith [Real.pi_pos])
    calc |Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ| / Real.cos θ
        ≤ K * (π / 2 - θ) / Real.cos θ := div_le_div_of_nonneg_right h2 hcos.le
      _ ≤ K * ((π / 2) * Real.cos θ) / Real.cos θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hK) hcos.le
      _ = K * (π / 2) := by field_simp
      _ ≤ 2 * K := by nlinarith [Real.pi_lt_four, hK]
  -- ## the induction on the level
  have key : ∀ n, n ≤ 4 → ∀ j, j + n ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j n Ψ z θ| ≤ D n * K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn j hjn z θ hz hθ
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [Work.Spaces.mixed_zero_right, hD0]
        exact hbound0 j (by omega) z θ hz hθ
      · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        -- coefficient bound at the level `n'`
        have hAb' : ∀ m ≤ n', ∀ θ' ∈ Work.Spaces.Iθ,
            |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ'| ≤ A :=
          fun m hm θ' hθ' => hAb m (by omega) θ' hθ'
        have hBb' : ∀ m ≤ n', ∀ θ' ∈ Work.Spaces.Iθ,
            |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ'| ≤ B :=
          fun m hm θ' hθ' => hBb m (by omega) θ' hθ'
        have hVb' : ∀ m ≤ n', ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
            |Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z' θ'| ≤ K :=
          fun m hm z' θ' hz' hθ' => hjets j (n' - m) (by omega) z' θ' hz' hθ'
        have hPb' : ∀ m ≤ n', ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
            |Work.Spaces.mixed j (n' - m) Ψ z' θ'| ≤ D (n' - m) * K :=
          fun m hm z' θ' hz' hθ' => ih (n' - m) (by omega) (by omega) j (by omega) z' θ' hz' hθ'
        have hshift : Work.Spaces.mixed j (n' + 1) Ψ z θ
            = Work.Spaces.mixed j n' (Work.Spaces.Dth Ψ) z θ := by
          simp only [Work.Spaces.mixed]
          rw [Work.FTS.TransportS.DthIter_shift]
        have hGeq : Set.EqOn (Function.uncurry (Work.Spaces.Dth Ψ))
            (Function.uncurry (fun z θ => Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ
              + 2 * Real.sin θ ^ 2 * Ψ z θ)) Work.FTS.EllipticEst.Q0 := by
          intro p hp
          rcases p with ⟨z', θ'⟩
          obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact Dth_eq_sfun_mul_add ⟨hθ'1, hθ'2⟩
        have hA1 : Work.FTS.EllipticEst.SmoothOpen
            (fun z θ => Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ) :=
          smoothOpen_angular_mul (by fun_prop) hVsm
        have hA2 : Work.FTS.EllipticEst.SmoothOpen
            (fun z θ => 2 * Real.sin θ ^ 2 * Ψ z θ) :=
          smoothOpen_angular_mul (by fun_prop) hsm
        rw [hshift, mixed_congr_Q0 hGeq j n' z θ hz hθ,
          Work.FTS.EllipticEst.SmoothOpen.mixed_add hA1 hA2 j n' z θ hz hθ.1 hθ.2,
          mixed_angular_mul (c := fun θ : ℝ => Real.sin (2 * θ)) (by intro θ'; fun_prop)
            hVsm j n' hz hθ,
          mixed_angular_mul (c := fun θ : ℝ => 2 * Real.sin θ ^ 2) (by intro θ'; fun_prop)
            hsm j n' hz hθ]
        -- bound the two sums
        have hch : (∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)) = (2 : ℝ) ^ n' := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        have hb1 : |∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ
              * Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
            ≤ (2 : ℝ) ^ n' * (A * K) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hterm : ∀ m ∈ Finset.range (n' + 1),
              |(n'.choose m : ℝ)
                * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ
                * Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
              ≤ (n'.choose m : ℝ) * (A * K) := by
            intro m hm
            have hmle : m ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            have h1 : |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ A :=
              hAb' m hmle θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
            have h2 := hVb' m hmle z θ hz hθ
            have hc : (0 : ℝ) ≤ (n'.choose m : ℝ) := Nat.cast_nonneg _
            have hAc : (n'.choose m : ℝ)
                * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ|
                ≤ (n'.choose m : ℝ) * A := mul_le_mul_of_nonneg_left h1 hc
            rw [abs_mul, abs_mul, abs_of_nonneg hc]
            calc (n'.choose m : ℝ)
                  * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ|
                  * |Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
                ≤ ((n'.choose m : ℝ) * A) * K :=
                  mul_le_mul hAc h2 (abs_nonneg _) (mul_nonneg hc hAnn)
              _ = (n'.choose m : ℝ) * (A * K) := by ring
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul, hch]
        have hb2 : |∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ
              * Work.Spaces.mixed j (n' - m) Ψ z θ|
            ≤ (2 : ℝ) ^ n' * (B * (D n' * K)) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hterm : ∀ m ∈ Finset.range (n' + 1),
              |(n'.choose m : ℝ)
                * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ
                * Work.Spaces.mixed j (n' - m) Ψ z θ|
              ≤ (n'.choose m : ℝ) * (B * (D n' * K)) := by
            intro m hm
            have hmle : m ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            have h1 : |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ| ≤ B :=
              hBb' m hmle θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
            have h2 : |Work.Spaces.mixed j (n' - m) Ψ z θ| ≤ D n' * K :=
              le_trans (hPb' m hmle z θ hz hθ)
                (mul_le_mul_of_nonneg_right (hDle (n' - m) n' (by omega)) hK)
            have hc : (0 : ℝ) ≤ (n'.choose m : ℝ) := Nat.cast_nonneg _
            have hBc : (n'.choose m : ℝ)
                * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ|
                ≤ (n'.choose m : ℝ) * B := mul_le_mul_of_nonneg_left h1 hc
            rw [abs_mul, abs_mul, abs_of_nonneg hc]
            calc (n'.choose m : ℝ)
                  * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ|
                  * |Work.Spaces.mixed j (n' - m) Ψ z θ|
                ≤ ((n'.choose m : ℝ) * B) * (D n' * K) :=
                  mul_le_mul hBc h2 (abs_nonneg _) (mul_nonneg hc hBnn)
              _ = (n'.choose m : ℝ) * (B * (D n' * K)) := by ring
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul, hch]
        refine le_trans (abs_add_le _ _) ?_
        refine le_trans (add_le_add hb1 hb2) ?_
        have heq : (2 : ℝ) ^ n' * (A * K) + (2 : ℝ) ^ n' * (B * (D n' * K))
            = ((2 : ℝ) ^ n' * A + B * ((2 : ℝ) ^ n' * D n')) * K := by ring
        rw [hDs, heq]
  -- ## assembly
  intro j i hji z θ hz hθ
  have hi4 : i ≤ 4 := by omega
  have h1 := key i hi4 j hji z θ hz hθ
  have h2 : D i ≤ 1 + D 0 + D 1 + D 2 + D 3 + D 4 := by
    interval_cases i <;> linarith [hDnn 0, hDnn 1, hDnn 2, hDnn 3, hDnn 4]
  calc |Work.Spaces.mixed j i Ψ z θ| ≤ D i * K := h1
    _ ≤ (1 + D 0 + D 1 + D 2 + D 3 + D 4) * K := mul_le_mul_of_nonneg_right h2 hK


end Work.FTS_EllLimOK.VopTransfer
end
end
-- ===== merged: Submission.Work.H2W.fstarDzIterFourAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Topology
open MeasureTheory Set Filter

/-- **The level-`4` angular moment `F_*(D_z^4 Ψ)` vanishes almost everywhere in `z > 0`.**

The level-`3` moment chain (`MomentAe.Fstar_DzIter_le_Psi`) gives `F_*(D_z³Ψ) ≡ 0` pointwise;
the level-`4` moment is obtained from the honest datum `A = z²∂_z²Ψ ∈ ℋ²` through the radial
identity `D_z^4Ψ = D_z³Ψ + D_z²A`. -/
theorem fstarDzIterFourAe (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0 := by
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    MomentAe.smoothOpen_zsq hΨsm
  have hAmem : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    h.memA
  have hBmem : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hmom : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 :=
    MomentAe.Fstar_DzIter_le_Psi α F Ψ h
  have hlev : ∀ i : ℕ, i ≤ 3 → ∀ u : ℝ, 0 < u →
      MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun i hi u hu => (MomentAe.level_bound hΨsm hAmem hBmem i hi).1 u hu
  have hA2 := fstar_DzIter_two_zsq_ae α F Ψ h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hA2
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hA2] with z hA2imp
  intro hzmem
  have hz : 0 < z := hzmem
  have hA2z : Work.Elliptic.Fstar (Work.Spaces.DzIter 2
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 := hA2imp hzmem
  have hI3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    hlev 3 (by norm_num) z hz
  have hIA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cert.GbarSin.integrableOn_DzIter_mul_sinCos2 α 2
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hAsm hAmem le_rfl hz
  have hcongr : (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ
        + Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Elliptic.sinCos2 θ) := by
    filter_upwards [MomentAe.ae_Ioo_mem] with θ hθ
    have hid := MomentAe.DzIter_zsq_pzIter2_eq hΨsm 2 hz hθ
    rw [hid]
    ring
  have hsplit : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z
        + Work.Elliptic.Fstar (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      MeasureTheory.integral_congr_ae hcongr]
    rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 Ψ z θ
            * Work.Elliptic.sinCos2 θ
          + Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Elliptic.sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Elliptic.sinCos2 θ)
        from MeasureTheory.integral_add hI3 hIA2]
  rw [hsplit, hmom 3 (by norm_num) z hz, hA2z, add_zero]

end Work.H2W
end
