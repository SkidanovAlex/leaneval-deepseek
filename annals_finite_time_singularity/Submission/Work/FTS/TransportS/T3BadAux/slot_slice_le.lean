import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.t2SupF
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
-- ===== merged: Submission.Work.FTS.TransportS.SlotT2.SlotIbpDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false

/-! ## The three blocks -/



/-- The integrand of the `k`-th hard-slot pairing (the integrand of the target statement). -/
def ps (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ * f z θ
    * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ

/-- The angular energy of the `k`-th slot as a function of `z`:
`∫_θ (Xz α g k z θ)² = ∫_θ (Thard g k z θ)² w(z)² sghard α k θ`. -/
def angE (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Xz α g k z θ) ^ 2

/-! ## Elementary pointwise identities -/




theorem w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _





/-! ## Continuity of the uncurried blocks on the open quadrant -/








/-! ## A.e. strong measurability of the blocks and of their slices -/










/-! ## The vanishing of the blocks at `z = 0` -/




/-! ## Slice integrability coming from `HkMem` -/





end Work.FTS.TransportS.SlotT2
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SupB2

set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- `sin(2σ) > 0` for `σ` in the interior of `Iθ`. -/
theorem sin_two_pos_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * σ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])

/-! ## The pointwise domination by the `ℋ⁴`-integrand -/

/-- The next mixed slot, weighted by `w` and by `sin(2σ)^{-γ}`, is the `(i, j+1)` summand of
`HkIntegrand α 4 f`. -/
theorem mixed_succ_mul_w_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {z σ : ℝ} (hz : 0 < z)
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hi1 : 1 ≤ i) (hij : i + (j + 1) ≤ 4) :
    (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  calc (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed (j + 1) i f z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = (Work.Spaces.mixed (j + 1) i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := by
        rw [Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    _ = (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.Wt α z σ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ i (j + 1) hi1 hij

/-- The mixed slot, weighted by `sin(2σ)^{-γ}`, is dominated by `HkIntegrand α 4 f` (because
`w ≥ 1` on `z > 0`). -/
theorem mixed_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {z σ : ℝ} (hz : 0 < z)
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hi1 : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 :=
    one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have hkey : (Work.Spaces.mixed j i f z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := by
    rw [Work.H2.T1Q.Wt_sq_eq α z σ hsin]
  calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ (Work.Spaces.mixed j i f z σ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact le_mul_of_one_le_left (Real.rpow_nonneg (le_of_lt hsin) _) hw1
    _ = (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := hkey
    _ = (Work.Spaces.mixed j i f z σ * Work.Spaces.Wt α z σ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ i j hi1 hij

/-! ## The main estimate -/

theorem mixed_slice_z_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f _hα _hα1 hF hmem j i hi hij z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π / 2) →
        IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz →
        (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
      have hlam : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (le_of_lt hsinσ) _
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.mixed j i f x σ)
            (Work.Spaces.pz (Work.Spaces.mixed j i f) x σ) x :=
        fun x hx => (hF.mixed j i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.mixed j i f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.mixed j i).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn
          (fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.mixed j i).pz).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : IntegrableOn
          (fun x : ℝ => (Work.Spaces.mixed j i f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.mixed j i f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the relevant slices
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      -- interval integrability
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
            (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact ContinuousOn.mul continuousOn_const (hcontW.pow 2)
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- the pointwise domination of the two window integrands by the `ℋ⁴`-integrand
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have hcomm : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
            = Work.Spaces.mixed (j + 1) i f x σ := rfl
        rw [hcomm]
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact mixed_succ_mul_w_sq_le_HkIntegrand hx0 hσ j i hi (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2
            = (Work.Spaces.mixed j i f x σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact mixed_sq_le_HkIntegrand (lt_of_lt_of_le hRpos hx.1) hσ j i hi (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      -- the weight factors out of the interval integrals
      have hAeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2)
          = ∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hBeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)
          = ∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f x σ) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z σ) ^ 2 := by ring
        _ ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (2 * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                      * Work.Spaces.w x) ^ 2)
                + (2 / R₀) * ∫ x in R₀..(2 * R₀),
                    (Work.Spaces.mixed j i f x σ) ^ 2) :=
              mul_le_mul_of_nonneg_left hwin hlam
        _ = 2 * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2))
              + (2 / R₀) * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)) := by ring
        _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2)
              + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j i f x σ) ^ 2) := by
              rw [hAeq, hBeq]
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
              + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by
              ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hfae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1],
            by linarith [hσ.2, Real.pi_pos]⟩) _)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          integral_mono_of_nonneg hfae (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end Work.FTS.TransportS.T2SupB2
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T3BadAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3BadAux

set_option autoImplicit false

set_option maxHeartbeats 1000000

/-! ## The `Badz`/`Hhard` identification -/


/-! ## The weights -/

/-- `(w / sin(2θ)^{η/2})² = w² sin(2θ)^{-η}`. -/
theorem w_div_sin_sq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    norm_num
  rw [div_pow, h1, Real.rpow_neg hs, div_eq_mul_inv]

/-- `Wt α z θ ² = w² sin(2θ)^{-γ}`. -/
theorem Wt_sq_eq {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    ring_nf
  rw [Spaces.Wt, Spaces.wTheta, mul_pow, h1]

/-! ## The weighted blocks -/



/-! ## The angular densities against `HkIntegrand` -/

/-- Each weighted order-four block is a single summand of `HkIntegrand α 4 g`. -/
theorem Thard_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have h := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 (by norm_num)
    rw [mul_pow, w_div_sin_sq hθ] at h
    have hT : Work.FTS.H2.Thard g 0 z θ = Spaces.DzIter 4 g z θ := by
      simp [Work.FTS.H2.Thard_eq_mixed, Work.Spaces.mixed_zero_right]
    rw [hT, Work.FTS.H2.sghard_apply_zero α θ]
    nlinarith [h]
  · have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ k.val (4 - k.val) (by omega)
      (by have := k.isLt; omega)
    rw [mul_pow, Wt_sq_eq (α := α) hθ] at h
    have hT : Work.FTS.H2.Thard g k z θ = Spaces.mixed (4 - k.val) k.val g z θ := by
      rw [Work.FTS.H2.Thard_eq_mixed]
    rw [hT, Work.FTS.H2.sghard_apply_ne α k hk]
    nlinarith [h]

/-- Each weighted order-five block is a single summand of `HkIntegrand α 5 g`. -/
theorem DzThard_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have h := Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 5 (by norm_num)
    rw [mul_pow, w_div_sin_sq hθ] at h
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Spaces.DzIter 5 g z θ := by
      simp [Work.FTS.TransportS.Dz_Thard]
    rw [hdz, Work.FTS.H2.sghard_apply_zero α θ]
    nlinarith [h]
  · have h := Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (5 - k.val) (by omega)
      (by have := k.isLt; omega)
    rw [mul_pow, Wt_sq_eq (α := α) hθ] at h
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        = Spaces.mixed (5 - k.val) k.val g z θ := by
      rw [Work.FTS.TransportS.Dz_Thard]
    rw [hdz, Work.FTS.H2.sghard_apply_ne α k hk]
    nlinarith [h]







/-! ## Domination of `Hhard` -/


end Work.FTS.TransportS.T3BadAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3BadAux

set_option autoImplicit false

theorem slot_slice_le {α Mf θ : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)))
    (hucd : ContDiffOn ℝ 1 (fun z => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)))
    (hfb : ∀ z ∈ Work.Spaces.Iz, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr0 : Filter.Tendsto
      (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htrT : Filter.Tendsto
      (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
      Filter.atTop (nhds 0))
    (hint1 : MeasureTheory.IntegrableOn (fun z => f z θ * z * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.Thard g k z θ * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.TransportS.gK' α f g k z θ) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
        (fun z => (Work.FTS.TransportS.Xz α g k z θ) ^ 2) (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.gK α f g k z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.FTS.TransportS.Xz α g k z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set S : ℝ := Work.FTS.H2.sghard α k θ with hS
  set V : ℝ → ℝ := fun z => Work.FTS.H2.Thard g k z θ with hV
  set V' : ℝ → ℝ := fun z => Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ with hV'
  set φ : ℝ → ℝ := fun z => f z θ * (z * (Work.Spaces.w z) ^ 2) with hφ
  set φ' : ℝ → ℝ := fun z => Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) with hφ'
  have hSpos : 0 < S := by
    rw [hS]
    rcases eq_or_ne k.val 0 with hk | hk
    · rw [show k = 0 from Fin.ext hk, Work.FTS.H2.sghard_apply_zero]
      exact Real.rpow_pos_of_pos hsin _
    · rw [Work.FTS.H2.sghard_apply_ne α k hk θ]
      exact Real.rpow_pos_of_pos hsin _
  have hSne : S ≠ 0 := ne_of_gt hSpos
  -- ## The pointwise identities
  have hgK_pt : ∀ z : ℝ, gK α f g k z θ = S * (φ z * V z * V' z) := by
    intro z
    simp only [gK, hS, hφ, hV, hV'] <;> ring
  have hgK'_pt : ∀ z : ℝ, gK' α f g k z θ = φ' z * V z ^ 2 := by
    intro z
    simp only [gK', hφ', hV]
  have hXz_pt : ∀ z : ℝ, (Xz α g k z θ) ^ 2 = S * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := by
    intro z
    simp only [hS, hV, Xz_sq (α := α) g k z θ hθI] <;> ring
  -- ## The derivative hypotheses
  have hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z := by
    intro z hz
    have hd := ((hucd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    simp only [hV, hV', Work.Spaces.pz] at hd ⊢
    exact hd
  have hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z := by
    intro z hz
    have hf : HasDerivAt (fun z' => f z' θ) (Work.Spaces.pz f z θ) z := by
      have hd := ((hφcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      simpa only [Work.Spaces.pz] using hd
    have hzw := Work.FTS.H2.hasDerivAt_zw2 hz
    have h := hf.mul hzw
    simp only [hφ, hφ'] at h ⊢
    convert h using 1
    ring
  -- ## The transfer of the integrability and boundary hypotheses
  have hlim0 : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [hV] using htr0
  have hlimTop : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [hV] using htrT
  have hint1' : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint1 ?_ measurableSet_Ioi
    intro z _
    simp only [hφ, hV, hV'] <;> ring
  have hint2' : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint2 ?_ measurableSet_Ioi
    intro z _
    simp only [gK', hφ', hV]
  have hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hz
    have hzw : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg hz (sq_nonneg _)
    simp only [hφ]
    rw [abs_mul, abs_of_nonneg hzw]
    exact mul_le_mul_of_nonneg_right (hfb z hzIz) hzw
  -- ## The pointwise bound for the integration-by-parts integrand
  have hgK'_le : ∀ z : ℝ, 0 < z →
      |gK' α f g k z θ| ≤ 4 * Mf * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hratio : |(z - 3) / (1 + z)| ≤ 3 := Work.FTS.H2.abs_ratio_le_three z hz
    have h2 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
        ≤ Mf * (Work.Spaces.w z) ^ 2 := by
      rw [show Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            = (Work.Spaces.pz f z θ * z) * (Work.Spaces.w z) ^ 2 from by ring,
        abs_mul, abs_of_nonneg hw2,
        show |Work.Spaces.pz f z θ * z| = |Work.Spaces.Dz f z θ| from by
          rw [Work.Spaces.Dz, mul_comm]]
      exact mul_le_mul_of_nonneg_right (hDfb z hzIz) hw2
    have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw2]
      calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
          ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) :=
            mul_le_mul (hfb z hzIz) (mul_le_mul_of_nonneg_left hratio hw2)
              (mul_nonneg hw2 (abs_nonneg _)) hMf
        _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
    have h1 : |φ' z| ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
      simp only [hφ']
      calc |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
              + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
          ≤ |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
            + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
        _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
        _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
    rw [hgK'_pt z, abs_mul, abs_of_nonneg (sq_nonneg (V z))]
    calc |φ' z| * V z ^ 2 ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * V z ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 4 * Mf * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by ring
  -- ## The monotonicity step against the `Xz²`-majorant
  have hMle : (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|)
      ≤ (4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        |gK' α f g k z θ| ≤ (4 * Mf / S) * (Xz α g k z θ) ^ 2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      calc |gK' α f g k z θ| ≤ 4 * Mf * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := hgK'_le z hz
        _ = (4 * Mf / S) * (Xz α g k z θ) ^ 2 := by
            rw [hXz_pt z]
            field_simp
    calc (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (4 * Mf / S) * (Xz α g k z θ) ^ 2 :=
          MeasureTheory.integral_mono_ae hint2.abs
            (MeasureTheory.Integrable.const_mul hint3 (4 * Mf / S)) hpt
      _ = (4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 :=
          MeasureTheory.integral_const_mul (4 * Mf / S) _
  -- ## The integration by parts identity
  have hIntgK : (∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ)
      = -(S / 2) * ∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ := by
    have hzibp := zibp_Ioi (Mf := Mf) hMf hderivφ hderivV hint1' hint2' hφbnd hlim0 hlimTop
    have hIntK' : (∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun z => (hgK'_pt z).symm))
    have h1 : (∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ)
        = S * ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgK_pt)]
      exact MeasureTheory.integral_const_mul S (fun z => φ z * V z * V' z)
    rw [h1, hzibp, hIntK']
    ring
  -- ## Conclusion
  have habs : |∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ|
      = (S / 2) * |∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ| := by
    rw [hIntgK, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ S / 2)]
  calc |∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ|
      = (S / 2) * |∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ| := habs
    _ ≤ (S / 2) * (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (fun z => gK' α f g k z θ)
    _ ≤ (S / 2) * ((4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hMle (by linarith)
    _ = 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 := by
        field_simp
        ring

end Work.FTS.TransportS.T3BadAux
end
end
