/-
# Level-six `T1` slot: the remaining analytic helpers

This module collects the helpers used by the proof of
`Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ` beyond `T1SlotZ/Base.lean`:

* `continuousOn_Wt_Q0` — joint continuity of the weight `Wt α = w·sin(2·)^{-γ/2}` on the open
  quadrant;
* `le_const_mul_alpha` — the elementary `c ≤ K` monotonicity of
  `c·α^{-1/2}·X·Z ≤ K·α^{-1/2}·X·Z` for `X, Z ≥ 0`;
* `L2Mem_of_le_HkIntegrand` — if the square of `B` is dominated pointwise by the
  `ℋ⁶`-integrand of `g`, then `B ∈ L²` in the iterated sense and `L2Sq B ≤ HkSq α 6 g`;
* `iterated_cs_le` — the two-dimensional Cauchy–Schwarz over `[0,∞) × [0,π/2]`: if
  `S ≤ |A·B|` on the open quadrant (and `S ≥ 0` there), then `∫∫S` converges and is at most
  `√(L2Sq A)·√(L2Sq B)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SlotZ

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_eta_eq canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Joint continuity of `Wt` -/

theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  refine ContinuousOn.mul ?_ ?_
  · show ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2) Work.FTS.EllipticEst.Q0
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  · refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt ?_)
    show 0 < Real.sin (2 * p.2)
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h := hp.2.1; linarith
    · have h := hp.2.2; linarith [Real.pi_pos]

/-! ## An arithmetic monotonicity -/

theorem le_const_mul_alpha {α c K X Z : ℝ} (hα : 0 < α) (hcK : c ≤ K)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) :
    c * α ^ (-(1 / 2 : ℝ)) * X * Z ≤ K * α ^ (-(1 / 2 : ℝ)) * X * Z := by
  have h1 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * X * Z :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hα.le _) hX) hZ
  rw [show c * α ^ (-(1 / 2 : ℝ)) * X * Z = c * (α ^ (-(1 / 2 : ℝ)) * X * Z) from by ring,
    show K * α ^ (-(1 / 2 : ℝ)) * X * Z = K * (α ^ (-(1 / 2 : ℝ)) * X * Z) from by ring]
  exact mul_le_mul_of_nonneg_right hcK h1

/-! ## A function dominated by the `ℋ⁶`-integrand is `L²` -/

theorem L2Mem_of_le_HkIntegrand {α : ℝ} {B g : ℝ → ℝ → ℝ}
    (hBc : ContinuousOn (Function.uncurry B) Work.FTS.EllipticEst.Q0)
    (hmemG : Work.Spaces.HkMem α 6 g)
    (hslice_aesm : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => (B z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hpt : ∀ z θ : ℝ, 0 ≤ z → 0 < θ → θ < Real.pi / 2 →
      (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ) :
    Work.Spaces.L2Mem B ∧ Work.Spaces.L2Sq B ≤ Work.Spaces.HkSq α 6 g := by
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (B p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hBc.pow 2)
  have hmarg : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hjoint
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmemG.1 z hz) (hslice_aesm z hz) ?_
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt z θ hz hθ.1 hθ.2
  constructor
  · refine ⟨hslice, ?_⟩
    refine MeasureTheory.Integrable.mono' hmemG.2 hmarg ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmemG.1 z hz) (ae_Iθ_of_forall_Ioo (fun θ hθ => hpt z θ hz hθ.1 hθ.2))
  · rw [Work.Spaces.L2Sq, Work.Spaces.HkSq]
    refine Work.FTS.TransportS.SlotT2.integral_Iz_mono (fun z hz => ?_)
      (fun z _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _))
      hmemG.2
    exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmemG.1 z hz) (ae_Iθ_of_forall_Ioo (fun θ hθ => hpt z θ hz hθ.1 hθ.2))

/-! ## The two-dimensional Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for the pairing of two `L²`-functions over the quadrant.**  If `S` is
nonnegative on the open quadrant, dominated there by `|A·B|`, and jointly a.e. strongly
measurable, and if `A`, `B` are square integrable in the iterated sense, then the radial
marginal of `S` is integrable and `∫_z∫_θ S ≤ √(L2Sq A)·√(L2Sq B)`. -/
theorem iterated_cs_le {A B S : ℝ → ℝ → ℝ}
    (hA : Work.Spaces.L2Mem A) (hB : Work.Spaces.L2Mem B)
    (hSjoint : AEStronglyMeasurable (Function.uncurry S)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hSnn : ∀ z θ : ℝ, 0 ≤ z → 0 < θ → θ < Real.pi / 2 → 0 ≤ S z θ)
    (hSle : ∀ z θ : ℝ, 0 ≤ z → 0 < θ → θ < Real.pi / 2 → S z θ ≤ |A z θ * B z θ|) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, S z θ) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, S z θ)
        ≤ Real.sqrt (Work.Spaces.L2Sq A) * Real.sqrt (Work.Spaces.L2Sq B) := by
  have hθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the radial majorant is integrable, by `√(FA z)√(FB z) ≤ (FA z + FB z)/2`
  have hmajInt : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' ((hA.2.add hB.2).const_mul (1 / 2)) ?_ ?_
    · exact (Real.continuous_sqrt.comp_aestronglyMeasurable
        hA.2.aestronglyMeasurable).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hB.2.aestronglyMeasurable)
    · refine MeasureTheory.ae_restrict_of_forall_mem hzm (fun z _ => ?_)
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2 :=
        MeasureTheory.setIntegral_nonneg hθm (fun θ _ => sq_nonneg _)
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2 :=
        MeasureTheory.setIntegral_nonneg hθm (fun θ _ => sq_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      have habs := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add
        (Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2))
        (Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2))
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        Real.sq_sqrt h1, Real.sq_sqrt h2] at habs
      calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
          ≤ ((∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) / 2 := habs
        _ = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) := by ring
  -- the angular Cauchy–Schwarz, at every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, S z θ)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) := by
    intro z hz
    have hABint : MeasureTheory.IntegrableOn (fun θ => |A z θ * B z θ|) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono'
        (((hA.1 z hz).add (hB.1 z hz)).const_mul (1 / 2)) ?_ ?_
      · have h1 : AEStronglyMeasurable
            (fun θ => (A z θ) ^ 2 * (B z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          MeasureTheory.AEStronglyMeasurable.mul (hA.1 z hz).aestronglyMeasurable
            (hB.1 z hz).aestronglyMeasurable
        refine (Real.continuous_sqrt.comp_aestronglyMeasurable h1).congr ?_
        exact Filter.Eventually.of_forall fun θ => by
          simp only [Real.sqrt_mul (sq_nonneg (A z θ)), Real.sqrt_sq_eq_abs, abs_mul]
      · refine MeasureTheory.ae_restrict_of_forall_mem hθm (fun θ _ => ?_)
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        have habs := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (A z θ) (B z θ)
        calc |A z θ * B z θ| ≤ (A z θ ^ 2 + B z θ ^ 2) / 2 := habs
          _ = (1 / 2) * (A z θ ^ 2 + B z θ ^ 2) := by ring
    calc (∫ θ in Work.Spaces.Iθ, S z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, |A z θ * B z θ| :=
          MeasureTheory.integral_mono_of_nonneg
            (ae_Iθ_of_forall_Ioo fun θ hθ => hSnn z θ hz hθ.1 hθ.2) hABint
            (ae_Iθ_of_forall_Ioo fun θ hθ => hSle z θ hz hθ.1 hθ.2)
      _ = ∫ θ in Work.Spaces.Iθ, Real.sqrt ((A z θ) ^ 2) * Real.sqrt ((B z θ) ^ 2) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          simp only [Real.sqrt_sq_eq_abs, abs_mul]
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) :=
          Work.FTS.TransportS.SlotT2.cs_sqrt_le (hA.1 z hz) (hB.1 z hz)
            (fun θ => sq_nonneg _) (fun θ => sq_nonneg _)
  constructor
  · refine MeasureTheory.Integrable.mono' hmajInt ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' hSjoint
    · refine MeasureTheory.ae_restrict_of_forall_mem hzm (fun z hz => ?_)
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, S z θ :=
        MeasureTheory.integral_nonneg_of_ae
          (ae_Iθ_of_forall_Ioo fun θ hθ => hSnn z θ hz hθ.1 hθ.2)
      rw [Real.norm_of_nonneg hnn]
      exact hslice z hz
  · calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, S z θ)
        ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem hzm (fun z hz =>
              MeasureTheory.integral_nonneg_of_ae
                (ae_Iθ_of_forall_Ioo fun θ hθ => hSnn z θ hz hθ.1 hθ.2)))
            hmajInt (MeasureTheory.ae_restrict_of_forall_mem hzm hslice)
      _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) :=
          Work.FTS.TransportS.SlotT2.cs_sqrt_le hA.2 hB.2
            (fun z => MeasureTheory.setIntegral_nonneg hθm (fun θ _ => sq_nonneg _))
            (fun z => MeasureTheory.setIntegral_nonneg hθm (fun θ _ => sq_nonneg _))
      _ = Real.sqrt (Work.Spaces.L2Sq A) * Real.sqrt (Work.Spaces.L2Sq B) := rfl

end Work.FTS.StrongPersist.N6Trans.T1SlotZ
