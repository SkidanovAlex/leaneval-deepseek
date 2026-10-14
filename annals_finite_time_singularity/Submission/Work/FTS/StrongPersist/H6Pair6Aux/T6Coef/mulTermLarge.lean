import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

set_option quotPrecheck false in
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

private lemma eta_le_slotW {α : ℝ} (hα : 0 < α) (a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.leafEta z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
  fun z θ _ hθ0 hθ1 => Work.FTS.TransportS.leafEta_le_slotW α hα ⟨hθ0, hθ1⟩

private lemma one_le_slotW {α : ℝ} (hα : 0 < α) (a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
  fun z θ _ hθ0 hθ1 => Work.FTS.TransportS.leafOne_le_slotW α hα ⟨hθ0, hθ1⟩

private lemma gam_le_slotW {α : ℝ} (hα : 0 < α) (a : ℕ) (ha : 1 ≤ a) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.leafGam α z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
  fun z θ _ hθ0 hθ1 => Work.FTS.TransportS.leafGam_le_slotW α hα ha ⟨hθ0, hθ1⟩

/-! ## the assembly -/

theorem mulTermLarge : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      3 ≤ a₁ + b₁ → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  have hC1 := slotPairCS
  obtain ⟨C2, hC2pos, hC2⟩ := midSlotSupLe
  obtain ⟨C4, hC4pos, hC4⟩ := leafGamPureZ
  obtain ⟨CP, hCPpos, hPw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  have hsq10 : 0 < Real.sqrt (10 * CP) := Real.sqrt_pos_of_pos (by linarith)
  have hCCpos : 0 < C4 + C2 + C2 + Real.sqrt (10 * CP) + 1 := by
    have h1 : 0 < Real.sqrt (10 * CP) := Real.sqrt_pos_of_pos (by linarith)
    linarith
  refine ⟨C4 + C2 + C2 + Real.sqrt (10 * CP) + 1, hCCpos, ?_⟩
  intro α hαI A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp ha₁ hb₁ hab hleaf
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hK0 : 0 ≤ K0 := by
    have hv := hcoef.val 1 1 (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
    have := abs_nonneg (A 1 1)
    linarith
  have hSq : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hdat.sm 4 (by norm_num) hdat.h6
  have hXn4 : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1
  have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.LocData.Qd := by
    rcases hleaf with h | h | ⟨-, h⟩
    · subst h
      simpa [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW] using
        Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
    · subst h
      simpa [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW] using
        Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
    · subst h
      simpa [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW] using
        Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
  have hcA : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i A p.1 p.2)
      Work.FTS.LocData.Qd := fun j i =>
    Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hcoef.sm j i
  have hcf : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.LocData.Qd := fun j i =>
    Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hdat.sm j i
  have hpow : α ^ (-(1/2:ℝ)) ≤ α ^ (-(3:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hA3nn : 0 ≤ α ^ (-(3:ℝ)) := Real.rpow_nonneg hα0.le _
  set RHS : ℝ := (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hRHSdef
  have hRHSnn : 0 ≤ RHS := by
    rw [hRHSdef]
    exact add_nonneg (mul_nonneg (add_nonneg (add_nonneg zero_le_one hK0) hK4)
        (add_nonneg zero_le_one hSq))
      (mul_nonneg (mul_nonneg (add_nonneg hK4 hK6) (add_nonneg zero_le_one hM))
        (add_nonneg zero_le_one hN6))
  have hRHS2 : (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) ≤ RHS := by
    rw [hRHSdef]
    exact le_add_of_nonneg_left (mul_nonneg (add_nonneg (add_nonneg zero_le_one hK0) hK4)
      (add_nonneg zero_le_one hSq))
  have hRHS1 : (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) ≤ RHS := by
    rw [hRHSdef]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (add_nonneg hK4 hK6)
      (add_nonneg zero_le_one hM)) (add_nonneg zero_le_one hN6))
  have supSlot : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen G →
      Work.Spaces.HkMem α 6 G → ∀ (KG : ℝ), Work.Spaces.HkNorm α 6 G ≤ KG →
      ∀ (b' a' : ℕ), a' + b' ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b' a' G z θ| ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * KG := by
    intro G hGsm hGmem KG hKG b' a' hba z θ hz hθ0 hθ1
    have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h1 := hPw α G b' a' hα0 hα1 hGsm hGmem hba z hz θ ⟨hθ0, hθ1⟩
    have h2 : Real.sqrt ((Work.Spaces.mixed b' a' G z θ) ^ 2)
        ≤ Real.sqrt (CP / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 G) :=
      Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    have hG0 : 0 ≤ Work.Spaces.HkSq α 6 G := Work.Spaces.HkSq_nonneg α 6 G
    have hKG0 : 0 ≤ KG := le_trans (Work.Spaces.HkNorm_nonneg α 6 G) hKG
    have hdiv : CP / (Work.Spaces.gam α - 1) = 10 * CP * α ^ (-(1:ℝ)) := by
      rw [Work.Spaces.gam_sub_one, Real.rpow_neg_one]
      field_simp
    have hexp : (10:ℝ) * CP * α ^ (-(1:ℝ)) * Work.Spaces.HkSq α 6 G
        = (10 * CP) * (α ^ (-(1/2:ℝ)) * α ^ (-(1/2:ℝ))) * Work.Spaces.HkSq α 6 G := by
      rw [← Real.rpow_add hα0]; norm_num
    calc |Work.Spaces.mixed b' a' G z θ|
        ≤ Real.sqrt (CP / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 G) := h2
      _ = Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Real.sqrt (Work.Spaces.HkSq α 6 G) := by
          rw [hdiv, hexp, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            show α ^ (-(1/2:ℝ)) * α ^ (-(1/2:ℝ)) = (α ^ (-(1/2:ℝ))) ^ 2 from (pow_two _).symm,
            Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * KG := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hKG
  have routeM : ∀ (l : ℕ) (hl6 : l ≤ 6) (hmemL : Work.Spaces.HkMem α l A) (K : ℝ)
      (hK : Real.sqrt (Work.Spaces.HkSq α l A) ≤ K) (hKle : K ≤ K4 + K6),
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → ρ z θ ≤ Work.FTS.TransportS.slotW α a₁ z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed b a f z θ|
            ≤ Real.sqrt (Work.Spaces.HkIntegrand α l A z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) →
      ((a - a₁) + (b - b₁) ≤ 2) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
        ≤ C2 * α ^ (-(3:ℝ)) * RHS := by
    intro l hl6 hmemL K hK hKle hρA hρf hdom hc2
    have hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| ≤ C2 * α ^ (-(1/2:ℝ)) * (1+M) :=
      (hC2 α f a b a₁ b₁ M hαI hdat.sm hdat.h6 hdat.bdd ha₁ hb₁ hp hab).1 hc2
    have hcont1 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * |Work.Spaces.mixed b₁ a₁ A p.1 p.2| * |Work.Spaces.mixed b a f p.1 p.2|)
        Work.FTS.LocData.Qd :=
      ((hρcont.mul (hcA b₁ a₁).abs).mul (hcf b a).abs)
    have hcont2 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.LocData.Qd :=
      (((hρcont.mul (hcA b₁ a₁)).mul (hcf (b - b₁) (a - a₁))).mul (hcf b a))
    obtain ⟨hint, hbnd⟩ := hC1 α A f (Work.Spaces.mixed b₁ a₁ A)
      (Work.Spaces.mixed (b - b₁) (a - a₁) f) (Work.Spaces.mixed b a f) ρ l
      (C2 * α ^ (-(1/2:ℝ)) * (1+M)) hαI hl6 hcoef.sm hmemL hdat.sm hdat.h6
      (by positivity) hρnn hcont1 hcont2 hsup hdom
    refine ⟨hint, ?_⟩
    refine hbnd.trans ?_
    have hBpos : 0 ≤ C2 * α ^ (-(1/2:ℝ)) * (1+M) :=
      mul_nonneg (mul_nonneg hC2pos.le (Real.rpow_nonneg hα0.le _)) (by linarith)
    have hK0' : 0 ≤ K := le_trans (Real.sqrt_nonneg _) hK
    calc (C2 * α ^ (-(1/2:ℝ)) * (1+M))
          * (Real.sqrt (Work.Spaces.HkSq α l A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        ≤ (C2 * α ^ (-(1/2:ℝ)) * (1+M)) * (K * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul_of_nonneg_left ?_ hBpos
          exact mul_le_mul hK le_rfl hN6 hK0'
      _ ≤ C2 * α ^ (-(3:ℝ)) * RHS := by
          have hmain : (C2 * α ^ (-(1/2:ℝ)) * (1+M)) * (K * Work.Spaces.HkNorm α 6 f)
              ≤ C2 * α ^ (-(3:ℝ))
                * ((K4 + K6) * (1+M) * (1+Work.Spaces.HkNorm α 6 f)) := by
            calc (C2 * α ^ (-(1/2:ℝ)) * (1+M)) * (K * Work.Spaces.HkNorm α 6 f)
                = (C2 * (α ^ (-(1/2:ℝ)) * (1+M))) * (K * Work.Spaces.HkNorm α 6 f) := by
                  ring
              _ ≤ (C2 * (α ^ (-(3:ℝ)) * (1+M)))
                    * ((K4 + K6) * (1+Work.Spaces.HkNorm α 6 f)) := by
                  refine mul_le_mul ?_ ?_ (mul_nonneg hK0' hN6)
                    (mul_nonneg hC2pos.le (mul_nonneg hA3nn (by linarith)))
                  · exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hpow (by linarith)) hC2pos.le
                  · exact mul_le_mul hKle (by linarith) hN6 (by linarith)
              _ = C2 * α ^ (-(3:ℝ))
                    * ((K4 + K6) * (1+M) * (1+Work.Spaces.HkNorm α 6 f)) := by ring
          exact le_trans hmain
            (mul_le_mul_of_nonneg_left hRHS2 (mul_nonneg hC2pos.le hA3nn))
  have routeK4 :
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → ρ z θ ≤ Work.FTS.TransportS.slotW α a₁ z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed b a f z θ|
            ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 A z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) →
      ((a - a₁) + (b - b₁) = 3) → a - a₁ = 0 → (a₁ + b₁ ≤ 4) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
        ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * K4 * Work.Spaces.HkNorm α 6 f
            * Work.Spaces.HkNorm α 6 f := by
    intro hρA hdom hc3 haa₁ hp4
    have hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
          ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 f := by
      intro z θ hz hθ0 hθ1
      rw [haa₁]
      exact supSlot f hdat.sm hdat.h6 (Work.Spaces.HkNorm α 6 f) le_rfl (b - b₁) 0
        (by omega) z θ hz hθ0 hθ1
    have hcont1 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * |Work.Spaces.mixed b₁ a₁ A p.1 p.2| * |Work.Spaces.mixed b a f p.1 p.2|)
        Work.FTS.LocData.Qd :=
      ((hρcont.mul (hcA b₁ a₁).abs).mul (hcf b a).abs)
    have hcont2 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.LocData.Qd :=
      (((hρcont.mul (hcA b₁ a₁)).mul (hcf (b - b₁) (a - a₁))).mul (hcf b a))
    have hBpos : 0 ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα0.le _)) hN6
    obtain ⟨hint, hbnd⟩ := hC1 α A f (Work.Spaces.mixed b₁ a₁ A)
      (Work.Spaces.mixed (b - b₁) (a - a₁) f) (Work.Spaces.mixed b a f) ρ 4
      (Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 f) hαI
      (by norm_num) hcoef.sm hcoef.h4 hdat.sm hdat.h6 hBpos hρnn hcont1 hcont2 hsup hdom
    refine ⟨hint, ?_⟩
    refine hbnd.trans ?_
    have hK : Real.sqrt (Work.Spaces.HkSq α 4 A) ≤ K4 := hcoef.n4
    have hK0' : 0 ≤ K4 := hK4
    calc (Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Real.sqrt (Work.Spaces.HkSq α 4 A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        ≤ (Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (K4 * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul_of_nonneg_left ?_ hBpos
          exact mul_le_mul hK le_rfl hN6 hK0'
      _ = Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * K4 * Work.Spaces.HkNorm α 6 f
            * Work.Spaces.HkNorm α 6 f := by ring
  have routeX :
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → ρ z θ ≤ Work.FTS.TransportS.slotW α (a - a₁) z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
              * |Work.Spaces.mixed b a f z θ|
            ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) →
      ((a₁ + b₁) ≤ 4) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
        ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A
            * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
    intro hρY hρf hdom hp4
    have hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b₁ a₁ A z θ|
          ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A :=
      supSlot A hcoef.sm hcoef.h6 (Work.Spaces.HkNorm α 6 A) le_rfl b₁ a₁ hp4
    have hcont1 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
        * |Work.Spaces.mixed b a f p.1 p.2|) Work.FTS.LocData.Qd :=
      ((hρcont.mul (hcf (b - b₁) (a - a₁)).abs).mul (hcf b a).abs)
    have hcont2 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.LocData.Qd :=
      (((hρcont.mul (hcf (b - b₁) (a - a₁))).mul (hcA b₁ a₁)).mul (hcf b a))
    have hBpos : 0 ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα0.le _))
        (Work.Spaces.HkNorm_nonneg α 6 A)
    obtain ⟨hint, hbnd⟩ := hC1 α f f (Work.Spaces.mixed (b - b₁) (a - a₁) f)
      (Work.Spaces.mixed b₁ a₁ A) (Work.Spaces.mixed b a f) ρ 4
      (Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A) hαI
      (by norm_num) hdat.sm hf4 hdat.sm hdat.h6 hBpos hρnn hcont1 hcont2 hsup hdom
    have heq : (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        = fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2 := by
      funext p; ring
    refine ⟨heq ▸ hint, ?_⟩
    rw [← heq]
    exact hbnd
  have hpow10 : Real.sqrt (10 * CP) ≤ C4 + C2 + C2 + Real.sqrt (10 * CP) + 1 := by
    linarith [hC4pos, hC2pos]
  have hC2le : C2 ≤ C4 + C2 + C2 + Real.sqrt (10 * CP) + 1 := by
    linarith [hC4pos, hC2pos, hsq10]
  have hC4le : C4 ≤ C4 + C2 + C2 + Real.sqrt (10 * CP) + 1 := by
    linarith [hC2pos, hsq10]
  have xstep : Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A
        * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f))
      ≤ (C4 + C2 + C2 + Real.sqrt (10 * CP) + 1) * α ^ (-(3:ℝ)) * RHS := by
    have hcd : K6 * M * Work.Spaces.HkNorm α 6 f
        ≤ (K4 + K6) * (1+M) * (1+Work.Spaces.HkNorm α 6 f) := by
      calc K6 * M * Work.Spaces.HkNorm α 6 f
          = (K6 * M) * Work.Spaces.HkNorm α 6 f := by ring
        _ ≤ ((K4 + K6) * (1+M)) * (1+Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul ?_ (by linarith) hN6
              (mul_nonneg (by linarith) (by linarith))
            exact mul_le_mul (by linarith) (by linarith) hM (by linarith)
        _ = (K4 + K6) * (1+M) * (1+Work.Spaces.HkNorm α 6 f) := by ring
    calc Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * Work.Spaces.HkNorm α 6 A
          * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        ≤ Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * K6
          * (M * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul ?_ ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα0.le _)) hK6)
          · refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα0.le _))
            exact hcoef.n6
          · exact mul_le_mul hdat.bdd le_rfl hN6 hM
      _ ≤ Real.sqrt (10 * CP) * α ^ (-(3:ℝ)) * RHS := by
          refine le_trans ?_ (mul_le_mul_of_nonneg_left hRHS2
            (mul_nonneg (Real.sqrt_nonneg _) hA3nn))
          calc Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * K6
                * (M * Work.Spaces.HkNorm α 6 f)
              = Real.sqrt (10 * CP) * (α ^ (-(1/2:ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f)) := by
                ring
            _ ≤ Real.sqrt (10 * CP) * (α ^ (-(3:ℝ))
                  * ((K4 + K6) * (1+M) * (1+Work.Spaces.HkNorm α 6 f))) := by
                refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
                exact mul_le_mul hpow hcd
                  (mul_nonneg (mul_nonneg (by linarith) hM) hN6) hA3nn
            _ = _ := by ring
      _ ≤ (C4 + C2 + C2 + Real.sqrt (10 * CP) + 1) * α ^ (-(3:ℝ)) * RHS := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow10 hA3nn) hRHSnn
  rcases hleaf with hρe | hρo | ⟨ha1, hρg⟩
  · -- ### `ρ = leafEta`
    subst hρe
    have hw : ∀ a' : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → Work.FTS.TransportS.leafEta z θ ≤ Work.FTS.TransportS.slotW α a' z θ :=
      fun a' => eta_le_slotW hα0 a'
    by_cases hc2 : (a - a₁) + (b - b₁) ≤ 2
    · by_cases hp4 : a₁ + b₁ ≤ 4
      · obtain ⟨hint, hbnd⟩ := routeM 4 (by norm_num) hcoef.h4 K4 hcoef.n4 (by linarith)
          (hw a₁) (hw a) (pairDom hα0 hρnn (hw a₁) (hw a) (Or.inr ⟨rfl, hp4⟩) hab) hc2
        refine ⟨hint, hbnd.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
      · obtain ⟨hint, hbnd⟩ := routeM 6 (by norm_num) hcoef.h6 K6 hcoef.n6 (by linarith)
          (hw a₁) (hw a) (pairDom hα0 hρnn (hw a₁) (hw a) (Or.inl ⟨rfl, by omega⟩) hab) hc2
        refine ⟨hint, hbnd.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
    · have hc3 : (a - a₁) + (b - b₁) = 3 := by omega
      have hc4 : (a - a₁) + (b - b₁) ≤ 4 := by omega
      obtain ⟨hint, hbnd⟩ := routeX (hw (a - a₁)) (hw a)
        (pairDom hα0 hρnn (hw (a - a₁)) (hw a) (Or.inr ⟨rfl, hc4⟩) hab) (by omega)
      exact ⟨hint, hbnd.trans xstep⟩
  · -- ### `ρ = leafOne`
    subst hρo
    have hw : ∀ a' : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
        → Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.TransportS.slotW α a' z θ :=
      fun a' => one_le_slotW hα0 a'
    by_cases hc2 : (a - a₁) + (b - b₁) ≤ 2
    · by_cases hp4 : a₁ + b₁ ≤ 4
      · obtain ⟨hint, hbnd⟩ := routeM 4 (by norm_num) hcoef.h4 K4 hcoef.n4 (by linarith)
          (hw a₁) (hw a) (pairDom hα0 hρnn (hw a₁) (hw a) (Or.inr ⟨rfl, hp4⟩) hab) hc2
        refine ⟨hint, hbnd.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
      · obtain ⟨hint, hbnd⟩ := routeM 6 (by norm_num) hcoef.h6 K6 hcoef.n6 (by linarith)
          (hw a₁) (hw a) (pairDom hα0 hρnn (hw a₁) (hw a) (Or.inl ⟨rfl, by omega⟩) hab) hc2
        refine ⟨hint, hbnd.trans ?_⟩
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
    · have hc3 : (a - a₁) + (b - b₁) = 3 := by omega
      have hc4 : (a - a₁) + (b - b₁) ≤ 4 := by omega
      obtain ⟨hint, hbnd⟩ := routeX (hw (a - a₁)) (hw a)
        (pairDom hα0 hρnn (hw (a - a₁)) (hw a) (Or.inr ⟨rfl, hc4⟩) hab) (by omega)
      exact ⟨hint, hbnd.trans xstep⟩
  · -- ### `ρ = leafGam`
    subst hρg
    by_cases ha₁0 : a₁ = 0
    · -- the delegated exceptional case
      obtain ⟨hint, hbnd⟩ := hC4 α hαI A f K0 K4 K6 M a b a₁ b₁ hcoef hdat ha₁0 ha1 ha₁ hb₁ hp hab
      rw [← hRHSdef] at hbnd
      refine ⟨hint, ?_⟩
      refine hbnd.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4le hA3nn) hRHSnn
    · have ha₁1 : 1 ≤ a₁ := Nat.one_le_iff_ne_zero.mpr ha₁0
      have hwA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
          → Work.FTS.TransportS.leafGam α z θ ≤ Work.FTS.TransportS.slotW α a₁ z θ :=
        gam_le_slotW hα0 a₁ ha₁1
      have hwZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
          → Work.FTS.TransportS.leafGam α z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
        gam_le_slotW hα0 a ha1
      by_cases hc2 : (a - a₁) + (b - b₁) ≤ 2
      · by_cases hp4 : a₁ + b₁ ≤ 4
        · obtain ⟨hint, hbnd⟩ := routeM 4 (by norm_num) hcoef.h4 K4 hcoef.n4 (by linarith)
            hwA hwZ (pairDom hα0 hρnn hwA hwZ (Or.inr ⟨rfl, hp4⟩) hab) hc2
          refine ⟨hint, hbnd.trans ?_⟩
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
        · obtain ⟨hint, hbnd⟩ := routeM 6 (by norm_num) hcoef.h6 K6 hcoef.n6 (by linarith)
            hwA hwZ (pairDom hα0 hρnn hwA hwZ (Or.inl ⟨rfl, by omega⟩) hab) hc2
          refine ⟨hint, hbnd.trans ?_⟩
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hA3nn) hRHSnn
      · have hc3 : (a - a₁) + (b - b₁) = 3 := by omega
        have hc4 : (a - a₁) + (b - b₁) ≤ 4 := by omega
        have hp4 : a₁ + b₁ ≤ 4 := by omega
        by_cases hya : a - a₁ = 0
        · -- the `(X,Z)`-pair at level 4, sup on `Y` via PwAny6
          have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              Work.FTS.TransportS.leafGam α z θ * |Work.Spaces.mixed b₁ a₁ A z θ|
                * |Work.Spaces.mixed b a f z θ|
                ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 A z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) :=
            pairDom hα0 hρnn hwA hwZ (Or.inr ⟨rfl, hp4⟩) hab
          obtain ⟨hint, hbnd⟩ := routeK4 hwA hdom hc3 hya hp4
          refine ⟨hint, ?_⟩
          refine hbnd.trans ?_
          have hsq : Work.Spaces.HkSq α 6 f = (Work.Spaces.HkNorm α 6 f) ^ 2 :=
            (Real.sq_sqrt hSq).symm
          have hRHS1' : K4 * Work.Spaces.HkSq α 6 f ≤ RHS := by
            refine le_trans ?_ hRHS1
            exact mul_le_mul (by linarith) (by linarith) hSq (by linarith)
          calc Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * K4 * Work.Spaces.HkNorm α 6 f
                * Work.Spaces.HkNorm α 6 f
              = Real.sqrt (10 * CP) * α ^ (-(1/2:ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) := by
                rw [hsq]; ring
            _ ≤ Real.sqrt (10 * CP) * α ^ (-(3:ℝ)) * RHS := by
                refine mul_le_mul ?_ ?_ (mul_nonneg hK4 hSq)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα0.le _))
                · exact mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
                · exact hRHS1'
            _ ≤ (C4 + C2 + C2 + Real.sqrt (10 * CP) + 1) * α ^ (-(3:ℝ)) * RHS := by
                refine mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hpow10 hA3nn) hRHSnn
        · have haa1 : 1 ≤ a - a₁ := Nat.one_le_iff_ne_zero.mpr hya
          have hwY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
              → Work.FTS.TransportS.leafGam α z θ
                ≤ Work.FTS.TransportS.slotW α (a - a₁) z θ :=
            gam_le_slotW hα0 (a - a₁) haa1
          obtain ⟨hint, hbnd⟩ := routeX hwY hwZ
            (pairDom hα0 hρnn hwY hwZ (Or.inr ⟨rfl, hc4⟩) hab) hp4
          refine ⟨hint, ?_⟩
          exact hbnd.trans xstep

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
