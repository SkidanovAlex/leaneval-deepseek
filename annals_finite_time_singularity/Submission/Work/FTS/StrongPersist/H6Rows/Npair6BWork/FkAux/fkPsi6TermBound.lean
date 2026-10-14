import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.psi6LowSlice
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1Small
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.RowFKfCore2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

noncomputable section

theorem fkRow_Wf_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h6 : Work.Spaces.HkMem α 6 f)
    (h7 : Work.Spaces.HkMem α 7 f) {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6) (hbk : k ≤ b)
    {C2 : ℝ} (hC2 : 0 < C2) (hk6 : k ≤ 6)
    (hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ C2 * Work.Spaces.HkSq α (k + 1) f) :
    MeasureTheory.Integrable (fun z => (-(1 / 2)) * ((b.choose k : ℝ)
        * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
            * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ
  set Kk : ℝ := Real.sqrt (C2 * Work.Spaces.HkSq α (k + 1) f) + 1 with hKkdef
  have hKk0 : 0 ≤ Kk := by rw [hKkdef]; positivity
  -- the a.e. bound on the radial factor
  have hArK : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z| ≤ Kk := by
    filter_upwards [hpt] with z hz
    have h1 : |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
        ≤ Real.sqrt (C2 * Work.Spaces.HkSq α (k + 1) f) := by
      have h2 := Real.sqrt_le_sqrt hz
      rwa [Real.sqrt_sq_eq_abs] at h2
    linarith
  -- the pointwise-in-`z` bound on the angular pairing
  have hJbind : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ| ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 7 f z θ := by
    intro z hz
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ θ in Work.Spaces.Iθ, ρ z θ * |Work.Spaces.mixed (b - k) (a + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [haeθ] with θ hθ
          rw [abs_mul, abs_mul, abs_of_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (h7.1 z hz) ?_
        · filter_upwards [haeθ] with θ hθ
          exact mul_nonneg (mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _)) (abs_nonneg _)
        · filter_upwards [haeθ] with θ hθ
          have hρ0 : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
          have hVe := domLeaf_le_row (f := f) hα hρ (by omega)
            (by omega : (a + 1) + (b - k) ≤ 7) hz hθ
          have hVf := domLeaf_le_row (f := f) hα hρ (le_refl a) (by omega : a + b ≤ 7) hz hθ
          have h4 : |Work.Spaces.mixed (b - k) (a + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|
              ≤ ((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
                + (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by
            have h2 := Work.Spaces.abs_mul_abs_le_half_add_sq
              (Work.Spaces.mixed (b - k) (a + 1) f z θ) (Work.Spaces.mixed b a f z θ)
            linarith [h2, sq_abs (Work.Spaces.mixed (b - k) (a + 1) f z θ),
              sq_abs (Work.Spaces.mixed b a f z θ)]
          have h3 : ρ z θ * |Work.Spaces.mixed (b - k) (a + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|
              ≤ ρ z θ * (((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
                  + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by
            calc ρ z θ * |Work.Spaces.mixed (b - k) (a + 1) f z θ|
                  * |Work.Spaces.mixed b a f z θ|
                = ρ z θ * (|Work.Spaces.mixed (b - k) (a + 1) f z θ|
                    * |Work.Spaces.mixed b a f z θ|) := by ring
              _ ≤ ρ z θ * (((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
                    + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
                  mul_le_mul_of_nonneg_left h4 hρ0
          linarith [h3, hVe, hVf]
  -- the a.e. domination of the summand by an integrable majorant
  have harith : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(-(1 / 2)) * ((b.choose k : ℝ)
        * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
            * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ))‖
      ≤ ((1 / 2) * ((b.choose k : ℝ) * Kk)) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 7 f z θ) := by
    filter_upwards [hArK, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz hzI
    have hc0 : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
    have hJ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ :=
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 7 f z θ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0), neg_neg, abs_of_nonneg hc0]
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul hz (hJbind z hzI) (abs_nonneg _) hKk0) hc0)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)) (le_of_eq (by ring))
  -- the majorant is integrable
  have hmaj : MeasureTheory.Integrable (fun z => ((1 / 2) * ((b.choose k : ℝ) * Kk))
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    h7.2.const_mul _
  -- a.e. strong measurability
  have hAaesm : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.aesm_Qang hsm k).congr
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkQangAe hsm h6 k hk6).symm
  have hJaesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hρ).mul
        (hsm.mixed (b - k) (a + 1)).continuousOn).mul (hsm.mixed b a).continuousOn
    have hX := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine hmaj.mono' ?_ harith
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z => (-(1 / 2)) * ((b.choose k : ℝ)
      * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
        * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ))))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (((hAaesm.mul hJaesm).const_mul ((b.choose k : ℝ))).const_mul (-(1 / 2)))
  exact h1

/-! ## The per-summand Cauchy–Schwarz bound -/

/-- **One Leibniz summand of the first conjunct.**  With the radial price `K` of `D_z^k(FK f)`
and the level-matched price `KYv` of the shifted slot `D_z^{b-k}D_θ^{a+1}f`, the summand is
bounded by the angular-then-radial Cauchy–Schwarz `fkPairCSae`:

  `|∫_z (D_z^k(FK f))·(∫_θ ρ·(D_z^{b-k}D_θ^{a+1}f)·(D_z^bD_θ^af))| ≤ K·√KYv·√(HkSq α 6 f)`. -/
theorem fkRow_summand_CS {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h6 : Work.Spaces.HkMem α 6 f)
    (h7 : Work.Spaces.HkMem α 7 f)
    {a b k : ℕ} (hab : a + b ≤ 6) (hkb : k ≤ b) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    {K KYv : ℝ} (hVf2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f)
    (hK0 : 0 ≤ K) (hlev : (a + 1) + (b - k) ≤ 6)
    (hArK : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z| ≤ K)
    (hKYv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2) ≤ KYv) :
    |∫ z in Work.Spaces.Iz, Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
        * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ)|
      ≤ K * Real.sqrt KYv * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
  have hα0 : 0 < α := hα.1
  have hVeI := slotIntegrable_row hα0 hsm h7 hρ (by omega : a ≤ a + 1)
    (by omega : (a + 1) + (b - k) ≤ 7)
  have hVfI := slotIntegrable_row hα0 hsm h7 hρ (le_refl a) (by omega : a + b ≤ 7)
  have hρae : ∀ z, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 ≤ ρ z θ :=
    fun z => MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z hθ)
  refine le_trans (fkPairCSae (ρ := ρ)
    (r := fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z)
    (V₁ := fun z θ => Work.Spaces.mixed (b - k) (a + 1) f z θ)
    (V₂ := fun z θ => Work.Spaces.mixed b a f z θ) (K := K) hK0 hArK hρae
    hVeI.1 hVfI.1 hVeI.2 hVfI.2) ?_
  calc K * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      ≤ K * Real.sqrt KYv * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKYv) hK0)
          (Real.sqrt_le_sqrt hVf2) (Real.sqrt_nonneg _)
          (mul_nonneg hK0 (Real.sqrt_nonneg _))

/-! ## The splitting of the pairing -/

/-- **The pairing splits into its Leibniz summands.** -/
theorem fkRow_pairing_eq_sum {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h6 : Work.Spaces.HkMem α 6 f)
    (h7 : Work.Spaces.HkMem α 7 f) {a b : ℕ} (hab : a + b ≤ 6) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {C : ℝ} (hCpos : 0 < C)
    (hpt : ∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter j (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ C * Work.Spaces.HkSq α (j + 1) f) :
    Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) f
      = ∑ k ∈ Finset.range (b + 1), ∫ z in Work.Spaces.Iz, (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)) := by
  rw [Work.FTS.TransportS.slotPairing]
  have hcongr : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
        * Work.Spaces.mixed b a
            (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∑ k ∈ Finset.range (b + 1), (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))) := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkTheta_ae_pos] with z hz
    exact fkRow_inner_eq hα hα1 hsm h7 hab hρ hz
  rw [MeasureTheory.integral_congr_ae hcongr]
  refine MeasureTheory.integral_finsetSum _ (fun k hk => ?_)
  have hkb : k ≤ b := by have h := Finset.mem_range.mp hk; omega
  exact fkRow_Wf_integrable hα hsm h6 h7 hρ hab hkb hCpos
    (by omega) (hpt k (by omega))

end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two helpers on the restricted radial measure `volume.restrict Iz` -/

/-- **A.e. dominated product.**  If `X, Y ≥ 0` a.e., `X * Y ≤ g` a.e. and `g` is integrable, then
`X * Y` is integrable and `∫ X*Y ≤ ∫ g`. -/
private theorem integrable_mul_of_le {X Y g : ℝ → ℝ}
    (hXnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ X z)
    (hYnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ Y z)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hXaesm : MeasureTheory.AEStronglyMeasurable X
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hYaesm : MeasureTheory.AEStronglyMeasurable Y
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), X z * Y z ≤ g z) :
    MeasureTheory.Integrable (fun z => X z * Y z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, X z * Y z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  have hmul : MeasureTheory.AEStronglyMeasurable (fun z => X z * Y z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hXaesm.mul hYaesm
  have hint : MeasureTheory.Integrable (fun z => X z * Y z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hg hmul ?_
    filter_upwards [hXnn, hYnn, hle] with z hx hy hb
    rw [Real.norm_of_nonneg (mul_nonneg hx hy)]
    exact hb
  refine ⟨hint, ?_⟩
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg hle
  filter_upwards [hXnn, hYnn] with z hx hy
  exact mul_nonneg hx hy

/-! ## A.e. strong measurability of the two factors -/

/-- The `z`-marginal `z ↦ ∫_θ HkIntegrand α k f z θ` of the level-`k` integrand of an
open-quadrant smooth datum is a.e. strongly measurable on `Iz`: the uncurried integrand is
continuous on the open quadrant (`SmoothOpen.continuousOn_HkIntegrand`). -/
private theorem aesm_HkIntegrand_zMarginal {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _
    (hF.continuousOn_HkIntegrand α k)).integral_prod_right'

/-- The squared `D_z^j`-iterate of the angular moment is a.e. strongly measurable on `Iz`: it is
the `θ`-marginal of the jointly continuous (on the open quadrant)
`(z,θ) ↦ D_z^j f z θ · K θ`. -/
private theorem aesm_FK_DzIter_sq {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Construction.FK (Work.Spaces.DzIter j f) z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter j f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter j).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  exact (hjoint.integral_prod_right').pow 2

/-! ## The target -/

theorem fkPsi6TermBound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      ∀ b : ℕ, b ≤ 6 →
        MeasureTheory.Integrable (fun z => (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
        (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
          ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkDzdIterSqLe
  obtain ⟨C₂, hC₂pos, hC₂⟩ := psi6LowSlice
  obtain ⟨C₃, hC₃pos, hC₃⟩ := fkMomentJetSq
  refine ⟨C₁ + C₂ * C₃ + 1, by positivity, ?_⟩
  intro α hαmem f M hD b hb
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαmem
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  -- `HkSq α 4 f ≤ M ^ 2`
  have hM4 : Work.Spaces.HkSq α 4 f ≤ M ^ 2 := by
    have hXn : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ M := hD.bdd
    have h0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 f) := Real.sqrt_nonneg _
    calc Work.Spaces.HkSq α 4 f = (Real.sqrt (Work.Spaces.HkSq α 4 f)) ^ 2 :=
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ h0 hXn 2
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- the matched level is honest
  have h6b : 6 - b ≤ 6 := by omega
  have hmem6b : Work.Spaces.HkMem α (6 - b) f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm (6 - b) h6b hD.h6
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hD.h6
  -- a.e. strong measurabilities and nonnegativities of the two factors
  have hYaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := aesm_HkIntegrand_zMarginal hsm
  have hXaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.DzIter b
        (fun z _ => Work.Construction.FK f z) z 0) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hae := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hD.h6 b hb
    refine (aesm_FK_DzIter_sq hsm b).congr ?_
    filter_upwards [hae] with z hz
    rw [hz 0]
  have hYnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
    Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ
  have hXnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg _
  rcases le_or_gt b 3 with hb3 | hb3
  · -- ## the low slots `b ≤ 3`
    have hXle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          ≤ C₁ * M ^ 2 := by
      filter_upwards [hC₁ hα0 hsm hD.h6 hD.h7 b hb] with z hz
      have hmono : Work.Spaces.HkSq α (b + 1) f ≤ Work.Spaces.HkSq α 4 f :=
        Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) hmem4
      calc (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          ≤ C₁ * Work.Spaces.HkSq α (b + 1) f := hz
        _ ≤ C₁ * Work.Spaces.HkSq α 4 f :=
            mul_le_mul_of_nonneg_left hmono (le_of_lt hC₁pos)
        _ ≤ C₁ * M ^ 2 := mul_le_mul_of_nonneg_left hM4 (le_of_lt hC₁pos)
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₁ * M ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
      filter_upwards [hXle, hYnn] with z hx hy
      exact mul_le_mul_of_nonneg_right hx hy
    have hmain := integrable_mul_of_le hXnn hYnn (hmem6b.2.const_mul (C₁ * M ^ 2))
      hXaesm hYaesm hle
    refine ⟨hmain.1, ?_⟩
    have hIntY : (∫ z in Work.Spaces.Iz,
          (C₁ * M ^ 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ))
        = (C₁ * M ^ 2) * Work.Spaces.HkSq α (6 - b) f := by
      rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    have hlast : C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f
        ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
      have hleC : C₁ ≤ C₁ + C₂ * C₃ + 1 := by nlinarith [hC₂pos, hC₃pos]
      have hnn : 0 ≤ M ^ 2 * Work.Spaces.HkSq α 6 f := mul_nonneg hM2 hSnn
      calc C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f
          = C₁ * (M ^ 2 * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ (C₁ + C₂ * C₃ + 1) * (M ^ 2 * Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right hleC hnn
        _ = (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
        ≤ ∫ z in Work.Spaces.Iz, (C₁ * M ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := hmain.2
      _ = (C₁ * M ^ 2) * Work.Spaces.HkSq α (6 - b) f := hIntY
      _ ≤ (C₁ * M ^ 2) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α h6b hD.h6) (by positivity)
      _ = C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
      _ ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := hlast
  · -- ## the high slots `4 ≤ b ≤ 6`: the matched angular level is `6 - b ≤ 2`
    have hb4 : 4 ≤ b := by omega
    have hm2 : 6 - b ≤ 2 := by omega
    -- the matched slice, uniformly in `z > 0`
    have hYle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2 := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)]
        with z hne hzI
      have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hzI) (Ne.symm hne)
      have h := hC₂ α hαmem f hsm hmem4 (6 - b) hm2 z hzpos
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ C₂ * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := h
        _ ≤ C₂ * M ^ 2 * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hM4 (le_of_lt hC₂pos)) hw2
        _ = (C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2 := by ring
    have hI3 := hC₃ α hαmem f hsm hD.h6 b hb
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      filter_upwards [hYle] with z hy
      rw [Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0]
      calc (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
              * ((C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2) :=
            mul_le_mul_of_nonneg_left hy (sq_nonneg _)
        _ = (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
    have hmain := integrable_mul_of_le hXnn hYnn (hI3.1.const_mul (C₂ * M ^ 2))
      hXaesm hYaesm hle
    refine ⟨hmain.1, ?_⟩
    have hlast : C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f
        ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
      have hleC : C₂ * C₃ ≤ C₁ + C₂ * C₃ + 1 := by nlinarith [hC₁pos]
      have hnn : 0 ≤ M ^ 2 * Work.Spaces.HkSq α 6 f := mul_nonneg hM2 hSnn
      calc C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f
          = C₂ * C₃ * (M ^ 2 * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ (C₁ + C₂ * C₃ + 1) * (M ^ 2 * Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right hleC hnn
        _ = (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
        ≤ ∫ z in Work.Spaces.Iz, (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := hmain.2
      _ = (C₂ * M ^ 2) * (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (C₂ * M ^ 2) * (C₃ * Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left hI3.2 (by positivity)
      _ = C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
      _ ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := hlast

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
