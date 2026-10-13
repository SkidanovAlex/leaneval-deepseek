/- # `H6Row6/RowFKfCore2` — integrability, the splitting of the pairing and the per-summand Cauchy–Schwarz -/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux2
import Submission.Work.FTS.StrongPersist.H6Row6.FkRowPrices
import Submission.Work.FTS.StrongPersist.H6Row6.fkSlotShift

import Submission.Work.FTS.StrongPersist.H6Row6.fkPairCSae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfCore

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
