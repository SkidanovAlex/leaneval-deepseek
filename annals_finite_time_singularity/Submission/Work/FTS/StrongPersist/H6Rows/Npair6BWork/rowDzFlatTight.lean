import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumFlux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1ZeroSmall
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumB1Five
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1Small
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1Big

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

theorem rowDzFlatTight : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A →
      Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ C * α ^ (-(4 : ℝ))
            * ((1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C1, hC1, hA1S⟩ := rowSumA1Small
  obtain ⟨C2, hC2, hA1B⟩ := rowSumA1Big
  obtain ⟨C3, hC3, hSg⟩ := rowSumGamSin
  obtain ⟨C4, hC4, hZ0⟩ := rowSumZ0
  obtain ⟨C5, hC5, hFx⟩ := rowSumFlux
  obtain ⟨C6, hC6, hA0S⟩ := rowSumA1ZeroSmall
  obtain ⟨C7, hC7, hB15⟩ := rowSumB1Five
  refine ⟨64 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + 1)) + 1,
    by linarith [hC1, hC2, hC3, hC4, hC5, hC6, hC7], ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b ρ hcoef hthmem hth hdat hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK00 : 0 ≤ K0 := by
    have h := hcoef.val 1 1 one_pos one_pos (by linarith [Real.pi_gt_three])
    exact le_trans (abs_nonneg _) h
  have hK40 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK60 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hK10 : 0 ≤ K1 := le_trans (coefTh_nonneg 1 A) hth
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX60 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hα4pos : 0 < α ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hα0 _
  have hα12 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαh : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hone4 : (1 : ℝ) ≤ α ^ (-(4 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ 0 by norm_num)
    simpa using h
  set Csm : ℝ := 2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + 1) with hCsmdef
  set Ctot : ℝ := 64 * Csm + 1 with hCtotdef
  set T : ℝ := (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hTdef
  have hCsmpos : 0 < Csm := by rw [hCsmdef]; linarith [hC1, hC2, hC3, hC4, hC5, hC6, hC7]
  have h2C1 : 2 * C1 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C2 : 2 * C2 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C3 : 2 * C3 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C4 : 2 * C4 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C5 : 2 * C5 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C6 : 2 * C6 ≤ Csm := by rw [hCsmdef]; linarith
  have h2C7 : 2 * C7 ≤ Csm := by rw [hCsmdef]; linarith
  have hC1le : C1 ≤ Csm := by rw [hCsmdef]; linarith
  have hC2le : C2 ≤ Csm := by rw [hCsmdef]; linarith
  have hC3le : C3 ≤ Csm := by rw [hCsmdef]; linarith
  have hB0 : (0 : ℝ) ≤ 1 + K0 + K4 + K1 := by linarith
  have hK60' : (0 : ℝ) ≤ K4 + K6 := by linarith
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact add_nonneg (mul_nonneg (mul_nonneg hB0 (by linarith)) (by linarith))
      (mul_nonneg (mul_nonneg hK60' (by linarith)) (by linarith))
  have hSq_le : ∀ c : ℝ, 0 ≤ c → c ≤ 1 + K0 + K4 + K1 →
      c * Work.Spaces.HkSq α 6 f ≤ T := by
    intro c hc0 hcle
    have h2 : Work.Spaces.HkSq α 6 f ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
      nlinarith [hM0, hSq0]
    have h1 : c * Work.Spaces.HkSq α 6 f
        ≤ (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
      calc c * Work.Spaces.HkSq α 6 f
          ≤ c * ((1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left h2 hc0
        _ ≤ (1 + K0 + K4 + K1) * ((1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_right hcle (by nlinarith [hM0, hSq0])
        _ = (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring
    have h3 : (0 : ℝ) ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
      mul_nonneg (mul_nonneg hK60' (by linarith)) (by linarith)
    rw [hTdef]
    linarith
  have hMK6_le : ∀ c : ℝ, 0 ≤ c → c ≤ K4 + K6 →
      M * c * Work.Spaces.HkNorm α 6 f ≤ T := by
    intro c hc0 hcle
    have hMle : M * Work.Spaces.HkNorm α 6 f
        ≤ (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by nlinarith [hM0, hX60]
    have h1 : M * c * Work.Spaces.HkNorm α 6 f
        ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
      calc M * c * Work.Spaces.HkNorm α 6 f = c * (M * Work.Spaces.HkNorm α 6 f) := by ring
        _ ≤ (K4 + K6) * (M * Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_right hcle (mul_nonneg hM0 hX60)
        _ ≤ (K4 + K6) * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
            mul_le_mul_of_nonneg_left hMle hK60'
        _ = (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by ring
    have h3 : (0 : ℝ) ≤ (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (mul_nonneg hB0 (by linarith)) (by linarith)
    rw [hTdef]
    linarith
  -- absorption of a summand bound into the final bracket
  have absorb_half : ∀ c Y : ℝ, 0 ≤ c → 2 * c ≤ Csm → 0 ≤ Y → Y ≤ 2 * T →
      (c * α ^ (-(1 / 2 : ℝ))) * Y ≤ (Csm * α ^ (-(4 : ℝ))) * T := by
    intro c Y hc h2c hY hYT
    have hc2 : (0 : ℝ) ≤ 2 * c := by linarith
    have h1 : (c * α ^ (-(1 / 2 : ℝ))) * Y ≤ (c * α ^ (-(1 / 2 : ℝ))) * (2 * T) :=
      mul_le_mul_of_nonneg_left hYT (mul_nonneg hc hα12)
    have h2 : (c * α ^ (-(1 / 2 : ℝ))) * (2 * T) = (2 * c * α ^ (-(1 / 2 : ℝ))) * T := by ring
    have h3 : (2 * c * α ^ (-(1 / 2 : ℝ))) * T ≤ (2 * c * α ^ (-(4 : ℝ))) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαh hc2) hT0
    have h4 : (2 * c * α ^ (-(4 : ℝ))) * T ≤ (Csm * α ^ (-(4 : ℝ))) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2c hα4pos.le) hT0
    exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 h4))
  have absorb_zero : ∀ c Y : ℝ, 0 ≤ c → c ≤ Csm → 0 ≤ Y → Y ≤ T →
      c * Y ≤ (Csm * α ^ (-(4 : ℝ))) * T := by
    intro c Y hc hcle hY hYT
    have hYT' : Y ≤ α ^ (-(4 : ℝ)) * T := by
      calc Y ≤ T := hYT
        _ = 1 * T := by ring
        _ ≤ α ^ (-(4 : ℝ)) * T := mul_le_mul_of_nonneg_right hone4 hT0
    calc c * Y ≤ Csm * Y := mul_le_mul_of_nonneg_right hcle hY
      _ ≤ Csm * (α ^ (-(4 : ℝ)) * T) := mul_le_mul_of_nonneg_left hYT' hCsmpos.le
      _ = Csm * α ^ (-(4 : ℝ)) * T := by ring
  have absorb_four : ∀ c : ℝ, c ≤ Csm →
      c * α ^ (-(4 : ℝ)) * T ≤ (Csm * α ^ (-(4 : ℝ))) * T :=
    fun c hcle =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcle hα4pos.le) hT0
  -- the per-summand bound
  have hsummand : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) PM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂PM| ≤ Csm * α ^ (-(4 : ℝ)) * T := by
    intro a₁ b₁ ha₁ hb₁
    by_cases hflux : a₁ = 0 ∧ b₁ = 0 ∧ a + b = 6
    · -- the flux summand (both `D_z`-slots of the datum, coefficient slot `A` itself)
      obtain ⟨hf1, hf2, hf3⟩ := hflux
      subst hf1
      subst hf2
      simp only [Nat.sub_zero, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
      obtain ⟨hint, hbd⟩ :=
        hFx α hα A f K0 K4 K6 K1 M a b ρ hcoef hthmem hth hdat hf3 hleaf
      refine ⟨hint, ?_⟩
      refine le_trans hbd ?_
      refine le_trans (le_of_eq (by ring :
          C5 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * Work.Spaces.HkSq α 6 f
            = (C5 * α ^ (-(1 / 2 : ℝ))) * ((K0 + K4) * Work.Spaces.HkSq α 6 f))) ?_
      refine absorb_half C5 ((K0 + K4) * Work.Spaces.HkSq α 6 f) hC5.le h2C5
        (mul_nonneg (by linarith) hSq0) ?_
      linarith [hSq_le (K0 + K4) (by linarith) (by linarith), hT0]
    · by_cases ha₁0 : a₁ = 0
      · subst ha₁0
        simp only [Nat.sub_zero]
        by_cases ha0 : a = 0
        · -- all three factors are pure radial slots
          subst ha0
          simp only [Work.Spaces.mixed_zero_right]
          obtain ⟨hint, hbd⟩ :=
            hZ0 α hα A f K0 K4 K6 K1 M b b₁ ρ hcoef hthmem hth hdat (by omega) hleaf hb₁
              (by rintro ⟨h1, h2⟩; exact hflux ⟨rfl, h1, by omega⟩)
          refine ⟨hint, ?_⟩
          refine le_trans hbd ?_
          refine le_trans (le_of_eq (by ring :
              C4 * α ^ (-(1 / 2 : ℝ))
                  * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f)
                = (C4 * α ^ (-(1 / 2 : ℝ)))
                  * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                    + M * K6 * Work.Spaces.HkNorm α 6 f))) ?_
          refine absorb_half C4 _ hC4.le h2C4 (add_nonneg (mul_nonneg (by linarith) hSq0)
            (mul_nonneg (mul_nonneg hM0 hK60) hX60)) ?_
          linarith [hSq_le (K0 + K4) (by linarith) (by linarith),
            hMK6_le K6 hK60 (by linarith), hT0]
        · -- `1 ≤ a`: the pure coefficient slot
          have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
          by_cases hb4 : b₁ ≤ 4
          · obtain ⟨hint, hbd⟩ :=
              hA0S α hα A f K0 K4 K6 K1 M a b b₁ ρ hcoef hthmem hth hdat hab hleaf ha1 hb4
                hb₁ (by rintro ⟨h1, h2⟩; exact hflux ⟨rfl, h1, h2⟩)
            refine ⟨hint, ?_⟩
            refine le_trans hbd ?_
            refine le_trans (le_of_eq (by ring :
                C6 * α ^ (-(1 / 2 : ℝ))
                    * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f)
                  = (C6 * α ^ (-(1 / 2 : ℝ)))
                    * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                      + M * K6 * Work.Spaces.HkNorm α 6 f))) ?_
            refine absorb_half C6 _ hC6.le h2C6 (add_nonneg (mul_nonneg (by linarith) hSq0)
              (mul_nonneg (mul_nonneg hM0 hK60) hX60)) ?_
            linarith [hSq_le (K0 + K4) (by linarith) (by linarith),
              hMK6_le K6 hK60 (by linarith), hT0]
          · -- `b₁ = 5`, hence `a = 1`, `b = 5`
            have hb15 : b₁ = 5 := by omega
            have hb5 : b = 5 := by omega
            have ha1' : a = 1 := by omega
            subst hb15
            subst hb5
            subst ha1'
            simp only [Nat.sub_zero, Nat.sub_self, Nat.zero_add, Work.Spaces.mixed_zero_right]
            obtain ⟨hint, hbd⟩ := hB15 α hα A f K0 K4 K6 K1 M ρ hcoef hthmem hth hdat hleaf
            refine ⟨hint, ?_⟩
            refine le_trans hbd ?_
            refine le_trans (le_of_eq (by ring :
                C7 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f
                  = (C7 * α ^ (-(1 / 2 : ℝ))) * (M * K6 * Work.Spaces.HkNorm α 6 f))) ?_
            refine absorb_half C7 (M * K6 * Work.Spaces.HkNorm α 6 f) hC7.le h2C7
              (mul_nonneg (mul_nonneg hM0 hK60) hX60) ?_
            linarith [hMK6_le K6 hK60 (by linarith), hT0]
      · -- `1 ≤ a₁`
        have ha1 : 1 ≤ a₁ := Nat.one_le_iff_ne_zero.mpr ha₁0
        by_cases hgam : a₁ = a ∧ ρ = Work.FTS.TransportS.leafGam α ∧ a₁ + b₁ ≤ 2
        · -- the σ-gain case
          obtain ⟨haeq, hrho, hp2⟩ := hgam
          rw [haeq] at ha1 hp2 ⊢
          subst hrho
          simp only [Nat.sub_self, Work.Spaces.mixed_zero_right]
          rw [show b + 1 - b₁ = b - b₁ + 1 from by omega]
          obtain ⟨hint, hbd⟩ :=
            hSg α hα A f K0 K4 K6 K1 M a b b₁ hcoef hthmem hth hdat hab ha1 hb₁ hp2
          refine ⟨hint, ?_⟩
          refine le_trans hbd ?_
          refine le_trans (le_of_eq (by ring :
              C3 * K1 * Work.Spaces.HkSq α 6 f
                = C3 * (K1 * Work.Spaces.HkSq α 6 f))) ?_
          refine absorb_zero C3 (K1 * Work.Spaces.HkSq α 6 f) hC3.le hC3le
            (mul_nonneg hK10 hSq0) ?_
          exact hSq_le K1 hK10 (by linarith)
        · by_cases hp2 : a₁ + b₁ ≤ 2
          · obtain ⟨hint, hbd⟩ :=
              hA1S α hα A f K0 K4 K6 K1 M a b a₁ b₁ ρ hcoef hthmem hth hdat hab hleaf ha1
                ha₁ hb₁ hp2 (by rintro ⟨h1, h2⟩; exact hgam ⟨h1, h2, hp2⟩)
            refine ⟨hint, ?_⟩
            refine le_trans hbd ?_
            exact absorb_four C1 hC1le
          · have hp3 : 3 ≤ a₁ + b₁ := by omega
            obtain ⟨hint, hbd⟩ :=
              hA1B α hα A f K0 K4 K6 K1 M a b a₁ b₁ ρ hcoef hthmem hth hdat hab hleaf ha1
                ha₁ hb₁ hp3
            refine ⟨hint, ?_⟩
            refine le_trans hbd ?_
            exact absorb_four C2 hC2le
  -- the Leibniz expansion of the target slot, a.e.
  have hpt : ∀ᵐ p ∂PM, (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2))
      = ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2 := by
    filter_upwards [ae_PM_Q0] with p hp
    have hL := Work.FTS.TransportS.mixed_mul_Dz_open b a A f hcoef.sm hdat.sm p.1 p.2
      hp.1 hp.2.1 hp.2.2
    rw [hL]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ hb₁ => ?_
    rw [show b - b₁ + 1 = b + 1 - b₁ from by
      have hb : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
      omega]
    ring
  have hint : ∀ a₁ : ℕ, a₁ ≤ a → ∀ b₁ : ℕ, b₁ ≤ b → MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM :=
    fun a₁ ha₁ b₁ hb₁ => (hsummand a₁ b₁ ha₁ hb₁).1
  have hae : (fun p : ℝ × ℝ => ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2))
      =ᵐ[PM] (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) := by
    filter_upwards [hpt] with p hp
    exact hp
  have hintU : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2)) PM := by
    refine MeasureTheory.integrable_finsetSum (Finset.range (a + 1)) ?_
    intro a₁ ha₁
    refine MeasureTheory.integrable_finsetSum (Finset.range (b + 1)) ?_
    intro b₁ hb₁
    exact (hint a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))).const_mul _
  have hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) PM := hintU.congr hae
  -- the integrated Leibniz expansion
  have hSint1 : ∫ p, (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2)) ∂PM
      = ∑ a₁ ∈ Finset.range (a + 1),
          ∫ p, (∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2)) ∂PM :=
    MeasureTheory.integral_finsetSum (Finset.range (a + 1))
      (f := fun a₁ (p : ℝ × ℝ) => ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2))
      (fun a₁ ha₁ => MeasureTheory.integrable_finsetSum (Finset.range (b + 1))
        (f := fun b₁ (p : ℝ × ℝ) => ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2))
        (fun b₁ hb₁ => (hint a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))).const_mul _))
  have hSint2 : (∑ a₁ ∈ Finset.range (a + 1),
          ∫ p, (∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2)) ∂PM)
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂PM) :=
    Finset.sum_congr rfl fun a₁ ha₁ =>
      (MeasureTheory.integral_finsetSum (Finset.range (b + 1))
        (f := fun b₁ (p : ℝ × ℝ) => ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2))
        (fun b₁ hb₁ => (hint a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))).const_mul _)).trans
      (Finset.sum_congr rfl fun b₁ hb₁ => MeasureTheory.integral_const_mul _ _)
  have hSint : ∫ p, (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2)) ∂PM
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂PM) := hSint1.trans hSint2
  have hExp : ∫ p, ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2 ∂PM
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂PM) :=
    (MeasureTheory.integral_congr_ae hae).symm.trans hSint
  have hpp := slotPairing_eq_prod (ρv := ρ) (a := a) (b := b)
    (u := fun z θ => A z θ * Work.Spaces.Dz f z θ) (v := f) hXY
  rw [hpp, hExp]
  have hbnd : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b →
      |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
        * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂PM)|
        ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * (Csm * α ^ (-(4 : ℝ)) * T) := by
    intro a₁ b₁ ha₁ hb₁
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hsummand a₁ b₁ ha₁ hb₁).2
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hbinom : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
    rw [← Finset.sum_mul_sum]
    congr 1
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hmain : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂PM)|
      ≤ 64 * (Csm * α ^ (-(4 : ℝ)) * T) := by
    have h1 : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂PM)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂PM)| :=
          Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂PM)|)
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * (Csm * α ^ (-(4 : ℝ)) * T) := by
      refine Finset.sum_le_sum fun a₁ ha₁ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b₁ hb₁ => hbnd a₁ b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
    have h3 : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * (Csm * α ^ (-(4 : ℝ)) * T))
        = (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) * (Csm * α ^ (-(4 : ℝ)) * T) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_mul]
    refine (h1.trans h2).trans ?_
    rw [h3, hbinom]
    exact mul_le_mul_of_nonneg_right hpow (mul_nonneg (mul_nonneg hCsmpos.le hα4pos.le) hT0)
  have h64 : 64 * (Csm * α ^ (-(4 : ℝ)) * T) ≤ Ctot * α ^ (-(4 : ℝ)) * T := by
    rw [hCtotdef]
    have hsplit : (64 * Csm + 1) * α ^ (-(4 : ℝ)) * T
        = 64 * (Csm * α ^ (-(4 : ℝ)) * T) + (α ^ (-(4 : ℝ)) * T) := by ring
    rw [hsplit]
    linarith [mul_nonneg hα4pos.le hT0]
  exact hmain.trans h64

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
