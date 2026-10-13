import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- **The flux (top self-pairing) Leibniz summand: `a₁ = b₁ = 0`, `a + b = 6`.**

The summand is `∫∫ ρ · A · mixed (b+1) a f · mixed b a f` (the `(0,0)` Leibniz term of
`D_z^bD_θ^a (A·D_z f)` at the top slot, where `mixed (b+1) a f = D_z(mixed b a f)`).

Route: `Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay` (proved) applied with `h := A`, `g := f`,
`q := γ` if `1 ≤ a` resp. `q := η` if `a = 0`, and `M := max K0 (C/√(γ-1)·K4)` (bounds for `|A|` and `|D_zA|`
from `CoefData.val` and `TransportS.sup_dz_le_hk` with `Xn α A = HkNorm α 4 A`) gives
`|∫_z∫_θ canonW q · A · D_z(mixed b a f) · mixed b a f| ≤ 2·M·HkSq α 6 f`.  Choose `q` to be the exponent of
the leaf weight `ρ` itself when that is convenient (`IsLeafW` makes `ρ` one of `canonW η`, `canonW 0`,
`canonW (gam α)`), so that the left-hand side *is* the `fluxSix_noDecay` integral; otherwise use
`ρ ≤ canonW q` on the open quadrant and absorb `ρ/canonW q` (a `θ`-only factor bounded by `1`) into `h`.
Convert the iterated integral into the `PM`-integral by Fubini (`MeasureTheory.integral_prod`; integrability
comes from the pointwise domination by `canonW q·|A|·|D_z(mixed b a f)|·|mixed b a f|` and `HkMem α 6 f`,
`HkMem α 7 f`).  Since `C/√(γ-1) = C√10·α^{-1/2}`, the conclusion is `C α^{-1/2}(K0+K4)·HkSq α 6 f`. -/
theorem rowSumFlux : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b = 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cfl, hCflpos, hflux⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
  obtain ⟨Cd, hCdpos, hsd⟩ := Work.FTS.TransportS.sup_dz_le_hk
  refine ⟨Cfl * max 1 (Cd * Real.sqrt 10), by positivity, ?_⟩
  intro α hαIoc A f K0 K4 K6 K1 M a b ρ hcoef hctmem hctle hdat hab hleaf
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hCd0 : 0 ≤ Cd := le_of_lt hCdpos
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) (by norm_num) (by positivity)
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  -- ## the pointwise price of the coefficient slot `D_z A`
  have hph : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα0 _
  have hple : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
  have hpow1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    exact (one_le_inv₀ hph).mpr hple
  have hsqrt_gam : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα0.le]
  have hpow_alpha : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα0.le (1 / 2 : ℝ)]
  have hdiv : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹
      = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    rw [hsqrt_gam, inv_div, div_eq_mul_inv, hpow_alpha]
  have hDzA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz A z θ| ≤ Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by
    intro z θ hz hθ0 hθ2
    have h1 := hsd α A hα0 hα1 hcoef.sm hcoef.h4 1 (by norm_num) z θ hz hθ0 hθ2
    have h2 : |Work.Spaces.Dz A z θ| ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α A := by
      simpa only [Work.Spaces.DzIter, Work.Spaces.Dz] using h1
    have hmain : Cd / Real.sqrt (Work.Spaces.gam α - 1)
        = Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, hdiv]
      ring
    calc |Work.Spaces.Dz A z θ|
        ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := h2
      _ ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1) * K4 :=
          mul_le_mul_of_nonneg_left hcoef.n4 (div_nonneg hCd0 (Real.sqrt_nonneg _))
      _ = Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by rw [hmain]
  set MA : ℝ := max K0 (Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4) with hMAdef
  have hMA0 : 0 ≤ MA := le_trans hK0 (le_max_left _ _)
  have hC0_1 : (1 : ℝ) ≤ max 1 (Cd * Real.sqrt 10) := le_max_left _ _
  have hpow_nn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hα0 _)
  have hA_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA :=
    fun z θ hz hθ0 hθ2 => le_trans (hcoef.val z θ hz hθ0 hθ2) (le_max_left _ _)
  have hDzA_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz A z θ| ≤ MA :=
    fun z θ hz hθ0 hθ2 => le_trans (hDzA z θ hz hθ0 hθ2) (le_max_right _ _)
  have hMA_le : MA ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
    rw [hMAdef]
    refine max_le ?_ ?_
    · have h1 : K0 ≤ α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
        le_trans (le_add_of_nonneg_right hK4) (le_mul_of_one_le_left (by linarith) hpow1)
      calc K0 ≤ α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := h1
        _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
            have h2 : α ^ (-(1 / 2 : ℝ))
                ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) := by
              calc α ^ (-(1 / 2 : ℝ)) = 1 * α ^ (-(1 / 2 : ℝ)) := by ring
                _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) :=
                    mul_le_mul_of_nonneg_right hC0_1 hpow_nn
            exact mul_le_mul_of_nonneg_right h2 (by linarith)
    · have h2 : Cd * Real.sqrt 10 ≤ max 1 (Cd * Real.sqrt 10) := le_max_right _ _
      have hnn : 0 ≤ max 1 (Cd * Real.sqrt 10) := le_trans zero_le_one hC0_1
      have h3 : Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
          ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * K4 := by
        refine mul_le_mul_of_nonneg_right ?_ hK4
        exact mul_le_mul_of_nonneg_right h2 hpow_nn
      calc Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
          ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * K4 := h3
        _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hnn hpow_nn)
  -- ## the canonical-weight form of the slot, for an admissible exponent `q`
  have key : ∀ (q : ℝ), 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      MeasureTheory.Integrable
          (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
            * Work.Spaces.HkSq α 6 f := by
    intro q hq0 hqγ hqη
    -- the iterated-integral flux bound
    have hflux_it : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ Cfl * MA * Work.Spaces.HkSq α 6 f :=
      hflux α A f a b q MA hα0 hα1 hq0 hqγ hqη (by omega) hcoef.sm hdat.sm hdat.h6 hdat.h7
        hA_le hDzA_le
    -- the two pointwise slot dominations
    have hdom6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ hθ2
      rcases Nat.eq_zero_or_pos a with ha | ha
      · rw [ha, Work.Spaces.mixed_zero_right]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 6 (hqη ha) hθ hθ2 (by omega)
      · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 6 hqγ hθ hθ2 ha (by omega)
    have hdom7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
      intro z θ _ hθ hθ2
      rcases Nat.eq_zero_or_pos a with ha | ha
      · rw [ha, Work.Spaces.mixed_zero_right]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 7 (hqη ha) hθ hθ2 (by omega)
      · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 7 hqγ hθ hθ2 ha (by omega)
    -- the pointwise bound on the integrand
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
          ≤ (MA / 2) * (Work.Spaces.HkIntegrand α 7 f z θ
              + Work.Spaces.HkIntegrand α 6 f z θ) := by
      intro z θ hz hθ0 hθ2
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
      have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
        Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
      have hX := hdom7 z θ hz hθ0 hθ2
      have hY := hdom6 z θ hz hθ0 hθ2
      have hrew : Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ
          = A z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ) := by ring
      rw [hrew]
      refine le_trans (Work.FTS.StrongPersist.N6Trans.SixAux.abs_mul_canonW_mul_le
        (q := q) (M := MA) (X := Work.Spaces.mixed (b + 1) a f z θ)
        (Y := Work.Spaces.mixed b a f z θ) (hh := A z θ) hcw hMA0
        (hA_le z θ hz hθ0 hθ2)) ?_
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith : 0 ≤ MA / 2)
    -- continuity on the open quadrant
    have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.FTS.TransportS.SlotT2.canonW q p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.TransportS.SlotT2.continuousOn_canonW q
      have h2 : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcoef.sm.continuousOn
      have h3 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.mixed (b + 1) a f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hdat.sm.mixed (b + 1) a).continuousOn
      have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hdat.sm.mixed b a).continuousOn
      exact (((h1.mul h2).mul h3).mul h4).congr (fun p _ => rfl)
    -- integrability of the integrand
    have hdomint : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (MA / 2) * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
          + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (((Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hdat.sm hdat.h7).1.add
        (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hdat.sm hdat.h6).1).const_mul
          (MA / 2))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcontF
    have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ‖Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2‖
          ≤ (MA / 2) * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
              + Work.Spaces.HkIntegrand α 6 f p.1 p.2) :=
      ae_of_forall_Qd
        (fun z θ hz hθ0 hθ2 => by rw [Real.norm_eq_abs]; exact hpt z θ hz hθ0 hθ2)
    have hFint : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hdomint.mono' haesm hae
    -- Fubini
    have hFub : (∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ :=
      (MeasureTheory.integral_integral
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun z θ => Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
        hFint).symm
    have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      rfl
    -- the price
    have hprice : Cfl * MA * Work.Spaces.HkSq α 6 f
        ≤ Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
            * Work.Spaces.HkSq α 6 f := by
      calc Cfl * MA * Work.Spaces.HkSq α 6 f
          ≤ Cfl * (max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * Work.Spaces.HkSq α 6 f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMA_le hCflpos.le) hS0
        _ = Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
              * Work.Spaces.HkSq α 6 f := by ring
    exact ⟨hFint, by rw [hFub, hcongr]; exact le_trans hflux_it hprice⟩
  -- ## the three leaf weights
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · subst hρ
    exact key Work.Spaces.eta Work.Spaces.eta_nonneg
      (Work.FTS.TransportS.T2Sup.eta_le_gam hα0) (fun _ => le_rfl)
  · subst hρ
    have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafOne p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
        = (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW 0 p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2) := by
      funext p
      simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
        Real.rpow_zero, mul_one]
    rw [hfun]
    exact key 0 le_rfl (le_of_lt (Work.Spaces.gam_pos hα0))
      (fun _ => Work.Spaces.eta_nonneg)
  · subst hρ
    exact key (Work.Spaces.gam α) (le_of_lt (Work.Spaces.gam_pos hα0)) le_rfl
      (fun ha0 => absurd ha0 (Nat.one_le_iff_ne_zero.mp ha1))

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
