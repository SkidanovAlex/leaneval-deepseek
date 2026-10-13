/-
# `Coer1T` — the arithmetic ledger of the level-1 coercivity of `𝓛_Γ^T`

See `NOTES_coer1_LGammaT.md` in this directory.  This file does *not* re-prove any of the
four slot estimates (they are the paper's four §6 propositions, ported to the interior
class `CoerAdm` by the sibling files of this directory); it contains the weighted-energy
comparisons used by the ledger and the pure arithmetic that turns the four slot estimates
into the target.

The four slot estimates, with `G = 𝓛_Γ^T f`:

  `P₁ = ⟨D_z G, D_z f⟩_{w²sin^{-η}} ≥ (1/5)EDz − 100·EfEta − 100·EDth − 10¹²·Ef`
  `P₂ = ⟨G, f⟩_{w²sin^{-η}} ≥ (1/5)EfEta − 10⁵(EL12z + EDthW + Ef)`
  `P₃ = ⟨G, f⟩_{w²} ≥ (1/5)Ef − 1000·EDthW`
  `P₄ = ⟨D_θG, D_θ f⟩_{w²sin^{-γ}} ≥ (17/40 − 1/100)EDth − 10⁻⁶·Ef`

multiplied by the coefficients `10, 10¹⁰, 10¹⁷, 10²¹` of `H1IP` and combined with
`EL12z ≤ 16Ef`, `EDthW ≤ EDth`, the resulting left-hand side dominates
`EDz + EfEta + EDth = |f|²_{ℋ¹}` with margin
`(2−1)EDz + (2·10⁹−10³)EfEta + 1.99·10¹⁵·Ef + 3.15·10²⁰·EDth`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The comparison `EnOne u ≤ En η u` -/

/-- On the open angular interval the plain radial weight `w²` is dominated by the
`η`-weight `w²·sin(2θ)^{-η}`; integrating gives `EnOne u ≤ En η u` as soon as both
integrals are honest. -/
theorem EnOne_le_En_eta {u : Fn}
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        u z θ ^ 2 * Work.Spaces.w z ^ 2 * Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Coer1.EnOne u ≤ Coer1.En Work.Spaces.eta u := by
  have h2' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Coer1.iz_prod_restrict]; exact h2
  have e1 : Coer1.EnOne u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := Coer1.EnOne_eq_prod h1
  have e2 : Coer1.En Work.Spaces.eta u = ∫ p : ℝ × ℝ,
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2) h2').symm
  rw [e1, e2]
  refine MeasureTheory.integral_mono_ae ?_ h2' ?_
  · rw [Coer1.iz_prod_restrict]; exact h1
  · filter_upwards [Coer1.ae_prod_snd_mem_Ioo] with p hp
    have hle : Work.Spaces.w p.1 ^ 2 ≤ Coer1.Rho Work.Spaces.eta p.1 p.2 :=
      Coer1.w2_le_Rho_eta p.1 p.2 hp
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg (u p.1 p.2))
    simpa only [Coer1.Rho, Coer1.sig, mul_assoc] using h

/-! ## The three comparisons needed by the ledger -/

/-- `EDthW f ≤ EDth α f` for `f` in the interior class `RegQ α 2`. -/
theorem EDthW_le_EDth_Q (α : ℝ) (hα : 0 < α) {f : Fn}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f := by
  have h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_MixedOne α hα hsq hm 1 0 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using h
  have h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ ^ 2 * Work.Spaces.w z ^ 2
        * Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_MixedEta α hα hsq hm 1 0 (by norm_num) (by norm_num)
    have h1 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed 0 1 f z θ ^ 2
          * Work.Spaces.w z ^ 2 * Coer1.sig Work.Spaces.eta θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := Coer1.to_h1 (β := Work.Spaces.eta) h
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, mul_assoc] using h1
  have h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ ^ 2 * Work.Spaces.w z ^ 2
        * Coer1.sig (Work.Spaces.gam α) θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_MixedGam α hα hsq hm 1 0 (by norm_num) (by norm_num)
    have h1 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed 0 1 f z θ ^ 2
          * Work.Spaces.w z ^ 2 * Coer1.sig (Work.Spaces.gam α) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := Coer1.to_h1 (β := Work.Spaces.gam α) h
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, mul_assoc] using h1
  have hA : Work.Coercivity.EDthW f = Coer1.EnOne (Work.Spaces.Dth f) := Coer1.wip_one_self _
  have hB : Work.Coercivity.EDth α f = Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    Coer1.EDth_eq_En α f
  rw [hA, hB]
  exact le_trans (EnOne_le_En_eta (u := Work.Spaces.Dth f) h1 h2)
    (Coer1.En_eta_le_En_gam α hα (Work.Spaces.Dth f) h2 h3)

/-- `Ef f ≤ EfEta f` for `f` in the interior class `RegQ α 2`. -/
theorem Ef_le_EfEta_Q (α : ℝ) (hα : 0 < α) {f : Fn}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.Coercivity.Ef f ≤ Work.Coercivity.EfEta f := by
  have h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_DzOne α hsq hm 0 (by norm_num)
    simpa only [Work.Spaces.DzIter_zero] using h
  have h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Work.Spaces.w z ^ 2
        * Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_DzEta α hsq hm 0 (by norm_num)
    have h1 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.DzIter 0 f z θ ^ 2
          * Work.Spaces.w z ^ 2 * Coer1.sig Work.Spaces.eta θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := Coer1.to_h1 (β := Work.Spaces.eta) h
    simpa only [Work.Spaces.DzIter_zero, mul_assoc] using h1
  have hA : Work.Coercivity.Ef f = Coer1.EnOne f := Coer1.Ef_eq_EnOne f
  have hB : Work.Coercivity.EfEta f = Coer1.En Work.Spaces.eta f := Coer1.EfEta_eq_En f
  rw [hA, hB]
  exact EnOne_le_En_eta h1 h2

/-- `EL12z f ≤ 16·Ef f` for `f` in the interior class (`HardyHyp` supplies the first Hardy
inequality; the `ℋ²`-membership makes `(f w)²` integrable). -/
theorem EL12z_le_Q (α : ℝ) (hα : 0 < α) {f : Fn}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hm : Work.Spaces.HkMem α 2 f)
    (hHH : Work.Coercivity.HardyHyp f) :
    Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f := by
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Coer1.sq_DzOne α hsq hm 0 (by norm_num)
    simpa only [Work.Spaces.DzIter_zero, mul_pow] using h
  exact Work.Coercivity.EL12z_le f hHH hfw

/-! ## The arithmetic ledger -/

/-- **The ledger**: the four slot estimates, rescaled by the coefficients of `H1IP`, dominate
the `ℋ¹`-energy. -/
theorem ledger (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : Fn}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hm1 : Work.Spaces.HkMem α 1 f)
    (hED : Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f)
    (hEL : Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f)
    (hP : (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f))
    (hQ : (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f)
    (hR : (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f)
    (hS : (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f
        - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hHk : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EDz f + Work.Coercivity.EfEta f + Work.Coercivity.EDth α f :=
    Coer1.HkSq_one_eq α hsq hm1
  rw [hHk, Work.Coercivity.H1IP]
  -- the four slot bounds, rescaled by the coefficients of `H1IP`
  have h1 : (2 : ℝ) * Work.Coercivity.EDz f - 1000 * Work.Coercivity.EfEta f
        - 1000 * Work.Coercivity.EDth α f - 10 ^ 13 * Work.Coercivity.Ef f
      ≤ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
    have := mul_le_mul_of_nonneg_left hP (show (0 : ℝ) ≤ 10 by norm_num)
    linarith [this]
  have h2 : 2 * 10 ^ 9 * Work.Coercivity.EfEta f
        - 17 * 10 ^ 15 * Work.Coercivity.Ef f - 10 ^ 15 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    have hEL' : (10 : ℝ) ^ 15 * Work.Coercivity.EL12z f
        ≤ 16 * 10 ^ 15 * Work.Coercivity.Ef f := by
      have := mul_le_mul_of_nonneg_left hEL (show (0 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num)
      linarith [this]
    have hED' : (10 : ℝ) ^ 15 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 15 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
      rw [Coer1.Ef_eq_EnOne]; exact Coer1.EnOne_nonneg f
    linarith [hb, hEL', hED', hEfnn]
  have h3 : 2 * 10 ^ 16 * Work.Coercivity.Ef f - 10 ^ 20 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    have hED' : (10 : ℝ) ^ 20 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 20 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    linarith [hb, hED']
  have h4 : ((17 / 40 - 1 / 100) * 10 ^ 21) * Work.Coercivity.EDth α f
        - 10 ^ 15 * Work.Coercivity.Ef f
      ≤ (10 : ℝ) ^ 21 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
    have hb := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    linarith [hb]
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Coer1.EDz_eq_En]; exact Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Coer1.EfEta_eq_En]; exact Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Coer1.Ef_eq_EnOne]; exact Coer1.EnOne_nonneg f
  have e4 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Coer1.EDth_eq_En]; exact Coer1.En_nonneg _ _
  linarith [h1, h2, h3, h4, e1, e2, e3, e4]

end Work.FTS.CoercivityFix.Coer1T
