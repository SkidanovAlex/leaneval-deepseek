import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary arithmetic

The elementary real-arithmetic lemma that converts the case-`A` bound
(`Ce·Kx·HkSq` with `Kx ≤ C·α^{-1}·K4`) into the constant shape requested by `mulTermSmall`. -/

/-- `α^{-1} ≤ α^{-3}` on `(0,1]`. -/
private lemma rpow_neg_one_le_neg_three {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 : ℝ)) ≤ α ^ (-(3 : ℝ)) := by
  have h2 : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hα0.le, one_le_inv₀ (by positivity)]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  calc α ^ (-(1 : ℝ)) = α ^ (-(1 : ℝ)) * 1 := by ring
    _ ≤ α ^ (-(1 : ℝ)) * α ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hα0.le _)
    _ = α ^ (-(3 : ℝ)) := by
        rw [← Real.rpow_add hα0]
        norm_num

/-- The case-`A` (guard) arithmetic: `Kx ≤ (Cz*10+Cm+1) α^{-1} K4`. -/
private lemma arithA (Ce Cz Cm Kc α K0 K4 K6 M HkSq HkN : ℝ)
    (hCe : 0 ≤ Ce) (hCz : 0 ≤ Cz) (hCm : 0 ≤ Cm) (hKc : 0 ≤ Kc)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hM : 0 ≤ M)
    (hSq : 0 ≤ HkSq) (hN : 0 ≤ HkN) :
    Ce * ((Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4) * HkSq
      ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + HkSq) + (K4 + K6) * (1 + M) * (1 + HkN)) := by
  have hα13 := rpow_neg_one_le_neg_three hα0 hα1
  have ha3 : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hT2 : 0 ≤ (K4 + K6) * (1 + M) * (1 + HkN) := by positivity
  have hsum : K4 * HkSq ≤ (1 + K0 + K4) * (1 + HkSq) + (K4 + K6) * (1 + M) * (1 + HkN) := by
    have h1 : K4 * HkSq ≤ (1 + K0 + K4) * (1 + HkSq) := by nlinarith
    linarith
  have hkey : α ^ (-(1 : ℝ)) * (K4 * HkSq)
      ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)
          + (K4 + K6) * (1 + M) * (1 + HkN)) := by
    have h1 : α ^ (-(1 : ℝ)) * (K4 * HkSq) ≤ α ^ (-(3 : ℝ)) * (K4 * HkSq) :=
      mul_le_mul_of_nonneg_right hα13 (by positivity)
    have h2 : α ^ (-(3 : ℝ)) * (K4 * HkSq)
        ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)
            + (K4 + K6) * (1 + M) * (1 + HkN)) :=
      mul_le_mul_of_nonneg_left hsum ha3
    exact h1.trans h2
  have hcoef1 : Ce * (Cz * 10 + Cm + 1)
      ≤ Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1 := by
    have : 0 ≤ Kc * Cm + Kc + 1 := by positivity
    linarith
  have hB0 : 0 ≤ Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1 := by positivity
  have hc0 : 0 ≤ α ^ (-(1 : ℝ)) * (K4 * HkSq) := by positivity
  calc Ce * ((Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4) * HkSq
      = (Ce * (Cz * 10 + Cm + 1)) * (α ^ (-(1 : ℝ)) * (K4 * HkSq)) := by ring
    _ ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
          * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)
              + (K4 + K6) * (1 + M) * (1 + HkN))) :=
        mul_le_mul hcoef1 hkey hc0 hB0
    _ = (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + HkSq) + (K4 + K6) * (1 + M) * (1 + HkN)) := by ring

/-! ## `mulTermSmall` from the mismatch sub-case -/

/-- **`mulTermSmall` conditional on the mismatch sub-case.**  Everything except the
`ρ = leafGam α ∧ a = a₁` sub-case is proved here:

* the **guard** case (`1 ≤ a - a₁ ∨ ρ = leafEta ∨ ρ = leafOne`) is `T6Gen.summand_le_easy`
  applied to the coefficient slot `mixed b₁ a₁ A`, whose *absolute pointwise bound* is
  `sup_dz_le_hk` (`a₁ = 0`, `b₁ ≤ 2`) resp. `T2SupB2.mixed_pointwise_le_Xn` (`a₁ ≥ 1`);
* the arithmetic is `arithA`, and the dispatch is the `by_cases`.

`Kc` is the constant of the mismatch sub-case (`T6CoefAux/mismatchCoefCase`). -/
theorem mulTermSmall_of_mismatch (Kc : ℝ) (hKcpos : 0 < Kc)
    (hmis : ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ Kc * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
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
  obtain ⟨Ce, hCepos, heasy⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
  obtain ⟨Cz, hCzpos, hdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cm, hCmpos, hmx⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  have hCe0 : 0 ≤ Ce := le_of_lt hCepos
  have hCz0 : 0 ≤ Cz := le_of_lt hCzpos
  have hCm0 : 0 ≤ Cm := le_of_lt hCmpos
  have hKc0 : 0 ≤ Kc := le_of_lt hKcpos
  refine ⟨Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp2 ha₁ hb₁ hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) (by norm_num) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN0 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hαinv1 : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hα0.le, Real.rpow_one]
    exact (one_le_inv₀ hα0).mpr hα1
  -- ## the pointwise bound of the `A`-slot
  have hXbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a₁ A z θ| ≤ (Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4 := by
    intro z θ hz hθ hθ2
    rcases Nat.eq_zero_or_pos a₁ with h0 | hpos
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b₁ ≤ 2 := by omega
      have h1 := hdz α A hα0 hα1 hcoef.sm hcoef.h4 b₁ hb z θ hz hθ hθ2
      have hscale : Cz / Real.sqrt (Work.Spaces.gam α - 1) ≤ Cz * 10 * α ^ (-(1 : ℝ)) := by
        rw [Work.Spaces.gam_sub_one]
        have hpos10 : 0 < α / 10 := by linarith
        have hs : α / 10 ≤ Real.sqrt (α / 10) := by
          have hsq : (α / 10) ^ 2 ≤ α / 10 := by nlinarith
          nlinarith [Real.sq_sqrt hpos10.le, Real.sqrt_nonneg (α / 10)]
        have h3 : 1 / Real.sqrt (α / 10) ≤ 1 / (α / 10) := one_div_le_one_div_of_le hpos10 hs
        have h4 : (1 : ℝ) / (α / 10) = 10 * α ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg hα0.le, Real.rpow_one, one_div_div, div_eq_mul_inv]
        calc Cz / Real.sqrt (α / 10) = Cz * (1 / Real.sqrt (α / 10)) := by ring
          _ ≤ Cz * (1 / (α / 10)) := mul_le_mul_of_nonneg_left h3 hCz0
          _ = Cz * (10 * α ^ (-(1 : ℝ))) := by rw [h4]
          _ = Cz * 10 * α ^ (-(1 : ℝ)) := by ring
      have h3nn : 0 ≤ Cz / Real.sqrt (Work.Spaces.gam α - 1) :=
        div_nonneg hCz0 (Real.sqrt_nonneg _)
      calc |Work.Spaces.DzIter b₁ A z θ|
          ≤ Cz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := h1
        _ ≤ Cz / Real.sqrt (Work.Spaces.gam α - 1) * K4 :=
              mul_le_mul_of_nonneg_left hcoef.n4 h3nn
        _ ≤ (Cz * 10 * α ^ (-(1 : ℝ))) * K4 := mul_le_mul_of_nonneg_right hscale hK4
        _ ≤ ((Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ))) * K4 := by
              refine mul_le_mul_of_nonneg_right ?_ hK4
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hα0.le _)
              linarith [hCm0]
        _ = (Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4 := by ring
    · have h1 := hmx α A hα0 hα1 hcoef.sm hcoef.h4 b₁ a₁ hpos hp2 z θ hz hθ hθ2
      have hC : Cm ≤ (Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) := by
        have h1' : Cm ≤ Cz * 10 + Cm + 1 := by linarith [hCz0]
        have h2 : Cm ≤ (Cz * 10 + Cm + 1) * 1 := by simpa using h1'
        exact h2.trans (mul_le_mul_of_nonneg_left hαinv1 (by linarith [hCz0, hCm0]))
      calc |Work.Spaces.mixed b₁ a₁ A z θ| ≤ Cm * Work.FTS.Nonlin.Xn α A := h1
        _ ≤ Cm * K4 := mul_le_mul_of_nonneg_left hcoef.n4 hCm0
        _ ≤ ((Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ))) * K4 :=
              mul_le_mul_of_nonneg_right hC hK4
        _ = (Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4 := by ring
  by_cases hguard : 1 ≤ a - a₁ ∨ ρ = Work.FTS.TransportS.leafEta
      ∨ ρ = Work.FTS.TransportS.leafOne
  · -- ## Case A: the guard holds
    obtain ⟨hint, hbd⟩ := heasy α hα (fun z θ => Work.Spaces.mixed b₁ a₁ A z θ) f
      (a - a₁) (b - b₁) a b ρ ((Cz * 10 + Cm + 1) * α ^ (-(1 : ℝ)) * K4)
      (hcoef.sm.mixed b₁ a₁) (by positivity) hXbd hdat.sm hdat.h6 (by omega) hab hleaf hguard
    refine ⟨hint, ?_⟩
    refine hbd.trans ?_
    exact arithA Ce Cz Cm Kc α K0 K4 K6 M (Work.Spaces.HkSq α 6 f)
      (Work.Spaces.HkNorm α 6 f) hCe0 hCz0 hCm0 hKc0 hα0 hα1 hK0 hK4 hK6 hM0 hSq0 hN0
  · -- ## Case B: the mismatch (`ρ = leafGam`, `a = a₁`), delegated
    push_neg at hguard
    have hρ : ρ = Work.FTS.TransportS.leafGam α := by
      rcases hleaf with h | h | ⟨-, h⟩
      · exact absurd h hguard.2.1
      · exact absurd h hguard.2.2
      · exact h
    have ha₁1 : 1 ≤ a₁ := by
      have h1a : 1 ≤ a := by
        rcases hleaf with h | h | ⟨h, -⟩
        · exact absurd h hguard.2.1
        · exact absurd h hguard.2.2
        · exact h
      have hz : a - a₁ = 0 := by omega
      omega
    refine ⟨?_, ?_⟩
    · rw [hρ]
      exact (hmis α hα A f K0 K4 a b a₁ b₁ hcoef.sm hcoef.h4 hcoef.h6 hcoef.val hcoef.n4
        hdat.sm hdat.h7 hdat.vanish ha₁1 hp2 ha₁ hb₁ hab).1
    · rw [hρ]
      refine (hmis α hα A f K0 K4 a b a₁ b₁ hcoef.sm hcoef.h4 hcoef.h6 hcoef.val hcoef.n4
        hdat.sm hdat.h7 hdat.vanish ha₁1 hp2 ha₁ hb₁ hab).2.trans ?_
      -- the constant bookkeeping
      have hle : Kc ≤ Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1 := by
        have : 0 ≤ Ce * (Cz * 10 + Cm + 1) + Kc * Cm + 1 := by positivity
        linarith
      have hT2 : 0 ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
      have h1 : Kc * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
            * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have h2 : (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
            * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
            * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hα0.le _))
          (by positivity)
      calc Kc * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
          = Kc * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by ring
        _ ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
              * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := h1
        _ ≤ (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1)
              * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                  + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := h2
        _ = (Ce * (Cz * 10 + Cm + 1) + Kc * Cm + Kc + 1) * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by ring

theorem mulTermSmall : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
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
  obtain ⟨Kc, hKcpos, hmis⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase
  exact mulTermSmall_of_mismatch Kc hKcpos hmis

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
