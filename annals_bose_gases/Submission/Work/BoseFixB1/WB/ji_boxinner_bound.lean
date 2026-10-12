import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.WB.boxState_sq_bound
import Submission.Work.BoseFixB1.WB.ji_helpers
import Submission.Work.BoseFixB1.perBoxF_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A uniform bound on the inner `x`-integral `boxInner`

`boxInner v h μ n Φ u = ∫_{abox n ℓ} Φ² F(nCountB(u)/chiMass(u))` is bounded by the
`u`-independent constant `μ P n ℓ^{3(n-1)} + μ²‖Φ‖²`, where `P` bounds `Φ²` on the box
and `∫ nCountB(u)` is computed by the product decomposition of the box integral.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem boxInner_le_const_self {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hμ : 0 < μ) (hM : 1 ≤ (paramsAt μ (a v)).M)
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ³,
      boxInner v h μ n (Φ : X n → ℝ) u ≤ M := by
  obtain ⟨P, hP0, hPb⟩ := boxState_sq_bound (n := n) (ℓ := sideAt μ (a v)) Φ
  refine ⟨μ * P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)) + μ ^ 2 * normB v μ n (Φ : X n → ℝ),
    ?_, ?_⟩
  · have h1 : 0 ≤ μ * P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)) := by
      refine mul_nonneg (mul_nonneg hμ.le hP0) ?_
      exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (pow_nonneg hℓ.le 3) _)
    have h2 : 0 ≤ μ ^ 2 * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (sq_nonneg _) (normB_nonneg _)
    linarith
  · intro u
    have hcontN : Continuous (fun x : X n =>
        nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x) := by
      unfold nCountB
      refine continuous_finset_sum _ fun i _ => ?_
      exact ((chiSmallB_continuous hM hℓ hd u).comp (continuous_apply i)).pow 2
    have hΦc : Continuous (fun x : X n => (Φ : X n → ℝ) x ^ 2) := (Φ.contDiff.continuous).pow 2
    have haboxmeas : MeasurableSet (abox n (sideAt μ (a v))) :=
      (Work.UBBInputs9.B.abox_isCompact n (sideAt μ (a v))).isClosed.measurableSet
    -- the pointwise bound `F(t) ≤ μ(t+μ)` and the first monotonicity
    have hCnn : 0 ≤ chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      chiMass_nonneg _ _ _ _
    have hintF : IntegrableOn (fun x : X n => (Φ : X n → ℝ) x ^ 2 *
        (μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
        (abox n (sideAt μ (a v))) :=
      Work.UBBInputs9.B.integrableOn_abox_of_continuous'
        (hΦc.mul ((continuous_const.mul (hcontN.div_const _)).add continuous_const))
    have hstep1 : boxInner v h μ n (Φ : X n → ℝ) u
        ≤ ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
            (μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ) := by
      rw [boxInner]
      refine integral_mono_of_nonneg ?_ hintF ?_
      · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
        intro x _
        exact mul_nonneg (sq_nonneg _)
          (psiWeight_one_nonneg_local hμ
            (div_nonneg (nCountB_nonneg _ _ _ _ x) hCnn))
      · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
        intro x _
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have ht : 0 ≤ nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
          div_nonneg (nCountB_nonneg _ _ _ _ x) hCnn
        have h := Work.BoseFixB1.psiWeight_le_mu_mul_add (μ := μ) hμ ht
        calc psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            ≤ μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ) := h
          _ = μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ := by
              ring
    -- ## step 2: `∫ N ≤ n ℓ^{3(n-1)}·chiMass`
    have hIntNbound : (∫ x in abox n (sideAt μ (a v)),
          nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        ≤ (n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
            * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      rw [show (fun x : X n => nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u x)
            = fun x : X n => ∑ i : Fin n,
                (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u (x i)) ^ 2
          from by funext x; rw [nCountB]]
      rw [MeasureTheory.integral_finset_sum]
      · have hcomp : ∀ i : Fin n,
            (∫ x in abox n (sideAt μ (a v)),
              (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u (x i)) ^ 2)
            = (sideAt μ (a v) ^ 3) ^ (n - 1) *
                ∫ z in acube (sideAt μ (a v)),
                  (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u z) ^ 2 :=
          fun i => Work.UBBInputs8.A.integral_abox_comp_apply
            (N := n) (L := sideAt μ (a v)) hℓ.le i
            (((chiSmallB_continuous hM hℓ hd u).pow 2).continuousOn.integrableOn_compact
              (acube_compact hℓ))
        rw [Finset.sum_congr rfl (fun i _ => hcomp i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have hle : (∫ z in acube (sideAt μ (a v)),
              (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u z) ^ 2)
            ≤ chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
          rw [chiMass_def]
          exact setIntegral_le_integral (integrable_chiSmallB_sq_slice hM hℓ u)
            (Filter.Eventually.of_forall fun z => sq_nonneg _)
        calc (n : ℝ) * ((sideAt μ (a v) ^ 3) ^ (n - 1) *
              ∫ z in acube (sideAt μ (a v)),
                (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u z) ^ 2)
            ≤ (n : ℝ) * ((sideAt μ (a v) ^ 3) ^ (n - 1) *
                chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hle (pow_nonneg (pow_nonneg hℓ.le 3) _))
                (Nat.cast_nonneg n)
          _ = (n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by ring
      · intro i _
        exact ContinuousOn.integrableOn_compact
          (Work.UBBInputs9.B.abox_isCompact n (sideAt μ (a v)))
          (((chiSmallB_continuous hM hℓ hd u).comp (continuous_apply i)).pow 2).continuousOn
    -- ## step 3: `∫ Φ²·N ≤ P·n·ℓ^{3(n-1)}·chiMass`
    have hintPN : IntegrableOn (fun x : X n => P * nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x) (abox n (sideAt μ (a v))) :=
      Work.UBBInputs9.B.integrableOn_abox_of_continuous' (continuous_const.mul hcontN)
    have hkey : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
          nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        ≤ P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
            * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
      have hmono : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
            nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          ≤ ∫ x in abox n (sideAt μ (a v)), P *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x := by
        refine integral_mono_of_nonneg ?_ hintPN ?_
        · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
          intro x _
          exact mul_nonneg (sq_nonneg _) (nCountB_nonneg _ _ _ _ x)
        · apply MeasureTheory.ae_restrict_of_forall_mem haboxmeas
          intro x hx
          exact mul_le_mul_of_nonneg_right (hPb x hx) (nCountB_nonneg _ _ _ _ x)
      rw [MeasureTheory.integral_const_mul] at hmono
      exact hmono.trans (mul_le_mul_of_nonneg_left hIntNbound hP0)
    -- assemble
    have hstep2 : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
          (μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
        = μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by
      rw [show (fun x : X n => (Φ : X n → ℝ) x ^ 2 *
            (μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ))
          = fun x : X n => (μ * ((Φ : X n → ℝ) x ^ 2 *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            + μ ^ 2 * (Φ : X n → ℝ) x ^ 2) from by
        funext x; ring]
      have h1int : IntegrableOn (fun x : X n => (μ * ((Φ : X n → ℝ) x ^ 2 *
            nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
          (abox n (sideAt μ (a v))) :=
        Work.UBBInputs9.B.integrableOn_abox_of_continuous'
          ((continuous_const.mul (hΦc.mul hcontN)).div_const _)
      have h2int : IntegrableOn (fun x : X n => μ ^ 2 * (Φ : X n → ℝ) x ^ 2)
          (abox n (sideAt μ (a v))) :=
        (Work.UBBInputs9.B.integrableOn_abox_of_continuous' hΦc).const_mul (μ ^ 2)
      rw [MeasureTheory.integral_add h1int h2int]
      simp only [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
        Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      try ring_nf
    have hCdiv : μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
            nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
          / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))) := by
      have hdiv : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          ≤ P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)) := by
        by_cases hC0 : chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u = 0
        · rw [hC0, div_zero]
          exact mul_nonneg hP0
            (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (pow_nonneg hℓ.le 3) _))
        · rw [div_le_iff₀ (lt_of_le_of_ne hCnn (Ne.symm hC0))]
          calc (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
                nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
              ≤ P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)
                  * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := hkey
            _ = P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))
                  * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by ring
      calc μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          = μ * ((∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
                nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by ring
        _ ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))) :=
            mul_le_mul_of_nonneg_left hdiv hμ.le
    calc boxInner v h μ n (Φ : X n → ℝ) u
        ≤ (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
            (μ * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + μ * μ)) :=
          hstep1
      _ = μ * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
              nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := hstep2
      _ ≤ μ * (P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1)))
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by
          linarith [hCdiv]
      _ = μ * P * ((n : ℝ) * (sideAt μ (a v) ^ 3) ^ (n - 1))
          + μ ^ 2 * normB v μ n (Φ : X n → ℝ) := by ring

end Work.BoseFixB1.WB
