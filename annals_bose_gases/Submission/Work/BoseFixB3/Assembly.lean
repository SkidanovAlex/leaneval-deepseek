import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3.Assembly` — `NodeB3B` from the five steps of FS §7

The **assembly** of the LEAD-FROZEN `Work.BoseBoxFix.NodeB3B` from the five
statements of `Steps.lean`.  This is pure bookkeeping plus the `n₊^H`/`n₊`
budget split of FS `eq:ReduceQ3`; it contains no analysis.  Verified, sorry-free.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `‖Φ‖² ≥ 0` on the box. -/
lemma normB_nonneg (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    0 ≤ normB v μ n Φ :=
  integral_nonneg fun x => sq_nonneg (Φ x)

/-- `Adm` is monotone in the diluteness threshold. -/
lemma adm_mono {v : ℝ³ → ℝ} {ε ε' μ : ℝ} (h : Adm v ε μ) (hε : ε ≤ ε') : Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hε, h.2.2⟩

/-- The assembling arithmetic: from the five steps, `NodeB3B`.

The `n₊^H` budget `(b/100)ε_T(dℓ)⁻²n₊^H` of `eq:ReduceQ3` is exactly the two
`(b/200)` halves consumed by `B3CSRoot` and `B3EpsRoot` through
`B3HAbsorbRoot`; the `n₊` budget `(b/100)ℓ⁻²n₊` splits into the `(b/200)ℓ⁻²n₊`
moved into `B3CSRoot` and a discarded half. -/
theorem nodeB3B_of_steps {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ} {fc : LowCut}
    (hav : 0 < a v)
    (hsplit : B3SplitRoot v h fc) (hcs : B3CSRoot v h R fc)
    (habs : B3HAbsorbRoot v) (hconv : B3ConvRoot v h R fc) (heps : B3EpsRoot v h fc) :
    NodeB3B v h R fc := by
  classical
  obtain ⟨Kcs, εcs, hKcs, hεcs, hcs⟩ := hcs
  obtain ⟨Kcn, εcn, hKcn, hεcn, hcn⟩ := hconv
  obtain ⟨Kep, εep, hKep, hεep, hep⟩ := heps
  obtain ⟨εab, hεab, hab⟩ := habs Kcs hKcs
  refine ⟨max Kcn Kep, min εab (min εcn (min εep εcs)), le_max_of_le_left hKcn, ?_, ?_⟩
  · exact lt_min hεab (lt_min hεcn (lt_min hεep hεcs))
  · intro μ hAdm n Φ hn
    have hμ : 0 < μ := hAdm.1
    have hμa : 0 < μ * (a v) := mul_pos hμ hav
    have hμa3 : 0 < μ * (a v) ^ 3 := by positivity
    have hKl : 0 < (patAt μ (a v)).Kl := by
      rw [patAt_Kl]; exact fsXp_pos hμa3
    have hℓ : 0 < ellAt μ (a v) := by
      have := boxSide_pos (P := patAt μ (a v)) (μ := μ) (a := a v) hμ hav hKl
      simpa [ellAt, patAt, sideAt] using this
    have hadm_ab : Adm v εab μ := adm_mono hAdm (min_le_left _ _)
    have hadm_cn : Adm v εcn μ :=
      adm_mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    have hadm_ep : Adm v εep μ :=
      adm_mono hAdm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hadm_cs : Adm v εcs μ :=
      adm_mono hAdm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hb : 0 ≤ (patAt μ (a v)).b := by rw [patAt_b]; exact bValue_pos.le
    have heT : 0 ≤ (patAt μ (a v)).eT := by
      rw [patAt_eT]; exact fsXp_nonneg hμa3.le
    have hd : 0 ≤ (patAt μ (a v)).d := by
      rw [patAt_d]; exact fsXp_nonneg hμa3.le
    have hℓ2 : 0 ≤ (ellAt μ (a v)) ^ (-2 : ℤ) := zpow_nonneg hℓ.le _
    have hnp : 0 ≤ cnPlus (ellAt μ (a v)) (Φ : X n → ℝ) := cnPlus_nonneg _
    have hnH : 0 ≤ nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) :=
      nPlusHB_nonneg hℓ _
    have hNn : 0 ≤ normB v μ n (Φ : X n → ℝ) := normB_nonneg v μ n _
    have hdl : 0 ≤ ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ) :=
      zpow_nonneg (mul_nonneg hd hℓ.le) _
    have hTd : 0 ≤ (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1)) :=
      pow_nonneg hd _
    have hRR : 0 ≤ R ^ 2 / ellAt μ (a v) ^ 2 := div_nonneg (sq_nonneg R) (by positivity)
    have hXX : 0 ≤ μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) (pow_nonneg hℓ.le 3)) hNn
    -- the four step inequalities at this state
    have h1 := hcs μ hadm_cs n Φ hn
    have h2 := hab μ hadm_ab
    have h3 := hcn μ hadm_cn n Φ hn
    have h4 := hep μ hadm_ep n Φ hn
    have h5 := hsplit μ n Φ
    -- the absorbed `n₊^H` error: `Kcs ℓ⁻²K_ℓ⁴ n₊^H ≤ (b/200)ε_T(dℓ)⁻²n₊^H`
    have hdne : (patAt μ (a v)).d ≠ 0 := by
      rw [patAt_d]; exact ne_of_gt (fsXp_pos hμa3)
    have hℓne : ellAt μ (a v) ≠ 0 := ne_of_gt hℓ
    have hℓinv : (ellAt μ (a v)) ^ (-2 : ℤ)
        = (patAt μ (a v)).d ^ 2 * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ) := by
      have h2 : (patAt μ (a v)).d ^ (2 : ℕ) * ((patAt μ (a v)).d ^ (2 : ℕ))⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero 2 hdne)
      have h3 : ((patAt μ (a v)).d * ellAt μ (a v)) ^ (2 : ℕ)
          = (patAt μ (a v)).d ^ (2 : ℕ) * (ellAt μ (a v)) ^ (2 : ℕ) := mul_pow _ _ _
      calc (ellAt μ (a v)) ^ (-2 : ℤ)
          = ((ellAt μ (a v)) ^ (2 : ℕ))⁻¹ := by
            simp [zpow_neg]
        _ = ((patAt μ (a v)).d ^ (2 : ℕ) * ((patAt μ (a v)).d ^ (2 : ℕ))⁻¹)
              * ((ellAt μ (a v)) ^ (2 : ℕ))⁻¹ := by rw [h2, one_mul]
        _ = (patAt μ (a v)).d ^ 2
              * (((patAt μ (a v)).d ^ (2 : ℕ) * (ellAt μ (a v)) ^ (2 : ℕ)))⁻¹ := by
            rw [mul_inv]; ring
        _ = (patAt μ (a v)).d ^ 2
              * (((patAt μ (a v)).d * ellAt μ (a v)) ^ (2 : ℕ))⁻¹ := by rw [← h3]
        _ = (patAt μ (a v)).d ^ 2
              * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ) := by
            simp [zpow_neg]
    have hY : 0 ≤ (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
        * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
        * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hb (by norm_num : (0:ℝ) ≤ 200)) heT) hdl) hnH
    have habsorb : Kcs * (ellAt μ (a v)) ^ (-2 : ℤ) * (patAt μ (a v)).Kl ^ 4
        * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)
        ≤ (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
            * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
            * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) := by
      have hkey : Kcs * (patAt μ (a v)).d ^ 2 * (patAt μ (a v)).Kl ^ 4
          * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
          ≤ (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
              * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ) :=
        mul_le_mul_of_nonneg_right h2 hdl
      calc Kcs * (ellAt μ (a v)) ^ (-2 : ℤ) * (patAt μ (a v)).Kl ^ 4
              * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)
          = Kcs * (patAt μ (a v)).d ^ 2 * (patAt μ (a v)).Kl ^ 4
              * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
              * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) := by
            rw [hℓinv]; ring
        _ ≤ (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
              * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
              * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) :=
            mul_le_mul_of_nonneg_right hkey hnH
    -- the budget identity
    have hbudget : (patAt μ (a v)).b / 100
          * ((ellAt μ (a v)) ^ (-2 : ℤ) * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
            + (patAt μ (a v)).eT * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
                * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ))
        = (patAt μ (a v)).b / 200 * (ellAt μ (a v)) ^ (-2 : ℤ)
              * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
            + (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
                * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
                * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)
            + ((patAt μ (a v)).b / 200 * (ellAt μ (a v)) ^ (-2 : ℤ)
                * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
              + (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
                * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
                * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)) := by
      ring
    -- the error-factor identity
    have herror : (max Kcn Kep) * μ ^ 2 * a v * ellAt μ (a v) ^ 3
          * ((patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
            + R ^ 2 / ellAt μ (a v) ^ 2) * normB v μ n (Φ : X n → ℝ)
        = (max Kcn Kep * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
            + max Kcn Kep * (R ^ 2 / ellAt μ (a v) ^ 2))
          * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)) := by
      ring
    have hKpe : Kep * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
        ≤ max Kcn Kep * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hTd
    have hKcnR : Kcn * (R ^ 2 / ellAt μ (a v) ^ 2)
        ≤ max Kcn Kep * (R ^ 2 / ellAt μ (a v) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hRR
    have hfinal : Kep * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ))
            * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
          + Kcn * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ))
            * (R ^ 2 / ellAt μ (a v) ^ 2)
        ≤ (max Kcn Kep * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
            + max Kcn Kep * (R ^ 2 / ellAt μ (a v) ^ 2))
          * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)) := by
      have e1 : Kep * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ))
            * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
          = Kep * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
            * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)) := by ring
      have e2 : Kcn * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ))
            * (R ^ 2 / ellAt μ (a v) ^ 2)
          = Kcn * (R ^ 2 / ellAt μ (a v) ^ 2)
            * (μ ^ 2 * a v * ellAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)) := by ring
      rw [e1, e2, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hKpe hXX)
        (mul_le_mul_of_nonneg_right hKcnR hXX)
    have key : q3word (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)
          + (1 / 4) * q4word (ellAt μ (a v)) (wAt μ (a v) v) (omAt h) (Φ : X n → ℝ)
          + (patAt μ (a v)).b / 100
              * ((ellAt μ (a v)) ^ (-2 : ℤ) * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
                + (patAt μ (a v)).eT * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
                    * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ))
        ≥ q3lowWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)
          - (max Kcn Kep) * μ ^ 2 * a v * ellAt μ (a v) ^ 3
              * ((patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
                + R ^ 2 / ellAt μ (a v) ^ 2)
              * normB v μ n (Φ : X n → ℝ) := by
      rw [h5, hbudget, herror]
      nlinarith [h1, h3, h4, habsorb, hY, hnp, hnH, hXX, hRR, hTd,
        mul_nonneg (div_nonneg hb (by norm_num : (0:ℝ) ≤ 200)) hℓ2,
        mul_nonneg (mul_nonneg (div_nonneg hb (by norm_num : (0:ℝ) ≤ 200)) hℓ2) hnp,
        mul_le_mul_of_nonneg_right hKpe hXX, mul_le_mul_of_nonneg_right hKcnR hXX]
    exact key

end Work.BoseFixB3
