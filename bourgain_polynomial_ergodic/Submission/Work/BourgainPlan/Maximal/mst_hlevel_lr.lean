import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.Maximal.mst_level_lr_small
import Submission.Work.Maximal.mst_level_lr_large

/-!
# The `ℓʳ` half of MST's level estimate, assembled from the two standalone halves

`mst_hlevel_lr` is the hypothesis `h_level_lr` of `maximal_statement_of_inputs`, but with the level
bump's Mikhlin data as explicit arguments (the interface of `Work.Maximal.mst_level_lr_small` and
`Work.Maximal.mst_level_lr_large`) instead of `η 0 = 1`.  It is the assembly of the two halves of
MST Theorem 7/8 (`k ≤ 2^{κ_s}` and `k ≥ 2^{κ_s}`) by
`sup_k ≤ sup_{k ≤ 2^{κ_s}} + sup_{k ≥ 2^{κ_s}}`, exactly as in `Maximal/mst_level_lr.lean` (the
sibling file of the same content, kept for the record).

This file exists so that the critical path does **not** depend on `Maximal/mst_level_lr.lean`: the
two halves are maintained by the `ℓʳ` lane under `Submission/Work/Maximal/`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset Filter
open scoped BigOperators ENNReal Topology
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

theorem mst_hlevel_lr (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.Maximal.mst_level_lr_small hΘ P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hδ D hD hGauss hνsml hr hr2
  obtain ⟨C₂, hC₂, h₂⟩ := Work.Maximal.mst_level_lr_large hΘ P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hδ D hD hGauss hνsml hr hr2
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun s g => ?_⟩
  have hlogpos : 0 < Real.log ((s : ℝ) + 2) := by
    apply Real.log_pos
    have : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
    linarith
  have hs1 : (1:ℝ) ≤ (s:ℝ) + 1 := by
    have : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
    linarith
  have hflog : 0 ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) :=
    mul_nonneg (by linarith) hlogpos.le
  have hpoint : ∀ m : ℤ,
      (⨆ k : ℕ, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ)
      ≤ (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ)
        + (⨆ k : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ) := by
    intro m
    refine iSup_le fun k => ?_
    rcases lt_or_ge k (2 ^ (mstKappa P s) + 1) with hk | hk
    · exact le_add_right (le_iSup_of_le k (le_iSup_of_le (Finset.mem_range.mpr hk) le_rfl))
    · refine le_add_left ?_
      have hk' : 2 ^ (mstKappa P s) ≤ k := by omega
      exact le_iSup_of_le k (le_iSup_of_le hk' le_rfl)
  have hmono : eLpNorm (fun m : ℤ => (⨆ k : ℕ,
      ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ))
      (ENNReal.ofReal r) Measure.count
    ≤ eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ)
        + (⨆ k : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ))
      (ENNReal.ofReal r) Measure.count := by
    refine eLpNorm_mono_enorm Measurable.of_discrete.aestronglyMeasurable (fun m => ?_)
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint m
  have hmeas1 : AEStronglyMeasurable (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
      ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ))
      Measure.count := Measurable.of_discrete.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun m : ℤ => (⨆ k : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
      ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ))
      Measure.count := Measurable.of_discrete.aestronglyMeasurable
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.mpr (le_of_lt hr)
  have hle2 : ENNReal.ofReal (C₂ * Real.log ((s : ℝ) + 2))
      ≤ ENNReal.ofReal (C₂ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) := by
    apply ENNReal.ofReal_le_ofReal
    calc C₂ * Real.log ((s : ℝ) + 2)
        = C₂ * (1 * Real.log ((s : ℝ) + 2)) := by ring
      _ ≤ C₂ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs1 hlogpos.le) hC₂.le
  have hkey : ENNReal.ofReal (C₁ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
        * eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count
      + ENNReal.ofReal (C₂ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
        * eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count
      = ENNReal.ofReal ((C₁ + C₂) * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
        * eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count := by
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hC₁.le hflog) (mul_nonneg hC₂.le hflog),
      show C₁ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))
          + C₂ * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))
          = (C₁ + C₂) * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) by ring]
  refine hmono.trans ?_
  refine (eLpNorm_add_le hr1).trans ?_
  refine (add_le_add (h₁ s g) (h₂ s g)).trans ?_
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_right hle2 (by positivity))).trans ?_
  rw [hkey]

end

end Work.BourgainPlan.Maximal
