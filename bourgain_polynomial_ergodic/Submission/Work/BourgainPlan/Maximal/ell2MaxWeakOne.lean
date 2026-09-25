import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.linearizedWeakType
import Submission.Work.BourgainPlan.Maximal.aeSelectionLinOp

/-!
# Weak-`(1,1)` bound for the `ℓ²`-valued dyadic maximal function

The proof is the standard linearisation: `ell2F = (Σ_t (dyMax ‖f t‖ₑ)²)^{1/2}` is (a.e.) the
supremum, over measurable selections of dyadic levels `m` and normalised weights `e`
(`Σ_t e_t² ≤ 1`), of the *linearised* operator `linOp f m e`. The weak-`(1,1)` bound for the
latter is `linearizedWeakType` (a Calderón--Zygmund argument), and the selection is supplied by
`aeSelectionLinOp`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

theorem ell2MaxWeakOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam < (Work.BourgainPlan.Maximal.ell2Max f x) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C₁, hC₁, hlin⟩ := linearizedWeakType
  refine ⟨2 * C₁, by positivity, fun n f hf lam hlam => ?_⟩
  have hpos : (0 : ℝ) < 2 * C₁ / lam := by positivity
  by_cases hσ : ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((1 : ℝ) / 2) = ⊤
  · rw [hσ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne']
    exact le_top
  · obtain ⟨m, e, hm, he, he0, he1, hnull, hae⟩ := aeSelectionLinOp n f hf (by simpa [ell2Sigma] using hσ)
    have hbound := hlin n f hf m hm e he he0 he1 lam hlam
    have hN : volume {x : ℝ | ¬ (ell2F f x ≤ 2 * linOp f m e x)} = 0 :=
      (MeasureTheory.measure_eq_zero_iff_ae_notMem).mpr
        (hae.mono fun x hx => by simp only [Set.mem_setOf_eq, not_not]; exact hx)
    have hsub : {x : ℝ | ENNReal.ofReal lam < ell2F f x} ⊆
        ({x : ℝ | ell2F f x = ⊤} ∪ {x : ℝ | ¬ (ell2F f x ≤ 2 * linOp f m e x)})
          ∪ {x : ℝ | ENNReal.ofReal (lam / 2) < linOp f m e x} := by
      intro x hx
      by_cases htop : ell2F f x = ⊤
      · exact Or.inl (Or.inl htop)
      · by_cases hbad : ¬ (ell2F f x ≤ 2 * linOp f m e x)
        · exact Or.inl (Or.inr hbad)
        · refine Or.inr ?_
          have hbad' : ell2F f x ≤ 2 * linOp f m e x := not_not.mp hbad
          have h1 : ENNReal.ofReal lam < 2 * linOp f m e x := lt_of_lt_of_le hx hbad'
          have h2 : ENNReal.ofReal lam / 2 < linOp f m e x := by
            rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
              (Or.inr ENNReal.ofReal_ne_top), mul_comm]
            exact h1
          have h3 : ENNReal.ofReal (lam / 2) < linOp f m e x := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
            exact h2
          exact h3
    calc volume {x : ℝ | ENNReal.ofReal lam < ell2F f x}
        ≤ volume (({x : ℝ | ell2F f x = ⊤} ∪ {x : ℝ | ¬ (ell2F f x ≤ 2 * linOp f m e x)})
            ∪ {x : ℝ | ENNReal.ofReal (lam / 2) < linOp f m e x}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ volume ({x : ℝ | ell2F f x = ⊤} ∪ {x : ℝ | ¬ (ell2F f x ≤ 2 * linOp f m e x)})
            + volume {x : ℝ | ENNReal.ofReal (lam / 2) < linOp f m e x} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ (volume {x : ℝ | ell2F f x = ⊤} + volume {x : ℝ | ¬ (ell2F f x ≤ 2 * linOp f m e x)})
            + volume {x : ℝ | ENNReal.ofReal (lam / 2) < linOp f m e x} :=
          add_le_add (MeasureTheory.measure_union_le _ _) le_rfl
      _ = volume {x : ℝ | ENNReal.ofReal (lam / 2) < linOp f m e x} := by
          rw [hnull, hN, add_zero, zero_add]
      _ ≤ ENNReal.ofReal (C₁ / lam) * ∫⁻ x, ell2Sigma f x := by
          simpa using hbound
      _ ≤ ENNReal.ofReal (2 * C₁ / lam) * ∫⁻ x, (ell2Sq f x) ^ ((1 : ℝ) / 2) := by
          have h1 : ∫⁻ x, ell2Sigma f x = ∫⁻ x, (ell2Sq f x) ^ ((1 : ℝ) / 2) := rfl
          rw [h1]
          refine mul_le_mul_left ?_ _
          rw [show (2 * C₁ / lam : ℝ) = 2 * (C₁ / lam) by ring]
          exact ENNReal.ofReal_le_ofReal (by linarith [show (0 : ℝ) < C₁ / lam by positivity])

end Work.BourgainPlan.Maximal
