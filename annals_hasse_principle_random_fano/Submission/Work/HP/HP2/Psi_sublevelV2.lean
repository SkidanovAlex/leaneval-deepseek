import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.HP2.Psi_M
import Submission.Work.HP2.Psi_form_repr
import Submission.Work.HP2.hom_sublevelV2

set_option autoImplicit false
noncomputable section

namespace Work.HP.HP2

theorem Psi_sublevel (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (a : Work.HP.Mon d n → ℤ) (α T lam : ℝ),
      a ≠ 0 → 1 ≤ α → 0 < T → 0 ≤ lam →
      (MeasureTheory.volume {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ T ∧
          |Work.HP.Psi d n a α x| ≤ lam}).toReal
        ≤ T ^ (n + 1) * C *
            Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (Work.HP.eNorm a) ^ 2))) (1 / K) := by
  obtain ⟨C, K, hCpos, hKpos, hbound⟩ :=
    Work.HP2.hom_sublevel n (2 * d) hn (by omega)
  obtain ⟨c, hcpos, hPsiM⟩ := Psi_M d n hd
  refine ⟨C * Real.rpow c⁻¹ (1 / K), K, ?_, hKpos, ?_⟩
  · exact mul_pos hCpos (Real.rpow_pos_of_pos (inv_pos.mpr hcpos) _)
  · intro a α T lam ha hα hT hlam
    obtain ⟨M, hMpos, hsup, hatt, hcM⟩ := hPsiM a α ha hα
    obtain ⟨H, hH⟩ := Work.HP2.Psi_form_repr d n a α
    have hhom : ∀ c' : ℝ, 0 ≤ c' → ∀ x,
        Psi d n a α (c' • x) = c' ^ (2 * d) * Psi d n a α x := by
      intro c' hc' x
      have h := Psi_const_mul (d := d) (n := n) a α c' x hc'
      have heq : (c' • x : Fin (n + 1) → ℝ) = fun i => c' * x i := by
        funext i; simp [Pi.smul_apply, smul_eq_mul]
      rw [heq]; exact h
    have hmain := hbound (fun x => Psi d n a α x) H M lam T hH hhom hMpos hsup hatt hlam hT
    have hepos : 0 < eNorm a := eNorm_pos ha
    have hcMpos : 0 < c * α ^ 2 * (eNorm a) ^ 2 := by positivity
    have hden2pos : 0 < T ^ (2 * d) * (c * α ^ 2 * (eNorm a) ^ 2) := by positivity
    have hden1pos : 0 < T ^ (2 * d) * M := by positivity
    have hdenle : T ^ (2 * d) * (c * α ^ 2 * (eNorm a) ^ 2) ≤ T ^ (2 * d) * M :=
      mul_le_mul_of_nonneg_left hcM (pow_nonneg hT.le _)
    have hAle : lam / (T ^ (2 * d) * M)
        ≤ c⁻¹ * (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) := by
      have h1 : lam / (T ^ (2 * d) * M)
          ≤ lam / (T ^ (2 * d) * (c * α ^ 2 * (eNorm a) ^ 2)) :=
        div_le_div_of_nonneg_left hlam hden2pos hdenle
      have h2 : lam / (T ^ (2 * d) * (c * α ^ 2 * (eNorm a) ^ 2))
          = c⁻¹ * (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) := by
        rw [show T ^ (2 * d) * (c * α ^ 2 * (eNorm a) ^ 2)
              = c * (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2)) by ring]
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hAnneg : 0 ≤ lam / (T ^ (2 * d) * M) := div_nonneg hlam (le_of_lt hden1pos)
    have hBneg : 0 ≤ lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2)) := by positivity
    have hKinv : 0 ≤ 1 / K := div_nonneg zero_le_one hKpos.le
    have hrpow : Real.rpow (lam / (T ^ (2 * d) * M)) (1 / K)
        ≤ Real.rpow c⁻¹ (1 / K) *
          Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / K) := by
      calc Real.rpow (lam / (T ^ (2 * d) * M)) (1 / K)
          ≤ Real.rpow (c⁻¹ * (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2)))) (1 / K) :=
            Real.rpow_le_rpow hAnneg hAle hKinv
        _ = Real.rpow c⁻¹ (1 / K) *
              Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / K) :=
            Real.mul_rpow (inv_nonneg.mpr hcpos.le) hBneg
    calc (MeasureTheory.volume {x : Fin (n + 1) → ℝ |
            rNorm x ≤ T ∧ |Psi d n a α x| ≤ lam}).toReal
        ≤ T ^ (n + 1) * C * Real.rpow (lam / (T ^ (2 * d) * M)) (1 / K) := hmain
      _ ≤ T ^ (n + 1) * C *
            (Real.rpow c⁻¹ (1 / K) *
              Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / K)) :=
          mul_le_mul_of_nonneg_left hrpow (mul_nonneg (pow_nonneg hT.le _) hCpos.le)
      _ = T ^ (n + 1) * (C * Real.rpow c⁻¹ (1 / K)) *
            Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / K) := by ring

end Work.HP.HP2
