/-
# Measurability and boundedness of the window-parametrised §6 model symbol

`Work.KMTAreas.A7.lp_measurable_symMWin` and `Work.KMTAreas.A7.lp_exists_bound_symMWin`: the
(model) symbol `symMWin ρ P u N l₁ l₂ k₁ k₂` of the repaired window is jointly measurable and
globally bounded.  These are the window-parametrised versions of
`Work.KMTPlan.A6.measurable_symM` / `Work.KMTPlan.A6.exists_bound_symM`, needed to apply the
`coeff2` linearity `Work.KMTPlan.A6.coeff2_sub_of_meas_bdd` to the pair `(symC, symMWin)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedWinDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The model symbol `symMWin` is jointly measurable. -/
lemma lp_measurable_symMWin (ρ : ℝ) (P : Polynomial ℤ) (u N l₁ l₂ k₁ k₂ : ℕ) :
    Measurable (fun z : ℝ × ℝ => symMWin ρ P u N l₁ l₂ k₁ k₂ z.1 z.2) := by
  have hG : Measurable (fun w : (ℝ × ℝ) × ℝ =>
      Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) w.1.1 w.1.2
        * Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ w.2)) w.1.1
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ w.2)) w.1.2) := by
    have hA : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) w.1.1 w.1.2) :=
      (Work.KMTPlan.A6.measurable_symSeq2 _).comp measurable_fst
    have hB : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ w.2)) w.1.1) :=
      Work.KMTPlan.A6.measurable_symSeq_family3 (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ t))
        (fun j => Work.KMTPlan.A6.measurable_tmKer_varphiNt ρ l₁ N k₁ j)
    have hC : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        Work.KMTPlan.A6.symSeq
          (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ w.2)) w.1.2) :=
      Work.KMTPlan.A6.measurable_symSeq_family3'
        (fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        (fun j => Work.KMTPlan.A6.measurable_tmKer_varphitildeNt ρ P l₂ N k₂ j)
    exact (hA.mul hB).mul hC
  have hsingle : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t in Set.Ioc (1 / 2 : ℝ) 1,
      Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) z.1 z.2
        * Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2) :=
    StronglyMeasurable.integral_prod_right (f := fun z : ℝ × ℝ => fun t : ℝ =>
      Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) z.1 z.2
        * Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2)
      (ν := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) hG.stronglyMeasurable
  have hSm : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) z.1 z.2
        * Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hsingle
  simpa only [symMWin] using hSm.measurable

/-- The model symbol `symMWin` is bounded. -/
lemma lp_exists_bound_symMWin (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (u N l₁ l₂ k₁ k₂ : ℕ) :
    ∃ C : ℝ, ∀ x y : ℝ, ‖symMWin ρ P u N l₁ l₂ k₁ k₂ x y‖ ≤ C := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := Work.KMTPlan.A6.uniform_tmKer_varphiNt ρ l₁ N k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := Work.KMTPlan.A6.uniform_tmKer_varphitildeNt ρ P l₂ N k₂
  have hK : Summable (fun p : ℤ × ℤ => ‖arithKerMWin ρ P u l₁ l₂ p.1 p.2‖) :=
    Work.KMTPlan.A6.summable_arithKerMWin ρ P u l₁ l₂
  refine ⟨(∑' p : ℤ × ℤ, ‖arithKerMWin ρ P u l₁ l₂ p.1 p.2‖) * B₁ * B₂
    * |(1 : ℝ) - 1 / 2|, fun x y => ?_⟩
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  have hIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
  simp only [symMWin, norm_mul]
  exact mul_le_mul (mul_le_mul (Work.KMTPlan.A6.norm_symSeq2_le hK x y)
      (le_trans (Work.KMTPlan.A6.norm_symSeq_le (hB₁ t hIcc).1 x) (hB₁ t hIcc).2)
      (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _)))
    (le_trans (Work.KMTPlan.A6.norm_symSeq_le (hB₂ t hIcc).1 y) (hB₂ t hIcc).2)
    (norm_nonneg _) (mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _)) hB₁0)

end

end Work.KMTAreas.A7
