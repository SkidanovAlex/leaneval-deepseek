import Mathlib
import Submission.Commons.Analysis.Integral.phiFun_nonneg_of_le_eighth
import Submission.Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg
import Submission.Commons.Analysis.Integral.integrableOn_phiFun_mul_rpow

namespace Commons.Analysis.Integral

open MeasureTheory Set Real

theorem phiFun_v_neg_three_halves_tail_le {v0 : ℝ} (hv0 : 0 < v0) (hv : v0 ≤ 1 / 8) :
    ∫ v in Set.Ioi v0, (((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)) * v ^ (-(3 : ℝ) / 2))
      ≤ ∫ v in Set.Ioi (0:ℝ), (((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)) * v ^ (-(3 : ℝ) / 2)) := by
  set G : ℝ → ℝ := fun v => ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)) * v ^ (-(3 : ℝ) / 2) with hG
  change ∫ v in Set.Ioi v0, G v ≤ ∫ v in Set.Ioi (0:ℝ), G v
  -- integrability on `(0, ∞)`
  have hInt : IntegrableOn G (Set.Ioi (0:ℝ)) := by
    rw [hG]; exact integrableOn_phiFun_mul_rpow
  have hsubA : Set.Ioi v0 ⊆ Set.Ioi (0:ℝ) := fun x hx => hv0.trans hx
  have hsubB : Set.Ioc (0:ℝ) v0 ⊆ Set.Ioi (0:ℝ) := fun x hx => hx.1
  have hIntA : IntegrableOn G (Set.Ioi v0) := hInt.mono_set hsubA
  have hIntB : IntegrableOn G (Set.Ioc (0:ℝ) v0) := hInt.mono_set hsubB
  -- the union decomposition
  have hunion : Set.Ioi v0 ∪ Set.Ioc (0:ℝ) v0 = Set.Ioi (0:ℝ) := by
    ext x
    simp only [mem_union, mem_Ioi, mem_Ioc]
    constructor
    · rintro (h | ⟨h1, h2⟩) <;> linarith
    · intro hx
      rcases lt_or_ge v0 x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
  have hdisj : Disjoint (Set.Ioi v0) (Set.Ioc (0:ℝ) v0) := by
    rw [disjoint_left]
    intro x hx1 hx2
    rw [mem_Ioi] at hx1
    rw [mem_Ioc] at hx2
    linarith [hx1, hx2.2]
  have hsplit : (∫ v in Set.Ioi (0:ℝ), G v)
      = (∫ v in Set.Ioi v0, G v) + (∫ v in Set.Ioc (0:ℝ) v0, G v) := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hIntA hIntB]
  -- nonnegativity on `(0, v0]`
  have hBnn : 0 ≤ ∫ v in Set.Ioc (0:ℝ) v0, G v := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro v hvmem
    rw [mem_Ioc] at hvmem
    obtain ⟨hvpos, hvv0⟩ := hvmem
    have hvle : v ≤ 1 / 8 := le_trans hvv0 hv
    have hphi := phiFun_nonneg_of_le_eighth v hvpos.le hvle
    rw [hG]
    exact mul_nonneg hphi (Real.rpow_nonneg hvpos.le _)
  calc (∫ v in Set.Ioi v0, G v)
      ≤ (∫ v in Set.Ioi v0, G v) + (∫ v in Set.Ioc (0:ℝ) v0, G v) :=
        le_add_of_nonneg_right hBnn
    _ = ∫ v in Set.Ioi (0:ℝ), G v := hsplit.symm

end Commons.Analysis.Integral
