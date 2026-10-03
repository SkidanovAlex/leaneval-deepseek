import Mathlib

/-!
# The mass distribution (Frostman) principle for the Hausdorff dimension in `ℂ`

Self-contained version of the dimension-lowering estimate used by the `DIM` area: if a measure `μ`
satisfies `μ A ≤ C · (diam A)^d` for every set of diameter `≤ σ` (all `σ > 0`), then every set of
positive `μ`-measure has Hausdorff dimension at least `d`.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory Metric Set

noncomputable section

namespace Work.Dim

/-- **Mass distribution principle.** -/
theorem le_dimH_of_frostman {s : Set ℂ} {d : ℝ} (hd : 0 < d) (μ : MeasureTheory.Measure ℂ)
    (hμ : μ s ≠ 0)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (A : Set ℂ) (σ : ℝ), 0 < σ →
      (∀ a ∈ A, ∀ b ∈ A, dist a b ≤ σ) → μ A ≤ ENNReal.ofReal (C * σ ^ d)) :
    ENNReal.ofReal d ≤ dimH s := by
  obtain ⟨C, hC, hb⟩ := hbound
  -- singletons have measure zero
  have hsingle : ∀ x : ℂ, μ {x} = 0 := by
    intro x
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    set σ : ℝ := ((ε:ℝ) / C) ^ (1 / d) with hσdef
    have hσpos : 0 < σ := Real.rpow_pos_of_pos (div_pos hε0 hC) _
    have hσval : C * σ ^ d = (ε:ℝ) := by
      rw [hσdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (ε:ℝ) / C)]
      rw [one_div_mul_cancel hd.ne', Real.rpow_one]
      field_simp
    have h1 := hb {x} σ hσpos (by
      intro a ha b hb'
      rw [mem_singleton_iff] at ha hb'
      rw [ha, hb']
      simpa using hσpos.le)
    rw [hσval] at h1
    simpa using h1
  -- the Frostman bound in terms of `ediam`
  have hmain : ∀ A : Set ℂ, μ A ≤ ENNReal.ofReal C * (ediam A) ^ d := by
    intro A
    rcases eq_or_ne (ediam A) ⊤ with htop | htop
    · have h1 : ENNReal.ofReal C * (Metric.ediam A) ^ d = ⊤ := by
        rw [htop, ENNReal.top_rpow_of_pos hd,
          ENNReal.mul_top (by positivity : ENNReal.ofReal C ≠ 0)]
      rw [h1]
      exact le_top
    · have hdiam : ∀ a ∈ A, ∀ b ∈ A, dist a b ≤ diam A :=
        fun a ha b hb' => dist_le_diam_of_mem' htop ha hb'
      rcases eq_or_lt_of_le (diam_nonneg (s := A)) with h0 | hpos
      · have hsub : A.Subsingleton := fun a ha b hb' => by
          have h1 : dist a b ≤ 0 := by
            have h2 := hdiam a ha b hb'
            rwa [← h0] at h2
          exact dist_eq_zero.mp (le_antisymm h1 dist_nonneg)
        rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
        · simp
        · have hAeq : A = {x} := Set.ext fun y => ⟨fun hy => by
            rw [mem_singleton_iff]
            exact hsub hy hx, fun hy => by rw [mem_singleton_iff] at hy; rwa [hy]⟩
          rw [hAeq, hsingle x]
          exact bot_le
      · have h1 := hb A (diam A) hpos hdiam
        calc μ A ≤ ENNReal.ofReal (C * (diam A) ^ d) := h1
          _ = ENNReal.ofReal C * ENNReal.ofReal ((diam A) ^ d) := ENNReal.ofReal_mul hC.le
          _ = ENNReal.ofReal C * ENNReal.ofReal (diam A) ^ d := by
                rw [ENNReal.ofReal_rpow_of_nonneg diam_nonneg hd.le]
          _ = ENNReal.ofReal C * (ediam A) ^ d := by
                rw [show ENNReal.ofReal (diam A) = ediam A from by
                  rw [Metric.diam, ENNReal.ofReal_toReal htop]]
  -- the comparison with the Hausdorff measure
  set ν : MeasureTheory.Measure ℂ := (ENNReal.ofReal C)⁻¹ • μ with hνdef
  have hCne : ENNReal.ofReal C ≠ 0 :=
    (by positivity : (0:ENNReal) < ENNReal.ofReal C).ne'
  have hν : ν ≤ μH[d] := by
    refine MeasureTheory.Measure.le_hausdorffMeasure d ν 1 one_pos ?_
    intro A _
    rw [hνdef, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    have h1 := hmain A
    have h2 : (ENNReal.ofReal C)⁻¹ * ENNReal.ofReal C = 1 :=
      ENNReal.inv_mul_cancel hCne ENNReal.ofReal_ne_top
    calc (ENNReal.ofReal C)⁻¹ * μ A
        ≤ (ENNReal.ofReal C)⁻¹ * (ENNReal.ofReal C * (ediam A) ^ d) := by gcongr
      _ = (ediam A) ^ d := by rw [← mul_assoc, h2, one_mul]
  -- conclusion
  have hνs : ν s ≠ 0 := by
    rw [hνdef, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top) hμ
  have hne : μH[d] s ≠ 0 := fun h0 => hνs (le_antisymm (h0 ▸ hν s) bot_le)
  have hne' : μH[((d.toNNReal : NNReal) : ℝ)] s ≠ 0 := by
    rw [Real.coe_toNNReal d hd.le]
    exact hne
  exact le_dimH_of_hausdorffMeasure_ne_zero (s := s) hne'

end Work.Dim
