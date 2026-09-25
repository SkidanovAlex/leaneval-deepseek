import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type

/-!
# Elementary facts about the Hardy--Littlewood maximal function `hlMax`

Small, self-contained lemmas about `Commons.Analysis.Maximal.hlMax` that several files need:
monotonicity, the `L^∞` bound, the "interval average is at most the maximal function at a point of
the interval" fact, and the decomposition of `hlMax ψ` through the truncation `ψ · 1_{ψ > λ}`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

/-- Monotonicity of the Hardy--Littlewood maximal function. -/
theorem hlMax_mono_pointwise {f g : ℝ → ENNReal} (h : ∀ x, f x ≤ g x) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax f x ≤ Commons.Analysis.Maximal.hlMax g x := by
  rw [Commons.Analysis.Maximal.hlMax, Commons.Analysis.Maximal.hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  exact le_iSup_of_le a (le_iSup_of_le b
    (le_iSup_of_le hab (mul_le_mul_right (lintegral_mono h) _)))

theorem ofReal_inv_mul_ofReal_le_one (r : ℝ) : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r ≤ 1 := by
  rcases le_total 0 r with h | h
  · rcases eq_or_ne r 0 with hr | hr
    · subst hr; simp
    · rw [← ENNReal.ofReal_mul (inv_nonneg.mpr h), inv_mul_cancel₀ hr]
      simp
  · rw [ENNReal.ofReal_eq_zero.mpr h, mul_zero]
    exact zero_le_one

/-- The maximal function of a function that is everywhere at most `c` is at most `c`. -/
theorem hlMax_le_const {f : ℝ → ENNReal} {c : ℝ≥0∞} (h : ∀ y, f y ≤ c) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax f x ≤ c := by
  rw [Commons.Analysis.Maximal.hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_
  have h2 : ∫⁻ y in Set.Icc a b, c = c * ENNReal.ofReal (b - a) := by
    rw [setLIntegral_const, Real.volume_Icc]
  have h1 : ∫⁻ y in Set.Icc a b, f y ≤ c * ENNReal.ofReal (b - a) := by
    rw [← h2]; exact lintegral_mono fun y => h y
  calc ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, f y
      ≤ ENNReal.ofReal (b - a)⁻¹ * (c * ENNReal.ofReal (b - a)) := mul_le_mul_right h1 _
    _ = c * (ENNReal.ofReal (b - a)⁻¹ * ENNReal.ofReal (b - a)) := by ring
    _ ≤ c * 1 := mul_le_mul_right (ofReal_inv_mul_ofReal_le_one (b - a)) c
    _ = c := mul_one c

/-- Splitting `hlMax ψ` into the part of `ψ` above the level `λ` plus the level `λ`. -/
theorem hlMax_le_hlMax_trunc_add {ψ : ℝ → ENNReal} (hψ : Measurable ψ) {lam : ℝ}
    (hlam : 0 < lam) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax ψ x ≤
      Commons.Analysis.Maximal.hlMax
        (fun y => if ENNReal.ofReal lam < ψ y then ψ y else 0) x + ENNReal.ofReal lam := by
  set ψt : ℝ → ENNReal := fun y => if ENNReal.ofReal lam < ψ y then ψ y else 0 with hψt
  have hψtmeas : Measurable ψt :=
    Measurable.ite (measurableSet_lt measurable_const hψ) hψ measurable_const
  have hpt : ∀ y, ψ y ≤ ψt y + ENNReal.ofReal lam := by
    intro y
    by_cases hy : ENNReal.ofReal lam < ψ y
    · simp only [hψt, hy, reduceIte]
      exact le_add_right le_rfl
    · simp only [hψt, hy, reduceIte, zero_add]
      exact le_of_not_gt hy
  rw [Commons.Analysis.Maximal.hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  have hsplit : ∫⁻ y in Set.Icc a b, (ψt y + ENNReal.ofReal lam)
      = (∫⁻ y in Set.Icc a b, ψt y) + ENNReal.ofReal lam * ENNReal.ofReal (b - a) := by
    rw [lintegral_add_left hψtmeas]
    congr 1
    rw [setLIntegral_const, Real.volume_Icc]
  have hb1 : ∫⁻ y in Set.Icc a b, ψ y ≤ ∫⁻ y in Set.Icc a b, (ψt y + ENNReal.ofReal lam) :=
    lintegral_mono fun y => hpt y
  have hfin : ENNReal.ofReal lam * ENNReal.ofReal (b - a) =
      ENNReal.ofReal lam * ENNReal.ofReal (b - a) := rfl
  calc ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ψ y
      ≤ ENNReal.ofReal (b - a)⁻¹ *
          ((∫⁻ y in Set.Icc a b, ψt y) + ENNReal.ofReal lam * ENNReal.ofReal (b - a)) := by
        rw [hsplit] at hb1; exact mul_le_mul_right hb1 _
    _ = ENNReal.ofReal (b - a)⁻¹ * (∫⁻ y in Set.Icc a b, ψt y)
          + ENNReal.ofReal (b - a)⁻¹ * (ENNReal.ofReal lam * ENNReal.ofReal (b - a)) := by
        rw [mul_add]
    _ ≤ Commons.Analysis.Maximal.hlMax ψt x + ENNReal.ofReal lam := by
        refine add_le_add (Commons.Analysis.Maximal.hlMax_le_of_mem ψt hab.1 hab.2) ?_
        rw [mul_comm (ENNReal.ofReal lam) (ENNReal.ofReal (b - a))]
        calc ENNReal.ofReal (b - a)⁻¹ * (ENNReal.ofReal (b - a) * ENNReal.ofReal lam)
            = (ENNReal.ofReal (b - a)⁻¹ * ENNReal.ofReal (b - a)) * ENNReal.ofReal lam := by ring
          _ ≤ 1 * ENNReal.ofReal lam := mul_le_mul' (ofReal_inv_mul_ofReal_le_one (b - a)) le_rfl
          _ = ENNReal.ofReal lam := one_mul _

end Work.BourgainPlan.Maximal
