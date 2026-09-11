import ChallengeDeps
import Submission.LowerBounds
import Submission.Realize
import Submission.KOrder
import Submission.LowerFinal
import Submission.UpperAsm
import Submission.NBridge
import Mathlib.Analysis.Asymptotics.Lemmas

open EquiangularLinesFixedAngle
open Filter
open Asymptotics
open scoped RealInnerProductSpace

set_option autoImplicit false

namespace Submission

theorem theorem_1_2 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    let k := spectralRadiusOrder ((1 - α) / (2 * α))
    (k < ⊤ → ∀ᶠ d in atTop, N α d = ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
    (k = ⊤ → ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d) := by
  classical
  dsimp
  constructor
  · intro hklt
    have hkl : spectralRadiusOrder (lam α) < (⊤ : ℕ∞) := by
      simpa [lam] using hklt
    have hlb := eventually_lower_bound α hα.1 hα.2 hkl
    have hub := eventually_upper_finite α hα.1 hα.2 hkl
    refine (Filter.Eventually.and hlb hub).mono ?_
    intro d hd
    -- hd.1 : upperVal-form ≤ N, hd.2 : N ≤ upperVal k0 d  (with k0 := (spectralRadiusOrder (lam α)).toNat)
    exact (le_antisymm hd.1 hd.2).symm
  · intro hkt
    have hki : spectralRadiusOrder (lam α) = (⊤ : ℕ∞) := by
      simpa [lam] using hkt
    let e : ℕ → ℝ := fun d => (N α d : ℝ) - (d : ℝ)
    refine ⟨e, ?_, ?_⟩
    · -- e =o[atTop] Nat.cast
      have he_nonneg : ∀ d : ℕ, 0 ≤ e d := by
        intro d
        dsimp [e]
        exact sub_nonneg.mpr (by exact_mod_cast N_ge_d hα.1 hα.2 d)
      rw [isLittleO_iff]
      intro c hc
      have hc' : 0 < c / 2 := by positivity
      have hup := eventually_upper_infinite α hα.1 hα.2 hki (c / 2) hc'
      filter_upwards [hup] with d hd
      -- goal: ‖e d‖ ≤ c * ‖(d : ℝ)‖
      rw [Real.norm_eq_abs, abs_of_nonneg (he_nonneg d)]
      have hd' : e d ≤ (c / 2) * (d : ℝ) := by
        -- hd : (N α d : ℝ) ≤ (1 + c/2) * (d : ℝ) : N ≤ d + (c/2)d : e d = N − d ≤ (c/2)d
        dsimp [e] at *
        nlinarith
      -- need e d ≤ c * d: from e d ≤ (c/2) d ≤ c d since c/2 ≤ c (c>0): nlinarith
      have hd2 : (d : ℝ) = ‖(d : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact_mod_cast (Nat.zero_le d)
      rw [← hd2]
      nlinarith
    · intro d
      -- (N α d : ℝ) = (d : ℝ) + e d
      dsimp [e]
      ring
