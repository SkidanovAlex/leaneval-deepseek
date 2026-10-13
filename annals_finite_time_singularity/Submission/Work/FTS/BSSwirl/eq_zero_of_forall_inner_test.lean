/-
# A vector field tested against every smooth compactly supported field vanishes

If `V : ℝ³ → ℝ³` is continuous and `∫ ⟪V x, Ψ x⟫ = 0` for every smooth compactly supported
`Ψ : ℝ³ → ℝ³`, then `V` vanishes identically.

The proof is the standard "soft bump" argument, arranged so that no change-of-variables formula is
needed.  Fix `x₀` and `c`; choose a smooth bump `f` with centre `x₀`, vanishing outside
`ball x₀ η` and equal to `1` at `x₀`, and test against `Ψ = f • c`.  The hypothesis gives
`∫ x, f x * ⟪V x, c⟫ = 0`.  Writing `⟪V x₀, c⟫ · ∫ x, f x = ∫ x, f x * ⟪V x₀, c⟫` and subtracting,
and using

* `|⟪V x, c⟫ - ⟪V x₀, c⟫| ≤ ‖V x - V x₀‖ ‖c‖ ≤ δ ‖c‖` on `support f` (continuity of `V`),
* `0 < ∫ x, f x` (a nonnegative continuous bump with a nonvanishing value),

we obtain `|⟪V x₀, c⟫| ≤ δ ‖c‖` for every `δ > 0`.  Letting `δ → 0` gives `⟪V x₀, c⟫ = 0`, and
choosing `c = V x₀` gives `V x₀ = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory Metric Set Function

theorem eq_zero_of_forall_inner_test {V : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hV : Continuous V)
    (h : ∀ Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3, (∀ n : ℕ, ContDiff ℝ n Ψ) →
      HasCompactSupport Ψ → ∫ x, inner ℝ (V x) (Ψ x) = 0) :
    ∀ x, V x = 0 := by
  intro x₀
  -- It suffices to prove `⟪V x₀, c⟫ = 0` for every `c`; take `c = V x₀` at the end.
  have key : ∀ c : R3, inner ℝ (V x₀) c = 0 := by
    intro c
    -- The bound `|⟪V x₀, c⟫| ≤ δ ‖c‖` for every `δ > 0`.
    have bound : ∀ δ : ℝ, 0 < δ → |inner ℝ (V x₀) c| ≤ δ * ‖c‖ := by
      intro δ hδ
      -- the radius of the bump, from the continuity of `V` at `x₀`
      obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hV.continuousAt δ hδ
      -- a smooth bump supported in `ball x₀ η`, equal to `1` at `x₀`
      let f : ContDiffBump x₀ := ⟨η / 2, η, by linarith, by linarith⟩
      have hfrIn : f.rIn = η / 2 := rfl
      have hfrOut : f.rOut = η := rfl
      have hfx₀ : f x₀ = 1 :=
        f.one_of_mem_closedBall (mem_closedBall_self (by rw [hfrIn]; linarith))
      -- test against `Ψ = f • c`
      have hΨ : ∫ x, inner ℝ (V x) (f x • c) = 0 :=
        h (fun x : R3 => f x • c) (fun n => f.contDiff.smul_const c)
          (f.hasCompactSupport.smul_right (f' := fun _ : R3 => c))
      have hint : ∫ x, f x * inner ℝ (V x) c = 0 := by
        rw [← hΨ]
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [real_inner_smul_right]
      -- the bump is continuous, integrable and has positive integral
      have hfcont : Continuous fun x : R3 => f x := f.continuous
      have hfint : Integrable (fun x : R3 => f x) :=
        hfcont.integrable_of_hasCompactSupport f.hasCompactSupport
      have hA : 0 < ∫ x, f x :=
        integral_pos_of_integrable_nonneg_nonzero (x := x₀) hfcont hfint (fun x => f.nonneg)
          (by rw [hfx₀]; norm_num)
      have hInt1 : Integrable (fun x : R3 => f x * inner ℝ (V x₀) c) := hfint.mul_const _
      have hInt2 : Integrable (fun x : R3 => f x * inner ℝ (V x) c) :=
        (hfcont.mul (hV.inner continuous_const)).integrable_of_hasCompactSupport
          (f.hasCompactSupport.mul_right (f' := fun x : R3 => inner ℝ (V x) c))
      -- the exact identity `⟪V x₀, c⟫ ∫ f = ∫ f (⟪V x₀, c⟫ - ⟪V x, c⟫)`
      have hkey : inner ℝ (V x₀) c * (∫ x, f x)
          = ∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c) := by
        have hsub : (∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c))
            = (∫ x, f x * inner ℝ (V x₀) c) - (∫ x, f x * inner ℝ (V x) c) := by
          rw [← integral_sub hInt1 hInt2]
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [mul_sub]
        rw [hsub, integral_mul_const (inner ℝ (V x₀) c) (fun x : R3 => f x), hint, sub_zero]
        ring
      have hbd : |inner ℝ (V x₀) c| * (∫ x, f x) ≤ δ * ‖c‖ * (∫ x, f x) := by
        calc
          |inner ℝ (V x₀) c| * (∫ x, f x)
              = |inner ℝ (V x₀) c * (∫ x, f x)| := by rw [abs_mul, abs_of_pos hA]
          _ = |∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c)| := by rw [hkey]
          _ ≤ ∫ x, |f x * (inner ℝ (V x₀) c - inner ℝ (V x) c)| :=
                abs_integral_le_integral_abs
          _ = ∫ x, f x * |inner ℝ (V x₀) c - inner ℝ (V x) c| := by
                refine integral_congr_ae ?_
                filter_upwards with x
                rw [abs_mul, abs_of_nonneg f.nonneg]
          _ ≤ ∫ x, f x * (δ * ‖c‖) := by
                refine integral_mono ?_ ?_ ?_
                · have habscont : Continuous
                      (fun x : R3 => |inner ℝ (V x₀) c - inner ℝ (V x) c|) :=
                    Continuous.abs <|
                      (continuous_const :
                          Continuous (fun _ : R3 => inner ℝ (V x₀) c)).sub
                        (hV.inner (continuous_const : Continuous (fun _ : R3 => c)))
                  exact (hfcont.mul habscont).integrable_of_hasCompactSupport
                    (f.hasCompactSupport.mul_right
                      (f' := fun x : R3 => |inner ℝ (V x₀) c - inner ℝ (V x) c|))
                · exact hfint.mul_const _
                · intro x
                  by_cases hfx : f x = 0
                  · simp [hfx]
                  · -- on the support of the bump, `V` is `δ`-close to `V x₀`
                    have hxball : dist x x₀ < η := by
                      have hx : x ∈ Function.support f := Function.mem_support.mpr hfx
                      rw [f.support_eq, hfrOut, mem_ball] at hx
                      exact hx
                    have hVbd : dist (V x) (V x₀) ≤ δ := le_of_lt (hη (x := x) hxball)
                    refine mul_le_mul_of_nonneg_left ?_ f.nonneg
                    calc |inner ℝ (V x₀) c - inner ℝ (V x) c|
                        = |inner ℝ (V x₀ - V x) c| := by rw [inner_sub_left]
                      _ ≤ ‖V x₀ - V x‖ * ‖c‖ := abs_real_inner_le_norm _ _
                      _ = dist (V x) (V x₀) * ‖c‖ := by rw [dist_eq_norm, norm_sub_rev]
                      _ ≤ δ * ‖c‖ := mul_le_mul_of_nonneg_right hVbd (norm_nonneg c)
          _ = δ * ‖c‖ * (∫ x, f x) := by
                rw [integral_mul_const (δ * ‖c‖) (fun x : R3 => f x)]
                ring
      exact le_of_mul_le_mul_right hbd hA
    -- `|⟪V x₀, c⟫| ≤ δ ‖c‖` for all `δ > 0`, so it vanishes
    have hz : |inner ℝ (V x₀) c| = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (abs_nonneg _)
      have h1 := bound (e / (‖c‖ + 1)) (by positivity)
      have h2 : e / (‖c‖ + 1) * ‖c‖ ≤ e := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖c‖ + 1)]
        nlinarith [norm_nonneg c]
      linarith
    exact abs_eq_zero.mp hz
  exact inner_self_eq_zero.mp (key (V x₀))

end Work.FTS.BSSwirl
