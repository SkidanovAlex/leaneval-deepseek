import Mathlib
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.slabGlobalExtendPeriodic
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.derivRhoHNeg
import Submission.Work.RPB.B5.derivBoundOnPeriodic

/-!
# `Work.RPB.B5.extend_rho_per`

The radius family `ρh` of the chord chart on the closed slab `[0,1] × ℝ × (-1,1)` is extended to a
*global* `C⁸` function `ρe` which

* is `2π`-periodic in `t`,
* vanishes on `σ = 0`,
* agrees with `ρh` on the strip `|σ| < 1/2`,
* satisfies a linear bound `|ρh τ t σ| ≤ L |σ|` for `|σ| ≤ 1/4`,
* has strictly negative `σ`-derivative on `|σ| ≤ 1/4`.

The construction is the one already used for `Work.RPB.B5.exists_rho`:

* `slabExtendPeriodic` widens the closed slab `[0,1]` to the open slab `(-1,2)` (both seams at
  `τ = 0` and `τ = 1`), preserving `2π`-periodicity in `t`;
* `slabGlobalExtendPeriodic` glues the result to `0` outside a slightly smaller slab, giving a
  globally `C⁸`, still periodic, function which agrees with `ρh` on `|σ| < 1/2` (the cut-off is
  the identity there) and still vanishes at `σ = 0`;
* on `|σ| < 1/2` the global extension coincides with `ρh`, so `derivRhoHNeg` transfers the strict
  negativity of the `σ`-derivative, and the uniform `L` comes from
  `Work.RPB.B5.derivBoundOnPeriodic` (compactness on `[0,1] × [0,2π] × [-1/4,1/4]` plus
  periodicity) together with the mean value inequality
  `Convex.norm_image_sub_le_of_norm_deriv_le`.
-/

namespace Work.RPB.B5

open scoped ContDiff

theorem extend_rho_per (ρh : ℝ → ℝ → ℝ → ℝ)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1))
    (hh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (hhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 1,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0)
    (hhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 0, 0 < ρh τ t σ) :
    ∃ (ρe : ℝ → ℝ → ℝ → ℝ) (L : ℝ), 0 < L ∧
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρe z.1 z.2.1 z.2.2) ∧
      (∀ τ t σ, ρe τ (t + 2 * Real.pi) σ = ρe τ t σ) ∧
      (∀ τ t, ρe τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| < 1 / 2 → ρe τ t σ = ρh τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 → |ρh τ t σ| ≤ L * |σ|) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
        deriv (fun s : ℝ => ρe τ t s) σ < 0) := by
  classical
  -- (1) widen the closed slab `[0,1]` to the open slab `(-1,2)`, keeping periodicity
  obtain ⟨F1, hF1cd, hF1eq, hF1per⟩ :=
    slabExtendPeriodic ρh 8 1 (by norm_num) 1 (by norm_num) hh hhper
  have hF1_0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, F1 τ t 0 = 0 := by
    intro τ hτ t
    rw [hF1eq τ hτ t 0 (by norm_num)]
    exact hh0 τ hτ t
  have hF1cd' : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => F1 z.1 z.2.1 z.2.2)
      (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1) := by
    have h := hF1cd
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
    exact h
  -- (2) glue to a globally `C⁸`, periodic, function vanishing at `σ = 0`
  obtain ⟨ρe, hρecd, hρeper, hρe0, hρeeq⟩ :=
    slabGlobalExtendPeriodic F1 1 (by norm_num) hF1cd' hF1per hF1_0
  -- (3) agreement with `ρh` on the strip `|σ| < 1/2`
  have hρeρh : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| < 1 / 2 →
      ρe τ t σ = ρh τ t σ := by
    intro τ hτ t σ hσ
    rw [hρeeq τ hτ t σ hσ]
    refine hF1eq τ hτ t σ ?_
    simpa [Set.mem_Ioo, abs_lt] using (lt_of_le_of_lt hσ.le (by norm_num : (1:ℝ) / 2 < 1))
  -- (4) the `σ`-derivative of `ρh` is negative on `(-1,1)`
  have hneg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 1,
      deriv (fun s : ℝ => ρh τ t s) σ < 0 := derivRhoHNeg ρh hh hh0 hhmono hhpos
  -- (5) hence the `σ`-derivative of `ρe` is negative on `|σ| ≤ 1/4`
  have hderiv_neg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
      deriv (fun s : ℝ => ρe τ t s) σ < 0 := by
    intro τ hτ t σ hσ
    have hmem : σ ∈ Set.Ioo (-1 : ℝ) 1 :=
      abs_lt.mp (lt_of_le_of_lt hσ (by norm_num : (1:ℝ) / 4 < 1))
    have heq : deriv (fun s : ℝ => ρe τ t s) σ = deriv (fun s : ℝ => ρh τ t s) σ := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Metric.ball_mem_nhds σ (by norm_num : (0:ℝ) < 1 / 4)] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      refine hρeρh τ hτ t s ?_
      rw [abs_lt] at hs ⊢
      have h2 := abs_le.mp hσ
      constructor <;> linarith [hs.1, hs.2, h2.1, h2.2]
    rw [heq]
    exact hneg τ hτ t σ hmem
  -- (6) uniform bound for the `σ`-derivative of `ρe` on `|σ| ≤ 1/4`
  obtain ⟨M, hMpos, hMb⟩ := derivBoundOnPeriodic ρe hρecd hρeper hderiv_neg
  -- (7) the linear bound on `|σ| ≤ 1/4`, by the mean value inequality
  have hlip : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
      |ρe τ t σ| ≤ M * |σ| := by
    intro τ hτ t σ hσ
    have hρec1 : ContDiff ℝ 1 (fun u : ℝ => ρe τ t u) :=
      (hρecd.of_le (show ((1:ℕ) : WithTop ℕ∞) ≤ ((8:ℕ) : WithTop ℕ∞) by norm_num)).comp
        (by fun_prop : ContDiff ℝ 1 (fun u : ℝ => (τ, (t, u))))
    have hdiff0 : Differentiable ℝ (fun u : ℝ => ρe τ t u) := hρec1.differentiable (by norm_num)
    have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) σ, DifferentiableAt ℝ (fun u : ℝ => ρe τ t u) x :=
      fun x _ => hdiff0 x
    have hbd : ∀ x ∈ Set.uIcc (0:ℝ) σ, ‖deriv (fun u : ℝ => ρe τ t u) x‖ ≤ M := by
      intro x hx
      rw [Real.norm_eq_abs]
      refine hMb τ hτ t x ?_
      rw [abs_le]
      rcases le_total (0:ℝ) σ with hle | hle
      · rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1], by linarith [hx.2, (abs_le.mp hσ).2]⟩
      · rw [Set.uIcc_of_ge hle, Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1, (abs_le.mp hσ).1], by linarith [hx.2]⟩
    have hkey := (convex_uIcc (0:ℝ) σ).norm_image_sub_le_of_norm_deriv_le hdiff hbd
      Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [hρe0 τ t, Real.norm_eq_abs] using hkey
  refine ⟨ρe, M, hMpos, hρecd, hρeper, hρe0, hρeρh, ?_, hderiv_neg⟩
  intro τ hτ t σ hσ
  rw [← hρeρh τ hτ t σ (lt_of_le_of_lt hσ (by norm_num : (1:ℝ) / 4 < 1 / 2))]
  exact hlip τ hτ t σ hσ

end Work.RPB.B5
