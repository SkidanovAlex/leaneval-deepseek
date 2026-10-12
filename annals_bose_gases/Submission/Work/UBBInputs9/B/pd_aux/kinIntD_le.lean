import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.UBBInputs9.B.Basic
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The window-derivative integrand `kinIntD` is uniformly bounded in `u` and `x`.**

`kinIntD ℓ d u x = Σ_{k : Fin 3} (∂_k χ_{B(u)}(x))²` where the derivative is the one along the
kinetic direction `kcDir 1 0 k` of the lifted cutoff `y ↦ chiB ℓ d u (y 0)`.  The chain rule
turns it into `∂_k chiB ℓ d u` at `x 0`, the product rule for
`chiB ℓ d u = chiScale ℓ · (chiScale (ℓ*d) ∘ (· - (ℓ*d)•u))` splits it into two terms, and
each factor is bounded uniformly: `|chiScale s z| ≤ chiSup` and
`|fderiv ℝ (chiScale s) z (kcStdBasis k)| ≤ MD s k`, where `MD s k` bounds the continuous
compactly supported function `z ↦ fderiv ℝ (chiScale s) z (kcStdBasis k)`.

HINT.  `ChiDeriv.fderiv_chiB_apply` (`Submission.Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq`),
`Work.UBBInputs9.B.fderiv_liftX_apply` and `Work.UBBInputs9.B.projX1` (`Submission.Work.UBBInputs9.B.Basic`)
for the slot-projection chain rule, `Submission.BoseGases.abs_chiScale_le_chiSup` for the window
factors, and for the derivative bound: `(Submission.BoseGases.chiScale_hasCompactSupport hne).fderiv_apply ℝ (kcStdBasis k)`
applied to the continuous derivative
(`(Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any s).continuous_fderiv (by simp) |>.clm_apply continuous_const`),
then `.exists_bound_of_continuous`.  Take `K := Σ k, (chiSup * (MD1 k + MD2 k))^2` (or any such bound). -/
theorem kinIntD_le {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X 1),
      Work.UBBInputs9.B.kinIntD ℓ d u x ≤ K := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hldPos : 0 < ℓ * d := mul_pos hℓ hd
  have hldne : ℓ * d ≠ 0 := ne_of_gt hldPos
  -- ### Step 1: uniform bounds for the directional derivatives of the window factors
  have hbnd : ∀ s : ℝ, s ≠ 0 → ∀ k : Fin 3, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℝ³, |fderiv ℝ (chiScale s) z (kcStdBasis k)| ≤ M := by
    intro s hs k
    have hc : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale s) z (kcStdBasis k)) :=
      ((Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any s).continuous_fderiv
        (by simp)).clm_apply continuous_const
    obtain ⟨M, hM⟩ := (chiScale_hasCompactSupport hs).fderiv_apply ℝ (kcStdBasis k)
      |>.exists_bound_of_continuous hc
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), fun z => by
      rw [← Real.norm_eq_abs]; exact hM z⟩
  choose MD1 hMD1 using fun k => hbnd ℓ hℓne k
  choose MD2 hMD2 using fun k => hbnd (ℓ * d) hldne k
  refine ⟨∑ k : Fin 3, (chiSup * (MD1 k + MD2 k)) ^ 2,
    Finset.sum_nonneg (fun k _ => sq_nonneg _), ?_⟩
  intro u x
  -- ### Step 2: the chain rule for the lifted cutoff vanishes into the product rule
  unfold Work.UBBInputs9.B.kinIntD
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hder : fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)) x (kcDir 1 0 k)
      = fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)
          * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
        + chiScale ℓ (x 0)
          * fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k) := by
    rw [Work.UBBInputs9.B.fderiv_liftX_apply (chiB ℓ d u) x
      ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).differentiable (by simp) (x 0)) k]
    rw [Work.UBBInputs9.B.ChiDeriv.fderiv_chiB_apply ℓ d u (x 0) (kcStdBasis k)]
    ring
  -- ### Step 3: the uniform bound of the split expression
  have hA : |fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)| ≤ MD1 k := (hMD1 k).2 _
  have hB : |chiScale (ℓ * d) (x 0 - (ℓ * d) • u)| ≤ chiSup := abs_chiScale_le_chiSup _ _
  have hC : |chiScale ℓ (x 0)| ≤ chiSup := abs_chiScale_le_chiSup _ _
  have hD : |fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)| ≤ MD2 k :=
    (hMD2 k).2 _
  have hb : |fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)) x (kcDir 1 0 k)|
      ≤ chiSup * (MD1 k + MD2 k) := by
    rw [hder]
    calc |fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)
            * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
          + chiScale ℓ (x 0)
            * fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)|
        ≤ |fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)
              * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)|
          + |chiScale ℓ (x 0)
              * fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)| :=
          abs_add_le _ _
      _ = |fderiv ℝ (chiScale ℓ) (x 0) (kcStdBasis k)|
              * |chiScale (ℓ * d) (x 0 - (ℓ * d) • u)|
          + |chiScale ℓ (x 0)|
              * |fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)| := by
          rw [abs_mul, abs_mul]
      _ ≤ MD1 k * chiSup + chiSup * MD2 k :=
          add_le_add (mul_le_mul hA hB (abs_nonneg _) (hMD1 k).1)
            (mul_le_mul hC hD (abs_nonneg _) chiSup_pos.le)
      _ = chiSup * (MD1 k + MD2 k) := by ring
  -- ### Step 4: square both sides
  simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

end Work.UBBInputs9.B.pd_aux
