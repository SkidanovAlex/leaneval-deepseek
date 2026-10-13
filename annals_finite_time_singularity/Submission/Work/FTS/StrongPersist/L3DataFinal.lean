/-
# `Work.FTS.StrongPersist.L3DataFinal` — S6's package `L3Data`, uniformly in the elliptic constant

Both analytic halves of the level-three package `L3Data` are proved:

* the **linear** half `L3Data.lin` — `L3_lin_mem` (`L3_lin_mem.lean`);
* the **nonlinear** half `L3Data.rhs` — `L3RhsPriced` (`L3RhsPriced.lean`), whose statement
  quantifies the elliptic perturbation constant `Ce` *inside* the `∀ α` and produces the
  constants `(α₂, C3, Cpow)` outside it.

Because the two halves are stated in that shape, the package is inhabited **uniformly in `Ce`**:

```
∃ α₂ C3 Cpow > 0, 0 ≤ Cpow ∧ ∀ Ce, L3Data α₂ Ce C3 Cpow.
```

This uniformity is what S6 needs: `Dbd.dbd_of_eq` takes `L3Data α₂ Ce C3 Cpow` for the *same*
`Ce` that occurs in the caller's elliptic context `Ell6Ctx α Ce Cs E Φs f Φ` (the constant of
the level-six perturbation package `EllPkgK α 6 Ce f (E f)`), and a caller cannot be asked to
change `Ce` to match an existentially produced one.

The proof is the merge of `L3DataExists.L3Data_exists_of` (min of the `α₂`'s, max of the `C3`'s)
run *after* the `∀ Ce` binder.  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3_lin_mem
import Submission.Work.FTS.StrongPersist.L3RhsPriced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)
open Work.Spaces (HkMem HkSq HkNorm)

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- **S6's package `L3Data`, uniformly in `Ce`.**  There are constants `α₂, C3 > 0`, `Cpow ≥ 0`
such that for *every* elliptic perturbation constant `Ce` the package `L3Data α₂ Ce C3 Cpow`
holds.  Consequently `Dbd.dbd_of_eq` applies with the caller's own `Ce`. -/
theorem L3Data_exists : ∃ α₂ C3 Cpow : ℝ, 0 < α₂ ∧ 0 < C3 ∧ 0 ≤ Cpow ∧
    ∀ Ce : ℝ, L3Data α₂ Ce C3 Cpow := by
  obtain ⟨α₂l, C3l, hα₂l, hC3l, hlin⟩ := L3_lin_mem
  obtain ⟨α₂r, C3r, Cpow, hα₂r, hC3r, hCpow, hrhs⟩ := L3RhsPriced
  refine ⟨min α₂l α₂r, max (max C3l C3r) 0, Cpow, lt_min hα₂l hα₂r, ?_, hCpow, ?_⟩
  · exact lt_of_lt_of_le hC3l (le_trans (le_max_left _ _) (le_max_left _ _))
  intro Ce
  refine ⟨⟨lt_of_lt_of_le hC3l (le_trans (le_max_left _ _) (le_max_left _ _)),
    lt_min hα₂l hα₂r, hCpow⟩, ?_, ?_⟩
  · intro α hα f hf
    have hαl : α ∈ Set.Ioc 0 α₂l := ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
    obtain ⟨hm, hb⟩ := hlin α hαl f hf
    refine ⟨hm, le_trans hb ?_⟩
    have hx : (0 : ℝ) ≤ (1 + Xn α f) ^ 4 :=
      pow_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 4 f]) 4
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  · intro α hα E Φs Φ f Cs μ lam M hell hf hM hμ hlam
    have hαr : α ∈ Set.Ioc 0 α₂r := ⟨hα.1, le_trans hα.2 (min_le_right _ _)⟩
    obtain ⟨hm, hb⟩ := hrhs α hαr Ce Cs E Φs Φ f μ lam M hell hf hM hμ hlam
    refine ⟨hm, le_trans hb ?_⟩
    have hB : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.1.le _
    have hC : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
    have hY : (0 : ℝ) ≤ (1 + HkNorm α 6 f) ^ 2 := by positivity
    have h1 : C3r * (1 + |Ce| + |Cs|) ^ 4 ≤ max C3l C3r * (1 + |Ce| + |Cs|) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have h1' : max C3l C3r * (1 + |Ce| + |Cs|) ^ 4
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h2 : C3r * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow)
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h1') hB
    have h3 : C3r * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4
        ≤ max (max C3l C3r) 0 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
      mul_le_mul_of_nonneg_right h2 hC
    exact mul_le_mul_of_nonneg_right h3 hY

end Work.FTS.StrongPersist
