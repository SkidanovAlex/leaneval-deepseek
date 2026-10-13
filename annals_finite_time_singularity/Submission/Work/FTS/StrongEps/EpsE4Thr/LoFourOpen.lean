/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/LoFourOpen.lean` — the `lo` clause of the level-four
coercivity, on the **open** class

`V_bounds.lo_four` proves, on the frozen class `RegQ α 4`,

  `clo · |f|²_{ℋ⁴} ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f`,

which is the comparability half of the level-four coercivity — and with it the *only* clause of
`UnifIPO` that the level-four barrier actually consumes
(`OpenBarrier.apriori_fourth_of_barrier_open` uses `UnifIPO.lo` and nothing else).

The frozen proof cannot be run along the route, because `RegQ` contains `SmoothQuad` (which the
projected mollified slice does not satisfy, `not_smoothQuad_Pz_Jeps`).  This file supplies the
open-class version `lo_four_open`, i.e. the same comparison on

  `RegQo α 4 f = SmoothOpen f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`,

which *is* available along the route (`OpenBarrier.coerAdmO_slice_JfamP`).

The proof is a transcription of the frozen one onto the open class, using the open-class
ingredients that the level-six chapter already provides
(`StrongPersist/IP6_lo_coeffs.lean`, the `_SO` family):

* the recursion step `lo_step_SO_min` (the open analogue of `V_bounds.lo_step`, with the
  `min 1 (min c₁ c₂)` bookkeeping for arbitrary *positive* coefficients), built here on
  `StrongPersist.HkSq_succ_le_SO` and `Transfer.HkMem_descent_Q0Sm`;
* the base `StrongPersist.H1IP_le_self_SO` (`|f|²_{ℋ¹} ≤ H1IP α f f` on `SmoothOpen ∧ HkMem α 1`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Assembly.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-! ## The recursion step on the open class -/

/-- **One step of the lower comparison, on the open class** (the `RegQo` analogue of
`V_bounds.lo_step`).  If the level-`n` pairing dominates `cst·|v|²_{ℋⁿ}` on the open class, then
the level-`n+1` pairing `HkIPStep c₁ c₂ IP` dominates `(cst·min 1 (min c₁ c₂))·|v|²_{ℋ^{n+1}}`
there. -/
theorem lo_step_SO_min {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcst : 0 < cst)
    (h : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      cst * Work.Spaces.HkSq α (n + 1) v ≤ IP v v) :
    ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 2) v →
      (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
        ≤ Work.Coercivity.HkIPStep c₁ c₂ IP v v := by
  intro v hs hm
  obtain ⟨hmv, hmd, hmz⟩ :=
    Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα (n + 1)
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 1 + 1)) hm
  have h0 := h v hs hmv
  have h1 := h (Work.Spaces.Dth v) hs.Dth hmd
  have h2 := h (Work.Spaces.Dz v) hs.Dz hmz
  have hsucc := Work.FTS.StrongPersist.HkSq_succ_le_SO (α := α) hα (n + 1) (by omega)
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 2)) hm
  have hA0 := Work.Spaces.HkSq_nonneg α (n + 1) v
  have hA1 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dth v)
  have hA2 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dz v)
  have hm1 : min 1 (min c₁ c₂) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (min c₁ c₂) ≤ c₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min 1 (min c₁ c₂) ≤ c₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcm : 0 ≤ cst * min 1 (min c₁ c₂) :=
    (mul_pos hcst (lt_min one_pos (lt_min hc₁ hc₂))).le
  have e0 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v ≤ IP v v := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        ≤ (cst * 1) * Work.Spaces.HkSq α (n + 1) v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hcst.le) hA0
      _ = cst * Work.Spaces.HkSq α (n + 1) v := by ring
      _ ≤ IP v v := h0
  have e1 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
      ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        ≤ (cst * c₁) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 hcst.le) hA1
      _ = c₁ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)) := by ring
      _ ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_left h1 hc₁.le
  have e2 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
      ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
        ≤ (cst * c₂) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm3 hcst.le) hA2
      _ = c₂ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)) := by ring
      _ ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_left h2 hc₂.le
  have hsum : (cst * min 1 (min c₁ c₂))
        * (Work.Spaces.HkSq α (n + 1) v + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
          + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v))
      = (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) := by
    ring
  rw [Work.Coercivity.HkIPStep]
  have hmain : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
      ≤ IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsucc hcm) ?_
    rw [hsum]; linarith [e0, e1, e2]
  exact hmain

/-! ## The level-four lower comparison -/

/-- **The `lo` clause of the level-four coercivity on the open class** — the open analogue of
`V_bounds.lo_four`: for arbitrary *positive* coefficients, the squared `ℋ⁴`-norm of a `RegQo α 4`
profile is dominated by the diagonal of `IP4`. -/
theorem lo_four_open {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ clo : ℝ, 0 < clo ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn,
      RegQo α 4 f →
        clo * Work.Spaces.HkSq α 4 f
          ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f := by
  refine ⟨((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''),
    mul_pos (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
      (lt_min one_pos (lt_min h₁' h₂'))) (lt_min one_pos (lt_min h₁'' h₂'')), ?_⟩
  intro α hα f hf
  have b1 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 1 g →
      (1 : ℝ) * Work.Spaces.HkSq α 1 g ≤ Work.Coercivity.H1IP α g g :=
    fun g hg hmg => by simpa using Work.FTS.StrongPersist.H1IP_le_self_SO hg hmg
  have b2 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 2 g →
      (1 * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α 2 g
        ≤ Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α) g g :=
    lo_step_SO_min (n := 0) hα h₁ h₂ one_pos b1
  have b3 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      ((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * Work.Spaces.HkSq α 3 g
        ≤ Work.Coercivity.HkIPStep c₁' c₂'
            (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)) g g :=
    lo_step_SO_min (n := 1) hα h₁' h₂'
      (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂))) b2
  have b4 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      (((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''))
          * Work.Spaces.HkSq α 4 g
        ≤ Work.Coercivity.HkIPStep c₁'' c₂''
            (Work.Coercivity.HkIPStep c₁' c₂'
              (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))) g g :=
    lo_step_SO_min (n := 2) hα h₁'' h₂''
      (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
        (lt_min one_pos (lt_min h₁' h₂'))) b3
  have h := b4 f hf.1 hf.2.1
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h

end Work.FTS.StrongEps.EpsE4Thr
