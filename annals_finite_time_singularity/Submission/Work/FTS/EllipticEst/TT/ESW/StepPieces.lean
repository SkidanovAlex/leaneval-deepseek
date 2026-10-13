import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.TT.WeakDescent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.StepPieces`: the assembly of the induction step, with a cone that avoids `propHk_fts`

This module is a *verbatim copy* of `Work.FTS.EllipticEst.remov.EllEstUnif_step_of_pieces`
(`Submission/Work/FTS/EllipticEst/remov/EllEstUnif_step.lean`, lines 39--328), renamed into the
namespace `Work.FTS.EllipticEst.TT.ESW.Pieces`.

The copy is necessary because the original module's import cone contains
`remov.EllWeakPos_DzIter_one_shift` and `remov.A_top_slot_bound`, whose cones reach
`remov.propHk_fts`; and `propHk_fts` reaches `TT.propHk_core`, which *imports* the target of this
work, `TT.est_step_weak`.  Anything on the critical path of `TT.est_step_weak` must therefore
avoid `propHk_fts` entirely.

The statement is the one of the original: with the exact splitting of `HkSq` at level `k`, the
domination of the shifted level-`(k-1)` expression, the admissibility of the radially
differentiated data, the top-angular core and the elementary side conditions as hypotheses, the
induction step follows.  Only `remov.EllEstUnifStepAux` (the vocabulary `Qd`, `Tk`) is imported.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Step

/-- `√(x + y) ≤ √x + √y` for nonnegative `x, y`. -/
theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h4 : 0 ≤ Real.sqrt x + Real.sqrt y := by
    have h1 := Real.sqrt_nonneg x
    have h2 := Real.sqrt_nonneg y
    linarith
  have h5 : (Real.sqrt x + Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
      = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
    have h2 := Real.sq_sqrt hx
    have h3 := Real.sq_sqrt hy
    nlinarith only [h2, h3]
  have h6 : 0 ≤ 2 * (Real.sqrt x * Real.sqrt y) := by
    have h1 := Real.sqrt_nonneg x
    have h2 := Real.sqrt_nonneg y
    positivity
  have h7 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x + y)
  have h8 := Real.sqrt_nonneg (x + y)
  nlinarith only [h5, h6, h7, h8, h4]

/-- `√(x + y + z) ≤ √x + √y + √z` for nonnegative `x, y, z`. -/
theorem sqrt_add_add_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have h1 : Real.sqrt (x + y + z) ≤ Real.sqrt (x + y) + Real.sqrt z :=
    sqrt_add_le' (by linarith) hz
  have h2 : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := sqrt_add_le' hx hy
  linarith

end Step

open Work.FTS.EllipticEst.TT

/-- **The assembly of the induction step.**  Given the exact splitting of `HkSq` at level `k`
(with the top angular slot), the domination of the shifted level-`(k-1)` expression, the
admissibility of the radially differentiated data, the top-angular core, and the elementary
smoothness and congruence side conditions, the induction step `EllEstUnif (k-1) C → EllEstUnif k C`
follows. -/
theorem EllEstUnif_step_of_pieces
    (hstep : ∀ {k : ℕ}, 1 ≤ k → ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.remov.Step.Qd) → Work.Spaces.HkMem α k f →
      Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α (k - 1) f
        + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f) + Work.FTS.EllipticEst.remov.Step.Tk α k f)
    (hshift : ∀ {k : ℕ}, 1 ≤ k → ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.remov.Step.Qd) → Work.Spaces.HkMem α k f →
      Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k f)
    (hpos : ∀ {α : ℝ} {k : ℕ}, 2 ≤ k → ∀ {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
        (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ))
    (hcore : ∀ (D : ℝ), 0 < D → ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) ≤ C * Work.Spaces.HkNorm α k F)
    (hsmF : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.remov.Step.Qd)
    (hsmA : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) Work.FTS.EllipticEst.remov.Step.Qd)
    (hsmB : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.remov.Step.Qd)
    (hAz : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    (hBz : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
          = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :
    ∀ k : ℕ, 3 ≤ k → (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
      (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C := by
  intro k hk _ hk1
  obtain ⟨C₁, hC₁pos, hEst⟩ := hk1
  obtain ⟨Ck, hCkpos, hcorek⟩ := hcore (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
    (mul_pos hC₁pos (Real.sqrt_pos.mpr (by positivity))) k hk
  refine ⟨2 * C₁ * (1 + Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
    + Ck + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hFmem : Work.Spaces.HkMem α k F := h.memF
  have hA : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := h.memA
  have hB : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hsmF' := hsmF h
  have hsmA' := hsmA h
  have hsmB' := hsmB h
  -- the shifted data and the descent of the equation data
  have h₂ : Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := hpos (by omega) h
  have h₁ : Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1) F Ψ :=
    ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmF' hFmem,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmA' hA,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmB' hB,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) (Work.FTS.EllipticEst.TT.smoothOpen_diagHon hsmB') h.memZPth2⟩
  have e₁ := hEst α F Ψ hα hα4 h₁
  have e₂ := hEst α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 h₂
  -- the constants
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hDzFbound : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F)
      ≤ Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkNorm α k F := by
    have h1 : Work.Spaces.HkSq α (k - 1) (Work.Spaces.DzIter 1 F)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k F :=
      hshift (by omega) α F hsmF' hFmem
    have h2 : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F)
        ≤ Real.sqrt (((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k F) := by
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt h1
    refine le_trans h2 ?_
    rw [Real.sqrt_mul (by positivity), Work.Spaces.HkNorm]
  have hFmono : Work.Spaces.HkNorm α (k - 1) F ≤ Work.Spaces.HkNorm α k F := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (f := F) (by omega) hFmem)
  -- the two hypotheses of the core
  have hcore_hyp₁ : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
    calc α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ C₁ * Work.Spaces.HkNorm α (k - 1) F := e₁
      _ ≤ C₁ * Work.Spaces.HkNorm α k F :=
          mul_le_mul_of_nonneg_left hFmono (le_of_lt hC₁pos)
      _ ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
          have h0 : (0 : ℝ) ≤ C₁ * Work.Spaces.HkNorm α k F := by
            have hkF : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
            positivity
          have h1 := mul_le_mul_of_nonneg_left hsqrt1 h0
          nlinarith [h1]
  have hcore_hyp₂ : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
    calc α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C₁ * Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F) := e₂
      _ ≤ C₁ * (Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkNorm α k F) :=
          mul_le_mul_of_nonneg_left hDzFbound (le_of_lt hC₁pos)
      _ = (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by ring
  have htop := hcorek α F Ψ hα hα4 h hcore_hyp₁ hcore_hyp₂
  -- the exact splitting, for `A` and `B`, with the shifted fields identified
  have hAeq : Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = Work.Spaces.HkSq α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    Work.FTS.EllipticEst.HkSq_congr_open α (k - 1) (fun z θ hz hθ hlt => hAz h z θ hz hθ hlt)
  have hBeq : Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      = Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α (k - 1) (fun z θ hz hθ hlt => hBz h z θ hz hθ hlt)
  have hsplitA := hstep (k := k) (by omega) α
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hsmA' hA
  have hsplitB := hstep (k := k) (by omega) α (Work.Spaces.pthIter 2 Ψ) hsmB' hB
  rw [hAeq] at hsplitA
  rw [hBeq] at hsplitB
  -- square-root bookkeeping
  have hrootA : Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hsplitA) ?_
    have h1 : 0 ≤ Work.Spaces.HkSq α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.Spaces.HkSq_nonneg _ _ _
    have h2 : 0 ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
      have := Work.Spaces.HkSq_nonneg α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      positivity
    have h3 : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    refine le_trans (Step.sqrt_add_add_le h1 h2 h3) ?_
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), Work.Spaces.HkNorm]
    exact le_refl _
  have hrootB : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ)
      ≤ Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hsplitB) ?_
    have h1 : 0 ≤ Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkSq_nonneg _ _ _
    have h2 : 0 ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
      have := Work.Spaces.HkSq_nonneg α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      positivity
    have h3 : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ) := Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    refine le_trans (Step.sqrt_add_add_le h1 h2 h3) ?_
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), Work.Spaces.HkNorm]
    exact le_refl _
  -- final bookkeeping
  have hFk : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
  have hb1 : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F :=
    hcore_hyp₂
  have hcross : Real.sqrt ((k : ℝ) + 1) * α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ Real.sqrt ((k : ℝ) + 1) * (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
        * Work.Spaces.HkNorm α k F := by
    have h0 : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hb1 h0
    nlinarith [h1]
  have hαsq : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have htop' : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) ≤ Ck * Work.Spaces.HkNorm α k F := htop
  calc α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ)
      ≤ α ^ 2 * (Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + (Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))) := by
        nlinarith only [hrootA, hrootB, hαsq, le_refl (0:ℝ)]
    _ = (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ))
        + Real.sqrt ((k : ℝ) + 1) * α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))) := by ring
    _ ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F
        + Real.sqrt ((k : ℝ) + 1) * (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
          * Work.Spaces.HkNorm α k F
        + Ck * Work.Spaces.HkNorm α k F := by
        linarith [hcore_hyp₁, hcross, htop']
    _ ≤ (2 * C₁ * (1 + Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
        + Ck + 1) * Work.Spaces.HkNorm α k F := by
        set S := Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) with hS
        set x := Real.sqrt ((k : ℝ) + 1) with hx
        have hSnn : 0 ≤ S := Real.sqrt_nonneg _
        have hxnn : 0 ≤ x := Real.sqrt_nonneg _
        have hx1 : 1 ≤ x := by
          rw [hx]
          have h1k : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ k + 1)
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt h1k
        have hxS : x ≤ S := by
          rw [hx, hS]
          exact Real.sqrt_le_sqrt (by push_cast; nlinarith)
        have hprod1 : (1 - x) * S ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hSnn
        have hscal : C₁ * S + x * (C₁ * S) + Ck ≤ 2 * C₁ * (1 + x * S) + Ck + 1 := by
          nlinarith [hprod1, hC₁pos, hSnn, hxnn, hx1]
        have hmul := mul_le_mul_of_nonneg_right hscal hFk
        rw [hS, hx] at hmul ⊢
        nlinarith [hmul]

end Work.FTS.EllipticEst.TT.ESW.Pieces
