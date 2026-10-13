/-
# Buildable copy of `Work.FTS.StrongEps.E4R3.Nblock6.aux.mul_WlInf6_HkSq`

The assigned file lives at
`Submission/Work/FTS/StrongEps/E4R3/Nblock6/aux/mul_WlInf6_HkSq.lean`, whose module name
`Submission.Work.FTS.StrongEps.E4R3.Nblock6.aux.mul_WlInf6_HkSq` contains the component `aux`,
a file name reserved on some operating systems (`CON`, `PRN`, **`AUX`**, `NUL`, …).  Lean 4.34
rejects such module names in `Lean.checkModuleNamePortability`, *before* elaboration, so that
module can never be built from sources and nothing can `import` it
(`lake build Submission.Work.FTS.StrongEps.E4R3.Nblock6.aux.mul_WlInf6_HkSq` fails with
`'aux' is a reserved file name on some operating systems`).

This file is the rehomed copy: it lives under `Nblock6/Auxiliary/`, so its module name is
portable and it can be built and imported, while declaring **the same** theorem name
`Work.FTS.StrongEps.E4R3.Nblock6.aux.mul_WlInf6_HkSq` (the namespace is unchanged).  Import
this module, not the `aux/` one.  The mathematical content is identical to the assigned file
(the four lines of imports and the body are the same).

## `mul_WlInf6_HkSq` — the `𝒲^{6,∞}`-priced product rule, in `HkSq` form

`Submission/Work/FTS/StrongPersist/H6Rows/Npair6SupAux/hknorm_mul_of_WlInf6_cd6.lean` proves
the product rule for a `C^∞` coefficient `f` on the open quadrant which is of class `𝒲^{6,∞}`:

  `HkMem α 6 (f·g) ∧ |f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} · |g|_{ℋ⁶}`.

The consumers of the level-six rows price things by the *square* `HkSq` of the `ℋ⁶`-norm
(rather than by the norm itself), and they only know a bound `|Y|_{𝒲^{6,∞}} ≤ CY·α` for the
coefficient.  This file provides that shape:

  `HkSq α 6 (Y·w) ≤ C · CY² · α · HkSq α 6 w`

for `α ∈ (0,1]`, `Y` smooth on the open quadrant and of class `𝒲^{6,∞}`, `w` smooth on the
open quadrant and of class `ℋ⁶`, and `CY ≥ 0` with `|Y|_{𝒲^{6,∞}} ≤ CY·α`.  The constant is
the square of the constant of `hknorm_mul_aux6` (hence universal, and explicitly
`(7 Cz + 49 Cm)·42701` in terms of the slot constants); the `α`-powers are
`(α^{-1/2})² = α^{-1}` and `α^{-1}·(CY·α)² = CY²·α`.

The price `α^{-1/2}` of the norm form is one of the two reasons for the hypothesis
`|Y|_{𝒲^{6,∞}} ≤ CY·α`: it cancels against the `𝒲^{6,∞}`-size, leaving the `α`-linear price
above.  (The other reason is that the raw product rule is only available for `α ≤ 1`; the
underlying slot lemmas `Cd6.zslot_le_winf6_cd6`, `Cd6.dzIter_w_mean_le6_cd6`,
`Cd6.mslot_le_winf6_cd6` all carry `0 < α → α ≤ 1 → …` explicitly, so no unspecified
`α₂`-threshold gets in the way.)

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

open scoped Real Topology

/-- **The elementary `HkSq` arithmetic of the product rule.**  If `S² = C` and
`b ≤ S·α^{-1/2}·W·N` with `b ≥ 0`, `W ≥ 0` and `W ≤ CY·α`, then `b² ≤ C·CY²·α·N²`.

This isolates the passage from the (square-root) norm bound to the squared norm bound: the
two `α`-powers `α^{-1/2}` and `α^{-1}` and the factor `(CY·α)²` are combined here. -/
private lemma sq_bound_of {C S α CY W N b : ℝ} (hC : 0 ≤ C) (hS : S ^ 2 = C) (hα : 0 < α)
    (hWnn : 0 ≤ W) (hW : W ≤ CY * α)
    (hb : b ≤ S * α ^ (-(1 / 2 : ℝ)) * W * N) (hb0 : 0 ≤ b) :
    b ^ 2 ≤ C * CY ^ 2 * α * N ^ 2 := by
  have hrpow : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
    rw [pow_two, ← Real.rpow_add hα, show (-(1 / 2 : ℝ)) + (-(1 / 2)) = -1 by norm_num,
      Real.rpow_neg_one]
  have heq : (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 = C * α⁻¹ * W ^ 2 * N ^ 2 := by
    rw [show (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2
        = S ^ 2 * (α ^ (-(1 / 2 : ℝ))) ^ 2 * W ^ 2 * N ^ 2 from by ring, hS, hrpow]
  have h1 : b ^ 2 ≤ (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have hW2 : W ^ 2 ≤ (CY * α) ^ 2 := pow_le_pow_left₀ hWnn hW 2
  have h2 : C * α⁻¹ * W ^ 2 * N ^ 2 ≤ C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 := by
    have h : 0 ≤ C * α⁻¹ := mul_nonneg hC (inv_nonneg.mpr hα.le)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW2 h) (sq_nonneg N)
  have h4 : C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 = C * CY ^ 2 * α * N ^ 2 := by field_simp
  calc b ^ 2 ≤ (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 := h1
    _ = C * α⁻¹ * W ^ 2 * N ^ 2 := heq
    _ ≤ C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 := h2
    _ = C * CY ^ 2 * α * N ^ 2 := h4

theorem mul_WlInf6_HkSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Y w : ℝ → ℝ → ℝ) (CY : ℝ),
    Work.FTS.EllipticEst.SmoothOpen Y → Work.Spaces.WlInfMem α 6 Y →
    Work.Spaces.WlInf α 6 Y ≤ CY * α → 0 ≤ CY →
    Work.FTS.EllipticEst.SmoothOpen w → Work.Spaces.HkMem α 6 w →
    Work.Spaces.HkSq α 6 (fun z θ => Y z θ * w z θ) ≤ C * CY ^ 2 * α * Work.Spaces.HkSq α 6 w := by
  -- the slot constants of the `C⁶` product rule
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨(7 * Cz + 49 * Cm) * 42701, by positivity, ?_⟩
  intro α hαIoc Y w CY hYsm hYW hYle hCY hwsm hwH
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- `SmoothOpen` is `C^∞` on the open quadrant, in particular `C⁶`
  have hYcd : ContDiffOn ℝ 6 (Function.uncurry Y) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hYsm 6
  have hwcd : ContDiffOn ℝ 6 (Function.uncurry w) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hwsm 6
  -- the norm form of the product rule
  obtain ⟨-, hnorm⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_aux6 (f := Y) (g := w)
      hα hα1 hYcd hYW hwcd hwH hCz hCm
      (fun i hi z θ hz hθ0 hθ1 => hZ α Y w hα hα1 hYcd hYW hwcd i hi z θ hz hθ0 hθ1)
      (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α Y w hα hα1 hYcd hYW hwcd hwH
        (fun d hd z' θ' hz' hθ0' hθ1' =>
          hCBmean α w d hα hα1 hwcd hwH hd z' θ' hz' hθ0' hθ1')
        I J hI hIJ z θ hz hθ0 hθ1)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 Y := Work.Spaces.WlInf_nonneg α 6 Y hYW
  have hmain := sq_bound_of (C := (7 * Cz + 49 * Cm) * 42701)
    (S := Real.sqrt ((7 * Cz + 49 * Cm) * 42701)) (α := α) (CY := CY)
    (W := Work.Spaces.WlInf α 6 Y) (N := Work.Spaces.HkNorm α 6 w)
    (b := Work.Spaces.HkNorm α 6 (fun z θ => Y z θ * w z θ))
    (by positivity) (Real.sq_sqrt (by positivity)) hα hWnn hYle hnorm
    (Work.Spaces.HkNorm_nonneg α 6 _)
  calc Work.Spaces.HkSq α 6 (fun z θ => Y z θ * w z θ)
      = (Work.Spaces.HkNorm α 6 (fun z θ => Y z θ * w z θ)) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)]
    _ ≤ ((7 * Cz + 49 * Cm) * 42701) * CY ^ 2 * α * (Work.Spaces.HkNorm α 6 w) ^ 2 := hmain
    _ = ((7 * Cz + 49 * Cm) * 42701) * CY ^ 2 * α * Work.Spaces.HkSq α 6 w := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]

end Work.FTS.StrongEps.E4R3.Nblock6.aux
