import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.FsFinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ZpError` — the `hEzero` slot in scalar form

The `hEzero` slot of `bogOpBoundFS_of_fsData` is

  `zpError (ell v μ) (a v) (M μ ρ).D.a … ≤ C₄·errBracket v R μ`,

where `zpError` (the zero-point error of `Work.BoseB6Est.fsZeroPoint_le`) is

  `zpError = (1/2)(2π)⁻³ℓ³ρ²a_scat√(ρa_scat³)·(latticeMeshErr(8π)n + zpRiemErr n K c₂)`
  `        + (1/2)·10¹⁰·lhyEps(a,R,ε_T,K_ℓ,s,d,μ)·ρ²a√(ρa³)ℓ³`.

All the *physical* prefactors `ℓ³`, `ρ²`, `a√(ρa³)` factor out of `zpError` and out of
`errBracket = μ²aℓ³√(dil)·(X² + (R/a)²√dil + X^{1/1615})`, so the comparison is
equivalent to the **scalar** inequality

  `zpScalar := (1/2)(2π)⁻³(latticeMeshErr(8π)n + zpRiemErr n K c₂) + (1/2)10¹⁰ lhyEps`
  `  ≤ C·(X² + (R/a)²√dil + X^{1/1615})`,

together with `ρ ≲ μ` (FS's close region: `ρ²√(ρa³) ≤ 4μ²√(μa³)`).

This module proves the factorization (`zpError_eq_zpScalar`) and the comparison
(`zpError_le_scalar`), so that `hEzero` reduces to `hscal` — a statement about the *mesh
index* `n` (FS's `(n+1) = ℓ√(ρ_za)`, hence `n+1 = K_ℓ√(ρ_z/μ) = O(1)`), the kernel's
`K.B`, `K.T`, `c₂` (through `zpRiemErr`) and the explicit `ε(μ,ρ_z)` (through `lhyEps`).
Every summand is a power of `X = (μa³)^{1/323}` or a logarithm, so the inequality lies
inside FS's §11 budget; it is the GATE/ESTIMATES node's arithmetic to finish.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The bracket's second factor: `X² + (R/a)²√(dil) + X^{1/1615}`
(`errBracket v R μ = μ²aℓ³√(dil)·errSlot v R μ`, definitionally). -/
abbrev errSlot (v : ℝ³ → ℝ) (R μ : ℝ) : ℝ :=
  fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ

/-- `errBracket` is `μ²aℓ³√(dil)` times the bracket's second factor. -/
theorem errBracket_eq_mul_errSlot (v : ℝ³ → ℝ) (R μ : ℝ) :
    errBracket v R μ = μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errSlot v R μ := rfl

/-- The scalar part of the zero-point error: everything in `zpError` except the physical
prefactors `ℓ³ρ²a√(ρa³)`. -/
def zpScalar (a R εT Kl s d μ : ℝ) (n : ℕ) (K : Work.BoseB6Est.FsKernel) (c₂ : ℝ) : ℝ :=
  (1 / 2) * ((2 * π) ^ 3)⁻¹ * (Work.BoseB6.latticeMeshErr (8 * π) n
      + Work.BoseB6Est.zpRiemErr n K c₂)
    + (1 / 2) * 10 ^ 10 * Work.BoseB6.lhyEps a R εT Kl s d μ

/-- **The factorization of `zpError`.**  With `a_scat = a` (which `FsMatch`/`RViewFS`
supply: both are `a v`), the zero-point error is the scalar part times `ℓ³ρ²a√(ρa³)`. -/
theorem zpError_eq_zpScalar (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ)
    (K : Work.BoseB6Est.FsKernel) (c₂ : ℝ) :
    zpError ℓ a a R εT Kl s d μ ρ n K c₂
      = ℓ ^ 3 * (ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3)) * zpScalar a R εT Kl s d μ n K c₂ := by
  rw [zpError, zpScalar]
  ring

/-- **The `hEzero` slot reduces to the scalar inequality `hscal`.**  The physical
prefactors cancel against `errBracket = μ²aℓ³√(dil)·errSlot`: it suffices that
`ρ²√(ρa³) ≤ 4μ²√(μa³)` (FS's close region gives `ρ ≤ (3/2)μ`) and that the scalar part
`(1/2)(2π)⁻³(latticeMeshErr + zpRiemErr) + (1/2)10¹⁰lhyEps` is `C·errSlot`. -/
theorem zpError_le_scalar (v : ℝ³ → ℝ) (R μ ρ : ℝ) (εT Kl s d : ℝ) (n : ℕ)
    (K : Work.BoseB6Est.FsKernel) (c₂ C : ℝ)
    (hav : 0 < a v) (hμ : 0 < μ) (hC : 0 ≤ C) (hℓ : 0 ≤ ell v μ) (hρ : 0 ≤ ρ)
    (hρμ : ρ ^ 2 * Real.sqrt (ρ * a v ^ 3) ≤ 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
    (hscal : zpScalar (a v) R εT Kl s d μ n K c₂ ≤ C * errSlot v R μ) :
    zpError (ell v μ) (a v) (a v) R εT Kl s d μ ρ n K c₂
      ≤ (4 * C) * errBracket v R μ := by
  rw [zpError_eq_zpScalar, errBracket_eq_mul_errSlot]
  have hℓ3 : 0 ≤ ell v μ ^ 3 := pow_nonneg hℓ 3
  have hX : 0 ≤ errSlot v R μ := by
    rw [errSlot]
    have h1 : (0 : ℝ) ≤ fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / a v) ^ 2 * Real.sqrt (dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h3 : (0 : ℝ) ≤ errExp v μ := by
      rw [errExp]
      exact Real.rpow_nonneg (by rw [dil]; positivity) _
    linarith
  have hfac : (0 : ℝ) ≤ ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3)) :=
    mul_nonneg hℓ3
      (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hav)) (Real.sqrt_nonneg _))
  calc ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3))
        * zpScalar (a v) R εT Kl s d μ n K c₂
      ≤ ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3)) * (C * errSlot v R μ) :=
        mul_le_mul_of_nonneg_left hscal hfac
    _ = C * (ell v μ ^ 3 * a v) * (ρ ^ 2 * Real.sqrt (ρ * a v ^ 3)) * errSlot v R μ := by ring
    _ ≤ C * (ell v μ ^ 3 * a v) * (4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
          * errSlot v R μ := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul_of_nonneg_left hρμ
          (mul_nonneg hC (mul_nonneg hℓ3 (le_of_lt hav)))
    _ = 4 * C * (μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errSlot v R μ) := by
        rw [ell3, dil]
        ring

end Work.BoseBogFS
