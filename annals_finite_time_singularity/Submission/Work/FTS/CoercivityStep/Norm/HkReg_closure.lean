/-
# `HkReg α k` is closed under `+`, `-` and scalar multiplication

`Work.FTS.CoercivityStep.HkReg α k f` is the linearity class of the `ℋ^k` inner product
(`Submission/Work/FTS/CoercivityStep/Defs.lean`):

  `HkReg α k f  :=  Work.Spaces.SmoothNbhd f ∧ Work.Spaces.HkMem α k f`.

Every constructive clause of `IsHkIP_fts` (additivity, homogeneity, congruence on the
open quadrant, Cauchy–Schwarz) is stated on this class, so the class must be shown to be
a *vector space*: it is closed under `f₁ + f₂`, under `fun z θ => c * f₁ z θ` and under
`f₁ - f₂`.  This file provides that closure, together with the two components separately
(the smoothness part is `ContDiffOn` bookkeeping; the `ℋ^k`-part is the substantive
statement, the pointwise subadditivity of the `H^k`-integrand plus the a.e. strong
measurability of that integrand for a `SmoothNbhd` function).

The `ℋ^k`-membership components are proved in the sibling modules
`Submission/Work/FTS/CoercivityStep/Norm/HkMem_add.lean` (`HkMem_add`) and
`.../HkMem_const_mul.lean` (`HkMem_const_mul`); negation and subtraction are derived
here from the scalar-multiplication case.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.CoercivityStep.Norm.HkMem_add
import Submission.Work.FTS.CoercivityStep.Norm.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

/-! ## The smoothness half: `SmoothNbhd` is closed under the vector-space operations

`SmoothNbhd f` is `ContDiffOn ℝ ⊤ (Function.uncurry f) nbhU`, and `Function.uncurry`
commutes with `+`, `-` and scalar multiplication definitionally, so these are the
corresponding `ContDiffOn` closure lemmas. -/

/-- `SmoothNbhd` is closed under subtraction. -/
theorem SmoothNbhd_sub {f₁ f₂ : ℝ → ℝ → ℝ} (h₁ : Work.Spaces.SmoothNbhd f₁)
    (h₂ : Work.Spaces.SmoothNbhd f₂) : Work.Spaces.SmoothNbhd (f₁ - f₂) :=
  h₁.sub h₂

/-- `SmoothNbhd` is closed under negation. -/
theorem SmoothNbhd_neg {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (fun z θ => -f z θ) :=
  h.neg

/-- `SmoothNbhd` is stable under multiplication by a scalar. -/
theorem SmoothNbhd_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (fun z θ => c * f z θ) :=
  h.const_smul c

/-! ## The `ℋ^k` half: negation and subtraction

`HkIntegrand α k (-f) = HkIntegrand α k f` holds unconditionally (the totalised `deriv`
is odd), so negation is the scalar case `c = -1` up to the identification
`(-1) * f z θ = -f z θ`. -/

/-- `ℋ^k` is closed under negation. -/
theorem HkMem_neg (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have h := HkMem_const_mul α k (-1) hf hmf
  have hfun : (fun z θ : ℝ => (-1 : ℝ) * f z θ) = (fun z θ : ℝ => -f z θ) := by
    funext z θ
    exact neg_one_mul (f z θ)
  rwa [hfun] at h

/-- `ℋ^k` is closed under subtraction. -/
theorem HkMem_sub (α : ℝ) (k : ℕ) {f₁ f₂ : ℝ → ℝ → ℝ} (hf₁ : Work.Spaces.SmoothNbhd f₁)
    (hf₂ : Work.Spaces.SmoothNbhd f₂) (hm₁ : Work.Spaces.HkMem α k f₁)
    (hm₂ : Work.Spaces.HkMem α k f₂) :
    Work.Spaces.HkMem α k (f₁ - f₂) :=
  HkMem_add α k hf₁ (SmoothNbhd_neg hf₂) hm₁ (HkMem_neg α k hf₂ hm₂)

/-! ## The closure of `HkReg` -/

/-- `HkReg α k` is closed under addition. -/
theorem HkReg_add {f₁ f₂ : ℝ → ℝ → ℝ} {α : ℝ} {k : ℕ}
    (h₁ : Work.FTS.CoercivityStep.HkReg α k f₁)
    (h₂ : Work.FTS.CoercivityStep.HkReg α k f₂) :
    Work.FTS.CoercivityStep.HkReg α k (f₁ + f₂) :=
  ⟨SmoothNbhd_add h₁.1 h₂.1, HkMem_add α k h₁.1 h₂.1 h₁.2 h₂.2⟩

/-- `HkReg α k` is closed under multiplication by a scalar. -/
theorem HkReg_smul (c : ℝ) {f : ℝ → ℝ → ℝ} {α : ℝ} {k : ℕ}
    (h : Work.FTS.CoercivityStep.HkReg α k f) :
    Work.FTS.CoercivityStep.HkReg α k (fun z θ => c * f z θ) :=
  ⟨SmoothNbhd_const_mul c h.1, HkMem_const_mul α k c h.1 h.2⟩

/-- `HkReg α k` is closed under negation. -/
theorem HkReg_neg {f : ℝ → ℝ → ℝ} {α : ℝ} {k : ℕ}
    (h : Work.FTS.CoercivityStep.HkReg α k f) :
    Work.FTS.CoercivityStep.HkReg α k (fun z θ => -f z θ) :=
  ⟨SmoothNbhd_neg h.1, HkMem_neg α k h.1 h.2⟩

/-- `HkReg α k` is closed under subtraction. -/
theorem HkReg_sub {f₁ f₂ : ℝ → ℝ → ℝ} {α : ℝ} {k : ℕ}
    (h₁ : Work.FTS.CoercivityStep.HkReg α k f₁)
    (h₂ : Work.FTS.CoercivityStep.HkReg α k f₂) :
    Work.FTS.CoercivityStep.HkReg α k (f₁ - f₂) :=
  ⟨SmoothNbhd_sub h₁.1 h₂.1, HkMem_sub α k h₁.1 h₂.1 h₁.2 h₂.2⟩

/-- **`HkReg α k` is closed under the vector-space operations.** -/
theorem HkReg_closure (α : ℝ) (k : ℕ) {f₁ f₂ : ℝ → ℝ → ℝ} (c : ℝ)
    (h₁ : Work.FTS.CoercivityStep.HkReg α k f₁) (h₂ : Work.FTS.CoercivityStep.HkReg α k f₂) :
    Work.FTS.CoercivityStep.HkReg α k (f₁ + f₂) ∧
      Work.FTS.CoercivityStep.HkReg α k (fun z θ => c * f₁ z θ) ∧
      Work.FTS.CoercivityStep.HkReg α k (f₁ - f₂) :=
  ⟨HkReg_add h₁ h₂, HkReg_smul c h₁, HkReg_sub h₁ h₂⟩

end Work.FTS.CoercivityStep.Norm
