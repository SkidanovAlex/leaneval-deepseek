/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinIdents
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Basic facts about the Klein matrix `M(x)`

`kleinM a b x` is the `5 × 5` matrix `M_{i j} = c_{j - i} x_{i + j}` (`c = (0, a, b, -b, -a)`,
indices mod `5`) whose vector of `4 × 4` Pfaffians is `kleinP a b x`.  It is defined in
`Submission/Work/MotK/KleinData.lean` as a *bare function* `Fin 5 → Fin 5 → R`; `kleinMat` is the
same data as an element of `Matrix (Fin 5) (Fin 5) R`, so that Mathlib's matrix API applies.

This file records, for use by the census of the Crauder--Katz link (`Submission/Work/MotK`):

* `kleinMat_apply` — the two forms agree pointwise;
* `kleinMat_transpose` — `M(x)` is skew-symmetric;
* `kleinMat_diag` — `M(x)` has vanishing diagonal (so `M(x)` is *alternating*);
* `kleinMat_mulVec_kleinP` — `M(x) · p(x) = 0` in `Matrix.mulVec` form (`kleinM_mul_kleinP`);
* `exists_kleinP_ne_zero` — a nonzero Pfaffian vector has a nonzero coordinate.
-/

set_option autoImplicit false

open Matrix

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The Klein matrix `M(x)` as a Mathlib matrix (the definition `kleinM` is a bare function). -/
abbrev kleinMat (a b : R) (x : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.of (kleinM a b x)

@[simp] theorem kleinMat_apply (a b : R) (x : Fin 5 → R) (i j : Fin 5) :
    kleinMat a b x i j = kleinM a b x i j := rfl

/-- **`M(x)` is skew-symmetric.** -/
theorem kleinMat_transpose (a b : R) (x : Fin 5 → R) :
    (kleinMat a b x)ᵀ = -kleinMat a b x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kleinMat, Matrix.transpose_apply, kleinM, kleinM0, kleinM1, kleinM2, kleinM3, kleinM4]

/-- **`M(x)` has vanishing diagonal.** -/
theorem kleinMat_diag (a b : R) (x : Fin 5 → R) (i : Fin 5) : kleinMat a b x i i = 0 := by
  fin_cases i <;> simp [kleinMat, kleinM, kleinM0, kleinM1, kleinM2, kleinM3, kleinM4]

/-- **`M(x) · p(x) = 0`**, in `Matrix.mulVec` form. -/
theorem kleinMat_mulVec_kleinP (a b : R) (x : Fin 5 → R) :
    (kleinMat a b x) *ᵥ (kleinP a b x) = 0 := by
  funext i
  show ∑ j, kleinM a b x i j * kleinP a b x j = 0
  exact kleinM_mul_kleinP a b x i

/-- **A nonzero Pfaffian vector has a nonzero coordinate.** -/
theorem exists_kleinP_ne_zero (a b : R) (x : Fin 5 → R) (h : kleinP a b x ≠ 0) :
    ∃ k, kleinP a b x k ≠ 0 := by
  by_contra h'
  simp only [not_exists, not_not] at h'
  exact h (funext h')

end Work.MotK
