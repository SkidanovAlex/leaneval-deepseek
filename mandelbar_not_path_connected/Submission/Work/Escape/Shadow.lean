import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Holomorphic shadows of the iterates of the antipolynomial

For the harmonicity of the Green function we need, for every iterate `f^[k]`, a *holomorphic*
function which has the same modulus as `f^[k]` (the Green function only sees moduli).  If `f` is
holomorphic, the iterates themselves qualify.  If `f = Td d c` is antiholomorphic, then the
square `f ∘ f` is the polynomial `pTd d c z = (z^d + conj c)^d + c`, and the iterates alternate
between `(f ∘ f)^[j]` and its composition with the holomorphic shadow `fTd d c = conj ∘ f`.

The main results about `shadowTd` (differentiability, equality of moduli, and smallness of the
ratios `shadowTd (k+1) z / (shadowTd k z)^d - 1` for large orbits) are proved in
`Submission/Work/Escape/shadowTd_*.lean` and used in `Submission/Work/Escape/GreenHarmonic.lean`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-! ## The holomorphic shadow of the antipolynomial -/

/-- The holomorphic shadow `conj ∘ (Td d c)` of the antipolynomial `Td d c`:
`fTd d c z = z^d + conj c`. -/
def fTd (d : ℕ) (c : ℂ) : ℂ → ℂ := fun z => z ^ d + (starRingEnd ℂ) c

/-- The square `Td d c ∘ Td d c` of the antipolynomial `Td d c`: the polynomial
`pTd d c z = (z^d + conj c)^d + c`. -/
def pTd (d : ℕ) (c : ℂ) : ℂ → ℂ := fun z => (z ^ d + (starRingEnd ℂ) c) ^ d + c

theorem fTd_apply (d : ℕ) (c z : ℂ) : fTd d c z = (starRingEnd ℂ) (Td d c z) := by
  simp [fTd, Td, map_add, map_pow]

theorem pTd_apply (d : ℕ) (c z : ℂ) : pTd d c z = Td d c (Td d c z) := by
  simp [pTd, Td, map_add, map_pow]

theorem fTd_eq (d : ℕ) (c : ℂ) : fTd d c = fun z => (starRingEnd ℂ) (Td d c z) := by
  funext z; exact fTd_apply d c z

theorem pTd_eq (d : ℕ) (c : ℂ) : pTd d c = Td d c ∘ Td d c := by
  funext z; exact pTd_apply d c z

theorem differentiable_fTd (d : ℕ) (c : ℂ) : Differentiable ℂ (fTd d c) := by
  have h : fTd d c = fun z : ℂ => z ^ d + (starRingEnd ℂ) c := rfl
  rw [h]
  fun_prop

theorem differentiable_pTd (d : ℕ) (c : ℂ) : Differentiable ℂ (pTd d c) := by
  have h : pTd d c = fun z : ℂ => (z ^ d + (starRingEnd ℂ) c) ^ d + c := rfl
  rw [h]
  fun_prop

/-! ## The shadow family -/

/-- Holomorphic shadows of the iterates of the antipolynomial `Td d c`:
`shadowTd d c 0 = id`, `shadowTd d c 1 = fTd d c`, and
`shadowTd d c (n+2) = shadowTd d c n ∘ pTd d c`.  Thus `shadowTd d c (2j) = (pTd d c)^[j]` and
`shadowTd d c (2j+1) = fTd d c ∘ (pTd d c)^[j]`, both holomorphic. -/
def shadowTd (d : ℕ) (c : ℂ) : ℕ → ℂ → ℂ
  | 0 => id
  | 1 => fTd d c
  | (n + 2) => shadowTd d c n ∘ pTd d c

@[simp] theorem shadowTd_zero (d : ℕ) (c : ℂ) : shadowTd d c 0 = id := rfl

@[simp] theorem shadowTd_one (d : ℕ) (c : ℂ) : shadowTd d c 1 = fTd d c := rfl

theorem shadowTd_add_two (d : ℕ) (c : ℂ) (n : ℕ) :
    shadowTd d c (n + 2) = shadowTd d c n ∘ pTd d c := rfl

theorem shadowTd_even (d : ℕ) (c : ℂ) (j : ℕ) :
    shadowTd d c (2 * j) = (pTd d c)^[j] := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [this, shadowTd_add_two, ih, Function.iterate_succ]

theorem shadowTd_odd (d : ℕ) (c : ℂ) (j : ℕ) :
    shadowTd d c (2 * j + 1) = fTd d c ∘ (pTd d c)^[j] := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
      rw [this, shadowTd_add_two, ih, Function.iterate_succ, Function.comp_assoc]

end Work.Escape
