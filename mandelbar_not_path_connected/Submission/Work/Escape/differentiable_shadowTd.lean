import Mathlib
import Submission.Work.Escape.Shadow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

/-!
# Differentiability of the holomorphic shadows `shadowTd d c k`

The shadow family is defined by the recursion `shadowTd d c 0 = id`,
`shadowTd d c 1 = fTd d c` and `shadowTd d c (n + 2) = shadowTd d c n ∘ pTd d c`, where
`fTd d c z = z^d + conj c` and `pTd d c z = (z^d + conj c)^d + c` are polynomials.  Since `id`,
`fTd` and `pTd` are holomorphic and the holomorphic functions are closed under composition, every
`shadowTd d c k` is holomorphic.  This is what makes the shadow usable as a holomorphic
representative of the (antiholomorphic) iterate `(Td d c)^[k]` when computing the Laplacian of
the Green function.
-/

/-- Every holomorphic shadow of an iterate of the antipolynomial is holomorphic.  The recursion
steps down by `2` in the index, so the induction is a strong induction on `k`. -/
theorem differentiable_shadowTd (d : ℕ) (c : ℂ) (k : ℕ) :
    Differentiable ℂ (shadowTd d c k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [shadowTd_zero]; exact differentiable_id
    | 1 => simpa using differentiable_fTd d c
    | n + 2 =>
      rw [shadowTd_add_two]
      exact Differentiable.comp (ih n (by omega)) (differentiable_pTd d c)

end Work.Escape
