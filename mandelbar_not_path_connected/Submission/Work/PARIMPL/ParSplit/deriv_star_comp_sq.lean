/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# The chain rule for the conjugate-holomorphic square of a holomorphic map

For a holomorphic `h : ℂ → ℂ`, the map `x ↦ conj (h (conj (h x)))` is holomorphic and its
derivative is `h'(z) · conj (h' (conj (h z)))`.  This is the elementary chain-rule input behind the
"swap side" multiplier relation `ρ' = conj ρ` (see
`Submission/Work/PARIMPL/ParSplit/deriv_conj_of_swap.lean` and `NOTES.md`).

The proof writes `k := conj ∘ h ∘ conj` (`Mathlib`'s `deriv_conj_conj` computes
`k' w = conj (h' (conj w))`), observes that the target map is `k ∘ h`, and applies the chain rule
`deriv_comp`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

open scoped ComplexConjugate

/-- **The conjugate-square chain rule.**  For holomorphic `h`,
`deriv (conj ∘ h ∘ conj ∘ h) z = h'(z) * conj (h' (conj (h z)))`.  Equivalently, since the map
`x ↦ conj (h (conj (h x)))` is the composite of the holomorphic map `k = conj ∘ h ∘ conj` with `h`,
the derivative is `k'(h z) · h'(z) = conj (h' (conj (h z))) · h'(z)`. -/
theorem deriv_star_comp_sq {h : ℂ → ℂ} (hh : Differentiable ℂ h) (z : ℂ) :
    deriv (fun x => star (h (star (h x)))) z = deriv h z * star (deriv h (star (h z))) := by
  -- `k := conj ∘ h ∘ conj` is differentiable at `h z` because `h` is differentiable at `conj (h z)`.
  have hkd : DifferentiableAt ℂ (fun x => star (h (star x))) (h z) := by
    have h1 := (hh.differentiableAt (x := star (h z))).star_star
    rw [show star (star (h z)) = h z from star_star (h z)] at h1
    exact h1
  -- The chain rule on `k ∘ h`.
  have hcomp : deriv (fun x => star (h (star (h x)))) z
      = deriv (fun x => star (h (star x))) (h z) * deriv h z := by
    have heq : (fun x => star (h (star (h x)))) = (fun x => star (h (star x))) ∘ h := rfl
    rw [heq]
    exact deriv_comp z hkd (hh.differentiableAt (x := z))
  rw [hcomp]
  -- `deriv_conj_conj` gives `k' w = conj (h' (conj w))`.
  have hkderiv : deriv (fun x => star (h (star x))) (h z) = star (deriv h (star (h z))) := by
    have hfun : (fun x => star (h (star x))) = (starRingEnd ℂ) ∘ h ∘ (starRingEnd ℂ) := rfl
    rw [hfun, deriv_conj_conj]
    rfl
  rw [hkderiv, mul_comm]

end Work.PARIMPL.ParSplit
