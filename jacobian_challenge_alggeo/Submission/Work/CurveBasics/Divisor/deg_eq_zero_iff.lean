import Mathlib
import Submission.Work.CurveBasics.Divisor
import Submission.Work.CurveBasics.Place.residueDegree_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# An effective divisor of degree zero is zero

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let
`D = ∑_Q n_Q [Q]` be an effective divisor on `C`, so that all coefficients `n_Q` are
nonnegative.  Its degree is `∑_Q n_Q [κ(Q) : k]`.  Since every place has positive
residue degree (`Place.residueDegree_pos`), every summand is nonnegative, and
`deg D = 0` forces every summand to vanish; as `[κ(Q) : k] ≠ 0` this gives `n_Q = 0`
for every `Q`, i.e. `D = 0`.  The converse is `Curve.deg_zero`.
-/

namespace Work.CurveBasics.Divisor

open Work.CurveBasics Work.CurveBasics.Curve in
theorem deg_eq_zero_iff {k : Type*} [Field k] {C : Curve k} {D : C.Div} (hD : Div.IsEffective D) :
    C.deg D = 0 ↔ D = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, Curve.deg_zero]⟩
  -- Unfold the degree as a sum over the support of `D`.
  have h' : D.sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) = 0 := h
  rw [Finsupp.sum] at h'
  -- Every summand is nonnegative: the coefficient is, and so is the residue degree.
  have hnonneg : ∀ Q ∈ D.support, 0 ≤ D Q * (C.hom.residueDegree Q.point : ℤ) := by
    intro Q _
    refine mul_nonneg (hD Q) ?_
    have hpos := Place.residueDegree_pos (C := C) Q
    exact_mod_cast le_of_lt hpos
  -- A sum of nonnegative integers vanishes only if every summand does.
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h'
  refine Finsupp.ext fun Q => ?_
  by_cases hQ : Q ∈ D.support
  · have hz := hall Q hQ
    have hne : (C.hom.residueDegree Q.point : ℤ) ≠ 0 := by
      have hpos := Place.residueDegree_pos (C := C) Q
      have hpos' : (0:ℤ) < (C.hom.residueDegree Q.point : ℤ) := by exact_mod_cast hpos
      omega
    exact (mul_eq_zero.mp hz).resolve_right hne
  · rwa [Finsupp.notMem_support_iff] at hQ

end Work.CurveBasics.Divisor
