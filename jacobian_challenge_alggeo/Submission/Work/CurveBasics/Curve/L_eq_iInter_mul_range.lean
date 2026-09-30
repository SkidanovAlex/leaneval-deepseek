import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.Curve.exists_affine_principal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

set_option linter.style.haveILetI false

section

universe u

variable {k : Type u} [Field k]

/-! ## Auxiliary facts about the order of vanishing at a place -/

/-- The order of vanishing at a place is additive on products of nonzero rational functions. -/
private theorem ordAt_mul {C : Curve k} {f g : C.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (Q : Place C) : C.ordAt (f * g) Q = C.ordAt f Q + C.ordAt g Q :=
  Scheme.ord_mul hf hg

/-- The order of vanishing of the constant function `1` at a place is zero. -/
private theorem ordAt_one {C : Curve k} (Q : Place C) :
    C.ordAt (1 : C.functionField) Q = 0 := by
  have h : C.ordAt ((1 : C.functionField) * 1) Q = C.ordAt 1 Q + C.ordAt 1 Q :=
    ordAt_mul one_ne_zero one_ne_zero Q
  rw [mul_one] at h
  linarith

/-- The order of vanishing of the inverse of a nonzero rational function is the negative of
its order of vanishing. -/
private theorem ordAt_inv {C : Curve k} {f : C.functionField} (hf : f ≠ 0) (Q : Place C) :
    C.ordAt f⁻¹ Q = -C.ordAt f Q := by
  have h : C.ordAt (f⁻¹ * f) Q = C.ordAt f⁻¹ Q + C.ordAt f Q :=
    ordAt_mul (inv_ne_zero hf) hf Q
  rw [inv_mul_cancel₀ hf, ordAt_one Q] at h
  linarith

/-- The order of vanishing of a quotient of nonzero rational functions. -/
private theorem ordAt_mul_inv {C : Curve k} {f t : C.functionField} (hf : f ≠ 0) (ht : t ≠ 0)
    (Q : Place C) : C.ordAt (f * t⁻¹) Q = C.ordAt f Q - C.ordAt t Q := by
  rw [ordAt_mul hf (inv_ne_zero ht) Q, ordAt_inv ht Q]
  ring

/-- Effectivity of `div h + D`, written with `ordAt`. -/
private theorem isEffective_div_add_iff_ordAt {C : Curve k} {D : Curve.Div C}
    {h : C.functionField} :
    (C.div h + D).IsEffective ↔ ∀ Q : Place C, -D Q ≤ C.ordAt h Q :=
  C.isEffective_div_add_iff

end

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/-- For a divisor `D` on a curve `C`, a family `U i` of nonempty affine opens covering `C` and
a family of local equations `t i` for `-D` on `U i`, the Riemann-Roch space `L(D)` is the
intersection over `i` of the `K(C)`-multiples of `t i` by functions regular on `U i`:
`L(D) = ⋂ i, t i · Γ(C, U i)`.

Here `t i ≠ 0` has order of vanishing `-D Q` at every place `Q` whose point lies in `U i`. -/
theorem L_eq_iInter_mul_range {k : Type u} [Field k] {C : Curve k} {ι : Type u}
    (D : Curve.Div C) (U : ι → C.left.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hne : ∀ i, Nonempty (U i))
    (hcov : ∀ z : C.left, ∃ i, z ∈ U i)
    (t : ι → C.functionField) (ht : ∀ i, t i ≠ 0)
    (htord : ∀ i, ∀ Q : Curve.Place C, Q.point ∈ U i → C.ordAt (t i) Q = -D Q) :
    (C.L D : Set C.functionField) = ⋂ i, {f : C.functionField |
      ∃ g ∈ (C.germToFunctionField (U i)).hom.range, f = t i * g} := by
  ext f
  constructor
  · -- `f ∈ L(D)`: on `U i`, `f` is `t i` times the regular function `f / t i`.
    intro hf
    rw [Set.mem_iInter]
    intro i
    haveI := hne i
    by_cases hf0 : f = 0
    · refine ⟨0, Subring.zero_mem _, ?_⟩
      rw [hf0, mul_zero]
    · have hD : (C.div f + D).IsEffective := by
        rcases (C.mem_L_iff).mp (show f ∈ C.L D from hf) with h | h
        · exact absurd h hf0
        · exact h
      have hle : ∀ Q : Curve.Place C, -D Q ≤ C.ordAt f Q :=
        isEffective_div_add_iff_ordAt.mp hD
      refine ⟨f * (t i)⁻¹, ?_, ?_⟩
      · refine (BaseChange.mem_range_germ_iff (U i) (hU i) (f * (t i)⁻¹)).mpr ?_
        intro Q hQ
        rw [ordAt_mul_inv hf0 (ht i) Q]
        have h1 := hle Q
        have h2 := htord i Q hQ
        linarith
      · rw [← mul_assoc, mul_comm (t i) f, mul_assoc, mul_inv_cancel₀ (ht i), mul_one]
  · -- Conversely, the local inequality at one place containing `Q` bounds `ord f` at `Q`.
    intro hf
    change f ∈ C.L D
    rw [C.mem_L_iff]
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    · refine Or.inr ?_
      rw [isEffective_div_add_iff_ordAt]
      intro Q
      obtain ⟨i, hQi⟩ := hcov Q.point
      haveI := hne i
      obtain ⟨g, hgmem, hfg⟩ := Set.mem_iInter.mp hf i
      have hreg : C.RegularOn (U i) g :=
        (BaseChange.mem_range_germ_iff (U i) (hU i) g).mp hgmem
      have hg0 : g ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hfg
        exact hf0 hfg
      have h1 : C.ordAt f Q = C.ordAt (t i) Q + C.ordAt g Q := by
        rw [hfg, ordAt_mul (ht i) hg0 Q]
      have h2 := htord i Q hQi
      have h3 := hreg Q hQi
      linarith

end Work.CurveBasics.Curve
