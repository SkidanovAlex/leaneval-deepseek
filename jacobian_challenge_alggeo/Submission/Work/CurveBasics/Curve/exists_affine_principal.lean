import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.exists_affine_nbhd
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe v

variable {k : Type v} [Field k]

/-! ## Auxiliary facts about the order of vanishing at a place

`Curve.ordAt` is `Scheme.ord` evaluated at the point of a place.  Since the local ring at a
place is a discrete valuation ring, the order of vanishing is additive on products of nonzero
rational functions; from this we deduce the behaviour under (integer) powers, which is what
lets us realise a prescribed order of vanishing at a single place by a uniformizer power. -/

/-- The order of vanishing of the constant function `1` at any place is zero. -/
private theorem ordAt_one_eq_zero {C : Curve k} (Q : C.Place) :
    C.ordAt (1 : C.functionField) Q = 0 := by
  have h : C.ordAt ((1 : C.functionField) * 1) Q = C.ordAt 1 Q + C.ordAt 1 Q :=
    Scheme.ord_mul one_ne_zero one_ne_zero
  rw [mul_one] at h
  linarith

/-- The order of vanishing at a place is additive on products of nonzero rational functions. -/
private theorem ordAt_mul_of_ne_zero {C : Curve k} {f g : C.functionField} (hf : f ≠ 0)
    (hg : g ≠ 0) (Q : C.Place) : C.ordAt (f * g) Q = C.ordAt f Q + C.ordAt g Q :=
  Scheme.ord_mul hf hg

/-- The order of vanishing of the inverse of a nonzero rational function is the negative of its
order of vanishing. -/
private theorem ordAt_inv_of_ne_zero {C : Curve k} {f : C.functionField} (hf : f ≠ 0)
    (Q : C.Place) : C.ordAt f⁻¹ Q = -C.ordAt f Q := by
  have h := C.ordAt_mul_of_ne_zero (inv_ne_zero hf) hf Q
  rw [inv_mul_cancel₀ hf, ordAt_one_eq_zero] at h
  linarith

/-- The order of vanishing of a natural power of a nonzero rational function. -/
private theorem ordAt_pow_of_ne_zero {C : Curve k} {f : C.functionField} (hf : f ≠ 0) (n : ℕ)
    (Q : C.Place) : C.ordAt (f ^ n) Q = (n : ℤ) * C.ordAt f Q := by
  induction n with
  | zero => rw [pow_zero, ordAt_one_eq_zero, Nat.cast_zero]; ring
  | succ n ih =>
      rw [pow_succ, C.ordAt_mul_of_ne_zero (pow_ne_zero n hf) hf Q, ih]
      push_cast
      ring

/-- The order of vanishing of an integer power of a nonzero rational function. -/
private theorem ordAt_zpow_of_ne_zero {C : Curve k} {f : C.functionField} (hf : f ≠ 0) (n : ℤ)
    (Q : C.Place) : C.ordAt (f ^ n) Q = n * C.ordAt f Q := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hn
    rw [zpow_negSucc, C.ordAt_inv_of_ne_zero (pow_ne_zero (m + 1) hf) Q,
      ordAt_pow_of_ne_zero hf (m + 1) Q, Int.negSucc_eq]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zpow_natCast, ordAt_pow_of_ne_zero hf m Q]

/-- A uniformizer of the local ring at a place has order of vanishing one there. -/
private theorem ordAt_uniformizer_eq_one {C : Curve k} (Q : C.Place) :
    C.ordAt Q.uniformizer Q = 1 :=
  Place.ord_uniformizer Q

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem exists_affine_principal {k : Type u} [Field k] {C : Curve k} (D : Curve.Div C)
    (z : C.left) :
    ∃ (W : C.left.Opens) (t : C.functionField), AlgebraicGeometry.IsAffineOpen W ∧ z ∈ W ∧
      t ≠ 0 ∧ ∀ Q : Curve.Place C, Q.point ∈ W → C.ordAt t Q = -D Q := by
  classical
  -- Step 1: a nonzero rational function `t` whose order of vanishing at the places above `z`
  -- equals the coefficient of `-D` there.  If `z` is not a closed point there are no such
  -- places and `t = 1` works; otherwise `t` is a suitable power of a uniformizer at `z`.
  obtain ⟨t, ht_ne, ht_ord⟩ : ∃ t : C.functionField, t ≠ 0 ∧
      ∀ Q : C.Place, Q.point = z → C.ordAt t Q = -D Q := by
    by_cases hz : IsClosed ({z} : Set C.left)
    · let Q₀ : C.Place := ⟨z, hz⟩
      have h0ord : C.ordAt (0 : C.functionField) Q₀ = 0 := by
        change Scheme.ord (0 : C.functionField) Q₀.point = 0
        simp [Scheme.ord_zero]
      have hu : Q₀.uniformizer ≠ 0 := by
        intro h0
        have h1 : C.ordAt (0 : C.functionField) Q₀ = 1 := by
          simpa [h0] using Place.ord_uniformizer Q₀
        exact one_ne_zero (h1.symm.trans h0ord)
      refine ⟨Q₀.uniformizer ^ (-(D Q₀)), zpow_ne_zero _ hu, ?_⟩
      intro Q hQz
      have hQ : Q = Q₀ := Subtype.ext hQz
      rw [hQ]
      have hzpow : C.ordAt (Q₀.uniformizer ^ (-(D Q₀))) Q₀ = -(D Q₀) := by
        rw [ordAt_zpow_of_ne_zero hu (-(D Q₀)) Q₀, ordAt_uniformizer_eq_one Q₀, mul_one]
      exact hzpow
    · refine ⟨1, one_ne_zero, fun Q hQ => absurd (hQ ▸ Q.isClosed) hz⟩
  -- Step 2: `t` fails the required identity only on the finite support of `div t + D`, which
  -- avoids `z` by Step 1; take an affine open neighbourhood of `z` avoiding that support.
  have hz_avoid : ∀ Q ∈ (((C.div t + D).support : Finset C.Place) : Set C.Place),
      Q.point ≠ z := by
    intro Q hQmem hQz
    have h1 : (C.div t + D) Q = 0 := by
      have hd : C.div t Q = C.ordAt t Q := C.div_apply t Q
      rw [Finsupp.add_apply, hd, ht_ord Q hQz]
      ring
    exact (Finsupp.mem_support_iff.mp hQmem) h1
  obtain ⟨W, hWaff, hzW, hW⟩ :=
    BaseChange.exists_affine_nbhd_avoiding C
      (A := (((C.div t + D).support : Finset C.Place) : Set C.Place))
      (Finset.finite_toSet _) hz_avoid
  refine ⟨W, t, hWaff, hzW, ht_ne, ?_⟩
  intro Q hQW
  have hQnotin : Q ∉ (C.div t + D).support := hW Q hQW
  have hsum : (C.div t + D) Q = 0 := Finsupp.notMem_support_iff.mp hQnotin
  rw [Finsupp.add_apply, C.div_apply] at hsum
  linarith

end Work.CurveBasics.Curve
