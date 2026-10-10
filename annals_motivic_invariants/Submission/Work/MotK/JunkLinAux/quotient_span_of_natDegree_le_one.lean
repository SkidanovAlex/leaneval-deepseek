import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.JunkLinAux

/-- The quotient of `R[X]` by a polynomial of `natDegree ≤ 1` whose linear coefficient is a unit
is `R`.

Route: `Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp` writes `p = C a * X + C b`; comparing
`coeff 1` gives `a = p.coeff 1`, which is a unit, so with `u : Rˣ`, `↑u = a` one has
`p = C ↑u * (X - C (-(↑u⁻¹ * b)))` (use `Units.mul_inv`).  Since `IsUnit (Polynomial.C ↑u)`
(`Polynomial.isUnit_C`), `Ideal.span_singleton_mul_left_unit` identifies `Ideal.span {p}` with
`Ideal.span {X - C (-(↑u⁻¹ * b))}`; conclude with `Ideal.quotientEquivAlgOfEq` and
`Polynomial.quotientSpanXSubCAlgEquiv`. -/
lemma quotient_span_of_natDegree_le_one {R : Type} [CommRing R] (p : Polynomial R)
    (hp : p.natDegree ≤ 1) (hu : IsUnit (p.coeff 1)) :
    Nonempty ((Polynomial R ⧸ Ideal.span {p}) ≃ₐ[R] R) := by
  obtain ⟨a, b, hp_eq0⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp
  have hp1 : p.coeff 1 = a := by rw [hp_eq0]; simp
  rw [hp1] at hu
  obtain ⟨u, hu_eq⟩ := hu
  -- `c` is the root of `p`, so that `p = C ↑u * (X - C c)`.
  let c : R := -(↑u⁻¹ * b)
  have hp_eq : p = Polynomial.C (↑u : R) * (Polynomial.X - Polynomial.C c) := by
    show p = Polynomial.C (↑u : R) * (Polynomial.X - Polynomial.C (-(↑u⁻¹ * b)))
    rw [hp_eq0, ← hu_eq, mul_sub]
    have hcancel : (↑u : R) * -(↑u⁻¹ * b) = -(b) := by
      rw [mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
    rw [← Polynomial.C_mul, hcancel, Polynomial.C_neg, sub_neg_eq_add]
  -- `p` is a unit multiple of `X - C c`, hence generates the same ideal.
  have hid : Ideal.span ({p} : Set (Polynomial R))
      = Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial R)) := by
    rw [hp_eq]
    rw [Ideal.span_singleton_mul_left_unit (Polynomial.isUnit_C.mpr u.isUnit)]
  let e1 : (Polynomial R ⧸ Ideal.span ({p} : Set (Polynomial R))) ≃ₐ[R]
      (Polynomial R ⧸ Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial R))) :=
    Ideal.quotientEquivAlgOfEq R hid
  let e2 : (Polynomial R ⧸ Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial R)))
      ≃ₐ[R] R :=
    Polynomial.quotientSpanXSubCAlgEquiv c
  exact ⟨e1.trans e2⟩

end Work.MotK.JunkLinAux
