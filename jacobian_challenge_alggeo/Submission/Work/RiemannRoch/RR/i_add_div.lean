/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance of the index of speciality under adding a principal divisor

For a curve `C` over a field `k`, a divisor `D` and a nonzero rational function `z`, the
index of speciality `i D = dim_k A_K/(K + A(D))` depends only on the divisor class of `D`:

`i (D + div z) = i D`.

This is RR4 of `Submission/Work/NOTES_LEAD_jacobian_RR.md`.  Componentwise multiplication of
adèles by `z` is a `k`-linear automorphism `mulAdele C z` of the adèle space (defined in
`Submission/Work/RiemannRoch/AdeleOps.lean`); it carries the lattice `A(D + div z)` onto
`A(D)` and the diagonal copy of `K` onto itself, hence induces an isomorphism
`H1 C (D + div z) ≃ₗ[k] H1 C D`, and the two quotients have the same `k`-dimension.
-/
import Mathlib
import Submission.Work.RiemannRoch.AdeleOps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Work.RiemannRoch.Curve

open Work.CurveBasics

noncomputable section

variable {k : Type u} [Field k]

/-- Multiplication by a nonzero rational function carries the lattice `A(D + div f)` onto
`A(D)`:  `(D + div f) + div f⁻¹ = D` on the level of orders, and multiplication by `f` is
bijective on the adèles (`AdeleOps.mulAdele_surjective`). -/
theorem map_mulAdele_Asub (C : Curve k) (D : C.Div) {f : C.functionField} (hf : f ≠ 0) :
    Submodule.map (mulAdele C f) (Asub C (D + C.div f)) = Asub C D := by
  rw [← comap_mulAdele_Asub C hf D, Submodule.map_comap_eq,
    LinearMap.range_eq_top.mpr (mulAdele_surjective C hf), top_inf_eq]

/-- Multiplication by a nonzero rational function carries `A(D + div f) + K` onto
`A(D) + K`. -/
theorem map_sup_diagK_mulAdele (C : Curve k) (D : C.Div) {f : C.functionField} (hf : f ≠ 0) :
    Submodule.map (mulAdele C f) (Asub C (D + C.div f) ⊔ diagK C) = Asub C D ⊔ diagK C := by
  rw [Submodule.map_sup, map_mulAdele_Asub C D hf, map_diagK_mulAdele C hf]

/-- Multiplication by a nonzero rational function, as a `k`-linear equivalence of the adèle
space (it is injective with inverse multiplication by `f⁻¹`). -/
def mulAdeleEquiv (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    Adeles C ≃ₗ[k] Adeles C :=
  LinearEquiv.ofBijective (mulAdele C f)
    ⟨mulAdele_injective C hf, mulAdele_surjective C hf⟩

@[simp]
theorem mulAdeleEquiv_apply (C : Curve k) {f : C.functionField} (hf : f ≠ 0) :
    ((mulAdeleEquiv C hf : Adeles C →ₗ[k] Adeles C) : Adeles C → Adeles C) = mulAdele C f := rfl

/-- **The index of speciality depends only on the divisor class.**  For `z ≠ 0`,
`mulAdele C z` maps `A(D + div z) + K` onto `A(D) + K`, so it induces an isomorphism
`H1 C (D + div z) ≃ₗ[k] H1 C D`. -/
theorem i_add_div_eq (C : Curve k) (D : C.Div) {z : C.functionField} (hz : z ≠ 0) :
    i C (D + C.div z) = i C D := by
  refine (Submodule.Quotient.equiv
    (Asub C (D + C.div z) ⊔ diagK C) (Asub C D ⊔ diagK C) (mulAdeleEquiv C hz) ?_).finrank_eq
  exact map_sup_diagK_mulAdele C D hz

end

end Work.RiemannRoch.Curve

namespace Work.RiemannRoch.RR

open Work.CurveBasics

theorem i_add_div {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (D : C.Div)
    {z : C.functionField} (hz : z ≠ 0) :
    Work.RiemannRoch.Curve.i C (D + C.div z) = Work.RiemannRoch.Curve.i C D :=
  Work.RiemannRoch.Curve.i_add_div_eq C D hz

end Work.RiemannRoch.RR
