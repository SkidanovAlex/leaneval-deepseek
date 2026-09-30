/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The divisor cut out by an ideal of an affine open of a curve (area SY, `divOf`)

For a curve `C` over a field `F`, an affine open `V ⊆ C` and an ideal `J ≠ 0` of the affine ring
`B = Γ(C,V)`, the *divisor of `J`* is `Σ_z v_z(J) [z]`, where `z` runs over the closed points of
`V` and `v_z(J) = placeOrder J z hz` is the multiplicity of the maximal ideal `m_z` in the
factorization of `J` (Mathlib's Dedekind factorization, `Associates.count`).

The support is finite: the primes with `v_z(J) ≠ 0` are among the finitely many primes dividing
`J` (`Ideal.finite_factors`), and the map `z ↦ m_z` is injective
(`Work.SymQuot.DivOf.placeIdeal_injective`), the correspondence between places in `V` and
height-one primes of `B` being `Work.SymQuot.DivOf.heightOneSpectrum_equiv_place`.

This is the extraction step of the construction of `divOf`: the divisor of a point of `Symⁿ C`
is the divisor of the ideal `Work.SymQuot.DivOf.baseChangedIdeal`.
-/
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.placeIdeal_injective
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {F : Type u} [Field F]

/-- **The bijection between the places of `C` lying in the affine open `V` and the height-one
primes of `Γ(C,V)`**, mapping a place to its maximal ideal `placeIdeal`. -/
noncomputable def heightOneEquiv (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)] :
    {z : C.Place // z.point ∈ V} ≃ IsDedekindDomain.HeightOneSpectrum Γ(C.left, V) :=
  Classical.choose (heightOneSpectrum_equiv_place hV)

theorem heightOneEquiv_apply (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (z : {z : C.Place // z.point ∈ V}) :
    (heightOneEquiv C V hV z).asIdeal = placeIdeal C V z.1 z.2 :=
  Classical.choose_spec (heightOneSpectrum_equiv_place hV) z

/-- **The divisor cut out by an ideal** `J ≠ 0` of the affine ring `Γ(C,V)`:
`Σ_z (placeOrder J z hz) [z]`. -/
noncomputable def divisorOfIdeal (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (J : Ideal Γ(C.left, V)) : C.Div :=
  Finsupp.ofSupportFinite
    (fun z => if hz : z.point ∈ V then (placeOrder C V J z hz : ℤ) else 0)
    (by
      classical
      by_cases hJ : J = ⊥
      · subst hJ
        rw [placeOrder_bot_fun C V]
        rw [show (Function.support fun _ : C.Place => (0 : ℤ)) = ∅ from by
          ext z
          simp]
        exact Set.finite_empty
      · let T : Finset C.Place := (Ideal.finite_factors hJ).toFinset.image
          (fun v : IsDedekindDomain.HeightOneSpectrum
              ↥(C.left.presheaf.obj (Opposite.op V)) =>
            ((heightOneEquiv C V hV).symm v).1)
        refine Set.Finite.subset (hs := T.finite_toSet) ?_
        intro z hz
        rw [Function.mem_support] at hz
        by_cases hzV : z.point ∈ V
        · rw [dif_pos hzV] at hz
          set v : IsDedekindDomain.HeightOneSpectrum
              ↥(C.left.presheaf.obj (Opposite.op V)) :=
            heightOneEquiv C V hV ⟨z, hzV⟩ with hv
          have h1 : v.asIdeal = placeIdeal C V z hzV := by
            rw [hv]
            exact heightOneEquiv_apply C V hV ⟨z, hzV⟩
          have hcnt : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by
            rw [h1]
            exact_mod_cast hz
          obtain hdvd := (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hcnt
          refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, ?_, ?_⟩)
          · exact Finset.mem_coe.mp (by simpa using hdvd)
          · simp only [hv, Equiv.symm_apply_apply]
        · rw [dif_neg hzV] at hz
          exact absurd rfl hz)

@[simp]
theorem divisorOfIdeal_apply (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (J : Ideal Γ(C.left, V)) (z : C.Place) :
    divisorOfIdeal C V hV J z =
      if hz : z.point ∈ V then (placeOrder C V J z hz : ℤ) else 0 := by
  rw [divisorOfIdeal, Finsupp.ofSupportFinite_coe]

/-- The divisor cut out by an ideal is effective. -/
theorem divisorOfIdeal_isEffective (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (J : Ideal Γ(C.left, V)) : (divisorOfIdeal C V hV J).IsEffective := by
  intro z
  rw [divisorOfIdeal_apply]
  split
  · exact Int.natCast_nonneg _
  · exact le_rfl

end Work.SymQuot.DivOf
