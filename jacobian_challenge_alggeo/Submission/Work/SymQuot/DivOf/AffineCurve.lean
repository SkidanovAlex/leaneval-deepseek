/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places and ideals in an affine open of a curve (area SY, `divOf`)

For a curve `C` over a field `F` and an affine open `V ⊆ C`, the ring `B = Γ(C,V)` is a Dedekind
domain (`Work.SymQuot.DivOf.isDedekindDomain_sections`, proved downstream), whose maximal ideals
are the closed points of `V`.  This file provides the two definitions on which the extraction of
the divisor of a point of `Symⁿ C` from an ideal rests:

* `placeIdeal C V z hz` — the maximal ideal `m_z ⊆ Γ(C,V)` of the closed point `z ∈ V`, i.e. the
  kernel of the evaluation map `Γ(C,V) → κ(z)`;
* `idealOrder J v` — the order of vanishing of an ideal `J ⊆ Γ(C,V)` at a height-one prime `v`
  (Mathlib's `Associates.count`, so that `J = ⨅ v, v^(idealOrder J v)` by
  `Ideal.iInf_maxPowDividing_eq`).

The divisor of a point of `Symⁿ C` is then `Σ_z (idealOrder J z) [z]`, where `J` is the ideal of
regular functions vanishing on the divisor — see `Submission/Work/SymQuot/NOTES.md`.
-/
import Mathlib
import Submission.Work.CurveBasics.All

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

/-- **The maximal ideal of a closed point `z` of `C` inside an affine open `V ∋ z`**: the kernel
of the evaluation map `Γ(C,V) → κ(z)`, i.e. of the composite
`Γ(C,V) → O_{C,z} → κ(z)`. -/
noncomputable def placeIdeal (C : Curve F) (V : C.left.Opens) (z : C.Place)
    (hz : z.point ∈ V) : Ideal Γ(C.left, V) :=
  RingHom.ker ((IsLocalRing.residue (C.left.presheaf.stalk z.point)).comp
    ((C.left.presheaf.germ V z.point hz).hom))

/-- **The order of vanishing of an ideal at a place of the affine open**: the multiplicity of
the maximal ideal `m_z` in the factorization of `J`, i.e. Mathlib's `Associates.count`. -/
noncomputable def placeOrder (C : Curve F) (V : C.left.Opens) [IsDedekindDomain Γ(C.left, V)]
    (J : Ideal Γ(C.left, V)) (z : C.Place) (hz : z.point ∈ V) : ℕ :=
  (Associates.mk (placeIdeal C V z hz)).count (Associates.mk J).factors

/-- The order of the zero ideal is `0`. -/
@[simp]
theorem placeOrder_bot (C : Curve F) (V : C.left.Opens) [IsDedekindDomain Γ(C.left, V)]
    (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (⊥ : Ideal Γ(C.left, V)) z hz = 0 := by
  rw [placeOrder, show (Associates.mk (⊥ : Ideal Γ(C.left, V))) = 0 from Associates.mk_zero,
    Associates.factors_zero]
  simp only [Associates.count]
  split <;> simp [Associates.bcount]

/-- The function `z ↦ placeOrder ⊥ z` is identically zero. -/
theorem placeOrder_bot_fun (C : Curve F) (V : C.left.Opens) [IsDedekindDomain Γ(C.left, V)] :
    (fun z : C.Place =>
        if hz : z.point ∈ V then (placeOrder C V (⊥ : Ideal Γ(C.left, V)) z hz : ℤ) else 0)
      = fun _ => 0 := by
  funext z
  by_cases hzV : z.point ∈ V
  · rw [dif_pos hzV, placeOrder_bot]
    rfl
  · exact dif_neg hzV

/-- **The order of vanishing of an ideal at a height-one prime**: the exponent of the prime in
the factorization of the ideal, Mathlib's `Associates.count`.  By
`Ideal.iInf_maxPowDividing_eq` this recovers the ideal as the intersection of the powers of the
maximal ideals. -/
noncomputable def idealOrder (C : Curve F) (V : C.left.Opens) [IsDedekindDomain Γ(C.left, V)]
    (J : Ideal Γ(C.left, V)) (v : IsDedekindDomain.HeightOneSpectrum Γ(C.left, V)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk J).factors

end Work.SymQuot.DivOf

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {F : Type u} [Field F] (C : Curve F) (V : C.left.Opens)
variable [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))]

/-- The order of a power of a height-one prime at that prime is the exponent. -/
theorem idealOrder_pow (v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)))
    (a : ℕ) : idealOrder C V (v.asIdeal ^ a) v = a := by
  rw [idealOrder, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

/-- **The order of an ideal at a height-one prime, as a divisibility condition**:
`v` occurs in `J` to order at least `k` if and only if `J ⊆ v^k`. -/
theorem idealOrder_le_iff {J : Ideal ↥(C.left.presheaf.obj (Opposite.op V))} (hJ : J ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V))) (k : ℕ) :
    k ≤ idealOrder C V J v ↔ J ≤ v.asIdeal ^ k := by
  rw [idealOrder, ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

end Work.SymQuot.DivOf
