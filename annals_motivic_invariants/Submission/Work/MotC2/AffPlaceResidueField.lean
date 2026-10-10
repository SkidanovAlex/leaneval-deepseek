import Mathlib
import Submission.Work.MotC2.AffPlaceSetup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

/-
GUIDANCE.  `S := affPlaceAt E a b ⊆ Func E = L(E)` is the localization of the affine coordinate
ring `A := Coord E` at the maximal ideal `I := affPlaceIdeal E a b = ⟨x - a, y - b⟩`.  The module
`Submission.Work.MotC2.AffPlaceSetup` provides `IsNonsingularPoint`, the instances
`IsLocalization.AtPrime ↥S I`, `IsLocalRing ↥S`, `IsNoetherianRing ↥S`, `IsMaximal I`, and the
lemmas `affPlaceAt_algebraMap_val` (`↑(algebraMap A ↥S r) = algebraMap A (Func E) r`) and
`affPlaceAt_algebraMap_algebraMap` (`algebraMap A ↥S (algebraMap L A c) = algebraMap L ↥S c`).

Route: let `hh : eval a (eval (C b) E.polynomial) = 0` be `h.nonsingular.1`.  Then
`CoordinateRing.quotientXYIdealEquiv (W' := E) hh : A ⧸ I ≃ₐ[L] L` and
`IsLocalization.AtPrime.equivQuotMaximalIdeal I ↥(affPlaceAt E a b) : A ⧸ I ≃+* ↥S ⧸ 𝔪` with
`simp` lemma `equivQuotMaximalIdeal_apply_mk (x : A) : equiv (mk I x) = mk 𝔪 (algebraMap A ↥S x)`.
Show by `funext` + `simp [equivQuotMaximalIdeal_apply_mk, affPlaceAt_algebraMap_algebraMap]` that
the map `c ↦ Ideal.Quotient.mk 𝔪 (algebraMap L ↥S c)` equals the composite
`(equivQuotMaximalIdeal I ↥S) ∘ (fun c => Ideal.Quotient.mk I (algebraMap L A c))` and conclude
with `RingEquiv.bijective` and the `L`-algebra equivalence `quotientXYIdealEquiv hh`
(the maps `L → A ⧸ I` and `L → L` coincide by `AlgEquiv.commutes`).
-/
theorem AffPlaceResidueField (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (a b : L) [h : Work.MotC2.IsNonsingularPoint E a b] :
    Function.Bijective (fun c : L =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b))
        (algebraMap L ↥(Work.MotC2.affPlaceAt E a b) c)) := by
  have hh : Polynomial.eval a
      (Polynomial.eval (Polynomial.C b) (WeierstrassCurve.Affine.polynomial E)) = 0 :=
    h.nonsingular.1
  -- The `L`-algebra equivalence `Coord E ⧸ affPlaceIdeal E a b ≃ₐ[L] L`.
  set φ : (Coord E ⧸ affPlaceIdeal E a b) ≃ₐ[L] L :=
    CoordinateRing.quotientXYIdealEquiv (W' := E) (x := a) (y := Polynomial.C b) hh
  -- The map `c ↦ mk I (algebraMap L A c)` is `φ.symm`, hence bijective.
  have hbij : Function.Bijective
      (fun c : L => Ideal.Quotient.mk (affPlaceIdeal E a b) (algebraMap L (Coord E) c)) := by
    have heq : (fun c : L =>
          Ideal.Quotient.mk (affPlaceIdeal E a b) (algebraMap L (Coord E) c)) = φ.symm := by
      funext c
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply]
      change φ (algebraMap L (Coord E ⧸ affPlaceIdeal E a b) c) = c
      rw [AlgEquiv.commutes]
      rfl
    rw [heq]
    exact φ.symm.bijective
  -- The target map is `equivQuotMaximalIdeal I ↥S` composed with the above.
  have hfun : (fun c : L =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(affPlaceAt E a b))
          (algebraMap L ↥(affPlaceAt E a b) c))
      = (fun x => IsLocalization.AtPrime.equivQuotMaximalIdeal (affPlaceIdeal E a b)
            ↥(affPlaceAt E a b) x) ∘
        (fun c : L => Ideal.Quotient.mk (affPlaceIdeal E a b) (algebraMap L (Coord E) c)) := by
    funext c
    simp only [Function.comp_apply,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
      affPlaceAt_algebraMap_algebraMap]
  rw [hfun]
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal (affPlaceIdeal E a b)
    ↥(affPlaceAt E a b)).bijective.comp hbij

end Work.MotC2
