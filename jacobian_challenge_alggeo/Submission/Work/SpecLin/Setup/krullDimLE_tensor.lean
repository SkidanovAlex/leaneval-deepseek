import Mathlib
import Submission.Work.CurveBasics.BaseChange.krullDimLE_tensor
import Submission.Work.SpecLin.Setup.ringKrullDim_polynomial_valuationRing
import Submission.Work.SpecLin.Setup.injective_eval2RingHom_tmul
import Submission.Work.SpecLin.Setup.isIntegral_eval2RingHom_tmul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u
open Polynomial
open scoped TensorProduct
set_option autoImplicit false

namespace Work.SpecLin.Setup

/-- **Noether normalisation for a finitely generated domain of dimension one.**

Let `A` be a finitely generated domain over a field `K` of Krull dimension exactly one.  Then there
is `t ∈ A` which is transcendental over `K` (i.e. `Polynomial.aeval t` is injective) and over whose
image every element of `A` is integral.

The proof uses `exists_integral_inj_algHom_of_fg` to obtain a Noether normalisation
`MvPolynomial (Fin s) K →ₐ[K] A` which is injective and integral; `s ≤ 1` because
`dim (MvPolynomial (Fin s) K) = s ≤ dim A ≤ 1`, and `s ≠ 0` because otherwise `A` would be integral
(hence of dimension `≤ dim K = 0`) over the field `K`, contradicting `hA`. -/
theorem exists_transcendental_isIntegral {K A : Type*} [Field K] [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A] (hA : ¬ Ring.KrullDimLE 0 A) :
    ∃ t : A, Function.Injective (Polynomial.aeval t : Polynomial K →ₐ[K] A) ∧
      ((Polynomial.aeval t : Polynomial K →ₐ[K] A)).toRingHom.IsIntegral := by
  classical
  obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hg_int⟩
  have hle : ringKrullDim (MvPolynomial (Fin s) K) ≤ ringKrullDim A :=
    Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral_of_injective_aux hg_inj
  have hdim : ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin s)]
    simp
  have hle1 : ringKrullDim A ≤ (1 : WithBot ℕ∞) := Ring.krullDimLE_iff.mp (by assumption)
  have hs_le : s ≤ 1 := by
    have h : (s : WithBot ℕ∞) ≤ 1 := hdim ▸ hle.trans hle1
    exact_mod_cast h
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hdim0 : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin 0)]
      simp
    have h2 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
      Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral_aux
    exact hA (Ring.krullDimLE_iff.mpr (h2.trans_eq hdim0))
  have hs1 : s = 1 := by omega
  subst hs1
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  let f : Polynomial K →ₐ[K] A := g.comp e.symm
  have hfinj : Function.Injective f := fun x y hxy => e.symm.injective (hg_inj hxy)
  letI : Algebra (Polynomial K) A := f.toRingHom.toAlgebra
  have hfint : f.toRingHom.IsIntegral := fun x =>
    IsIntegral.map_of_comp_eq (R := MvPolynomial (Fin 1) K) (S := A) (T := Polynomial K)
      (U := A) e.toRingHom (RingHom.id A) (by
        ext x <;> simp [f, RingHom.algebraMap_toAlgebra]) (hInt.isIntegral x)
  have ht : f = Polynomial.aeval (f Polynomial.X) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
  exact ⟨f Polynomial.X, ht ▸ hfinj, ht ▸ hfint⟩

/-- The dimension formula for a curve chart base changed to a valuation ring.

`A` is a finitely generated `K`-algebra of Krull dimension exactly one (in the application the
coordinate ring of an affine chart of a smooth curve), `R` is a valuation ring which is a
`K`-algebra, and `A ⊗[K] R` is a domain.  Then the Krull dimension of `A ⊗[K] R` is exactly one
more than that of `R`.

This is the commutative-algebra input of `Work.SpecLin.Setup.cruxPIT`, the last gap of the
affine-chart proof of specialisation of linear equivalence: the "vertical" half of the principal
ideal result for `(A ⊗[K] R)_N`.

Note `dim A = 1` must be assumed explicitly: `Ring.KrullDimLE 1 A` alone also allows `dim A = 0`
(e.g. `A = K`), for which the statement fails; the hypothesis `hA` below excludes this.

The proof: by `exists_transcendental_isIntegral` there is `t ∈ A`, transcendental over `K`, with `A`
integral over `K[t]`.  Hence `A ⊗[K] R` is integral over `Polynomial R` via `X ↦ t ⊗ 1`, and the map
`Polynomial R → A ⊗[K] R` is injective; a theorem of Seidenberg for valuation (Prüfer) rings gives
`dim R[X] = dim R + 1`. -/
theorem krullDimLE_tensor {K : Type u} [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)] {n : ℕ} :
    Ring.KrullDimLE (n + 1) (TensorProduct K A R) ↔ Ring.KrullDimLE n R := by
  classical
  obtain ⟨t, ht_inj, ht_int⟩ := exists_transcendental_isIntegral (K := K) (A := A) hA
  let φ : Polynomial R →+* TensorProduct K A R := Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeRight (A := A) (B := R)).toRingHom (t ⊗ₜ[K] (1 : R))
  have hφ_inj : Function.Injective φ := injective_eval2RingHom_tmul t ht_inj
  have hφ_int : φ.IsIntegral := isIntegral_eval2RingHom_tmul t ht_int
  letI : Algebra (Polynomial R) (TensorProduct K A R) := φ.toAlgebra
  haveI : Algebra.IsIntegral (Polynomial R) (TensorProduct K A R) := ⟨fun x => hφ_int x⟩
  have h_le : ringKrullDim (TensorProduct K A R) ≤ ringKrullDim (Polynomial R) :=
    Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral_aux
  have h_ge : ringKrullDim (Polynomial R) ≤ ringKrullDim (TensorProduct K A R) :=
    Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral_of_injective_aux hφ_inj
  have hdim : ringKrullDim (TensorProduct K A R) = ringKrullDim R + 1 := by
    rw [le_antisymm h_le h_ge, ringKrullDim_polynomial_valuationRing]
  have hcast : ∀ m : ℕ, ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) + 1 := by
    intro m
    push_cast
    rfl
  have key : ∀ m : ℕ, Ring.KrullDimLE (m + 1) (TensorProduct K A R) ↔ Ring.KrullDimLE m R := by
    intro m
    rw [Ring.krullDimLE_iff, Ring.krullDimLE_iff, hcast m, hdim]
    exact WithBot.add_le_add_iff_right' (α := ℕ) (c := (1 : WithBot (WithTop ℕ)))
      (by decide) (by decide)
  exact key n

end Work.SpecLin.Setup
