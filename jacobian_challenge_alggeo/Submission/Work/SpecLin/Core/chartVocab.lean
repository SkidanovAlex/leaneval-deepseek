/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The chart algebra of the relative chart `W ×_K Spec R` (vocabulary)

This module collects the *vocabulary* of the affine-chart analysis of the specialisation of linear
equivalence: the coordinate ring `B = Γ(C,W) ⊗_K R = chartTensor R W` of the relative chart, the
evaluation `evChart` at an `R`-point of the chart, the section prime `sectionPrime` (`B ⧸ I ≅ R`),
the prime `chartFibrePrime` of the generic point of the special fibre (`B ⧸ P ≅ Γ(C,W) ⊗_K κ`) and
the content normalisation `exists_smul_notMem_chartFibrePrime`.

It lives in a module of its own, *upstream* of
`Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart`, for the following reason: the proof
of the affine-chart statement is carried out in modules that refer to this vocabulary, and those
modules must not be downstream of the module that *states* the theorem.  The declarations keep
their original fully qualified names, so every module that imported them from
`Core/linEquiv_of_sections_of_chart.lean` still sees them unchanged.

This file also contains the `R`-model `X = C ×_K Spec R` of the curve and the two rewrites
`rPt_map_fractionRing`, `rPt_map_residueField` identifying the generic and the special fibre of an
`R`-point with `RPt.map` along `R → Frac R` resp. `R → κ`.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections
import Submission.Work.SpecLin.Setup.Basic
import Submission.Work.SpecLin.Core.module_free_chartTensor
import Submission.Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Core
section ChartAlgebra

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

/-- The coordinate ring `B = A ⊗_K R` of the relative chart `W ×_K Spec R`, where
`A = Γ(C, W)` is the coordinate ring of an affine chart of the curve. -/
noncomputable abbrev chartTensor (W : C.left.Opens) : Type u := Γ(C.left, W) ⊗[K] R

/-- The `K`-algebra map `B = A ⊗_K R → R` given by the `K`-algebra map `φ : A →_K R` ("evaluation
of the coordinate ring at the `R`-point of the chart"). -/
noncomputable def evChart (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    chartTensor (K := K) (C := C) R W →ₐ[K] R :=
  Algebra.TensorProduct.lift φ (AlgHom.id K R) (fun _ _ => Commute.all _ _)

@[simp]
theorem evChart_tmul (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R)
    (a : Γ(C.left, W)) (r : R) :
    evChart (K := K) (C := C) R W φ (a ⊗ₜ[K] r) = φ a * r := by
  simp [evChart]

theorem evChart_surjective (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    Function.Surjective (evChart (K := K) (C := C) R W φ) :=
  fun r => ⟨(1 : Γ(C.left, W)) ⊗ₜ[K] r, by simp⟩

/-- The prime `I_m = ker(B → R)` of the generic point of the section with coordinate ring
map `φ`; it is a prime of the generic fibre (`I_m ∩ R = 0`). -/
noncomputable def sectionPrime (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    Ideal (chartTensor (K := K) (C := C) R W) :=
  RingHom.ker (evChart (K := K) (C := C) R W φ)

/-- The ideal `P = m_R · (A ⊗_K R)` of the relative chart `B = A ⊗_K R`, where `A = Γ(C, W)`:
the prime of the generic point of the special fibre of the flat family `Spec B → Spec R`, so
that `V(P) = Spec (A ⊗_K κ)` is the affine chart of the special fibre `C_κ`. -/
noncomputable def chartFibrePrime (W : C.left.Opens) :
    Ideal (chartTensor (K := K) (C := C) R W) :=
  (IsLocalRing.maximalIdeal R).map
    (Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R))

/-- **The special fibre of the relative chart.**  The quotient `B ⧸ P` of the coordinate ring
of the relative chart by `P = m_R·B` is the tensor product of `A = Γ(C, W)` with the residue
field `κ = R/m_R`, i.e. the coordinate ring of the chart `W_κ` of the special fibre. -/
noncomputable def chartFibreQuotEquiv (W : C.left.Opens) :
    (chartTensor (K := K) (C := C) R W ⧸ chartFibrePrime (K := K) (C := C) R W) ≃+*
      (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K R Γ(C.left, W)
    (IsLocalRing.maximalIdeal R)).symm.toRingEquiv

/-- The quotient `B ⧸ P` of the relative chart by the fibre prime is a domain (the coordinate
ring of the chart `W_κ` of the integral curve `C_κ`). -/
theorem isDomain_chartFibreQuot (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    IsDomain (chartTensor (K := K) (C := C) R W ⧸
      chartFibrePrime (K := K) (C := C) R W) := by
  haveI : IsDomain (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R) :=
    Work.CurveBasics.Curve.isDomain_tensor_sections C hW (IsLocalRing.ResidueField R)
  exact Function.Injective.isDomain (chartFibreQuotEquiv (K := K) (C := C) R W)
    (RingEquiv.injective _)

/-- The fibre prime `P` is prime: its quotient is the coordinate ring of the chart `W_κ` of the
curve `C_κ`, which is integral. -/
theorem isPrime_chartFibrePrime (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    (chartFibrePrime (K := K) (C := C) R W).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime (I := chartFibrePrime (K := K) (C := C) R W)).mp
    (isDomain_chartFibreQuot (K := K) (C := C) R W hW)

/-- The relative chart `B = A ⊗_K R` is a domain: `A = Γ(C, W)` is and `C/K` is geometrically
integral. -/
theorem isDomain_chartTensor (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    IsDomain (chartTensor (K := K) (C := C) R W) :=
  Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing
    (Work.CurveBasics.Curve.isDomain_tensor_sections C hW (FractionRing R))

/-- **The section prime.**  The kernel `I = ker (B →_K R)` of the evaluation of the relative
chart at the `R`-point given by `φ` has quotient `R`: the section is a *flat* closed
subscheme `Spec R ⊆ Spec B` of the relative chart. -/
noncomputable def sectionPrimeQuotEquiv (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    chartTensor (K := K) (C := C) R W ⧸ sectionPrime (K := K) (C := C) R W φ ≃+* R :=
  (evChart (K := K) (C := C) R W φ).toRingHom.quotientKerEquivOfSurjective
    (evChart_surjective (K := K) (C := C) R W φ)

/-- The section prime is prime. -/
theorem isPrime_sectionPrime (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    (sectionPrime (K := K) (C := C) R W φ).IsPrime :=
  RingHom.ker_isPrime _

theorem isDomain_sectionPrimeQuot (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    IsDomain (chartTensor (K := K) (C := C) R W ⧸ sectionPrime (K := K) (C := C) R W φ) :=
  Function.Injective.isDomain (sectionPrimeQuotEquiv (K := K) (C := C) R W φ)
    (RingEquiv.injective _)



/-- **Content normalisation for the relative chart** (step 2 of the proof plan).  Every element
of `B = A ⊗_K R` is `c • b'` with `c ∈ R` and `b' ∉ P = m_R·B`: an element of `B` is a
coordinate in some `R`-basis multiplied by a scalar of `R`, and dividing by the "content" makes
it invertible modulo `P`.  This is
`Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map` applied to the relative chart, using
that `B` is free over `R` (`Work.SpecLin.Core.module_free_chartTensor`).

Consequently, for `h ∈ K(C_F) = Frac B` one may multiply by a scalar of `F^×` (which does not
change the divisor of `h`) and write `h = a/b` with `a, b ∈ B` both *not* in `P`, so that `h` is
a unit of `B_P` and has a well-defined reduction `h̄ ∈ Frac(B ⧸ P) = K(C_κ)`. -/
theorem exists_smul_notMem_chartFibrePrime (W : C.left.Opens) (hW : IsAffineOpen W)
    [Nonempty W] (b : chartTensor (K := K) (C := C) R W) :
    letI : Algebra R (chartTensor (K := K) (C := C) R W) :=
      Algebra.TensorProduct.rightAlgebra (R := K) (A := Γ(C.left, W)) (B := R)
    ∃ (c : R) (b' : chartTensor (K := K) (C := C) R W),
      b = c • b' ∧ b' ∉ chartFibrePrime (K := K) (C := C) R W := by
  letI : Algebra R (chartTensor (K := K) (C := C) R W) :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := Γ(C.left, W)) (B := R)
  haveI : Module.Free R (chartTensor (K := K) (C := C) R W) :=
    module_free_chartTensor (K := K) (A := Γ(C.left, W)) (R := R)
  haveI : Nontrivial (chartTensor (K := K) (C := C) R W) := by
    letI : Module.Free K R := Module.Free.of_divisionRing K R
    letI : Module.Flat K R := Module.Flat.of_free
    exact (Algebra.TensorProduct.includeRight_injective (R := K) (A := Γ(C.left, W)) (B := R)
      (RingHom.injective (algebraMap K Γ(C.left, W)))).nontrivial
  exact Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map b

end ChartAlgebra


/-! ### The generic and the special fibre of an `R`-point, as `RPt.map` along `R → F` / `R → κ`

These two rewrites are the bridge between the `ptDiv`-form of the statement (with `genPt` and
`closedPt`) and the `RPt.map`-form used by `Work.SpecLin.Alt.chartCore`. -/

section FibreRewrites

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- The generic fibre `genPt R ≫ p` of an `R`-point of a curve is the extension of scalars of
`p` along `R → Frac R`. -/
@[simp]
theorem rPt_map_fractionRing (R : Type u) [CommRing R] [IsDomain R] [Algebra K R]
    (p : Work.SpecLin.CurvePt C R) :
    Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) p
      = Work.SpecLin.genPt (K := K) R ≫ p := by
  rw [Work.SpecLin.RPt.map, Work.SpecLin.genPt_eq_specOfMap]

/-- The special fibre `closedPt R ≫ p` of an `R`-point of a curve is the extension of scalars of
`p` along `R → κ`. -/
@[simp]
theorem rPt_map_residueField (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (p : Work.SpecLin.CurvePt C R) :
    Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) p
      = Work.SpecLin.closedPt (K := K) R ≫ p := by
  rw [Work.SpecLin.RPt.map, Work.SpecLin.closedPt_eq_specOfMap]

end FibreRewrites

section Model

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-! ### The `R`-model of the curve `C ×_K Spec R`

The independent proof of the target (see the status block at the end of this file) proceeds by
restricting principal divisors on the model `X = C ×_K Spec R` to its special fibre. -/

/-- The structure morphism `Spec R ⟶ Spec K` of a `K`-algebra `R`. -/
noncomputable abbrev specOfMapAlg (R : Type u) [CommRing R] [Algebra K R] :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K R))

/-- **The `R`-model of the curve**: `X = C ×_K Spec R`, as a scheme over `Spec R`.  Its generic
fibre is `C_F` (`F = Frac R`) and its special fibre is `C_κ` (`κ = R ⧸ m_R`). -/
noncomputable abbrev curveModel (R : Type u) [CommRing R] [Algebra K R] :
    Over (Spec (CommRingCat.of R)) :=
  (Over.pullback (specOfMapAlg (K := K) R)).obj C.toOver

/-- The projection `X ⟶ C` of the `R`-model to the curve. -/
noncomputable abbrev curveModelFst (R : Type u) [CommRing R] [Algebra K R] :
    (curveModel (K := K) (C := C) R).left ⟶ C.left :=
  pullback.fst C.hom (specOfMapAlg (K := K) R)

end Model

end Work.SpecLin.Core
