import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotAS.ASRul.sAS2_ruling_mem
import Submission.Work.MotAS.ASrulV_mem
import Submission.Work.MotAS.ASrulW_mem
import Submission.Work.MotAS.Nodes.ASCertGen.P1Nat

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.ASGen` — The ruling line over the generic point of the residual curve (piece 2/6)

This module is one piece of the split of `Submission/Work/MotAS/Nodes/ASCertDefsGen.lean`
(51 KB, `maxHeartbeats 100000000`), which never compiled within the build budget.  The pieces
below 25 KB each with `maxHeartbeats 4000000`; the aggregator `ASCertDefsGen` still exports the
whole `Work.MotAS.Nodes.ASGen` namespace, so no consumer has to change.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.Nodes.ASGen

/-! ## §2  The ruling line over the generic point -/

/-- The quotient map `K[X₀,X₁,X₂] → A`. -/
noncomputable def asMk {K : Type} [Field K] (a b g : K) :
    MvPolynomial (Fin 3) K →+* Work.MotC5N3.ASrulA a b g :=
  Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))

/-- The quotient map fixes the constants. -/
theorem asMk_C {K : Type} [Field K] (a b g : K) (x : K) :
    asMk a b g (MvPolynomial.C x) = algebraMap K (Work.MotC5N3.ASrulA a b g) x := by
  rw [MvPolynomial.C_eq_algebraMap]
  exact Ideal.Quotient.mk_algebraMap K (Ideal.radical (Work.MotAS.ZIAS a b g)) x

/-- `Polynomial.C ∘ asMk` fixes the constants. -/
theorem asMk_polyC {K : Type} [Field K] (a b g : K) (x : K) :
    Polynomial.C (asMk a b g (MvPolynomial.C x))
      = algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) x := by
  rw [asMk_C a b g x, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply K (Work.MotC5N3.ASrulA a b g)
      (Polynomial (Work.MotC5N3.ASrulA a b g)) x]

/-- The two AS ruling vectors agree with `kbRv` / `kbRw`. -/
theorem ASrulV_eq_kbRv {K : Type} [Field K] (a b g : K) :
    Work.MotAS.ASrulV a b g = Work.MotAS.ASRul.kbRv a b g := rfl

/-- The two AS ruling vectors agree with `kbRv` / `kbRw`. -/
theorem ASrulW_eq_kbRw {K : Type} [Field K] (a b g : K) :
    Work.MotAS.ASrulW a b g = Work.MotAS.ASRul.kbRw a b g := rfl

/-- The ruling line over the generic point of the residual curve. -/
noncomputable def zvT {K : Type} [Field K] (a b g : K) :
    Fin 5 → Polynomial (Work.MotC5N3.ASrulA a b g) := fun k =>
  Polynomial.C (asMk a b g (Work.MotAS.ASRul.kbRv a b g k)) * Polynomial.X
    + Polynomial.C (asMk a b g (Work.MotAS.ASRul.kbRw a b g k))

/-- The generic base point of the residual curve, in `A[T]`. -/
noncomputable def cvT {K : Type} [Field K] (a b g : K) :
    Fin 5 → Polynomial (Work.MotC5N3.ASrulA a b g) := fun k =>
  Polynomial.C (asMk a b g (Work.MotAS.asBaseVec K k))

/-- The localization map `A[T] →+* A[T][1/ε]`, spelled out because the typeclass search for
`Algebra A[T] A[T][1/ε]` is stuck on the `Ideal.Quotient` instance diamond. -/
noncomputable def toS {K : Type} [Field K] (a b g : K) :
    Polynomial (Work.MotC5N3.ASrulA a b g) →+*
      Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) := by
  letI : Semiring (Work.MotC5N3.ASrulA a b g) :=
    (inferInstance : CommSemiring (Work.MotC5N3.ASrulA a b g)).toSemiring
  letI : CommSemiring (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : CommRing (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : Algebra (Polynomial (Work.MotC5N3.ASrulA a b g))
      (Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))) := OreLocalization.instAlgebra
  exact algebraMap _ _

/-- The composite `A → A[T] → A[T][1/ε]`. -/
noncomputable def toSA {K : Type} [Field K] (a b g : K) :
    Work.MotC5N3.ASrulA a b g →+*
      Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) :=
  (toS a b g).comp Polynomial.C

/-- The composite `K → A → A[T] → A[T][1/ε]`. -/
noncomputable def toSK {K : Type} [Field K] (a b g : K) :
    K →+* Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) :=
  (toSA a b g).comp ((asMk a b g).comp MvPolynomial.C)

/-- The ruling line over the generic point, in `S = A[T][1/ε]`. -/
noncomputable def zvS {K : Type} [Field K] (a b g : K) :
    Fin 5 → Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) := fun k =>
  toS a b g (zvT a b g k)

/-- The generic base point of the residual curve, in `S`. -/
noncomputable def cvS {K : Type} [Field K] (a b g : K) :
    Fin 5 → Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) := fun k =>
  toS a b g (cvT a b g k)

/-- The normalising element `ε` in `S`. -/
noncomputable def epsS {K : Type} [Field K] (a b g : K) :
    Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) :=
  toS a b g (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))

/-- The fourth coordinate of the ruling line over the generic point is the normaliser `ε`. -/
@[simp] theorem zvT_four {K : Type} [Field K] (a b g : K) :
    zvT a b g 4 = Polynomial.C (Work.MotC5N3.ASrulEpsA a b g) := by
  have h : Work.MotAS.ASRul.kbRv a b g 4 = 0 := by
    simp [Work.MotAS.ASRul.kbRv]
  simp only [zvT, h, map_zero, Polynomial.C_0, zero_mul, zero_add,
    Work.MotC5N3.ASrulEpsA, asMk]

/-- The fourth coordinate of the generic base point vanishes. -/
@[simp] theorem cvT_four {K : Type} [Field K] (a b g : K) :
    cvT a b g 4 = 0 := by
  simp [cvT]

/-- The fourth coordinate of the ruling line in `S` is `epsS`. -/
@[simp] theorem zvS_four {K : Type} [Field K] (a b g : K) :
    zvS a b g 4 = epsS a b g := by
  show toS a b g (zvT a b g 4) = toS a b g (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))
  rw [zvT_four]

/-- The zeroth coordinate of the generic base point is `1`. -/
theorem cvT_zero {K : Type} [Field K] (a b g : K) : cvT a b g 0 = 1 := by
  simp [cvT]

/-- The constant term of the ruling line: `zvT k = C (mk (kbRv k)) * T + C (mk (kbRw k))`. -/
theorem zvT_apply {K : Type} [Field K] (a b g : K) (k : Fin 5) :
    zvT a b g k = Polynomial.C (asMk a b g (Work.MotAS.ASRul.kbRv a b g k)) * Polynomial.X
      + Polynomial.C (asMk a b g (Work.MotAS.ASRul.kbRw a b g k)) := rfl

end Work.MotAS.Nodes.ASGen
