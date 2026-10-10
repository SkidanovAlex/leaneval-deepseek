import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulingVec

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2.Defs` — the ruling presentation of the AS source divisor (chart `c₀ = 1`)

This is the AS analogue of `Work.MotK.TGen.STRulingTheta` (the T-route's ruling presentation of
the source divisor `sT`).  The residual curve of the AS chart lives in the plane chart
`c = (1, X₀, X₁, X₂, 0)` of the target hyperplane `{z₄ = 0}`, i.e.

* `ZIAS a b g = Ideal.span (Set.range (zcubAS a b g))`,
  `zcubAS a b g k = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] k` (`ASResidual.lean`);

the ruling line of the source surface `{sAS2 = 0}` over a point `(u,v,w) ∈ V(ZIAS)` is spanned by
the two explicit polynomial vectors `ASRul.kbRv a b g`, `ASRul.kbRw a b g`
(`ASRul/kernel_basis.lean`, whose `kernel_basis` records this for `w ≠ 0`), with slots `3, 4` equal
to `(δ, 0)` resp. `(0, ε)`, where `δ = X₂²(2a−b)(a+2b)` and `ε = X₂²(a+2b)²(2a−b)`.

The ruling presentation is

  `θ (X j) = C (mk (kbRv (j+1))) * X + C (mk (kbRw (j+1)))`     (`ASrulTh`, `ASrulTheta`),

an element of `A[X]`, `A = K[X₀,X₁,X₂] ⧸ radical (ZIAS a b g)` — the source ruling divisor is ruled
over the residual curve.  Dividing by the normalising coefficient `ε` (`ASrulThetaField`) gives the
`K`-algebra map `S →ₐ[K] FractionRing (Polynomial A)` whose kernel is the claimed prime `x` and
whose range generates the fraction field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

/-- The chart index `j ↦ j + 1` (`Fin 3 → Fin 5`), the analogue of the T-route's `ch3'`. -/
def asCh3 (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

@[simp] theorem asCh3_val (j : Fin 3) : (asCh3 j).val = j.val + 1 := rfl

variable {K : Type*} [Field K]

/-- **The coordinate ring of the AS residual curve** in the chart `(1, X₀, X₁, X₂, 0)`. -/
abbrev ASrulRing (a b g : K) :=
  MvPolynomial (Fin 3) K ⧸ Ideal.radical (ZIAS a b g)

/-- The ruling parametrisation into the polynomial ring `K[X₀,X₁,X₂][T]` (before reduction modulo
the residual curve): `X j ↦ C (kbRv (j+1)) · T + C (kbRw (j+1))`. -/
noncomputable def ASrulTh (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.aeval (fun j : Fin 3 =>
    Polynomial.C (ASRul.kbRv a b g (asCh3 j)) * Polynomial.X
      + Polynomial.C (ASRul.kbRw a b g (asCh3 j)))

/-- **The ruling presentation of the AS source divisor**:
`ASrulTheta a b g : K[X₀,X₁,X₂] →ₐ[K] A[T]` with `A = ASrulRing a b g`. -/
noncomputable def ASrulTheta (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Polynomial (ASrulRing a b g) :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ K (Ideal.radical (ZIAS a b g)))).comp
    (ASrulTh a b g)

/-- The value of the ruling presentation on the generators. -/
theorem ASrulTheta_X (a b g : K) (j : Fin 3) :
    ASrulTheta a b g (MvPolynomial.X j)
      = Polynomial.C (Ideal.Quotient.mk (Ideal.radical (ZIAS a b g))
            (ASRul.kbRv a b g (asCh3 j))) * Polynomial.X
        + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (ZIAS a b g))
            (ASRul.kbRw a b g (asCh3 j))) := by
  simp [ASrulTheta, ASrulTh, MvPolynomial.aeval_X]

/-- The normalising coefficient `kbRw · 4 = X₂² (a+2b)² (2a−b)` of the second ruling vector. -/
theorem ASRul_kbRw_four (a b g : K) :
    ASRul.kbRw a b g 4
      = MvPolynomial.C (a + 2 * b) ^ 2 * MvPolynomial.C (2 * a - b) * (MvPolynomial.X 2) ^ 2 := by
  simp [ASRul.kbRw]

/-- The normalising coefficient `kbRv · 3 = X₂² (2a−b)(a+2b)` of the first ruling vector. -/
theorem ASRul_kbRv_three (a b g : K) :
    ASRul.kbRv a b g 3
      = MvPolynomial.C (2 * a - b) * MvPolynomial.C (a + 2 * b) * (MvPolynomial.X 2) ^ 2 := by
  simp [ASRul.kbRv]

/-- `kbRw · 3 = 0`. -/
theorem ASRul_kbRw_three (a b g : K) : ASRul.kbRw a b g 3 = 0 := rfl

/-! ## The normalised (field-valued) ruling presentation

The chart coordinate of the ruling point in the source chart `{v₀ = 0, v₄ = 1}` is the
*projection* normalised by its fourth coordinate, i.e. `(T·rv_{j+1} + rw_{j+1})/ε` with
`ε = kbRw · 4` (cf. `ASRul.srcRulPt`).  Since `sAS2` is **not** homogeneous, the vanishing
certificate `θ (sAS2) = 0` holds for this normalised map and *not* for `ASrulTheta`
(so `ASrulTheta` alone is not the right presentation for the certificate).

The field-valued map `S →ₐ[K] FractionRing (Polynomial A)` with `X j ↦ (C (mk (kbRv (j+1)))·X +
C (mk (kbRw (j+1))))·(C (mk ε))⁻¹` **cannot be defined at this level**: the
`FractionRing`/`OreLocalization` instance diamond ("typeclass instance problem is stuck" on
`algebraMap (Polynomial A) (FractionRing (Polynomial A))` and no `Inv` instance without
`IsDomain A`) blocks it, exactly as recorded in `ASRULINGMAINNEW_STATE.md` §3rd addendum.  The
workarounds are

* build it inside the proof of the K5 statement, where `hDZ : IsDomain A` is a local instance and
  the `letI` pins of `Work.MotK.TGen.ThetaRangeClosure` can be used, or
* use `Localization.Away (C (mk ε))` of `Polynomial A` (whose `IsLocalization.mk'` needs no `Inv`)
  and pass to `FractionRing (Polynomial A)` at the end.

The *cleared* form of the certificate, which lives in `Polynomial (ASrulRing a b g)` and therefore
has no instance obstruction, is recorded here. -/

/-- The normalising coefficient `ε = kbRw · 4 = X₂²(a+2b)²(2a−b)` of the AS ruling vectors. -/
noncomputable def ASrulEps (a b g : K) : MvPolynomial (Fin 3) K := ASRul.kbRw a b g 4

end Work.MotAS
