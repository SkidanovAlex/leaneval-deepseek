import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.MotC5N3.hparam_kernel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

section Defs

variable {K : Type} [Field K]

/-- **The coordinate ring of the AS residual curve** (chart `(1,X₀,X₁,X₂,0)`), i.e. the base of
the ruling of the source ruling divisor `sAS2 a b g`. -/
abbrev ASrulA (a b g : K) : Type :=
  MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotAS.ZIAS a b g)

/-- The normalising coefficient `ε = kbRw · 4 = X₂²(a+2b)²(2a−b)` as an element of the coordinate
ring of the residual curve.  It equals `(a+2b) · (kbRv · 3)`. -/
noncomputable def ASrulEpsA (a b g : K) : ASrulA a b g :=
  Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) (Work.MotAS.ASRul.kbRw a b g 4)

end Defs

section Theta

variable {K : Type} [Field K] [CharP K 5]

set_option maxHeartbeats 3200000 in
/-- **The AS ruling presentation** of the source ruling surface `{sAS2 = 0}` over the residual
curve, normalised by `ε = kbRw · 4`:

`X j ↦ ε⁻¹ · (C (mk (kbRv (j+1))) · T + C (mk (kbRw (j+1))))`,

a `K`-algebra map `K[X₀,X₁,X₂] → A[T][1/ε]`, `A = K[X] ⧸ √ZIAS`.  This is the AS analogue of the
T-route's `Work.MotK.TGen.theta` and of `Work.MotAS.ASRulV2.ASrulTheta` (the unnormalised
version, which lands in `A[T]`).

The normalisation is by the *second* ruling vector (which has pivot `ε`), and is what makes the
chart relation `y (asCh3 j) = y 4 * X j` hold.  The two properties needed for K5 are

* `RingHom.ker (ASrulTheta a b g hDZ) ≠ ⊥`, from the explicit identity
  `kbRv 3 · (ε · X 1 − kbRw 2) = kbRv 2 · (ε · X 2 − kbRw 3)` (where `kbRw 3 = 0` identically) in
  `A[T][1/ε]`;
* `FractionRing (ASrulTheta a b g hDZ).range ≅ FractionRing (Polynomial A)` — the "range
  closure", the analogue of `Work.MotK.TGen.ThetaRangeClosure`: `T = (a+2b) · θ (X 2)` and
  `C (mk (X i)) = θ (fwVecAS2 a b g (i+1)) · (θ (fwVecAS2 a b g 0))⁻¹` lie in the closure.

The target is the `Away`-localization (and not `FractionRing (Polynomial A)` directly) because the
evaluation `σ` used to compute `ker θ` is only defined after inverting `ε`. -/
noncomputable def ASrulTheta (a b g : K) (hDZ : IsDomain (ASrulA a b g)) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (Polynomial.C (ASrulEpsA a b g)) := by
  letI := hDZ
  let R := Polynomial (ASrulA a b g)
  let S := Localization.Away (Polynomial.C (ASrulEpsA a b g))
  exact MvPolynomial.aeval (fun j : Fin 3 =>
    IsLocalization.mk' S
      (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
        + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))))
      ⟨Polynomial.C (ASrulEpsA a b g), Submonoid.mem_powers _⟩)

end Theta

-- K5 of the AS branch in the corrected chart, generic in the base field: every codimension-one
-- point `x` of `A^3_K` at which the corrected source ruling quintic `sAS2 a b g` vanishes (and whose
-- forward chart denominator `fwVecAS2 a b g 0` does not) has residue field the function field of
-- `(residual curve) x A^1`: `FractionRing (Polynomial (K[x0,x1,x2] / radical (ZIAS a b g)))`.
-- This is a fresh copy (in namespace `Work.MotC5N3`) of the already-generic statement
-- `Work.MotAS.ASRulingMainV2` (`Submission/Work/MotAS/ASRulingMainV2.lean`), whose proof is still
-- missing there; proving it here gives `Work.MotC5N3.ASRulingDiv2` an independent route.
--
-- ROUTE (validated this stretch; CAS scripts in `_c5n3scratch/`).
--
-- Step 0 (`a * b = 0` is vacuous).  If `a * b = 0` then `a ^ 2 - a * b - b ^ 2 ≠ 0` forces
-- `(a,b) ≠ (0,0)` and `kleinRAS` is homogeneous of degree `4` in `(a,b)`, so
-- `ZIAS a b g = ZIAS 1 0 g` or `= ZIAS 0 1 g`; in both cases `g ∈ ZIAS a b g`
-- (`Work.MotC5N3.ZIAS_eq_top_of_mul_eq_zero`), so `g ≠ 0` makes the ideal `⊤` and
-- `IsDomain (K[X] ⧸ √ZIAS) = IsDomain 0` is FALSE — contradicting `hDZ`.
-- Henceforth `a b ≠ 0`, so `a ≠ 0`, `b ≠ 0`, and (`ha`, in characteristic `5`) `b ≠ 2a`.
--
-- Step 1 (`fwVecAS2 a b g 3 ∉ x`): `Work.MotC5N3.fwVecAS2_three_notMem_x`.
--
-- Step 2 (the ruling parametrisation).  Put `k := resF K x`, `f : K[X] ↠ k` the residue map,
-- `y := f ∘ ASrulYv`, `c' := f ∘ fwVecAS2 a b g`.  Then `kleinRAS c' = 0` (I1^AS,
-- `Work.MotAS.KleinTwScalarASv` + naturality) and `AmatAS2 a b g c' *ᵥ y = 0`
-- (`Work.MotAS.AmatAS2_mulVec_of_kleinPAS`); by linearity of `AmatAS2` in the base point,
-- `AmatAS2 a b g ![1,b₁,b₂,b₃,0] *ᵥ y = 0` with `bᵢ := c'ᵢ / c'₀`, while `y 4 = 2(a²−ab−b²) ≠ 0`
-- (`ASrulYv_four`) and `b₃ ≠ 0` (Step 1).  `Work.MotC5N3.hparam_kernel` then gives
-- `f (X j) = (y 3/y 4) · ev (kbRv (asCh3 j)) / ev (kbRv 3) + ev (kbRw (asCh3 j)) / ev (kbRw 4)`
-- (the left side by the chart identity `ASrulYv_ch3`), `ev = eval ![b₁,b₂,b₃]`; with
-- `τ := (a+2b) · y 3 / y 4` and `ev (kbRw 4) = (a+2b) · ev (kbRv 3)` this is
-- `f (X j) = σ (θ (X j))` for `σ : A[T][1/ε] → k`, `mk q ↦ ev q`, `T ↦ τ`.
--
-- Step 3 (`ker θ ≤ x`): immediate from `σ ∘ θ = f` and `ker f = x`.
--
-- Step 4 (`ker θ = x`): `ker θ ≠ ⊥` by a Step-2-comment, and
-- `Ideal.height_add_one_le_of_lt_of_isPrime` with `height x = 1`.
--
-- Step 5: `resF K x ≅ FractionRing (ASrulTheta …).range`
-- (`IsFractionRing.algEquivOfAlgEquiv`), and `FractionRing (ASrulTheta …).range ≅
-- FractionRing (Polynomial A)` by the range closure; `FractionRing (Localization.Away ε) ≅
-- FractionRing (Polynomial A)` because `mk ε ≠ 0` (needs `X 2 ∉ √ZIAS`,
-- `Work.MotC5N3.X2_notMem_radical_gen`).
-- **Removed (2026-10-07).**  The declaration that used to be placed here carried the only `sorry`
-- of this module and was referenced by nothing: its statement is superseded on the wire by
-- `Work.MotC5N3.K5Ruling` (the one actually consumed) and by `Work.MotC5N3.ASRulingMainV2Hab`.
-- The definitions above (`ASrulA`, `ASrulEpsA`, `ASrulTheta`, …) are what every consumer of this
-- module imports; the route recorded in the comments above is kept as documentation.

end Work.MotC5N3
