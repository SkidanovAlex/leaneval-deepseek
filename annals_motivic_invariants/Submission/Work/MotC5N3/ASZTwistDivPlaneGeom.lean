import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.ASZChartData
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotC5N3.ASZPhiMemGen
import Submission.Work.MotC5N3.ASZChartNegIso
import Submission.Work.MotC5N3.ASZPhiKerRoot
import Submission.Work.MotC5N3.ASZRadicalIsPrime
import Submission.Work.MotC5N3.ASZSatCertAll
import Submission.Work.MotC5N3.D0_regular_AS
import Submission.Work.MotAS.asChartIdeal_fracIso_of_certificates

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

/-!
# `Work.MotC5N3.ASZTwistDivPlaneGeom` — the K6 leaf of the AS census

The residual curve of the class-`g` AS Crauder–Katz link is the image of the AS-twisted Klein
curve `C_{3g} = V(kleinPAS a b (3 * g))` under the *linear* projection `phiAS a b`, which is
birational onto it; hence the function field of the residual curve is that of the chart `Y₀ = 1`
of `C_{3g}`, i.e. `Frac (K[Y] ⧸ asChartIdeal a b (3 * g))`.  Composing with the sign reversal
`3 * g = -(2 * g)` (`Work.MotC5N3.ASZChartNegIso`) gives the target.

## The two chart maps

* **Forward** `K[X₀,X₁,X₂] →ₐ[K] Frac (K[Y] ⧸ asChartIdeal a b (3g))`, `X i ↦ Z_{i+1}/Z_0` with
  `Z_k = Σ_j phiAS a b k j · Y_j`: it kills `√ZIAS` because by `Work.MotC5N3.ASZPhiMemGen` the
  vector `phiAS a b · Y` satisfies the residual equations `kleinRAS a b g` modulo
  `⟨kleinPAS a b (3g)(Y)⟩`, and `kleinRAS` is homogeneous of degree three.
* **Inverse** `K[Y] →ₐ[K] Frac (K[X] ⧸ √ZIAS)`, `Y 0 ↦ 1`, `Y j ↦ -B₁·Pb_j/(D₁·C₁)`: the closed
  point of `C_{3g}` on the ruling line over the generic point of the residual, normalised to the
  chart `Y₀ = 1`.  It kills `asChartIdeal a b (3g)`: `Y 0 - 1` trivially, the five Pfaffians by the
  certificate `aszLco k ∈ √ZIAS` (`Submission/Work/MotC5N3/ASZCertLco.lean`).

The two maps are inverse on the generators of the two chart rings, which gives the fraction-field
identification (`Work.MotAS.fractionRing_quotient_algEquiv_of_ker`, `IsFractionRing.liftAlgHom`).

## The two data facts

* the certificate `aszLco a b g k ∈ √ZIAS a b g` — `Submission/Work/MotC5N3/ASZCertLco.lean`
  (CAS-exported coefficients, `ring`-checked in characteristic `5`);
* the non-vanishing `aszCco a b g 1 ∉ √ZIAS a b g` — the inverse point does not lie in the
  hyperplane `Y₀ = 0`; needed to invert `C₁` in the inverse chart map
  (`Submission/Work/MotC5N3/ASZCcoOneNotMem.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {K : Type} [Field K] [CharP K 5]

/-! ## §1  The assembly: the class-`3 * g` leaf implies the target -/

/-- **The `3 * g` leaf implies the target.**  In characteristic `5` one has `3 * g = -(2 * g)`, and
the sign involution `y_i ↦ (-1)^i y_i` identifies the chart ideals of the classes `c` and `-c`
(`Work.MotC5N3.ASZChartNegIso`). -/
theorem ASZTwistDivPlaneGeom_of_three (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [CharP 𝕜 5] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K)
    (h : Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (aK K D) (bK K D) (3 * g)))) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (aK K D) (bK K D) (2 * g))) := by
  obtain ⟨e₁⟩ := h
  obtain ⟨e₂⟩ := ASZChartNegIso K (aK K D) (bK K D) g
  exact ⟨e₁.trans e₂⟩

/-- **The class-`3 * g` leaf**: the function field of the residual curve is the function field of
the chart `Y₀ = 1` of the AS-twisted Klein curve of class `3 * g`.

Forward map `X i ↦ Z_{i+1}/Z_0` into `Frac (K[Y] ⧸ asChartIdeal a b (3g))`, inverse
`Y j ↦ -B₁·Pb_j/(D₁·C₁)`; both are checked on generators. -/
theorem ASZTwistDivPlaneGeom_three (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [CharP 𝕜 5] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (3 * g))) := by
  -- CLOSED 2026-10-08 (area owner).  The primality of `√(ZIAS a b g)` is supplied *sorry-free and
  -- axiom-clean* by the `D₀`-regularity route:
  -- `Work.MotC5N3.D0_regular_AS` (proved: `D₀` is a non-zero-divisor modulo `ZIAS a b g`) gives the
  -- `D₀`-avoidance through `Work.MotC5N3.Dmin_of_Dregular`, and the saturation certificate
  -- `Work.MotC5N3.ASZSatCert_ASZGC` (the `hB1`/`hB3`-certificate route) gives `ZIAS ≤ Sat`, so
  -- `Work.MotC5N3.isPrime_radical_ZIAS_of_Dregular` yields `IsPrime (√ZIAS)`.
  -- `Work.MotC5N3.ASZPhiKerRoot` then converts exactly that input into this leaf.
  -- (The `ASZRadicalIsPrime` import is retained for backward compatibility of the transitive
  -- import graph; the proof no longer goes through it, whose closure still contains the
  -- `ASRulV2M` leaves `Nn_dvd_gen`, `ZiasLeSpanPQG`, `ann_eq_gen`.)
  have hreg := D0_regular_AS K (aK K D) (bK K D) g (aK_sq_sub_ne (K := K) D hD) hg
  exact ASZTwistDivPlaneGeom_three_of_isPrime K D hD g hg
    (isPrime_radical_ZIAS_of_Dregular K (aK K D) (bK K D) g (aK_sq_sub_ne (K := K) D hD) hg hreg)

/-- **The K6 leaf of the AS census**, general form: the plane model of the residual curve is the
chart of the twist by `2 * g`.  **The lead has ruled (2026-10-07, `Submission/Work/MotC5N3/K6_RULING.md`)
that this statement is TRUE AS WRITTEN, class `2 • g` included** — the reviewer who called it false
double-counted the doubling: the `asM (3 * w) * diag (2 ^ j)` frame already puts the residual curve in
class `3 * g`, and `3 * g ≅ 2 * g` in characteristic `5` via `kleinPAS_neg_apply` (`y_i ↦ (-1) ^ i y_i`),
the same reversal as in `Work.MotC5N3.ASZChartNegIso`; the Gröbner certificates over `𝔽₅[b,g]` show
`kleinRAS_k (phiAS · y) ∈ ⟨kleinPAS (a, b, 3 * g)⟩` (and fail for `g`, `2 * g`, `4 * g`), the image
ideal equals `√ZIAS`, and `e₀ ∉ C_{3g}` since `kleinPAS₀ e₀ = (a + 2 * b) ^ 2 ≠ 0`, so the
projection is birational.  Note that `hg` is never used in the argument.

For a field `K` of characteristic `5` over `𝕜`, Klein data `D` with `ASGood D` and any `g : K`, the
fraction field of `K[X₀,X₁,X₂] / √(ZIAS (aK K D) (bK K D) g)` is `K`-isomorphic to the fraction field
of the chart ring `K[Y₀..Y₄] / asChartIdeal (aK K D) (bK K D) (2 • g)`.

Plan (`K6_RULING.md` §3): the forward map is `X_i ↦ Z_{i+1} / Z₀` (the `phiAS` of
`Submission/Work/MotC5N3/ASZTwistDivPlaneGeomGen.lean`), the inverse `Θ` sends `Y_j ↦ f_j / S` with
`S = -C₁ / B₁` and uses the proved `ASZCert0`–`ASZCert4` / `ASZConsistCert`; check both compositions on
generators, finish with `IsFractionRing.liftAlgHom`, then compose with the `3 * g → 2 * g` reversal
`Work.MotC5N3.ASZChartNegIso`.  Export the ideal-membership coefficients from a CAS and keep every
data file ≤ 15 KB with `maxHeartbeats ≤ 4000000`.

This is the leaf called by `Work.MotC5N3.ASZTwistDiv2`, hence the K6 input of the `hS` clause
`Work.MotC5N3.censusAS2_class_sAS` of the generic AS census, hence of
`Work.MotC5N3.CensusReduction.CensusSASClause` and of node **G-LK**; with `K5Ruling` and
`X2_notMem_radical_gen` it is one of the last three inputs of the unconditional
`Submission/Work/MotC5N3/Patch.lean`.

Deliverable: sorry-free and axiom-clean, in namespace `Work.MotC5N3`, at the file
`Submission/Work/MotC5N3/ASZTwistDivPlaneGeom.lean`; the existing open statement file
(`ASZTwistDivPlaneGeomGen.lean`) then becomes a one-line wrapper and `ASZTwistDiv2` keeps calling it. -/
theorem ASZTwistDivPlaneGeom (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (2 • g))) := by
  -- `2 • g` and `2 * g` are only *propositionally* equal; the defeq check on the big
  -- `FractionRing ⧸ asChartIdeal` type is prohibitively expensive, so rewrite first.
  rw [show (2 : ℕ) • g = 2 * g from nsmul_eq_mul 2 g]
  exact ASZTwistDivPlaneGeom_of_three K D hD g (ASZTwistDivPlaneGeom_three K D hD g hg)

end Work.MotC5N3
