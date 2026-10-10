import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Surjectivity of the reduction map on points (Silverman, AEC, VII.2.1)

The main result is `Work.SilvermanReduction.redPoint_surjective`: over a Henselian discrete
valuation ring `R` with fraction field `K`, every point of the special fibre of a Weierstrass
curve `W/K` with good reduction is the reduction of a point of `E(K)`.

The mathematical content is Hensel's lemma applied to the Weierstrass equation, once in the
`y`-variable (`hensel_exists_root_Y`) and, when the `y`-derivative vanishes, in the `x`-variable
(`hensel_exists_root_X`).

## Main results

* `hensel_exists_root_Y` — the `y`-direction Hensel lift.
* `hensel_exists_root_X` — the `x`-direction Hensel lift.
* `redPoint_surjective` — Silverman, AEC, VII.2.1 (surjectivity).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open Polynomial
open IsLocalRing (ResidueField residue)
open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.SilvermanReduction

noncomputable section

/-! ## Hensel's lemma in the two coordinate directions -/

/-- **Hensel lift in the `y`-direction.**  Let `R` be a Henselian local ring, `I` a Weierstrass
curve over `R` and `(x̄, ȳ)` a point of the reduction `I.mod m` whose `y`-partial derivative
`∂F/∂y = 2y + a₁x + a₃` is nonzero.  Then any lift `r ∈ R` of `x̄` extends to a point
`(r, s)` of `I` with `s ≡ ȳ (mod m)`.

The polynomial used is the monic quadratic `G(Y) = Y² + (a₁r + a₃)Y - (r³ + a₂r² + a₄r + a₆)`; its
derivative at `ȳ` is exactly `∂F/∂y` at `(x̄, ȳ)`. -/
lemma hensel_exists_root_Y {R : Type*} [CommRing R] [HenselianLocalRing R]
    (I : WeierstrassCurve R) (r : R) (yb : ResidueField R)
    (heq : Equation (I.map (residue R)) (residue R r) yb)
    (hY : (polynomialY (I.map (residue R))).evalEval (residue R r) yb ≠ 0) :
    ∃ s : R, Equation I r s ∧ residue R s = yb := by
  let g : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (I.a₁ * r + I.a₃) * Polynomial.X
    - Polynomial.C (r ^ 3 + I.a₂ * r ^ 2 + I.a₄ * r + I.a₆)
  have hgmonic : g.Monic := by simp only [g]; monicity!
  have hg0 : Polynomial.aeval yb g = 0 := by
    have h1 : yb ^ 2 + (residue R I.a₁ * residue R r + residue R I.a₃) * yb
        - (residue R r ^ 3 + residue R I.a₂ * residue R r ^ 2 + residue R I.a₄ * residue R r
          + residue R I.a₆) = 0 := by
      rw [equation_iff] at heq
      rw [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
      rw [sub_eq_zero]
      rw [show yb ^ 2 + (residue R I.a₁ * residue R r + residue R I.a₃) * yb
          = yb ^ 2 + (residue R I.a₁ * residue R r) * yb + (residue R I.a₃) * yb from by ring,
        heq]
    simpa only [g, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      ResidueField.algebraMap_eq] using h1
  have hder : Polynomial.derivative g
      = Polynomial.C 2 * Polynomial.X + Polynomial.C (I.a₁ * r + I.a₃) := by
    simp only [g, Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_pow,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_mul]
    ring_nf
  have hg1 : Polynomial.aeval yb (Polynomial.derivative g) ≠ 0 := by
    rw [hder]
    rw [evalEval_polynomialY, map_a₁, map_a₃] at hY
    simpa only [map_add, map_mul, map_ofNat, Polynomial.aeval_X, Polynomial.aeval_C,
      ResidueField.algebraMap_eq, add_assoc] using hY
  have H := ((HenselianLocalRing.TFAE R).out 1 2).mp (inferInstance : HenselianLocalRing R)
  obtain ⟨s, hsroot, hsr⟩ := H g hgmonic yb hg0 hg1
  refine ⟨s, ?_, hsr⟩
  rw [equation_iff]
  have hs : Polynomial.eval s g = 0 := hsroot
  simp only [g, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] at hs
  rw [show s ^ 2 + I.a₁ * r * s + I.a₃ * s = s ^ 2 + (I.a₁ * r + I.a₃) * s from by ring,
    ← sub_eq_zero, hs]

/-- **Hensel lift in the `x`-direction.**  Let `R` be a Henselian local ring, `I` a Weierstrass
curve over `R` and `(x̄, ȳ)` a point of the reduction `I.mod m` whose `x`-partial derivative
`∂F/∂x = a₁y - (3x² + 2a₂x + a₄)` is nonzero.  Then any lift `s ∈ R` of `ȳ` extends to a point
`(r, s)` of `I` with `r ≡ x̄ (mod m)`.

The polynomial used is the monic cubic
`G(X) = X³ + a₂X² + (a₄ - a₁s)X + (a₆ - s² - a₃s)`; its derivative at `x̄` is the negative of
`∂F/∂x` at `(x̄, ȳ)`. -/
lemma hensel_exists_root_X {R : Type*} [CommRing R] [HenselianLocalRing R]
    (I : WeierstrassCurve R) (s : R) (xb : ResidueField R)
    (heq : Equation (I.map (residue R)) xb (residue R s))
    (hX : (polynomialX (I.map (residue R))).evalEval xb (residue R s) ≠ 0) :
    ∃ r : R, Equation I r s ∧ residue R r = xb := by
  let g : Polynomial R := Polynomial.X ^ 3 + Polynomial.C I.a₂ * Polynomial.X ^ 2
    + Polynomial.C (I.a₄ - I.a₁ * s) * Polynomial.X + Polynomial.C (I.a₆ - s ^ 2 - I.a₃ * s)
  have hgmonic : g.Monic := by simp only [g]; monicity!
  have hg0 : Polynomial.aeval xb g = 0 := by
    have h1 : xb ^ 3 + residue R I.a₂ * xb ^ 2
          + (residue R I.a₄ - residue R I.a₁ * residue R s) * xb
          + (residue R I.a₆ - residue R s ^ 2 - residue R I.a₃ * residue R s) = 0 := by
      rw [equation_iff] at heq
      rw [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
      rw [show xb ^ 3 + residue R I.a₂ * xb ^ 2
              + (residue R I.a₄ - residue R I.a₁ * residue R s) * xb
              + (residue R I.a₆ - residue R s ^ 2 - residue R I.a₃ * residue R s)
            = (xb ^ 3 + residue R I.a₂ * xb ^ 2 + residue R I.a₄ * xb + residue R I.a₆)
              - (residue R s ^ 2 + residue R I.a₁ * xb * residue R s
                + residue R I.a₃ * residue R s) from by ring,
        heq, sub_self]
    simpa only [g, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      ResidueField.algebraMap_eq] using h1
  have hder : Polynomial.derivative g = Polynomial.C 3 * Polynomial.X ^ 2
      + Polynomial.C (I.a₂ * 2) * Polynomial.X + Polynomial.C (I.a₄ - I.a₁ * s) := by
    simp only [g, Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.derivative_mul, Polynomial.C_mul]
    ring_nf
  have hX' : residue R I.a₁ * residue R s
      - (3 * xb ^ 2 + 2 * residue R I.a₂ * xb + residue R I.a₄) ≠ 0 := by
    rwa [evalEval_polynomialX, map_a₁, map_a₂, map_a₄] at hX
  have hg1 : Polynomial.aeval xb (Polynomial.derivative g) ≠ 0 := by
    rw [hder]
    have hkey : Polynomial.aeval xb (Polynomial.C 3 * Polynomial.X ^ 2
          + Polynomial.C (I.a₂ * 2) * Polynomial.X + Polynomial.C (I.a₄ - I.a₁ * s))
        = -(residue R I.a₁ * residue R s
            - (3 * xb ^ 2 + 2 * residue R I.a₂ * xb + residue R I.a₄)) := by
      simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, Polynomial.aeval_X,
        Polynomial.aeval_C, ResidueField.algebraMap_eq]
      first | refl_ring1 | ring
    rw [hkey]
    exact neg_ne_zero.mpr hX'
  have H := ((HenselianLocalRing.TFAE R).out 1 2).mp (inferInstance : HenselianLocalRing R)
  obtain ⟨r, hsroot, hsr⟩ := H g hgmonic xb hg0 hg1
  refine ⟨r, ?_, hsr⟩
  rw [equation_iff]
  have hs : Polynomial.eval r g = 0 := hsroot
  simp only [g, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] at hs
  rw [← sub_eq_zero]
  rw [show s ^ 2 + I.a₁ * r * s + I.a₃ * s - (r ^ 3 + I.a₂ * r ^ 2 + I.a₄ * r + I.a₆)
      = -(r ^ 3 + I.a₂ * r ^ 2 + (I.a₄ - I.a₁ * s) * r + (I.a₆ - s ^ 2 - I.a₃ * s))
      from by ring, hs, neg_zero]

/-! ## Surjectivity of the reduction map -/

/-- **Silverman, AEC, VII.2.1 (surjectivity of the reduction map).**  Let `R` be a *Henselian*
discrete valuation ring with fraction field `K` and residue field `k`, and let `W/K` be a
Weierstrass curve with good reduction at the place.  Then every point of the special fibre is the
reduction of a point of `E(K)`: `Function.Surjective (redPoint R W)`.

Proof route: `Ẽ(k)` is the affine curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with the point at
infinity.  Given `(x̄, ȳ)` on the reduced curve, use Hensel's lemma (`HenselianLocalRing R`, via
`HenselianLocalRing.TFAE`) for the Weierstrass equation.  The equation is monic in `y` and has a
simple root modulo the maximal ideal **unless** `2ȳ + a₁x̄ + a₃ = 0`; in that case the equation is
monic in `x` with nonzero derivative `∂f/∂x = -(3x̄² + 2a₂x̄ + a₄ - a₁ȳ)` (the point is nonsingular
because `(W.reduction R).IsElliptic`, available from `HasGoodReduction`), so Hensel-lift `x` from
`ȳ` instead.  The point at infinity of `Ẽ(k)` is hit by `redPoint_zero`. -/
theorem redPoint_surjective {K : Type*} [Field K] [DecidableEq K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R] :
    Function.Surjective (Work.SilvermanReduction.redPoint R W) := by
  intro P
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨0, redPoint_zero R⟩
  · classical
    -- View the nonsingular point of the special fibre as a point of the reduction of the
    -- integral model `I = W.integralModel R`.
    have hP' : Nonsingular ((WeierstrassCurve.integralModel R W).map (residue R)) x y := by
      simpa only [WeierstrassCurve.reduction] using hP
    -- Hensel: lift the coordinates to an integral point of `I`.
    have key : ∃ r s : R, Equation (WeierstrassCurve.integralModel R W) r s ∧
        residue R r = x ∧ residue R s = y := by
      rcases hP'.2 with hX | hY
      · -- `∂F/∂x ≠ 0`: lift `ȳ` and Hensel in the `x`-variable.
        obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective y
        have heq : Equation ((WeierstrassCurve.integralModel R W).map (residue R)) x (residue R s) := by
          rw [hs]; exact hP'.1
        have hX' : (polynomialX ((WeierstrassCurve.integralModel R W).map (residue R))).evalEval x
            (residue R s) ≠ 0 := by
          rw [hs]; exact hX
        obtain ⟨r, heqR, hr⟩ := hensel_exists_root_X (WeierstrassCurve.integralModel R W) s x heq hX'
        exact ⟨r, s, heqR, hr, hs⟩
      · -- `∂F/∂y ≠ 0`: lift `x̄` and Hensel in the `y`-variable.
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective x
        have heq : Equation ((WeierstrassCurve.integralModel R W).map (residue R)) (residue R r) y := by
          rw [hr]; exact hP'.1
        have hY' : (polynomialY ((WeierstrassCurve.integralModel R W).map (residue R))).evalEval
            (residue R r) y ≠ 0 := by
          rw [hr]; exact hY
        obtain ⟨s, heqR, hs⟩ := hensel_exists_root_Y (WeierstrassCurve.integralModel R W) r y heq hY'
        exact ⟨r, s, heqR, hr, hs⟩
    obtain ⟨r, s, heqR, hr, hs⟩ := key
    -- The Hensel lift is nonsingular: a nonvanishing partial derivative in the special fibre
    -- lifts to a nonvanishing partial derivative over `R`.
    have hnsR : Nonsingular (WeierstrassCurve.integralModel R W) r s := by
      refine ⟨heqR, ?_⟩
      have keyX : residue R (Polynomial.evalEval r s
            (polynomialX (WeierstrassCurve.integralModel R W)))
          = Polynomial.evalEval (residue R r) (residue R s)
              (polynomialX ((WeierstrassCurve.integralModel R W).map (residue R))) := by
        rw [map_polynomialX, Polynomial.map_mapRingHom_evalEval]
      have keyY : residue R (Polynomial.evalEval r s
            (polynomialY (WeierstrassCurve.integralModel R W)))
          = Polynomial.evalEval (residue R r) (residue R s)
              (polynomialY ((WeierstrassCurve.integralModel R W).map (residue R))) := by
        rw [map_polynomialY, Polynomial.map_mapRingHom_evalEval]
      rcases hP'.2 with hX | hY
      · left
        intro h0
        exact hX (by rw [← hr, ← hs, ← keyX, h0, map_zero])
      · right
        intro h0
        exact hY (by rw [← hr, ← hs, ← keyY, h0, map_zero])
    -- Base change the lift to `K`, where it becomes a point of `W`.
    have hnsK : Nonsingular W (algebraMap R K r) (algebraMap R K s) := by
      have h2 : Nonsingular ((WeierstrassCurve.integralModel R W).baseChange K)
          (algebraMap R K r) (algebraMap R K s) :=
        (map_nonsingular (W := WeierstrassCurve.integralModel R W) (f := algebraMap R K)
          algebraMap_injective r s).mpr hnsR
      rwa [WeierstrassCurve.baseChange_integralModel_eq R W] at h2
    refine ⟨WeierstrassCurve.Affine.Point.some (algebraMap R K r) (algebraMap R K s) hnsK, ?_⟩
    rw [redPoint_some_mk R (W := W) hnsK rfl rfl]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hr, hs⟩

end

end Work.SilvermanReduction
