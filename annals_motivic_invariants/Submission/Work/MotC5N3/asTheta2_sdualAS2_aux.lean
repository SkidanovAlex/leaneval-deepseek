import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.asRulingEval
import Submission.Work.MotAS.ASI2
import Submission.Work.MotAS.ASChartGeo

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asTheta2_sdualAS2_aux` — the corrected AS target divisor vanishes on its ruling
(generic base field `K`)

The `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.asTheta2_sdualAS2_aux`
(`Submission/Work/MotAS/asTheta2_sdualAS2.lean`): the presentation
`asTheta2 D g = MvPolynomial.aeval (asPhi2 D g)` of the corrected AS target divisor
(`Submission/Work/MotC5N3/Ruling.lean`) kills the target ruling quintic
`sdualAS2 (aK K D) (bK K D) g`.

## Route

Write `W = asW2 D g` (the ruling point `asRuleQW a b g c X` over the generic curve point
`c = as2c D g`).

1. `c` lies on the twisted Klein curve: this is the hypothesis `hcurve`.
2. `asW2 D g 0 ≠ 0`: this is the hypothesis `hW0`, and it makes the normalisation
   `z_j = W j / W 0` of `asPhi2` legitimate.
3. The ruling identity `Work.MotAS.asRulingEval` (generic in the base field) gives
   `R(W)_i c_j = R(W)_j c_i`; with `c 0 = 1` this reads `R(W) = R(W)_0 • c`.
4. The AS link identity `Work.MotAS.ASI2` (a polynomial identity over any commutative ring with
   `5 = 0`) at component `0` reads `P_0(R(W)) = s'(W)·W_0`; since `R(W) = R(W)_0 • c` and
   `P_0(c) = 0`, homogeneity of `P_0` gives `P_0(R(W)) = R(W)_0^2 P_0(c) = 0`, whence
   `s'(W)·W_0 = 0` and, by step 2, `s'(W) = 0`.
5. `sdualAS2 ∘ asPhi2 = kleinSecDualAS (z_j = W j / W 0)` by naturality of `kleinSecDualAS`
   under `MvPolynomial.aeval`; homogeneity in `z` (`kleinSecDualAS_smul`) turns that into
   `((W_0)⁻¹)^5 · s'(W) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace Work.MotC5N3

open MvPolynomial

/-- Naturality of the dual secant quintic under a ring homomorphism. -/
theorem asTheta2_aux_map_kleinSecDualAS {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (a b g : A) (z : Fin 5 → A) :
    φ (Work.MotAS.kleinSecDualAS a b g z)
      = Work.MotAS.kleinSecDualAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  simp only [Work.MotAS.kleinSecDualAS]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- `MvPolynomial.aeval` on constants, phrased for the underlying ring homomorphism (the form in
which it occurs after applying the naturality lemma). -/
theorem asTheta2_aux_aeval_toRingHom_C {L A : Type*} [CommRing L] [CommRing A] [Algebra L A]
    (ψ : Fin 3 → A) (a : L) :
    (MvPolynomial.aeval ψ).toRingHom (MvPolynomial.C a) = algebraMap L A a := by
  change MvPolynomial.aeval ψ (MvPolynomial.C a) = algebraMap L A a
  rw [MvPolynomial.aeval_C]

/-- **The chart substitution.**  Evaluating `sdualAS2` along the chart map `X i ↦ ψ i` is the same
as evaluating `kleinSecDualAS` at the chart vector `![1, ψ 0, ψ 1, ψ 2, 0]` (the target chart
`tchart = ![1, X 0, X 1, X 2, 0]`). -/
theorem aeval_sdualAS2_tchart {L A : Type*} [CommRing L] [CommRing A] [Algebra L A]
    (ψ : Fin 3 → A) (a b g : L) :
    MvPolynomial.aeval ψ (Work.MotAS.sdualAS2 a b g)
      = Work.MotAS.kleinSecDualAS (algebraMap L A a) (algebraMap L A b) (algebraMap L A g)
          ![1, ψ 0, ψ 1, ψ 2, 0] := by
  rw [Work.MotAS.sdualAS2]
  change (MvPolynomial.aeval ψ).toRingHom
      (Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (Work.MotAS.tchart L))
    = Work.MotAS.kleinSecDualAS (algebraMap L A a) (algebraMap L A b) (algebraMap L A g)
        ![1, ψ 0, ψ 1, ψ 2, 0]
  rw [asTheta2_aux_map_kleinSecDualAS
    (φ := (MvPolynomial.aeval ψ).toRingHom) (MvPolynomial.C a) (MvPolynomial.C b)
    (MvPolynomial.C g) (Work.MotAS.tchart L)]
  have hvec : (fun i => (MvPolynomial.aeval ψ).toRingHom (Work.MotAS.tchart L i))
      = ![1, ψ 0, ψ 1, ψ 2, 0] := by
    funext i
    fin_cases i <;> simp [Work.MotAS.tchart, MvPolynomial.aeval_X]
  rw [hvec]
  rw [asTheta2_aux_aeval_toRingHom_C, asTheta2_aux_aeval_toRingHom_C,
    asTheta2_aux_aeval_toRingHom_C]

theorem asTheta2_sdualAS2_aux (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hcurve : ∀ k : Fin 5, Work.MotAS.kleinPAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
      (Work.MotC5N3.as2g D g) (Work.MotC5N3.as2c D g) k = 0)
    (hW0 : Work.MotC5N3.asW2 D g 0 ≠ 0) :
    Work.MotC5N3.asTheta2 D g
      (Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g) = 0 := by
  classical
  haveI hC𝕜 : CharP 𝕜 5 := charP_of_algebra_charP_lemma (𝕜 := 𝕜) (K := K)
  have h5R : (5 : as2A D g) = 0 := by
    have h : algebraMap K (as2A D g) ((5 : ℕ) : K) = 0 := by
      rw [CharP.cast_eq_zero K 5, map_zero]
    simpa only [Nat.cast_ofNat, map_ofNat] using h
  -- the two forms of the Klein parameters
  have ha : algebraMap 𝕜 (as2A D g) D.a = algebraMap K (as2A D g) (aK K D) := by
    rw [aK_eq]
    exact (IsScalarTower.algebraMap_apply 𝕜 K (as2A D g) D.a)
  have hb : algebraMap 𝕜 (as2A D g) D.b = algebraMap K (as2A D g) (bK K D) := by
    rw [bK_eq]
    exact (IsScalarTower.algebraMap_apply 𝕜 K (as2A D g) D.b)
  -- the curve hypothesis, in the `𝕜`-form
  have hck : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
        (Work.MotC5N3.as2g D g) (Work.MotC5N3.as2c D g) k = 0 := hcurve
  -- the curve hypothesis, in the `K`-form used by `asRulingEval`
  have hck' : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap K (as2A D g) (aK K D))
        (algebraMap K (as2A D g) (bK K D)) (algebraMap K (as2A D g) g) (as2c D g) k = 0 := by
    intro k
    rw [← ha, ← hb]
    exact hck k
  -- `c 0 = 1`
  have hc0 : as2c D g 0 = 1 := by
    show algebraMap ↥(twistFieldAS D g) (as2A D g) (asY0 D g 0) = 1
    have hy0 : asTwY D g 0 ≠ 0 := asTwY_zero_ne_zero D g hD.1
    have h1 : (asY0 D g 0 : OmA K D) = 1 := by
      change asTwY D g 0 / asTwY D g 0 = 1
      exact div_self hy0
    have h2 : asY0 D g 0 = 1 := Subtype.ext h1
    rw [h2, map_one]
  -- the vanishing of the fourth coordinate of the ruling point
  have hW4 : asW2 D g 4 = 0 :=
    Work.MotAS.asRuleQW_four (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
      (algebraMap K (as2A D g) g) (as2c D g) (RatFunc.X : as2A D g)
  -- the ruling identity: `R(W) = R(W)_0 • c`
  have hRrul : Work.MotAS.kleinRAS (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
      (algebraMap K (as2A D g) g) (asW2 D g)
      = fun j => Work.MotAS.kleinRAS (algebraMap 𝕜 (as2A D g) D.a)
          (algebraMap 𝕜 (as2A D g) D.b) (algebraMap K (as2A D g) g) (asW2 D g) 0 * as2c D g j := by
    funext j
    have h := Work.MotAS.asRulingEval K (as2A D g) h5R (aK K D) (bK K D) g
      (RatFunc.X : as2A D g) (as2c D g) hck' j 0
    rw [hc0, mul_one] at h
    rw [← ha, ← hb] at h
    exact h
  -- `s'(W) = 0`
  have hsW : Work.MotAS.kleinSecDualAS (algebraMap 𝕜 (as2A D g) D.a)
      (algebraMap 𝕜 (as2A D g) D.b) (algebraMap K (as2A D g) g) (asW2 D g) = 0 := by
    have hz : Work.MotAS.kleinPAS0 (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
        (algebraMap K (as2A D g) g) (as2c D g) = 0 := by
      simpa only [Work.MotAS.kleinPAS_zero] using hck 0
    have hz0 : Work.MotAS.kleinPAS0 (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
        (algebraMap K (as2A D g) g)
        (Work.MotAS.kleinRAS (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
          (algebraMap K (as2A D g) g) (asW2 D g)) = 0 := by
      rw [hRrul, Work.MotAS.kleinPAS0_smul, hz, mul_zero]
    have hI2 : Work.MotAS.kleinPAS0 (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
        (algebraMap K (as2A D g) g)
        (Work.MotAS.kleinRAS (algebraMap 𝕜 (as2A D g) D.a) (algebraMap 𝕜 (as2A D g) D.b)
          (algebraMap K (as2A D g) g) (asW2 D g))
        = Work.MotAS.kleinSecDualAS (algebraMap 𝕜 (as2A D g) D.a)
            (algebraMap 𝕜 (as2A D g) D.b) (algebraMap K (as2A D g) g) (asW2 D g)
          * asW2 D g 0 := by
      simpa only [Work.MotAS.kleinPAS_zero] using
        congrFun (Work.MotAS.ASI2 h5R (algebraMap 𝕜 (as2A D g) D.a)
          (algebraMap 𝕜 (as2A D g) D.b) (algebraMap K (as2A D g) g) (asW2 D g)) 0
    rw [hz0] at hI2
    exact (mul_eq_zero.mp hI2.symm).resolve_right hW0
  -- the chart evaluation
  have h1 : asTheta2 D g (Work.MotAS.sdualAS2 (aK K D) (bK K D) g)
      = Work.MotAS.kleinSecDualAS (algebraMap K (as2A D g) (aK K D))
          (algebraMap K (as2A D g) (bK K D)) (algebraMap K (as2A D g) g)
          ![1, asW2 D g (Work.MotAS.asIdx 0) / asW2 D g 0,
            asW2 D g (Work.MotAS.asIdx 1) / asW2 D g 0,
            asW2 D g (Work.MotAS.asIdx 2) / asW2 D g 0, 0] := by
    rw [asTheta2]
    exact aeval_sdualAS2_tchart (asPhi2 D g) (aK K D) (bK K D) g
  rw [h1]
  -- the chart vector is the normalised ruling point
  have hze : (![1, asW2 D g (Work.MotAS.asIdx 0) / asW2 D g 0,
      asW2 D g (Work.MotAS.asIdx 1) / asW2 D g 0,
      asW2 D g (Work.MotAS.asIdx 2) / asW2 D g 0, 0] : Fin 5 → as2A D g)
      = fun i => (asW2 D g 0)⁻¹ * asW2 D g i := by
    funext i
    fin_cases i
    · change (1 : as2A D g) = (asW2 D g 0)⁻¹ * asW2 D g 0
      rw [inv_mul_cancel₀ hW0]
    · change asW2 D g (Work.MotAS.asIdx 0) / asW2 D g 0
          = (asW2 D g 0)⁻¹ * asW2 D g (Work.MotAS.asIdx 0)
      rw [div_eq_mul_inv, mul_comm]
    · change asW2 D g (Work.MotAS.asIdx 1) / asW2 D g 0
          = (asW2 D g 0)⁻¹ * asW2 D g (Work.MotAS.asIdx 1)
      rw [div_eq_mul_inv, mul_comm]
    · change asW2 D g (Work.MotAS.asIdx 2) / asW2 D g 0
          = (asW2 D g 0)⁻¹ * asW2 D g (Work.MotAS.asIdx 2)
      rw [div_eq_mul_inv, mul_comm]
    · change (0 : as2A D g) = (asW2 D g 0)⁻¹ * asW2 D g 4
      rw [hW4, mul_zero]
  rw [hze, Work.MotAS.kleinSecDualAS_smul, ← ha, ← hb, hsW, mul_zero]

end Work.MotC5N3
