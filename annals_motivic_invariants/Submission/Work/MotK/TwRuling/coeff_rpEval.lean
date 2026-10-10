import Mathlib
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.MotK.KleinTwRMap
import Submission.Work.MotK.KleinTwRuleMem
import Submission.Work.MotK.KleinTwRulingQuinticMem

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-! ## Naturality lemmas

The whole construction is a polynomial expression built from ring operations, so it commutes with
the evaluation `MvPolynomial.aeval κ` (`Polynomial.map` on the `T`-side).  The two elementary
naturality facts are recorded here first. -/

/-- The evaluation of a constant multivariate polynomial, in the `RingHom`-coercion form (the form
produced by `Polynomial.map_C`). -/
theorem aeval_toRingHom_C {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (κ : σ → S) (r : R) :
    (MvPolynomial.aeval κ).toRingHom (MvPolynomial.C r : MvPolynomial σ R) = algebraMap R S r :=
  MvPolynomial.aeval_C κ r

/-- The evaluation of a variable, in the `RingHom`-coercion form. -/
theorem aeval_toRingHom_X {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (κ : σ → S) (i : σ) :
    (MvPolynomial.aeval κ).toRingHom (MvPolynomial.X i : MvPolynomial σ R) = κ i :=
  MvPolynomial.aeval_X κ i

/-- Naturality of the first ruling vector `qA` under `MvPolynomial.aeval`. -/
theorem aeval_qA (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (a b h : R) (κ : Fin 5 → S) (k : Fin 5) :
    (MvPolynomial.aeval κ).toRingHom (qA R a b h k)
      = Work.MotK.kleinTwRuleA (algebraMap R S a) (algebraMap R S b) (algebraMap R S h) κ k := by
  have hkey := congrFun (Work.MotK.kleinTwRuleA_map (MvPolynomial.aeval κ).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.X i)) k
  rw [show qA R a b h k = Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h) (fun i => MvPolynomial.X i) k from rfl]
  rw [hkey]
  simp only [aeval_toRingHom_C, aeval_toRingHom_X]

/-- Naturality of the second ruling vector `qB` under `MvPolynomial.aeval`.

(⚠ The `_map` suffix avoids a name clash with `Work.MotK.TwRuling.aeval_qB` of
`Submission/Work/MotK/TwRuling/sdCoeff6_notMem_twIdeal6.lean`, a different statement about the
same symbol.) -/
theorem aeval_qB_map (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (a b h : R) (κ : Fin 5 → S) (k : Fin 5) :
    (MvPolynomial.aeval κ).toRingHom (qB R a b h k)
      = Work.MotK.kleinTwRuleB (algebraMap R S a) (algebraMap R S b) (algebraMap R S h) κ k := by
  have hkey := congrFun (Work.MotK.kleinTwRuleB_map (MvPolynomial.aeval κ).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.X i)) k
  rw [show qB R a b h k = Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h) (fun i => MvPolynomial.X i) k from rfl]
  rw [hkey]
  simp only [aeval_toRingHom_C, aeval_toRingHom_X]

/-- `Polynomial.map` commutes with the substitution defining `coeffPoly`: the polynomial
`R₀(A + T·B)` is natural. -/
theorem map_coeffPoly (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (a b h : R) (κ : Fin 5 → S) :
    Polynomial.map (MvPolynomial.aeval κ).toRingHom (coeffPoly R a b h)
      = Work.MotK.kleinTwR0 (Polynomial.C (algebraMap R S a)) (Polynomial.C (algebraMap R S b))
          (Polynomial.C (algebraMap R S h))
          (fun k => Polynomial.C (Work.MotK.kleinTwRuleA (algebraMap R S a) (algebraMap R S b)
                (algebraMap R S h) κ k)
            + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB (algebraMap R S a)
                (algebraMap R S b) (algebraMap R S h) κ k)) := by
  have hmain : Polynomial.map (MvPolynomial.aeval κ).toRingHom (coeffPoly R a b h)
      = Work.MotK.kleinTwR0 (Polynomial.C ((MvPolynomial.aeval κ).toRingHom (MvPolynomial.C a)))
          (Polynomial.C ((MvPolynomial.aeval κ).toRingHom (MvPolynomial.C b)))
          (Polynomial.C ((MvPolynomial.aeval κ).toRingHom (MvPolynomial.C h)))
          (fun k => Polynomial.C ((MvPolynomial.aeval κ).toRingHom (qA R a b h k))
            + Polynomial.X * Polynomial.C ((MvPolynomial.aeval κ).toRingHom (qB R a b h k))) := by
    simp only [coeffPoly, Work.MotK.kleinTwR0, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_C,
      Polynomial.map_X]
  rw [hmain]
  simp only [aeval_toRingHom_C, aeval_qA, aeval_qB_map]

/-- Naturality of the whole construction: the `T^j` coefficient of `rpEval K D h` (the ruling
polynomial `R₀(A(κ)+T·B(κ))` over the function field `OmG K D`, `κ = twCoordG K D h`) equals
`MvPolynomial.aeval κ (sdCoeff6 (KbG K) a b h j)`.

Route: `Polynomial.coeff_map` reduces this to `Polynomial.map (MvPolynomial.aeval κ) (coeffPoly …) =
rpEval K D h`; prove that by unfolding `coeffPoly`, `rpEval`, `qA`, `qB`, `kleinTwR0` and pushing
`Polynomial.map`/`MvPolynomial.aeval` through `add/mul/pow/neg/C/X` (`Polynomial.map_add`,
`map_mul`, `map_pow`, `map_C`, `map_X`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X`), using
`IsScalarTower.algebraMap_apply` for `algebraMap (KbG K) (OmG K D) ∘ algebraMap K (KbG K)`.
No hypotheses (`D.Good`, `h ≠ 0`) are needed. -/
theorem coeff_rpEval (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) (j : ℕ) :
    (Work.MotK.TwRuling.rpEval K D h).coeff j
      = MvPolynomial.aeval (Work.MotK.twCoordG K D h)
          (Work.MotK.TwRuling.sdCoeff6 (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
            (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h) j) := by
  have hmap : Polynomial.map (MvPolynomial.aeval (Work.MotK.twCoordG K D h)).toRingHom
      (coeffPoly (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h))
      = rpEval K D h := by
    rw [map_coeffPoly]
    simp only [rpEval, ← IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)]
  have hcoeff := congrArg (fun p : Polynomial (Work.MotK.OmG K D) => p.coeff j) hmap
  rw [Polynomial.coeff_map] at hcoeff
  exact hcoeff.symm

end Work.MotK.TwRuling
