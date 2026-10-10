import Mathlib
import Submission.Work.MotK.TwRuling.SdSextDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- Evaluation of a constant multivariate polynomial (with coefficients in the base ring `R`)
at an algebra homomorphism into an `R`-algebra `A`, in the ring-hom form. -/
theorem aeval_C_algebraMap {R A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x : σ → A) (r : R) :
    (MvPolynomial.aeval x).toRingHom (MvPolynomial.C r : MvPolynomial σ R)
      = algebraMap R A r :=
  MvPolynomial.aeval_C x r

/-- Evaluation of a variable, in the ring-hom form, with coefficients in the base ring `R`. -/
theorem aeval_X_algebraMap {R A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x : σ → A) (s : σ) :
    (MvPolynomial.aeval x).toRingHom (MvPolynomial.X s : MvPolynomial σ R) = x s :=
  MvPolynomial.aeval_X x s

/-- The ruling sextic form `sdGform a b σ = R0(A + σ·B)` is the `MvPolynomial`-lift of the
sextic polynomial function `y ↦ kleinTwR0 a b 1 (A(y) + σ·B(y))`: evaluating it at a point `x`
of an `R`-algebra `A` gives the sextic value at `x`, with the coefficients of `sdGform` sent
along `algebraMap R A`.

The proof is pure naturality.  Writing `Φ := (MvPolynomial.aeval x).toRingHom`, the defining
expressions of `kleinTwRuleA`, `kleinTwRuleB` and `kleinTwR` are polynomial in their arguments
and coefficients, so they commute with `Φ`:

* `kleinTwRuleA_map`, `kleinTwRuleB_map` give `Φ (A(X)) = A(x)` and `Φ (B(X)) = B(x)`;
* `kleinTwR_map_apply` gives `Φ (R0(z)) = kleinTwR0 (Φ a) (Φ b) (Φ 1) (fun i => Φ (z i))`,
  noting that `kleinTwR0` is the zeroth component of `kleinTwR`.

The coefficients evaluate to `algebraMap R A a`, `algebraMap R A b`, `algebraMap R A 1` and the
ruling parameter to `algebraMap R A σ`, and the composite `z i = A(X) i + C σ · B(X) i` evaluates
to `A(x) i + algebraMap R A σ · B(x) i`. -/
theorem aeval_sdGform_gen {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a b σ : R) (x : Fin 5 → A) :
    MvPolynomial.aeval x (Work.MotK.TwRuling.sdGform a b σ)
      = Work.MotK.kleinTwR0 (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1)
          (fun i => Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A 1) x i
            + algebraMap R A σ * Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A 1) x i) := by
  have hC : ∀ (r : R), (MvPolynomial.aeval x).toRingHom
      (MvPolynomial.C r : MvPolynomial (Fin 5) R) = algebraMap R A r :=
    fun r => Work.MotK.TwRuling.aeval_C_algebraMap x r
  have hX : ∀ (s : Fin 5), (MvPolynomial.aeval x).toRingHom
      (MvPolynomial.X s : MvPolynomial (Fin 5) R) = x s :=
    fun s => Work.MotK.TwRuling.aeval_X_algebraMap x s
  rw [Work.MotK.TwRuling.sdGform]
  set z : Fin 5 → MvPolynomial (Fin 5) R :=
    fun i => Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
          (fun j => MvPolynomial.X j) i
      + MvPolynomial.C σ * Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C 1) (fun j => MvPolynomial.X j) i with hz
  have hz_eval : ∀ i, (MvPolynomial.aeval x).toRingHom (z i)
      = Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1) x i
        + algebraMap R A σ * Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b)
            (algebraMap R A 1) x i := by
    intro i
    rw [hz, map_add, map_mul]
    congr 1
    · rw [congrFun (Work.MotK.kleinTwRuleA_map (MvPolynomial.aeval x).toRingHom
        (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) (fun j => MvPolynomial.X j)) i]
      simp only [hC, hX]
    · congr 1
      · exact hC σ
      · rw [congrFun (Work.MotK.kleinTwRuleB_map (MvPolynomial.aeval x).toRingHom
          (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) (fun j => MvPolynomial.X j)) i]
        simp only [hC, hX]
  have hR0 : Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z
      = Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0 := by
    simp only [Work.MotK.kleinTwR, Matrix.cons_val_zero]
  rw [hR0]
  change (MvPolynomial.aeval x).toRingHom
    (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0) = _
  rw [Work.MotK.kleinTwR_map_apply (MvPolynomial.aeval x).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0]
  simp only [hC]
  have hfun : (fun i => (MvPolynomial.aeval x).toRingHom (z i))
      = (fun i => Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1) x i
          + algebraMap R A σ * Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A 1) x i) := by
    funext i
    exact hz_eval i
  rw [hfun]
  have hR0' : Work.MotK.kleinTwR (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1)
        (fun i => Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1) x i
          + algebraMap R A σ * Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A 1) x i) 0
      = Work.MotK.kleinTwR0 (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1)
        (fun i => Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b) (algebraMap R A 1) x i
          + algebraMap R A σ * Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b)
              (algebraMap R A 1) x i) := by
    simp only [Work.MotK.kleinTwR, Matrix.cons_val_zero]
  exact hR0'

end Work.MotK.TwRuling
