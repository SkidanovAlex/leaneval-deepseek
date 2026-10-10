import Mathlib
import Submission.Work.MotK.TwRuling.SdSextDefs
import Submission.Work.MotK.KleinTwRulingQuinticMem

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- The ruling sextic form `sdGform a b σ = R0(A + σ·B)` is the `MvPolynomial`-lift of the
sextic polynomial function `y ↦ kleinTwR0 a b 1 (A(y) + σ·B(y))`: evaluating it at a point `x`
gives the sextic value at `x`.

The proof is pure naturality.  Writing `Φ := (MvPolynomial.aeval x).toRingHom`, the defining
expressions of `kleinTwRuleA`, `kleinTwRuleB` and `kleinTwR` are polynomial in their arguments
and coefficients, so they commute with `Φ`:

* `kleinTwRuleA_map`, `kleinTwRuleB_map` give `Φ (A(X)) = A(x)` and `Φ (B(X)) = B(x)`;
* `kleinTwR_map_apply` gives `Φ (R0(z)) = kleinTwR0 a b 1 (fun i => Φ (z i))`, noting that
  `kleinTwR0` is the zeroth component of `kleinTwR`.

The composite `z i = A(X) i + C σ · B(X) i` then evaluates to `A(x) i + σ · B(x) i`. -/
theorem aeval_sdGform {R : Type*} [CommRing R] (a b σ : R) (x : Fin 5 → R) :
    MvPolynomial.aeval x (Work.MotK.TwRuling.sdGform a b σ)
      = Work.MotK.kleinTwR0 a b 1 (fun i => Work.MotK.kleinTwRuleA a b 1 x i
          + σ * Work.MotK.kleinTwRuleB a b 1 x i) := by
  rw [Work.MotK.TwRuling.sdGform]
  set z : Fin 5 → MvPolynomial (Fin 5) R :=
    fun i => Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
          (fun j => MvPolynomial.X j) i
      + MvPolynomial.C σ * Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C 1) (fun j => MvPolynomial.X j) i with hz
  -- Evaluation of the ruling vectors: `A(X) ↦ A(x)`, `B(X) ↦ B(x)`.
  have hz_eval : ∀ i, (MvPolynomial.aeval x).toRingHom (z i)
      = Work.MotK.kleinTwRuleA a b 1 x i + σ * Work.MotK.kleinTwRuleB a b 1 x i := by
    intro i
    rw [hz]
    rw [map_add, map_mul, Work.MotK.aeval_C_apply_ringHom]
    congr 1
    · rw [congrFun (Work.MotK.kleinTwRuleA_map (MvPolynomial.aeval x).toRingHom
        (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) (fun j => MvPolynomial.X j)) i]
      simp only [Work.MotK.aeval_C_apply_ringHom, Work.MotK.aeval_X_ringHom]
    · rw [congrFun (Work.MotK.kleinTwRuleB_map (MvPolynomial.aeval x).toRingHom
        (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) (fun j => MvPolynomial.X j)) i]
      simp only [Work.MotK.aeval_C_apply_ringHom, Work.MotK.aeval_X_ringHom]
  -- `kleinTwR0` is the zeroth component of the inverse cubic map `kleinTwR`.
  have hR0 : Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z
      = Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0 := by
    simp only [Work.MotK.kleinTwR, Matrix.cons_val_zero]
  rw [hR0]
  change (MvPolynomial.aeval x).toRingHom
    (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0) = _
  rw [Work.MotK.kleinTwR_map_apply (MvPolynomial.aeval x).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1) z 0]
  simp only [Work.MotK.aeval_C_apply_ringHom]
  -- Evaluation of the ruling point.
  have hfun : (fun i => (MvPolynomial.aeval x).toRingHom (z i))
      = (fun i => Work.MotK.kleinTwRuleA a b 1 x i
          + σ * Work.MotK.kleinTwRuleB a b 1 x i) := by
    funext i
    exact hz_eval i
  rw [hfun]
  have hR0' : Work.MotK.kleinTwR a b 1
        (fun i => Work.MotK.kleinTwRuleA a b 1 x i + σ * Work.MotK.kleinTwRuleB a b 1 x i) 0
      = Work.MotK.kleinTwR0 a b 1
        (fun i => Work.MotK.kleinTwRuleA a b 1 x i + σ * Work.MotK.kleinTwRuleB a b 1 x i) := by
    simp only [Work.MotK.kleinTwR, Matrix.cons_val_zero]
  exact hR0'

end Work.MotK.TwRuling
