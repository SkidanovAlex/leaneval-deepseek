import Mathlib
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.ASTransport
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.Ker4

open MvPolynomial

/-- The constant embedding `MvPolynomial.C` commutes with the source Galois matrix `asM`
evaluated at `asRoot g`. -/
lemma C_asM_Kb (𝕜 : Type) [Field 𝕜] (g : RatFunc 𝕜) (i j : Fin 5) :
    (MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) :
        MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))
      = Work.MotAS.asM (MvPolynomial.C (Work.MotV5.asRoot g)) i j := by
  simp only [Work.MotAS.asM, Matrix.of_apply, map_pow, map_add, map_natCast]

/-- The constant embedding `MvPolynomial.C` commutes with the target Galois matrix `asN`
evaluated at `asRoot g`. -/
lemma C_asN_Kb (𝕜 : Type) [Field 𝕜] (g : RatFunc 𝕜) (k j : Fin 5) :
    (MvPolynomial.C (Work.MotAS.asN (Work.MotV5.asRoot g) k j) :
        MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))
      = Work.MotAS.asN (MvPolynomial.C (Work.MotV5.asRoot g)) k j := by
  simp only [Work.MotAS.asN, Matrix.of_apply, map_pow, map_add, map_natCast, map_mul, map_ofNat]

/-- `MvPolynomial.aeval` commutes with the Pfaffian `kleinP` in the coordinates `X i`. -/
lemma aeval_kleinP_X_Kb (𝕜 : Type) [Field 𝕜] (a b : Work.MotV.Kb 𝕜)
    (σ : Fin 5 → MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) (k : Fin 5) :
    MvPolynomial.aeval σ (Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
        (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b) σ k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Work.MotK.fin5_zero, Work.MotK.fin5_one,
      Work.MotK.fin5_two, Work.MotK.fin5_three, Work.MotK.fin5_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, map_add, map_sub, map_mul, map_pow, map_neg]

theorem asTransportP_mv (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (g : RatFunc 𝕜) (k : Fin 5) :
    MvPolynomial.aeval
        (fun i : Fin 5 => ∑ j : Fin 5,
          MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j)
        (Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i => MvPolynomial.X i) k)
      = ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asN (Work.MotV5.asRoot g) k j)
          * Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
              (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
              (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) j := by
  have h5 : (5 : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) = 0 := CharP.cast_eq_zero _ 5
  have hw : (MvPolynomial.C (Work.MotV5.asRoot g) :
      MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) ^ 5
      = MvPolynomial.C (Work.MotV5.asRoot g)
        + MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) := by
    rw [← map_pow, ← map_add]
    congr 1
    have h := Work.MotV5.asRoot_spec g
    linear_combination (norm := first | refl_ring1 | ring1) h
  set σ : Fin 5 → MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
      fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j with hσ
  have hstep : MvPolynomial.aeval σ
        (Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)) σ k :=
    aeval_kleinP_X_Kb 𝕜 _ _ σ k
  have hσ' : σ = fun i : Fin 5 => ∑ j : Fin 5,
      Work.MotAS.asM (MvPolynomial.C (Work.MotV5.asRoot g)) i j * MvPolynomial.X j := by
    funext i
    simp only [hσ, C_asM_Kb 𝕜 g]
  have htr := Work.MotAS.asTransportP
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
      (MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g))
      (MvPolynomial.C (Work.MotV5.asRoot g)) h5 hw (fun i => MvPolynomial.X i)
  rw [hstep, hσ', htr, Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [C_asN_Kb 𝕜 g]
  rfl

end Work.MotAS.Ker4
