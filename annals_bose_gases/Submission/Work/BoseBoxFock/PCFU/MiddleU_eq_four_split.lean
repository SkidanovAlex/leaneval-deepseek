import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chint_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.MiddleU_eq_four_split`

The **integral form** of `PCFU.MiddleU_eq_four`: integrating the pointwise identity

    `MiddleU(x,y,u) = ℓ^{-9/2}·(ChAU(y,x,u) − ChBU(y,x,u) − ChCU(y,x,u) + ChDU(y,x,u))`

against the two-slot test function `Θ(q.1)·θ_ℓ(q.1 i)·Θ(update)` gives

    `∫ Θ(q.1)θ(q.1 i)MiddleU(q.1 j,q.2.1,q.2.2)Θ(update)
       = ℓ^{-9/2}·(chAint − chBint − chCint + chDint)`

(`chAint` … `chDint` are the four channel integrals of `PCFU/ChWordChains`).  The proof is
linearity of the Bochner integral, the four integrability facts being supplied by the PROVED
`PCFU.chint_integrable`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem MiddleU_eq_four_integral_via_integrable {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N),
      fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k)
        = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * (chAint v h fc fu μ N i j Θ
              - chBint v h fc fu μ N i j Θ
              - chCint v h fc fu μ N i j Θ
              + chDint v h fc fu μ N i j Θ) := by
  obtain ⟨hA, hB, hC, hD⟩ := chint_integrable v h fc fu μ N i j Θ hΘm hΘb hΘs
  have hpt : ∀ q : Submission.BoseGases.X n × (E3 × E3),
      ((Θ q.1 : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
        * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
        * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
      = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
        * (chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q
            - chCintand v h fc fu μ N i j Θ q + chDintand v h fc fu μ N i j Θ q) := fun q => by
    simp only [chAintand, chBintand, chCintand, chDintand]
    rw [MiddleU_eq_four v h fc fu μ N (q.1 j) q.2.1 q.2.2 hsub]
    ring
  calc (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
            * (chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q
                - chCintand v h fc fu μ N i j Θ q + chDintand v h fc fu μ N i j Θ q) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * ∫ q : Submission.BoseGases.X n × (E3 × E3),
              (chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q
                - chCintand v h fc fu μ N i j Θ q + chDintand v h fc fu μ N i j Θ q) :=
        integral_const_mul _ _
    _ = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * ((∫ q : Submission.BoseGases.X n × (E3 × E3), chAintand v h fc fu μ N i j Θ q)
              - (∫ q : Submission.BoseGases.X n × (E3 × E3), chBintand v h fc fu μ N i j Θ q)
              - (∫ q : Submission.BoseGases.X n × (E3 × E3), chCintand v h fc fu μ N i j Θ q)
              + (∫ q : Submission.BoseGases.X n × (E3 × E3), chDintand v h fc fu μ N i j Θ q)) := by
        have e1 : (∫ q : Submission.BoseGases.X n × (E3 × E3),
              (chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q))
            = (∫ q : Submission.BoseGases.X n × (E3 × E3), chAintand v h fc fu μ N i j Θ q)
              - (∫ q : Submission.BoseGases.X n × (E3 × E3), chBintand v h fc fu μ N i j Θ q) :=
          MeasureTheory.integral_sub hA hB
        have e2 : (∫ q : Submission.BoseGases.X n × (E3 × E3),
              ((chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q)
                - chCintand v h fc fu μ N i j Θ q))
            = (∫ q : Submission.BoseGases.X n × (E3 × E3),
                (chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q))
              - (∫ q : Submission.BoseGases.X n × (E3 × E3), chCintand v h fc fu μ N i j Θ q) :=
          MeasureTheory.integral_sub (hA.sub hB) hC
        have e3 : (∫ q : Submission.BoseGases.X n × (E3 × E3),
              ((chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q)
                - chCintand v h fc fu μ N i j Θ q)
              + chDintand v h fc fu μ N i j Θ q)
            = (∫ q : Submission.BoseGases.X n × (E3 × E3),
                ((chAintand v h fc fu μ N i j Θ q - chBintand v h fc fu μ N i j Θ q)
                  - chCintand v h fc fu μ N i j Θ q))
              + (∫ q : Submission.BoseGases.X n × (E3 × E3), chDintand v h fc fu μ N i j Θ q) :=
          MeasureTheory.integral_add ((hA.sub hB).sub hC) hD
        rw [e3, e2, e1]
    _ = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * (chAint v h fc fu μ N i j Θ
              - chBint v h fc fu μ N i j Θ
              - chCint v h fc fu μ N i j Θ
              + chDint v h fc fu μ N i j Θ) := by
        rw [chAint_eq_integral, chBint_eq_integral, chCint_eq_integral, chDint_eq_integral]

end Work.BoseBoxFock.PCFU
