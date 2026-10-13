import Mathlib
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval

namespace Work.WilE5.Flat
open WilkiesDesign WilkiesDesign.E

/-- The Fréchet derivative of the vector-valued map `z ↦ (a ↦ eaEval c (h a) z)` acts on a
direction `v` by the directional derivatives: component `a` of the derivative at `x` applied to
`v` is `∑ i, eaEval c (eaD c i (h a)) x * v i`. -/
theorem fderiv_pi_eaEval_apply {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (x v : Fin k → ℝ) (a : Fin j) :
    fderiv ℝ (fun z : Fin k → ℝ => fun a : Fin j => eaEval c (h a) z) x v a
      = ∑ i : Fin k, eaEval c (eaD c i (h a)) x * v i := by
  have hpi : HasFDerivAt (fun z : Fin k → ℝ => fun a : Fin j => eaEval c (h a) z)
      (ContinuousLinearMap.pi fun a : Fin j =>
        ∑ i : Fin k, (eaEval c (eaD c i (h a)) x) • ContinuousLinearMap.proj i) x :=
    hasFDerivAt_pi.mpr fun a => Work.WilE5.Calc.hasFDerivAt_eaEval c (h a) x
  rw [hpi.fderiv]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

end Work.WilE5.Flat
