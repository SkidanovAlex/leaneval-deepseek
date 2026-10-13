import Mathlib
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

open WilkiesDesign.E

/-- The derivative of the straightening map `PhiC c h ι z = (uCoord k ι z, eaEvalC c (h ·) z)` at
an arbitrary complex point `z` is `DPhiC c h ι z`. -/
theorem hasFDerivAt_PhiC {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (z : Fin k → ℂ) :
    HasFDerivAt (Work.WilE3.Frame.PhiC c h ι)
      (Work.WilE3.Frame.DPhiC c h ι z) z := by
  -- The first block: the `ι`-complement coordinates are linear.
  have h1 : HasFDerivAt (fun z : Fin k → ℂ => uCoord k ι z)
      ((ContinuousLinearMap.pi fun i : U k ι =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1) :
        (Fin k → ℂ) →L[ℂ] (U k ι → ℂ)) z := by
    have hlin := (ContinuousLinearMap.pi (fun i : U k ι =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1)).hasFDerivAt (x := z)
    simpa [uCoord, ContinuousLinearMap.pi_apply] using hlin
  -- The second block: the complexified chain polynomials, differentiated by `eaEvalC_fderiv_analytic`.
  have h2 : HasFDerivAt (fun z : Fin k → ℂ => fun a => eaEvalC c (h a) z)
      ((ContinuousLinearMap.pi fun a : Fin j => ∑ i : Fin k,
        (eaEvalC c (eaD c i (h a)) z) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i) :
        (Fin k → ℂ) →L[ℂ] (Fin j → ℂ)) z := by
    refine hasFDerivAt_pi.mpr (fun a => ?_)
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (h a) z).2
  exact h1.prodMk h2

end Work.WilE3.Frame
