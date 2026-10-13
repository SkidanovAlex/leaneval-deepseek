/-
  annals_wilkies_conjecture, AREA E3, frame step: the derivative of the straightening map `PhiC`.

  `Frame.Setup` defines `PhiC c h ι z = (uCoord k ι z, fun a => eaEvalC c (h a) z)`, the coordinate
  map whose local inverse straightens `{h = 0}`.  Its derivative at `z` is the block-triangular
  continuous linear map `DPhiC c h ι z` defined here: the first block is the projection to the
  `ι`-complement coordinates, the second block is the (complexified) `ι`-Jacobian of `h` at `z`.
-/
import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E

variable {k r j : ℕ}

/-- The derivative of `PhiC c h ι` at the point `z`, as a continuous `ℂ`-linear map
`(Fin k → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ))`.  In blocks it is
`[[proj_ιᶜ, 0], [*, M]]` with `M a i = eaEvalC c (eaD c i (h a)) z`. -/
def DPhiC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : (Fin k → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) :=
  (ContinuousLinearMap.pi fun i : U k ι =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1).prod
    (ContinuousLinearMap.pi fun a : Fin j =>
      ∑ i : Fin k, (eaEvalC c (eaD c i (h a)) z) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)

/-- The `U`-component of `DPhiC` is the projection to the `ι`-complement coordinates, i.e. applied
to `v` it is `uCoord k ι v`.  This makes the first component of `PhiC` transparently linear. -/
theorem DPhiC_fst (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z v : Fin k → ℂ) :
    (DPhiC c h ι z v).1 = uCoord k ι v := rfl

/-- The `Fin j`-component of `DPhiC` is the linearised `ι`-Jacobian of `h`. -/
theorem DPhiC_snd (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z v : Fin k → ℂ) (a : Fin j) :
    (DPhiC c h ι z v).2 a = ∑ i : Fin k, eaEvalC c (eaD c i (h a)) z * v i := by
  simp [DPhiC, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]

end

end Work.WilE3.Frame
