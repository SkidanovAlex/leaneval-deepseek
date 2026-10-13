/-
Open-class analogue of `Work.FTS.CoercivityFix.Coer1.intL_of`.

`IntFacts.intL_of` proves that the `𝓛`-pairing `𝓛u·u·ρ` is `IntegrableOn` the quadrant as soon
as `u²ρ` and `(D_zu)²ρ` are, but it assumes `Work.FTS.LocData.SmoothQuad u`
(`C^∞` on the *closed* quadrant, in particular flatness at `z = 0`).  On the open route the
datum is only `Work.FTS.EllipticEst.SmoothOpen u`, i.e. `C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)` — which is literally the `Qd` of the closed chapter.

The proof is the same one: smoothness of `u` is used only for continuity of the blocks `D_z u`
and `u` on the quadrant (`SmoothOpen.Dz.continuousOn`, `SmoothOpen.continuousOn`), which
`SmoothQuad` supplied through `continuousOn_mixed_Q` / `continuousOn_f_Q`.  Everything else
(`2|ab| ≤ a² + b²`, the bounded factor `1/(1+z)`, the pointwise identity for `𝓛`) is
smoothness-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

theorem intL_of_O {u : Work.FTS.Galerkin.Fn} {ρ : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hdz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((hs.Dz).continuousOn.mul hs.continuousOn).mul hρc) hρnn hdz hsq
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q hsq hcross
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ) / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hsq
  have h4 := h3.const_mul (-2)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ)
        + (-2) * ((u z θ ^ 2 * ρ z θ) / (1 + z)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q h1 h4
  refine h5.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.L]
  ring

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
