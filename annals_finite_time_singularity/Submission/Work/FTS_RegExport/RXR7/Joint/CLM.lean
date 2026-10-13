import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

/-! ## §1  Elementary continuous-linear-map helpers

`ℝ × ℝ × ℝ` is right-associated: `p = (p.1, p.2.1, p.2.2)`.  We record the three coordinate
functionals, the CLM whose coordinate vector is `(a,b,c)`, the CLM `(z,θ) ↦ a z + b θ`, and the
"boundary" CLM `(z,θ,τ) ↦ L (z,θ) + c τ`. -/

/-- `p ↦ p.1`. -/
def p1 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- `p ↦ p.2.1`. -/
def p2 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- `p ↦ p.2.2`. -/
def p3 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The CLM `(z,θ,τ) ↦ a z + b θ + c τ`. -/
def tripleCLM (a b c : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := a • p1 + b • p2 + c • p3

/-- The CLM `(z,θ) ↦ a z + b θ`. -/
def pairCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • (ContinuousLinearMap.fst ℝ ℝ ℝ) + b • (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The CLM `(z,θ,τ) ↦ L (z,θ) + c τ` of the boundary derivative. -/
def bdryCLM (L : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  L.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
    + c • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

theorem tripleCLM_apply (a b c : ℝ) (v : ℝ × ℝ × ℝ) :
    tripleCLM a b c v = a * v.1 + b * v.2.1 + c * v.2.2 := by
  simp [tripleCLM, p1, p2, p3]

theorem pairCLM_apply (a b : ℝ) (v : ℝ × ℝ) : pairCLM a b v = a * v.1 + b * v.2 := by
  simp [pairCLM]

theorem bdryCLM_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) (v : ℝ × ℝ × ℝ) :
    bdryCLM L c v = L (v.1, v.2.1) + c * v.2.2 := by
  simp [bdryCLM]

theorem tripleCLM_add (a b c a' b' c' : ℝ) :
    tripleCLM a b c + tripleCLM a' b' c' = tripleCLM (a + a') (b + b') (c + c') := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [add_apply, tripleCLM_apply, tripleCLM_apply, tripleCLM_apply]
  ring

theorem pairCLM_add (a b a' b' : ℝ) :
    pairCLM a b + pairCLM a' b' = pairCLM (a + a') (b + b') := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [add_apply, pairCLM_apply, pairCLM_apply, pairCLM_apply]
  ring

theorem bdryCLM_pairCLM (a b c : ℝ) : bdryCLM (pairCLM a b) c = tripleCLM a b c := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [bdryCLM_apply, tripleCLM_apply, pairCLM_apply]

/-- A CLM `(ℝ×ℝ×ℝ) →L ℝ` is determined by its values on the three coordinate vectors. -/
theorem clm_ext_triple {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {a b c : ℝ}
    (h1 : L (1, 0, 0) = a) (h2 : L (0, 1, 0) = b) (h3 : L (0, 0, 1) = c) :
    L = tripleCLM a b c := by
  refine ContinuousLinearMap.ext fun p => ?_
  have hp : p = p.1 • (1, 0, 0) + p.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) + p.2.2 • (0, 0, 1) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3, tripleCLM_apply]
  simp only [smul_eq_mul]
  ring

/-- A CLM `(ℝ×ℝ) →L ℝ` is determined by its values on the two coordinate vectors. -/
theorem clm_ext_pair {L : (ℝ × ℝ) →L[ℝ] ℝ} {a b : ℝ}
    (h1 : L (1, 0) = a) (h2 : L (0, 1) = b) : L = pairCLM a b := by
  refine ContinuousLinearMap.ext fun q => ?_
  have hq : q = q.1 • (1, 0) + q.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hq]
  rw [map_add, map_smul, map_smul, h1, h2, pairCLM_apply]
  simp only [smul_eq_mul]
  ring

/-- The first coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e1 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (1, 0, 0) = deriv (fun z => Φ (z, x.2.1, x.2.2)) x.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, x.2.1, x.2.2)) (1, 0, 0) x.1 := by
    simpa using (hasDerivAt_id x.1).prodMk
      ((hasDerivAt_const x.1 x.2.1).prodMk (hasDerivAt_const x.1 x.2.2))
  have hd := (hL.comp_hasDerivAt x.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

/-- The second coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e2 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 1, 0) = deriv (fun θ => Φ (x.1, θ, x.2.2)) x.2.1 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, t, x.2.2)) (0, 1, 0) x.2.1 := by
    simpa using (hasDerivAt_const x.2.1 x.1).prodMk
      ((hasDerivAt_id x.2.1).prodMk (hasDerivAt_const x.2.1 x.2.2))
  have hd := (hL.comp_hasDerivAt x.2.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

/-- The third coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e3 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 0, 1) = deriv (fun τ => Φ (x.1, x.2.1, τ)) x.2.2 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, x.2.1, t)) (0, 0, 1) x.2.2 := by
    simpa using (hasDerivAt_const x.2.2 x.1).prodMk
      ((hasDerivAt_const x.2.2 x.2.1).prodMk (hasDerivAt_id x.2.2))
  have hd := (hL.comp_hasDerivAt x.2.2 hc).deriv
  simpa [Function.comp_def] using hd.symm

theorem fderiv_apply_2d_1 {Φ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (1, 0) = deriv (fun z => Φ (z, x.2)) x.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, x.2)) (1, 0) x.1 := by
    simpa using (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hd := (hL.comp_hasDerivAt x.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

theorem fderiv_apply_2d_2 {Φ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 1) = deriv (fun θ => Φ (x.1, θ)) x.2 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, t)) (0, 1) x.2 := by
    simpa using (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have hd := (hL.comp_hasDerivAt x.2 hc).deriv
  simpa [Function.comp_def] using hd.symm

end Work.FTS_RegExport.RXR7
