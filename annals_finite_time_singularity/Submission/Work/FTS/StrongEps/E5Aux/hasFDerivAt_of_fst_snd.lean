import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E5Aux.C1LocUnifAux
import Submission.Work.FTS.StrongEps.E5Aux.abs_sub_sub_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.StrongEps.E5Aux

/-- `toSpanSingleton ℝ c` is multiplication by `c` on `ℝ`. -/
theorem toSpanSingleton_real_eq_smul_one (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • (1 : ℝ →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **A function on `ℝ × E` with continuous partial derivatives is differentiable.**

If, on an open set `V ∋ p`, the `x`-partial derivatives of `f` exist (with values `g₁`) and
the `y`-partial Fréchet derivatives exist (with values `g₂`), and both `g₁` and `g₂` are
continuous on `V`, then `f` is (strictly) Fréchet differentiable at `p` with derivative
`(x, y) ↦ g₁ p * x + g₂ p y = clmHead E (g₁ p) (g₂ p)`. -/
theorem hasFDerivAt_of_fst_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} {g₁ : ℝ × E → ℝ} {g₂ : ℝ × E → E →L[ℝ] ℝ} {V : Set (ℝ × E)}
    {p : ℝ × E} (hV : IsOpen V) (hp : p ∈ V)
    (h₁ : ∀ q ∈ V, HasDerivAt (fun x : ℝ => f (x, q.2)) (g₁ q) q.1)
    (h₂ : ∀ q ∈ V, HasFDerivAt (fun y : E => f (q.1, y)) (g₂ q) q.2)
    (hc₁ : ContinuousOn g₁ V) (hc₂ : ContinuousOn g₂ V) :
    HasFDerivAt f (Work.FTS.StrongEps.E5Aux.clmHead E (g₁ p) (g₂ p)) p := by
  have hmem : V ∈ 𝓝 p := hV.mem_nhds hp
  -- the `x`-partial derivatives, as continuous linear functionals
  have hdf₁ : ∀ᶠ v in 𝓝 p,
      HasFDerivAt (fun x : ℝ => f (x, v.2)) (g₁ v • (1 : ℝ →L[ℝ] ℝ)) v.1 := by
    filter_upwards [hmem] with v hv
    exact (h₁ v hv).hasFDerivAt.congr_fderiv (toSpanSingleton_real_eq_smul_one (g₁ v))
  have hdf₂ : ∀ᶠ v in 𝓝 p,
      HasFDerivAt (fun y : E => f (v.1, y)) (g₂ v) v.2 := by
    filter_upwards [hmem] with v hv
    exact h₂ v hv
  have hcf₁ : ContinuousAt (fun v : ℝ × E => g₁ v • (1 : ℝ →L[ℝ] ℝ)) p :=
    Filter.Tendsto.smul_const (hc₁.continuousAt hmem) (1 : ℝ →L[ℝ] ℝ)
  have hcf₂ : ContinuousAt (fun v : ℝ × E => g₂ v) p := hc₂.continuousAt hmem
  have hstrict := hasStrictFDerivAt_uncurry_coprod
    (f := fun (x : ℝ) (y : E) => f (x, y))
    (f₁ := fun (x : ℝ) (y : E) => g₁ (x, y) • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun (x : ℝ) (y : E) => g₂ (x, y))
    (u := p) hdf₁ hdf₂ hcf₁ hcf₂
  refine hstrict.hasFDerivAt.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  have hA : (↿fun (x : ℝ) (y : E) => g₁ (x, y) • (1 : ℝ →L[ℝ] ℝ)) p = g₁ p • 1 := rfl
  have hB : (↿fun (x : ℝ) (y : E) => g₂ (x, y)) p = g₂ p := rfl
  rw [ContinuousLinearMap.coprod_apply, clmHead_apply, hA, hB,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]

end Work.FTS.StrongEps.E5Aux
