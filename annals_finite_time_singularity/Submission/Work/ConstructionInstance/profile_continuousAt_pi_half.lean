import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Topology Set
open scoped Topology

namespace Work.ConstructionInstance

/-- **Continuity of the profile at `θ = π/2`.**

Near `θ = π/2` the sign condition `0 ≤ θ` holds everywhere (as `π/2 > 0`), so the odd
extension defining `profile` never uses its negative branch there: `profile p g` agrees, on a
neighbourhood of `(z, π/2)`, with `F_*(z,θ) + g(z,θ)`.  Both summands are continuous there —
`g` because `SmoothNbhd g` is smoothness on an *open* neighbourhood of the quadrant, and
`F_*` because it is the product of the smooth radial factor `Work.FM.Fstar` with the angular
factor `Γ(θ) = (sin θ · cos²θ)^{p/3}`, which is continuous at `θ = π/2` since the base vanishes
there and the exponent `p/3` is positive (`Real.continuousAt_rpow_const` at base `0`). -/
theorem profile_continuousAt_pi_half {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) :
    ContinuousAt (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, Real.pi / 2) := by
  have _ := hvt
  -- `(z, π/2)` lies in the open neighbourhood on which `g` is smooth.
  have hset : (z, Real.pi / 2) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    refine ⟨hz, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- Continuity of `g` at `(z, π/2)` from smoothness on the open set.
  have hgcont : ContinuousAt (Function.uncurry g) (z, Real.pi / 2) :=
    hsmooth.continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hset)
  -- Continuity of the angular factor `Γ(θ) = (sin θ cos²θ)^{p/3}` at `θ = π/2`.
  have hbase : ContinuousAt (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Real.pi / 2) :=
    (Real.continuous_sin.continuousAt).mul ((Real.continuous_cos.continuousAt).pow 2)
  have hGam : ContinuousAt (fun θ : ℝ => Work.Spaces.Gam p θ) (Real.pi / 2) := by
    have h := hbase.rpow continuousAt_const (Or.inr (by positivity : (0:ℝ) < p / 3))
    simpa [Work.Spaces.Gam] using h
  -- Continuity of the smooth radial factor `z ↦ 2z/(1+z)²` at `z`.
  have hFz : ContinuousAt (fun z : ℝ => Work.FM.Fstar z) z :=
    (Work.FM.hasDerivAt_Fstar z hz).continuousAt
  -- Continuity of the uncurried `F_*` at `(z, π/2)`.
  have hFcont : ContinuousAt (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2)
      (z, Real.pi / 2) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (z, Real.pi / 2) :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => q.2) (x := (z, Real.pi / 2)) hGam
        continuous_snd.continuousAt
    have h2 : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2 / Work.Spaces.c p)
        (z, Real.pi / 2) := h1.div_const _
    have h3 : ContinuousAt (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, Real.pi / 2) :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => q.1) (x := (z, Real.pi / 2)) hFz
        continuous_fst.continuousAt
    have h4 : ContinuousAt
        (fun q : ℝ × ℝ => p * (Work.Spaces.Gam p q.2 / Work.Spaces.c p) * Work.FM.Fstar q.1)
        (z, Real.pi / 2) := (continuousAt_const.mul h2).mul h3
    simpa [Work.Construction.Fstar] using h4
  have hcomb : ContinuousAt
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, Real.pi / 2) :=
    hFcont.add hgcont
  -- On the neighbourhood `{θ > 0}` the profile uses its positive branch.
  have hU : {q : ℝ × ℝ | (0:ℝ) < q.2} ∈ 𝓝 (z, Real.pi / 2) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by norm_num [Real.pi_pos])
  have hEv : Function.uncurry (Work.ConstructionInstance.profile p g) =ᶠ[𝓝 (z, Real.pi / 2)]
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) := by
    filter_upwards [hU] with q hq
    exact profile_of_nonneg (le_of_lt hq)
  exact hcomb.congr hEv.symm

end Work.ConstructionInstance
