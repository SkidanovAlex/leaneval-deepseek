import Mathlib
import Submission.Work.EQ.H0_regular_aux

/-!
# Holomorphicity of `psiC ∘ p ∘ G`

`psiC q = ψ₁(q)ψ₂(q)` is the invariant parameter `ψ = ψ₁ψ₂` of a chain, read on a component
`↥(connectedComponent P)` of Rychlik's connection surface `H0 a h`.

Rychlik's local structure theorem for `H0` (`Work.EQ.psi_local_chart`, the analytic half of
`Work.EQ.H0_structure`) says that near every point of `H0` the invariant parameter `ψ` agrees
with an analytic function `Γ` of the stable coordinate `ψ₁`.  Consequently, as soon as `ψ₁` is
complex differentiable at a point `y` of the component, so is `ψ`:

* `psiC_mdifferentiableAt` — `psiC` is `MDifferentiableAt` at `y` provided `ψ₁` is.

The target lemma is then pure chain rule: `psiC ∘ p` is complex differentiable wherever `p`
and `ψ₁` are, and composing with an `MDifferentiableAt` map `G : ℂ → ℍ` gives the result.
This is the analytic input used by `Work.EQ.H0_disc_cover_holomorphic`.

Everything here is stated in terms of the manifold structures (`modelWithCornersSelf ℂ ℂ`)
carried by `UpperHalfPlane` (its induced singleton charted space) and by the component of `H0`
(an arbitrary `ChartedSpace ℂ` instance, as supplied by the uniformization construction).
-/

open scoped Manifold Topology
open Complex Metric Filter

namespace Work.EQ

/-- **`psiC` is complex differentiable where `ψ₁` is.**  The local chart of `ψ` on `H0`
(`Work.EQ.psi_local_chart`) writes `ψ = Γ ∘ ψ₁` near `y` with `Γ` analytic, so the chain rule
for manifolds applies. -/
theorem psiC_mdifferentiableAt {a : ℝ} {h : ℂ → ℂ} {P : H0 a h}
    [ChartedSpace ℂ ↥(connectedComponent P)] (hsect : LocalSections a h)
    (y : ↥(connectedComponent P))
    (hψmd : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => ((q : H0 a h) : ChainData).2.1) y) :
    MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => psiC q) y := by
  obtain ⟨ρ, Γ, hρ, hΓ, hΓy, hchart⟩ :=
    psi_local_chart hsect (((y : H0 a h) : ChainData)) (y : H0 a h).2
  -- the underlying chain of `q : ↥(connectedComponent P)` is continuous at `y`
  have hcont : ContinuousAt (fun q : ↥(connectedComponent P) => ((q : H0 a h) : ChainData)) y :=
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt
  -- pull the local chart back along it: `psiC = Γ ∘ ψ₁` near `y`
  have hev : (fun q : ↥(connectedComponent P) => psiC q) =ᶠ[𝓝 y]
      (fun q : ↥(connectedComponent P) => Γ (((q : H0 a h) : ChainData).2.1)) := by
    filter_upwards [hcont.tendsto.eventually hchart] with q hq
    exact hq (q : H0 a h).2
  have hΓat : DifferentiableAt ℂ Γ (((y : H0 a h) : ChainData).2.1) :=
    (hΓ _ (by rw [Metric.mem_ball, dist_self]; exact hρ)).differentiableAt
  have hfin : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => Γ (((q : H0 a h) : ChainData).2.1)) y :=
    hΓat.mdifferentiableAt.comp y hψmd
  exact MDifferentiableAt.congr_of_eventuallyEq hfin hev

/-- **`psiC ∘ p ∘ G` is complex differentiable.**  `ψ = ψ₁ψ₂` is a complex differentiable
function of `ψ₁` on the component (`psiC_mdifferentiableAt`), `ψ₁` is complex differentiable on
the component and `p : ℍ → ↥(connectedComponent P)` is holomorphic, so `psiC ∘ p` is holomorphic
on the upper half plane; composing with the holomorphic germ `G : ℂ → ℍ` gives the claim. -/
theorem psiC_comp_differentiableAt {a : ℝ} {h : ℂ → ℂ} {P : Work.EQ.H0 a h}
    [ChartedSpace ℂ ↥(connectedComponent P)]
    (hsect : Work.EQ.LocalSections a h)
    {p : UpperHalfPlane → ↥(connectedComponent P)}
    (hpmd : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) p)
    (hψmd : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => ((q : Work.EQ.H0 a h) : Work.EQ.ChainData).2.1))
    {G : ℂ → UpperHalfPlane} {z : ℂ}
    (hG : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G z) :
    DifferentiableAt ℂ (fun w : ℂ => Work.EQ.psiC (p (G w))) z := by
  have hA : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => psiC q) (p (G z)) :=
    psiC_mdifferentiableAt hsect (p (G z)) (hψmd.mdifferentiableAt)
  have hpg : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun w : ℂ => p (G w)) z := hpmd.mdifferentiableAt.comp z hG
  have hcomp := hA.comp z hpg
  exact hcomp.differentiableAt

end Work.EQ
