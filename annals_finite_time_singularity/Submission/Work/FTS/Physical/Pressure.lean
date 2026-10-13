/-
# `Work.FTS.Physical.Pressure` — the pressure of the reconstructed solution

The last clause of `IsLocalEulerEquationSolution` is the Euler equation itself, i.e. the existence
of the pressure.  The vorticity formulation of Euler determines the pressure up to a constant: the
vorticity equation for `(u, ω = ∇×u)` says exactly that the *material acceleration*
`G = ∂ₜu + (u·∇)u` is curl-free, and the Poincaré lemma on `ℝ³` then produces `p` with `∇p = -G`.

This module contains

* `vorticity_materialAccel_eq` (`Pressure/vorticity_materialAccel_eq`): the classical product rule
  `∇×((u·∇)u) = (u·∇)(∇×u) - ((∇×u)·∇)u` for a `C²`, divergence-free velocity field;
* `vorticity_timeDeriv_eq` (`Pressure/vorticity_timeDeriv_eq`): `∇×` commutes with `∂ₜ` (Clairaut,
  for a jointly `C²` field);
* `vorticity_materialAccel_eq_zero_at` (`Pressure/vorticity_materialAccel_eq_zero_at`): the
  curl-free statement obtained by combining the two with the vorticity equation — "the vorticity
  equation is the curl of the Euler equation";
* `radialPrim`, the explicit primitive `p(x,t) = ∫₀¹ ⟪G(sx,t), x⟫ ds` of a curl-free field, with
  `hasFDerivAt_radialPrim` giving `∇p = G` (the Poincaré lemma in explicit form, with the
  parametric dependence on `t` that `Work.LWP.CurlFree.curlFree_isGradient` does not provide) and
  `contDiffOn_radialPrim` giving the joint `C¹` regularity in `(x,t)`;
* `exists_pressure_of_smooth`: the assembly — for a smooth field satisfying the vorticity equation,
  `p := -radialPrim (∂ₜu + (u·∇)u)` is jointly `C¹` and `∂ₜu + (u·∇)u + ∇p = 0`.

The *general* `C^{1,α}` case is not reachable by this route — `(∇u)·u` is only `C^{0,α}` and not
differentiable — and is the elliptic input `Work.LWP.PressureReconstruction α` of the LWP chapter
(producing `p` as the Schauder solution of `-Δp = div((u·∇)u)`); the reconstruction theorem of
`Physical/Reconstruction.lean` therefore consumes `PressureReconstruction α` as its pressure
input, while the smooth case is proved here.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Pressure.RadialPrim
import Submission.Work.LWP.Inputs
import Submission.Work.FTS.Physical.Pressure.vorticity_materialAccel_eq
import Submission.Work.FTS.Physical.Pressure.vorticity_timeDeriv_eq
import Submission.Work.FTS.Physical.Pressure.vorticity_materialAccel_eq_zero_at
import Submission.Work.FTS.Physical.Pressure.hasFDerivAt_radialPrim
import Submission.Work.FTS.Physical.Pressure.contDiffOn_radialPrim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- **The curl of the material acceleration.**  For a velocity field `u` that is `C²` and
divergence-free at time `t`,

  `∇×((u·∇)u) = (u·∇)(∇×u) - ((∇×u)·∇)u`.

This is the product rule for the curl, obtained from the classical identity
`(u·∇)u = ∇(‖u‖²/2) - u × (∇×u)` (which holds pointwise for every vector field, by the
`ε`-identity `(u × (∇×u))ᵢ = (∂ᵢuⱼ)uⱼ - (∂ⱼuᵢ)uⱼ`) together with
`∇×(u × ω) = u(∇·ω) - ω(∇·u) + (ω·∇)u - (u·∇)ω`; the term `∇(‖u‖²/2)` contributes nothing to the
curl and `∇·ω = 0` identically, so only `∇·u = 0` is needed as a hypothesis. -/
theorem vorticity_materialAccel_eq {u : R3 → ℝ → R3} {t : ℝ} (x : R3)
    (hdiv : div (u · t) = 0) (hsm : ContDiffAt ℝ 2 (u · t) x) :
    vorticity (fun y => fderiv ℝ (u · t) y (u y t)) x
      = fderiv ℝ (fun y => vorticity (u · t) y) x (u x t)
        - fderiv ℝ (u · t) x (vorticity (u · t) x) :=
  Work.FTS.Physical.Pressure.vorticity_materialAccel_eq x hdiv hsm

/-- **`∇×` commutes with `∂ₜ`.**  For a jointly `C²` spacetime field the mixed second derivatives
agree (Clairaut), so the curl of the time derivative is the time derivative of the curl. -/
theorem vorticity_timeDeriv_eq {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 (fun q : R3 × ℝ => u q.1 q.2) (x, t)) :
    deriv (fun s => vorticity (fun y => u y s) x) t
      = vorticity (fun y => deriv (fun s => u y s) t) x :=
  Work.FTS.Physical.Pressure.vorticity_timeDeriv_eq h

/-- **The material acceleration is curl-free.**  Combining the curl product rule with the
vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u` (and `ω = ∇×u` *at every time* — needed so that
`∂ₜω = ∂ₜ(curl u)` — and `div u = 0`), `∇×(∂ₜu + (u·∇)u) = 0` at every point where the fields are
smooth.  This is the whole content of "the vorticity equation is the curl of the Euler equation",
and hence of the existence of the pressure. -/
theorem vorticity_materialAccel_eq_zero_at {u ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hcurl : ∀ y : R3, ∀ s : ℝ, vorticity (fun z => u z s) y = ω y s)
    (hdivu : div (u · t) = 0)
    (hvort : ∀ y : R3,
      timeDeriv ω y t + directionalDeriv ω u y t = directionalDeriv u ω y t)
    (hjoint : ContDiffAt ℝ 2 (fun q : R3 × ℝ => u q.1 q.2) (x, t)) :
    vorticity (fun y => timeDeriv u y t + directionalDeriv u u y t) x = 0 :=
  Work.FTS.Physical.Pressure.vorticity_materialAccel_eq_zero_at hcurl hdivu hvort hjoint

/- The radial primitive `radialPrim` (with its docstring) is *defined* in the lower module
`Submission.Work.FTS.Physical.Pressure.RadialPrim`, imported above, rather than in this umbrella
file: the lemma module `Submission.Work.FTS.Physical.Pressure.contDiffOn_radialPrim` (imported
below, like the other `Pressure` lemma modules) is stated in terms of `radialPrim`, so defining
`radialPrim` here would create the import cycle umbrella → lemma → umbrella. -/

/-- **The radial primitive integrates a curl-free field.**  If `t ↦ G(·,t)` is `C¹` and curl-free
at time `t`, then `fderiv (radialPrim G · t) x = ⟪G x t, ·⟫`, i.e. `∇p = G`.

The proof is the classical one: differentiating under the integral,
`∂ᵢ p = ∫₀¹ [s·(∂ᵢG(sx))·x + G(sx)·eᵢ] ds`; the curl-free condition gives
`(∂ᵢG)·x = s·d/ds(G(sx)·eᵢ)`, and `∫₀¹ s·g'(s) ds = g(1) - ∫₀¹ g` telescopes the first term
against the second.  (The global `C¹` hypothesis is needed, not just `ContDiffAt` at the endpoint
`x`: `hcurl` alone is compatible with jump surfaces off the ray.) -/
theorem hasFDerivAt_radialPrim {G : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hC1 : ContDiff ℝ 1 (fun y => G y t)) (hcurl : ∀ y : R3, vorticity (fun z => G z t) y = 0) :
    HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, inner ℝ (G (s • y) t) y) (innerSL ℝ (G x t)) x :=
  Work.FTS.Physical.Pressure.hasFDerivAt_radialPrim hC1 hcurl

/-- **Joint `C¹` of the radial primitive.**  The parametric integral `(x,t) ↦ radialPrim G x t` of a
jointly `C¹` field is jointly `C¹` on the strip; no curl-freeness is needed for this. -/
theorem contDiffOn_radialPrim {G : R3 → ℝ → R3} {T : ℝ}
    (hG : ContDiffOn ℝ 1 (fun q : R3 × ℝ => G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T)) :
    ContDiffOn ℝ 1 (fun q : R3 × ℝ => radialPrim G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T) :=
  Work.FTS.Physical.Pressure.contDiffOn_radialPrim hG

/-- **The gradient is the Riesz dual of the derivative**: `fderiv ℝ f x = ⟪∇f x, ·⟫`, the bridge
between Mathlib's gradient and the `fderiv` of `ChallengeDeps`. -/
theorem fderiv_eq_innerSL_spaceGrad (p : R3 → ℝ → ℝ) (x : R3) (t : ℝ) :
    fderiv ℝ (p · t) x = innerSL ℝ (spaceGrad p x t) := by
  rw [spaceGrad]
  rw [← toDual_gradient (𝕜 := ℝ) (f := fun y : R3 => p y t) (x := x)]
  ext y
  simp

/-- **The gradient is determined by its inner products.** -/
theorem spaceGrad_eq_of_inner_eq {p : R3 → ℝ → ℝ} {x : R3} {t : ℝ} {v : R3}
    (h : ∀ y : R3, inner ℝ (spaceGrad p x t) y = inner ℝ v y) :
    spaceGrad p x t = v := by
  have hzero : inner ℝ (spaceGrad p x t - v) (spaceGrad p x t - v) = 0 := by
    have h1 : inner ℝ (spaceGrad p x t - v) (spaceGrad p x t) = 0 := by
      rw [inner_sub_left, h (spaceGrad p x t), sub_self]
    have h2 : inner ℝ (spaceGrad p x t - v) v = 0 := by
      rw [inner_sub_left, h v, sub_self]
    rw [inner_sub_right, h1, h2, sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- **Existence of the pressure for a smooth solution of the vorticity equation.**  If
`ω = ∇×u` at every time, `u` is divergence-free, `ω` solves the vorticity equation against `u`,
and the fields are smooth enough for the product rule and Clairaut, then
`p := -radialPrim (∂ₜu + (u·∇)u)` is a pressure: it is jointly `C¹` and
`∂ₜu + (u·∇)u + ∇p = 0`.  This is the Euler equation in the form of
`IsLocalEulerEquationSolution` (up to the half-open/closed strip). -/
theorem exists_pressure_of_smooth {u ω : R3 → ℝ → R3} {T : ℝ} (_hT : 0 < T)
    (hcurl : ∀ y : R3, ∀ s : ℝ, vorticity (fun z => u z s) y = ω y s)
    (hdivu : ∀ t : ℝ, div (u · t) = 0)
    (hvort : ∀ y : R3, ∀ t : ℝ,
      timeDeriv ω y t + directionalDeriv ω u y t = directionalDeriv u ω y t)
    (hjoint : ∀ x : R3, ∀ t ∈ Set.Ioo 0 T,
      ContDiffAt ℝ 2 (fun q : R3 × ℝ => u q.1 q.2) (x, t))
    (hG : ContDiffOn ℝ 1
      (fun q : R3 × ℝ => timeDeriv u q.1 q.2 + directionalDeriv u u q.1 q.2)
      (Set.univ ×ˢ Set.Ioo 0 T)) :
    ∃ p : R3 → ℝ → ℝ, ContDiffOn ℝ 1 p.uncurry (Set.univ ×ˢ Set.Ioo 0 T) ∧
      ∀ x t, t ∈ Set.Ioo 0 T →
        timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0 := by
  set G : R3 → ℝ → R3 := fun x t => timeDeriv u x t + directionalDeriv u u x t with hGdef
  have hG' : ContDiffOn ℝ 1 (fun q : R3 × ℝ => G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T) := hG
  refine ⟨fun x t => -radialPrim G x t, ?_, ?_⟩
  · -- joint `C¹` of the primitive, negated
    have hprim := contDiffOn_radialPrim (G := G) hG'
    have hneg : ContDiffOn ℝ 1 (fun q : R3 × ℝ => -radialPrim G q.1 q.2)
        (Set.univ ×ˢ Set.Ioo 0 T) := hprim.neg
    refine hneg.congr ?_
    intro q _
    rfl
  · intro x t ht
    -- the slice of `G` is `C¹` (the strip is open in `t`)
    have hC1t : ContDiff ℝ 1 (fun y => G y t) := by
      rw [← contDiffOn_univ]
      exact hG'.comp (contDiff_prodMk_left t).contDiffOn (fun y _ => ⟨trivial, ht⟩)
    have hcurlG : ∀ y : R3, vorticity (fun z => G z t) y = 0 := fun y =>
      vorticity_materialAccel_eq_zero_at hcurl (hdivu t) (fun z => hvort z t) (hjoint y t ht)
    have hfd : HasFDerivAt (fun y => radialPrim G y t) (innerSL ℝ (G x t)) x :=
      hasFDerivAt_radialPrim hC1t hcurlG
    have hfd' : HasFDerivAt (fun y => -radialPrim G y t) (innerSL ℝ (-(G x t))) x := by
      have h := hfd.neg
      have hneg : innerSL ℝ (-(G x t)) = -(innerSL ℝ (G x t)) := map_neg _ _
      rw [hneg]
      exact h
    -- hence the gradient of `p · t` at `x` is `-(G x t)`
    have hgrad : spaceGrad (fun x t => -radialPrim G x t) x t = -(G x t) := by
      refine spaceGrad_eq_of_inner_eq (fun y => ?_)
      have hb := fderiv_eq_innerSL_spaceGrad (fun x t => -radialPrim G x t) x t
      rw [hfd'.fderiv] at hb
      exact (congrArg (fun (L : R3 →L[ℝ] ℝ) => L y) hb).symm
    rw [hgrad]
    have hunfold : G x t = timeDeriv u x t + directionalDeriv u u x t := rfl
    rw [hunfold]
    simp

end Work.FTS.Physical
