import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.contDiffOn_two_of_partials` (leaf B7b)

`ContDiffTwoOfPartials h U` says: on an **open** set `U ⊆ ℝ × ℝ`, if `uncurry h` is `C¹` and
both plain partial derivatives `uncurry (pz h)` and `uncurry (pth h)` are `C¹`, then `uncurry h`
is `C²`.

This is the standard "`C¹` with `C¹` partials gives `C²`" statement, in the form needed by the
`θ`-gluing argument (`glue_line_C2`).  The proof:

* the candidate second-order derivative of `f := uncurry h` at `u = (a, b)` is the continuous
  linear map `A u := ∂_z h (a,b) • ε₁ + ∂_θ h (a,b) • ε₂`, i.e.
  `(toSpanSingleton ℝ (pz h a b)).coprod (toSpanSingleton ℝ (pth h a b))`;
* `A` is `C¹` on `U`, because for every fixed `y : ℝ × ℝ` the function
  `u ↦ A u y = ∂_z h u * y.1 + ∂_θ h u * y.2` is a linear combination of the two hypotheses
  (and `contDiffOn_clm_apply` reduces the `C¹`-ness of a continuous-linear-map-valued function
  to the `C¹`-ness of all its applications);
* `f` has Fréchet derivative `A u` at every `u ∈ U`, by `hasStrictFDerivAt_uncurry_coprod`: the
  `z`-slice of `f` near `u` is differentiable with derivative `∂_z h` (its Fréchet derivative in
  the direction `(1,0)`, and `pz h` is by definition the slice derivative), the `θ`-slice
  similarly, and both partial-derivative families are continuous at `u` because `pz h`, `pth h`
  are `C¹` (hence continuous) there;
* the criterion `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn` with `n = 1` (and
  `U` open, so `UniqueDiffOn ℝ U`) then concludes.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-- On `ℝ`, the "span of `c`" linear functional is `c` times the identity. -/
private lemma toSpanSingleton_eq_smul_one (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • (1 : ℝ →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.ext
  intro t
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

theorem contDiffOn_two_of_partials (h : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) :
    Work.FTS_StreamBdry.SB25.ContDiffTwoOfPartials h U := by
  intro hU h1 hz hθ
  -- the candidate second derivative of `uncurry h`
  let f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b =>
    ContinuousLinearMap.toSpanSingleton ℝ (Work.Spaces.pz h a b)
  let f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b =>
    ContinuousLinearMap.toSpanSingleton ℝ (Work.Spaces.pth h a b)
  let A : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun u => (f₁ u.1 u.2).coprod (f₂ u.1 u.2)
  -- `A` is `C¹`, componentwise
  have hA : ContDiffOn ℝ 1 A U := by
    rw [contDiffOn_clm_apply]
    intro y
    have hz' : ContDiffOn ℝ 1 (fun u : ℝ × ℝ => Work.Spaces.pz h u.1 u.2) U := hz
    have hθ' : ContDiffOn ℝ 1 (fun u : ℝ × ℝ => Work.Spaces.pth h u.1 u.2) U := hθ
    have hsum : ContDiffOn ℝ 1 (fun u : ℝ × ℝ =>
        Work.Spaces.pz h u.1 u.2 • (y.1 : ℝ) + Work.Spaces.pth h u.1 u.2 • (y.2 : ℝ)) U :=
      (hz'.smul_const y.1).add (hθ'.smul_const y.2)
    refine hsum.congr (fun u hu => ?_)
    simp only [A, f₁, f₂, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  -- `uncurry h` has Fréchet derivative `A u` at every `u ∈ U`
  have hderiv : ∀ u ∈ U, HasFDerivAt (Function.uncurry h) (A u) u := by
    intro u hu
    have hf₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun z : ℝ => h z v.2) (↿f₁ v) v.1 := by
      filter_upwards [hU.mem_nhds hu] with v hv
      have hc : ContDiffAt ℝ 1 (Function.uncurry h) v := h1.contDiffAt (hU.mem_nhds hv)
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => h p.1 p.2) v :=
        hc.differentiableAt (by norm_num)
      have hpair : HasFDerivAt (fun z : ℝ => ((z, v.2) : ℝ × ℝ))
          ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) v.1 :=
        (hasFDerivAt_id (x := v.1)).prodMk (hasFDerivAt_const (x := v.1) v.2)
      have hcomp := (hd.hasFDerivAt.comp v.1 hpair).hasDerivAt
      -- the slice derivative is `pz h v.1 v.2` by definition of `pz`
      have hder : HasDerivAt (fun z : ℝ => h z v.2) (Work.Spaces.pz h v.1 v.2) v.1 := by
        have hval : Work.Spaces.pz h v.1 v.2
            = ((fderiv ℝ (fun p : ℝ × ℝ => h p.1 p.2) v).comp
                ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) 1 := by
          simp only [Work.Spaces.pz]
          exact hcomp.deriv
        rw [hval]
        exact hcomp
      exact hder.hasFDerivAt
    have hf₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun z : ℝ => h v.1 z) (↿f₂ v) v.2 := by
      filter_upwards [hU.mem_nhds hu] with v hv
      have hc : ContDiffAt ℝ 1 (Function.uncurry h) v := h1.contDiffAt (hU.mem_nhds hv)
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => h p.1 p.2) v :=
        hc.differentiableAt (by norm_num)
      have hpair : HasFDerivAt (fun z : ℝ => ((v.1, z) : ℝ × ℝ))
          ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) v.2 :=
        (hasFDerivAt_const (x := v.2) v.1).prodMk (hasFDerivAt_id (x := v.2))
      have hcomp := (hd.hasFDerivAt.comp v.2 hpair).hasDerivAt
      have hder : HasDerivAt (fun z : ℝ => h v.1 z) (Work.Spaces.pth h v.1 v.2) v.2 := by
        have hval : Work.Spaces.pth h v.1 v.2
            = ((fderiv ℝ (fun p : ℝ × ℝ => h p.1 p.2) v).comp
                ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 := by
          simp only [Work.Spaces.pth]
          exact hcomp.deriv
        rw [hval]
        exact hcomp
      exact hder.hasFDerivAt
    -- the two partial-derivative families are continuous at `u`
    have hcf₁ : ContinuousAt (↿f₁) u := by
      have hcont : ContinuousAt (fun v : ℝ × ℝ => Work.Spaces.pz h v.1 v.2) u :=
        hz.continuousOn.continuousAt (hU.mem_nhds hu)
      have heq : (↿f₁) = fun v : ℝ × ℝ => (Work.Spaces.pz h v.1 v.2) • (1 : ℝ →L[ℝ] ℝ) := by
        funext v
        exact toSpanSingleton_eq_smul_one _
      exact (hcont.smul continuousAt_const).congr (Filter.EventuallyEq.of_eq heq.symm)
    have hcf₂ : ContinuousAt (↿f₂) u := by
      have hcont : ContinuousAt (fun v : ℝ × ℝ => Work.Spaces.pth h v.1 v.2) u :=
        hθ.continuousOn.continuousAt (hU.mem_nhds hu)
      have heq : (↿f₂) = fun v : ℝ × ℝ => (Work.Spaces.pth h v.1 v.2) • (1 : ℝ →L[ℝ] ℝ) := by
        funext v
        exact toSpanSingleton_eq_smul_one _
      exact (hcont.smul continuousAt_const).congr (Filter.EventuallyEq.of_eq heq.symm)
    exact (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := u) (f := h)
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hcf₁ hcf₂).hasFDerivAt
  -- `C¹` with `C¹` first derivative is `C²`
  have key := contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (𝕜 := ℝ)
    (s := U) (f := Function.uncurry h) (n := 1) hU.uniqueDiffOn
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl]
  refine key.2 ⟨?_, A, hA, ?_⟩
  · intro hh
    exact absurd hh (by simp)
  · intro x hx
    exact (hderiv x hx).hasFDerivWithinAt

end Work.FTS_StreamBdry.SB25
