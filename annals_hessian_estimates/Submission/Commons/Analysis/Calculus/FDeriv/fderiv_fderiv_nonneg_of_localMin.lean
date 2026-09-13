import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus.FDeriv

open Set Topology Filter

/-- Auxiliary one-dimensional fact: if `g` is continuous at `0` and has a local minimum at `0`,
then the second derivative of `g` at `0` (which is `0` if it does not exist) is nonnegative. -/
lemma deriv_deriv_nonneg_of_continuousAt_localMin {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (hmin : IsLocalMin g 0) : 0 ≤ deriv (deriv g) 0 := by
  by_contra h
  push Not at h
  have hd0 : deriv g 0 = 0 := hmin.deriv_eq_zero
  have hsign : ∀ᶠ x in 𝓝[≠] (0:ℝ), SignType.sign (deriv g x) = SignType.sign (0 - x) :=
    nhdsWithin_le_nhds (eventually_nhdsWithin_sign_eq_of_deriv_neg h hd0)
  have hmax : IsLocalMax g 0 := isLocalMax_of_sign_deriv hg hsign
  have hconst : ∀ᶠ y in 𝓝 (0:ℝ), g y = g 0 := by
    filter_upwards [hmin, hmax] with y hy1 hy2 using le_antisymm hy2 hy1
  rw [Filter.eventually_iff] at hconst
  obtain ⟨t, ht_sub, ht_open, ht_mem⟩ := mem_nhds_iff.mp hconst
  have hderiv0 : deriv g =ᶠ[𝓝 (0:ℝ)] (fun _ : ℝ => 0) := by
    rw [Filter.EventuallyEq]
    refine mem_of_superset (ht_open.mem_nhds ht_mem) ?_
    intro y hy
    show deriv g y = 0
    have hyeq : g =ᶠ[𝓝 y] (fun _ : ℝ => g 0) := by
      rw [Filter.EventuallyEq]
      exact mem_of_superset (ht_open.mem_nhds hy) (fun z hz => ht_sub hz)
    rw [hyeq.deriv_eq]
    simp
  have h2 : deriv (deriv g) 0 = deriv (fun _ : ℝ => (0:ℝ)) 0 := hderiv0.deriv_eq
  rw [h2] at h
  simp at h

/-- The second derivative of the function `t ↦ f (x + t • v)` at `0` is the second Fréchet
derivative of `f` at `x` evaluated at `v` twice. -/
lemma deriv_deriv_comp_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 = (fderiv ℝ (fderiv ℝ f) x) v v := by
  have h_e : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0:ℝ)]
      (fun t : ℝ => (fderiv ℝ f (x + t • v)) v) := by
    have hψ : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) ((1:ℝ) • v) 0 :=
        (hasDerivAt_id (0:ℝ)).smul_const v
      have h2 : HasDerivAt (fun t : ℝ => x + t • v) ((1:ℝ) • v) 0 := h1.const_add x
      simpa [one_smul] using h2
    have hdiffat : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
      (hf.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
    have hdiff0 : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ f (x + t • v) := by
      have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
        simpa using hψ.continuousAt.tendsto
      exact htend.eventually hdiffat
    rw [Filter.EventuallyEq]
    filter_upwards [hdiff0] with t ht
    have hψt : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      have h1 : HasDerivAt (fun s : ℝ => s • v) ((1:ℝ) • v) t := (hasDerivAt_id t).smul_const v
      have h2 : HasDerivAt (fun s : ℝ => x + s • v) ((1:ℝ) • v) t := h1.const_add x
      simpa [one_smul] using h2
    have hderiv := ht.hasFDerivAt.comp_hasDerivAt t hψt
    simpa [Function.comp_def] using hderiv.deriv
  rw [h_e.deriv_eq]
  set F : E → (E →L[ℝ] ℝ) := fderiv ℝ f with hF
  set A : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ F x with hAdef
  have hF1 : ContDiffAt ℝ 1 F x := by
    have := hf.fderiv_right (m := 1) (n := 2) (by norm_num)
    simpa [F] using this
  have hA : HasFDerivAt F A x := by
    have hdiff : DifferentiableAt ℝ F x := hF1.differentiableAt (by norm_num)
    have := hdiff.hasFDerivAt
    simpa [A] using this
  set ψ : ℝ → E := fun t => x + t • v with hψdef
  have hψ : HasDerivAt ψ v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) ((1:ℝ) • v) 0 := (hasDerivAt_id (0:ℝ)).smul_const v
    have h2 : HasDerivAt (fun t : ℝ => x + t • v) ((1:ℝ) • v) 0 := h1.const_add x
    simpa [ψ, one_smul] using h2
  set Φ : ℝ → (E →L[ℝ] ℝ) := fun t => F (ψ t) with hΦdef
  set φ : ℝ → ℝ := fun t => Φ t v with hφdef
  have hA' : HasFDerivAt F A (ψ 0) := by simpa [ψ] using hA
  have hΦ : HasFDerivAt Φ (A.comp (ContinuousLinearMap.toSpanSingleton ℝ v)) 0 := by
    have := hA'.comp 0 hψ.hasFDerivAt
    simpa [Φ, Function.comp_def] using this
  have hφF : HasFDerivAt φ
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        (A.comp (ContinuousLinearMap.toSpanSingleton ℝ v))) 0 := by
    have := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp 0 hΦ
    simpa [φ, Φ, Function.comp_def] using this
  have hφ : HasDerivAt φ (A v v) 0 := by
    have := hφF.hasDerivAt
    simpa using this
  have hgoal : deriv φ 0 = (fderiv ℝ (fderiv ℝ f) x) v v := by
    rw [hφ.deriv]
  simpa only [φ, Φ, ψ, F] using hgoal

theorem fderiv_fderiv_nonneg_of_localMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) (v : E) :
    0 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hψcont : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hmin_g : IsLocalMin g 0 := by
    have hψt : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hψcont.tendsto
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), f x ≤ f (x + t • v) := hψt.eventually hmin
    have hev' : ∀ᶠ t in 𝓝 (0:ℝ), f (x + (0:ℝ) • v) ≤ f (x + t • v) := by simpa using hev
    rw [IsLocalMin, IsMinFilter]
    simpa [g] using hev'
  have hgcont : ContinuousAt g 0 := by
    have hψt : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hψcont.tendsto
    rw [ContinuousAt]
    have := hf.continuousAt.tendsto.comp hψt
    simpa [g, Function.comp_def] using this
  have h1 : 0 ≤ deriv (deriv g) 0 :=
    deriv_deriv_nonneg_of_continuousAt_localMin hgcont hmin_g
  have h2 : deriv (deriv g) 0 = (fderiv ℝ (fderiv ℝ f) x) v v := by
    simpa [g] using deriv_deriv_comp_line hf v
  rwa [h2] at h1

end Commons.Analysis.Calculus.FDeriv