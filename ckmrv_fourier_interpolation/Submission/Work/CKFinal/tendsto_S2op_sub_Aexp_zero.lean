import Mathlib
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2

noncomputable section

open UpperHalfPlane ModularGroup Filter Topology
open scoped Topology

namespace Work.CKFinal

/-- The cusp-expansion remainder `K(σ, it) - 𝒢(σ, it)` of the kernel along the contour,
for fixed `σ ∈ ℍ`. -/
private def cuspRem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (σ : UpperHalfPlane) (t : ℝ) : ℂ :=
  Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t

/-- The cusp-expansion remainder tends to `0` at a point whose `SL(2,ℤ)`-orbit misses the
imaginary axis, by the far-side cusp expansion `cusp_expansion_of_kernel_of_clean` and the
exponential-beats-polynomial limit. -/
lemma tendsto_cuspRem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (σ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Filter.Tendsto (fun t : ℝ => cuspRem ℓ d σ t) Filter.atTop (nhds 0) := by
  obtain ⟨C, M, T₀, hC, hM, hT, hbnd⟩ :=
    Work.LayerCont.FarTail.cusp_expansion_of_kernel_of_clean ℓ d hd (K := {σ})
      isCompact_singleton (fun τ t ht hτ => by
        rw [Set.mem_singleton_iff] at hτ
        subst hτ
        exact hclean t ht)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase : Filter.Tendsto (fun x : ℝ => x ^ M * Real.exp (-Real.pi * x))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M Real.pi Real.pi_pos
  have hshift : Filter.Tendsto (fun t : ℝ => 1 + t) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b - 1, fun a ha => by linarith⟩
  have hcomp : Filter.Tendsto (fun t : ℝ => (1 + t) ^ M * Real.exp (-Real.pi * (1 + t)))
      Filter.atTop (nhds 0) := hbase.comp hshift
  have hg : Filter.Tendsto (fun t : ℝ => C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
      Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto (fun t : ℝ => (C * Real.exp (Real.pi * (1 + T₀)))
        * ((1 + t) ^ M * Real.exp (-Real.pi * (1 + t)))) Filter.atTop (nhds 0) := by
      have h := hcomp.const_mul (C * Real.exp (Real.pi * (1 + T₀)))
      simpa using h
    refine hmul.congr' (Eventually.of_forall fun t => ?_)
    change C * Real.exp (Real.pi * (1 + T₀)) * ((1 + t) ^ M * Real.exp (-Real.pi * (1 + t)))
      = C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))
    rw [show -(Real.pi * (t - T₀)) = Real.pi * (1 + T₀) + (-Real.pi * (1 + t)) by ring,
      Real.exp_add]
    ring
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht1
  exact hbnd σ t (Set.mem_singleton σ) ht1

/-- The pointwise evaluation of `S2op` on the cusp-expansion remainder: the three `S`-images
`S•τ`, `S•(τ+1)`, `S•(τ+2)` of the three translates, with the weight factors of the slash by `S`
as `t`-independent coefficients. -/
lemma S2op_cuspRem_apply (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op ((d : ℤ) / 2) (fun σ : UpperHalfPlane => cuspRem ℓ d σ t) τ
      = cuspRem ℓ d (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t
            * ((((2 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2))
        - 2 * (cuspRem ℓ d (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t
            * ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)))
        + cuspRem ℓ d (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-((d : ℤ) / 2))) := by
  rw [Work.Asymptotics.S2op_apply_eq]
  simp only [Work.Kernels.slash_S_apply]

/-- At a point `τ` whose `SL(2,ℤ)`-orbit misses the imaginary axis, the `S(T-I)²`-defect of the
cusp-expansion remainder `K - 𝒢` along the contour tends to `0` as `t → ∞`. -/
theorem tendsto_S2op_sub_Aexp_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Filter.Tendsto (fun t : ℝ => Work.Asymptotics.S2op ((d : ℤ) / 2)
        (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ)
      Filter.atTop (nhds 0) := by
  have hc0 : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun (ModularGroup.S • τ) ≠
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht h
    rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul] at h
    exact hclean t ht h
  have hc1 : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) ≠
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht h
    rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul,
      Work.Kernels.KernelFacts.jInvariantFun_vadd_one] at h
    exact hclean t ht h
  have hc2 : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) ≠
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht h
    rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul] at h
    rw [Work.Kernels.vadd_one_add_one] at h
    rw [Work.Kernels.KernelFacts.jInvariantFun_vadd_one] at h
    rw [Work.Kernels.KernelFacts.jInvariantFun_vadd_one] at h
    exact hclean t ht h
  have hA0 := tendsto_cuspRem ℓ d hd (ModularGroup.S • τ) hc0
  have hA1 := tendsto_cuspRem ℓ d hd (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) hc1
  have hA2 := tendsto_cuspRem ℓ d hd (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) hc2
  have h0 : Filter.Tendsto (fun t : ℝ =>
      cuspRem ℓ d (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-((d : ℤ) / 2))))
      Filter.atTop (nhds 0) := by
    have h := hA0.mul_const (((τ : ℂ) ^ (-((d : ℤ) / 2))))
    simpa using h
  have h1 : Filter.Tendsto (fun t : ℝ => 2 *
      (cuspRem ℓ d (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t
        * ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2))))
      Filter.atTop (nhds 0) := by
    have h := hA1.mul_const (((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)))
    have h' := h.const_mul (2 : ℂ)
    simpa using h'
  have h2 : Filter.Tendsto (fun t : ℝ =>
      cuspRem ℓ d (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t
        * ((((2 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)))
      Filter.atTop (nhds 0) := by
    have h := hA2.mul_const (((((2 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)))
    simpa using h
  have hcomb := (h2.sub h1).add h0
  have hgoal : (fun t : ℝ => Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ)
      = fun t : ℝ => cuspRem ℓ d (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t
            * ((((2 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2))
        - 2 * (cuspRem ℓ d (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t
            * ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) ^ (-((d : ℤ) / 2)))
        + cuspRem ℓ d (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-((d : ℤ) / 2))) := by
    funext t
    exact S2op_cuspRem_apply ℓ d τ t
  rw [hgoal]
  simpa using hcomb

end Work.CKFinal
