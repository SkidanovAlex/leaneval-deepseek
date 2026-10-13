import Mathlib
import Submission.Work.WilE5.Calc.exists_comp_of_ker_le_ker
import Submission.Work.WilE5.Calc.clm_eq_sum_smul_proj

namespace Work.WilE5.Calc

open Filter
open scoped Topology

/-- Analytic core.  Let `g : ℝ^q → ℝ^k` be strictly differentiable at `z` with surjective
derivative `D = fderiv ℝ g z`, let `f` be differentiable at `z`, and suppose that `f` vanishes
on the zero level set of `g` in a neighbourhood of `z`.  Then the differential of `f` at `z`
vanishes on the kernel of `D`, i.e. `df_z ∘ ι = 0` where `ι : ker D ↪ ℝ^q` is the inclusion.

The proof uses the implicit function theorem: since `D` is surjective, the level set `{g = g z}`
is locally parametrized by `ker D` through `γ = implicitFunction`, and `γ` has derivative the
inclusion of `ker D` at `0`.  Composing with the parametrization gives that `f ∘ γ` is locally
`0`, hence its derivative, which is `df_z ∘ ι`, vanishes. -/
theorem fderiv_comp_subtypeL_eq_zero {q k : ℕ} (g : (Fin q → ℝ) → (Fin k → ℝ)) (f : (Fin q → ℝ) → ℝ) (z : Fin q → ℝ)
    (hg : HasStrictFDerivAt g (fderiv ℝ g z) z) (hf : HasFDerivAt f (fderiv ℝ f z) z)
    (hgz : g z = 0) (hsurj : (fderiv ℝ g z).range = ⊤)
    (hv : ∀ᶠ w in nhds z, g w = 0 → f w = 0) :
    (fderiv ℝ f z).comp (fderiv ℝ g z).ker.subtypeL = 0 := by
  -- The local parametrisation of the level set `{g = 0}` by an open subset of `ker D`.
  let γ : (fderiv ℝ g z).ker → (Fin q → ℝ) :=
    HasStrictFDerivAt.implicitFunction g (fderiv ℝ g z) hg hsurj (g z)
  have hγ0 : γ 0 = z := HasStrictFDerivAt.implicitFunction_apply_image hg hsurj
  have hγd : HasStrictFDerivAt γ (fderiv ℝ g z).ker.subtypeL 0 :=
    HasStrictFDerivAt.to_implicitFunction hg hsurj
  -- `γ` takes values in the level set `{g = 0}` on a neighbourhood of `0`.
  have hlevel : ∀ᶠ u in 𝓝 (0 : (fderiv ℝ g z).ker), g (γ u) = 0 := by
    have h := HasStrictFDerivAt.map_implicitFunction_eq hg hsurj
    have h2 : ∀ᶠ u in 𝓝 (0 : (fderiv ℝ g z).ker), g (γ u) = g z := by
      have ht : Tendsto (fun u : (fderiv ℝ g z).ker => (g z, u)) (𝓝 0) (𝓝 (g z, 0)) :=
        tendsto_const_nhds.prodMk_nhds tendsto_id
      simpa [γ] using ht.eventually h
    filter_upwards [h2] with u hu
    rw [hu, hgz]
  -- Pulling back the hypothesis `hv` along `γ`.
  have hv' : ∀ᶠ u in 𝓝 (0 : (fderiv ℝ g z).ker), g (γ u) = 0 → f (γ u) = 0 := by
    have hcont : Tendsto γ (𝓝 (0 : (fderiv ℝ g z).ker)) (𝓝 z) := by
      have := hγd.continuousAt.tendsto
      rwa [hγ0] at this
    exact hcont.eventually hv
  -- Hence `f ∘ γ` is eventually `0` near `0`.
  have heq : (fun _ : (fderiv ℝ g z).ker => (0 : ℝ)) =ᶠ[𝓝 0] (fun u => f (γ u)) := by
    filter_upwards [hlevel, hv'] with u hu hv2
    exact (hv2 hu).symm
  -- Its derivative at `0` is `df_z ∘ ι` by the chain rule, and `0` since it is eventually constant.
  have hcomp : HasFDerivAt (fun u : (fderiv ℝ g z).ker => f (γ u))
      ((fderiv ℝ f z).comp (fderiv ℝ g z).ker.subtypeL) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f z) (γ 0) := by rw [hγ0]; exact hf
    have := hf'.comp 0 hγd.hasFDerivAt
    simpa [Function.comp_def] using this
  have hzero : HasFDerivAt (fun _ : (fderiv ℝ g z).ker => (0 : ℝ))
      ((fderiv ℝ f z).comp (fderiv ℝ g z).ker.subtypeL) 0 :=
    hcomp.congr_of_eventuallyEq heq
  exact hzero.unique (hasFDerivAt_const (0 : ℝ) 0)

theorem fderiv_eq_sum_of_vanishes_on_levelSet {q k : ℕ} (g : (Fin q → ℝ) → (Fin k → ℝ)) (f : (Fin q → ℝ) → ℝ) (z : Fin q → ℝ)
    (hg : HasStrictFDerivAt g (fderiv ℝ g z) z) (hf : HasFDerivAt f (fderiv ℝ f z) z)
    (hgz : g z = 0) (hsurj : (fderiv ℝ g z).range = ⊤)
    (hv : ∀ᶠ w in nhds z, g w = 0 → f w = 0) :
    ∃ lam : Fin k → ℝ,
      fderiv ℝ f z = ∑ a, lam a • ((ContinuousLinearMap.proj a) ∘L (fderiv ℝ g z)) := by
  -- The differential of `f` vanishes on `ker D`, so `D.ker ≤ (fderiv ℝ f z).ker`.
  have hsub := fderiv_comp_subtypeL_eq_zero g f z hg hf hgz hsurj hv
  have hker : (fderiv ℝ g z).ker ≤ (fderiv ℝ f z).ker := by
    intro v hv
    have hmem : ((fderiv ℝ f z).comp (fderiv ℝ g z).ker.subtypeL)
        (⟨v, hv⟩ : (fderiv ℝ g z).ker) = 0 := by
      rw [hsub]; simp
    simpa using hmem
  -- Thus `df_z` factors through `D`.
  obtain ⟨φ, hφ⟩ :=
    exists_comp_of_ker_le_ker (fderiv ℝ g z) (fderiv ℝ f z) hsurj hker
  -- And every continuous linear functional on `ℝ^k` is a combination of the coordinate projections.
  obtain ⟨lam, hlam⟩ := clm_eq_sum_smul_proj φ
  refine ⟨lam, ?_⟩
  rw [hφ, hlam]
  rw [ContinuousLinearMap.finsetSum_comp]
  simp only [ContinuousLinearMap.smul_comp]

end Work.WilE5.Calc
