import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Transversality along a line is an open condition in the parameter

Let `M` be a smooth `n`-manifold (`n ≥ 2`) and `γ : ℝ → M` a smooth curve.  For a smooth
`g : M → ℝ` and a smooth `ψ : M → ℝ^{n-1}` we say that `ψ` is *transverse* at `γ s` (with respect
to `g`) if `(dψ, dg)` is injective at `γ s`, i.e. if `Transverse γ g ψ s` holds.

The main result of this file, `Work.Noncompact.CompressionTube.transverse_open`, shows that the set
of `s` at which `ψ` is transverse is a neighbourhood of every point where it holds.  Since
`ker dψ ∩ ker dg = 0` at `γ s₀` means that `(dψ, dg)` is an immersion at `γ s₀`, and since the
dimensions agree (`dim M = n = (n-1) + 1`), it is a local diffeomorphism at `γ s₀`; hence it stays
an immersion on a whole neighbourhood of `γ s₀` in `M`, and a fortiori along the curve.

The argument is carried out in the chart `c = chartAt E (γ s₀)`, with `E = ℝ^n`.  Everything is
reduced to the coordinate expression
`F = fun y ↦ (ψ (c.symm y), g (c.symm y)) : E → ℝ^{n-1} × ℝ`:

* `F` is smooth at `y₀ = c (γ s₀)`;
* `fderiv ℝ F y₀` is injective, by the chain rule and `Transverse γ g ψ s₀`;
* the set of points at which the derivative of a `C¹` map between finite-dimensional normed spaces
  is injective is open (`ContinuousLinearMap.isOpen_injective`), so `fderiv ℝ F` stays injective on
  an open neighbourhood `W` of `y₀`;
* for `s` close to `s₀` the chart sends `γ s` into `W`, and the chain rule identifies `(dψ, dg)` at
  `γ s` with `fderiv ℝ F (c (γ s))` composed with the (invertible) derivative of the chart, giving
  `Transverse γ g ψ s`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Filter

-- `TangentSpace I x` is a reducible synonym for the model space; several statements below mix
-- `mfderiv`-valued terms with their `fderiv` counterparts, so we unfold generously.
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Injectivity of the derivative is an open condition -/

/-- If the derivative of a `C^1` map `f : E → F` between finite-dimensional real normed spaces is
injective at `x`, then it is injective for all `y` in a neighbourhood of `x`. -/
theorem eventually_injective_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {x : E} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) (hm : m ≠ 0)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    ∀ᶠ y in nhds x, Function.Injective (fderiv ℝ f y) :=
  (hf.continuousAt_fderiv hm).preimage_mem_nhds
    ((ContinuousLinearMap.isOpen_injective (𝕜 := ℝ)).mem_nhds hinj)

/-- The set of points at which the derivative of a `C^1` map between finite-dimensional real normed
spaces is injective is open, in the form used below. -/
theorem exists_open_injective_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {x : E} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) (hm : m ≠ 0)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, Function.Injective (fderiv ℝ f y) := by
  obtain ⟨W, hW, hsub⟩ := (eventually_injective_fderiv hdim hf hm hinj).exists_mem
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hW
  exact ⟨V, hVopen, hxV, fun y hy => hsub y (hVsub hy)⟩

/-- The dimension count underlying the proof: `ℝ^n` and `ℝ^{n-1} × ℝ` have the same dimension. -/
theorem finrank_euclideanSpace_prod {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
  rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Module.finrank_self,
    Fintype.card_fin, Fintype.card_fin]
  omega

/-- Pushing a composition through a product of continuous linear maps. -/
theorem comp_prod_eq_prod_comp {E E₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    (A : E →L[ℝ] E₁) (B : E →L[ℝ] ℝ) (S : E →L[ℝ] E) :
    (A.comp S).prod (B.comp S) = (A.prod B).comp S := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]

/-! ## The derivative of the coordinate expression of `(ψ, g)` -/

/-- In the chart `c`, the coordinate expression `y ↦ (ψ (c.symm y), g (c.symm y))` of the map
`(ψ, g)` has derivative `(dψ, dg) ∘ d(c.symm)`: this is the manifold chain rule, rewritten in terms
of `fderiv` because all the spaces involved carry their self model-with-corners. -/
theorem hasFDerivAt_coord_pair {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target) :
    HasFDerivAt (fun y' => (ψ (c.symm y'), g (c.symm y')))
      (((mfderiv (MC n) (MC (n - 1)) ψ (c.symm y)).prod
          (mfderiv (MC n) MCreal g (c.symm y))).comp
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) y)) y := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) y :=
    contMDiffAt_symm_of_mem_maximalAtlas hc hy
  have hsymm_md : MDifferentiableAt (MC n) (MC n)
      (c.symm : EuclideanSpace ℝ (Fin n) → M) y :=
    hsymm.mdifferentiableAt hn0
  have hA : HasFDerivAt (fun y' => ψ (c.symm y'))
      ((mfderiv (MC n) (MC (n - 1)) ψ (c.symm y)).comp
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) y)) y :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((hψ.mdifferentiableAt (x := c.symm y) hn0).hasMFDerivAt.comp y hsymm_md.hasMFDerivAt)
  have hB : HasFDerivAt (fun y' => g (c.symm y'))
      ((mfderiv (MC n) MCreal g (c.symm y)).comp
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) y)) y :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((hg.mdifferentiableAt (x := c.symm y) hn0).hasMFDerivAt.comp y hsymm_md.hasMFDerivAt)
  exact (hA.prodMk hB).congr_fderiv (comp_prod_eq_prod_comp _ _ _)

/-! ## The main theorem -/

theorem transverse_open {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder ψ)
    (h0 : ∀ s : ℝ, ψ (γ s) = 0) {s₀ : ℝ}
    (hs : Work.Noncompact.CompressionTube.Transverse γ g ψ s₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s - s₀| < ρ →
      Work.Noncompact.CompressionTube.Transverse γ g ψ s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at the base point
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (γ s₀)
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s₀)
  have hcs : γ s₀ ∈ c.source := mem_chart_source _ (γ s₀)
  have hct : c (γ s₀) ∈ c.target := c.map_source hcs
  have hct' : c (γ s₀) ∈ c.symm.source := by
    rwa [OpenPartialHomeomorph.symm_source]
  have hmd : c.MDifferentiable (MC n) (MC n) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)
  -- the coordinate expression of `(ψ, g)`
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun y => (ψ (c.symm y), g (c.symm y)) with hF
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hct
  have hFdiff : ContDiffAt ℝ smoothOrder F (c (γ s₀)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => ψ (c.symm y)) (c (γ s₀)) :=
      (hψ.contMDiffAt (x := c.symm (c (γ s₀)))).comp (c (γ s₀)) hsymm
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => g (c.symm y)) (c (γ s₀)) :=
      (hg.contMDiffAt (x := c.symm (c (γ s₀)))).comp (c (γ s₀)) hsymm
    rw [hF]
    exact h1.contDiffAt.prodMk h2.contDiffAt
  -- the derivative of `F` at the base point is injective
  have hbase : c.symm (c (γ s₀)) = γ s₀ := c.left_inv hcs
  have hFind : Function.Injective (fderiv ℝ F (c (γ s₀))) := by
    have hd : fderiv ℝ F (c (γ s₀)) =
        ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
            (mfderiv (MC n) MCreal g (γ s₀))).comp
          (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀))) := by
      have h := (hasFDerivAt_coord_pair hψ hg hcm hct).fderiv
      rw [hbase] at h
      exact h
    rw [hd]
    have hP : Function.Injective ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
        (mfderiv (MC n) MCreal g (γ s₀))) := by
      intro a b hab
      have h0 : ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
          (mfderiv (MC n) MCreal g (γ s₀))) (a - b) = 0 := by
        rw [map_sub, sub_eq_zero.mpr hab]
      have h1 : mfderiv (MC n) (MC (n - 1)) ψ (γ s₀) (a - b) = 0 := by
        have h := congrArg Prod.fst h0
        simpa [ContinuousLinearMap.prod_apply] using h
      have h2 : mfderiv (MC n) MCreal g (γ s₀) (a - b) = 0 := by
        have h := congrArg Prod.snd h0
        simpa [ContinuousLinearMap.prod_apply] using h
      exact sub_eq_zero.mp (hs _ h1 h2)
    have hS : Function.Injective
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀))) :=
      (hmd.symm.mfderiv hct').injective
    intro a b hab
    exact hS (hP hab)
  -- the open set where the derivative of `F` stays injective
  obtain ⟨W, hWopen, hWmem, hWsub⟩ :=
    exists_open_injective_fderiv (finrank_euclideanSpace_prod (by omega)) hFdiff hn0 hFind
  -- a parameter interval mapping into it
  have hcontγ : ContinuousAt γ s₀ := hprop.continuous.continuousAt
  have hcontc : ContinuousAt c (γ s₀) := c.continuousAt hcs
  have hpre : γ ⁻¹' (c.source ∩ c ⁻¹' W) ∈ 𝓝 s₀ := by
    rw [preimage_inter]
    exact Filter.inter_mem (hcontγ.preimage_mem_nhds (c.open_source.mem_nhds hcs))
      (hcontγ.preimage_mem_nhds (hcontc.preimage_mem_nhds (hWopen.mem_nhds hWmem)))
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hεpos, fun s hs' => ?_⟩
  have hsball : s ∈ Metric.ball s₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hs'
  obtain ⟨hxsrc, hcxW⟩ := hεsub hsball
  have hcxt : c (γ s) ∈ c.target := c.map_source hxsrc
  have hleft : c.symm (c (γ s)) = γ s := c.left_inv hxsrc
  -- the derivatives at `γ s`, with concrete types
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ (γ s)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s)
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hxsrc
  have hderiv : fderiv ℝ F (c (γ s)) = (A.prod B).comp Se := by
    have h := (hasFDerivAt_coord_pair hψ hg hcm hcxt).fderiv
    rw [hleft] at h
    exact h
  have hderiv_inj : Function.Injective ((A.prod B).comp Se) := by
    rw [← hderiv]
    exact hWsub _ hcxW
  -- conclude
  intro v hv1 hv2
  have hv0 : (A.prod B) v = 0 := by
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext hv1 hv2
  have hval : Se (Ce v) = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [ContinuousLinearMap.comp_apply] using h1
  have hkey : ((A.prod B).comp Se) (Ce v) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hval, hv0]
  have hzero : Ce v = 0 := hderiv_inj (by simpa using hkey)
  calc v = Se (Ce v) := hval.symm
    _ = Se 0 := by rw [hzero]
    _ = 0 := map_zero Se

end

end Work.Noncompact.CompressionTube
