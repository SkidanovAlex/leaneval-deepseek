import Mathlib

/-!
# An immersion of manifolds of equal dimension is a local diffeomorphism

This file proves `Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion`: a `C^∞` map
`f : ℝ^{n-1} × ℝ → M` into an `n`-dimensional manifold whose manifold derivative is injective at
every point is a local diffeomorphism.

The bulk of the file is the (currently missing in Mathlib) inverse function theorem for manifolds
in the case where the source is a model vector space: a `C^∞` map `f : E → M` (with `E` a
finite-dimensional real normed space and `M` a manifold modelled on `E'`) whose `mfderiv` is
injective everywhere is a local diffeomorphism, provided `finrank ℝ E = finrank ℝ E'`.

The strategy is: write `f` in a chart `c` of `M`, obtaining `g = c ∘ f : E → E'`; the derivative
of `g` is invertible everywhere (it is the composition of `mfderiv f` with the (invertible)
derivative of a chart), so the usual inverse function theorem in normed spaces applies pointwise,
and the resulting local inverse of `g` gives an open partial homeomorphism `Ψ : E ≃ₚ E'` with
`Ψ = g` on its source.  Conjugating by the chart produces the required `PartialDiffeomorph`.
-/

open scoped Manifold ContDiff
open Set Function

namespace Work.Noncompact.CompressionTube

variable {E E' : Type*}

/-- A linear algebra lemma: an injective continuous linear map between finite-dimensional real
normed spaces of the same dimension is a continuous linear equivalence. -/
theorem exists_continuousLinearEquiv_of_injective
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [CompleteSpace E']
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    (L : E →L[ℝ] E') (hL : Function.Injective L) :
    ∃ L' : E ≃L[ℝ] E', (L' : E →L[ℝ] E') = L := by
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hL
  have hsurj : Function.Surjective L := by
    have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (L : E →ₗ[ℝ] E'))).mp hL
    simpa using h
  have hrange : L.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hsurj
  refine ⟨ContinuousLinearEquiv.ofBijective L hker hrange, ?_⟩
  ext v
  rfl

section ManifoldIFT

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M]
  [IsManifold 𝓘(ℝ,E') ∞ M] {f : E → M}

set_option backward.isDefEq.respectTransparency false in
/-- The manifold derivative of a chart is injective at every point of its source. -/
theorem isLocalDiffeomorphAt_chart_mfderiv_injective
    {c : OpenPartialHomeomorph M E'} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M)
    {y : M} (hy : y ∈ c.source) :
    Function.Injective (mfderiv 𝓘(ℝ,E') 𝓘(ℝ,E') (c : M → E') y) := by
  let Φ : PartialDiffeomorph 𝓘(ℝ,E') 𝓘(ℝ,E') M E' ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  have hld : IsLocalDiffeomorphAt 𝓘(ℝ,E') 𝓘(ℝ,E') ∞ (c : M → E') y :=
    PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ,E') 𝓘(ℝ,E') _ Φ hy
  have hn : (∞:ℕ∞ω) ≠ 0 := by norm_num
  rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn]
  exact (hld.mfderivToContinuousLinearEquiv hn).injective

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule for the coordinate expression `y ↦ c (f y)` of `f` in a chart `c` of the target. -/
theorem hasFDerivAt_chart_comp (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f)
    {c : OpenPartialHomeomorph M E'} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M)
    {y : E} (hy : f y ∈ c.source) :
    HasFDerivAt (fun z => c (f z))
      (mfderiv 𝓘(ℝ,E') 𝓘(ℝ,E') (c : M → E') (f y) ∘SL mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E') f y) y := by
  have hcm : MDifferentiableAt 𝓘(ℝ,E') 𝓘(ℝ,E') (c : M → E') (f y) :=
    (contMDiffAt_of_mem_maximalAtlas hc hy).mdifferentiableAt (by norm_num)
  have hfm : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E') f y :=
    hf.contMDiffAt.mdifferentiableAt (by norm_num)
  exact ((hcm.hasMFDerivAt).comp y (hfm.hasMFDerivAt)).hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the coordinate expression `y ↦ c (f y)` of `f` in a chart `c` of the target. -/
theorem contDiffAt_chart_comp (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f)
    {c : OpenPartialHomeomorph M E'} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M)
    {y : E} (hy : f y ∈ c.source) :
    ContDiffAt ℝ ∞ (fun z => c (f z)) y :=
  ((contMDiffAt_of_mem_maximalAtlas hc hy).comp y (hf.contMDiffAt (x := y))).contDiffAt

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the coordinate expression `y ↦ c (f y)` is injective wherever `mfderiv f`
is. -/
theorem injective_fderiv_chart_comp (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f)
    {c : OpenPartialHomeomorph M E'} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M)
    (himm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E') f p))
    {y : E} (hy : f y ∈ c.source) :
    Function.Injective (fderiv ℝ (fun z => c (f z)) y) := by
  rw [(hasFDerivAt_chart_comp hf hc hy).fderiv, ContinuousLinearMap.coe_comp]
  exact Function.Injective.comp (isLocalDiffeomorphAt_chart_mfderiv_injective hc hy) (himm y)

set_option backward.isDefEq.respectTransparency false in
/-- **Inverse function theorem for manifolds**, in the case where the source is a model space:
a `C^∞` map `f : E → M` between manifolds of the same dimension (modelled on `E` and `E'`) whose
manifold derivative is injective everywhere is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_mfderiv_injective
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E'] [CompleteSpace E']
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f)
    (himm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E') f p)) :
    IsLocalDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f := by
  intro x
  let c : OpenPartialHomeomorph M E' := chartAt E' (f x)
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M := IsManifold.chart_mem_maximalAtlas (f x)
  have hcmem : f x ∈ c.source := mem_chart_source E' (f x)
  have hn : (∞:ℕ∞ω) ≠ 0 := by norm_num
  have hinj_x := injective_fderiv_chart_comp hf hc himm hcmem
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_of_injective hdim
    (fderiv ℝ (fun z => c (f z)) x) hinj_x
  have hFx : HasFDerivAt (fun z => c (f z)) (L : E →L[ℝ] E') x :=
    HasFDerivAt.congr_fderiv
      ((contDiffAt_chart_comp hf hc hcmem).differentiableAt hn).hasFDerivAt hL.symm
  have hcdx : ContDiffAt ℝ ∞ (fun z => c (f z)) x := contDiffAt_chart_comp hf hc hcmem
  let Ψ : OpenPartialHomeomorph E E' :=
    ContDiffAt.toOpenPartialHomeomorph (fun z => c (f z)) hcdx hFx hn
  have hxΨ : x ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hcdx hFx hn
  let U : Set E := Ψ.source ∩ f ⁻¹' c.source
  have hUopen : IsOpen U := Ψ.open_source.inter (IsOpen.preimage hf.continuous c.open_source)
  have hxU : x ∈ U := ⟨hxΨ, hcmem⟩
  have hUsub : U ⊆ Ψ.source := fun y hy => hy.1
  have hUsubsrc : U ⊆ f ⁻¹' c.source := fun y hy => hy.2
  have hIm_open : IsOpen (Ψ '' U) := Ψ.isOpen_image_of_subset_source hUopen hUsub
  have hIm_sub : Ψ '' U ⊆ c.target := by
    rintro z ⟨y, hyU, rfl⟩
    exact c.map_source (hUsubsrc hyU)
  have hfU_eq : f '' U = c.symm '' (Ψ '' U) := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨y, hyU, hyz⟩
      refine ⟨Ψ y, ⟨y, hyU, rfl⟩, ?_⟩
      rw [← hyz]
      exact c.left_inv (hUsubsrc hyU)
    · intro hz
      rcases hz with ⟨w, ⟨y, hyU, hyw⟩, hzw⟩
      rw [← hyw] at hzw
      refine ⟨y, hyU, ?_⟩
      rw [← hzw]
      exact (c.left_inv (hUsubsrc hyU)).symm
  have hUimg_open : IsOpen (f '' U) := by
    rw [hfU_eq]
    exact c.isOpen_image_symm_of_subset_target hIm_open hIm_sub
  have hinv_smooth : ContMDiffOn 𝓘(ℝ,E') 𝓘(ℝ,E) ∞ (fun z => Ψ.symm (c z)) (f '' U) := by
    rintro z ⟨y, hyU, rfl⟩
    obtain ⟨Ly, hLy⟩ := exists_continuousLinearEquiv_of_injective hdim
      (fderiv ℝ (fun w => c (f w)) y) (injective_fderiv_chart_comp hf hc himm hyU.2)
    have hLy' : HasFDerivAt (fun w => c (f w)) (Ly : E →L[ℝ] E') y :=
      HasFDerivAt.congr_fderiv
        ((contDiffAt_chart_comp hf hc hyU.2).differentiableAt hn).hasFDerivAt hLy.symm
    have hcdy : ContDiffAt ℝ ∞ (fun w => c (f w)) y := contDiffAt_chart_comp hf hc hyU.2
    have hsy : Ψ.symm (c (f y)) = y := Ψ.left_inv hyU.1
    have hLy'' : HasFDerivAt (↑Ψ) (Ly : E →L[ℝ] E') (Ψ.symm (c (f y))) := by
      rw [hsy]; exact hLy'
    have hcdy' : ContDiffAt ℝ ∞ (↑Ψ) (Ψ.symm (c (f y))) := by
      rw [hsy]; exact hcdy
    have h1 : ContDiffAt ℝ ∞ Ψ.symm (c (f y)) :=
      Ψ.contDiffAt_symm (Ψ.map_source hyU.1) hLy'' hcdy'
    exact (h1.contMDiffAt.comp (f y) (contMDiffAt_of_mem_maximalAtlas hc hyU.2)).contMDiffWithinAt
  let Φ : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E') E M ∞ :=
    { toPartialEquiv :=
        { toFun := f
          invFun := fun z => Ψ.symm (c z)
          source := U
          target := f '' U
          map_source' := fun y hy => ⟨y, hy, rfl⟩
          map_target' := by
            rintro z ⟨y, hyU, rfl⟩
            have hsy : Ψ.symm (c (f y)) = y := Ψ.left_inv hyU.1
            rw [hsy]
            exact hyU
          left_inv' := by
            intro y hy
            have hsy : Ψ.symm (c (f y)) = y := Ψ.left_inv hy.1
            rw [hsy]
          right_inv' := by
            rintro z ⟨y, hyU, rfl⟩
            have hsy : Ψ.symm (c (f y)) = y := Ψ.left_inv hyU.1
            rw [hsy] }
      open_source := hUopen
      open_target := hUimg_open
      contMDiffOn_toFun := hf.contMDiffOn
      contMDiffOn_invFun := hinv_smooth }
  exact ⟨Φ, hxU, fun y hy => rfl⟩

end ManifoldIFT

theorem isLocalDiffeomorph_of_immersion {n : ℕ} (hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M}
    (hf : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ p, Function.Injective
      (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) f p)) :
    IsLocalDiffeomorph ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Module.finrank_self]
    simp only [Fintype.card_fin]
    omega
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hf himm ⊢
  exact isLocalDiffeomorph_of_mfderiv_injective hdim hf himm

end Work.Noncompact.CompressionTube
