import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs

/-!
# The inverse function theorem for a pair `(ψ, g)` with injective derivative

This file proves `Work.Noncompact.CompressionTube.isLocalDiffeomorphAt_pair_of_mfderiv_injective`:
for a smooth map `ψ : M → ℝ^{n-1}` and a smooth function `g : M → ℝ` on an `n`-dimensional
manifold `M`, if the manifold derivative of the pair `y ↦ (ψ y, g y)` is injective at a point `x`,
then the pair is a local diffeomorphism at `x`.  This is the pointwise inverse function theorem
for a smooth map from a manifold into a model space of the same dimension.

The proof is by way of the model space.  Writing the pair as `F`, charting `M` at `x` by
`c = chartAt ℝ^n x` and putting `G = F ∘ c.symm : ℝ^n → ℝ^{n-1} × ℝ`, the manifold derivative of
`G` at `c x` is the composite of the (injective) derivative of `F` at `x` with the derivative of
the chart inverse at `c x`, which is a continuous linear equivalence; hence it is injective, and as
source and target have the same finite dimension it is invertible.  The inverse function theorem in
normed spaces then produces a local inverse of `G` near `c x`, and conjugating by the chart gives
the result.

Because the hypothesis is only at the single point `x`, the classical theorem does not apply
directly to `G` on a whole neighbourhood; instead we use the two facts that `G` is smooth on the
open set `c.target` (the chart inverse is smooth there and `F` is smooth everywhere) and that
invertibility of the derivative is an *open* condition in finite dimensions (a continuous linear
map close enough to an invertible one is injective, hence invertible as the dimensions agree), to
locate an open neighbourhood of `c x` on which the inverse function theorem applies pointwise.

## Main results

* `injective_of_norm_mul_lt_one`: a continuous linear map sufficiently close to an invertible one
  is injective.
* `exists_isOpen_forall_hasFDerivAt_clmEquiv`: on an open set where a `C^1` map has an invertible
  derivative at one point, there is an open neighbourhood of that point on which the derivative is
  invertible at every point.
* `isLocalDiffeomorphAt_of_contDiffOn_of_forall_hasFDerivAt_clmEquiv`: the inverse function theorem
  in normed spaces at a point.
* `isLocalDiffeomorphAt_pair_of_mfderiv_injective`: the target of this file.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Filter

noncomputable section

/-! ## Auxiliary lemmas -/

/-- `IsLocalDiffeomorphAt` is invariant under pointwise eventual equality. -/
theorem isLocalDiffeomorphAt_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
    {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] {n : ℕ∞ω}
    {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (h : f =ᶠ[𝓝 x] g) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨Φ, hx, hEq⟩ := hf
  obtain ⟨U, hU, hU'⟩ := Filter.eventually_iff_exists_mem.1 h
  obtain ⟨W, hWsub, hWopen, hxW⟩ :=
    mem_nhds_iff.1 (Filter.inter_mem hU (Φ.open_source.mem_nhds hx))
  have hWsrc : W ⊆ Φ.source := fun y hy => (hWsub hy).2
  refine ⟨{
    toPartialEquiv := {
      toFun := Φ.toFun
      invFun := Φ.invFun
      source := W
      target := Φ.toFun '' W
      map_source' := fun y hy => ⟨y, hy, rfl⟩
      map_target' := fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        rw [(Φ.toPartialEquiv).left_inv' (hWsrc hy')]
        exact hy'
      left_inv' := fun y hy => (Φ.toPartialEquiv).left_inv' (hWsrc hy)
      right_inv' := fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        rw [(Φ.toPartialEquiv).left_inv' (hWsrc hy')] }
    open_source := hWopen
    open_target := (Φ.toOpenPartialHomeomorph).isOpen_image_iff_of_subset_source hWsrc |>.2 hWopen
    contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono hWsrc
    contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono (fun y hy => by
      obtain ⟨y', hy', rfl⟩ := hy
      exact Φ.map_source (hWsrc hy')) },
    hxW, fun y hy => (hU' y (hWsub hy).1).symm.trans (hEq (hWsub hy).2)⟩

/-- A continuous linear map between real normed spaces which is close enough to an invertible one
is injective: indeed if `L - e` is so small that `‖L - e‖ * ‖e⁻¹‖ < 1` then `L v = 0` forces
`‖v‖ ≤ ‖L - e‖ * ‖e⁻¹‖ * ‖v‖`, whence `v = 0`. -/
theorem injective_of_norm_mul_lt_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {e : E ≃L[ℝ] F} {L : E →L[ℝ] F}
    (h : ‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖ < 1) : Function.Injective L := by
  intro u v huv
  have hw : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hkey : u - v = - (e.symm : F →L[ℝ] E) ((L - e) (u - v)) := by
    have hsplit : L (u - v) = (L - e) (u - v) + e (u - v) := by simp [sub_apply]
    have h1 : (e.symm : F →L[ℝ] E) (L (u - v)) =
        (e.symm : F →L[ℝ] E) ((L - e) (u - v)) + (u - v) := by
      rw [hsplit, map_add]; simp
    rw [hw, map_zero] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  have hz : u - v = 0 := by
    by_contra hne
    have hpos : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
    have hx1 : ‖u - v‖ = ‖(e.symm : F →L[ℝ] E) ((L - e) (u - v))‖ := by
      conv_lhs => rw [hkey]
      rw [norm_neg]
    have hle : ‖u - v‖ ≤ ‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖ * ‖u - v‖ := by
      calc ‖u - v‖ = ‖(e.symm : F →L[ℝ] E) ((L - e) (u - v))‖ := hx1
        _ ≤ ‖(e.symm : F →L[ℝ] E)‖ * ‖(L - e) (u - v)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖(e.symm : F →L[ℝ] E)‖ * (‖L - e‖ * ‖u - v‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = ‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖ * ‖u - v‖ := by ring
    have hlt : ‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖ * ‖u - v‖ < ‖u - v‖ := by
      calc ‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖ * ‖u - v‖
          = (‖L - e‖ * ‖(e.symm : F →L[ℝ] E)‖) * ‖u - v‖ := by ring
        _ < 1 * ‖u - v‖ := mul_lt_mul_of_pos_right h hpos
        _ = ‖u - v‖ := one_mul _
    linarith
  exact sub_eq_zero.mp hz

/-- An injective continuous linear map between finite-dimensional real normed spaces of the same
dimension is a continuous linear equivalence. -/
theorem exists_clmEquiv_of_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ L' : E ≃L[ℝ] F, (L' : E →L[ℝ] F) = L := by
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hL
  have hsurj : Function.Surjective L := by
    have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (L : E →ₗ[ℝ] F))).mp hL
    simpa using h
  have hrange : L.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hsurj
  refine ⟨ContinuousLinearEquiv.ofBijective L hker hrange, ?_⟩
  ext v
  rfl

/-- **Invertibility of the derivative is an open condition.**  If `f` is `C^1` on an open set `s`
and its derivative at `x ∈ s` is invertible, then there is an open neighbourhood `W ⊆ s` of `x` on
which the derivative of `f` is invertible at every point. -/
theorem exists_isOpen_forall_hasFDerivAt_clmEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ 1 f s) {x : E} (hx : x ∈ s)
    {e : E ≃L[ℝ] F} (he : HasFDerivAt f (e : E →L[ℝ] F) x) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ s ∧
      ∀ z ∈ W, ∃ e_z : E ≃L[ℝ] F, HasFDerivAt f (e_z : E →L[ℝ] F) z := by
  have hfx : ContDiffAt ℝ 1 f x := (IsOpen.contDiffOn_iff hs).mp hf hx
  have hcont : ContinuousAt (fderiv ℝ f) x := hfx.continuousAt_fderiv (by norm_num)
  have hderivx : fderiv ℝ f x = (e : E →L[ℝ] F) := he.fderiv
  have htend : Tendsto (fderiv ℝ f) (𝓝 x) (𝓝 (e : E →L[ℝ] F)) := by
    simpa only [ContinuousAt, hderivx] using hcont
  have hε : 0 < (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨r, hr, hr'⟩ := Metric.tendsto_nhds_nhds.mp htend _ hε
  refine ⟨Metric.ball x r ∩ s, Metric.isOpen_ball.inter hs, ⟨by simpa using hr, hx⟩,
    inter_subset_right, ?_⟩
  intro z hz
  have hzdist : dist z x < r := hz.1
  have hzs : z ∈ s := hz.2
  have hznorm : ‖fderiv ℝ f z - (e : E →L[ℝ] F)‖ < (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ := by
    have := hr' hzdist
    rwa [dist_eq_norm] at this
  have hinj : Function.Injective (fderiv ℝ f z) := by
    refine injective_of_norm_mul_lt_one (e := e) ?_
    have hN : (0:ℝ) ≤ ‖(e.symm : F →L[ℝ] E)‖ := norm_nonneg _
    have h1 : ‖fderiv ℝ f z - (e : E →L[ℝ] F)‖ * ‖(e.symm : F →L[ℝ] E)‖
        ≤ (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ * ‖(e.symm : F →L[ℝ] E)‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt hznorm) hN
    have h2 : (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ * ‖(e.symm : F →L[ℝ] E)‖ < 1 := by
      have h3 : (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ * ‖(e.symm : F →L[ℝ] E)‖
          < (‖(e.symm : F →L[ℝ] E)‖ + 1)⁻¹ * (‖(e.symm : F →L[ℝ] E)‖ + 1) :=
        mul_lt_mul_of_pos_left (by linarith) (by positivity)
      rwa [inv_mul_cancel₀ (by positivity : (‖(e.symm : F →L[ℝ] E)‖ + 1) ≠ 0)] at h3
    linarith
  obtain ⟨e_z, he_z⟩ := exists_clmEquiv_of_injective hdim (fderiv ℝ f z) hinj
  refine ⟨e_z, ?_⟩
  have hzf : HasFDerivAt f (fderiv ℝ f z) z :=
    ((IsOpen.contDiffOn_iff hs).mp hf hzs).differentiableAt_one.hasFDerivAt
  rwa [he_z]

/-- **The inverse function theorem in normed spaces, at a point.**  If `f : E → F` is `C^n` on an
open set `s` (with `n ≠ 0`) and its derivative is invertible at every point of `s`, then `f` is a
local diffeomorphism at every point of `s`; in particular at `x ∈ s`. -/
theorem isLocalDiffeomorphAt_of_contDiffOn_of_forall_hasFDerivAt_clmEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) {f : E → F} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f s)
    {x : E} (hx : x ∈ s)
    (hf' : ∀ z ∈ s, ∃ e : E ≃L[ℝ] F, HasFDerivAt f (e : E →L[ℝ] F) z)
    (hn : n ≠ 0) : IsLocalDiffeomorphAt 𝓘(ℝ,E) 𝓘(ℝ,F) n f x := by
  obtain ⟨e, he⟩ := hf' x hx
  have hfx : ContDiffAt ℝ n f x := (IsOpen.contDiffOn_iff hs).mp hf hx
  let Ψ : OpenPartialHomeomorph E F := hfx.toOpenPartialHomeomorph f he hn
  have hxΨ : x ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hfx he hn
  have hΨx : f x ∈ Ψ.target := Ψ.map_source hxΨ
  have hfxW : f x ∈ Ψ '' (s ∩ Ψ.source) := ⟨x, ⟨hx, hxΨ⟩, rfl⟩
  have hVopen : IsOpen (Ψ.target ∩ Ψ '' (s ∩ Ψ.source)) :=
    Ψ.open_target.inter (Ψ.isOpen_image_of_subset_source (hs.inter Ψ.open_source) inter_subset_right)
  have hsub : Ψ.symm '' (Ψ.target ∩ Ψ '' (s ∩ Ψ.source)) ⊆ s := by
    rintro z ⟨y, ⟨hyT, z₀, ⟨hz₀s, hz₀Ψ⟩, hyz⟩, rfl⟩
    rw [← hyz, Ψ.left_inv hz₀Ψ]
    exact hz₀s
  have hfV : ContDiffOn ℝ n f (Ψ.symm '' (Ψ.target ∩ Ψ '' (s ∩ Ψ.source))) := hf.mono hsub
  have hsymm : ContDiffOn ℝ n Ψ.symm (Ψ.target ∩ Ψ '' (s ∩ Ψ.source)) := by
    rw [IsOpen.contDiffOn_iff hVopen]
    intro y hy
    obtain ⟨hyT, z, ⟨hzs, hzΨ⟩, hzy⟩ := hy
    have hsym : Ψ.symm y = z := by rw [← hzy, Ψ.left_inv hzΨ]
    obtain ⟨e_z, he_z⟩ := hf' z hzs
    exact Ψ.contDiffAt_symm hyT (by rw [hsym]; exact he_z)
      (by rw [hsym]; exact (IsOpen.contDiffOn_iff hs).mp hf hzs)
  let Φ : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) E F n :=
    { toPartialEquiv :=
        { toFun := f
          invFun := Ψ.symm
          source := Ψ.symm '' (Ψ.target ∩ Ψ '' (s ∩ Ψ.source))
          target := Ψ.target ∩ Ψ '' (s ∩ Ψ.source)
          map_source' := by
            rintro z ⟨y, hy, rfl⟩
            rw [show f (Ψ.symm y) = Ψ (Ψ.symm y) from rfl, Ψ.right_inv hy.1]
            exact hy
          map_target' := fun y hy => ⟨y, hy, rfl⟩
          left_inv' := by
            rintro z ⟨y, hy, rfl⟩
            rw [show f (Ψ.symm y) = Ψ (Ψ.symm y) from rfl, Ψ.right_inv hy.1]
          right_inv' := by
            rintro y hy
            rw [show f (Ψ.symm y) = Ψ (Ψ.symm y) from rfl, Ψ.right_inv hy.1] }
      open_source := Ψ.isOpen_image_symm_of_subset_target hVopen inter_subset_left
      open_target := hVopen
      contMDiffOn_toFun := hfV.contMDiffOn
      contMDiffOn_invFun := hsymm.contMDiffOn }
  exact ⟨Φ, ⟨f x, ⟨hΨx, hfxW⟩, Ψ.left_inv hxΨ⟩, fun y hy => rfl⟩

/-! ## The target theorem -/

theorem isLocalDiffeomorphAt_pair_of_mfderiv_injective {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))} {g : M → ℝ}
    (hψ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder ψ)
    (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (x : M)
    (h : Function.Injective (mfderiv (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MCprod n) (fun y : M => (ψ y, g y)) x)) :
    IsLocalDiffeomorphAt (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MCprod n)
      Work.Noncompact.CompressionTube.smoothOrder (fun y : M => (ψ y, g y)) x := by
  let F : M → EuclideanSpace ℝ (Fin (n - 1)) × ℝ := fun y => (ψ y, g y)
  have hF : ContMDiff (MC n) (MCprod n) smoothOrder F := by
    rw [← chartedSpaceSelf_prod]
    exact hψ.prodMk hg
  have hFmd : MDifferentiableAt (MC n) (MCprod n) F x :=
    hF.contMDiffAt.mdifferentiableAt (by simp [smoothOrder])
  -- the chart at `x`, viewed as a partial diffeomorphism
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ c.source := mem_chart_source _ x
  have hct : c x ∈ c.target := c.map_source hx
  let cP : PartialDiffeomorph (MC n) (MC n) M (EuclideanSpace ℝ (Fin n)) smoothOrder :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  have hc_ld : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder
      (c : M → EuclideanSpace ℝ (Fin n)) x :=
    PartialDiffeomorph.isLocalDiffeomorphAt (MC n) (MC n) smoothOrder cP hx
  have hcsymm_ld : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (MC n) (MC n) smoothOrder cP.symm (by
      show c x ∈ cP.target
      exact hct)
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  have hc_md : MDifferentiableAt (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x) :=
    (contMDiffAt_symm_of_mem_maximalAtlas hc hct).mdifferentiableAt hn0
  have hinj_csymm : Function.Injective
      (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x)) := by
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hcsymm_ld hn0]
    exact (hcsymm_ld.mfderivToContinuousLinearEquiv hn0).injective
  -- the coordinate expression of `F` in the chart
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ := fun z => F (c.symm z)
  have hcomp : HasMFDerivAt (MC n) (MCprod n) G (c x)
      (mfderiv (MC n) (MCprod n) F x ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x)) := by
    have h1 : HasMFDerivAt (MC n) (MCprod n) F (c.symm (c x)) (mfderiv (MC n) (MCprod n) F x) := by
      rw [c.left_inv hx]
      exact hFmd.hasMFDerivAt
    exact h1.comp (c x) (hc_md.hasMFDerivAt)
  have hL_inj : Function.Injective
      (mfderiv (MC n) (MCprod n) F x ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x)) := by
    intro u v huv
    exact hinj_csymm (h huv)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Module.finrank_self]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e, he⟩ := exists_clmEquiv_of_injective hdim _ hL_inj
  have hGe : HasFDerivAt G (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (c x) := he.symm ▸ hcomp.hasFDerivAt
  -- `G` is smooth on the chart target, and its derivative is invertible on an open subset
  have hG_smooth : ContDiffOn ℝ smoothOrder G c.target := by
    have hmem : c.target ⊆ (c.symm : EuclideanSpace ℝ (Fin n) → M) ⁻¹' (Set.univ : Set M) :=
      fun z _ => Set.mem_univ z
    have h1 : ContMDiffOn (MC n) (MCprod n) smoothOrder
        (F ∘ (c.symm : EuclideanSpace ℝ (Fin n) → M)) c.target :=
      ContMDiffOn.comp (I := MC n) (I' := MC n) (I'' := MCprod n) (n := smoothOrder)
        (f := (c.symm : EuclideanSpace ℝ (Fin n) → M)) (g := F) (s := c.target)
        (t := Set.univ) hF.contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc) hmem
    exact h1.contDiffOn
  have h1le : (1 : ℕ∞ω) ≤ smoothOrder := by simp [smoothOrder]
  obtain ⟨W, hWopen, hcW, hWsub, hWderiv⟩ :=
    exists_isOpen_forall_hasFDerivAt_clmEquiv hdim c.open_target (hG_smooth.of_le h1le) hct hGe
  have hG_ld_self : IsLocalDiffeomorphAt (MC n)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ)) smoothOrder G (c x) :=
    isLocalDiffeomorphAt_of_contDiffOn_of_forall_hasFDerivAt_clmEquiv hWopen
      (hG_smooth.mono hWsub) hcW hWderiv hn0
  have hMC : MCprod n = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    show (MC (n - 1)).prod MCreal = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n-1)) × ℝ)
    rw [modelWithCornersSelf_prod]
  have hG_ld : IsLocalDiffeomorphAt (MC n) (MCprod n) smoothOrder G (c x) := by
    rw [hMC]
    exact hG_ld_self
  -- compose with the chart and compare with `F`
  have hcomp_ld : IsLocalDiffeomorphAt (MC n) (MCprod n) smoothOrder (G ∘ c) x :=
    IsLocalDiffeomorphAt.comp (K := MCprod n) (P := EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
      hc_ld hG_ld
  have hevent : (G ∘ c) =ᶠ[𝓝 x] F := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    show G (c y) = F y
    rw [show G (c y) = F (c.symm (c y)) from rfl, c.left_inv hy]
  exact isLocalDiffeomorphAt_congr hcomp_ld hevent

end

end Work.Noncompact.CompressionTube
