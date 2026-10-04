import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.C2

open scoped ContDiff Topology
open Filter

/-- **Auxiliary form of `within_slice_clairaut`**, with the extra hypothesis that the `y`-domain
`U` is a `UniqueDiffOn` set (which is what the symmetry of the second derivative within the
product set needs).  The target `within_slice_clairaut` follows by applying this to `interior U`:
the conclusion does not mention `U` at all. -/
theorem within_slice_clairaut_aux
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : ℝ × V → G} {a b : ℝ} {U : Set V} {t₀ : ℝ} {y₀ : V}
    (hab : a < b) (hU : U ∈ nhds y₀) (huniq : UniqueDiffOn ℝ U) (ht₀ : t₀ ∈ Set.Icc a b)
    (hΨ : ContDiffWithinAt ℝ 2 Ψ (Set.Icc a b ×ˢ U) (t₀, y₀)) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      (fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc a b) t₀) y₀)
      (Set.Icc a b) t₀ := by
  set S : Set (ℝ × V) := Set.Icc a b ×ˢ U with hS
  have hy₀U : y₀ ∈ U := mem_of_mem_nhds hU
  have hmem : (t₀, y₀) ∈ S := by rw [hS]; exact ⟨ht₀, hy₀U⟩
  have huniqS : UniqueDiffOn ℝ S := by rw [hS]; exact (uniqueDiffOn_Icc hab).prod huniq
  have huniqIcc : UniqueDiffWithinAt ℝ (Set.Icc a b) t₀ := (uniqueDiffOn_Icc hab) t₀ ht₀
  -- `(t₀,y₀)` lies in the closure of the interior of the strip, so the second derivative within
  -- `S` is symmetric there.
  have hcl : (t₀, y₀) ∈ closure (interior S) := by
    have h₁ : interior S = Set.Ioo a b ×ˢ interior U := by
      rw [hS, interior_prod_eq, interior_Icc]
    rw [h₁, closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨ht₀, subset_closure (mem_interior_iff_mem_nhds.mpr hU)⟩
  have hsymm : IsSymmSndFDerivWithinAt ℝ Ψ S (t₀, y₀) :=
    hΨ.isSymmSndFDerivWithinAt (n := 2) (by norm_num) huniqS hcl hmem
  -- The second derivative of `Ψ` within `S` at `(t₀,y₀)`.
  set P : (ℝ × V) →L[ℝ] ((ℝ × V) →L[ℝ] G) :=
    fderivWithin ℝ (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) with hP
  have hA_cd : ContDiffWithinAt ℝ 1 (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) :=
    hΨ.fderivWithin_right huniqS (m := 1) (by norm_num) hmem
  have hA_diff : DifferentiableWithinAt ℝ (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) S (t₀, y₀) :=
    hA_cd.differentiableWithinAt (by norm_num)
  have hA_has : HasFDerivWithinAt (fun p : ℝ × V ↦ fderivWithin ℝ Ψ S p) P S (t₀, y₀) := by
    rw [hP]; exact hA_diff.hasFDerivWithinAt
  have hsymm_eq : ∀ v : V, P (0, v) (1, 0) = P (1, 0) (0, v) := by
    intro v
    have h := hsymm.eq (0, v) (1, 0)
    simpa only [hP] using h
  -- The continuous linear map `T ↦ T.comp inr`, extracting the `V`-slot.
  set C : ((ℝ × V) →L[ℝ] G) →L[ℝ] (V →L[ℝ] G) :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] G) (ContinuousLinearMap.inr ℝ ℝ V)).comp
      (ContinuousLinearMap.compL ℝ V (ℝ × V) G) with hCdef
  have hC_apply : ∀ T : (ℝ × V) →L[ℝ] G, C T = T.comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro T
    rw [hCdef]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply]
  -- ## The `s`-derivative of the slice differential at `y₀`.
  have hM : HasDerivWithinAt
      (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V))
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) (Set.Icc a b) t₀ := by
    have hφ : HasFDerivWithinAt (fun s : ℝ ↦ (s, y₀))
        (ContinuousLinearMap.inl ℝ ℝ V) (Set.Icc a b) t₀ :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ y₀).hasFDerivWithinAt
    have h1' : HasFDerivWithinAt (fun s : ℝ ↦ fderivWithin ℝ Ψ S (s, y₀))
        (P.comp (ContinuousLinearMap.inl ℝ ℝ V)) (Set.Icc a b) t₀ :=
      hA_has.comp t₀ hφ (by intro s hs; exact ⟨hs, hy₀U⟩)
    have h2 : HasFDerivWithinAt (fun s : ℝ ↦ C (fderivWithin ℝ Ψ S (s, y₀)))
        (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) (Set.Icc a b) t₀ :=
      (ContinuousLinearMap.hasFDerivWithinAt C (s := Set.univ)).comp t₀ h1'
        (by intro x _; exact trivial)
    have h3 := h2.hasDerivWithinAt
    have hvalC : (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) 1
        = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      exact hC_apply (P (1, 0))
    simpa only [hC_apply, hvalC, Function.comp_def] using h3
  -- ## The slice `fderiv` at `y₀` agrees with the within-`fderiv` of `Ψ`.
  have key1 : ∀ s ∈ Set.Icc a b, ContDiffWithinAt ℝ 2 Ψ S (s, y₀) →
      fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀
        = (fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro s hs hcont
    have hd : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ S (s, y₀)) S (s, y₀) :=
      (hcont.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have hψ : HasFDerivWithinAt (fun y : V ↦ (s, y))
        (ContinuousLinearMap.inr ℝ ℝ V) U y₀ :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) s y₀).hasFDerivWithinAt
    have hge : HasFDerivAt (fun y : V ↦ Ψ (s, y))
        ((fderivWithin ℝ Ψ S (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)) y₀ := by
      have h := (hd.comp y₀ hψ (by intro y hy; exact ⟨hs, hy⟩)).hasFDerivAt hU
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using h
    exact hge.fderiv
  have hslic : ∀ᶠ s in 𝓝[Set.Icc a b] t₀, ContDiffWithinAt ℝ 2 Ψ S (s, y₀) := by
    have htend : Tendsto (fun s : ℝ ↦ (s, y₀)) (𝓝[Set.Icc a b] t₀) (𝓝[S] (t₀, y₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · exact (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact ⟨hs, hy₀U⟩
    have hev := hΨ.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    rw [Set.insert_eq_of_mem hmem] at hev
    exact htend.eventually hev
  have hEv : (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      =ᶠ[𝓝[Set.Icc a b] t₀]
        (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp
          (ContinuousLinearMap.inr ℝ ℝ V)) := by
    filter_upwards [hslic, self_mem_nhdsWithin] with s hc hs
    exact key1 s hs hc
  have hpt : (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀) t₀
      = (fun s : ℝ ↦ (fderivWithin ℝ Ψ S (s, y₀)).comp
          (ContinuousLinearMap.inr ℝ ℝ V)) t₀ :=
    key1 t₀ ht₀ hΨ
  have hF : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) (Set.Icc a b) t₀ :=
    hM.congr_of_eventuallyEq hEv hpt
  -- ## The claimed value: the `y`-derivative of the `s`-partial.
  have key2 : ∀ y ∈ U, ContDiffWithinAt ℝ 2 Ψ S (t₀, y) →
      derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc a b) t₀
        = (fderivWithin ℝ Ψ S (t₀, y)) (1, 0) := by
    intro y hy hcont
    have hd : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ S (t₀, y)) S (t₀, y) :=
      (hcont.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have hφ : HasFDerivWithinAt (fun s : ℝ ↦ (s, y))
        (ContinuousLinearMap.inl ℝ ℝ V) (Set.Icc a b) t₀ :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ y).hasFDerivWithinAt
    have hd2 := (hd.comp t₀ hφ (by intro s hs; exact ⟨hs, hy⟩)).hasDerivWithinAt
    have hder := hd2.derivWithin huniqIcc
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using hder
  have htend2 : Tendsto (fun y : V ↦ (t₀, y)) (𝓝 y₀) (𝓝[S] (t₀, y₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact continuousAt_const.prodMk continuousAt_id
    · filter_upwards [hU] with y hy
      exact ⟨ht₀, hy⟩
  have hsl : ∀ᶠ y in 𝓝 y₀, ContDiffWithinAt ℝ 2 Ψ S (t₀, y) := by
    have hev := hΨ.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    rw [Set.insert_eq_of_mem hmem] at hev
    exact htend2.eventually hev
  have hEv' : (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc a b) t₀)
      =ᶠ[𝓝 y₀] (fun y : V ↦ (fderivWithin ℝ Ψ S (t₀, y)) (1, 0)) := by
    filter_upwards [hsl, hU] with y hc hy
    exact key2 y hy hc
  have hR : HasFDerivAt (fun y : V ↦ (fderivWithin ℝ Ψ S (t₀, y)) (1, 0))
      ((ContinuousLinearMap.apply ℝ G (1, 0)).comp
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V))) y₀ := by
    have hψ : HasFDerivWithinAt (fun y : V ↦ (t₀, y))
        (ContinuousLinearMap.inr ℝ ℝ V) U y₀ :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) t₀ y₀).hasFDerivWithinAt
    have h1'' : HasFDerivWithinAt (fun y : V ↦ fderivWithin ℝ Ψ S (t₀, y))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) U y₀ :=
      hA_has.comp y₀ hψ (by intro y hy; exact ⟨ht₀, hy⟩)
    have h1a : HasFDerivAt (fun y : V ↦ fderivWithin ℝ Ψ S (t₀, y))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) y₀ := h1''.hasFDerivAt hU
    have h2a := (ContinuousLinearMap.apply ℝ G (1, 0)).hasFDerivAt.comp y₀ h1a
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2a
  have hval : fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc a b) t₀) y₀
      = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    rw [hEv'.fderiv_eq, hR.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inr_apply]
    exact hsymm_eq v
  rw [hval]
  exact hF

/-- **One-sided Clairaut (Schwarz) for the slice `fderiv`.**

For `Ψ : ℝ × V → G` which is `C²` within the closed strip `Set.Icc a b ×ˢ U` at `(t₀, y₀)`
(`U` a neighbourhood of `y₀`, `t₀ ∈ Set.Icc a b`), the within-derivative at `t₀` of the
`y`-slice Fréchet differential (along `Set.Icc a b`) equals the `y`-Fréchet differential of the
`s`-partial `derivWithin (fun s ↦ Ψ (s, y)) (Set.Icc a b) t₀`.

This is the version of `Work.Diff.EXT.hasDerivAt_sliceFDeriv` / `Work.Diff.T.clairaut_fderiv_apply`
in which the `s`-variable is confined to a closed interval, i.e. the one-sided/mixed Schwarz
theorem.  The existing `HasDerivAt` versions require `ContDiffAt` at an *interior* point of the
`(s,y)`-space, hence cannot be applied at `t₀ = a` (or `t₀ = b`).

Suggested route: reduce to the symmetry of the second derivative within the product set
`S := Set.Icc a b ×ˢ U` (`ContDiffWithinAt.isSymmSndFDerivWithinAt`, using `uniqueDiffOn_Icc`,
`UniqueDiffOn.prod` and `(t₀,y₀) ∈ closure (interior S)`), then mirror the proof of
`Work.Diff.EXT.hasDerivAt_sliceFDeriv` with `fderivWithin` in place of `fderiv`
(`HasFDerivWithinAt.comp`, `ContDiffWithinAt.eventually`, `HasFDerivWithinAt.hasDerivWithinAt`,
`fderivWithin_fderivWithin_eq_of_mem_nhds`). -/
theorem within_slice_clairaut
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : ℝ × V → G} {a b : ℝ} {U : Set V} {t₀ : ℝ} {y₀ : V}
    (hab : a < b) (hU : U ∈ nhds y₀) (ht₀ : t₀ ∈ Set.Icc a b)
    (hΨ : ContDiffWithinAt ℝ 2 Ψ (Set.Icc a b ×ˢ U) (t₀, y₀)) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ (fun y : V ↦ Ψ (s, y)) y₀)
      (fderiv ℝ (fun y : V ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc a b) t₀) y₀)
      (Set.Icc a b) t₀ := by
  -- Replace `U` by its interior: the conclusion does not mention `U`, and the interior is a
  -- `UniqueDiffOn` neighbourhood of `y₀`.
  have hy₀int : y₀ ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hU' : interior U ∈ nhds y₀ := isOpen_interior.mem_nhds hy₀int
  have hΨ' : ContDiffWithinAt ℝ 2 Ψ (Set.Icc a b ×ˢ interior U) (t₀, y₀) :=
    hΨ.mono (Set.prod_mono_right interior_subset)
  exact within_slice_clairaut_aux hab hU' isOpen_interior.uniqueDiffOn ht₀ hΨ'

end Work.Diff.STE.C2
