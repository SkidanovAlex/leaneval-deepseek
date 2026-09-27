/-
# Smooth charts from injective immersions into `ℝⁿ`

This file proves the missing manifold-level instance of the inverse function theorem:

* `exists_localSection_of_injective_mfderiv` — if `g : M → ℝⁿ` is `C^∞` on an `n`-manifold `M` and
  `mfderiv g x` is injective (hence bijective, the two tangent spaces being the *same* `n`-dimensional
  space), then `g` admits a local smooth section through `x`: there is `ψ : ℝⁿ → M`, `C^∞` at `g x`,
  with `ψ (g x) = x` and `g (ψ y) = y` for all `y` near `g x`.
* `exists_smoothChart_of_injOn_immersion_of_nonempty` — the fix of
  `Work.Drive.PushDisc.exists_smoothChart_of_injOn_immersion`: an injective immersion on an open set
  `U` of a *nonempty* manifold is a smooth chart on `U`.

`M = Empty` is the only obstruction to the unconditional statement: an
`OpenPartialHomeomorph Empty E` would need a function `E → Empty`, and `E` is inhabited.  See
`_cex_emptyM.lean` for the machine-checked counterexample.
-/
import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Projection.mfderiv_chartAt_decomp

open scoped Manifold ContDiff
open Topology

namespace Work.Drive.PushDisc

noncomputable section

/-- `C^∞` in the `ℕ∞ω` encoding used by the workspace. -/
abbrev hInf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The model space of the statement: `ℝⁿ`. -/
abbrev ES (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The model with corners of the statement. -/
abbrev MWC (n : ℕ) : ModelWithCorners ℝ (ES n) (ES n) := modelWithCornersSelf ℝ (ES n)

/-! ## The chart bridge

The Fréchet derivative of the chart representation of a smooth map at the *centre* of the chart is
the manifold derivative.  (`Work.Drive.PushDisc.fderiv_chartRep_eq_mfderiv` is the same statement for
the shifted representation into `ℝ^{2n}`; here we need the unshifted one, in arbitrary target
dimension.) -/

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem fderiv_chartRep_at_centre {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M]
    (f : M → ES N) (p : M)
    (hf : ContMDiff (MWC n) (MWC N) hInf f) :
    fderiv ℝ (fun y : ES n => f ((chartAt (ES n) p).symm y))
        ((chartAt (ES n) p) p)
      = mfderiv (MWC n) (MWC N) f p := by
  have hmem : p ∈ (chartAt (ES n) p).source := mem_chart_source (ES n) p
  have hchart : mfderiv (MWC n) (MWC n) (chartAt (ES n) p) p
      = ContinuousLinearMap.id ℝ (TangentSpace (MWC n) p) := by
    have hcoe : ⇑(chartAt (ES n) p) = ⇑(extChartAt (MWC n) p) := by
      rw [extChartAt_coe]
      rfl
    rw [hcoe]
    exact mfderiv_extChartAt_self
  have hdec := Work.Projection.mfderiv_chartAt_decomp (n := n) (N := N) f hf p p hmem
  rw [hdec, hchart, ContinuousLinearMap.comp_id]

/-! ## Injectivity of the differential is bijectivity -/

/-- On an `n`-manifold, the tangent space is the model space, so an injective differential at a
point of a map to `ℝⁿ` is bijective (finite dimension). -/
theorem bijective_mfderiv_of_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M]
    (g : M → ES n) (x : M)
    (hinj : Function.Injective (mfderiv (MWC n) (MWC n) g x)) :
    Function.Bijective (mfderiv (MWC n) (MWC n) g x) := by
  haveI : FiniteDimensional ℝ (TangentSpace (MWC n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (ES n))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

/-! ## The local section -/

/-- **The inverse function theorem on an `n`-manifold, `ℝⁿ`-valued case.**  A smooth map
`g : M → ℝⁿ` whose differential at `x` is injective is a local diffeomorphism at `x`; the concrete
output used below is a local smooth section of `g` through `x`. -/
theorem exists_localSection_of_injective_mfderiv {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M]
    (g : M → ES n) (hg : ContMDiff (MWC n) (MWC n) hInf g) (x : M)
    (himm : Function.Injective (mfderiv (MWC n) (MWC n) g x)) :
    ∃ ψ : ES n → M,
      ContMDiffAt (𝓘(ℝ, ES n)) (MWC n) hInf ψ (g x) ∧
      ψ (g x) = x ∧
      ∀ᶠ y in 𝓝 (g x), g (ψ y) = y := by
  have hne : hInf ≠ 0 := by decide
  -- the chart at `x` and the chart representation of `g`
  set e : OpenPartialHomeomorph M (ES n) := chartAt (ES n) x with he
  have hx : x ∈ e.source := mem_chart_source (ES n) x
  set a : ES n := e x with ha
  have haT : a ∈ e.target := e.map_source hx
  set G : ES n → ES n := fun v => g (e.symm v) with hG
  -- smoothness of the chart representation
  have hsymm : ContMDiffAt (𝓘(ℝ, ES n)) (MWC n) hInf (fun v : ES n => e.symm v) a :=
    (contMDiffOn_chart_symm (x := x)).contMDiffAt (e.open_target.mem_nhds haT)
  have hGsmMD : ContMDiffAt (𝓘(ℝ, ES n)) (𝓘(ℝ, ES n)) hInf G a :=
    (hg.contMDiffAt (x := e.symm a)).comp a hsymm
  have hGsm : ContDiffAt ℝ hInf G a := hGsmMD.contDiffAt
  -- the differential in coordinates is `mfderiv g x`
  have hder : fderiv ℝ G a = mfderiv (MWC n) (MWC n) g x := by
    have h := fderiv_chartRep_at_centre (n := n) (N := n) g x hg
    simpa [G, e, a] using h
  -- the differential is an equivalence
  have hbij := bijective_mfderiv_of_injective g x himm
  let L : ES n ≃L[ℝ] ES n :=
    ContinuousLinearEquiv.ofBijective (mfderiv (MWC n) (MWC n) g x)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hL : (L : ES n →L[ℝ] ES n) = mfderiv (MWC n) (MWC n) g x :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hGdrv : HasFDerivAt G (L : ES n →L[ℝ] ES n) a := by
    rw [hL, ← hder]
    exact (hGsm.differentiableAt hne).hasFDerivAt
  -- the inverse function theorem
  set Ψ : OpenPartialHomeomorph (ES n) (ES n) := hGsm.toOpenPartialHomeomorph G hGdrv hne with hΨ
  have haΨ : a ∈ Ψ.source := hGsm.mem_toOpenPartialHomeomorph_source (f := G) hGdrv hne
  have hΨcoe : ⇑Ψ = G := ContDiffAt.toOpenPartialHomeomorph_coe hGsm (f := G) hGdrv hne
  have hGxa : G a = g x := by
    simp only [G, ha, e.left_inv hx]
  have hgxΨT : g x ∈ Ψ.target := by
    have h := hGsm.image_mem_toOpenPartialHomeomorph_target (f := G) hGdrv hne
    rw [hGxa] at h
    exact h
  have hright : ∀ y ∈ Ψ.target, g (e.symm (Ψ.symm y)) = y := by
    intro y hy
    calc g (e.symm (Ψ.symm y)) = G (Ψ.symm y) := rfl
      _ = Ψ (Ψ.symm y) := by rw [hΨcoe]
      _ = y := Ψ.right_inv hy
  have hΨsymm_gx : Ψ.symm (g x) = a := by
    have h : Ψ.symm (Ψ a) = a := Ψ.left_inv haΨ
    rwa [hΨcoe, hGxa] at h
  have hΨsymm_at : ContDiffAt ℝ hInf (⇑Ψ.symm) (g x) := by
    refine Ψ.contDiffAt_symm (f₀' := L) hgxΨT ?_ ?_
    · rw [hΨsymm_gx, hΨcoe]
      exact hGdrv
    · rw [hΨsymm_gx, hΨcoe]
      exact hGsm
  have hsymm_aT : Ψ.symm (g x) ∈ e.target := by
    rw [hΨsymm_gx]; exact haT
  have hcont : ContinuousAt (⇑Ψ.symm) (g x) := hΨsymm_at.continuousAt
  refine ⟨fun y => e.symm (Ψ.symm y), ?_, ?_, ?_⟩
  · -- smoothness of the section at `g x`
    have h1 : ContMDiffAt (𝓘(ℝ, ES n)) (𝓘(ℝ, ES n)) hInf (⇑Ψ.symm) (g x) :=
      hΨsymm_at.contMDiffAt
    have h2 : ContMDiffAt (𝓘(ℝ, ES n)) (MWC n) hInf (fun v : ES n => e.symm v)
        (Ψ.symm (g x)) :=
      (contMDiffOn_chart_symm (x := x)).contMDiffAt (e.open_target.mem_nhds hsymm_aT)
    exact h2.comp (g x) h1
  · simp only [hΨsymm_gx, ha, e.left_inv hx]
  · filter_upwards [Ψ.open_target.mem_nhds hgxΨT] with y hy
    exact hright y hy

/-! ## The corrected main statement -/

/-- **An injective immersion on an open set of a nonempty `n`-manifold is a smooth chart.**

This is `Work.Drive.PushDisc.exists_smoothChart_of_injOn_immersion` with the hypothesis
`[Nonempty M]` added, which is *necessary*: for `M = Empty` the conclusion asks for a partial
homeomorphism `Empty ⇝ ℝⁿ`, i.e. for a function `ℝⁿ → Empty` (see `_cex_emptyM.lean`). -/
theorem exists_smoothChart_of_injOn_immersion_of_nonempty {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M] [Nonempty M]
    (g : M → ES n) (U : Set M) (hUo : IsOpen U)
    (hg : ContMDiff (MWC n) (MWC n) hInf g)
    (hinj : Set.InjOn g U)
    (himm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (MWC n) (MWC n) g x)) :
    ∃ c : OpenPartialHomeomorph M (ES n),
      c.source = U ∧ (∀ x : M, x ∈ U → c x = g x) ∧ Work.Whitney.IsSmoothChart c := by
  classical
  -- a local smooth section of `g` through every point of `U`
  have hsec : ∀ x : M, x ∈ U → ∃ ψ : ES n → M,
      ContMDiffAt (𝓘(ℝ, ES n)) (MWC n) hInf ψ (g x) ∧ ψ (g x) = x ∧
      ∀ᶠ y in 𝓝 (g x), g (ψ y) = y :=
    fun x hx => exists_localSection_of_injective_mfderiv g hg x (himm x hx)
  -- the inverse of `g` on `g '' U`, extended by an arbitrary point off it
  let σ : ES n → M := fun y =>
    if h : ∃ x ∈ U, g x = y then h.choose else Classical.choice (inferInstance : Nonempty M)
  have hσ_mem : ∀ y (h : ∃ x ∈ U, g x = y), σ y ∈ U := by
    intro y h
    simp only [σ]
    rw [dif_pos h]
    exact h.choose_spec.1
  have hσ_g : ∀ y (h : ∃ x ∈ U, g x = y), g (σ y) = y := by
    intro y h
    simp only [σ]
    rw [dif_pos h]
    exact h.choose_spec.2
  -- `g '' U` is open
  have hopen : IsOpen (g '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hxU, rfl⟩
    obtain ⟨ψ, hψsm, hψx, hψev⟩ := hsec x hxU
    have hpre : ψ ⁻¹' U ∈ 𝓝 (g x) :=
      hψsm.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hψx]; exact hxU))
    exact Filter.mem_of_superset (Filter.inter_mem hpre hψev)
      (fun z hz => ⟨ψ z, hz.1, hz.2⟩)
  -- `σ` is smooth on `g '' U`, being locally equal to the local sections
  have hσ_sm : ContMDiffOn (𝓘(ℝ, ES n)) (MWC n) hInf σ (g '' U) := by
    rintro y ⟨x, hxU, rfl⟩
    obtain ⟨ψ, hψsm, hψx, hψev⟩ := hsec x hxU
    have hev : σ =ᶠ[𝓝 (g x)] ψ := by
      have h1 : g '' U ∈ 𝓝 (g x) := hopen.mem_nhds ⟨x, hxU, rfl⟩
      have h2 : ψ ⁻¹' U ∈ 𝓝 (g x) :=
        hψsm.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hψx]; exact hxU))
      filter_upwards [h1, h2, hψev] with z hzimg hzU hzg
      exact hinj (hσ_mem z hzimg) hzU ((hσ_g z hzimg).trans hzg.symm)
    exact (hψsm.congr_of_eventuallyEq hev).contMDiffWithinAt
  -- the partial homeomorphism
  let F : PartialEquiv M (ES n) :=
    { toFun := g
      invFun := σ
      source := U
      target := g '' U
      map_source' := fun x hx => ⟨x, hx, rfl⟩
      map_target' := fun y hy => hσ_mem y hy
      left_inv' := fun x hx => by
        have h : ∃ x' ∈ U, g x' = g x := ⟨x, hx, rfl⟩
        exact hinj (hσ_mem (g x) h) hx (hσ_g (g x) h)
      right_inv' := fun y hy => hσ_g y hy }
  let c : OpenPartialHomeomorph M (ES n) :=
    { toPartialEquiv := F
      open_source := hUo
      open_target := hopen
      continuousOn_toFun := hg.contMDiffOn.continuousOn
      continuousOn_invFun := hσ_sm.continuousOn }
  refine ⟨c, rfl, fun x hx => rfl, ?_, ?_⟩
  · exact hg.contMDiffOn
  · exact hσ_sm

/-- **The same statement with the nonemptiness hypothesis on the open set** rather than on the
manifold: for an open `U ≠ ∅` the conclusion is unaffected by `M` being empty or not. -/
theorem exists_smoothChart_of_injOn_immersion_of_nonempty_source {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M]
    (g : M → ES n) (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hg : ContMDiff (MWC n) (MWC n) hInf g) (hinj : Set.InjOn g U)
    (himm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (MWC n) (MWC n) g x)) :
    ∃ c : OpenPartialHomeomorph M (ES n),
      c.source = U ∧ (∀ x : M, x ∈ U → c x = g x) ∧ Work.Whitney.IsSmoothChart c := by
  obtain ⟨x₀, hx₀⟩ := hUne
  haveI : Nonempty M := ⟨x₀⟩
  exact exists_smoothChart_of_injOn_immersion_of_nonempty g U hUo hg hinj himm

/-- **The requested statement with no extra hypothesis at all**: either the smooth chart exists on
`U`, or `M` is empty.  The empty manifold is the *only* obstruction (`_cex_emptyM.lean`), and the
first alternative is exactly `exists_smoothChart_of_injOn_immersion_of_nonempty`. -/
theorem exists_smoothChart_or_not_nonempty {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ES n) M] [IsManifold (MWC n) hInf M]
    (g : M → ES n) (U : Set M) (hUo : IsOpen U)
    (hg : ContMDiff (MWC n) (MWC n) hInf g) (hinj : Set.InjOn g U)
    (himm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (MWC n) (MWC n) g x)) :
    (∃ c : OpenPartialHomeomorph M (ES n),
        c.source = U ∧ (∀ x : M, x ∈ U → c x = g x) ∧ Work.Whitney.IsSmoothChart c) ∨
      ¬ Nonempty M := by
  by_cases h : Nonempty M
  · exact Or.inl (exists_smoothChart_of_injOn_immersion_of_nonempty g U hUo hg hinj himm)
  · exact Or.inr h

end

end Work.Drive.PushDisc
