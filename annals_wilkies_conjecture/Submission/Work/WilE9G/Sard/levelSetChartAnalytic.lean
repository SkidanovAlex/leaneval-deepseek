import Mathlib

/-!
# Analytic chart for a level set of an analytic submersion

`Work.WilE9G.Sard.levelSetChartAnalytic`: if `h : (Fin Q → ℝ) → (Fin j → ℝ)` is analytic
everywhere and its derivative at `z₀` is surjective, then the level set `{h = h z₀}` is, near
`z₀`, the image of an *analytic* chart `γ` defined on a neighbourhood `V` of `0` in the kernel
`W = ker (fderiv ℝ h z₀)`.  The chart is a graph over `W`: there is a continuous linear
projection `C : (Fin Q → ℝ) →L[ℝ] W` (onto `W` along a complement) with

`C (γ t - z₀) = t`  for `t ∈ V`,  and conversely every level-set point `y` in a neighbourhood
`U` of `z₀` is uniquely recovered as `γ (C (y - z₀))`.

The construction is the standard one: take a continuous projection `C` onto `W` (available
because `W` is the kernel of a continuous linear map with finite dimensional range, hence
closed complemented), apply the implicit function theorem to `Φ x = (h x, C (x - z₀))`, and
invert it.  The inverse is analytic at `(h z₀, 0)` by the analytic inverse function theorem
(`OpenPartialHomeomorph.analyticAt_symm'`), and — this is the point that gives analyticity on
*all* of a neighbourhood rather than at a single point — any function analytic at a point is
analytic on a whole neighbourhood of it (`AnalyticAt.eventually_analyticAt`).
-/

namespace Work.WilE9G.Sard

open scoped Topology

theorem levelSetChartAnalytic {Q j : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (z₀ : Fin Q → ℝ)
    (hh : ∀ x, AnalyticAt ℝ h x) (hsurj : Function.Surjective (fderiv ℝ h z₀)) :
    ∃ (C : (Fin Q → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker)
      (γ : (fderiv ℝ h z₀).ker → (Fin Q → ℝ))
      (V : Set (fderiv ℝ h z₀).ker) (U : Set (Fin Q → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ h z₀).ker) ∈ V ∧ z₀ ∈ U ∧
      γ 0 = z₀ ∧ (∀ t ∈ V, AnalyticAt ℝ γ t) ∧
      (∀ t ∈ V, γ t ∈ U) ∧
      (∀ t ∈ V, h (γ t) = h z₀) ∧
      (∀ t ∈ V, C (γ t - z₀) = t) ∧
      (∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y) := by
  classical
  -- A continuous projection onto the kernel `W = ker (fderiv ℝ h z₀)`.
  have hker : (fderiv ℝ h z₀).ker.ClosedComplemented :=
    (fderiv ℝ h z₀).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin Q → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker := Classical.choose hker
  have hC : ∀ x : (fderiv ℝ h z₀).ker, C x = x := Classical.choose_spec hker
  haveI : CompleteSpace (fderiv ℝ h z₀).ker :=
    (fderiv ℝ h z₀).isClosed_ker.completeSpace_coe
  -- The implicit function data for `Φ x = (h x, C (x - z₀))`.
  let φ : ImplicitFunctionData ℝ (Fin Q → ℝ) (Fin j → ℝ) (fderiv ℝ h z₀).ker :=
    { leftFun := h
      leftDeriv := fderiv ℝ h z₀
      rightFun := fun x => C (x - z₀)
      rightDeriv := C
      pt := z₀
      hasStrictFDerivAt_leftFun := (hh z₀).hasStrictFDerivAt
      hasStrictFDerivAt_rightFun :=
        C.hasStrictFDerivAt.comp z₀ ((hasStrictFDerivAt_id z₀).sub_const z₀)
      range_leftDeriv := LinearMap.range_eq_top.mpr hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj hC
      isCompl_ker := LinearMap.isCompl_of_proj hC }
  have hleft : ∀ x, φ.leftFun x = h x := fun x => rfl
  have hright : ∀ x, φ.rightFun x = C (x - z₀) := fun x => rfl
  have hpt : φ.pt = z₀ := rfl
  -- `Φ = φ.prodFun` is analytic at `z₀`.
  have hC_an : AnalyticAt ℝ (fun x : Fin Q → ℝ => C (x - z₀)) z₀ := by
    have h3 := (C.analyticAt z₀).sub (analyticAt_const (v := C z₀) (x := z₀))
    have heq : (⇑C) - (fun _ : Fin Q → ℝ => C z₀) = (fun x : Fin Q → ℝ => C (x - z₀)) := by
      funext x; simp
    rwa [heq] at h3
  have hΦ : AnalyticAt ℝ φ.prodFun z₀ := by
    have hprod := (hh z₀).prod hC_an
    have heq : φ.prodFun = (fun x : Fin Q → ℝ => (h x, C (x - z₀))) := by
      funext x
      rw [ImplicitFunctionData.prodFun_apply, hleft, hright]
    rw [heq]
    exact hprod
  -- Its derivative at `z₀` is the linear equivalence `x ↦ (fderiv ℝ h z₀ x, C x)`.
  let e : (Fin Q → ℝ) ≃L[ℝ] (Fin j → ℝ) × (fderiv ℝ h z₀).ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hfderiv : fderiv ℝ φ.prodFun z₀
      = (e : (Fin Q → ℝ) →L[ℝ] (Fin j → ℝ) × (fderiv ℝ h z₀).ker) := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
    rw [hpt] at h
    exact h
  -- The chart, obtained by inverting `Φ` and restricting to the slice `h = h z₀`.
  let γ : (fderiv ℝ h z₀).ker → (Fin Q → ℝ) :=
    fun v => φ.toOpenPartialHomeomorph.symm (h z₀, v)
  have hγ_an0 : AnalyticAt ℝ γ 0 := by
    have h1 : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) z₀ := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hΦ
    have h2 : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) z₀ = e := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hfderiv
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm'
      φ.pt_mem_toOpenPartialHomeomorph_source h1 h2
    have hptimg : φ.toOpenPartialHomeomorph z₀
        = ((h z₀, (0 : (fderiv ℝ h z₀).ker)) :
            (Fin j → ℝ) × (fderiv ℝ h z₀).ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    -- `h3 : AnalyticAt ℝ (⇑symm) (φ.toOpenPartialHomeomorph φ.pt)`
    have h3' : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
        ((h z₀, (0 : (fderiv ℝ h z₀).ker)) :
          (Fin j → ℝ) × (fderiv ℝ h z₀).ker) := by
      rw [hpt, hptimg] at h3
      exact h3
    have h2' : AnalyticAt ℝ
        (fun v : (fderiv ℝ h z₀).ker =>
          ((h z₀, v) : (Fin j → ℝ) × (fderiv ℝ h z₀).ker)) 0 := by
      have h := (analyticAt_const (v := h z₀) (x := (0 : (fderiv ℝ h z₀).ker))).prod
        (analyticAt_id (𝕜 := ℝ) (z := (0 : (fderiv ℝ h z₀).ker)))
      simpa using h
    simpa [γ, Function.comp_def] using h3'.comp h2'
  -- Any function analytic at `0` is analytic on a neighbourhood of `0`.
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hγ_an0.eventually_analyticAt
  -- The chart domain, and the corresponding neighbourhood of `z₀`.
  let Vt : Set (fderiv ℝ h z₀).ker :=
    {v | ((h z₀, v) : (Fin j → ℝ) × (fderiv ℝ h z₀).ker) ∈ φ.toOpenPartialHomeomorph.target}
  let V : Set (fderiv ℝ h z₀).ker := Vt ∩ Metric.ball 0 ρ
  let U : Set (Fin Q → ℝ) :=
    {y | y ∈ φ.toOpenPartialHomeomorph.source ∧ C (y - z₀) ∈ V}
  have hVt_open : IsOpen Vt :=
    φ.toOpenPartialHomeomorph.open_target.preimage (continuous_const.prodMk continuous_id)
  have hV_open : IsOpen V := hVt_open.inter Metric.isOpen_ball
  have h0Vt : (0 : (fderiv ℝ h z₀).ker) ∈ Vt := by
    have h := φ.toOpenPartialHomeomorph.map_source (φ.pt_mem_toOpenPartialHomeomorph_source)
    simpa [Vt, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h
  have h0V : (0 : (fderiv ℝ h z₀).ker) ∈ V := ⟨h0Vt, Metric.mem_ball_self hρpos⟩
  have hU_open : IsOpen U := by
    refine φ.toOpenPartialHomeomorph.open_source.inter ?_
    exact hV_open.preimage (C.continuous.comp (continuous_id.sub continuous_const))
  have hz₀U : z₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
    · simpa using h0V
  have hγ0 : γ 0 = z₀ := by
    have hz₀src : z₀ ∈ φ.toOpenPartialHomeomorph.source := by
      simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
    have h0 : ((h z₀, (0 : (fderiv ℝ h z₀).ker)) :
        (Fin j → ℝ) × (fderiv ℝ h z₀).ker) = φ.toOpenPartialHomeomorph z₀ := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    show φ.toOpenPartialHomeomorph.symm
      ((h z₀, (0 : (fderiv ℝ h z₀).ker)) :
        (Fin j → ℝ) × (fderiv ℝ h z₀).ker) = z₀
    rw [h0]
    exact φ.toOpenPartialHomeomorph.left_inv hz₀src
  have hγ_an : ∀ t ∈ V, AnalyticAt ℝ γ t := fun t ht => hρsub ht.2
  have hγU : ∀ t ∈ V, γ t ∈ U := by
    intro t ht
    refine ⟨?_, ?_⟩
    · show φ.toOpenPartialHomeomorph.symm (h z₀, t) ∈ φ.toOpenPartialHomeomorph.source
      exact φ.toOpenPartialHomeomorph.map_target ht.1
    · have h := congr_arg Prod.snd (φ.toOpenPartialHomeomorph.right_inv ht.1)
      have hthis : C (γ t - z₀) = t := by
        simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright] using h
      rw [hthis]
      exact ht
  have hγh : ∀ t ∈ V, h (γ t) = h z₀ := by
    intro t ht
    have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv ht.1)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright] using h
  have hγC : ∀ t ∈ V, C (γ t - z₀) = t := by
    intro t ht
    have h := congr_arg Prod.snd (φ.toOpenPartialHomeomorph.right_inv ht.1)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright] using h
  have hlast : ∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y := by
    intro y hy hyh
    obtain ⟨hysrc, hyV⟩ := hy
    refine ⟨hyV, ?_⟩
    have hy' : φ.toOpenPartialHomeomorph y
        = ((h z₀, C (y - z₀)) : (Fin j → ℝ) × (fderiv ℝ h z₀).ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hyh]
    show φ.toOpenPartialHomeomorph.symm (h z₀, C (y - z₀)) = y
    rw [← hy']
    exact φ.toOpenPartialHomeomorph.left_inv hysrc
  exact ⟨C, γ, V, U, hV_open, hU_open, h0V, hz₀U, hγ0, hγ_an, hγU, hγh, hγC, hlast⟩

end Work.WilE9G.Sard
