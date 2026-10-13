import Mathlib
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart

/-!
# `levelSetChartV`: an analytic chart of a level set, analytic on its whole domain

Let `g : ℝⁿ → ℝᵏ` be analytic at `p` and suppose its differential at `p` is surjective.
Then, near `p`, the level set `{g = g p}` is the graph of an analytic map over an open
neighbourhood `V` of `0` in the kernel `W = ker (fderiv ℝ g p)`.

Concretely we construct a chart `γ : W → ℝⁿ`, open sets `V ⊆ W` and `U ⊆ ℝⁿ` with
`0 ∈ V`, `p ∈ U`, `γ 0 = p`, such that

* `γ` is analytic at every point of `V` (not only at `0`),
* `γ` maps `V` into `U`, and `g (γ v) = g p` for every `v ∈ V`,
* there is a continuous linear projection `C : ℝⁿ →L[ℝ] W` onto `W` such that every
  level point `y ∈ U` is recovered from its `C`-coordinate: `C (y - p) ∈ V` and
  `γ (C (y - p)) = y`.

The construction is the standard one: take a continuous linear projection `C` onto the
kernel `W` (available because `W` is the kernel of a continuous linear map with finite
dimensional range, hence closed and complemented), apply the implicit function theorem to
`Φ x = (g x, C (x - p))` — whose derivative at `p` is the linear equivalence
`x ↦ (fderiv ℝ g p x, C x)` — and invert it.  The inverse of `Φ` is analytic near
`(g p, 0)` by the analytic inverse function theorem
(`OpenPartialHomeomorph.analyticAt_symm'`), and since a function analytic at a point is
analytic on a whole neighbourhood of it (`AnalyticAt.eventually_analyticAt`), the chart is
analytic on all of a neighbourhood of `0`.  Note that only `AnalyticAt ℝ g p` is needed:
the chart, and the whole construction, lives in a neighbourhood of `p`.
-/

namespace Work.WilE9G.Sard

open scoped Topology

theorem levelSetChartV {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : AnalyticAt ℝ g p) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (V : Set (fderiv ℝ g p).ker)
      (U : Set (Fin n → ℝ)) (C : (Fin n → ℝ) →L[ℝ] (fderiv ℝ g p).ker),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      (∀ v ∈ V, AnalyticAt ℝ γ v) ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → C (y - p) ∈ V ∧ γ (C (y - p)) = y) := by
  classical
  -- A continuous linear projection onto the kernel `W = ker (fderiv ℝ g p)`.
  have hker : (fderiv ℝ g p).ker.ClosedComplemented :=
    (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin n → ℝ) →L[ℝ] (fderiv ℝ g p).ker := Classical.choose hker
  have hC : ∀ x : (fderiv ℝ g p).ker, C x = x := Classical.choose_spec hker
  haveI : CompleteSpace (fderiv ℝ g p).ker :=
    (fderiv ℝ g p).isClosed_ker.completeSpace_coe
  -- The implicit function data for `Φ x = (g x, C (x - p))`.
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) (fderiv ℝ g p).ker :=
    { leftFun := g
      leftDeriv := fderiv ℝ g p
      rightFun := fun x => C (x - p)
      rightDeriv := C
      pt := p
      hasStrictFDerivAt_leftFun := hg.hasStrictFDerivAt
      hasStrictFDerivAt_rightFun :=
        C.hasStrictFDerivAt.comp p ((hasStrictFDerivAt_id p).sub_const p)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj hC
      isCompl_ker := LinearMap.isCompl_of_proj hC }
  have hleft : ∀ x, φ.leftFun x = g x := fun x => rfl
  have hright : ∀ x, φ.rightFun x = C (x - p) := fun x => rfl
  have hpt : φ.pt = p := rfl
  -- `Φ = φ.prodFun` is analytic at `p`.
  have hC_an : AnalyticAt ℝ (fun x : Fin n → ℝ => C (x - p)) p := by
    have h3 := (C.analyticAt p).sub (analyticAt_const (v := C p) (x := p))
    have heq : (⇑C) - (fun _ : Fin n → ℝ => C p) = (fun x : Fin n → ℝ => C (x - p)) := by
      funext x; simp
    rwa [heq] at h3
  have hΦ : AnalyticAt ℝ φ.prodFun p := by
    have hprod := hg.prod hC_an
    have heq : φ.prodFun = (fun x : Fin n → ℝ => (g x, C (x - p))) := by
      funext x
      rw [ImplicitFunctionData.prodFun_apply, hleft, hright]
    rw [heq]
    exact hprod
  -- Its derivative at `p` is the linear equivalence `x ↦ (fderiv ℝ g p x, C x)`.
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin k → ℝ) × (fderiv ℝ g p).ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hfderiv : fderiv ℝ φ.prodFun p
      = (e : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × (fderiv ℝ g p).ker) := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
    rw [hpt] at h
    exact h
  -- The chart, obtained by inverting `Φ` and restricting to the slice `g = g p`.
  let γ : (fderiv ℝ g p).ker → (Fin n → ℝ) :=
    fun v => φ.toOpenPartialHomeomorph.symm (g p, v)
  have hγ_an0 : AnalyticAt ℝ γ 0 := by
    have h1 : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) p := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hΦ
    have h2 : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) p = e := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hfderiv
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm'
      φ.pt_mem_toOpenPartialHomeomorph_source h1 h2
    have hptimg : φ.toOpenPartialHomeomorph p
        = ((g p, (0 : (fderiv ℝ g p).ker)) :
            (Fin k → ℝ) × (fderiv ℝ g p).ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    -- `h3 : AnalyticAt ℝ (⇑symm) (φ.toOpenPartialHomeomorph φ.pt)`
    have h3' : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
        ((g p, (0 : (fderiv ℝ g p).ker)) :
          (Fin k → ℝ) × (fderiv ℝ g p).ker) := by
      rw [hpt, hptimg] at h3
      exact h3
    have h2' : AnalyticAt ℝ
        (fun v : (fderiv ℝ g p).ker =>
          ((g p, v) : (Fin k → ℝ) × (fderiv ℝ g p).ker)) 0 := by
      have h := (analyticAt_const (v := g p) (x := (0 : (fderiv ℝ g p).ker))).prod
        (analyticAt_id (𝕜 := ℝ) (z := (0 : (fderiv ℝ g p).ker)))
      simpa using h
    simpa [γ, Function.comp_def] using h3'.comp h2'
  -- Any function analytic at `0` is analytic on a neighbourhood of `0`.
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hγ_an0.eventually_analyticAt
  -- The chart domain, and the corresponding neighbourhood of `p` (defined so that the
  -- `C`-coordinate of every level point in `U` automatically lies in `V`).
  let Vt : Set (fderiv ℝ g p).ker :=
    {v | ((g p, v) : (Fin k → ℝ) × (fderiv ℝ g p).ker) ∈ φ.toOpenPartialHomeomorph.target}
  let V : Set (fderiv ℝ g p).ker := Vt ∩ Metric.ball 0 ρ
  let U : Set (Fin n → ℝ) :=
    {y | y ∈ φ.toOpenPartialHomeomorph.source ∧ C (y - p) ∈ V}
  have hVt_open : IsOpen Vt :=
    φ.toOpenPartialHomeomorph.open_target.preimage (continuous_const.prodMk continuous_id)
  have hV_open : IsOpen V := hVt_open.inter Metric.isOpen_ball
  have h0Vt : (0 : (fderiv ℝ g p).ker) ∈ Vt := by
    have h := φ.toOpenPartialHomeomorph.map_source (φ.pt_mem_toOpenPartialHomeomorph_source)
    simpa [Vt, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h
  have h0V : (0 : (fderiv ℝ g p).ker) ∈ V := ⟨h0Vt, Metric.mem_ball_self hρpos⟩
  have hU_open : IsOpen U := by
    refine φ.toOpenPartialHomeomorph.open_source.inter ?_
    exact hV_open.preimage (C.continuous.comp (continuous_id.sub continuous_const))
  have hpU : p ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
    · simpa using h0V
  have hγ0 : γ 0 = p := by
    have hpsrc : p ∈ φ.toOpenPartialHomeomorph.source := by
      simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
    have h0 : ((g p, (0 : (fderiv ℝ g p).ker)) :
        (Fin k → ℝ) × (fderiv ℝ g p).ker) = φ.toOpenPartialHomeomorph p := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    show φ.toOpenPartialHomeomorph.symm
      ((g p, (0 : (fderiv ℝ g p).ker)) : (Fin k → ℝ) × (fderiv ℝ g p).ker) = p
    rw [h0]
    exact φ.toOpenPartialHomeomorph.left_inv hpsrc
  have hγ_an : ∀ t ∈ V, AnalyticAt ℝ γ t := fun t ht => hρsub ht.2
  have hγC : ∀ t ∈ V, C (γ t - p) = t := by
    intro t ht
    have h := congr_arg Prod.snd (φ.toOpenPartialHomeomorph.right_inv ht.1)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright] using h
  have hγU : ∀ t ∈ V, γ t ∈ U := by
    intro t ht
    refine ⟨?_, ?_⟩
    · show φ.toOpenPartialHomeomorph.symm (g p, t) ∈ φ.toOpenPartialHomeomorph.source
      exact φ.toOpenPartialHomeomorph.map_target ht.1
    · rw [hγC t ht]; exact ht
  have hγh : ∀ t ∈ V, g (γ t) = g p := by
    intro t ht
    have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv ht.1)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright] using h
  have hlast : ∀ y ∈ U, g y = g p → C (y - p) ∈ V ∧ γ (C (y - p)) = y := by
    intro y hy hyh
    obtain ⟨hysrc, hyV⟩ := hy
    refine ⟨hyV, ?_⟩
    have hy' : φ.toOpenPartialHomeomorph y
        = ((g p, C (y - p)) : (Fin k → ℝ) × (fderiv ℝ g p).ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hyh]
    show φ.toOpenPartialHomeomorph.symm (g p, C (y - p)) = y
    rw [← hy']
    exact φ.toOpenPartialHomeomorph.left_inv hysrc
  exact ⟨γ, V, U, C, hV_open, hU_open, h0V, hpU, hγ0, hγ_an, hγU, hγh, hlast⟩

end Work.WilE9G.Sard
