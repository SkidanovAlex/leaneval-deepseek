/-
  `Work.WilE7.Aux.criticalLevelSetLocallyConst`

  Local constancy, near a regular point `p`, of an analytic function `F` along the zero set of an
  analytic map `g` whose differential at `p` is surjective, assuming `dF` vanishes on `ker dg`
  along that zero set.

  ## Mathematical content

  Let `f' = fderiv ℝ g p`.  Since `f'` is onto and we are in finite dimension, its kernel is a
  complemented subspace; choosing a continuous projection `L` onto it makes

  `Φ = (g, fun x ↦ L (x - p)) : ℝⁿ → ℝᵏ × ker f'`

  a local homeomorphism at `p` with `Φ p = (g p, 0)`, whose inverse is analytic at `(g p, 0)`
  (analytic inverse function theorem, `OpenPartialHomeomorph.analyticAt_symm'`).  Slicing at the
  first coordinate gives a local chart `γ` of the fibre `{g = g p}` by `ker f'`, with an explicit
  continuous "parameter map" `σ` (`CritChart.analyticChart` below).

  `F ∘ γ` is analytic at `0`, and its derivative vanishes on a neighbourhood of `0`:  indeed
  `g ∘ γ` is constantly `g p` near `0`, so `0 = fderiv (g ∘ γ) = fderiv g ∘ fderiv γ`, i.e. the
  range of `fderiv γ` lies in `ker (fderiv g)`; the hypothesis `hcrit` then gives
  `fderiv F ∘ fderiv γ = 0`.  Hence `F ∘ γ` is constant near `0`, and `σ` transports this back to
  a neighbourhood of `p`, because every point of the fibre close to `p` equals `γ (σ ·)`.

  ## A note on the environment

  The module path `Submission/Work/WilE7/Aux/…` has the path component `Aux`, and
  `Lean.Elab.checkModuleNamePortability` rejects module names containing `Aux` (`AUX` is a
  reserved file name on some operating systems) while processing the *header*, before any command
  of the file is elaborated.  Consequently `lake build
  Submission.Work.WilE7.Aux.criticalLevelSetLocallyConst` cannot recompile this file from source,
  whatever its contents.  A byte-identical copy of this file lives at
  `Submission/Work/WilE7/AuxLC/criticalLevelSetLocallyConst.lean` (module
  `Submission.Work.WilE7.AuxLC.criticalLevelSetLocallyConst`), which builds; its `.olean` carries
  the very same declaration `Work.WilE7.Aux.criticalLevelSetLocallyConst`.
-/
import Mathlib

noncomputable section

open Set Filter
open scoped Topology

namespace Work.WilE7.Aux

namespace CritChart

/-- Local analytic parametrization of the fibre `{g = g p}` of an analytic map whose differential
at `p` is surjective.  The parametrization `γ` is defined on (a neighbourhood `V` of `0` in) the
kernel of the differential, maps `0` to `p`, is analytic at `0`, and is complemented by a globally
continuous "parameter" map `σ`: every point of the fibre close to `p` is `γ (σ ·)`, with `σ`
continuous and `σ p = 0`. -/
theorem analyticChart {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (σ : (Fin n → ℝ) → (fderiv ℝ g p).ker)
      (V : Set (fderiv ℝ g p).ker) (U : Set (Fin n → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ ContinuousOn γ V ∧ Continuous σ ∧ σ p = 0 ∧
      (∀ v ∈ V, γ v ∈ U ∧ g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → σ y ∈ V ∧ γ (σ y) = y) := by
  let f' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p
  have hgp : HasStrictFDerivAt g f' p := (hg p).hasStrictFDerivAt
  have hker : f'.ker.ClosedComplemented := f'.ker_closedComplemented_of_finiteDimensional_range
  let L : (Fin n → ℝ) →L[ℝ] f'.ker := Classical.choose hker
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) f'.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented g f' hgp hsurj hker
  have hleft : φ.leftFun = g := rfl
  have hright : ∀ x, φ.rightFun x = L (x - p) := fun _ => rfl
  have hpt : φ.pt = p := rfl
  -- analyticity of the product map at `p`
  have hLin_an : AnalyticAt ℝ (fun x : Fin n → ℝ => L (x - p)) p := by
    have hsub : AnalyticAt ℝ (fun x : Fin n → ℝ => x - p) p :=
      (analyticAt_id (𝕜 := ℝ) (z := p)).sub (analyticAt_const (v := p))
    exact (L.analyticAt (p - p)).comp (f := fun x : Fin n → ℝ => x - p) hsub
  have hΦ : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) p := by
    have h := (hg p).prod hLin_an
    have h' : (fun x : Fin n → ℝ => (g x, L (x - p))) = (⇑φ.toOpenPartialHomeomorph) := by
      funext x
      show (g x, L (x - p)) = φ.toOpenPartialHomeomorph x
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      rfl
    rwa [h'] at h
  -- the derivative is a linear equivalence
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin k → ℝ) × f'.ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
      φ.isCompl_ker
  have hfderiv : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) p
      = (e : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × f'.ker) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe]
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  -- the inverse is analytic at `(g p, 0)`
  have hsymm_an : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
      ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
    have h0 : p ∈ φ.toOpenPartialHomeomorph.source :=
      hpt ▸ φ.pt_mem_toOpenPartialHomeomorph_source
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm' (i := e) h0 hΦ hfderiv
    have hpt' : φ.toOpenPartialHomeomorph p = ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    rwa [hpt'] at h3
  -- the parametrization and its "inverse"
  let γ : f'.ker → (Fin n → ℝ) := φ.implicitFunction (g p)
  let σ : (Fin n → ℝ) → f'.ker := fun y => L (y - p)
  let V : Set f'.ker :=
    {v | ((g p, v) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target}
  let U : Set (Fin n → ℝ) := φ.toOpenPartialHomeomorph.source
  have hγval : ∀ v : f'.ker,
      γ v = φ.toOpenPartialHomeomorph.symm ((g p, v) : (Fin k → ℝ) × f'.ker) := by
    intro v
    show φ.implicitFunction (g p) v = _
    rw [ImplicitFunctionData.implicitFunction_apply]
  have hγan : AnalyticAt ℝ γ 0 := by
    have h2 : AnalyticAt ℝ (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) 0 :=
      (analyticAt_const (v := g p)).prod (analyticAt_id (𝕜 := ℝ) (z := (0 : f'.ker)))
    have h3 := hsymm_an.comp h2
    have h4 : γ = (⇑φ.toOpenPartialHomeomorph.symm) ∘
        (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) := by
      funext v
      rw [Function.comp_apply, hγval v]
    rw [h4]
    exact h3
  have hγcont : ContinuousOn γ V := by
    have hf : Continuous (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) :=
      continuous_const.prodMk continuous_id
    have h1 : ContinuousOn (⇑φ.toOpenPartialHomeomorph.symm) φ.toOpenPartialHomeomorph.target :=
      φ.toOpenPartialHomeomorph.continuousOn_invFun
    have h2 : ContinuousOn
        (fun v : f'.ker =>
          φ.toOpenPartialHomeomorph.symm ((g p, v) : (Fin k → ℝ) × f'.ker)) V :=
      h1.comp hf.continuousOn (fun v hv => hv)
    have h3 : γ = (⇑φ.toOpenPartialHomeomorph.symm) ∘
        (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) := by
      funext v
      rw [Function.comp_apply, hγval v]
    rw [h3]
    exact h2
  have hσcont : Continuous σ :=
    L.continuous.comp (continuous_id.sub continuous_const)
  have hVopen : IsOpen V :=
    φ.toOpenPartialHomeomorph.open_target.preimage
      (continuous_const.prodMk (continuous_id : Continuous fun v : f'.ker => v))
  have hUopen : IsOpen U := φ.toOpenPartialHomeomorph.open_source
  have h0V : (0 : f'.ker) ∈ V := by
    show ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target
    have h := φ.map_pt_mem_toOpenPartialHomeomorph_target
    rw [hpt] at h
    simpa [hleft, hright] using h
  have hpU : p ∈ U := hpt ▸ φ.pt_mem_toOpenPartialHomeomorph_source
  have hγ0 : γ 0 = p := by
    have h0mem : p ∈ φ.toOpenPartialHomeomorph.source :=
      hpt ▸ φ.pt_mem_toOpenPartialHomeomorph_source
    have hpt' : φ.toOpenPartialHomeomorph p = ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    show φ.implicitFunction (g p) 0 = p
    rw [ImplicitFunctionData.implicitFunction_apply, ← hpt']
    exact φ.toOpenPartialHomeomorph.left_inv h0mem
  have hσp : σ p = 0 := by
    show L (p - p) = 0
    simp
  have hVg : ∀ v ∈ V, γ v ∈ U ∧ g (γ v) = g p := by
    intro v hv
    constructor
    · show γ v ∈ φ.toOpenPartialHomeomorph.source
      rw [hγval v]
      exact φ.toOpenPartialHomeomorph.map_target hv
    · rw [hγval v]
      have h := φ.toOpenPartialHomeomorph.right_inv hv
      have h2 : (φ.toOpenPartialHomeomorph
          (φ.toOpenPartialHomeomorph.symm ((g p, v) : (Fin k → ℝ) × f'.ker))).1 = g p := by
        rw [h]
      exact h2
  have hσγ : ∀ y ∈ U, g y = g p → σ y ∈ V ∧ γ (σ y) = y := by
    intro y hy hgy
    have heq : ((g p, σ y) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph y := by
      have h : φ.toOpenPartialHomeomorph y = ((g y, σ y) : (Fin k → ℝ) × f'.ker) := by
        rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
        rfl
      rw [h, hgy]
    constructor
    · show ((g p, σ y) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target
      rw [heq]
      exact φ.toOpenPartialHomeomorph.map_source hy
    · show γ (σ y) = y
      rw [hγval (σ y), heq]
      exact φ.toOpenPartialHomeomorph.left_inv hy
  exact ⟨γ, σ, V, U, hVopen, hUopen, h0V, hpU, hγ0, hγan, hγcont, hσcont, hσp, hVg, hσγ⟩

end CritChart

/-- **Local constancy along a regular level set.**  If `g` and `F` are analytic on `ℝⁿ`, the
differential of `g` is surjective at `p`, and `dF` vanishes on `ker dg` along the zero set of `g`
near `p`, then `F` is constant on the zero set of `g` near `p`. -/
theorem criticalLevelSetLocallyConst {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (F : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hF : ∀ q, AnalyticAt ℝ F q)
    (hsurj : (fderiv ℝ g p).range = ⊤)
    (hcrit : ∀ᶠ y in nhds p, g y = 0 → ∀ v, (fderiv ℝ g y) v = 0 → (fderiv ℝ F y) v = 0) :
    ∀ᶠ y in nhds p, g y = 0 → F y = F p := by
  by_cases hgp : g p = 0
  · -- main case: `p` lies on the zero set
    obtain ⟨γ, σ, V, U, hVopen, hUopen, h0V, hpU, hγ0, hγan, _hγcont, hσcont, hσp, hVg, hσγ⟩ :=
      CritChart.analyticChart g p hg hsurj
    -- `F ∘ γ` is analytic at `0`
    have hHan : AnalyticAt ℝ (fun v => F (γ v)) 0 :=
      AnalyticAt.comp (show AnalyticAt ℝ (fun y => F y) (γ 0) from hF (γ 0)) hγan
    -- `γ` is differentiable near `0`
    have hγdiff : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), DifferentiableAt ℝ γ v :=
      hγan.eventually_analyticAt.mono fun v hv => hv.differentiableAt
    -- `γ` tends to `p` at `0`
    have hγtend : Tendsto γ (𝓝 (0 : (fderiv ℝ g p).ker)) (𝓝 p) := by
      have h : Tendsto γ (𝓝 (0 : (fderiv ℝ g p).ker)) (𝓝 (γ 0)) := hγan.continuousAt
      rwa [hγ0] at h
    -- the hypothesis holds at `γ v` for `v` near `0`
    have hγS : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        g (γ v) = 0 → ∀ w, (fderiv ℝ g (γ v)) w = 0 → (fderiv ℝ F (γ v)) w = 0 :=
      hγtend.eventually hcrit
    -- `g ∘ γ` has zero derivative on `V`
    have hgc : ∀ v ∈ V, fderiv ℝ (fun w => g (γ w)) v = 0 := by
      intro v hv
      have hev : (fun w => g (γ w)) =ᶠ[𝓝 v] (fun _ => g p) :=
        Filter.eventually_of_mem (hVopen.mem_nhds hv) fun w hw => (hVg w hw).2
      rw [hev.fderiv_eq]
      exact (hasFDerivAt_const (g p) v).fderiv
    -- derivative of `F ∘ γ` vanishes near `0`
    have hzero : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        fderiv ℝ (fun w => F (γ w)) v = 0 := by
      filter_upwards [hγS, hVopen.mem_nhds h0V, hγdiff] with v hvS hvV hvdiff
      have hvd : fderiv ℝ (fun w => g (γ w)) v = 0 := hgc v hvV
      have h1 : fderiv ℝ (fun w => g (γ w)) v
          = (fderiv ℝ g (γ v)).comp (fderiv ℝ γ v) := by
        simpa only [Function.comp_def] using
          fderiv_comp (𝕜 := ℝ) v (f := γ) (g := fun y => g y)
            (hg (γ v)).differentiableAt hvdiff
      rw [h1] at hvd
      have h2 : fderiv ℝ (fun w => F (γ w)) v
          = (fderiv ℝ F (γ v)).comp (fderiv ℝ γ v) := by
        simpa only [Function.comp_def] using
          fderiv_comp (𝕜 := ℝ) v (f := γ) (g := fun y => F y)
            (hF (γ v)).differentiableAt hvdiff
      rw [h2]
      refine ContinuousLinearMap.ext fun e => ?_
      have h3 : (fderiv ℝ g (γ v)) ((fderiv ℝ γ v) e) = 0 := by
        have h := congrArg (fun (M : (fderiv ℝ g p).ker →L[ℝ] (Fin k → ℝ)) => M e) hvd
        simpa [ContinuousLinearMap.comp_apply] using h
      have h4 := hvS (by rw [(hVg v hvV).2, hgp]) ((fderiv ℝ γ v) e) h3
      simpa [ContinuousLinearMap.comp_apply] using h4
    -- `F ∘ γ` is constant near `0`
    have hdiffH : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        DifferentiableAt ℝ (fun w => F (γ w)) v :=
      hHan.eventually_analyticAt.mono fun v hv => hv.differentiableAt
    have hconst : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), F (γ v) = F p := by
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hdiffH.and hzero)
      filter_upwards [Metric.ball_mem_nhds (0 : (fderiv ℝ g p).ker) hr] with v hv
      have hc := IsOpen.is_const_of_fderiv_eq_zero (Metric.isOpen_ball)
        (convex_ball (0 : (fderiv ℝ g p).ker) r).isPreconnected
        (fun z hz => (hsub hz).1.differentiableWithinAt)
        (fun z hz => (hsub hz).2) (Metric.mem_ball_self hr) hv
      simpa [hγ0] using hc.symm
    -- transport back to `p` along `σ`
    have hσev : ∀ᶠ y in 𝓝 p, F (γ (σ y)) = F p := by
      filter_upwards [(hσcont.continuousAt (x := p)).preimage_mem_nhds
        (by rw [hσp]; exact hconst)] with y hy
      simpa only [Set.mem_preimage, Set.mem_setOf_eq] using hy
    filter_upwards [hσev, hUopen.mem_nhds hpU] with y hy hUy
    intro hgy
    have hgyp : g y = g p := by rw [hgy, hgp]
    obtain ⟨_hσyV, hγσy⟩ := hσγ y hUy hgyp
    rw [← hγσy]
    exact hy
  · -- `p` is not on the zero set: the statement is vacuous near `p`
    have hne : ∀ᶠ y in 𝓝 p, g y ≠ 0 :=
      (hg p).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hgp)
    filter_upwards [hne] with y hy hgy
    exact absurd hgy hy

end Work.WilE7.Aux
