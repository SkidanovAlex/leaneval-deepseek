import Mathlib

noncomputable section

open Set Filter
open scoped Topology

namespace Work.WilE7.Aux

/-- Local analytic parametrization of the level set `g = g p` of an analytic map with
surjective derivative at `p`.  `γ` parametrizes the level set near `p` by the kernel of
`fderiv ℝ g p`, and `σ` is "the inverse" in the sense that it recovers the parameter of a
point of the level set close to `p`. -/
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

/-- A preconnected set which meets an open set `u` and whose complement in it is (relatively)
open contains no point outside `u`. -/
theorem preconnected_subset_of_open_of_closed {α : Type*} [TopologicalSpace α]
    {s u : Set α} (hs : IsPreconnected s) (hu : IsOpen u) (hne : (s ∩ u).Nonempty)
    (hclosed : ∃ v : Set α, IsOpen v ∧ s ∩ v = s \ u) : s ⊆ u := by
  obtain ⟨v, hv, hsv⟩ := hclosed
  by_contra hsub
  obtain ⟨x, hxs, hxu⟩ := not_subset.mp hsub
  have hxsv : x ∈ s ∩ v := by rw [hsv]; exact ⟨hxs, hxu⟩
  have hsvne : (s ∩ v).Nonempty := ⟨x, hxsv⟩
  have hsuv : s ⊆ u ∪ v := by
    intro y hy
    by_cases hyu : y ∈ u
    · exact Or.inl hyu
    · right
      have hy' : y ∈ s \ u := ⟨hy, hyu⟩
      rw [← hsv] at hy'
      exact hy'.2
  obtain ⟨y, hys, hyu, hyv⟩ := hs u v hu hv hsuv hne hsvne
  have hy' : y ∈ s ∩ v := ⟨hys, hyv⟩
  rw [hsv] at hy'
  exact hy'.2 hyu

/-- An analytic function which is locally constant along a full-rank analytic level set is
constant on every preconnected piece of that level set. -/
theorem constantOnLevelSet {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (F : (Fin n → ℝ) → ℝ) (C : Set (Fin n → ℝ)) (z : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hF : ∀ q, AnalyticAt ℝ F q)
    (hzC : z ∈ C) (hCpre : IsPreconnected C)
    (hloc : ∀ p ∈ C, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ p ∈ U ∧ C ∩ U = {y | g y = 0} ∩ U)
    (hrank : ∀ p ∈ C, (fderiv ℝ g p).range = ⊤)
    (hvanish : ∀ᶠ y in nhds z, g y = 0 → F y = F z) :
    ∀ p ∈ C, F p = F z := by
  -- `C` lies in the zero set of `g`
  have hCZ : ∀ p ∈ C, g p = 0 := by
    intro p hp
    obtain ⟨U, hUo, hpU, hCU⟩ := hloc p hp
    have hp' : p ∈ C ∩ U := ⟨hp, hpU⟩
    rw [hCU] at hp'
    exact hp'.1
  -- the set where `F` is locally constant along the zero set of `g`
  let B : Set (Fin n → ℝ) := {y | ∀ᶠ w in nhds y, g w = 0 → F w = F z}
  have hBopen : IsOpen B := isOpen_setOfPred_eventually_nhds
  have hzB : z ∈ B := hvanish
  have hBF : ∀ y ∈ B, g y = 0 → F y = F z := by
    intro y hy hgy
    exact (mem_of_mem_nhds hy) hgy
  -- `C ∩ B` is closed in `C`
  have hclosed : closure (C ∩ B) ∩ C ⊆ B := by
    rintro p ⟨hpcl, hpC⟩
    obtain ⟨γ, σ, V, U, hVo, hUo, h0V, hpU, hγ0, hγan, hγcont, hσcont, hσp, hVg, hσγ⟩ :=
      analyticChart g p hg (hrank p hpC)
    have hgp0 : g p = 0 := hCZ p hpC
    -- the function `v ↦ F (γ v) - F z` is analytic near `0`
    have hhan : AnalyticAt ℝ (fun v => F (γ v) - F z) 0 := by
      have h1 : AnalyticAt ℝ (fun v => F (γ v)) 0 := (hF (γ 0)).comp hγan
      exact h1.sub (analyticAt_const (v := F z))
    obtain ⟨r, hrpos, hran⟩ := hhan.exists_ball_analyticOnNhd
    have hballpre : IsPreconnected (Metric.ball (0 : (fderiv ℝ g p).ker) r) :=
      (convex_ball (0 : (fderiv ℝ g p).ker) r).isPreconnected
    -- choose an accumulation point of `C ∩ B` close to `p` on the level set
    have hΩopen : IsOpen (U ∩ σ ⁻¹' Metric.ball (0 : (fderiv ℝ g p).ker) r) :=
      hUo.inter ((Metric.isOpen_ball).preimage hσcont)
    have hpΩ : p ∈ U ∩ σ ⁻¹' Metric.ball (0 : (fderiv ℝ g p).ker) r :=
      ⟨hpU, by
        rw [mem_preimage, hσp]
        exact Metric.mem_ball_self hrpos⟩
    obtain ⟨y, hyΩ, hyCB⟩ := (mem_closure_iff.mp hpcl) _ hΩopen hpΩ
    obtain ⟨hyC, hyB⟩ := hyCB
    have hyU : y ∈ U := hyΩ.1
    have hyball : σ y ∈ Metric.ball (0 : (fderiv ℝ g p).ker) r := hyΩ.2
    have hgy : g y = 0 := hCZ y hyC
    have hgyp : g y = g p := by rw [hgy, hgp0]
    obtain ⟨hσyV, hγσy⟩ := hσγ y hyU hgyp
    have hyF : F y = F z := hBF y hyB hgy
    -- an open set on which `v ↦ F (γ v) - F z` vanishes near `σ y`
    obtain ⟨W0, hW0sub, hW0open, hyW0⟩ := mem_nhds_iff.mp hyB
    have hWopen : IsOpen (V ∩ γ ⁻¹' W0) := hγcont.isOpen_inter_preimage hVo hW0open
    have hσyW : σ y ∈ V ∩ γ ⁻¹' W0 := ⟨hσyV, by rw [mem_preimage, hγσy]; exact hyW0⟩
    have hev : (fun v => F (γ v) - F z) =ᶠ[nhds (σ y)] 0 := by
      filter_upwards [hWopen.mem_nhds hσyW] with v hv
      have h1 : γ v ∈ W0 := hv.2
      have h2 : g (γ v) = g p := (hVg v hv.1).2
      have h3 : F (γ v) = F z := hW0sub h1 (by rw [h2, hgp0])
      exact sub_eq_zero.mpr h3
    -- identity theorem on the ball
    have hball : ∀ v ∈ Metric.ball (0 : (fderiv ℝ g p).ker) r, F (γ v) - F z = 0 := fun v hv =>
      hran.eqOn_zero_of_preconnected_of_eventuallyEq_zero hballpre hyball hev hv
    -- conclude `p ∈ B`
    show ∀ᶠ w in nhds p, g w = 0 → F w = F z
    have hσev : ∀ᶠ w in nhds p, σ w ∈ Metric.ball (0 : (fderiv ℝ g p).ker) r :=
      hσcont.continuousAt.preimage_mem_nhds
        ((Metric.isOpen_ball).mem_nhds (by rw [hσp]; exact Metric.mem_ball_self hrpos))
    filter_upwards [hσev, hUo.mem_nhds hpU] with w hwball hwU hgw
    have hgwp : g w = g p := by rw [hgw, hgp0]
    obtain ⟨_, hγσw⟩ := hσγ w hwU hgwp
    have h4 : F (γ (σ w)) - F z = 0 := hball (σ w) hwball
    rw [hγσw] at h4
    exact sub_eq_zero.mp h4
  -- preconnectedness finishes the job
  have hCsubB : C ⊆ B := by
    refine preconnected_subset_of_open_of_closed hCpre hBopen ⟨z, hzC, hzB⟩
      ⟨(closure (C ∩ B))ᶜ, isClosed_closure.isOpen_compl, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, fun hxB => hx.2 (subset_closure ⟨hx.1, hxB⟩)⟩
    · intro hx
      exact ⟨hx.1, fun hxcl => hx.2 (hclosed ⟨hxcl, hx.1⟩)⟩
  intro p hp
  exact hBF p (hCsubB hp) (hCZ p hp)

end Work.WilE7.Aux
