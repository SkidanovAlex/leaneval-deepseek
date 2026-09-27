import Mathlib
import Submission.Work.Drive.N2C.circlePhase

/-!
# A local phase function for an immersed curve in a surface

Given a `C^∞` immersion `γ : ℝ → M` of the real line into a surface `M` (a manifold modelled on
`EuclideanSpace ℝ (Fin 2)`), and a parameter `t₀`, there is an open neighbourhood `U` of `γ t₀`
and a `C^∞` function `φ : M → ℝ` with `φ (γ t) = t` for all `t` near `t₀`.

The proof is the classical one: in a chart at `γ t₀`, choose a linear functional `ℓ` which does not
vanish on the (nonzero) tangent vector `mfderiv γ t₀ 1`; the scalar function `f s = t₀ + ℓ (γ̂ s)`
(where `γ̂` is the chart expression of `γ`) has nonzero derivative at `t₀`, so it is locally
invertible there; the inverse, composed with the chart and `t₀ + ℓ ·`, is the desired phase.

The only subtlety is that the inverse function theorem in Mathlib gives smoothness only *at* a point
for the `C^∞` index (the index `((⊤ : ℕ∞) : WithTop ℕ∞)` is `C^∞`, not analytic), so we first record
that `f` is `C^∞` on the whole open set `J = γ ⁻¹' (chart source)`, and then use the (pointwise)
inverse function theorem at each point of a small target neighbourhood where the derivative of `f`
stays nonzero.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

theorem exists_localPhase_of_immersed_curve {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    (γ : ℝ → M)
    (hγsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (himm : ∀ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) γ t 1 ≠ 0) (t₀ : ℝ) :
    ∃ (U : Set M) (φ : M → ℝ), IsOpen U ∧ γ t₀ ∈ U ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) φ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), φ (γ t) = t := by
  let E := EuclideanSpace ℝ (Fin 2)
  let p : M := γ t₀
  set v : E := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀ 1 with hvdef
  have hv : v ≠ 0 := by rw [hvdef]; exact himm t₀
  obtain ⟨ℓ, _hℓnorm, hℓv⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.mpr hv)
  -- the chart at `p` agrees with the extended chart
  have hExt : ∀ y : M, extChartAt 𝓘(ℝ,E) p y = chartAt E p y := by
    intro y
    simp only [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe]
    rfl
  -- the coordinate expression of `γ`
  have hWchart : ∀ s : ℝ, writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) t₀ γ s = chartAt E p (γ s) := by
    intro s
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, Function.id_comp, modelWithCornersSelf_coe_symm]
    rw [show chartAt ℝ t₀ = OpenPartialHomeomorph.refl ℝ from @chartAt_self_eq ℝ _ (x := t₀)]
    rfl
  -- the scalar function whose inverse we will use
  let f : ℝ → ℝ := fun s => t₀ + ℓ (chartAt E p (γ s))
  -- its derivative at `t₀`
  have hwritten : HasFDerivAt (writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) t₀ γ)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀) t₀ := by
    have hmf : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀ (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀) :=
      (hγsm.contMDiffAt (x := t₀)).mdifferentiableAt (by simp) |>.hasMFDerivAt
    have h := (hmf.2).hasFDerivAt
      (show (Set.range 𝓘(ℝ,ℝ)) ∈ 𝓝 ((extChartAt 𝓘(ℝ,ℝ) t₀) t₀) from by simp)
    rwa [show ((extChartAt 𝓘(ℝ,ℝ) t₀) t₀) = t₀ from by simp [chartAt_self_eq]] at h
  have hf_deriv : HasFDerivAt f (ℓ.comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀)) t₀ := by
    have h1 : HasFDerivAt (⇑ℓ ∘ writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) t₀ γ)
        (ℓ.comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀)) t₀ :=
      HasFDerivAt.comp (hg := ℓ.hasFDerivAt) (hf := hwritten)
    have h2 : HasFDerivAt (fun s => t₀ + ℓ (writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) t₀ γ s))
        (ℓ.comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀)) t₀ := h1.const_add t₀
    rwa [show (fun s => t₀ + ℓ (writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) t₀ γ s)) = f from by
      funext s; rw [hWchart s]] at h2
  have hf'_ne : (ℓ.comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀)) 1 ≠ 0 := by
    rw [show (ℓ.comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀)) 1
        = ℓ (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t₀ 1) from rfl]
    rw [← hvdef, hℓv]
    exact norm_ne_zero_iff.mpr hv
  have hderiv_ne : deriv f t₀ ≠ 0 := by
    rw [hf_deriv.hasDerivAt.deriv]
    exact hf'_ne
  -- `f` is `C^∞` on the open set `J` where the chart is defined
  let J : Set ℝ := γ ⁻¹' (chartAt E p).source
  have hJopen : IsOpen J := (chartAt E p).open_source.preimage hγsm.continuous
  have ht₀J : t₀ ∈ J := mem_chart_source E p
  have hfJ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f J := by
    have hchartJ : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => chartAt E p y) (chartAt E p).source :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := p) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).congr
        (fun y _ => hExt y)
    have hγJ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((⊤ : ℕ∞) : WithTop ℕ∞) γ J :=
      hγsm.contMDiffOn.mono (subset_univ J)
    have hcomp : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => chartAt E p (γ s)) J :=
      hchartJ.comp hγJ (show J ⊆ γ ⁻¹' (chartAt E p).source from fun _ ht => ht)
    have hℓc : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => ℓ (chartAt E p (γ s))) J :=
      (ℓ.contMDiff.contMDiffOn).comp hcomp
        (show J ⊆ (fun s => chartAt E p (γ s)) ⁻¹' univ from fun _ _ => trivial)
    have hfin : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => t₀ + ℓ (chartAt E p (γ s))) J := contMDiffOn_const.add hℓc
    exact contMDiffOn_iff_contDiffOn.mp hfin
  have hf_smooth_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f t₀ :=
    (hfJ t₀ ht₀J).contDiffAt (hJopen.mem_nhds ht₀J)
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict : HasStrictDerivAt f (deriv f t₀) t₀ := hf_smooth_at.hasStrictDerivAt hn
  let i : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv f t₀) hderiv_ne)
  have hstrictF : HasStrictFDerivAt f (i : ℝ →L[ℝ] ℝ) t₀ :=
    hstrict.hasStrictFDerivAt_equiv hderiv_ne
  let R : OpenPartialHomeomorph ℝ ℝ := hstrictF.toOpenPartialHomeomorph f
  have hRcoe : ⇑R = f := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrictF
  have hRsource : t₀ ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrictF
  have hRtarget : f t₀ ∈ R.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hstrictF
  let g : ℝ → ℝ := ⇑R.symm
  have hg_left : ∀ᶠ s in 𝓝 t₀, g (f s) = s := by
    have h := hstrictF.eventually_left_inverse
    rw [HasStrictFDerivAt.localInverse_def hstrictF] at h
    exact h
  have hgft₀ : g (f t₀) = t₀ := by
    have h := HasStrictFDerivAt.localInverse_apply_image hstrictF
    rw [HasStrictFDerivAt.localInverse_def hstrictF] at h
    exact h
  -- the derivative of `f` does not vanish near `t₀`
  have hcont_deriv : ContinuousOn (deriv f) J :=
    hfJ.continuousOn_deriv_of_isOpen hJopen
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by simp)
  have hderiv_ev : ∀ᶠ t in 𝓝 t₀, deriv f t ≠ 0 :=
    (hcont_deriv.continuousAt (hJopen.mem_nhds ht₀J)).eventually_ne hderiv_ne
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hderiv_ev
  let J' : Set ℝ := J ∩ Metric.ball t₀ ε
  have hJ'open : IsOpen J' := hJopen.inter Metric.isOpen_ball
  have ht₀J' : t₀ ∈ J' := ⟨ht₀J, Metric.mem_ball_self hεpos⟩
  -- the region of the target on which the local inverse is `C^∞`
  let W : Set ℝ := R.target ∩ (⇑R.symm : ℝ → ℝ) ⁻¹' J'
  have hWopen : IsOpen W := R.continuousOn_symm.isOpen_inter_preimage R.open_target hJ'open
  have hWft₀ : f t₀ ∈ W := by
    refine ⟨hRtarget, ?_⟩
    show g (f t₀) ∈ J'
    rw [hgft₀]
    exact ht₀J'
  have hgW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g W := by
    rw [IsOpen.contDiffOn_iff hWopen]
    intro a ha
    rw [contDiffAt_infty]
    intro n
    have ha1 : a ∈ R.target := ha.1
    have ha2 : (↑R.symm : ℝ → ℝ) a ∈ J' := ha.2
    have ha2J : (↑R.symm : ℝ → ℝ) a ∈ J := ha2.1
    have hf_a : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ((↑R.symm : ℝ → ℝ) a) :=
      (hfJ _ ha2J).contDiffAt (hJopen.mem_nhds ha2J)
    have hf_a' : ContDiffAt ℝ (↑n) f ((↑R.symm : ℝ → ℝ) a) :=
      hf_a.of_le (by exact_mod_cast le_top)
    have hderivAt : HasDerivAt f (deriv f ((↑R.symm : ℝ → ℝ) a)) ((↑R.symm : ℝ → ℝ) a) :=
      (hf_a.differentiableAt (by simp)).hasDerivAt
    have hderivAtR : HasDerivAt (↑R) (deriv f ((↑R.symm : ℝ → ℝ) a)) ((↑R.symm : ℝ → ℝ) a) := by
      rw [hRcoe]
      exact hderivAt
    have hne : deriv f ((↑R.symm : ℝ → ℝ) a) ≠ 0 := hεsub ha2.2
    exact R.contDiffAt_symm_deriv (f₀' := deriv f ((↑R.symm : ℝ → ℝ) a)) hne ha1 hderivAtR hf_a'
  -- a ball in the chart whose image under the local inverse lies in `W`
  let c : E := chartAt E p p
  have hft₀ : f t₀ = t₀ + ℓ c := rfl
  have hWnhds : {x : E | t₀ + ℓ x ∈ W} ∈ 𝓝 c := by
    have hcont : ContinuousAt (fun x : E => t₀ + ℓ x) c := by fun_prop
    refine hcont.preimage_mem_nhds ?_
    have hWmem : W ∈ 𝓝 (t₀ + ℓ c) := by rw [← hft₀]; exact hWopen.mem_nhds hWft₀
    exact hWmem
  obtain ⟨r, hrpos, hrW⟩ := Metric.mem_nhds_iff.mp hWnhds
  refine ⟨(chartAt E p).source ∩ (chartAt E p) ⁻¹' (Metric.ball c r),
    (fun y : M => g (t₀ + ℓ (chartAt E p y))), ?_, ?_, ?_, ?_⟩
  · exact (chartAt E p).continuousOn.isOpen_inter_preimage (chartAt E p).open_source
      Metric.isOpen_ball
  · exact ⟨mem_chart_source E p, by
      show chartAt E p p ∈ Metric.ball c r
      exact Metric.mem_ball_self hrpos⟩
  · have hg₁ : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : E => g (t₀ + ℓ x)) (Metric.ball c r) := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => g (t₀ + ℓ x))
          (Metric.ball c r) :=
        hgW.comp (contDiff_const.add ℓ.contDiff).contDiffOn (fun x hx => hrW hx)
      exact h1.contMDiffOn
    have hchart_md : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => chartAt E p y)
        ((chartAt E p).source ∩ (chartAt E p) ⁻¹' (Metric.ball c r)) :=
      ((contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := p)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mono Set.inter_subset_left).congr (fun y _ => hExt y)
    exact hg₁.comp hchart_md (fun y hy => hy.2)
  · obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
      (show {s : ℝ | g (f s) = s} ∈ 𝓝 t₀ from hg_left)
    refine ⟨δ, hδpos, ?_⟩
    intro t ht
    have ht' : t ∈ Metric.ball t₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [f] using hδ ht'

end Work.Drive.N2C
