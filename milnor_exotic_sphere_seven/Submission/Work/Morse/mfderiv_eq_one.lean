import Mathlib
import Submission.Work.Morse.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- **Local existence of a smooth vector field with `df(v) = 1` at a regular point.**

If `x₀` is not a critical point of the smooth function `f` on the manifold `M`, then there is a
neighbourhood `W` of `x₀` and a smooth section `s` of the tangent bundle such that
`mfderiv f x (s x) = 1` for all `x ∈ W`.

The section is built from a chart `c` at `x₀`: writing `g = f ∘ c.symm`, one picks `u` with
`fderiv ℝ g (c x₀) u ≠ 0` and sets, in the trivialisation of the tangent bundle at `x₀`, the
coordinate function `a y = (fderiv ℝ g y u)⁻¹ • u`, so that `fderiv ℝ g y (a y) = 1`. -/
theorem exists_local_section {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x₀ : M}
    (hx₀ : ¬ IsCritPoint (n := n) f x₀) :
    ∃ (W : Set M) (_ : W ∈ 𝓝 x₀) (s : (x : M) → TangentSpace (𝓡 n) x),
      ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, s x⟩ : TangentBundle (𝓡 n) M)) W ∧
      ∀ x ∈ W, (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (s x) : ℝ) = 1 := by
  let E := EuclideanSpace ℝ (Fin n)
  let c : M → E := fun y => (extChartAt (𝓡 n) x₀) y
  let g : E → ℝ := fun y => f ((extChartAt (𝓡 n) x₀).symm y)
  have hxmem : x₀ ∈ (extChartAt (𝓡 n) x₀).source := mem_extChartAt_source x₀
  have hsrcopen : IsOpen (extChartAt (𝓡 n) x₀).source := isOpen_extChartAt_source (I := 𝓡 n) x₀
  have hcong_at : ∀ x ∈ (extChartAt (𝓡 n) x₀).source, f =ᶠ[𝓝 x] (g ∘ c) := by
    intro x hx
    filter_upwards [hsrcopen.mem_nhds hx] with y hy
    show f y = g (c y)
    simp only [g, c]
    rw [(extChartAt (𝓡 n) x₀).left_inv hy]
  have hcd_at : ∀ x ∈ (extChartAt (𝓡 n) x₀).source, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) c x := by
    intro x hx
    refine (mdifferentiableAt_extChartAt (I := 𝓡 n) (x := x₀) ?_).congr_of_eventuallyEq ?_
    · rw [← extChartAt_source (𝓡 n) x₀]; exact hx
    · filter_upwards with y; rfl
  have hg_symm : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (fun y => (extChartAt (𝓡 n) x₀).symm y)
      (extChartAt (𝓡 n) x₀).target := contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀
  have hgs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g (extChartAt (𝓡 n) x₀).target := by
    refine (hf.contMDiffOn (s := (extChartAt (𝓡 n) x₀).source)).comp hg_symm ?_
    intro y hy
    exact (extChartAt (𝓡 n) x₀).map_target hy
  have htgtopen : IsOpen (extChartAt (𝓡 n) x₀).target := isOpen_extChartAt_target (I := 𝓡 n) x₀
  have hgd_at : ∀ x ∈ (extChartAt (𝓡 n) x₀).source, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) g (c x) := by
    intro x hx
    exact (hgs.contMDiffAt (htgtopen.mem_nhds ((extChartAt (𝓡 n) x₀).map_source hx))).mdifferentiableAt (by simp)
  have hbase : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x₀ = fderiv ℝ g (c x₀) := by
    have hc : mfderiv (𝓡 n) 𝓘(ℝ, E) c x₀ = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x₀) := by
      simpa [c] using mfderiv_extChartAt_self (I := 𝓡 n) (x := x₀)
    rw [(hcong_at x₀ hxmem).mfderiv_eq]
    rw [mfderiv_comp x₀ (hgd_at x₀ hxmem) (hcd_at x₀ hxmem)]
    rw [mfderiv_eq_fderiv, hc]
    exact ContinuousLinearMap.comp_id (f := fderiv ℝ g (c x₀))
  have hfd : fderiv ℝ g (c x₀) ≠ 0 := by
    rw [← hbase]; exact hx₀
  obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ g (c x₀) u ≠ 0 := by
    by_contra h
    push Not at h
    exact hfd (ContinuousLinearMap.ext h)
  let η : E → ℝ := fun y => fderiv ℝ g y u
  let A : Set E := (extChartAt (𝓡 n) x₀).target ∩ {y | η y ≠ 0}
  have hgt : ContDiffOn ℝ ∞ g (extChartAt (𝓡 n) x₀).target := hgs.contDiffOn
  have hηt : ContDiffOn ℝ ∞ η (extChartAt (𝓡 n) x₀).target := by
    have hfd_g : ContDiffOn ℝ ∞ (fderiv ℝ g) (extChartAt (𝓡 n) x₀).target :=
      hgt.fderiv_of_isOpen htgtopen (by simp)
    simpa [η] using hfd_g.clm_apply (contDiffOn_const (c := u) (s := (extChartAt (𝓡 n) x₀).target))
  have hAopen : IsOpen A := by
    have h1 : IsOpen ((extChartAt (𝓡 n) x₀).target ∩ η ⁻¹' ({0}ᶜ)) :=
      hηt.continuousOn.isOpen_inter_preimage htgtopen (isOpen_compl_singleton (x := (0:ℝ)))
    convert h1 using 1
    ext y
    simp [A]
  have hηA : ContDiffOn ℝ ∞ η A := hηt.mono Set.inter_subset_left
  have hcA : c x₀ ∈ A := by
    refine ⟨(extChartAt (𝓡 n) x₀).map_source hxmem, ?_⟩
    show η (c x₀) ≠ 0
    exact hu
  let a : E → E := fun y => (η y)⁻¹ • u
  have ha : ContDiffOn ℝ ∞ a A := by
    have hinv : ContDiffOn ℝ ∞ (fun y => (η y)⁻¹) A := hηA.inv (fun y hy => hy.2)
    have h2 : ContDiffOn ℝ ∞ ((fun y => (η y)⁻¹) • (fun _ : E => u)) A :=
      hinv.smul (contDiffOn_const (c := u) (s := A))
    have hfun : ((fun y => (η y)⁻¹) • (fun _ : E => u)) = a := by
      funext y; simp [a]
    rwa [hfun] at h2
  let t := trivializationAt E (TangentSpace (𝓡 n)) x₀
  let s : (x : M) → TangentSpace (𝓡 n) x := fun x => t.symmL ℝ x (a (c x))
  let W : Set M := (extChartAt (𝓡 n) x₀).source ∩ c ⁻¹' A
  have hφsrc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c ((chartAt E x₀).source) := by
    simpa [c] using contMDiffOn_extChartAt (I := 𝓡 n) (x := x₀)
  have hWopen : IsOpen W := by
    have h1 := hφsrc.continuousOn.isOpen_inter_preimage (chartAt E x₀).open_source hAopen
    simpa [W, extChartAt_source] using h1
  have hφW : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c W := by
    refine hφsrc.mono ?_
    intro x hx
    rw [← extChartAt_source (𝓡 n) x₀]
    exact hx.1
  have hWbase : W ⊆ t.baseSet := by
    intro x hx
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (𝓡 n) x₀]
    exact hx.1
  have hx₀W : x₀ ∈ W := ⟨hxmem, hcA⟩
  have hWnhds : W ∈ 𝓝 x₀ := hWopen.mem_nhds hx₀W
  have hcoord : ∀ x ∈ W, (t ⟨x, s x⟩).2 = a (c x) := by
    intro x hx
    have hb : x ∈ t.baseSet := hWbase hx
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb (s x)]
    change t.linearMapAt ℝ x (s x) = a (c x)
    rw [show s x = t.symm x (a (c x)) from Bundle.Trivialization.symmL_apply t hb (a (c x))]
    exact Bundle.Trivialization.linearMapAt_symm t hb (a (c x))
  have hsmooth : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (fun x => (⟨x, s x⟩ : TangentBundle (𝓡 n) M)) W := by
    refine (Bundle.Trivialization.contMDiffOn_section_iff t hWopen hWbase).mpr ?_
    refine (ha.contMDiffOn.comp hφW (fun x hx => hx.2)).congr (fun x hx => ?_)
    rw [Function.comp_apply]
    exact hcoord x hx
  refine ⟨W, hWnhds, s, hsmooth, ?_⟩
  intro x hx
  have hxsrc : x ∈ (extChartAt (𝓡 n) x₀).source := hx.1
  have hηc : η (c x) ≠ 0 := hx.2.2
  have hbasex : x ∈ t.baseSet := hWbase hx
  have hc_x : mfderiv (𝓡 n) 𝓘(ℝ, E) c x = t.continuousLinearMapAt ℝ x := by
    refine (TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓡 n) (x₀ := x₀) (x := x) ?_).symm
    rw [← extChartAt_source (𝓡 n) x₀]; exact hxsrc
  have hcoordC : t.continuousLinearMapAt ℝ x (s x) = a (c x) := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hbasex (s x)]
    exact hcoord x hx
  have hmap_x : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = fderiv ℝ g (c x) ∘SL t.continuousLinearMapAt ℝ x := by
    rw [(hcong_at x hxsrc).mfderiv_eq]
    rw [mfderiv_comp x (hgd_at x hxsrc) (hcd_at x hxsrc)]
    rw [mfderiv_eq_fderiv, hc_x]
    rfl
  have happ : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (s x)
      = fderiv ℝ g (c x) (t.continuousLinearMapAt ℝ x (s x)) :=
    congrArg (fun L => L (s x)) hmap_x
  have hsecond : fderiv ℝ g (c x) (t.continuousLinearMapAt ℝ x (s x)) = 1 := by
    rw [hcoordC]
    show fderiv ℝ g (c x) ((η (c x))⁻¹ • u) = 1
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    have hη_eq : η (c x) = fderiv ℝ g (c x) u := rfl
    rw [← hη_eq]
    exact inv_mul_cancel₀ hηc
  exact happ.trans hsecond

/-- On a compact set `K` on which the differential of a smooth function `f` never vanishes, there
exists a smooth vector field `v` with `df(v) = 1` on `K`. -/
theorem mfderiv_eq_one {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M] {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {K : Set M} (hK : IsCompact K) (hreg : ∀ x ∈ K, ¬ IsCritPoint (n := n) f x) :
    ∃ v : (x : M) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)) ∧
      ∀ x ∈ K, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hUopen : IsOpen {x : M | ¬ IsCritPoint (n := n) f x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨W, hW, s, hs, hval⟩ := exists_local_section (n := n) hf hx
    refine Filter.mem_of_superset hW (fun y hy => ?_)
    intro hyc
    have hv : (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f y (s y) : ℝ) = 1 := hval y hy
    rw [hyc] at hv
    simp only [zero_apply] at hv
    have hv' : ((0 : ℝ)) = 1 := hv
    exact zero_ne_one hv'
  have hUnhds : {x : M | ¬ IsCritPoint (n := n) f x} ∈ 𝓝ˢ K :=
    hUopen.mem_nhdsSet.mpr hreg
  obtain ⟨V, hVopen, hKV, hVcl⟩ := hK.exists_isOpen_closure_subset hUnhds
  obtain ⟨φ, hφ1, hφ0, hφ01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (𝓡 n) hK.isClosed
    (by rw [hVopen.interior_eq]; exact hKV) (n := ⊤)
  have hsupp : Function.support (fun x => φ x) ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (hφ0 x hxV)
  have htsupp : tsupport (fun x => φ x) ⊆ {x : M | ¬ IsCritPoint (n := n) f x} :=
    (closure_mono hsupp).trans hVcl
  have hφsmooth : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (fun x => φ x) := by
    simpa using φ.contMDiff
  let tt : ∀ x : M, Set (TangentSpace (𝓡 n) x) := fun x => {w | mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x w = φ x}
  have hconv : ∀ x, Convex ℝ (tt x) := by
    intro x
    change Convex ℝ ({w | mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x w = φ x} : Set (TangentSpace (𝓡 n) x))
    exact Convex.linear_preimage (convex_singleton (φ x : ℝ)) (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x).toLinearMap
  have hHloc : ∀ x₀ : M, ∃ Ux ∈ 𝓝 x₀, ∃ s_loc : (x : M) → TangentSpace (𝓡 n) x,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, s_loc x⟩ : TangentBundle (𝓡 n) M)) Ux ∧
      ∀ y ∈ Ux, s_loc y ∈ tt y := by
    intro x₀
    by_cases hx : IsCritPoint (n := n) f x₀
    · refine ⟨(tsupport (fun x => φ x))ᶜ, (isClosed_tsupport _).isOpen_compl.mem_nhds ?_, (fun _ => 0), ?_, ?_⟩
      · exact fun h => (htsupp h) hx
      · exact Bundle.contMDiffOn_zeroSection (𝕜 := ℝ) (IB := 𝓡 n) (F := E)
          (E := TangentSpace (𝓡 n)) (t := (tsupport (fun x => φ x))ᶜ) (n := ∞)
      · intro y hy
        have hy0 : φ y = 0 := by
          by_contra h
          exact hy (subset_tsupport _ (Function.mem_support.mpr h))
        show (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f y (0 : TangentSpace (𝓡 n) y) : ℝ) = φ y
        rw [map_zero]
        show ((0 : ℝ)) = φ y
        rw [hy0]
    · obtain ⟨W, hW, s₁, hs₁, hval₁⟩ := exists_local_section (n := n) hf hx
      refine ⟨W, hW, (fun x => φ x • s₁ x), ?_, ?_⟩
      · exact hφsmooth.contMDiffOn.smul_section hs₁
      · intro y hy
        show (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f y (φ y • s₁ y) : ℝ) = φ y
        rw [map_smul]
        have h2 : (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f y (s₁ y) : ℝ) = 1 := hval₁ y hy
        rw [h2]
        show (φ y • (1:ℝ) : ℝ) = φ y
        rw [smul_eq_mul, mul_one]
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local (𝓡 n)
    (TangentSpace (𝓡 n)) tt hconv hHloc (n := ⊤)
  refine ⟨fun x => s x, ?_, ?_⟩
  · exact s.contMDiff_toFun
  · intro x hx
    have hx1 : φ x = 1 := Filter.Eventually.self_of_nhdsSet hφ1 x hx
    have hmem := hs x
    change mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x (s x) = φ x at hmem
    rw [hx1] at hmem
    exact hmem

end Work.Morse
