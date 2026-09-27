import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Noncompact.CompressionTube.ctc.exists_local_transverse_piece
import Submission.Work.Noncompact.CompressionTube.ctc.transverse_open
import Submission.Work.Noncompact.CompressionTube.ctc.exists_gauge
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_blend
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_on_Icc
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The transverse coordinate along a compact arc

Local versions of the `ctc` chain (which was stated for a *properly embedded line* and a global
height function) adapted to a compact arc `γ '' Icc a b` on which `g ∘ γ = id`: no properness, no
global injectivity, no second countability, and all vanishing/height hypotheses local.
-/

namespace Work.Noncompact.Routing

open scoped Manifold ContDiff
open Topology Set Function Filter
open Work.Noncompact.CompressionTube

noncomputable section

/-- Local form of `Work.Noncompact.CompressionTube.mfderiv_g_velocity`: it suffices that `g ∘ γ = id`
on a neighbourhood of the parameter. -/
theorem mfderiv_g_velocity_loc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {g : M → ℝ}
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {s : ℝ} (h : (fun t : ℝ => g (γ t)) =ᶠ[𝓝 s] id) :
    mfderiv (MC n) MCreal g (γ s) (mfderiv MCreal (MC n) γ s 1) = 1 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hγd : MDifferentiableAt MCreal (MC n) γ s := hγ.mdifferentiableAt (x := s) hn
  have hgd : MDifferentiableAt (MC n) MCreal g (γ s) := hg.mdifferentiableAt (x := γ s) hn
  have hcomp : mfderiv MCreal MCreal (fun t : ℝ => g (γ t)) s =
      (mfderiv (MC n) MCreal g (γ s)).comp (mfderiv MCreal (MC n) γ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MCreal) (f := γ) (g := g) s hgd hγd
  have h3 : ((mfderiv (MC n) MCreal g (γ s)).comp (mfderiv MCreal (MC n) γ s)) 1 = 1 := by
    rw [← hcomp, h.mfderiv_eq_v433, mfderiv_id]
    rfl
  simpa using h3

set_option backward.isDefEq.respectTransparency false in
/-- **A function vanishing near the base parameter kills the velocity.**  Local form of
`Work.Noncompact.CompressionTube.mfderiv_velocity_eq_zero`. -/
theorem mfderiv_velocity_eq_zero_loc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    {s : ℝ} (h0 : ∀ᶠ t in 𝓝 s, ψ (γ t) = 0) :
    mfderiv (MC n) (MC (n - 1)) ψ (γ s) (mfderiv MCreal (MC n) γ s 1) = 0 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hγd : MDifferentiableAt MCreal (MC n) γ s := hγ.mdifferentiableAt (x := s) hn
  have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ (γ s) := hψ.mdifferentiableAt (x := γ s) hn
  have hcomp : mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (γ t)) s =
      (mfderiv (MC n) (MC (n - 1)) ψ (γ s)).comp (mfderiv MCreal (MC n) γ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC (n - 1)) (f := γ) (g := ψ) s hψd hγd
  have hz : (fun t : ℝ => ψ (γ t)) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin (n - 1)))) := by
    filter_upwards [h0] with t ht
    exact ht
  rw [hz.mfderiv_eq_v433, mfderiv_const] at hcomp
  have h := congrArg
    (fun (L : TangentSpace MCreal s →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) => L 1) hcomp
  simp only [zero_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **A raw transverse piece at a parameter.**  A local form of
`Work.Noncompact.CompressionTube.exists_local_transverse_piece`: it suffices that `g ∘ γ = id` on a
neighbourhood of `s₀`.  The conclusion also records a radius on which the piece vanishes along the
curve. -/
theorem exists_local_transverse_piece_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {s₀ : ℝ} (hgloc : (fun t : ℝ => g (γ t)) =ᶠ[𝓝 s₀] id) :
    ∃ (δ : ℝ) (ψ : M → EuclideanSpace ℝ (Fin (n - 1))),
      0 < δ ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧
      (∀ t : ℝ, |t - s₀| < δ → ψ (γ t) = 0) ∧ Transverse γ g ψ s₀ := by
  classical
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  have hgs₀ : g (γ s₀) = s₀ := hgloc.self_of_nhds
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hgloc
  have hδabs : ∀ t : ℝ, |t - s₀| < δ → g (γ t) = t := fun t ht =>
    hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)
  -- the chart at `γ s₀` and its (injective) derivative
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s₀) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s₀)
  have hcsrc : γ s₀ ∈ c.source := mem_chart_source _ (γ s₀)
  set D : TangentSpace (MC n) (γ s₀) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (fun x : M => c x) (γ s₀) with hDdef
  have hDinj : Function.Injective D := by
    rw [hDdef]
    exact isLocalDiffeomorphAt_chart_mfderiv_injective hc hcsrc
  have hvelne : mfderiv MCreal (MC n) γ s₀ (1 : ℝ) ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) = 0 := by
      have h2 := mfderiv_g_velocity_loc hγ hg hgloc (s := s₀)
      rw [h0, map_zero] at h2
      exact h2.symm
    exact one_ne_zero h1
  set vH : EuclideanSpace ℝ (Fin n) := D (mfderiv MCreal (MC n) γ s₀ 1) with hvHdef
  have hvHne : vH ≠ 0 := by
    rw [hvHdef]
    intro h
    refine hvelne (hDinj ?_)
    rw [h, map_zero]
  obtain ⟨H, hH⟩ := exists_coord_proj_kernel (n := n) (by omega) vH hvHne
  -- the ingredients of the transverse function
  set ρ : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => H (c x) with hρdef
  set hh : M → M := fun x => γ (g x) with hhdef
  set ψ₀ : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => ρ x - ρ (hh x) with hψ₀def
  set W : Set M := c.source ∩ hh ⁻¹' c.source with hWdef
  have hhh_cont : Continuous hh := by
    rw [hhdef]
    exact hγ.continuous.comp hg.continuous
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact c.open_source.inter (hhh_cont.isOpen_preimage c.source c.open_source)
  have hWs : γ s₀ ∈ W := by
    refine ⟨hcsrc, ?_⟩
    rw [hhdef]
    show γ (g (γ s₀)) ∈ c.source
    rw [hgs₀]
    exact hcsrc
  have hWmem : W ∈ 𝓝 (γ s₀) := hWopen.mem_nhds hWs
  obtain ⟨β, hβsupp, hβeq⟩ :
      ∃ β : SmoothBumpFunction (MC n) (γ s₀), tsupport β ⊆ W ∧ β =ᶠ[𝓝 (γ s₀)] 1 := by
    obtain ⟨f, hf, -⟩ :=
      (SmoothBumpFunction.nhds_basis_support (I := MC n) hWmem).mem_iff.mp hWmem
    exact ⟨f, hf, f.eventuallyEq_one⟩
  have hβsm : ContMDiff (MC n) MCreal smoothOrder (β : M → ℝ) := β.contMDiff
  set ψ : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => β x • ψ₀ x with hψdef
  -- smoothness of `ψ₀` on `W`
  have hψ₀smOn : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder ψ₀ W := by
    have h1 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder ρ W := by
      rw [hρdef]
      exact H.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => (hWdef ▸ hx).1))
    have h2 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder (fun x => ρ (hh x)) W := by
      rw [hρdef]
      refine H.contMDiff.comp_contMDiffOn ?_
      rw [hhdef]
      exact (contMDiffOn_of_mem_maximalAtlas hc).comp (hγ.comp hg).contMDiffOn
        (fun x hx => (hWdef ▸ hx).2)
    rw [hψ₀def]
    exact h1.sub h2
  -- global smoothness of `ψ`
  have hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ := by
    rw [hψdef]
    exact contMDiff_smul_of_tsupport_subset hWopen hβsm hβsupp hψ₀smOn
  -- `ψ` vanishes on the line near `s₀`
  have hψcore : ∀ t : ℝ, |t - s₀| < δ → ψ (γ t) = 0 := by
    intro t ht
    have h0 : ψ₀ (γ t) = 0 := by
      rw [hψ₀def, hhdef]
      simp [hδabs t ht]
    rw [hψdef]
    simp only []
    rw [h0, smul_zero]
  -- the derivative of `ψ₀` at `γ s₀`
  set dh : TangentSpace (MC n) (γ s₀) →L[ℝ] TangentSpace (MC n) (γ s₀) :=
    (mfderiv MCreal (MC n) γ s₀) ∘L (mfderiv (MC n) MCreal g (γ s₀)) with hdhdef
  have hhmem : hh (γ s₀) ∈ c.source := by
    rw [hhdef]
    show γ (g (γ s₀)) ∈ c.source
    rw [hgs₀]
    exact hcsrc
  have hhhderiv : HasMFDerivAt (MC n) (MC n) hh (γ s₀) dh := by
    have hγd : HasMFDerivAt MCreal (MC n) γ (g (γ s₀))
        (mfderiv MCreal (MC n) γ (g (γ s₀))) :=
      (hγ.mdifferentiableAt (x := g (γ s₀)) hn0).hasMFDerivAt
    have hgd : HasMFDerivAt (MC n) MCreal g (γ s₀) (mfderiv (MC n) MCreal g (γ s₀)) :=
      (hg.mdifferentiableAt (x := γ s₀) hn0).hasMFDerivAt
    have h := hγd.comp (γ s₀) hgd
    rw [mfderiv_congr_point (f := γ) hgs₀] at h
    rw [hdhdef]
    simpa only [hhdef, Function.comp_def] using h
  have hc_diff : MDifferentiableAt (MC n) (MC n) (fun x : M => c x) (hh (γ s₀)) :=
    ((contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt
      (c.open_source.mem_nhds hhmem)).mdifferentiableAt hn0
  have hρ' : HasMFDerivAt (MC n) (MC (n - 1)) ρ (hh (γ s₀)) (H ∘L D) := by
    rw [hρdef]
    have h := (ContinuousLinearMap.hasMFDerivAt H).comp (hh (γ s₀)) hc_diff.hasMFDerivAt
    have hpoint : hh (γ s₀) = γ s₀ := by
      rw [hhdef]
      show γ (g (γ s₀)) = γ s₀
      rw [hgs₀]
    have hmf : mfderiv (MC n) (MC n) (fun x : M => c x) (hh (γ s₀))
        = mfderiv (MC n) (MC n) (fun x : M => c x) (γ s₀) :=
      mfderiv_congr_point hpoint
    rw [hmf] at h
    rw [hDdef]
    simpa only [Function.comp_def] using h
  have hρderiv : HasMFDerivAt (MC n) (MC (n - 1)) ρ (γ s₀) (H ∘L D) := by
    rw [hρdef, hDdef]
    have hcd : MDifferentiableAt (MC n) (MC n) (fun x : M => c x) (γ s₀) :=
      ((contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt
        (c.open_source.mem_nhds hcsrc)).mdifferentiableAt hn0
    exact (ContinuousLinearMap.hasMFDerivAt H).comp (γ s₀) hcd.hasMFDerivAt
  have hρhh : HasMFDerivAt (MC n) (MC (n - 1)) (fun x : M => ρ (hh x)) (γ s₀)
      ((H ∘L D) ∘L dh) := by
    have h := hρ'.comp (γ s₀) hhhderiv
    simpa only [Function.comp_def] using h
  have hψ₀deriv : HasMFDerivAt (MC n) (MC (n - 1)) ψ₀ (γ s₀)
      ((H ∘L D) - ((H ∘L D) ∘L dh)) := hρderiv.sub hρhh
  have hψeq : ψ =ᶠ[𝓝 (γ s₀)] ψ₀ := by
    rw [hψdef]
    filter_upwards [hβeq] with x hx
    rw [hx]
    simp
  refine ⟨δ, ψ, hδpos, hψsm, hψcore, ?_⟩
  -- transversality at `s₀`
  intro v h1 h2
  have hmfd : mfderiv (MC n) (MC (n - 1)) ψ (γ s₀) = (H ∘L D) - ((H ∘L D) ∘L dh) := by
    rw [Filter.EventuallyEq.mfderiv_eq_v433 hψeq, HasMFDerivAt.mfderiv hψ₀deriv]
  have h3 : H (D v) - H (D (dh v)) = 0 := by
    have h4 : ((H ∘L D) - ((H ∘L D) ∘L dh)) v = 0 := by
      rw [← hmfd]
      exact h1
    simpa only [sub_apply, ContinuousLinearMap.comp_apply] using h4
  -- `dh v` in terms of `dg`
  have hdhv : dh v = mfderiv MCreal (MC n) γ s₀ (mfderiv (MC n) MCreal g (γ s₀) v) := by
    rw [hdhdef]
    exact ContinuousLinearMap.comp_apply _ _ _
  have hz : mfderiv MCreal (MC n) γ s₀ (mfderiv (MC n) MCreal g (γ s₀) v) = 0 := by
    rw [h2]
    exact map_zero (mfderiv MCreal (MC n) γ s₀)
  have hDdh : D (dh v) = 0 := by
    rw [hdhv]
    exact (congrArg D hz).trans (map_zero D)
  have h4 : H (D v) = 0 := by
    rw [hDdh] at h3
    simpa using h3
  obtain ⟨a, ha⟩ := (hH (D v)).mp h4
  have hv : v = a • (mfderiv MCreal (MC n) γ s₀ 1) := by
    refine hDinj ?_
    rw [map_smul, ← hvHdef, ← ha]
  have hdg : mfderiv (MC n) MCreal g (γ s₀) (a • mfderiv MCreal (MC n) γ s₀ 1) = a := by
    rw [map_smul, mfderiv_g_velocity_loc hγ hg hgloc, smul_eq_mul, mul_one]
  have ha0 : a = 0 := by
    have h5 := h2
    rw [hv] at h5
    rw [hdg] at h5
    exact h5
  rw [ha0, zero_smul] at hv
  exact hv

set_option backward.isDefEq.respectTransparency false in
/-- **Transversality is open in the parameter.**  Local form of
`Work.Noncompact.CompressionTube.transverse_open` (the global vanishing hypothesis is unused). -/
theorem exists_transverse_open_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ) {s₀ : ℝ}
    (hs : Transverse γ g ψ s₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s - s₀| < ρ → Transverse γ g ψ s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at the base point
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (γ s₀)
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s₀)
  have hcs : γ s₀ ∈ c.source := mem_chart_source _ (γ s₀)
  have hct : c (γ s₀) ∈ c.target := c.map_source hcs
  have hct' : c (γ s₀) ∈ c.symm.source := by
    rwa [OpenPartialHomeomorph.symm_source]
  have hmd : c.MDifferentiable (MC n) (MC n) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)
  -- the coordinate expression of `(ψ, g)`
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun y => (ψ (c.symm y), g (c.symm y)) with hF
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hct
  have hFdiff : ContDiffAt ℝ smoothOrder F (c (γ s₀)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => ψ (c.symm y)) (c (γ s₀)) :=
      (hψ.contMDiffAt (x := c.symm (c (γ s₀)))).comp (c (γ s₀)) hsymm
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => g (c.symm y)) (c (γ s₀)) :=
      (hg.contMDiffAt (x := c.symm (c (γ s₀)))).comp (c (γ s₀)) hsymm
    rw [hF]
    exact h1.contDiffAt.prodMk h2.contDiffAt
  -- the derivative of `F` at the base point is injective
  have hbase : c.symm (c (γ s₀)) = γ s₀ := c.left_inv hcs
  have hFind : Function.Injective (fderiv ℝ F (c (γ s₀))) := by
    have hd : fderiv ℝ F (c (γ s₀)) =
        ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
            (mfderiv (MC n) MCreal g (γ s₀))).comp
          (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀))) := by
      have h := (hasFDerivAt_coord_pair hψ hg hcm hct).fderiv
      rw [hbase] at h
      exact h
    rw [hd]
    have hP : Function.Injective ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
        (mfderiv (MC n) MCreal g (γ s₀))) := by
      intro a b hab
      have h0 : ((mfderiv (MC n) (MC (n - 1)) ψ (γ s₀)).prod
          (mfderiv (MC n) MCreal g (γ s₀))) (a - b) = 0 := by
        rw [map_sub, sub_eq_zero.mpr hab]
      have h1 : mfderiv (MC n) (MC (n - 1)) ψ (γ s₀) (a - b) = 0 := by
        have h := congrArg Prod.fst h0
        simpa [ContinuousLinearMap.prod_apply] using h
      have h2 : mfderiv (MC n) MCreal g (γ s₀) (a - b) = 0 := by
        have h := congrArg Prod.snd h0
        simpa [ContinuousLinearMap.prod_apply] using h
      exact sub_eq_zero.mp (hs _ h1 h2)
    have hS : Function.Injective
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₀))) :=
      (hmd.symm.mfderiv hct').injective
    intro a b hab
    exact hS (hP hab)
  -- the open set where the derivative of `F` stays injective
  obtain ⟨W, hWopen, hWmem, hWsub⟩ :=
    exists_open_injective_fderiv (finrank_euclideanSpace_prod (by omega)) hFdiff hn0 hFind
  -- a parameter interval mapping into it
  have hcontγ : ContinuousAt γ s₀ := hγ.continuous.continuousAt
  have hcontc : ContinuousAt c (γ s₀) := c.continuousAt hcs
  have hpre : γ ⁻¹' (c.source ∩ c ⁻¹' W) ∈ 𝓝 s₀ := by
    rw [preimage_inter]
    exact Filter.inter_mem (hcontγ.preimage_mem_nhds (c.open_source.mem_nhds hcs))
      (hcontγ.preimage_mem_nhds (hcontc.preimage_mem_nhds (hWopen.mem_nhds hWmem)))
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hεpos, fun s hs' => ?_⟩
  have hsball : s ∈ Metric.ball s₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hs'
  obtain ⟨hxsrc, hcxW⟩ := hεsub hsball
  have hcxt : c (γ s) ∈ c.target := c.map_source hxsrc
  have hleft : c.symm (c (γ s)) = γ s := c.left_inv hxsrc
  -- the derivatives at `γ s`, with concrete types
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ (γ s)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s)
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hxsrc
  have hderiv : fderiv ℝ F (c (γ s)) = (A.prod B).comp Se := by
    have h := (hasFDerivAt_coord_pair hψ hg hcm hcxt).fderiv
    rw [hleft] at h
    exact h
  have hderiv_inj : Function.Injective ((A.prod B).comp Se) := by
    rw [← hderiv]
    exact hWsub _ hcxW
  -- conclude
  intro v hv1 hv2
  have hv0 : (A.prod B) v = 0 := by
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext hv1 hv2
  have hval : Se (Ce v) = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [ContinuousLinearMap.comp_apply] using h1
  have hkey : ((A.prod B).comp Se) (Ce v) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hval, hv0]
  have hzero : Ce v = 0 := hderiv_inj (by simpa using hkey)
  calc v = Se (Ce v) := hval.symm
    _ = Se 0 := by rw [hzero]
    _ = 0 := map_zero Se

/-- **The linear gauge between two transverse functions, local form.** -/
theorem exists_gauge_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {s₀ : ℝ} (hgloc : (fun t : ℝ => g (γ t)) =ᶠ[𝓝 s₀] id)
    {ψ₁ ψ₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (h₁ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ₁)
    (h₂ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ₂)
    (h₁0 : ∀ᶠ t in 𝓝 s₀, ψ₁ (γ t) = 0) (h₂0 : ∀ᶠ t in 𝓝 s₀, ψ₂ (γ t) = 0)
    (hT₁ : Transverse γ g ψ₁ s₀) (hT₂ : Transverse γ g ψ₂ s₀) :
    ∃ A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)),
      Function.Injective A ∧
      (∀ v : TangentSpace (MC n) (γ s₀),
        A (mfderiv (MC n) (MC (n - 1)) ψ₂ (γ s₀) v) =
        mfderiv (MC n) (MC (n - 1)) ψ₁ (γ s₀) v) := by
  classical
  -- the two differentials at the base point, and the differential of `g`
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₁ (γ s₀)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₂ (γ s₀)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s₀)
  let vel : EuclideanSpace ℝ (Fin n) := mfderiv MCreal (MC n) γ s₀ 1
  -- the velocity of `γ` is killed by both differentials, and is not killed by `dg`
  have hvel₁ : L₁ vel = 0 := mfderiv_velocity_eq_zero_loc hγ h₁ h₁0 (s := s₀)
  have hvel₂ : L₂ vel = 0 := mfderiv_velocity_eq_zero_loc hγ h₂ h₂0 (s := s₀)
  have hvelg : Lg vel = 1 := mfderiv_g_velocity_loc hγ hg hgloc (s := s₀)
  -- the map `v ↦ (dψ₂ v, dg v)` is injective (this is the transversality of `ψ₂`)
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := L₂.prod Lg
  have hΦapply : ∀ v : EuclideanSpace ℝ (Fin n), Φ v = (L₂ v, Lg v) := fun v => rfl
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    have h : Φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : L₂ (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.fst h
    have h2 : Lg (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.snd h
    exact sub_eq_zero.mp (hT₂ (v - w) h1 h2)
  -- the domain and the target of `Φ` have the same dimension
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace,
      Module.finrank_self, Fintype.card_fin, Fintype.card_fin]
    omega
  have hΦinjL : Function.Injective Φ.toLinearMap := hΦinj
  -- hence `Φ` is a linear equivalence
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim
  have heapp : ∀ y : EuclideanSpace ℝ (Fin n), e y = Φ y := by
    intro y
    show (Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim) y = Φ y
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  -- a section of `dψ₂`, sending `u` to the unique `v` with `dψ₂ v = u`, `dg v = 0`
  let S : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.symm.toLinearMap.comp (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n - 1))) ℝ)
  have hSapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), S u = e.symm (u, 0) := fun u => rfl
  -- the gauge and its continuous version
  let Aₗ : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    L₁.toLinearMap.comp S
  let A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    Aₗ.toContinuousLinearMap
  have hAapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), A u = Aₗ u := fun u => rfl
  -- `S` is a right inverse of `dψ₂`
  have heS : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), e (S u) = (u, 0) := by
    intro u
    rw [hSapply u, LinearEquiv.apply_symm_apply]
  have hvel_e : e vel = (0, 1) := by
    rw [heapp vel, hΦapply vel, hvel₂, hvelg]
  -- the decomposition of a tangent vector along the velocity
  have hvec : ∀ v : EuclideanSpace ℝ (Fin n), S (L₂ v) + Lg v • vel = v := by
    intro v
    apply e.injective
    rw [map_add, map_smul, heS (L₂ v), hvel_e, heapp v, hΦapply v]
    simp
  refine ⟨A, ?_, ?_⟩
  · -- injectivity of the gauge
    intro x y hxy
    have hz : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : Aₗ (x - y) = 0 := by rw [← hAapply (x - y)]; exact hz
    have hL1 : L₁ (S (x - y)) = 0 := hz'
    have hLg : Lg (S (x - y)) = 0 := by
      have h := congrArg Prod.snd (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y))] at h
      simpa using h
    have hS0 : S (x - y) = 0 := hT₁ (S (x - y)) hL1 hLg
    have hxy0 : x - y = 0 := by
      have h := congrArg Prod.fst (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y)), hS0] at h
      simpa using h.symm
    exact sub_eq_zero.mp hxy0
  · -- the defining property of the gauge
    intro v
    change A (L₂ v) = L₁ v
    have h1 : A (L₂ v) = Aₗ (L₂ v) := rfl
    have h2 : Aₗ (L₂ v) = L₁ (S (L₂ v)) := rfl
    have h3 : L₁ v = L₁ (S (L₂ v)) := by
      conv_lhs => rw [← hvec v]
      rw [map_add, map_smul, hvel₁, smul_zero, add_zero]
    rw [h1, h2]
    exact h3.symm

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_transverse_blend_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {G₁ G₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hG₁ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₁)
    (hG₂ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₂)
    {s₁ δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hG₁0 : ∀ t : ℝ, |t - s₁| < δ₁ → G₁ (γ t) = 0)
    (hG₂0 : ∀ t : ℝ, |t - s₁| < δ₂ → G₂ (γ t) = 0)
    (hagree : mfderiv (MC n) (MC (n - 1)) G₁ (γ s₁) =
      mfderiv (MC n) (MC (n - 1)) G₂ (γ s₁))
    (htrans : Transverse γ g G₁ s₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ min δ₁ δ₂ ∧ ∀ (χ : ℝ → ℝ), ContDiff ℝ smoothOrder χ →
      (∀ t : ℝ, χ t ∈ Set.Icc 0 1) → ∀ s : ℝ, |s - s₁| < ρ →
        Transverse γ g
          (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at `γ s₁`
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s₁) with hcdef
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s₁)
  have hmd : c.MDifferentiable (MC n) (MC n) := mdifferentiable_chart (γ s₁)
  have hcsrc : γ s₁ ∈ c.source := mem_chart_source _ (γ s₁)
  have hy₁t : c (γ s₁) ∈ c.target := c.map_source hcsrc
  have hy₁t' : c (γ s₁) ∈ c.symm.source := by rwa [OpenPartialHomeomorph.symm_source]
  -- the coordinate expressions of `G₁`, `G₂`, `g`
  set A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₁ (c.symm y) with hAdef
  set B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₂ (c.symm y) with hBdef
  set Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => g (c.symm y) with hΓdef
  -- the manifold derivatives at the base point, with concrete types
  let Se₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₁))
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (γ s₁)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (γ s₁)
  let Lg₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s₁)
  have hSeInj : Function.Injective Se₁ := (hmd.symm.mfderiv hy₁t').injective
  have hAder : fderiv ℝ A (c (γ s₁)) = L₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hAdef]
    exact h
  have hBder : fderiv ℝ B (c (γ s₁)) = L₂.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hBdef]
    exact h
  have hΓder : fderiv ℝ Γ (c (γ s₁)) = Lg₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hg hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hΓdef]
    exact h
  -- the transversality hypothesis at the base point, in coordinates
  have hL12 : L₁ = L₂ := hagree
  have hBA : fderiv ℝ B (c (γ s₁)) = fderiv ℝ A (c (γ s₁)) := by
    rw [hBder, hAder, hL12]
  have hbase : ∀ δ : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ (c (γ s₁)) δ = 0 → fderiv ℝ A (c (γ s₁)) δ = 0 → δ = 0 := by
    intro δ h1 h2
    rw [hΓder] at h1
    rw [hAder] at h2
    change Lg₁ (Se₁ δ) = 0 at h1
    change L₁ (Se₁ δ) = 0 at h2
    have h3 : Se₁ δ = 0 := htrans (Se₁ δ) h2 h1
    exact hSeInj (by rw [h3, map_zero])
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨ε, hεpos, hεprop⟩ :=
    exists_uniform_blend_injective (fderiv ℝ A (c (γ s₁))) (fderiv ℝ Γ (c (γ s₁))) hbase
  -- continuity of the derivative of the coordinate expressions
  have hsymmb : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₁)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hy₁t
  have hAcd : ContDiffAt ℝ smoothOrder A (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₁ (c.symm y)) (c (γ s₁)) :=
      (hG₁.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hAdef]
    exact h1.contDiffAt
  have hBcd : ContDiffAt ℝ smoothOrder B (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₂ (c.symm y)) (c (γ s₁)) :=
      (hG₂.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hBdef]
    exact h1.contDiffAt
  have hΓcd : ContDiffAt ℝ smoothOrder Γ (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => g (c.symm y)) (c (γ s₁)) :=
      (hg.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hΓdef]
    exact h1.contDiffAt
  have hAcont : ContinuousAt (fderiv ℝ A) (c (γ s₁)) := hAcd.continuousAt_fderiv hn0
  have hBcont : ContinuousAt (fderiv ℝ B) (c (γ s₁)) := hBcd.continuousAt_fderiv hn0
  have hΓcont : ContinuousAt (fderiv ℝ Γ) (c (γ s₁)) := hΓcd.continuousAt_fderiv hn0
  -- a neighbourhood of the base point on which all the blends are injective
  have hnhds : ∀ᶠ y in 𝓝 (c (γ s₁)),
      ‖fderiv ℝ A y - fderiv ℝ A (c (γ s₁))‖ < ε ∧
      ‖fderiv ℝ B y - fderiv ℝ A (c (γ s₁))‖ < ε ∧
      ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (γ s₁))‖ < ε := by
    have h1 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ A y - fderiv ℝ A (c (γ s₁))‖ < ε := by
      have hb := hAcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ A (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    have h2 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ B y - fderiv ℝ A (c (γ s₁))‖ < ε := by
      have hb := hBcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ B (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hBA] at hy
    have h3 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (γ s₁))‖ < ε := by
      have hb := hΓcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ Γ (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp c.open_target (c (γ s₁)) hy₁t
  set r : ℝ := min r₁ r₂ with hrdef
  have hrpos : 0 < r := lt_min hr₁pos hr₂pos
  have hgood : ∀ y ∈ Metric.ball (c (γ s₁)) r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ν : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ y ν = 0 → (t • fderiv ℝ A y + (1 - t) • fderiv ℝ B y) ν = 0 → ν = 0 := by
    intro y hy t ht ν hv1 hv2
    have hy1 : y ∈ Metric.ball (c (γ s₁)) r₁ := by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left _ _)
    obtain ⟨hdA, hdB, hdΓ⟩ := hr₁sub hy1
    exact hεprop (fderiv ℝ A y) (fderiv ℝ B y) (fderiv ℝ Γ y) hdA hdB hdΓ t ht ν hv1 hv2
  -- the corresponding neighbourhood of `s₁`
  have hγc : ContinuousAt γ s₁ := hγ.continuous.continuousAt
  have hcc : ContinuousAt (fun s : ℝ => c (γ s)) s₁ := (c.continuousAt hcsrc).comp hγc
  have hV : {s : ℝ | γ s ∈ c.source ∧ c (γ s) ∈ Metric.ball (c (γ s₁)) r} ∈ 𝓝 s₁ := by
    have h1 : γ ⁻¹' c.source ∈ 𝓝 s₁ := hγc.preimage_mem_nhds (c.open_source.mem_nhds hcsrc)
    have h2 : (fun s : ℝ => c (γ s)) ⁻¹' Metric.ball (c (γ s₁)) r ∈ 𝓝 s₁ :=
      hcc.preimage_mem_nhds (Metric.ball_mem_nhds _ hrpos)
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min ρ (min δ₁ δ₂), lt_min hρpos (lt_min hδ₁ hδ₂), min_le_right _ _, ?_⟩
  intro χ hχ hχI s hs
  have hsρ : |s - s₁| < ρ := lt_of_lt_of_le hs (min_le_left _ _)
  have hsδ₁ : |s - s₁| < δ₁ :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsδ₂ : |s - s₁| < δ₂ :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hsrcc, hsball⟩ := hρsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hsρ)
  -- smoothness of the blended map
  have hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder
      (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) := by
    intro x
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => χ (g x)) x :=
      ((contMDiff_iff_contDiff.mpr hχ).contMDiffAt (x := g x)).comp x hg.contMDiffAt
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => 1 - χ (g x)) x :=
      contMDiffAt_const.sub h1
    exact (h1.smul hG₁.contMDiffAt).add (h2.smul hG₂.contMDiffAt)
  -- transversality of the blend
  intro v hv1 hv2
  have hyt : c (γ s) ∈ c.target := c.map_source hsrcc
  have hsymm : c.symm (c (γ s)) = γ s := c.left_inv hsrcc
  -- the manifold derivatives at `γ s`, with concrete types
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ s)
  let T₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (γ s)
  let T₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (γ s)
  let Mψ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1))
      (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) (γ s)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hsrcc
  have hAder' : fderiv ℝ A (c (γ s)) = T₁.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hAdef]
    exact h
  have hBder' : fderiv ℝ B (c (γ s)) = T₂.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hBdef]
    exact h
  have hΓder' : fderiv ℝ Γ (c (γ s)) = Lg.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hg hcm hyt).fderiv
    rw [hsymm] at h
    rw [hΓdef]
    exact h
  have hψder' : fderiv ℝ (fun y' => (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x)
        (c.symm y')) (c (γ s)) = Mψ.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hψsm hcm hyt).fderiv
    rw [hsymm] at h
    exact h
  have hprod : fderiv ℝ (fun y' => χ (g (c.symm y')) • G₁ (c.symm y')
        + (1 - χ (g (c.symm y'))) • G₂ (c.symm y')) (c (γ s))
      = χ (g (γ s)) • fderiv ℝ A (c (γ s)) + (1 - χ (g (γ s))) • fderiv ℝ B (c (γ s)) := by
    have h := fderiv_blend_coord (n := n) hχ hg hG₁ hG₂ hcm hyt
      (by rw [hsymm]; exact hG₁0 s hsδ₁) (by rw [hsymm]; exact hG₂0 s hsδ₂)
    rw [h, hsymm]
  -- the vector in coordinates
  let δ : EuclideanSpace ℝ (Fin n) := Ce v
  have hDs : Se δ = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [δ, ContinuousLinearMap.comp_apply] using h1
  have hΓ0 : fderiv ℝ Γ (c (γ s)) δ = 0 := by
    rw [hΓder']
    change Lg (Se δ) = 0
    rw [hDs]
    exact hv2
  have hZ0 : (χ (g (γ s)) • fderiv ℝ A (c (γ s))
      + (1 - χ (g (γ s))) • fderiv ℝ B (c (γ s))) δ = 0 := by
    rw [← hprod]
    have hbridge : (fun y' => χ (g (c.symm y')) • G₁ (c.symm y')
          + (1 - χ (g (c.symm y'))) • G₂ (c.symm y'))
        = (fun y' => (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) (c.symm y')) := by
      funext y'; rfl
    rw [hbridge, hψder']
    change Mψ (Se δ) = 0
    rw [hDs]
    exact hv1
  have hδ0 : δ = 0 :=
    hgood (c (γ s)) hsball (χ (g (γ s))) (hχI (g (γ s))) δ hΓ0 hZ0
  calc v = Se δ := hDs.symm
    _ = Se 0 := by rw [hδ0]
    _ = 0 := map_zero _


/-! ## The extension step of the chain -/

set_option maxHeartbeats 2000000 in
/-- **The extension step.**  A piece which is transverse on `[a, c]` and vanishes on a neighbourhood
of `c` is blended with a fresh piece centred at `s` with `|c - s| < ρ/2`, using the linear gauge of
`exists_gauge_loc` and the blend window of `exists_transverse_blend_loc`; the result is transverse
and vanishing on the whole interval `[a, min (s + ρ/2) b]`, and still vanishes on a neighbourhood of
the new right end. -/
theorem extension_step_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {A B a b c : ℝ} (hAa : A < a) (hab : a ≤ b) (hbB : b < B)
    (hgwin : ∀ t ∈ Set.Icc A B, g (γ t) = t) (hc : c ∈ Set.Icc a b)
    {Ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ)
    {δ : ℝ} (hδ : 0 < δ) (hΨ0 : ∀ t : ℝ, |t - c| < δ → Ψ (γ t) = 0)
    (hΨ0ab : ∀ t ∈ Set.Icc a c, Ψ (γ t) = 0)
    (hΨT : ∀ t ∈ Set.Icc a c, Transverse γ g Ψ t)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    {s ρ : ℝ} (hρ : 0 < ρ)
    (hψ0 : ∀ t : ℝ, |t - s| < ρ → ψ (γ t) = 0)
    (hψT : ∀ t : ℝ, |t - s| < ρ → Transverse γ g ψ t)
    (hcU : |c - s| < ρ / 2) :
    ∃ (Ψ' : M → EuclideanSpace ℝ (Fin (n - 1))) (δ' : ℝ),
      0 < δ' ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧
      (∀ t : ℝ, |t - min (s + ρ / 2) b| < δ' → Ψ' (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (min (s + ρ / 2) b), Ψ' (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (min (s + ρ / 2) b), Transverse γ g Ψ' t) := by
  classical
  have hcAB : c ∈ Set.Ioo A B := ⟨by linarith [hAa, hc.1], by linarith [hbB, hc.2]⟩
  -- `g ∘ γ = id` on a two-sided neighbourhood of the junction
  have hgc : (fun t : ℝ => g (γ t)) =ᶠ[𝓝 c] id := by
    have hpos : 0 < min (c - A) (B - c) / 2 :=
      half_pos (lt_min (by linarith [hcAB.1]) (by linarith [hcAB.2]))
    refine Filter.mem_of_superset (Metric.ball_mem_nhds c hpos) fun t ht => ?_
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have h1 := (abs_lt.mp ht).1
    have h2 := (abs_lt.mp ht).2
    exact hgwin t ⟨by linarith [h1, min_le_left (c - A) (B - c)],
      by linarith [h2, min_le_right (c - A) (B - c)]⟩
  have hcs : |c - s| < ρ := by rw [abs_lt] at hcU ⊢; constructor <;> linarith
  have hcs' : c - s < ρ / 2 := (abs_lt.mp hcU).2
  have hcs'' : s - c < ρ / 2 := by have := (abs_lt.mp hcU).1; linarith
  have hcT : Transverse γ g Ψ c := hΨT c ⟨hc.1, le_refl c⟩
  have hcψ : Transverse γ g ψ c := hψT c (by rw [abs_lt] at hcU ⊢; constructor <;> linarith)
  -- the vanishing of both pieces near the junction
  have hΨ0nhds : ∀ᶠ t in 𝓝 c, Ψ (γ t) = 0 := by
    refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun t ht => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact hΨ0 t ht
  have hψ0nhds : ∀ᶠ t in 𝓝 c, ψ (γ t) = 0 := by
    have hlt : ∀ᶠ t in 𝓝 c, |t - s| < ρ := by
      refine Metric.mem_nhds_iff.mpr ⟨ρ - |c - s|, by linarith, fun t ht => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq] at ht
      have h2 : |t - s| ≤ |t - c| + |c - s| := by
        calc |t - s| = |(t - c) + (c - s)| := by rw [show t - s = (t - c) + (c - s) by ring]
          _ ≤ |t - c| + |c - s| := abs_add_le _ _
      have h3 : |t - s| < (ρ - |c - s|) + |c - s| := by linarith [h2, ht]
      rwa [sub_add_cancel] at h3
    filter_upwards [hlt] with t ht
    exact hψ0 t ht
  -- the gauge
  obtain ⟨Ac, hAinj, hAeq⟩ := exists_gauge_loc hn hγ hg hgc hΨsm hψsm hΨ0nhds hψ0nhds hcT hcψ
  have hGsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder (fun x : M => Ac (ψ x)) :=
    Ac.contMDiff.comp hψsm
  have hGder : mfderiv (MC n) (MC (n - 1)) (fun x : M => Ac (ψ x)) (γ c) =
      mfderiv (MC n) (MC (n - 1)) Ψ (γ c) := by
    ext v : 1
    rw [mfderiv_clm_comp_apply hψsm Ac (γ c) v]
    exact hAeq v
  have hGtrans : ∀ t : ℝ, Transverse γ g ψ t → Transverse γ g (fun x : M => Ac (ψ x)) t := by
    intro t ht v hv1 hv2
    rw [mfderiv_clm_comp_apply hψsm Ac (γ t) v] at hv1
    exact ht v (hAinj (by rw [hv1]; exact (map_zero Ac).symm)) hv2
  have hG0win : ∀ t : ℝ, |t - c| < ρ / 4 → (fun x : M => Ac (ψ x)) (γ t) = 0 := by
    intro t ht
    have h1 : |t - s| < ρ := by
      have h2 : |t - s| ≤ |t - c| + |c - s| := by
        calc |t - s| = |(t - c) + (c - s)| := by rw [show t - s = (t - c) + (c - s) by ring]
          _ ≤ |t - c| + |c - s| := abs_add_le _ _
      linarith [h2, ht, hcs]
    show Ac (ψ (γ t)) = 0
    rw [hψ0 t h1, map_zero]
  -- the blend window
  obtain ⟨ρb, hρb, -, hblend⟩ :=
    exists_transverse_blend_loc (n := n) hn hγ hg hΨsm hGsm hδ (by linarith) hΨ0 hG0win
      hGder.symm hcT
  -- the transition width and the step function
  set ηb : ℝ := min (min ρb δ) (ρ / 4) / 8 with hηbdef
  have hηbpos : 0 < ηb := by
    rw [hηbdef]
    exact div_pos (lt_min (lt_min hρb hδ) (by linarith)) (by norm_num)
  have hηbρb : ηb < ρb := by
    rw [hηbdef]
    have h1 : min (min ρb δ) (ρ / 4) ≤ ρb := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hηbδ : ηb ≤ δ := by
    rw [hηbdef]
    have h1 : min (min ρb δ) (ρ / 4) ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hηbρ : ηb ≤ ρ / 4 := by
    rw [hηbdef]
    have h1 : min (min ρb δ) (ρ / 4) ≤ ρ / 4 := min_le_right _ _
    linarith
  obtain ⟨χ, hχsm, hχ01, hχ1, hχ0⟩ := exists_smoothStep c ηb hηbpos
  -- the new right end and the new vanishing window
  have hcc' : c ≤ min (s + ρ / 2) b := le_min (by linarith [hcs']) hc.2
  have hc'b : min (s + ρ / 2) b ≤ b := min_le_right _ _
  have hc'A : A < min (s + ρ / 2) b := lt_of_lt_of_le hcAB.1 hcc'
  have hc'B : min (s + ρ / 2) b < B := lt_of_le_of_lt hc'b hbB
  set δ' : ℝ := min (min δ (ρ / 2)) (min ((min (s + ρ / 2) b - A) / 2)
      ((B - min (s + ρ / 2) b) / 2)) / 2 with hδ'def
  have hkey1 : min (min δ (ρ / 2)) (min ((min (s + ρ / 2) b - A) / 2)
      ((B - min (s + ρ / 2) b) / 2)) ≤ δ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hkey2 : min (min δ (ρ / 2)) (min ((min (s + ρ / 2) b - A) / 2)
      ((B - min (s + ρ / 2) b) / 2)) ≤ ρ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hkey3 : min (min δ (ρ / 2)) (min ((min (s + ρ / 2) b - A) / 2)
      ((B - min (s + ρ / 2) b) / 2)) ≤ (min (s + ρ / 2) b - A) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hkey4 : min (min δ (ρ / 2)) (min ((min (s + ρ / 2) b - A) / 2)
      ((B - min (s + ρ / 2) b) / 2)) ≤ (B - min (s + ρ / 2) b) / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ'pos : 0 < δ' := by
    rw [hδ'def]
    exact half_pos (lt_min (lt_min hδ (by linarith)) (lt_min (by linarith) (by linarith)))
  have hδ'δ : δ' ≤ δ := by rw [hδ'def]; linarith
  have hδ'ρ : δ' ≤ ρ / 4 := by rw [hδ'def]; linarith
  have hδ'A : δ' ≤ (min (s + ρ / 2) b - A) / 2 := by rw [hδ'def]; linarith
  have hδ'B : δ' ≤ (B - min (s + ρ / 2) b) / 2 := by rw [hδ'def]; linarith
  -- the fresh piece is transverse and vanishing on the relevant window
  have hts : ∀ t : ℝ, t ∈ Set.Icc c (min (s + ρ / 2) b) → |t - s| < ρ := by
    intro t ht
    rw [abs_lt]
    constructor
    · linarith [ht.1, hcs'']
    · have h3 : min (s + ρ / 2) b - s ≤ ρ / 2 := by
        have h4 := min_le_left (s + ρ / 2) b
        linarith
      linarith [ht.2, h3]
  have hwin : ∀ t : ℝ, |t - min (s + ρ / 2) b| < δ' → |t - s| < ρ := by
    intro t ht
    have h1 : |t - min (s + ρ / 2) b| < ρ / 4 := lt_of_lt_of_le ht hδ'ρ
    have h2 : |t - s| ≤ |t - min (s + ρ / 2) b| + |min (s + ρ / 2) b - s| := by
      calc |t - s| = |(t - min (s + ρ / 2) b) + (min (s + ρ / 2) b - s)| := by
            rw [show t - s = (t - min (s + ρ / 2) b) + (min (s + ρ / 2) b - s) by ring]
        _ ≤ |t - min (s + ρ / 2) b| + |min (s + ρ / 2) b - s| := abs_add_le _ _
    have h3 : |min (s + ρ / 2) b - s| ≤ ρ / 2 := by
      rw [abs_le]
      constructor
      · have h4 := min_le_left (s + ρ / 2) b
        linarith [hcs'']
      · have h4 := min_le_left (s + ρ / 2) b
        linarith
    linarith [h2, h1, h3]
  refine ⟨fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • Ac (ψ x), δ', hδ'pos, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => χ (g x)) :=
      (contMDiff_iff_contDiff.mpr hχsm).comp hg
    have h2 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => 1 - χ (g x)) :=
      contMDiff_const.sub h1
    exact (h1.smul hΨsm).add (h2.smul hGsm)
  · -- the vanishing window at the new right end
    intro t ht
    have htAB : t ∈ Set.Ioo A B := by
      rw [Set.mem_Ioo]
      exact ⟨by have h1 := (abs_lt.mp ht).1; linarith [h1, hδ'A],
             by have h1 := (abs_lt.mp ht).2; linarith [h1, hδ'B]⟩
    have hgt : g (γ t) = t := hgwin t ⟨le_of_lt htAB.1, le_of_lt htAB.2⟩
    have hts' : |t - s| < ρ := hwin t ht
    have hkey : |t - c| < δ ∨ c + ηb ≤ t := by
      rcases le_or_gt t c with h | h
      · left
        rw [abs_of_nonpos (by linarith)]
        have h1 := (abs_lt.mp ht).1
        linarith
      · by_cases h2 : t < c + ηb
        · left
          rw [abs_of_nonneg (by linarith)]
          linarith
        · right
          push_neg at h2
          exact h2
    change χ (g (γ t)) • Ψ (γ t) + (1 - χ (g (γ t))) • Ac (ψ (γ t)) = 0
    rcases hkey with hkey | hkey
    · simp [hΨ0 t hkey, hψ0 t hts']
    · have hchi : χ (g (γ t)) = 0 := by rw [hgt]; exact hχ0 t hkey
      simp [hchi, hψ0 t hts']
  · -- vanishing on `[a, min (s + ρ/2) b]`
    intro t ht
    have hgt : g (γ t) = t :=
      hgwin t ⟨by linarith [ht.1, hAa], by linarith [ht.2, hc'b, hbB]⟩
    change χ (g (γ t)) • Ψ (γ t) + (1 - χ (g (γ t))) • Ac (ψ (γ t)) = 0
    rcases le_or_gt t c with htc | htc
    · rcases le_or_gt t (c - ηb) with h1 | h1
      · have hchi : χ (g (γ t)) = 1 := by rw [hgt]; exact hχ1 t h1
        simp [hchi, hΨ0ab t ⟨ht.1, htc⟩]
      · have hts' : |t - s| < ρ := by
          have h2 : |t - s| ≤ |t - c| + |c - s| := by
            calc |t - s| = |(t - c) + (c - s)| := by
                  rw [show t - s = (t - c) + (c - s) by ring]
              _ ≤ |t - c| + |c - s| := abs_add_le _ _
          have h3 : |t - c| < ηb := by
            rw [abs_of_nonpos (by linarith)]
            linarith
          have h4 : |t - s| < ηb + |c - s| := by linarith [h2, h3]
          linarith [h4, hcs, hηbρ]
        simp [hΨ0ab t ⟨ht.1, htc⟩, hψ0 t hts']
    · rcases le_or_gt (c + ηb) t with h1 | h1
      · have hchi : χ (g (γ t)) = 0 := by rw [hgt]; exact hχ0 t h1
        have hts' : |t - s| < ρ := hts t ⟨le_of_lt htc, ht.2⟩
        simp [hchi, hψ0 t hts']
      · have h3 : |t - c| < δ := by
          rw [abs_of_nonneg (by linarith)]
          linarith [h1, hηbδ]
        have hts' : |t - s| < ρ := hts t ⟨le_of_lt htc, ht.2⟩
        simp [hΨ0 t h3, hψ0 t hts']
  · -- transversality on `[a, min (s + ρ/2) b]`
    intro t ht
    have hgt : g (γ t) = t :=
      hgwin t ⟨by linarith [ht.1, hAa], by linarith [ht.2, hc'b, hbB]⟩
    rcases lt_or_ge t (c - ηb) with h1 | h1
    · -- left of the window: the blend agrees with `Ψ`
      have htc : t ∈ Set.Icc a c := ⟨ht.1, by linarith⟩
      have heq : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • Ac (ψ x)) =ᶠ[𝓝 (γ t)] Ψ := by
        have hop : {x : M | g x < c - ηb} ∈ 𝓝 (γ t) :=
          hg.continuous.continuousAt.preimage_mem_nhds (by rw [hgt]; exact isOpen_Iio.mem_nhds h1)
        filter_upwards [hop] with x hx
        rw [hχ1 (g x) (le_of_lt hx)]
        simp
      exact (transverse_congr heq).mpr (hΨT t htc)
    · rcases lt_or_ge (c + ηb) t with h2 | h2
      · -- right of the window: the blend agrees with `Ac ∘ ψ`
        have heq : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • Ac (ψ x)) =ᶠ[𝓝 (γ t)]
            (fun x : M => Ac (ψ x)) := by
          have hop : {x : M | c + ηb < g x} ∈ 𝓝 (γ t) :=
            hg.continuous.continuousAt.preimage_mem_nhds (by rw [hgt]; exact isOpen_Ioi.mem_nhds h2)
          filter_upwards [hop] with x hx
          rw [hχ0 (g x) (le_of_lt hx)]
          simp
        exact (transverse_congr heq).mpr (hGtrans t (hψT t (hts t ⟨by linarith, ht.2⟩)))
      · -- inside the window: the blend lemma
        exact hblend χ hχsm hχ01 t (by rw [abs_lt]; constructor <;> linarith)

/-! ## The greedy chain of right ends -/

theorem exists_piece_on_chain_loc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {A B a b : ℝ} (hAa : A < a) (hab : a ≤ b) (hbB : b < B)
    (hgwin : ∀ t ∈ Set.Icc A B, g (γ t) = t)
    {F : Finset ℝ} {rr : ℝ → ℝ} {psi : ℝ → M → EuclideanSpace ℝ (Fin (n - 1))}
    (hpieces : ∀ u ∈ F, ContMDiff (MC n) (MC (n - 1)) smoothOrder (psi u) ∧ 0 < rr u ∧
      ∀ s : ℝ, |s - u| < rr u → psi u (γ s) = 0 ∧ Transverse γ g (psi u) s)
    (hcover : Set.Icc a b ⊆ ⋃ u ∈ F, Set.Ioo (u - rr u / 2) (u + rr u / 2)) (k : ℕ) :
    ∃ (Ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (δ : ℝ),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ ∧ 0 < δ ∧
      (∀ t : ℝ, |t - (rightEnds hcover hab k).val| < δ → Ψ (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (rightEnds hcover hab k).val, Ψ (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (rightEnds hcover hab k).val, Transverse γ g Ψ t) := by
  classical
  let State : ℕ → Prop := fun k => ∃ (Ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (δ : ℝ),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ ∧ 0 < δ ∧
      (∀ t : ℝ, |t - (rightEnds hcover hab k).val| < δ → Ψ (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (rightEnds hcover hab k).val, Ψ (γ t) = 0) ∧
      (∀ t ∈ Set.Icc a (rightEnds hcover hab k).val, Transverse γ g Ψ t)
  have hbase : State 0 := by
    obtain ⟨hpsm, hρ, hpT⟩ := hpieces _ (chainIdx_mem hcover hab 0)
    refine ⟨psi (chainIdx hcover hab 0), rr (chainIdx hcover hab 0) / 2, hpsm,
      half_pos hρ, ?_, ?_, ?_⟩
    · intro t ht
      have hspec := chainIdx_spec hcover hab 0
      rw [Set.mem_Ioo] at hspec
      have h0 : (rightEnds hcover hab 0).val = a := rightEnds_zero hcover hab
      rw [h0] at ht
      exact (hpT t (by rw [abs_lt] at ht ⊢; constructor <;> linarith [hspec.1, hspec.2])).1
    · intro t ht
      have h0 : (rightEnds hcover hab 0).val = a := rightEnds_zero hcover hab
      rw [h0] at ht
      have hta : t = a := le_antisymm ht.2 ht.1
      have hspec := chainIdx_spec hcover hab 0
      rw [Set.mem_Ioo] at hspec
      have hlt : |t - chainIdx hcover hab 0| < rr (chainIdx hcover hab 0) := by
        rw [abs_lt]
        constructor <;> linarith [hspec.1, hspec.2, hta]
      exact (hpT t hlt).1
    · intro t ht
      have h0 : (rightEnds hcover hab 0).val = a := rightEnds_zero hcover hab
      rw [h0] at ht
      have hta : t = a := le_antisymm ht.2 ht.1
      have hspec := chainIdx_spec hcover hab 0
      rw [Set.mem_Ioo] at hspec
      have hlt : |t - chainIdx hcover hab 0| < rr (chainIdx hcover hab 0) := by
        rw [abs_lt]
        constructor <;> linarith [hspec.1, hspec.2, hta]
      exact (hpT t hlt).2
  have hstep : ∀ k, State k → State (k + 1) := by
    intro k ih
    obtain ⟨Ψ, δ, hΨsm, hδ, hΨ0, hΨ0ab, hΨT⟩ := ih
    by_cases hkb : (rightEnds hcover hab k).val = b
    · refine ⟨Ψ, δ, hΨsm, hδ, ?_, ?_, ?_⟩
      · rw [rightEnds_succ, if_pos hkb]
        rw [hkb] at hΨ0
        exact hΨ0
      · rw [rightEnds_succ, if_pos hkb]
        rw [hkb] at hΨ0ab
        exact hΨ0ab
      · rw [rightEnds_succ, if_pos hkb]
        rw [hkb] at hΨT
        exact hΨT
    · obtain ⟨hpsm, hρ, hpT⟩ := hpieces _ (chainIdx_mem hcover hab k)
      have hc : (rightEnds hcover hab k).val ∈ Set.Icc a b := (rightEnds hcover hab k).property
      have hmid : |(rightEnds hcover hab k).val - chainIdx hcover hab k|
          < rr (chainIdx hcover hab k) / 2 := by
        have hspec := chainIdx_spec hcover hab k
        rw [Set.mem_Ioo] at hspec
        rw [abs_lt]
        constructor <;> linarith [hspec.1, hspec.2]
      obtain ⟨Ψ', δ', hδ'pos, hΨ'sm, hΨ'0, hΨ'0ab, hΨ'T⟩ :=
        extension_step_loc (n := n) hn hγ hg hAa hab hbB hgwin hc hΨsm hδ hΨ0 hΨ0ab hΨT
          hpsm hρ (fun s hs => (hpT s hs).1) (fun s hs => (hpT s hs).2) hmid
      refine ⟨Ψ', δ', hΨ'sm, hδ'pos, ?_, ?_, ?_⟩
      · rw [rightEnds_succ, if_neg hkb]
        exact hΨ'0
      · rw [rightEnds_succ, if_neg hkb]
        exact hΨ'0ab
      · rw [rightEnds_succ, if_neg hkb]
        exact hΨ'T
  show State k
  exact Nat.rec (motive := State) hbase hstep k

/-! ## The transverse coordinate on the arc -/

set_option maxHeartbeats 2000000 in
/-- **A transverse coordinate along a compact arc.**  If `g : M → ℝ` satisfies `g (γ t) = t` on an
interval `[a, b]` containing `[A, B]` (with `a < A < c ≤ d < B < b`), then there is a smooth
`P : M → ℝ^{n-1}` vanishing on `γ '' [c, d]` whose derivative together with `dg` is injective there.

This is the local form of `Work.Noncompact.CompressionTube.collar_transverse_coordinate`: no
properness, no global injectivity of `γ`, no second countability of `M`, and no global vanishing of
`g ∘ γ − id`. -/
theorem arc_transverse_local {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {a b A B c d : ℝ} (haA : a < A) (hAc : A < c) (hcd : c ≤ d) (hdB : d < B) (hBb : B < b)
    (hcore : ∀ t ∈ Set.Icc a b, g (γ t) = t) :
    ∃ P : M → EuclideanSpace ℝ (Fin (n - 1)), ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
      (∀ t ∈ Set.Icc c d, P (γ t) = 0) ∧ (∀ t ∈ Set.Icc c d, Transverse γ g P t) := by
  classical
  -- at every parameter of the compact interval there is a piece with a transversality radius
  have hkey : ∀ s : Set.Icc c d, ∃ (ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (ρ : ℝ),
      0 < ρ ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧
      ∀ u : ℝ, |u - s.1| < ρ → ψ (γ u) = 0 ∧ Transverse γ g ψ u := by
    intro s
    have hgloc : (fun u : ℝ => g (γ u)) =ᶠ[𝓝 s.1] id := by
      have hpos : 0 < min (s.1 - A) (B - s.1) / 2 :=
        half_pos (lt_min (by linarith [s.2.1, hAc]) (by linarith [s.2.2, hdB]))
      refine Filter.mem_of_superset (Metric.ball_mem_nhds s.1 hpos) fun u hu => ?_
      rw [Metric.mem_ball, Real.dist_eq] at hu
      have h1 := (abs_lt.mp hu).1
      have h2 := (abs_lt.mp hu).2
      exact hcore u ⟨by linarith [h1, min_le_left (s.1 - A) (B - s.1), hAc, haA],
        by linarith [h2, min_le_right (s.1 - A) (B - s.1), hdB, hBb]⟩
    obtain ⟨δ₁, ψ, hδ₁, hψsm, hψ0, hψT⟩ := exists_local_transverse_piece_loc hn hγ hg hgloc
    obtain ⟨ρ₁, hρ₁, hρT⟩ := exists_transverse_open_loc hn hγ hg hψsm hψT
    exact ⟨ψ, min δ₁ ρ₁, lt_min hδ₁ hρ₁, hψsm, fun u hu =>
      ⟨hψ0 u (lt_of_lt_of_le hu (min_le_left _ _)),
       hρT u (lt_of_lt_of_le hu (min_le_right _ _))⟩⟩
  let psi : Set.Icc c d → M → EuclideanSpace ℝ (Fin (n - 1)) := fun s => Classical.choose (hkey s)
  let rr : Set.Icc c d → ℝ := fun s => Classical.choose (Classical.choose_spec (hkey s))
  have hspec : ∀ s : Set.Icc c d, 0 < rr s ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder (psi s) ∧
      ∀ u : ℝ, |u - s.1| < rr s → psi s (γ u) = 0 ∧ Transverse γ g (psi s) u :=
    fun s => Classical.choose_spec (Classical.choose_spec (hkey s))
  -- the half-radius intervals cover the compact interval
  have hcov : Set.Icc c d ⊆ ⋃ s : Set.Icc c d, Set.Ioo (s.1 - rr s / 2) (s.1 + rr s / 2) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [Set.mem_Ioo]
    have h := (hspec ⟨x, hx⟩).1
    constructor <;> linarith
  obtain ⟨T, hT⟩ := IsCompact.elim_finite_subcover isCompact_Icc
    (fun s : Set.Icc c d => Set.Ioo (s.1 - rr s / 2) (s.1 + rr s / 2))
    (fun _ => isOpen_Ioo) hcov
  -- transport the finite family to a finset of reals
  set F : Finset ℝ := T.image Subtype.val with hFdef
  set psiR : ℝ → M → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun t => dite (t ∈ Set.Icc c d) (fun h => psi ⟨t, h⟩) (fun _ => fun _ => 0) with hpsiRdef
  set rrR : ℝ → ℝ :=
    fun t => dite (t ∈ Set.Icc c d) (fun h => rr ⟨t, h⟩) (fun _ => 1) with hrrRdef
  have hpieces : ∀ t ∈ F, ContMDiff (MC n) (MC (n - 1)) smoothOrder (psiR t) ∧ 0 < rrR t ∧
      ∀ s : ℝ, |s - t| < rrR t → psiR t (γ s) = 0 ∧ Transverse γ g (psiR t) s := by
    intro t ht
    obtain ⟨s, -, hst⟩ := Finset.mem_image.mp ht
    subst hst
    have hmem : s.1 ∈ Set.Icc c d := s.2
    have hsub : (⟨s.1, hmem⟩ : Set.Icc c d) = s := Subtype.ext rfl
    have h1 : psiR s.1 = psi s := by
      rw [hpsiRdef]
      simp only [dif_pos hmem, hsub]
    have h2 : rrR s.1 = rr s := by
      rw [hrrRdef]
      simp only [dif_pos hmem, hsub]
    rw [h1, h2]
    exact ⟨(hspec s).2.1, (hspec s).1, fun u hu => (hspec s).2.2 u hu⟩
  have hcover : Set.Icc c d ⊆ ⋃ t ∈ F, Set.Ioo (t - rrR t / 2) (t + rrR t / 2) := by
    intro x hx
    obtain ⟨s, hsT, hxs⟩ := Set.mem_iUnion₂.mp (hT hx)
    refine Set.mem_iUnion₂.mpr ⟨s.1, Finset.mem_image.mpr ⟨s, hsT, rfl⟩, ?_⟩
    have hmem : s.1 ∈ Set.Icc c d := s.2
    have hsub : (⟨s.1, hmem⟩ : Set.Icc c d) = s := Subtype.ext rfl
    have h2 : rrR s.1 = rr s := by
      rw [hrrRdef]
      simp only [dif_pos hmem, hsub]
    rw [h2]
    exact hxs
  -- run the chain
  obtain ⟨P, δ, hPsm, hδ, hP0, hP0ab, hPT⟩ :=
    exists_piece_on_chain_loc (n := n) hn hγ hg hAc hcd hdB
      (fun t ht => hcore t ⟨by linarith [ht.1, haA, hAc], by linarith [ht.2, hdB, hBb]⟩)
      hpieces hcover F.card
  refine ⟨P, hPsm, ?_, ?_⟩
  · intro t ht
    rw [rightEnds_card_eq_b hcover hcd] at hP0ab
    exact hP0ab t ht
  · intro t ht
    rw [rightEnds_card_eq_b hcover hcd] at hPT
    exact hPT t ht

end

end Work.Noncompact.Routing
