import Mathlib
import Submission.Work.Diff.ODE.Basic
import Submission.Work.Diff.ODE.ChartField
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz_of_mem_Ioo

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniqueness of the solutions of a time-dependent ODE on a manifold

A jointly smooth time-dependent vector field `X` on a boundaryless manifold `M` has, for a given
initial point, at most one solution of `γ' τ = X (a + τ) (γ τ)` through it.  The proof is the
standard one: in the chart at the initial point the equation becomes an ODE on `ℝ × E`
(an autonomous ODE for the curve `τ ↦ (τ, chart (γ τ))`), and uniqueness of solutions of an ODE
with a locally Lipschitz right-hand side (`Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz`)
applied on a small interval containing the initial time gives γ =ᶠ γ'.  A connectedness argument on
`Ioo (-T) T` then spreads this to the whole interval.
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Set Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **The chart equation of a curve following a time-dependent field.**  If `γ` has velocity
`X (a + t) (γ t)` at time `t` and `γ t` lies in the source of the chart at `x₀`, then in that chart
`γ` is differentiable with derivative the chart expression of `X (a + t) (γ t)`.  (Local version of
the statement proved in `Submission/Work/Diff/ODE/hasDerivAt_extChartAt_comp.lean`.) -/
private theorem hasDerivAt_extChartAt_comp_aux
    {X : ℝ → Π x : M, TangentSpace I x} {a t : ℝ} {x₀ : M} {γ : ℝ → M}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + t) (γ t))))
    (hsrc : γ t ∈ (extChartAt I x₀).source) :
    HasDerivAt ((extChartAt I x₀) ∘ γ)
      (chartField X x₀ (a + t, ((extChartAt I x₀) ∘ γ) t)) t := by
  have hx : γ t ∈ (chartAt H x₀).source := by rwa [← extChartAt_source (I := I) x₀]
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := hγ.mdifferentiableAt
  have hmdφ : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) hx
  have hmd' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I x₀) ∘ γ) t :=
    MDifferentiableAt.comp (hg := hmdφ) (hf := hmd)
  -- the velocity in the chart
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) = X (a + t) (γ t) := by
    rw [hγ.mfderiv, ContinuousLinearMap.smulRight_apply]
    change (1 : ℝ) • X (a + t) (γ t) = X (a + t) (γ t)
    rw [one_smul]
  have hkey : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I x₀) ∘ γ) t (1 : ℝ)
      = chartField X x₀ (a + t, ((extChartAt I x₀) ∘ γ) t) := by
    rw [mfderiv_comp_apply (x := t) hmdφ hmd (1 : ℝ), hvel]
    rw [chartField]
    simp only [Function.comp_apply]
    rw [PartialEquiv.left_inv (extChartAt I x₀) hsrc]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx]
    rfl
  have hD : HasDerivAt ((extChartAt I x₀) ∘ γ)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I x₀) ∘ γ) t (1 : ℝ)) t :=
    hmd'.hasMFDerivAt.hasFDerivAt.hasDerivAt
  rwa [hkey] at hD

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **The chart field is differentiable.**  The coordinate expression `chartField X x₀` of a
jointly smooth time-dependent field is differentiable at every point whose second coordinate lies
in the target of the chart at `x₀`.  (Local version of the statement proved in
`Submission/Work/Diff/ODE/chartField_contDiffAt.lean`.) -/
private theorem chartField_contDiffAt_aux [I.Boundaryless]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (x₀ : M) {t : ℝ} {u : E} (hu : u ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ 1 (chartField X x₀) (t, u) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  set y₀ : M := (extChartAt I x₀).symm u with hy₀
  have hy₀src : y₀ ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hu
  have hy₀base : y₀ ∈ e.baseSet := by
    rw [he, TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hy₀src
  have he_mem : (⟨y₀, X t y₀⟩ : TangentBundle I M) ∈ e.source := by
    rw [Trivialization.mem_source]
    exact hy₀base
  -- the section is smooth, hence its component in the trivialisation at `x₀` is smooth
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) (t, y₀) := hX (t, y₀)
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M ↦ (e (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)).2) (t, y₀) :=
    ((Bundle.Trivialization.contMDiffAt_iff (IB := I) (IM := 𝓘(ℝ, ℝ).prod I) (F := E)
      (E := TangentSpace I)
      (f := fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) (x₀ := (t, y₀))
      he_mem).mp hf).2
  -- on the base set the trivialisation is the coordinate change
  have h2' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M ↦ e.continuousLinearMapAt ℝ p.2 (X p.1 p.2)) (t, y₀) := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_baseSet.mem_nhds hy₀base)]
      with p hp
    change p.2 ∈ e.baseSet at hp
    simp only [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hp]
  -- transport along the chart inverse `(t,u) ↦ (t, (extChartAt I x₀).symm u)`
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm u :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds hu)
  have hχ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × E ↦ (q.1, (extChartAt I x₀).symm q.2)) (t, u) :=
    contMDiffAt_fst.prodMk (hsymm.comp (t, u) contMDiffAt_snd)
  have h3 := h2'.comp (t, u) hχ
  have h4 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (chartField X x₀) (t, u) := h3
  have h5 : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ, E) ∞ (chartField X x₀) (t, u) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h4
  exact (contMDiffAt_iff_contDiffAt.mp h5).of_le (mod_cast le_top)

/-- If `f` is continuous at `x` and `x` is in the closure of `s`, then `f x` lies in the closure of
`f '' s`. -/
private theorem mem_closure_image_of_continuousAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {s : Set X} {x : X} (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) := by
  rw [mem_closure_iff] at hx ⊢
  intro U hU hxU
  obtain ⟨V, hV, hVopen, hxV⟩ :=
    mem_nhds_iff.mp (hf.preimage_mem_nhds (hU.mem_nhds hxU))
  obtain ⟨y, hyV, hyS⟩ := hx V hVopen hxV
  exact ⟨f y, hV hyV, y, hyS, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **Local uniqueness** for the time-dependent ODE `γ' = X (a + ·) γ`: two solutions through the
same point at time `τ₀` agree on a neighbourhood of `τ₀`. -/
private theorem eventuallyEq_of_hasMFDerivAt_timeDep [I.Boundaryless]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {a τ₀ : ℝ} {γ γ' : ℝ → M} (h : γ τ₀ = γ' τ₀)
    (hγ : ∀ᶠ t in 𝓝 τ₀,
      HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + t) (γ t))))
    (hγ' : ∀ᶠ t in 𝓝 τ₀,
      HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + t) (γ' t)))) :
    γ =ᶠ[𝓝 τ₀] γ' := by
  -- both curves solve the equation at `τ₀`, hence are continuous there
  obtain ⟨s, hs, hs'⟩ := Filter.eventually_iff_exists_mem.mp hγ
  obtain ⟨s', hs'', hs'''⟩ := Filter.eventually_iff_exists_mem.mp hγ'
  have hγτ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ τ₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + τ₀) (γ τ₀))) :=
    hs' τ₀ (mem_of_mem_nhds hs)
  have hγ'τ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ' τ₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + τ₀) (γ' τ₀))) :=
    hs''' τ₀ (mem_of_mem_nhds hs'')
  have hcontγ : ContinuousAt γ τ₀ := hγτ.continuousAt
  have hcontγ' : ContinuousAt γ' τ₀ := hγ'τ.continuousAt
  -- the chart at the common initial point `x₀`
  set x₀ : M := γ τ₀ with hx₀
  have hsrc_nhds : γ ⁻¹' (extChartAt I x₀).source ∈ 𝓝 τ₀ :=
    hcontγ.preimage_mem_nhds (extChartAt_source_mem_nhds x₀)
  have hx₀' : γ' τ₀ = x₀ := by rw [hx₀]; exact h.symm
  have hsrc'_nhds : γ' ⁻¹' (extChartAt I x₀).source ∈ 𝓝 τ₀ := by
    have h1 : (extChartAt I x₀).source ∈ 𝓝 (γ' τ₀) := by
      rw [hx₀']; exact extChartAt_source_mem_nhds x₀
    exact hcontγ'.preimage_mem_nhds h1
  -- combine everything into a single eventual statement
  have hev : ∀ᶠ t in 𝓝 τ₀,
      ((HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + t) (γ t))) ∧
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + t) (γ' t)))) ∧
        t ∈ γ ⁻¹' (extChartAt I x₀).source) ∧ t ∈ γ' ⁻¹' (extChartAt I x₀).source :=
    ((hγ.and hγ').and hsrc_nhds).and hsrc'_nhds
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hev
  set δ : ℝ := ε / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hIcc : Icc (τ₀ - δ) (τ₀ + δ) ⊆ Metric.ball τ₀ ε := by
    intro σ hσ
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : |σ - τ₀| ≤ δ := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    rw [hδdef] at h1
    linarith
  -- the coordinate curves
  have hx₀'' : γ τ₀ = γ' τ₀ := hx₀.symm.trans h
  have h0 : (fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ ρ))) τ₀
      = (fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ' ρ))) τ₀ := by
    simp only [hx₀'']
  have hu : ∀ σ ∈ Icc (τ₀ - δ) (τ₀ + δ),
      HasDerivAt (fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ ρ)))
        ((1 : ℝ), chartField X x₀ (a + σ, (extChartAt I x₀) (γ σ))) σ := by
    intro σ hσ
    have hσ' := hε' (hIcc hσ)
    exact (hasDerivAt_id σ).prodMk
      (hasDerivAt_extChartAt_comp_aux (x₀ := x₀) hσ'.1.1.1 hσ'.1.2)
  have hv : ∀ σ ∈ Icc (τ₀ - δ) (τ₀ + δ),
      HasDerivAt (fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ' ρ)))
        ((1 : ℝ), chartField X x₀ (a + σ, (extChartAt I x₀) (γ' σ))) σ := by
    intro σ hσ
    have hσ' := hε' (hIcc hσ)
    exact (hasDerivAt_id σ).prodMk
      (hasDerivAt_extChartAt_comp_aux (x₀ := x₀) hσ'.1.1.2 hσ'.2)
  have hlip : ∀ σ ∈ Icc (τ₀ - δ) (τ₀ + δ),
      ∃ K : NNReal, ∃ U ∈ 𝓝 ((σ, (extChartAt I x₀) (γ σ)) : ℝ × E),
        LipschitzOnWith K (fun q : ℝ × E => ((1 : ℝ), chartField X x₀ (a + q.1, q.2))) U := by
    intro σ hσ
    have hσ' := hε' (hIcc hσ)
    have htgt : (extChartAt I x₀) (γ σ) ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hσ'.1.2
    have htrans : ContDiffAt ℝ 1 (fun q : ℝ × E => (a + q.1, q.2))
        (σ, (extChartAt I x₀) (γ σ)) := by fun_prop
    have hcomp : ContDiffAt ℝ 1
        ((chartField X x₀) ∘ (fun q : ℝ × E => (a + q.1, q.2)))
        (σ, (extChartAt I x₀) (γ σ)) :=
      (chartField_contDiffAt_aux hX x₀ htgt).comp (σ, (extChartAt I x₀) (γ σ)) htrans
    have hcd : ContDiffAt ℝ 1 (fun q : ℝ × E => chartField X x₀ (a + q.1, q.2))
        (σ, (extChartAt I x₀) (γ σ)) := by
      simpa only [Function.comp_def] using hcomp
    obtain ⟨K, W, hW, hlipW⟩ := hcd.exists_lipschitzOnWith
    exact ⟨K, W, hW, LipschitzOnWith.of_dist_le_mul fun q hq q' hq' => by
      have hle : dist ((fun q : ℝ × E => chartField X x₀ (a + q.1, q.2)) q)
          ((fun q : ℝ × E => chartField X x₀ (a + q.1, q.2)) q') ≤ K * dist q q' :=
        hlipW.dist_le_mul q hq q' hq'
      simpa [Prod.dist_eq] using hle⟩
  have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz_of_mem_Ioo
    (f := fun q : ℝ × E => ((1 : ℝ), chartField X x₀ (a + q.1, q.2)))
    (u := fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ ρ)))
    (v := fun ρ : ℝ => (ρ, (extChartAt I x₀) (γ' ρ)))
    (a := τ₀ - δ) (b := τ₀ + δ) (t₀ := τ₀)
    (by linarith) ⟨by linarith, by linarith⟩ hu hv hlip h0
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Icc (τ₀ - δ) (τ₀ + δ), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  intro t ht
  have h2 := hEq ht
  have h3 : (extChartAt I x₀) (γ t) = (extChartAt I x₀) (γ' t) := congrArg Prod.snd h2
  have hs1 : γ t ∈ (extChartAt I x₀).source := (hε' (hIcc ht)).1.2
  have hs2 : γ' t ∈ (extChartAt I x₀).source := (hε' (hIcc ht)).2
  calc γ t = (extChartAt I x₀).symm ((extChartAt I x₀) (γ t)) := (PartialEquiv.left_inv _ hs1).symm
    _ = (extChartAt I x₀).symm ((extChartAt I x₀) (γ' t)) := by rw [h3]
    _ = γ' t := PartialEquiv.left_inv _ hs2

/-- Two solutions of the time-dependent ODE `γ' = X (a + ·) γ` started at the same point at time
`0` agree on the whole open interval `Ioo (-T) T` on which they are required to solve the
equation. -/
theorem eqOn_Ioo_of_isXCurveOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {a : ℝ} {y : M} {T : ℝ} (hT : 0 < T) {γ γ' : ℝ → M}
    (hγ : Work.Diff.ODE.IsXCurveOn X a y T γ) (hγ' : Work.Diff.ODE.IsXCurveOn X a y T γ') :
    EqOn γ γ' (Ioo (-T) T) := by
  set S : Set ℝ := {t | γ t = γ' t} ∩ Ioo (-T) T with hS
  have hne : (Ioo (-T) T ∩ S).Nonempty := by
    refine ⟨0, mem_Ioo.mpr ⟨by linarith, by linarith⟩, ?_⟩
    rw [hS]
    exact ⟨hγ.1.trans hγ'.1.symm, mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rw [hS] at ht
    have hmem : Ioo (-T) T ∈ 𝓝 t := Ioo_mem_nhds ht.2.1 ht.2.2
    have heq := eventuallyEq_of_hasMFDerivAt_timeDep hX ht.1
      (Filter.eventually_of_mem hmem fun σ hσ => hγ.2 σ (abs_lt.mpr hσ))
      (Filter.eventually_of_mem hmem fun σ hσ => hγ'.2 σ (abs_lt.mpr hσ))
    rw [hS]
    exact Filter.inter_mem heq hmem
  have hcl : closure S ∩ Ioo (-T) T ⊆ S := by
    intro t ht
    rw [hS] at ht ⊢
    refine ⟨?_, ht.2⟩
    have hcontγ : ContinuousAt γ t := (hγ.2 t (abs_lt.mpr ht.2)).continuousAt
    have hcontγ' : ContinuousAt γ' t := (hγ'.2 t (abs_lt.mpr ht.2)).continuousAt
    have hfc : ContinuousAt (fun σ : ℝ => (γ σ, γ' σ)) t := hcontγ.prodMk hcontγ'
    have hcl' : (γ t, γ' t) ∈ closure ((fun σ : ℝ => (γ σ, γ' σ)) '' S) :=
      mem_closure_image_of_continuousAt hfc ht.1
    have hsub : (fun σ : ℝ => (γ σ, γ' σ)) '' S ⊆ {p : M × M | p.1 = p.2} := by
      rintro p ⟨σ, hσ, rfl⟩
      exact hσ.1
    have hclosed : IsClosed {p : M × M | p.1 = p.2} := isClosed_eq continuous_fst continuous_snd
    exact (closure_minimal hsub hclosed hcl' : (γ t, γ' t) ∈ {p : M × M | p.1 = p.2})
  have hsub : Ioo (-T) T ⊆ S :=
    (isPreconnected_Ioo (a := -T) (b := T)).subset_of_closure_inter_subset
      (u := S) hopen hne hcl
  intro t ht
  have h1 := hsub ht
  rw [hS] at h1
  exact h1.1

end Work.Diff.ODE
