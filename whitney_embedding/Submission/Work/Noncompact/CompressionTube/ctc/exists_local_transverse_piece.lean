import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Compat.MFDerivCongrV433

/-!
# A local transverse piece for a properly embedded line

Target: `Work.Noncompact.CompressionTube.exists_local_transverse_piece`.

Given a smooth proper embedding `γ : ℝ → M` of a line into a smooth `n`-manifold `M` (`n ≥ 2`), a
smooth `g : M → ℝ` with `g (γ s) = s`, and a parameter value `s₀`, we produce a *globally smooth*
`ψ : M → ℝ^{n-1}` with `ψ (γ s) = 0` for all `s` and with `(ψ, g)` having injective manifold
derivative at `γ s₀` (i.e. `Transverse γ g ψ s₀`).

The construction is elementary.  Let `c` be the chart at `x₀ := γ s₀` and let
`D := dc (x₀) : T_{x₀}M ≃ ℝⁿ` be its (injective) derivative; let `v := D (γ'(s₀)) ≠ 0` be the chart
velocity.  Choose a projection `H : ℝⁿ → ℝ^{n-1}` with kernel `ℝ v` (linear algebra, below), and put

  `ρ x := H (c x)`,   `ψ₀ x := ρ x - ρ (γ (g x))`,   `ψ := β • ψ₀`

where `β : M → ℝ` is a smooth bump equal to `1` near `x₀` and with `tsupport β` contained in the open
set on which both `x ↦ c x` and `x ↦ c (γ (g x))` are smooth.  Then

* `ψ` is globally smooth (bump times a function smooth on the support of the bump);
* `ψ (γ s) = β (γ s) • (ρ (γ s) - ρ (γ (g (γ s)))) = 0`;
* near `x₀` we have `ψ = ψ₀` (`β ≡ 1`), so `dψ (x₀) = dψ₀ (x₀) = (H ∘ D) - ((H ∘ D) ∘ d(γ ∘ g))`,
  and `d(γ ∘ g) (x₀) = dγ(s₀) ∘ dg(x₀)`; on `ker dg (x₀)` the velocity term drops out, leaving
  `dψ (x₀) v = H (D v)`.  Since `ker H = ℝ v` and `D` is injective, `H (D v) = 0` forces
  `v ∈ ℝ γ'(s₀)`, and then `dg (x₀) v = 0` forces `v = 0` because `dg (x₀) γ'(s₀) = 1`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff RealInnerProductSpace
open Topology Set Function

noncomputable section

/-- **Linear algebra.**  A continuous linear map `ℝⁿ → ℝⁿ⁻¹` whose kernel is exactly the line
spanned by a given nonzero vector `v`; obtained as the quotient projection `ℝⁿ ⧸ ℝ v → ℝⁿ⁻¹`. -/
theorem exists_coord_proj_kernel {n : ℕ} (hn : 1 ≤ n) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ∃ H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)),
      ∀ w : EuclideanSpace ℝ (Fin n), H w = 0 ↔ ∃ a : ℝ, w = a • v := by
  classical
  set M0 : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ {v} with hM0def
  have hspan1 : Module.finrank ℝ M0 = 1 := by
    rw [hM0def, finrank_span_singleton hv]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp [finrank_euclideanSpace]
  have hdimquot : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) ⧸ M0) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) := by
    have h1 := Submodule.finrank_quotient_add_finrank M0
    rw [hspan1, hfin] at h1
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h1 ⊢
    omega
  let e : (EuclideanSpace ℝ (Fin n) ⧸ M0) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin n) ⧸ M0)
      (EuclideanSpace ℝ (Fin (n - 1))) hdimquot
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    e.toLinearMap.comp M0.mkQ
  have hL : ∀ w : EuclideanSpace ℝ (Fin n), (LinearMap.toContinuousLinearMap L) w = L w :=
    fun w => congrArg
      (fun (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1))) => g w)
      (LinearMap.coe_toContinuousLinearMap L)
  refine ⟨LinearMap.toContinuousLinearMap L, fun w => ?_⟩
  rw [hL w]
  show e (M0.mkQ w) = 0 ↔ ∃ a : ℝ, w = a • v
  rw [← map_zero e, e.injective.eq_iff]
  have hker : ∀ x : EuclideanSpace ℝ (Fin n), M0.mkQ x = 0 ↔ x ∈ M0 := by
    intro x
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  rw [hker w]
  exact ⟨fun hx => by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      exact ⟨a, ha.symm⟩,
    fun hx => by
      obtain ⟨a, ha⟩ := hx
      exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩⟩

/-- **Bump times a locally defined function.**  If `W` is open, `β` is globally smooth with
`tsupport β ⊆ W`, and `φ` is smooth on `W`, then `x ↦ β x • φ x` is globally smooth. -/
theorem contMDiff_smul_of_tsupport_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {W : Set M} (hWo : IsOpen W) {β : M → ℝ} (hβ : ContMDiff (MC n) MCreal smoothOrder β)
    (hβW : tsupport β ⊆ W) {φ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hφ : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder φ W) :
    ContMDiff (MC n) (MC (n - 1)) smoothOrder (fun x => β x • φ x) := by
  intro x
  by_cases hx : x ∈ W
  · exact hβ.contMDiffAt.smul (hφ.contMDiffAt (hWo.mem_nhds hx))
  · have hx' : x ∉ tsupport β := fun h => hx (hβW h)
    have hcont : (fun y : M => β y • φ y) =ᶠ[𝓝 x]
        (fun _ => (0 : EuclideanSpace ℝ (Fin (n - 1)))) := by
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx'] with y hy
      have hy0 : β y = 0 := by
        by_contra h
        exact hy (subset_closure (mem_support.mpr h))
      simp [hy0]
    exact contMDiffAt_const.congr_of_eventuallyEq hcont

set_option backward.isDefEq.respectTransparency false in
theorem exists_local_transverse_piece {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s) (s₀ : ℝ) :
    ∃ ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC (n - 1))
        Work.Noncompact.CompressionTube.smoothOrder ψ ∧ (∀ s : ℝ, ψ (γ s) = 0) ∧
      Work.Noncompact.CompressionTube.Transverse γ g ψ s₀ := by
  classical
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
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
      have h2 := mfderiv_g_velocity hgcore hγ hg s₀
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
    rw [hgcore s₀]
    exact hcsrc
  obtain ⟨β, hβsm, _hβ01, hβone, hβsupp⟩ :=
    exists_contMDiff_bump_between (n := n) (K := {γ s₀}) (W := W) isCompact_singleton hWopen
      (by simpa using hWs)
  have hβeq : β =ᶠ[𝓝 (γ s₀)] (fun _ => (1 : ℝ)) := by
    have hS : {x : M | β x = 1} ∈ 𝓝 (γ s₀) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds (hβone (by simp))) interior_subset
    filter_upwards [hS] with x hx
    exact hx
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
  -- `ψ` vanishes on the line
  have hψcore : ∀ t : ℝ, ψ (γ t) = 0 := by
    intro t
    have h0 : ψ₀ (γ t) = 0 := by
      rw [hψ₀def, hhdef]
      simp [hgcore t]
    rw [hψdef]
    simp only []
    rw [h0, smul_zero]
  -- the derivative of `ψ₀` at `γ s₀`
  set dh : TangentSpace (MC n) (γ s₀) →L[ℝ] TangentSpace (MC n) (γ s₀) :=
    (mfderiv MCreal (MC n) γ s₀) ∘L (mfderiv (MC n) MCreal g (γ s₀)) with hdhdef
  have hhmem : hh (γ s₀) ∈ c.source := by
    rw [hhdef]
    show γ (g (γ s₀)) ∈ c.source
    rw [hgcore s₀]
    exact hcsrc
  have hhhderiv : HasMFDerivAt (MC n) (MC n) hh (γ s₀) dh := by
    have hγd : HasMFDerivAt MCreal (MC n) γ (g (γ s₀))
        (mfderiv MCreal (MC n) γ (g (γ s₀))) :=
      (hγ.mdifferentiableAt (x := g (γ s₀)) hn0).hasMFDerivAt
    have hgd : HasMFDerivAt (MC n) MCreal g (γ s₀) (mfderiv (MC n) MCreal g (γ s₀)) :=
      (hg.mdifferentiableAt (x := γ s₀) hn0).hasMFDerivAt
    have h := hγd.comp (γ s₀) hgd
    rw [mfderiv_congr_point (f := γ) (hgcore s₀)] at h
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
      rw [hgcore s₀]
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
    rw [hx, one_smul]
  refine ⟨ψ, hψsm, hψcore, ?_⟩
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
    rw [map_smul, mfderiv_g_velocity hgcore hγ hg s₀, smul_eq_mul, mul_one]
  have ha0 : a = 0 := by
    have h5 := h2
    rw [hv] at h5
    rw [hdg] at h5
    exact h5
  rw [ha0, zero_smul] at hv
  exact hv

end

end Work.Noncompact.CompressionTube
