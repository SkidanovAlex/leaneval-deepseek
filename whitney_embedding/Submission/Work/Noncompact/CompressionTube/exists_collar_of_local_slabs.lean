import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CollarDefs
import Submission.Work.Noncompact.CompressionTube.radial_ball_facts
import Submission.Work.Noncompact.CompressionTube.smooth_minorant
import Submission.Work.Noncompact.CompressionTube.ShrinkDefs
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion

/-!
# Gluing local slab sections into a collar

`exists_collar_of_local_slabs` (lemma **C** of the two-sided collar construction) assembles the
local sections of the map `η = (P, g) : M → ℝ^{n-1} × ℝ` given by the inverse function theorem into
a single smooth collar `Ψ : ℝ^{n-1} × ℝ → M` along the line `γ`.

The mathematical content:

* two local sections of `η` agree on the overlap of their (convex!) slabs: the set where they agree
  is open (at any point where they agree, `η` is locally injective by the inverse function
  principle) and closed, and it contains the axis point `(0, t)`, where both sections equal
  `γ t`;
* hence the sections glue to a single smooth section `Ψ₀` of `η` over the union `U` of the slabs;
* the availability radius `t ↦ sup {r s | |t - s| < ε s} > 0` of `U` is lower semicontinuous, so it
  admits a smooth positive minorant `ρ`; the radial compression `shrinkParam` with `ρ` maps the
  whole parameter space into `U`, and `Ψ := Ψ₀ ∘ shrinkParam` has all the claimed properties:
  its core is `γ`, it is injective on the unit tube (because `η ∘ Ψ = shrinkParam` is injective
  there), it is an immersion there (chain rule, `dη ∘ dΨ₀ = 1`), and it escapes to infinity in the
  `s`-direction because `g (Ψ p) = p.2`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Metric Filter

noncomputable section

/-- The model with corners bridge: `MCprod n` is the self model on `ℝ^{n-1} × ℝ`. -/
theorem prodModel_eq_self (n : ℕ) :
    MCprod n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1))) (F := ℝ)).symm

/-- **Inverse function principle at a point.**  If the manifold derivative of a `C^∞` map
`η : M → ℝ^{n-1} × ℝ` is surjective at a point `x` (source and target have the same dimension `n`),
then `η` is injective on a neighbourhood of `x`. -/
theorem locally_injective_of_surjective_mfderiv {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {η : M → CollarParam n} (hη : ContMDiff (MC n) (MCprod n) smoothOrder η) {x : M}
    (hsurj : Function.Surjective (mfderiv (MC n) (MCprod n) η x)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ Set.InjOn η V := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas x
  have hcx : x ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x
  have hcxs : c x ∈ c.target := c.map_source hcx
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  let Φ : PartialDiffeomorph (MC n) (MC n) M (EuclideanSpace ℝ (Fin n)) smoothOrder :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  have hld : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder (c : M → EuclideanSpace ℝ (Fin n)) x :=
    PartialDiffeomorph.isLocalDiffeomorphAt (MC n) (MC n) smoothOrder Φ hcx
  have hBsurj : Function.Surjective (mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) x) := by
    rw [← hld.mfderivToContinuousLinearEquiv_coe hn0]
    exact (hld.mfderivToContinuousLinearEquiv hn0).surjective
  set etahat : EuclideanSpace ℝ (Fin n) → CollarParam n := fun z => η (c.symm z) with hetahat
  have hcmm : MDifferentiableAt (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) x :=
    (contMDiffAt_of_mem_maximalAtlas hc hcx).mdifferentiableAt hn0
  have hetacm : ContMDiffAt (MC n) (MCprod n) smoothOrder etahat (c x) := by
    have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder c.symm (c x) :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds hcxs)
    exact (hη.contMDiffAt (x := c.symm (c x))).comp (c x) hsymm
  have hetamd : MDifferentiableAt (MC n) (MCprod n) etahat (c x) := hetacm.mdifferentiableAt hn0
  have hetacd : ContDiffAt ℝ smoothOrder etahat (c x) := by
    have h1 := hetacm
    rw [prodModel_eq_self (n := n)] at h1
    exact h1.contDiffAt
  have hchain : mfderiv (MC n) (MCprod n) η x
      = (mfderiv (MC n) (MCprod n) etahat (c x)).comp
        (mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) x) := by
    have hev : (fun y => etahat (c y)) =ᶠ[𝓝 x] η := by
      refine Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hcx) ?_
      intro y hy
      show η (c.symm (c y)) = η y
      rw [c.left_inv hy]
    have hcomp : mfderiv (MC n) (MCprod n) (fun y => etahat (c y)) x
        = (mfderiv (MC n) (MCprod n) etahat (c x)).comp
          (mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) x) :=
      mfderiv_comp (I := MC n) (I' := MC n) (I'' := MCprod n) x hetamd hcmm
    exact (hev.mfderiv_eq).symm.trans hcomp
  have hAsurj : Function.Surjective (mfderiv (MC n) (MCprod n) etahat (c x)) := by
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    refine ⟨(mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) x) w, ?_⟩
    have h2 : mfderiv (MC n) (MCprod n) η x w = v := hw
    rw [hchain] at h2
    exact h2
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ (CollarParam n) := by
    show Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Module.finrank_self,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have hAsurj' : Function.Surjective (fderiv ℝ etahat (c x)) := by
    rw [← mfderiv_eq_fderiv]
    rw [← prodModel_eq_self (n := n)]
    exact hAsurj
  have hAinj' : Function.Injective (fderiv ℝ etahat (c x)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv ℝ etahat (c x)).toLinearMap)).mpr hAsurj'
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_of_injective hdim
    (fderiv ℝ etahat (c x)) hAinj'
  have hF : HasFDerivAt etahat (L : EuclideanSpace ℝ (Fin n) →L[ℝ] CollarParam n) (c x) :=
    HasFDerivAt.congr_fderiv ((hetacd.differentiableAt hn0).hasFDerivAt) hL.symm
  have hstrict := hetacd.hasStrictFDerivAt' hF hn0
  let φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (CollarParam n) :=
    hstrict.toOpenPartialHomeomorph etahat
  have hφcoe : (φ : EuclideanSpace ℝ (Fin n) → CollarParam n) = etahat :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrict
  have hφsrc : c x ∈ φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict
  refine ⟨c.symm '' (φ.source ∩ c.target), ?_, ?_, ?_⟩
  · exact c.isOpen_image_symm_of_subset_target (φ.open_source.inter c.open_target) inter_subset_right
  · exact ⟨c x, ⟨hφsrc, hcxs⟩, c.left_inv hcx⟩
  · intro y hy y' hy' heq
    have hleft : ∀ z ∈ φ.source ∩ c.target, c.symm (φ.symm (etahat z)) = c.symm z := by
      rintro z hz
      have hφz : φ z = etahat z := by rw [hφcoe]
      have hsym : φ.symm (etahat z) = z := by
        rw [← hφz]
        exact φ.left_inv hz.1
      rw [hsym]
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hy'
    have e1 : etahat z = etahat z' := heq
    rw [← hleft z hz, ← hleft z' hz', e1]

/-- **A local section is an immersion and its target map is a submersion.**  If the smooth map
`η : M → ℝ^{n-1} × ℝ` has a smooth local section `σ` on an open set `U` (i.e. `η (σ p) = p` for
`p ∈ U`), then at every `q ∈ U` the manifold derivative of `σ` at `q` is injective and the manifold
derivative of `η` at `σ q` is surjective. -/
theorem injective_mfderiv_of_section {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {η : M → CollarParam n} (hη : ContMDiff (MC n) (MCprod n) smoothOrder η)
    {σ : CollarParam n → M} {U : Set (CollarParam n)} (hU : IsOpen U)
    (hσ : ContMDiffOn (MCprod n) (MC n) smoothOrder σ U)
    (hsect : ∀ p ∈ U, η (σ p) = p) {q : CollarParam n} (hq : q ∈ U) :
    Function.Injective (mfderiv (MCprod n) (MC n) σ q) ∧
    Function.Surjective (mfderiv (MC n) (MCprod n) η (σ q)) := by
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  have hσm : MDifferentiableAt (MCprod n) (MC n) σ q :=
    (hσ.contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt hn0
  have hηm : MDifferentiableAt (MC n) (MCprod n) η (σ q) :=
    (hη.contMDiffAt (x := σ q)).mdifferentiableAt hn0
  have hev : (fun p => η (σ p)) =ᶠ[𝓝 q] id :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hq) (fun p hp => hsect p hp)
  have hcomp : mfderiv (MCprod n) (MCprod n) (fun p => η (σ p)) q
      = (mfderiv (MC n) (MCprod n) η (σ q)).comp (mfderiv (MCprod n) (MC n) σ q) :=
    mfderiv_comp (I := MCprod n) (I' := MC n) (I'' := MCprod n) q hηm hσm
  have hleft : ∀ v : TangentSpace (MCprod n) q,
      (mfderiv (MC n) (MCprod n) η (σ q)) ((mfderiv (MCprod n) (MC n) σ q) v) = v := by
    intro v
    have h2 : (mfderiv (MCprod n) (MCprod n) (fun p => η (σ p)) q) v = v := by
      rw [hev.mfderiv_eq, mfderiv_id]
      rfl
    rw [hcomp] at h2
    simpa [ContinuousLinearMap.comp_apply] using h2
  constructor
  · intro v w hvw
    have h3 : (mfderiv (MC n) (MCprod n) η (σ q)) ((mfderiv (MCprod n) (MC n) σ q) v)
        = (mfderiv (MC n) (MCprod n) η (σ q)) ((mfderiv (MCprod n) (MC n) σ q) w) := by
      rw [hvw]
    rw [hleft v, hleft w] at h3
    exact h3
  · intro v
    exact ⟨(mfderiv (MCprod n) (MC n) σ q) v, hleft v⟩

/-- **Two local sections of `η` agree on a neighbourhood of a common point.**  At a point `q` where
two smooth local sections `σ₁`, `σ₂` of `η` have the same value, `η` is a local diffeomorphism at
that common value, so the two sections agree near `q`. -/
theorem sections_eventuallyEq_of_eq {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {η : M → CollarParam n} (hη : ContMDiff (MC n) (MCprod n) smoothOrder η)
    {σ₁ σ₂ : CollarParam n → M} {U₁ U₂ : Set (CollarParam n)} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hσ₁ : ContMDiffOn (MCprod n) (MC n) smoothOrder σ₁ U₁)
    (hσ₂ : ContMDiffOn (MCprod n) (MC n) smoothOrder σ₂ U₂)
    (hs₁ : ∀ p ∈ U₁, η (σ₁ p) = p) (hs₂ : ∀ p ∈ U₂, η (σ₂ p) = p)
    {q : CollarParam n} (hq : q ∈ U₁) (hq' : q ∈ U₂) (heq : σ₁ q = σ₂ q) :
    σ₁ =ᶠ[𝓝 q] σ₂ := by
  have hsurj := (injective_mfderiv_of_section hη hU₁ hσ₁ hs₁ hq).2
  obtain ⟨V, hVopen, hxV, hVinj⟩ := locally_injective_of_surjective_mfderiv hn hη hsurj
  have hcont₁ : ContinuousAt σ₁ q := (hσ₁.contMDiffAt (hU₁.mem_nhds hq)).continuousAt
  have hcont₂ : ContinuousAt σ₂ q := (hσ₂.contMDiffAt (hU₂.mem_nhds hq')).continuousAt
  have hpre₁ : σ₁ ⁻¹' V ∈ 𝓝 q := hcont₁.preimage_mem_nhds (hVopen.mem_nhds hxV)
  have hpre₂ : σ₂ ⁻¹' V ∈ 𝓝 q := by
    refine hcont₂.preimage_mem_nhds (hVopen.mem_nhds ?_)
    rw [← heq]; exact hxV
  refine Filter.eventuallyEq_of_mem
    (Filter.inter_mem (Filter.inter_mem (hU₁.mem_nhds hq) (hU₂.mem_nhds hq'))
      (Filter.inter_mem hpre₁ hpre₂)) ?_
  intro p hp
  exact hVinj hp.2.1 hp.2.2 (by rw [hs₁ p hp.1.1, hs₂ p hp.1.2])

/-- **Two local sections agree on a convex overlap.**  If two smooth local sections of `η` are
defined on the open sets `U₁`, `U₂` whose intersection is convex, and they agree at one point of the
intersection, then they agree on the whole intersection: the set where they agree is open (by
`sections_eventuallyEq_of_eq`) and its limit points inside the intersection are points of
agreement (by continuity and uniqueness of limits in the Hausdorff space `M`), so it is clopen and
nonempty in the preconnected intersection. -/
theorem sections_eqOn_of_convex {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {η : M → CollarParam n} (hη : ContMDiff (MC n) (MCprod n) smoothOrder η)
    {σ₁ σ₂ : CollarParam n → M} {U₁ U₂ : Set (CollarParam n)} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hσ₁ : ContMDiffOn (MCprod n) (MC n) smoothOrder σ₁ U₁)
    (hσ₂ : ContMDiffOn (MCprod n) (MC n) smoothOrder σ₂ U₂)
    (hs₁ : ∀ p ∈ U₁, η (σ₁ p) = p) (hs₂ : ∀ p ∈ U₂, η (σ₂ p) = p)
    (hconv : Convex ℝ (U₁ ∩ U₂)) {q : CollarParam n} (hq : q ∈ U₁ ∩ U₂)
    (hqeq : σ₁ q = σ₂ q) :
    ∀ p ∈ U₁ ∩ U₂, σ₁ p = σ₂ p := by
  have hAopen : IsOpen (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p}) := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hpV, hp⟩
    refine Filter.inter_mem ((hU₁.inter hU₂).mem_nhds hpV) ?_
    exact sections_eventuallyEq_of_eq hn hη hU₁ hU₂ hσ₁ hσ₂ hs₁ hs₂ hpV.1 hpV.2 hp
  have hAne : ((U₁ ∩ U₂) ∩ (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p})).Nonempty :=
    ⟨q, hq, hq, hqeq⟩
  have hAcl : closure (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p}) ∩ (U₁ ∩ U₂)
      ⊆ (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p}) := by
    rintro p ⟨hpcl, hpV⟩
    have hcl : ClusterPt p (𝓟 (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p})) :=
      mem_closure_iff_clusterPt.mp hpcl
    haveI : NeBot (𝓝 p ⊓ 𝓟 (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p})) := hcl
    have hcont₁ : ContinuousAt σ₁ p := (hσ₁.contMDiffAt (hU₁.mem_nhds hpV.1)).continuousAt
    have hcont₂ : ContinuousAt σ₂ p := (hσ₂.contMDiffAt (hU₂.mem_nhds hpV.2)).continuousAt
    have hev : σ₁ =ᶠ[𝓝 p ⊓ 𝓟 (U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p})] σ₂ :=
      Filter.eventually_of_mem (Filter.mem_inf_of_right (Filter.mem_principal_self _))
        (fun x hx => hx.2)
    exact ⟨hpV, tendsto_nhds_unique_of_eventuallyEq
      (hcont₁.tendsto.mono_left inf_le_left) (hcont₂.tendsto.mono_left inf_le_left) hev⟩
  have hsub := hconv.isPreconnected.subset_of_closure_inter_subset
    (u := U₁ ∩ U₂ ∩ {p : CollarParam n | σ₁ p = σ₂ p}) hAopen hAne hAcl
  exact fun p hp => (hsub hp).2

/-- A positive lower semicontinuous function on `ℝ` has a smooth positive minorant. -/
theorem exists_smooth_minorant_lsc {φ : ℝ → ℝ} (hpos : ∀ s : ℝ, 0 < φ s)
    (hlsc : LowerSemicontinuous φ) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ s : ℝ, 0 < r s) ∧
      ∀ s : ℝ, r s ≤ φ s := by
  have hloc : ∀ x : ℝ, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ Set.Ioo (0 : ℝ) (φ y) := fun x => by
    refine ⟨φ x / 2, ?_⟩
    have h1 : φ x / 2 < φ x := by linarith [hpos x]
    have hpos' : 0 < φ x / 2 := by linarith [hpos x]
    exact ((lowerSemicontinuous_iff.mp hlsc x) (φ x / 2) h1).mono
      (fun y hy => ⟨hpos', hy⟩)
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (F := ℝ) (n := (⊤ : ℕ∞)) (t := fun y => Set.Ioo (0 : ℝ) (φ y))
    (fun y => convex_Ioo 0 (φ y)) hloc
  exact ⟨fun s => g s, by
      have h := g.contMDiff
      rw [contMDiff_iff_contDiff] at h
      simpa using h,
    fun s => (hg s).1, fun s => (hg s).2.le⟩

/-- **Availability radius.**  Given positive functions `r`, `ε` on `ℝ` with `r ≤ 1`, there is a
smooth positive `ρ` such that every point `(u,t)` with `‖u‖ < ρ t` lies in the slab
`{‖u‖ < r s, |t - s| < ε s}` of some index `s`. -/
theorem exists_radius_minorant {n : ℕ} {r ε : ℝ → ℝ} (hr : ∀ s, 0 < r s) (hε : ∀ s, 0 < ε s)
    (hr1 : ∀ s, r s ≤ 1) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ t, 0 < ρ t) ∧
      ∀ (u : EuclideanSpace ℝ (Fin (n - 1))) (t : ℝ), ‖u‖ < ρ t →
        ∃ s : ℝ, |t - s| < ε s ∧ ‖u‖ < r s := by
  classical
  set A : ℝ → ℝ := fun t => sSup {x : ℝ | ∃ s : ℝ, |t - s| < ε s ∧ x = r s} with hAdef
  have hbdd : ∀ t : ℝ, BddAbove {x : ℝ | ∃ s : ℝ, |t - s| < ε s ∧ x = r s} := fun t =>
    ⟨1, by rintro x ⟨s, -, rfl⟩; exact hr1 s⟩
  have hmem : ∀ t s : ℝ, |t - s| < ε s →
      r s ∈ {x : ℝ | ∃ s' : ℝ, |t - s'| < ε s' ∧ x = r s'} := fun t s hs => ⟨s, hs, rfl⟩
  have hself : ∀ t : ℝ, |t - t| < ε t := by intro t; simpa using hε t
  have hApos : ∀ t : ℝ, 0 < A t := by
    intro t
    have h1 : r t ≤ A t := by
      rw [hAdef]
      exact le_csSup (hbdd t) (hmem t t (hself t))
    linarith [hr t, h1]
  have hAlsc : LowerSemicontinuous A := by
    rw [lowerSemicontinuous_iff]
    intro t
    rw [lowerSemicontinuousAt_iff]
    intro a ha
    have ha' : a < A t := ha
    rw [hAdef] at ha'
    obtain ⟨x, ⟨s, hs, hxs⟩, hax⟩ :=
      (lt_csSup_iff (hbdd t) ⟨r t, hmem t t (hself t)⟩).mp ha'
    rw [hxs] at hax
    have hI : {t' : ℝ | |t' - s| < ε s} ∈ 𝓝 t :=
      (isOpen_Iio.preimage ((continuous_id.sub continuous_const).abs)).mem_nhds hs
    filter_upwards [hI] with t' ht'
    have h1 : r s ≤ A t' := by
      rw [hAdef]
      exact le_csSup (hbdd t') (hmem t' s ht')
    linarith
  obtain ⟨ρ, hρcd, hρpos, hρle⟩ := exists_smooth_minorant_lsc hApos hAlsc
  refine ⟨ρ, hρcd, hρpos, ?_⟩
  intro u t hu
  have hu' : ‖u‖ < A t := lt_of_lt_of_le hu (hρle t)
  rw [hAdef] at hu'
  obtain ⟨x, ⟨s, hs, hxs⟩, hux⟩ :=
    (lt_csSup_iff (hbdd t) ⟨r t, hmem t t (hself t)⟩).mp hu'
  exact ⟨s, hs, by rwa [hxs] at hux⟩

/-- The radial compression of `ℝ^{n-1}` onto the open unit ball. -/
def tubeSquash (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) : EuclideanSpace ℝ (Fin (n - 1)) :=
  (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u

lemma tubeSquash_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞)) (tubeSquash n) :=
  (radial_ball_facts (n - 1)).1

lemma tubeSquash_injective (n : ℕ) : Function.Injective (tubeSquash n) :=
  (radial_ball_facts (n - 1)).2.1

lemma tubeSquash_norm_lt_one (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    ‖tubeSquash n u‖ < 1 := (radial_ball_facts (n - 1)).2.2.1 u

lemma tubeSquash_zero (n : ℕ) : tubeSquash n 0 = 0 := (radial_ball_facts (n - 1)).2.2.2.1

lemma tubeSquash_eq_univUnitBall (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    tubeSquash n u = OpenPartialHomeomorph.univUnitBall u :=
  (OpenPartialHomeomorph.univUnitBall_apply
    (E := EuclideanSpace ℝ (Fin (n - 1))) u).symm

lemma tubeSquash_fderiv_injective (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    Function.Injective (fderiv ℝ (tubeSquash n) u) := by
  have hsurj : Function.Surjective (fderiv ℝ (tubeSquash n) u) :=
    (radial_ball_facts (n - 1)).2.2.2.2 u
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) := rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

/-- The shrinking self-map `(u,s) ↦ (ρ s / 2 • (√(1+‖u‖²))⁻¹ • u, s)`. -/
def tubeShrink (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) : CollarParam n :=
  ((ρ p.2 / 2) • tubeSquash n p.1, p.2)

lemma tubeShrink_snd (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) :
    (tubeShrink n ρ p).2 = p.2 := rfl

lemma tubeShrink_fst (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) :
    (tubeShrink n ρ p).1 = (ρ p.2 / 2) • tubeSquash n p.1 := rfl

lemma tubeShrink_contDiff (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ContDiff ℝ ((⊤ : ℕ∞)) (tubeShrink n ρ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞))
      (fun p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ p.2 / 2) • tubeSquash n p.1) :=
    ((hρcd.comp contDiff_snd).div_const 2).smul ((tubeSquash_contDiff n).comp contDiff_fst)
  exact h1.prodMk contDiff_snd

lemma tubeShrink_contMDiff (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ContMDiff (MCprod n) (MCprod n) smoothOrder (tubeShrink n ρ) := by
  rw [prodModel_eq_self (n := n)]
  exact (contMDiff_iff_contDiff).2 (tubeShrink_contDiff n hρcd)

lemma tubeShrink_inv_contMDiffOn (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ)
    (hρ : ∀ s, 0 < ρ s) :
    ContMDiffOn (MCprod n) (MCprod n) smoothOrder
      (fun q : CollarParam n =>
        (OpenPartialHomeomorph.univUnitBall.symm (((ρ q.2 / 2)⁻¹) • q.1), q.2))
      {q : CollarParam n | ‖q.1‖ < ρ q.2 / 2} := by
  rw [prodModel_eq_self (n := n)]
  rw [contMDiffOn_iff_contDiffOn]
  have hinner : ContDiffOn ℝ ((⊤ : ℕ∞))
      (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((ρ q.2 / 2)⁻¹) • q.1)
      {q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖q.1‖ < ρ q.2 / 2} := by
    intro q hq
    have hne : ρ q.2 / 2 ≠ 0 := by have := hρ q.2; linarith
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞))
        (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ q.2 / 2)⁻¹) q :=
      (((hρcd.contDiffAt).comp q contDiffAt_snd).div_const 2).inv hne
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞))
        (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => q.1) q := contDiffAt_fst
    exact (h1.smul h2).contDiffWithinAt
  have hmaps : MapsTo (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((ρ q.2 / 2)⁻¹) • q.1)
      {q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖q.1‖ < ρ q.2 / 2}
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1) := by
    intro q hq
    have hpos : 0 < ρ q.2 / 2 := by have := hρ q.2; linarith
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    rw [inv_mul_lt_one₀ hpos]
    exact hq
  have hsymm := OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
    (E := EuclideanSpace ℝ (Fin (n - 1))) (n := (⊤ : ℕ∞))
  have hcomp := hsymm.comp hinner hmaps
  exact hcomp.prodMk contDiffOn_snd

theorem exists_shrink_param_clean {n : ℕ} {ρ : ℝ → ℝ} (hρ : ∀ s, 0 < ρ s)
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ∃ S : CollarParam n → CollarParam n, ContMDiff (MCprod n) (MCprod n) smoothOrder S ∧
      (∀ p : CollarParam n, ‖(S p).1‖ < ρ (S p).2) ∧
      (∀ p : CollarParam n, (S p).2 = p.2) ∧
      (∀ s : ℝ, S ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
        = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) ∧
      Set.InjOn S {p : CollarParam n | ‖p.1‖ ≤ 1} ∧
      (∀ p : CollarParam n, Function.Injective (mfderiv (MCprod n) (MCprod n) S p)) := by
  classical
  refine ⟨tubeShrink n ρ, tubeShrink_contMDiff n hρcd, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have hpos : 0 < ρ p.2 / 2 := by have := hρ p.2; linarith
    rw [tubeShrink_fst, tubeShrink_snd, norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
    calc (ρ p.2 / 2) * ‖tubeSquash n p.1‖ < (ρ p.2 / 2) * 1 :=
          mul_lt_mul_of_pos_left (tubeSquash_norm_lt_one n p.1) hpos
      _ = ρ p.2 / 2 := mul_one _
      _ < ρ p.2 := by linarith [hρ p.2]
  · intro p; exact tubeShrink_snd n ρ p
  · intro s
    rw [tubeShrink, tubeSquash_zero, smul_zero]
  · -- injectivity on the unit tube
    intro p hp q hq hpq
    have h2 : p.2 = q.2 := by
      simpa only [tubeShrink] using congrArg Prod.snd hpq
    have h1 : p.1 = q.1 := by
      refine tubeSquash_injective n ?_
      have h3 : (ρ p.2 / 2) • tubeSquash n p.1 = (ρ q.2 / 2) • tubeSquash n q.1 := by
        simpa only [tubeShrink] using congrArg Prod.fst hpq
      rw [h2] at h3
      exact smul_right_injective (EuclideanSpace ℝ (Fin (n - 1)))
        (ne_of_gt (by have := hρ q.2; linarith)) h3
    exact Prod.ext h1 h2
  · -- the derivative is injective: the map is a local diffeomorphism
    intro p
    have hΦ : IsLocalDiffeomorphAt (MCprod n) (MCprod n) smoothOrder (tubeShrink n ρ) p := by
      let Φ : PartialDiffeomorph (MCprod n) (MCprod n) (CollarParam n) (CollarParam n) smoothOrder :=
        { toPartialEquiv :=
            { toFun := tubeShrink n ρ
              invFun := fun q : CollarParam n =>
                (OpenPartialHomeomorph.univUnitBall.symm (((ρ q.2 / 2)⁻¹) • q.1), q.2)
              source := univ
              target := {q : CollarParam n | ‖q.1‖ < ρ q.2 / 2}
              map_source' := by
                intro x _
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                show ‖((ρ x.2 / 2) • tubeSquash n x.1)‖ < ρ x.2 / 2
                rw [norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
                calc (ρ x.2 / 2) * ‖tubeSquash n x.1‖ < (ρ x.2 / 2) * 1 :=
                      mul_lt_mul_of_pos_left (tubeSquash_norm_lt_one n x.1) hpos
                  _ = ρ x.2 / 2 := mul_one _
              map_target' := fun x _ => Set.mem_univ x
              left_inv' := by
                intro x _
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                have hmem : tubeSquash n x.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1 :=
                  mem_ball_zero_iff.mpr (tubeSquash_norm_lt_one n x.1)
                show (OpenPartialHomeomorph.univUnitBall.symm
                  (((ρ x.2 / 2)⁻¹) • ((ρ x.2 / 2) • tubeSquash n x.1)), x.2) = x
                rw [inv_smul_smul₀ (ne_of_gt hpos)]
                refine Prod.ext ?_ rfl
                show OpenPartialHomeomorph.univUnitBall.symm (tubeSquash n x.1) = x.1
                rw [tubeSquash_eq_univUnitBall n x.1]
                exact OpenPartialHomeomorph.left_inv OpenPartialHomeomorph.univUnitBall
                  (Set.mem_univ x.1)
              right_inv' := by
                intro x hx
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                have hmem : ((ρ x.2 / 2)⁻¹) • x.1
                    ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1 := by
                  rw [mem_ball_zero_iff, norm_smul,
                    Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hpos)), inv_mul_lt_one₀ hpos]
                  exact hx
                show (((ρ x.2 / 2)) • tubeSquash n (OpenPartialHomeomorph.univUnitBall.symm
                  (((ρ x.2 / 2)⁻¹) • x.1)), x.2) = x
                refine Prod.ext ?_ rfl
                show ((ρ x.2 / 2)) • OpenPartialHomeomorph.univUnitBall
                  (OpenPartialHomeomorph.univUnitBall.symm (((ρ x.2 / 2)⁻¹) • x.1)) = x.1
                rw [OpenPartialHomeomorph.right_inv OpenPartialHomeomorph.univUnitBall hmem]
                simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
              }
          open_source := isOpen_univ
          open_target := isOpen_lt continuous_fst.norm
            ((hρcd.continuous.comp continuous_snd).div_const 2)
          contMDiffOn_toFun := (tubeShrink_contMDiff n hρcd).contMDiffOn
          contMDiffOn_invFun := tubeShrink_inv_contMDiffOn n hρcd hρ }
      exact PartialDiffeomorph.isLocalDiffeomorphAt (MCprod n) (MCprod n) smoothOrder Φ
        (Set.mem_univ p)
    have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hΦ hn]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hΦ hn).injective

/-- The convexity of the intersection of two slabs of the same type. -/
lemma convex_slab_inter {n : ℕ} {r r' ε ε' s s' : ℝ} :
    Convex ℝ ({p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε}
      ∩ {p : CollarParam n | ‖p.1‖ < r' ∧ |p.2 - s'| < ε'}) := by
  intro a ha b hb u v hu hv huv
  have ha1 : a.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r :=
    mem_ball_zero_iff.mpr ha.1.1
  have hb1 : b.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r :=
    mem_ball_zero_iff.mpr hb.1.1
  have ha1' : a.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r' :=
    mem_ball_zero_iff.mpr ha.2.1
  have hb1' : b.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r' :=
    mem_ball_zero_iff.mpr hb.2.1
  have ha2 : a.2 ∈ Set.Ioo (s - ε) (s + ε) := by
    rw [Set.mem_Ioo]
    have h := abs_lt.mp ha.1.2
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hb2 : b.2 ∈ Set.Ioo (s - ε) (s + ε) := by
    rw [Set.mem_Ioo]
    have h := abs_lt.mp hb.1.2
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have ha2' : a.2 ∈ Set.Ioo (s' - ε') (s' + ε') := by
    rw [Set.mem_Ioo]
    have h := abs_lt.mp ha.2.2
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hb2' : b.2 ∈ Set.Ioo (s' - ε') (s' + ε') := by
    rw [Set.mem_Ioo]
    have h := abs_lt.mp hb.2.2
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa using (convex_ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r) ha1 hb1 hu hv huv
  · have hmem := (convex_Ioo (s - ε) (s + ε)) ha2 hb2 hu hv huv
    rw [Set.mem_Ioo] at hmem
    simp only [smul_eq_mul] at hmem
    rw [abs_lt]
    have h2 : (u • a + v • b).2 = u * a.2 + v * b.2 := by simp
    rw [h2]
    constructor <;> linarith [hmem.1, hmem.2]
  · simpa using (convex_ball (0 : EuclideanSpace ℝ (Fin (n - 1))) r') ha1' hb1' hu hv huv
  · have hmem := (convex_Ioo (s' - ε') (s' + ε')) ha2' hb2' hu hv huv
    rw [Set.mem_Ioo] at hmem
    simp only [smul_eq_mul] at hmem
    rw [abs_lt]
    have h2 : (u • a + v • b).2 = u * a.2 + v * b.2 := by simp
    rw [h2]
    constructor <;> linarith [hmem.1, hmem.2]

/-- **C.**  Gluing the local slab sections into the collar. -/
theorem exists_collar_of_local_slabs {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hcore : ∀ s : ℝ, P (γ s) = 0 ∧ g (γ s) = s)
    (hloc : ∀ s : ℝ, ∃ (r ε : ℝ) (σ : CollarParam n → M), 0 < r ∧ 0 < ε ∧
      ContMDiffOn (MCprod n) (MC n) smoothOrder σ
        {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
      (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
      (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p)) :
    ∃ Ψ : CollarParam n → M, ContMDiff (MCprod n) (MC n) smoothOrder Ψ ∧
      (∀ s : ℝ, Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s) ∧
      Set.InjOn Ψ {p : CollarParam n | ‖p.1‖ ≤ 1} ∧
      (∀ p : CollarParam n, ‖p.1‖ ≤ 1 → Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : CollarParam n,
        ‖p.1‖ ≤ 1 → S ≤ |p.2| → Ψ p ∉ K) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  -- smoothness of `η = (P, g)`
  have hηsm : ContMDiff (MC n) (MCprod n) smoothOrder (fun x : M => (P x, g x)) := by
    rw [prodModel_eq_self (n := n)]
    exact (contMDiff_prod_module_iff (I := MC n) (f := fun x : M => (P x, g x))).2
      ⟨hP, hg⟩
  -- choose the local slab data
  choose r ε σ hr hε hσsm hσcore hσsect using hloc
  set slabF : ℝ → Set (CollarParam n) :=
    fun s => {p : CollarParam n | ‖p.1‖ < r s ∧ |p.2 - s| < ε s} with hslabFdef
  have hslabF_open : ∀ s : ℝ, IsOpen (slabF s) := by
    intro s
    rw [hslabFdef]
    exact (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const)
  have haxis_mem : ∀ t : ℝ, ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) ∈ slabF t := by
    intro t
    rw [hslabFdef]
    exact ⟨by simpa using hr t, by simpa using hε t⟩
  -- the local sections agree on overlaps of slabs
  have hagree : ∀ (s s' : ℝ) (p : CollarParam n), p ∈ slabF s → p ∈ slabF s' →
      σ s p = σ s' p := by
    intro s s' p hp hp'
    by_cases hne : (slabF s ∩ slabF s').Nonempty
    · obtain ⟨q, hq⟩ := hne
      have ht1 : |q.2 - s| < ε s := hq.1.2
      have ht2 : |q.2 - s'| < ε s' := hq.2.2
      have hconv : Convex ℝ (slabF s ∩ slabF s') := by
        rw [hslabFdef]
        exact convex_slab_inter
      have h0mem : ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2) ∈ slabF s ∩ slabF s' := by
        constructor
        · rw [hslabFdef]; exact ⟨by simpa using hr s, ht1⟩
        · rw [hslabFdef]; exact ⟨by simpa using hr s', ht2⟩
      have h0eq : σ s ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2)
          = σ s' ((0 : EuclideanSpace ℝ (Fin (n - 1))), q.2) := by
        rw [hσcore s q.2 ht1, hσcore s' q.2 ht2]
      exact sections_eqOn_of_convex hn1 hηsm (hslabF_open s) (hslabF_open s')
        (hσsm s) (hσsm s') (fun q hq => hσsect s q hq.1 hq.2)
        (fun q hq => hσsect s' q hq.1 hq.2) hconv h0mem h0eq p ⟨hp, hp'⟩
    · exact absurd ⟨p, hp, hp'⟩ hne
  -- the union of the slabs and the glued section
  set U : Set (CollarParam n) := ⋃ s, slabF s with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]; exact isOpen_iUnion hslabF_open
  have hmemU : ∀ (s : ℝ) (p : CollarParam n), p ∈ slabF s → p ∈ U :=
    fun s p hp => Set.mem_iUnion.mpr ⟨s, hp⟩
  let sIdx : CollarParam n → ℝ :=
    fun p => if h : p ∈ U then Classical.choose (Set.mem_iUnion.mp h) else 0
  let Ψ₀ : CollarParam n → M := fun p => σ (sIdx p) p
  have hsIdx : ∀ (p : CollarParam n) (hp : p ∈ U), p ∈ slabF (sIdx p) := by
    intro p hp
    have h1 : sIdx p = Classical.choose (Set.mem_iUnion.mp hp) := by
      show (if h : p ∈ U then Classical.choose (Set.mem_iUnion.mp h) else 0) = _
      rw [dif_pos hp]
    rw [h1]
    exact Classical.choose_spec (Set.mem_iUnion.mp hp)
  have hΨ₀val : ∀ (s : ℝ) (p : CollarParam n), p ∈ slabF s → Ψ₀ p = σ s p :=
    fun s p hp => hagree (sIdx p) s p (hsIdx p (hmemU s p hp)) hp
  have hΨ₀sm : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ U := by
    intro p hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    have hcongr : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ₀ (U ∩ slabF s) :=
      ((hσsm s).mono inter_subset_right).congr (fun q hq => hΨ₀val s q hq.2)
    exact (hcongr.contMDiffAt ((hUopen.inter (hslabF_open s)).mem_nhds ⟨hp, hs⟩)).contMDiffWithinAt
  have hΨ₀sect : ∀ p ∈ U, ((P (Ψ₀ p), g (Ψ₀ p)) : CollarParam n) = p := by
    intro p hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    rw [hΨ₀val s p hs]
    exact hσsect s p hs.1 hs.2
  have hΨ₀core : ∀ t : ℝ, Ψ₀ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t := by
    intro t
    rw [hΨ₀val t _ (haxis_mem t)]
    exact hσcore t t (by simpa using hε t)
  have hΨ₀imm : ∀ p ∈ U, Function.Injective (mfderiv (MCprod n) (MC n) Ψ₀ p) := by
    intro p hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    have hev : Ψ₀ =ᶠ[𝓝 p] σ s :=
      Filter.eventuallyEq_of_mem ((hUopen.inter (hslabF_open s)).mem_nhds ⟨hp, hs⟩)
        (fun q hq => hΨ₀val s q hq.2)
    rw [hev.mfderiv_eq]
    exact (injective_mfderiv_of_section hηsm (hslabF_open s) (hσsm s)
      (fun q hq => hσsect s q hq.1 hq.2) hs).1
  -- the availability radius and the radial compression
  have hrpos : ∀ s : ℝ, 0 < min (r s) 1 := fun s => lt_min (hr s) one_pos
  have hrle : ∀ s : ℝ, min (r s) 1 ≤ 1 := fun s => min_le_right _ _
  obtain ⟨ρ, hρcd, hρpos, hρcov⟩ :=
    exists_radius_minorant (n := n) (r := fun s => min (r s) 1) (ε := ε) hrpos hε hrle
  obtain ⟨S, hSsm, hSnorm, hSsnd, hSaxis, hSinj, hSimm⟩ := exists_shrink_param_clean hρpos hρcd
  have hSmem : ∀ p : CollarParam n, S p ∈ U := by
    intro p
    have h1 : ‖(S p).1‖ < ρ p.2 := by
      have h2 := hSnorm p
      rwa [hSsnd p] at h2
    obtain ⟨s, hs1, hs2⟩ := hρcov (S p).1 p.2 h1
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    exact ⟨lt_of_lt_of_le hs2 (min_le_left _ _), by rwa [hSsnd p]⟩
  have hηS : ∀ p : CollarParam n, ((P (Ψ₀ (S p)), g (Ψ₀ (S p))) : CollarParam n) = S p :=
    fun p => hΨ₀sect (S p) (hSmem p)
  refine ⟨fun p => Ψ₀ (S p), ?_, ?_, ?_, ?_, ?_⟩
  · have hSsm' : ContMDiffOn (MCprod n) (MCprod n) smoothOrder S Set.univ :=
      fun x _ => (hSsm.contMDiffAt (x := x)).contMDiffWithinAt
    exact contMDiffOn_univ.mp (hΨ₀sm.comp hSsm' (fun p _ => hSmem p))
  · intro t
    show Ψ₀ (S ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) = γ t
    rw [hSaxis t, hΨ₀core t]
  · intro p hp q hq hpq
    refine hSinj hp hq ?_
    have hpq' : Ψ₀ (S p) = Ψ₀ (S q) := hpq
    have h2 : ((P (Ψ₀ (S p)), g (Ψ₀ (S p))) : CollarParam n)
        = (P (Ψ₀ (S q)), g (Ψ₀ (S q))) := by rw [hpq']
    rwa [hηS p, hηS q] at h2
  · intro p hp
    have hchain : mfderiv (MCprod n) (MC n) (fun p => Ψ₀ (S p)) p
        = (mfderiv (MCprod n) (MC n) Ψ₀ (S p)).comp (mfderiv (MCprod n) (MCprod n) S p) :=
      mfderiv_comp (I := MCprod n) (I' := MCprod n) (I'' := MC n) (f := S) (g := Ψ₀) p
        ((hΨ₀sm.contMDiffAt (hUopen.mem_nhds (hSmem p))).mdifferentiableAt hn0)
        (hSsm.contMDiffAt.mdifferentiableAt hn0)
    show Function.Injective (mfderiv (MCprod n) (MC n) (fun p => Ψ₀ (S p)) p)
    rw [hchain]
    intro a b hab
    exact hSimm p (hΨ₀imm (S p) (hSmem p) hab)
  · intro K hK
    obtain ⟨C, hC⟩ := (hK.image hg.continuous).isBounded.exists_norm_le
    refine ⟨C + 1, ?_⟩
    intro p hp hpC hmemK
    have h1 : g (Ψ₀ (S p)) ∈ g '' K := ⟨Ψ₀ (S p), hmemK, rfl⟩
    have h2 : ‖g (Ψ₀ (S p))‖ ≤ C := hC _ h1
    have h3 : g (Ψ₀ (S p)) = p.2 := by
      have h4 : g (Ψ₀ (S p)) = (S p).2 := by
        have h5 := congrArg Prod.snd (hηS p)
        simpa using h5
      rw [h4, hSsnd p]
    rw [h3, Real.norm_eq_abs] at h2
    linarith

end

end Work.Noncompact.CompressionTube
