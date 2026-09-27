import Mathlib
import Submission.Work.Sard.rank_chart
import Submission.Work.Sard.submersion_smooth
import Submission.Work.Sard.exists_contDiff_eq_nhds_of_hasBump

/-!
# The slice-Sard lemma (generic transversality in a parameter)

This file proves the missing input of §4/§7 of `ENCODED_GENERIC_DEAD.md` (the ends-clause genericity
`Work.Drive.exists_homotopy_meet3Hyp_encoded` of the project lead's `NOTES_LEAD_hodd_blockT6.md` §2.1,
whose parametric-Sard route is dead):

> **Slice-Sard.**  For a smooth `Φ : G × Y → W` whose *total* derivative is onto at every zero
> (`finrank ℝ Y = finrank ℝ W + 1`), the set of `p : G` at which the slice `Φ (p, ·)` is a submersion
> at **every** zero in a compact set `K ⊆ Y` is **dense**.

The proof is the classical one, adapted to the codimension-one situation (which is the one that
occurs in the application: the charted triple-difference map has `9` variables and `8` equations):

* `Z := Φ ⁻¹' {0}` is a closed `C^∞` submanifold of dimension `finrank ℝ G + 1`, and `p` is a bad
  parameter exactly when `(p, 0)` is a critical value of the projection `Z → G`;
* at a zero `z₀`, the submersion chart `Work.Sard.submersion_smooth` writes `Z` locally as the image
  of `γ : ker (fderiv ℝ Φ z₀) → G × Y`, and the bad parameters coming from zeros near `z₀` are the
  critical values of the codimension-one map `Θ := Prod.fst ∘ γ` — to which the weak Sard theorem
  `Work.Sard.weakSardAt_all` applies;
* a compactness cover plus the Baire category theorem turn the local statement into the global one.

The `C¹`-criticality of the relevant maps is `Work.Sard.isClosed_setOf_not_surjective_fderiv`; the
finite codimension-one Sard theorem is the `C^∞` weak Sard of the workspace's Sard chapter.
-/

namespace Work.Drive

open Set Filter Topology
open scoped Topology ContDiff

set_option maxHeartbeats 1000000

/-! ## 0. Pure linear algebra

At a zero `z` of `Φ` with `fderiv ℝ Φ z` onto, the two conditions

* "the projection of `ker (fderiv ℝ Φ z)` onto the parameter factor is onto", and
* "the slice derivative `v ↦ fderiv ℝ Φ z (0, v)` is onto"

are equivalent.  (`A + B = ⊤` with `A` the parameter block and `B` the variable block: `A ⊆ B`
implies `B = ⊤`, and conversely.)  No dimension hypothesis is needed. -/

theorem surjective_snd_iff_surjective_projKer {G Y W : Type*} [AddCommGroup G] [Module ℝ G]
    [AddCommGroup Y] [Module ℝ Y] [AddCommGroup W] [Module ℝ W]
    (L : (G × Y) →ₗ[ℝ] W) (hL : L.range = ⊤) :
    Function.Surjective (fun z : L.ker => (z : G × Y).1) ↔
      Function.Surjective (fun v : Y => L (0, v)) := by
  constructor
  · intro h w
    obtain ⟨⟨u, v⟩, huv⟩ : w ∈ L.range := by
      rw [hL]; exact Submodule.mem_top
    obtain ⟨z, hz⟩ := h u
    have hz1 : (z : G × Y).1 = u := hz
    have hz0 : L (z : G × Y) = 0 := LinearMap.mem_ker.mp z.2
    refine ⟨v - (z : G × Y).2, ?_⟩
    have hpair : ((0 : G), v - (z : G × Y).2) = (u, v) - (z : G × Y) := by
      ext <;> simp [hz1]
    show L ((0 : G), v - (z : G × Y).2) = w
    rw [hpair, map_sub, huv, hz0, sub_zero]
  · intro h u
    obtain ⟨v, hv⟩ := h (-(L (u, 0)))
    have hv' : L (0, v) = -(L (u, 0)) := hv
    refine ⟨⟨(u, v), LinearMap.mem_ker.mpr ?_⟩, rfl⟩
    have hsplit : ((u, v) : G × Y) = (u, 0) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, hv', add_neg_cancel]

/-- A finite union of closed sets with empty interior has empty interior (`BaireSpace`). -/
lemma interior_biUnion_finset_eq_empty_of_isClosed {X ι : Type*} [TopologicalSpace X]
    (T : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ T, IsClosed (f i))
    (hfi : ∀ i ∈ T, interior (f i) = ∅) :
    interior (⋃ i ∈ T, f i) = ∅ := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.set_biUnion_insert]
      have h1 : interior (f a ∪ ⋃ i ∈ T, f i) ⊆ f a ∪ interior (⋃ i ∈ T, f i) :=
        (hf a (Finset.mem_insert_self a T)).interior_union_left
      have h2 : interior (⋃ i ∈ T, f i) = ∅ :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfi i (Finset.mem_insert_of_mem hi))
      rw [h2, union_empty] at h1
      have h3 : interior (f a ∪ ⋃ i ∈ T, f i) ⊆ interior (f a) :=
        interior_maximal h1 isOpen_interior
      rw [hfi a (Finset.mem_insert_self a T)] at h3
      exact le_bot_iff.mp h3

/-! ## 1. The local step

At a zero `z₀` of `Φ`, the parameters that are bad *because of* zeros near `z₀` are contained in a
closed set with empty interior. -/

theorem sliceSard_local_core {G Y W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hY : Module.finrank ℝ Y = Module.finrank ℝ W + 1)
    (Φ : G × Y → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    {V : Set (G × Y)} (hV : IsOpen V)
    (hreg : ∀ z : G × Y, z ∈ V → Φ z = 0 → Function.Surjective (fderiv ℝ Φ z))
    (z₀ : G × Y) (hz₀V : z₀ ∈ V) (hz₀ : Φ z₀ = 0) :
    ∃ (U : Set (G × Y)) (Clo : Set G),
      IsOpen U ∧ z₀ ∈ U ∧ U ⊆ V ∧ IsClosed Clo ∧ interior Clo = ∅ ∧
        {p : G | ∃ y : Y, (p, y) ∈ U ∧ Φ (p, y) = 0 ∧
          ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} ⊆ Clo := by
  classical
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hsurj₀ : Function.Surjective (fderiv ℝ Φ z₀) := hreg z₀ hz₀V hz₀
  -- ## the kernel of the derivative at `z₀`, its dimension and a complement
  let K₀ : Submodule ℝ (G × Y) := (fderiv ℝ Φ z₀).ker
  have hKfin : Module.finrank ℝ K₀ = Module.finrank ℝ G + 1 := by
    have h1 : Module.finrank ℝ W + Module.finrank ℝ K₀
        = Module.finrank ℝ G + (Module.finrank ℝ W + 1) := by
      have h := LinearMap.finrank_range_add_finrank_ker
        ((fderiv ℝ Φ z₀) : (G × Y) →ₗ[ℝ] W)
      rw [LinearMap.range_eq_top.mpr hsurj₀, finrank_top, Module.finrank_prod, hY] at h
      exact h
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K₀
  let proj : (G × Y) →ₗ[ℝ] K₀ := Submodule.projectionOnto K₀ C hC
  let projC : (G × Y) →L[ℝ] K₀ := proj.toContinuousLinearMap
  have hprojC : ∀ x : G × Y, projC x = proj x := fun x => rfl
  -- ## the submersion chart at `z₀`
  obtain ⟨Φp, O, hOopen, hmem, hΦpsm, hΦpfst, hΦpbase, hΦpleft⟩ :=
    Work.Sard.submersion_smooth Φ hΦ z₀ hsurj₀ C hC
  -- ## the parametrisation `γ` of the zero set near `z₀`
  let γ : K₀ → G × Y := fun k => Φp ((0 : W), k)
  let O₀ : Set K₀ := {k : K₀ | ((0 : W), k) ∈ O}
  have hcont0 : Continuous (fun k : K₀ => ((0 : W), k)) :=
    continuous_const.prodMk continuous_id
  have hO₀open : IsOpen O₀ := hOopen.preimage hcont0
  have hk₀O₀ : proj z₀ ∈ O₀ := by
    show ((0 : W), proj z₀) ∈ O
    rw [← hz₀]
    exact hmem
  -- ## smoothness of the parameter projection `Θ = Prod.fst ∘ γ` on `O₀`
  have hΘsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun k : K₀ => (γ k).1) O₀ := by
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun k : K₀ => ((0 : W), k)) O₀ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact (hΦpsm.comp h2 (fun k hk => hk)).fst
  obtain ⟨Til, hTilsm, hTileq⟩ := Work.Sard.exists_contDiff_eq_nhds_of_finiteDimensional
    (fun k : K₀ => (γ k).1) (proj z₀) O₀ (hO₀open.mem_nhds hk₀O₀) hΘsm
  -- ## the neighbourhood of `proj z₀` on which `Til = Θ`
  have hO₁mem : {k : K₀ | Til k = (γ k).1} ∈ 𝓝 (proj z₀) := hTileq
  obtain ⟨O₁, hO₁sub, hO₁open, hk₀O₁⟩ := mem_nhds_iff.mp hO₁mem
  -- ## the compact set on which everything is valid
  have hγk₀ : γ (proj z₀) = z₀ := by
    show Φp ((0 : W), proj z₀) = z₀
    rw [← hz₀]
    exact hΦpbase
  have hγcont : ContinuousAt γ (proj z₀) :=
    (hΦpsm.continuousOn.continuousAt (hOopen.mem_nhds hk₀O₀)).comp hcont0.continuousAt
  have hγnhds : γ ⁻¹' V ∈ 𝓝 (proj z₀) :=
    hγcont.preimage_mem_nhds (by rw [hγk₀]; exact hV.mem_nhds hz₀V)
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem
      (inter_mem (hO₀open.mem_nhds hk₀O₀) (hO₁open.mem_nhds hk₀O₁)) hγnhds)
  let L : Set K₀ := Metric.closedBall (proj z₀) (ρ / 2)
  have hLcomp : IsCompact L := isCompact_closedBall _ _
  have hLsub : L ⊆ O₀ ∩ O₁ ∩ γ ⁻¹' V := fun k hk =>
    hρsub (Metric.closedBall_subset_ball (by linarith) hk)
  -- ## weak Sard at the codimension-one map `Til : K₀ → G`
  have hsard : interior (Til '' ({k : K₀ | ¬ Function.Surjective (fderiv ℝ Til k)} ∩ L)) = ∅ :=
    Work.Sard.weakSardAt_all (Module.finrank ℝ G) (E := K₀) (F := G) hKfin rfl Til hTilsm L hLcomp
  let Clo : Set G := Til '' ({k : K₀ | ¬ Function.Surjective (fderiv ℝ Til k)} ∩ L)
  have hClo_closed : IsClosed Clo := by
    have hcrit : IsClosed {k : K₀ | ¬ Function.Surjective (fderiv ℝ Til k)} :=
      Work.Sard.isClosed_setOf_not_surjective_fderiv Til (hTilsm.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))
    exact ((hLcomp.inter_left hcrit).image hTilsm.continuous).isClosed
  -- ## the open set `U` of parameters
  have hpleft_mem : {x : G × Y | Φp (Φ x, proj x) = x} ∈ 𝓝 z₀ := by
    filter_upwards [hΦpleft] with x hx
    simpa using hx
  obtain ⟨U₁, hU₁sub, hU₁open, hz₀U₁⟩ := mem_nhds_iff.mp hpleft_mem
  let U : Set (G × Y) := U₁ ∩ (V ∩ projC ⁻¹' interior L)
  have hUopen : IsOpen U := hU₁open.inter (hV.inter (isOpen_interior.preimage projC.continuous))
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀U₁, hz₀V, ?_⟩
    have h1 : proj z₀ ∈ Metric.ball (proj z₀) (ρ / 2) := Metric.mem_ball_self (by linarith)
    have h2 : proj z₀ ∈ interior L :=
      interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball h1
    show projC z₀ ∈ interior L
    rwa [hprojC]
  -- ## every bad parameter coming from a zero in `U` is a critical value of `Til`
  refine ⟨U, Clo, hUopen, hz₀U, fun x hx => hx.2.1, hClo_closed, hsard, ?_⟩
  rintro p ⟨y, hyU, hy0, hynsurj⟩
  obtain ⟨hyU₁, hyV, hyL⟩ := hyU
  let k : K₀ := proj (p, y)
  have hkL : k ∈ L := interior_subset hyL
  have hkO₀ : k ∈ O₀ := (hLsub hkL).1.1
  have hkO₁ : k ∈ O₁ := (hLsub hkL).1.2
  have hkV : γ k ∈ V := (hLsub hkL).2
  have hzeq : ((p, y) : G × Y) = γ k := by
    have h1 : Φp (Φ (p, y), proj (p, y)) = (p, y) := hU₁sub hyU₁
    rw [hy0] at h1
    exact h1.symm
  have hΦγ : Φ (γ k) = 0 := hΦpfst ((0 : W), k) hkO₀
  have hsurjL : Function.Surjective (fderiv ℝ Φ (γ k)) := hreg (γ k) hkV hΦγ
  -- the parametrisation is a critical point of `Til` at every bad zero
  have hcrit : ¬ Function.Surjective (fderiv ℝ Til k) := by
    intro hsurj
    -- the derivative of `γ` at `k` and the chain rules
    have hΦpd : HasFDerivAt Φp (fderiv ℝ Φp ((0 : W), k)) ((0 : W), k) :=
      (hΦpsm.contDiffAt (hOopen.mem_nhds hkO₀)).differentiableAt hnz |>.hasFDerivAt
    set inrK : K₀ →L[ℝ] W × K₀ := (0 : K₀ →L[ℝ] W).prod (1 : K₀ →L[ℝ] K₀) with hinrK
    have hinrK_apply : ∀ v : K₀, inrK v = ((0 : W), v) := fun v => rfl
    have hinr : HasFDerivAt (fun k' : K₀ => ((0 : W), k')) inrK k :=
      (hasFDerivAt_const (x := k) (c := (0 : W))).prodMk (hasFDerivAt_id k)
    set Dγ : K₀ →L[ℝ] G × Y := (fderiv ℝ Φp ((0 : W), k)).comp inrK with hDγ
    have hγd : HasFDerivAt γ Dγ k := hΦpd.comp k hinr
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (γ k)) (γ k) :=
      (hΦ.contDiffAt.differentiableAt hnz).hasFDerivAt
    -- `fderiv ℝ Φ (γ k) ∘ Dγ = 0`
    have hchain : (fderiv ℝ Φ (γ k)).comp Dγ = 0 := by
      have h1 : (fun k' : K₀ => Φ (γ k')) =ᶠ[𝓝 k] (fun _ => (0 : W)) := by
        filter_upwards [hO₀open.mem_nhds hkO₀] with k' hk'
        exact hΦpfst ((0 : W), k') hk'
      have h2 : fderiv ℝ (fun k' : K₀ => Φ (γ k')) k = (fderiv ℝ Φ (γ k)).comp Dγ :=
        (hΦd.comp k hγd).fderiv
      rw [← h2, Filter.EventuallyEq.fderiv_eq h1]
      simp
    have hcomp_zero : ∀ v : K₀, (fderiv ℝ Φ (γ k)) (Dγ v) = 0 := by
      intro v
      have := congrArg (fun (T : K₀ →L[ℝ] W) => T v) hchain
      simpa [zero_apply] using this
    -- the projection of the kernel is onto
    have hTilfk : fderiv ℝ Til k = (ContinuousLinearMap.fst ℝ G Y).comp Dγ := by
      have hev : Til =ᶠ[𝓝 k] fun k' : K₀ => (γ k').1 :=
        Filter.eventually_of_mem (hO₁open.mem_nhds hkO₁) (fun k' hk' => hO₁sub hk')
      rw [Filter.EventuallyEq.fderiv_eq hev, hγd.fst.fderiv]
    rw [hTilfk] at hsurj
    have hproj_surj : Function.Surjective (fun z : (fderiv ℝ Φ (γ k)).ker => (z : G × Y).1) := by
      intro u
      obtain ⟨v, hv⟩ := hsurj u
      refine ⟨⟨Dγ v, LinearMap.mem_ker.mpr (hcomp_zero v)⟩, ?_⟩
      have : ((ContinuousLinearMap.fst ℝ G Y).comp Dγ) v = u := hv
      simpa [ContinuousLinearMap.comp_apply] using this
    have hsnd : Function.Surjective (fun v : Y => (fderiv ℝ Φ (γ k)) ((0 : G), v)) :=
      (surjective_snd_iff_surjective_projKer ((fderiv ℝ Φ (γ k)) : (G × Y) →ₗ[ℝ] W)
        (LinearMap.range_eq_top.mpr hsurjL)).mp hproj_surj
    -- convert to the slice derivative
    have hinrY : HasFDerivAt (fun y' : Y => ((γ k).1, y'))
        ((0 : Y →L[ℝ] G).prod (1 : Y →L[ℝ] Y)) (γ k).2 :=
      (hasFDerivAt_const (x := (γ k).2) (c := (γ k).1)).prodMk (hasFDerivAt_id (γ k).2)
    have hslice : Function.Surjective
        (fderiv ℝ (fun y' : Y => Φ ((γ k).1, y')) (γ k).2) := by
      have hd : fderiv ℝ (fun y' : Y => Φ ((γ k).1, y')) (γ k).2
          = (fderiv ℝ Φ (γ k)).comp ((0 : Y →L[ℝ] G).prod (1 : Y →L[ℝ] Y)) :=
        (hΦd.comp (γ k).2 hinrY).fderiv
      rw [hd]
      intro w
      obtain ⟨v, hv⟩ := hsnd w
      exact ⟨v, by simpa [ContinuousLinearMap.comp_apply] using hv⟩
    have h1 : (γ k).1 = p := by rw [← hzeq]
    have h2 : (γ k).2 = y := by rw [← hzeq]
    rw [h1, h2] at hslice
    exact hynsurj hslice
  refine ⟨k, ⟨hcrit, hkL⟩, ?_⟩
  show Til k = p
  rw [hO₁sub hkO₁, ← hzeq]

/-- **The local step of the slice-Sard lemma** (global form: smoothness and regularity everywhere). -/
theorem sliceSard_local {G Y W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hY : Module.finrank ℝ Y = Module.finrank ℝ W + 1)
    (Φ : G × Y → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hreg : ∀ z : G × Y, Φ z = 0 → Function.Surjective (fderiv ℝ Φ z))
    (z₀ : G × Y) (hz₀ : Φ z₀ = 0) :
    ∃ (U : Set (G × Y)) (Clo : Set G),
      IsOpen U ∧ z₀ ∈ U ∧ IsClosed Clo ∧ interior Clo = ∅ ∧
        {p : G | ∃ y : Y, (p, y) ∈ U ∧ Φ (p, y) = 0 ∧
          ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} ⊆ Clo := by
  obtain ⟨U, Clo, hUo, hzU, -, hCl, hCi, hsub⟩ :=
    sliceSard_local_core hY Φ hΦ isOpen_univ (fun z _ => hreg z) z₀ trivial hz₀
  exact ⟨U, Clo, hUo, hzU, hCl, hCi, hsub⟩

/-- **The local step of the slice-Sard lemma with the smoothness and the regularity hypothesis only on
an open set `Ω ×ˢ V`.**  This is the form in which a *charted* expression (smooth only where the
values lie in the chart) can be fed in, with `Ω` a set of parameters and `V` a set of variables. -/
theorem sliceSard_local_open {G Y W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hY : Module.finrank ℝ Y = Module.finrank ℝ W + 1)
    (Φ : G × Y → W) {Ω : Set G} (hΩ : IsOpen Ω) {V : Set Y} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (Ω ×ˢ V))
    (hreg : ∀ z : G × Y, z ∈ Ω ×ˢ V → Φ z = 0 → Function.Surjective (fderiv ℝ Φ z))
    (z₀ : G × Y) (hz₀V : z₀ ∈ Ω ×ˢ V) (hz₀ : Φ z₀ = 0) :
    ∃ (U : Set (G × Y)) (Clo : Set G),
      IsOpen U ∧ z₀ ∈ U ∧ U ⊆ Ω ×ˢ V ∧ IsClosed Clo ∧ interior Clo = ∅ ∧
        {p : G | ∃ y : Y, (p, y) ∈ U ∧ Φ (p, y) = 0 ∧
          ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} ⊆ Clo := by
  classical
  have hOΩ : IsOpen (Ω ×ˢ V) := hΩ.prod hV
  -- a globally smooth representative of the germ of `Φ` at `z₀`
  obtain ⟨Φt, hΦtsm, hΦteq⟩ := Work.Sard.exists_contDiff_eq_nhds_of_finiteDimensional Φ z₀
    (Ω ×ˢ V) (hOΩ.mem_nhds hz₀V) hΦ
  obtain ⟨W, hWsub, hWopen, hz₀W⟩ := mem_nhds_iff.mp hΦteq
  have hzt : Φt z₀ = 0 := by rw [hWsub hz₀W, hz₀]
  -- the regularity hypothesis for the representative, on `W ∩ (Ω × V)`
  have hregt : ∀ z : G × Y, z ∈ W ∩ (Ω ×ˢ V) → Φt z = 0 →
      Function.Surjective (fderiv ℝ Φt z) := by
    intro z hz hzt'
    have hΦz : Φ z = 0 := by rw [← hWsub hz.1]; exact hzt'
    have hev : Φt =ᶠ[𝓝 z] Φ :=
      Filter.eventually_of_mem (hWopen.mem_nhds hz.1) (fun z' hz' => hWsub hz')
    rw [Filter.EventuallyEq.fderiv_eq hev]
    exact hreg z hz.2 hΦz
  obtain ⟨U, Clo, hUo, hz₀U, hUV, hCl, hCi, hsub⟩ :=
    sliceSard_local_core hY Φt hΦtsm (hWopen.inter hOΩ) hregt z₀ ⟨hz₀W, hz₀V⟩ hzt
  refine ⟨U, Clo, hUo, hz₀U, fun x hx => (hUV hx).2, hCl, hCi, ?_⟩
  -- transfer the local statement from the representative `Φt` back to `Φ`
  rintro p ⟨y, hyU, hy0, hynsurj⟩
  have hxyW : ((p, y) : G × Y) ∈ W := (hUV hyU).1
  have hΦty : Φt ((p, y) : G × Y) = 0 := by rw [hWsub hxyW]; exact hy0
  refine hsub ⟨y, hyU, hΦty, fun hsurj => hynsurj ?_⟩
  have hev : Φt =ᶠ[𝓝 ((p, y) : G × Y)] Φ :=
    Filter.eventually_of_mem (hWopen.mem_nhds hxyW) (fun z' hz' => hWsub hz')
  have hev2 : (fun y' : Y => Φt ((p, y') : G × Y)) =ᶠ[𝓝 y]
      (fun y' : Y => Φ ((p, y') : G × Y)) :=
    hev.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto y)
  rw [Filter.EventuallyEq.fderiv_eq hev2] at hsurj
  exact hsurj

/-! ## 2. The global statement -/

theorem sliceSard_dense {G Y W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hY : Module.finrank ℝ Y = Module.finrank ℝ W + 1)
    (Φ : G × Y → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hreg : ∀ z : G × Y, Φ z = 0 → Function.Surjective (fderiv ℝ Φ z))
    (K : Set Y) (hK : IsCompact K) :
    Dense {p : G | ∀ y ∈ K, Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} := by
  classical
  set Bad : Set G := {p : G | ∃ y ∈ K, Φ (p, y) = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} with hBad
  have hgood : {p : G | ∀ y ∈ K, Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} = Badᶜ := by
    rw [hBad]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro h ⟨y, hyK, hy0, hysurj⟩
      exact hysurj (h y hyK hy0)
    · intro h y hyK hy0
      by_contra hysurj
      exact h ⟨y, hyK, hy0, hysurj⟩
  rw [hgood, dense_iff_closure_eq, closure_compl, eq_univ_iff_forall]
  -- ### the compact-set form of the local statement
  have hbad_inter : ∀ (p₀ : G) (R : ℝ), interior (Bad ∩ Metric.closedBall p₀ R) = ∅ := by
    intro p₀ R
    let ZK : Set (G × Y) := Φ ⁻¹' {0} ∩ (Metric.closedBall p₀ R ×ˢ K)
    have hZK : IsCompact ZK := by
      have h1 : IsCompact (Metric.closedBall p₀ R ×ˢ K) :=
        (isCompact_closedBall (x := p₀) (r := R)).prod hK
      exact h1.inter_left (isClosed_singleton.preimage hΦ.continuous)
    have hloc : ∀ z : ZK, ∃ (U : Set (G × Y)) (Clo : Set G), IsOpen U ∧ (z : G × Y) ∈ U ∧
        IsClosed Clo ∧ interior Clo = ∅ ∧
        {p : G | ∃ y : Y, (p, y) ∈ U ∧ Φ (p, y) = 0 ∧
          ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} ⊆ Clo :=
      fun z => sliceSard_local hY Φ hΦ hreg z.1 z.2.1
    choose U Clo hUo hzU hCloc hCli hCsub using hloc
    obtain ⟨t, ht⟩ := hZK.elim_finite_subcover U hUo
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩)
    have hsub : Bad ∩ Metric.closedBall p₀ R ⊆ ⋃ z ∈ t, Clo z := by
      rintro p ⟨⟨y, hyK, hy0, hynsurj⟩, hpball⟩
      have hzK : ((p, y) : G × Y) ∈ ZK := ⟨hy0, ⟨hpball, hyK⟩⟩
      obtain ⟨z, hzt, hzmem⟩ := Set.mem_iUnion₂.mp (ht hzK)
      exact Set.mem_iUnion₂.mpr ⟨z, hzt, hCsub z ⟨y, hzmem, hy0, hynsurj⟩⟩
    refine le_bot_iff.mp ((interior_mono hsub).trans (le_of_eq ?_))
    exact interior_biUnion_finset_eq_empty_of_isClosed t (fun z _ => hCloc z)
      (fun z _ => hCli z)
  -- ### no point is an interior point of `Bad`
  intro p₀ hmem
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hmem)
  have h1 : interior (Metric.closedBall p₀ (ε / 2))
      ⊆ interior (Bad ∩ Metric.closedBall p₀ (ε / 2)) :=
    interior_mono fun q hq =>
      ⟨hεsub (Metric.closedBall_subset_ball (by linarith) hq), hq⟩
  have h2 : p₀ ∈ interior (Metric.closedBall p₀ (ε / 2)) :=
    interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith))
  have h3 : p₀ ∈ interior (Bad ∩ Metric.closedBall p₀ (ε / 2)) := h1 h2
  rw [hbad_inter p₀ (ε / 2)] at h3
  simp at h3


/-! ## 3. The localised global statement

For a *charted* expression — smooth only on the set of parameters for which every value lies in the
chart — the global statement above is not directly applicable.  The following localised form is: it
assumes smoothness (and the regularity hypothesis) only on `Ω ×ˢ univ`, and concludes that the good
parameters are **dense in `Ω`**. -/

theorem sliceSard_dense_open {G Y W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hY : Module.finrank ℝ Y = Module.finrank ℝ W + 1)
    (Φ : G × Y → W) {Ω : Set G} (hΩ : IsOpen Ω) {V : Set Y} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (Ω ×ˢ V))
    (hreg : ∀ z : G × Y, z ∈ Ω ×ˢ V → Φ z = 0 → Function.Surjective (fderiv ℝ Φ z))
    (K : Set Y) (hK : IsCompact K) (hKV : K ⊆ V) :
    ∀ p₀ ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ p ∈ Ω, ‖p - p₀‖ < ε ∧
      (∀ y ∈ K, Φ (p, y) = 0 →
        Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)) := by
  classical
  let Bad : Set G := {p : G | ∃ y ∈ K, Φ (p, y) = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)}
  have hgood : {p : G | ∀ y ∈ K, Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} = Badᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro h ⟨y, hyK, hy0, hysurj⟩
      exact hysurj (h y hyK hy0)
    · intro h y hyK hy0
      by_contra hysurj
      exact h ⟨y, hyK, hy0, hysurj⟩
  intro p₀ hp₀ ε hε
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hp₀)
  have hRpos : 0 < min (ε / 2) (r / 2) := lt_min (by linarith) (by linarith)
  -- ## the interior of the bad set on the closed ball is empty
  have hbad : interior (Bad ∩ Metric.closedBall p₀ (min (ε / 2) (r / 2))) = ∅ := by
    let T : Set (G × Y) := Metric.closedBall p₀ (min (ε / 2) (r / 2)) ×ˢ K
    have hTcomp : IsCompact T :=
      (isCompact_closedBall (x := p₀) (r := min (ε / 2) (r / 2))).prod hK
    have hTsub : T ⊆ Ω ×ˢ V := fun z hz =>
      ⟨hrsub (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith : r / 2 < r)) hz.1), hKV hz.2⟩
    -- ## the local data at every point of `T`
    have hcov : ∀ z : T, ∃ (U : Set (G × Y)) (Clo : Set G), IsOpen U ∧ (z : G × Y) ∈ U ∧
        IsClosed Clo ∧ interior Clo = ∅ ∧
        {p : G | ∃ y : Y, (p, y) ∈ U ∩ {x : G × Y | Φ x = 0} ∧ Φ (p, y) = 0 ∧
          ¬ Function.Surjective (fderiv ℝ (fun y' : Y => Φ (p, y')) y)} ⊆ Clo := by
      intro z
      by_cases hz : Φ (z : G × Y) = 0
      · obtain ⟨U₀, Clo₀, hU₀o, hzU₀, -, hCl₀, hCi₀, hsub₀⟩ :=
          sliceSard_local_open hY Φ hΩ hV hΦ hreg (z : G × Y) (hTsub z.2) hz
        refine ⟨U₀, Clo₀, hU₀o, hzU₀, hCl₀, hCi₀, ?_⟩
        rintro p ⟨y, hy, hy0, hynsurj⟩
        exact hsub₀ ⟨y, hy.1, hy0, hynsurj⟩
      · have hcont : ContinuousAt Φ (z : G × Y) :=
          hΦ.continuousOn.continuousAt ((hΩ.prod hV).mem_nhds (hTsub z.2))
        have hmem : Φ ⁻¹' (({0} : Set W))ᶜ ∈ 𝓝 (z : G × Y) :=
          hcont (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hz))
        obtain ⟨U₁, hU₁sub, hU₁open, hzU₁⟩ := mem_nhds_iff.mp hmem
        refine ⟨U₁, ∅, hU₁open, hzU₁, isClosed_empty, interior_empty, ?_⟩
        rintro p ⟨y, hy, hy0, -⟩
        exact absurd hy.2 (by simpa using hU₁sub hy.1)
    choose U Clo hUo hzU hClo hCli hsub using hcov
    obtain ⟨t, ht⟩ := hTcomp.elim_finite_subcover U hUo
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩)
    have hsub2 : Bad ∩ Metric.closedBall p₀ (min (ε / 2) (r / 2)) ⊆ ⋃ z ∈ t, Clo z := by
      rintro p ⟨⟨y, hyK, hy0, hynsurj⟩, hpball⟩
      have hzT : ((p, y) : G × Y) ∈ T := ⟨hpball, hyK⟩
      obtain ⟨z, hzt, hzmem⟩ := Set.mem_iUnion₂.mp (ht hzT)
      exact Set.mem_iUnion₂.mpr ⟨z, hzt, hsub z ⟨y, ⟨hzmem, hy0⟩, hy0, hynsurj⟩⟩
    refine le_bot_iff.mp ((interior_mono hsub2).trans (le_of_eq ?_))
    exact interior_biUnion_finset_eq_empty_of_isClosed t (fun z _ => hClo z) (fun z _ => hCli z)
  -- ## a good parameter exists in the closed ball
  by_contra hcon
  have hsub3 : Metric.closedBall p₀ (min (ε / 2) (r / 2)) ⊆ Bad := by
    intro p hp
    have hpΩ : p ∈ Ω := hrsub (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith : r / 2 < r)) hp)
    have hlt : ‖p - p₀‖ < ε := by
      have h1 : dist p p₀ ≤ min (ε / 2) (r / 2) := Metric.mem_closedBall.mp hp
      rw [dist_eq_norm] at h1
      linarith [min_le_left (ε / 2) (r / 2)]
    by_contra hpb
    have hgoodp : p ∈ {q : G | ∀ y ∈ K, Φ (q, y) = 0 →
        Function.Surjective (fderiv ℝ (fun y' : Y => Φ (q, y')) y)} := by
      rw [hgood]; exact hpb
    exact hcon ⟨p, hpΩ, hlt, hgoodp⟩
  have hle : interior (Metric.closedBall p₀ (min (ε / 2) (r / 2)))
      ⊆ interior (Bad ∩ Metric.closedBall p₀ (min (ε / 2) (r / 2))) :=
    interior_mono fun p hp => ⟨hsub3 hp, hp⟩
  have h2 : p₀ ∈ interior (Metric.closedBall p₀ (min (ε / 2) (r / 2))) :=
    interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball (Metric.mem_ball_self hRpos)
  have h3 : p₀ ∈ interior (Bad ∩ Metric.closedBall p₀ (min (ε / 2) (r / 2))) := hle h2
  rw [hbad] at h3
  simp at h3

end Work.Drive
