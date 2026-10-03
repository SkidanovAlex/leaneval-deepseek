import Mathlib
import Submission.Work.Interfaces.HornParts

/-!
# Claim A of Shishikura Prop. 5.3: `Φ` is a covering map on discs avoiding the critical values

`HornPhiStatement` asserts that the Fatou coordinate `Φ₀` of a parabolic germ `f₀ ∈ 𝓕₀` is onto the
immediate basin `B` and admits a holomorphic local section through every point over every disc that
avoids the critical values `Φ₀ c - ℕ`.  This file turns those *local sections* into the covering
statement `IsCoveringMapOn (fun z : ↥B => d.Φ z) (ball y r)`.

The mathematical content is the standard "local sections + holomorphy ⇒ covering" argument:

* a local section `σ` of `Φ` over `V` has `deriv Φ (σ u) ≠ 0` (chain rule, `d.Φ ∘ σ = id`);
* hence `σ` is (locally) an open embedding, so every "sheet" `σ '' V` is open;
* two sections of `Φ` over a *preconnected* `V` that agree at one point agree everywhere
  (`AnalyticAt` + `deriv ≠ 0` gives local injectivity of `Φ`; the agreement set is clopen);
* therefore the sheets over `V` partition `f ⁻¹' V` into disjoint open sets
  homeomorphic to `V`;
* `IsOpen.trivializationDiscrete` + `IsEvenlyCovered.of_trivialization` then give the covering.
-/

namespace Work.HornCov

open Set Metric Complex Filter Topology
open scoped Topology

noncomputable section

/-! ## Elementary facts about the parabolic basin -/

theorem isOpen_parabolicBasin (f : ℂ → ℂ) (D : Set ℂ) : IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hunif⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine mem_of_superset (hVopen.mem_nhds hzV) fun y hy =>
    ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hunif.mono hVU⟩

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- A holomorphic section of the Fatou coordinate `Φ₀` over the open set `V`, with values in `B`. -/
structure IsPhiSection (d : MandelDim.ParabData f₀ D₀) (B V : Set ℂ) (σ : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ σ V
  mapsTo : MapsTo σ V B
  sec : ∀ u ∈ V, d.Φ (σ u) = u

theorem differentiableAt_Phi_of_mem {d : MandelDim.ParabData f₀ D₀} {B : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) {z : ℂ} (hz : z ∈ B) : DifferentiableAt ℂ d.Φ z :=
  d.Φ_holo.differentiableAt ((isOpen_parabolicBasin f₀ D₀).mem_nhds (hB hz))

theorem analyticAt_Phi_of_mem {d : MandelDim.ParabData f₀ D₀} {B : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) {z : ℂ} (hz : z ∈ B) : AnalyticAt ℂ d.Φ z :=
  d.Φ_holo.analyticAt ((isOpen_parabolicBasin f₀ D₀).mem_nhds (hB hz))

/-- The chain rule for a local section `σ` of `Φ` over an open set `V`: the inner derivative is
never zero. -/
theorem deriv_Phi_section_ne_zero {d : MandelDim.ParabData f₀ D₀} {B V : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) (hV : IsOpen V) {σ : ℂ → ℂ} (hσ : IsPhiSection d B V σ)
    {u : ℂ} (hu : u ∈ V) : deriv d.Φ (σ u) ≠ 0 := by
  have hdΦ : DifferentiableAt ℂ d.Φ (σ u) := differentiableAt_Phi_of_mem hB (hσ.mapsTo hu)
  have hdσ : DifferentiableAt ℂ σ u := hσ.diff.differentiableAt (hV.mem_nhds hu)
  have hchain : deriv (d.Φ ∘ σ) u = deriv d.Φ (σ u) * deriv σ u := deriv_comp u hdΦ hdσ
  have hev : (d.Φ ∘ σ) =ᶠ[𝓝 u] id := by
    filter_upwards [hV.mem_nhds hu] with w hw
    exact hσ.sec w hw
  have hone : deriv (d.Φ ∘ σ) u = 1 := by rw [hev.deriv_eq, deriv_id]
  rintro h0
  rw [hchain, h0, zero_mul] at hone
  exact one_ne_zero hone.symm

/-- The same chain rule for the section itself. -/
theorem deriv_section_ne_zero {d : MandelDim.ParabData f₀ D₀} {B V : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) (hV : IsOpen V) {σ : ℂ → ℂ} (hσ : IsPhiSection d B V σ)
    {u : ℂ} (hu : u ∈ V) : deriv σ u ≠ 0 := by
  have hdΦ : DifferentiableAt ℂ d.Φ (σ u) := differentiableAt_Phi_of_mem hB (hσ.mapsTo hu)
  have hdσ : DifferentiableAt ℂ σ u := hσ.diff.differentiableAt (hV.mem_nhds hu)
  have hchain : deriv (d.Φ ∘ σ) u = deriv d.Φ (σ u) * deriv σ u := deriv_comp u hdΦ hdσ
  have hev : (d.Φ ∘ σ) =ᶠ[𝓝 u] id := by
    filter_upwards [hV.mem_nhds hu] with w hw
    exact hσ.sec w hw
  have hone : deriv (d.Φ ∘ σ) u = 1 := by rw [hev.deriv_eq, deriv_id]
  rintro h0
  rw [hchain, h0, mul_zero] at hone
  exact one_ne_zero hone.symm

/-- `Φ` is locally injective at any point of `B` where its derivative does not vanish. -/
theorem exists_open_injOn_Phi {d : MandelDim.ParabData f₀ D₀} {B : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) {z : ℂ} (hz : z ∈ B) (hne : deriv d.Φ z ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U.InjOn d.Φ := by
  have hana : AnalyticAt ℂ d.Φ z := analyticAt_Phi_of_mem hB hz
  have hsf := hana.hasStrictDerivAt.hasStrictFDerivAt_equiv hne
  refine ⟨(hsf.toOpenPartialHomeomorph d.Φ).source,
    (hsf.toOpenPartialHomeomorph d.Φ).open_source,
    hsf.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro a ha b hb hab
  refine (hsf.toOpenPartialHomeomorph d.Φ).injOn ha hb ?_
  simpa only [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hab

/-- A local section of `Φ` over an open set has open image (holomorphic + nonzero derivative). -/
theorem isOpen_image_of_isPhiSection {d : MandelDim.ParabData f₀ D₀} {B V : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) (hV : IsOpen V) {σ : ℂ → ℂ} (hσ : IsPhiSection d B V σ) :
    IsOpen (σ '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨u₀, hu₀, rfl⟩
  have hne : deriv σ u₀ ≠ 0 := deriv_section_ne_zero hB hV hσ hu₀
  have hana : AnalyticAt ℂ σ u₀ := hσ.diff.analyticAt (hV.mem_nhds hu₀)
  have hsf := hana.hasStrictDerivAt.hasStrictFDerivAt_equiv hne
  set e := hsf.toOpenPartialHomeomorph σ with he
  have hmem : u₀ ∈ e.source := hsf.mem_toOpenPartialHomeomorph_source
  have hsopen : IsOpen (e.source ∩ V) := e.open_source.inter hV
  have himg : IsOpen (e '' (e.source ∩ V)) :=
    (e.isOpen_image_iff_of_subset_source inter_subset_left).mpr hsopen
  have hzmem : σ u₀ ∈ e '' (e.source ∩ V) := ⟨u₀, ⟨hmem, hu₀⟩, rfl⟩
  exact mem_of_superset (himg.mem_nhds hzmem) (image_mono inter_subset_right)

/-- **Uniqueness of local sections of `Φ` over a preconnected open set.** Two holomorphic sections
that agree at one point agree everywhere. -/
theorem eq_of_isPhiSection_eq {d : MandelDim.ParabData f₀ D₀} {B V : Set ℂ}
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) (hV : IsOpen V) (hVc : IsPreconnected V)
    {σ σ' : ℂ → ℂ} (hσ : IsPhiSection d B V σ) (hσ' : IsPhiSection d B V σ')
    {u₀ : ℂ} (hu₀ : u₀ ∈ V) (hag : σ u₀ = σ' u₀) : ∀ u ∈ V, σ u = σ' u := by
  haveI : PreconnectedSpace ↥V := Subtype.preconnectedSpace hVc
  let A : Set ↥V := {u | (V.domRestrict σ) u = (V.domRestrict σ') u}
  have hcontσ : Continuous (V.domRestrict σ) := hσ.diff.continuousOn.domRestrict
  have hcontσ' : Continuous (V.domRestrict σ') := hσ'.diff.continuousOn.domRestrict
  have hAclosed : IsClosed A := isClosed_eq hcontσ hcontσ'
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    have hzu : (V.domRestrict σ) u = (V.domRestrict σ') u := hu
    have hne := deriv_Phi_section_ne_zero hB hV hσ u.2
    obtain ⟨U, hUopen, hzU, hUinj⟩ := exists_open_injOn_Phi hB (hσ.mapsTo u.2) hne
    have hU2 : (V.domRestrict σ') u ∈ U := by rw [← hzu]; exact hzU
    refine mem_of_superset
      (Filter.inter_mem (hcontσ.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hzU))
        (hcontσ'.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hU2))) ?_
    intro w hw
    exact hUinj hw.1 hw.2 (by simp only [Set.domRestrict]; rw [hσ.sec w.1 w.2, hσ'.sec w.1 w.2])
  rcases isClopen_iff.mp (⟨hAclosed, hAopen⟩ : IsClopen A) with h | h
  · have hne : A.Nonempty := ⟨⟨u₀, hu₀⟩, by show σ u₀ = σ' u₀; exact hag⟩
    rw [h] at hne
    exact absurd hne Set.not_nonempty_empty
  · intro u hu
    have : (⟨u, hu⟩ : ↥V) ∈ A := by rw [h]; exact Set.mem_univ _
    exact this


/-- **From local sections to a covering map.** Let `B` be the immediate basin of `f₀ ∈ 𝓕₀` and
`d` its §4.1 data. If `V` is open, preconnected with `y ∈ V`, the map `Φ₀` is onto, and every point
`z ∈ B` with `Φ₀ z ∈ V` lies on a holomorphic local section of `Φ₀` over `V`, then `Φ₀ : B → ℂ` is
a covering map over `V`. -/
theorem covering_of_sections {B : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀) {V : Set ℂ} (hV : IsOpen V) (hVc : IsPreconnected V)
    (y : ℂ) (hyV : y ∈ V) (hsurjy : ∃ z : ↥B, d.Φ z = y)
    (hsec : ∀ z : ↥B, d.Φ z ∈ V → ∃ σ : ℂ → ℂ, IsPhiSection d B V σ ∧ σ (d.Φ z) = z) :
    IsCoveringMapOn (fun z : ↥B => d.Φ z) V := by
  classical
  have hfcont : Continuous (fun z : ↥B => d.Φ z) :=
    (d.Φ_holo.mono hB).continuousOn.domRestrict
  haveI hEne : Nonempty (ℂ → ↥B) := ⟨fun _ => hsurjy.choose⟩
  let ι : Type := {w : ↥B // d.Φ w = y}
  haveI hιne : Nonempty ι := ⟨⟨hsurjy.choose, hsurjy.choose_spec⟩⟩
  have hex : ∀ w : ι, ∃ σ : ℂ → ℂ, IsPhiSection d B V σ ∧ σ y = w.1 := by
    intro w
    have hwV : d.Φ w.1 ∈ V := Eq.mpr (congrArg (fun z => z ∈ V) w.2) hyV
    obtain ⟨σ, hσ, hσz⟩ := hsec w.1 hwV
    exact ⟨σ, hσ, (congrArg σ w.2.symm).trans hσz⟩
  let σi : ι → ℂ → ℂ := fun w => Classical.choose (hex w)
  have σi_spec : ∀ w : ι, IsPhiSection d B V (σi w) ∧ σi w y = w.1 := fun w =>
    Classical.choose_spec (hex w)
  let U : ι → Set ↥B := fun w => {z | ∃ u ∈ V, σi w u = (z : ℂ)}
  have hUopen : ∀ w : ι, IsOpen (U w) := by
    intro w
    have himg : IsOpen (σi w '' V) := isOpen_image_of_isPhiSection hB hV (σi_spec w).1
    have hset : U w = Subtype.val ⁻¹' (σi w '' V) := by
      ext z
      exact Iff.rfl
    rw [hset]
    exact himg.preimage continuous_subtype_val
  have h_openiff : ∀ w : ι, ∀ {W : Set ℂ}, W ⊆ V →
      (IsOpen W ↔ IsOpen ((fun z : ↥B => d.Φ z) ⁻¹' W ∩ U w)) := by
    intro w W hWV
    constructor
    · intro hW
      exact (hfcont.isOpen_preimage W hW).inter (hUopen w)
    · intro hWU
      let g : ↥V → ↥B := fun u => ⟨σi w u.1, (σi_spec w).1.mapsTo u.2⟩
      have hgcont : Continuous g :=
        ((σi_spec w).1.diff.continuousOn.domRestrict).subtype_mk
          (fun u => (σi_spec w).1.mapsTo u.2)
      have hgf : ∀ u : ↥V, (fun z : ↥B => d.Φ z) (g u) = (u : ℂ) := fun u =>
        (σi_spec w).1.sec u.1 u.2
      have hgU : ∀ u : ↥V, g u ∈ U w := fun u => ⟨u.1, u.2, rfl⟩
      have hA : IsOpen (g ⁻¹' ((fun z : ↥B => d.Φ z) ⁻¹' W ∩ U w)) :=
        hgcont.isOpen_preimage _ hWU
      have hWeq : W = Subtype.val '' (g ⁻¹' ((fun z : ↥B => d.Φ z) ⁻¹' W ∩ U w)) := by
        ext x
        constructor
        · intro hx
          refine ⟨⟨x, hWV hx⟩, ⟨?_, hgU ⟨x, hWV hx⟩⟩, rfl⟩
          show (fun z : ↥B => d.Φ z) (g ⟨x, hWV hx⟩) ∈ W
          rw [hgf ⟨x, hWV hx⟩]
          exact hx
        · rintro ⟨u, hu, rfl⟩
          rw [← hgf u]
          exact hu.1
      rw [hWeq]
      obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hA
      rw [← hOeq, Set.image_preimage_eq_inter_range, Subtype.range_coe]
      exact hOopen.inter hV
  have h_inj : ∀ w : ι, Set.InjOn (fun z : ↥B => d.Φ z) (U w) := by
    intro w z hz z' hz' heq
    obtain ⟨u, hu, hzu⟩ := hz
    obtain ⟨u', hu', hzu'⟩ := hz'
    have h1 : d.Φ (σi w u) = u := (σi_spec w).1.sec u hu
    have h2 : d.Φ (σi w u') = u' := (σi_spec w).1.sec u' hu'
    have heq' : d.Φ (z : ℂ) = d.Φ (z' : ℂ) := heq
    have huu : u = u' := by rw [← h1, hzu, heq', ← hzu', h2]
    exact Subtype.ext (by rw [← hzu, ← hzu', huu])
  have h_surj : ∀ w : ι, Set.SurjOn (fun z : ↥B => d.Φ z) (U w) V := by
    intro w u hu
    exact ⟨⟨σi w u, (σi_spec w).1.mapsTo hu⟩, ⟨u, hu, rfl⟩, (σi_spec w).1.sec u hu⟩
  have h_disj : Pairwise (Function.onFun Disjoint U) := by
    intro w w' hne
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hz, hz'⟩ := hz
    obtain ⟨u, hu, hzu⟩ := hz
    obtain ⟨u', hu', hzu'⟩ := hz'
    have h1 : d.Φ (σi w u) = u := (σi_spec w).1.sec u hu
    have h2 : d.Φ (σi w' u') = u' := (σi_spec w').1.sec u' hu'
    have huu : u = u' := by rw [← h1, hzu, ← hzu', h2]
    have hag : σi w u = σi w' u := by rw [hzu, ← hzu', huu]
    have hfun : ∀ u ∈ V, σi w u = σi w' u :=
      eq_of_isPhiSection_eq hB hV hVc (σi_spec w).1 (σi_spec w').1 hu hag
    exact hne (Subtype.ext (Subtype.ext
      (by rw [← (σi_spec w).2, hfun y hyV, (σi_spec w').2])))
  have h_exh : (fun z : ↥B => d.Φ z) ⁻¹' V ⊆ ⋃ w, U w := by
    intro z hz
    obtain ⟨σz, hσz, hσzy⟩ := hsec z hz
    have hmem : σz y ∈ B := hσz.mapsTo hyV
    have hΦ : d.Φ (σz y) = y := hσz.sec y hyV
    refine Set.mem_iUnion.mpr ⟨⟨⟨σz y, hmem⟩, hΦ⟩, ?_⟩
    have hw1 : IsPhiSection d B V (σi ⟨⟨σz y, hmem⟩, hΦ⟩) := (σi_spec _).1
    have hag : σi ⟨⟨σz y, hmem⟩, hΦ⟩ y = σz y := by
      rw [(σi_spec ⟨⟨σz y, hmem⟩, hΦ⟩).2]
    have hfun := eq_of_isPhiSection_eq hB hV hVc hw1 hσz hyV hag
    exact ⟨d.Φ z, hz, by rw [hfun (d.Φ z) hz]; exact hσzy⟩
  haveI hιdisc : DiscreteTopology ι := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro w
    have hne : deriv d.Φ (w.1 : ℂ) ≠ 0 := by
      have h := deriv_Phi_section_ne_zero hB hV (σi_spec w).1 hyV
      rw [show σi w y = (w.1 : ℂ) from (σi_spec w).2] at h
      exact h
    obtain ⟨O, hOopen, hzO, hOinj⟩ := exists_open_injOn_Phi hB w.1.2 hne
    have hset : ({w} : Set ι) = Subtype.val ⁻¹' (Subtype.val ⁻¹' O) := by
      ext v
      rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_preimage]
      constructor
      · intro hv
        rw [hv]
        exact hzO
      · intro hv
        have h1 : (v.1 : ℂ) = (w.1 : ℂ) := hOinj hv hzO (by rw [v.2, w.2])
        exact Subtype.ext (Subtype.ext h1)
    rw [hset]
    exact (continuous_subtype_val : Continuous (Subtype.val : ι → ↥B)).isOpen_preimage _
      ((continuous_subtype_val : Continuous (Subtype.val : ↥B → ℂ)).isOpen_preimage _ hOopen)
  intro x hx
  have hxbase : x ∈ (IsOpen.trivializationDiscrete (f := fun z : ↥B => d.Φ z) U V hV h_openiff
      h_inj h_surj h_disj h_exh).baseSet := by
    rw [IsOpen.trivializationDiscrete_baseSet (f := fun z : ↥B => d.Φ z) U V hV h_openiff h_inj
      h_surj h_disj h_exh]
    exact hx
  exact (IsEvenlyCovered.of_trivialization hxbase).to_isEvenlyCovered_preimage

/-- **Claim A (Shishikura, Prop. 5.3) implies that `Φ₀` is a covering map on discs avoiding the
critical values `Φ₀ c - ℕ`.** -/
theorem sheet_Phi (hPhi : MandelDim.HornPhiStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) (y : ℂ)
    (hy : ∀ k : ℕ, y ≠ d.Φ c - k) :
    ∃ r : ℝ, 0 < r ∧ IsCoveringMapOn (fun z : ↥B => d.Φ z) (Metric.ball y r) := by
  classical
  obtain ⟨hsurj, hsecstmt⟩ := hPhi f₀ D₀ B c d hsetup
  obtain ⟨r, hr, hsec⟩ := hsecstmt y hy
  have hB : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  refine ⟨r, hr, covering_of_sections d hB Metric.isOpen_ball (convex_ball y r).isPreconnected
    y (Metric.mem_ball_self hr) ?_ ?_⟩
  · obtain ⟨z, hzB, hzy⟩ := hsurj y
    exact ⟨⟨z, hzB⟩, hzy⟩
  · intro z hz
    obtain ⟨σ, h1, h2, h3, h4⟩ := hsec z.1 z.2 hz
    exact ⟨σ, ⟨h1, h2, h3⟩, h4⟩

end

end Work.HornCov
