import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Topology.Metric.exists_pairwiseDisjoint_ball_subset

open Set Filter Metric
open scoped Topology

namespace Commons.Analysis.Complex

/-- A continuous function that is nowhere zero on a compact set is bounded below in norm by a
positive constant. -/
private theorem exists_pos_le_norm_of_isCompact_ne_zero {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] {K : Set X} (hK : IsCompact K) {g : X → E}
    (hg : ContinuousOn g K) (hne : ∀ x ∈ K, g x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖g x‖ := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn h hg.norm
    exact ⟨‖g x₀‖, norm_pos_iff.mpr (hne x₀ hx₀), fun x hx => hmin hx⟩

/-- At a point where an analytic function takes the value `w₀` with non-vanishing derivative,
the function is injective on some open neighbourhood of that point and is a local
homeomorphism there. -/
private theorem exists_open_injOn_of_analyticAt_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hder : deriv f z ≠ 0) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ), (e : ℂ → ℂ) = f ∧ z ∈ e.source ∧ InjOn f e.source := by
  have hd : deriv f z ≠ 0 := hder
  refine ⟨(hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph f,
    ?_, ?_, ?_⟩
  · exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  · exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  · have := (HasStrictFDerivAt.toOpenPartialHomeomorph f
      (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)).injOn
    simpa using this

/-- The set of points of `U` mapping to `w₀` is finite, under the standing hypotheses: `closure U`
is compact, `f` is continuous there and analytic on `U`, `w₀` is not attained on the frontier, and
every preimage of `w₀` in `U` is a simple zero. -/
private theorem finite_preimage_of_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsCompact (closure U)) {f : ℂ → ℂ} (hfc : ContinuousOn f (closure U))
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z)
    {w₀ : ℂ} (hno : w₀ ∉ f '' frontier U)
    (hder : ∀ z ∈ U, f z = w₀ → deriv f z ≠ 0) :
    (f ⁻¹' {w₀} ∩ U).Finite := by
  have hZeq : f ⁻¹' {w₀} ∩ closure U = f ⁻¹' {w₀} ∩ U := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨hxw, hxU⟩ := hx
      refine ⟨hxw, ?_⟩
      by_contra hxc
      have : x ∈ frontier U := by
        rw [frontier, hUo.interior_eq]; exact ⟨hxU, hxc⟩
      exact hno ⟨x, this, hxw⟩
    · intro x hx; exact ⟨hx.1, subset_closure hx.2⟩
  have hZfinite : (f ⁻¹' {w₀} ∩ closure U).Finite := by
    have hclosed : IsClosed (f ⁻¹' {w₀} ∩ closure U) := by
      rw [inter_comm]
      exact hfc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
    have hcompact : IsCompact (f ⁻¹' {w₀} ∩ closure U) :=
      hUc.of_isClosed_subset hclosed inter_subset_right
    refine hcompact.finite ?_
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    have hzw : f z = w₀ := hz.1
    have hzcl : z ∈ closure U := hz.2
    have hzU : z ∈ U := by
      by_contra hc
      have : z ∈ frontier U := by
        rw [frontier, hUo.interior_eq]; exact ⟨hzcl, hc⟩
      exact hno ⟨z, this, hzw⟩
    obtain ⟨e, hef, hzes, hinj⟩ :=
      exists_open_injOn_of_analyticAt_deriv_ne_zero (hf z hzU) (hder z hzU hzw)
    refine ⟨e.source, e.open_source, ?_⟩
    apply Subset.antisymm
    · intro y hy
      obtain ⟨hyes, hyw, -⟩ := hy
      have : f y = f z := by rw [hyw, hzw]
      have := hinj hyes hzes this
      simp [this]
    · intro y hy
      have hyz : y = z := by simpa using hy
      subst hyz
      exact ⟨hzes, hz⟩
  rwa [hZeq] at hZfinite

theorem eventually_ncard_preimage_eq_of_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsCompact (closure U)) {f : ℂ → ℂ} (hfc : ContinuousOn f (closure U))
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z)
    {w₀ : ℂ} (hno : w₀ ∉ f '' frontier U)
    (hder : ∀ z ∈ U, f z = w₀ → deriv f z ≠ 0) :
    Filter.Eventually (fun w : ℂ => (f ⁻¹' {w} ∩ U).ncard = (f ⁻¹' {w₀} ∩ U).ncard)
      (nhds w₀) := by
  classical
  set Z : Set ℂ := f ⁻¹' {w₀} ∩ U with hZdef
  have hZfin : Z.Finite := finite_preimage_of_deriv_ne_zero hUo hUc hfc hf hno hder
  have hzU : ∀ z : Z, (z : ℂ) ∈ U := fun z => z.2.2
  have hzw : ∀ z : Z, f z = w₀ := fun z => by simpa using z.2.1
  have hloc : ∀ z : Z, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = f ∧ (z : ℂ) ∈ e.source ∧ InjOn f e.source := fun z =>
    exists_open_injOn_of_analyticAt_deriv_ne_zero (hf z (hzU z)) (hder z (hzU z) (hzw z))
  let efun : Z → OpenPartialHomeomorph ℂ ℂ := fun z => Classical.choose (hloc z)
  have hefun : ∀ z, (efun z : ℂ → ℂ) = f ∧ (z:ℂ) ∈ (efun z).source ∧ InjOn f (efun z).source :=
    fun z => Classical.choose_spec (hloc z)
  let O : Z → Set ℂ := fun z => (efun z).source ∩ U
  have hOopen : ∀ z, IsOpen (O z) := fun z => (efun z).open_source.inter hUo
  have hOmem : ∀ z, (z:ℂ) ∈ O z := fun z => ⟨(hefun z).2.1, hzU z⟩
  have hOsub : ∀ z, O z ⊆ U := fun z => inter_subset_right
  have hOinj : ∀ z, InjOn f (O z) := fun z => (hefun z).2.2.mono inter_subset_left
  obtain ⟨r, hrpos, hrsub, hrdisj⟩ :=
    Commons.Topology.Metric.exists_pairwiseDisjoint_ball_subset hZfin O hOopen hOmem
  let K : Set ℂ := closure U ∩ (⋃ z : Z, ball (z:ℂ) (r z))ᶜ
  have hKclosed : IsClosed K := by
    refine isClosed_closure.inter ?_
    rw [isClosed_compl_iff]
    exact isOpen_iUnion (fun z => isOpen_ball)
  have hKsub : K ⊆ closure U := inter_subset_left
  have hKcompact : IsCompact K := hUc.of_isClosed_subset hKclosed hKsub
  let g : ℂ → ℂ := fun y => f y - w₀
  have hgne : ∀ y ∈ K, g y ≠ 0 := by
    intro y hy h0
    change f y - w₀ = 0 at h0
    have hycl : y ∈ closure U := hy.1
    have hynot : y ∉ ⋃ z : Z, ball (z:ℂ) (r z) := hy.2
    have hyU : y ∈ U := by
      by_contra hc
      have : y ∈ frontier U := by rw [frontier, hUo.interior_eq]; exact ⟨hycl, hc⟩
      exact hno ⟨y, this, sub_eq_zero.mp h0⟩
    have hyZ : y ∈ Z := by
      rw [hZdef]; exact ⟨by simpa using sub_eq_zero.mp h0, hyU⟩
    refine hynot (mem_iUnion.mpr ⟨⟨y, hyZ⟩, ?_⟩)
    exact Metric.mem_ball_self (hrpos ⟨y, hyZ⟩)
  have hgcont : ContinuousOn g K := (hfc.mono hKsub).sub continuousOn_const
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_norm_of_isCompact_ne_zero hKcompact hgcont hgne
  let W : Set ℂ := ⋂ z : Z, f '' ball (z:ℂ) (r z)
  have hWnhds : W ∈ 𝓝 w₀ := by
    have : Finite Z := hZfin.to_subtype
    have hWeq : W = ⋂ z : Z, f '' ball (z:ℂ) (r z) := rfl
    rw [hWeq, Filter.iInter_mem]
    intro z
    have hballnhds : ball (z:ℂ) (r z) ∈ 𝓝 (z:ℂ) := Metric.ball_mem_nhds _ (hrpos z)
    have h := (efun z).image_mem_nhds (hefun z).2.1 hballnhds
    rw [(hefun z).1] at h
    rwa [hzw z] at h
  have hmain : ∀ w ∈ W, dist w₀ w < δ → (f ⁻¹' {w} ∩ U).ncard = Z.ncard := by
    intro w hwW hwd
    rw [dist_eq_norm, norm_sub_rev] at hwd
    have hball : ∀ z : Z, ∃ p, p ∈ ball (z:ℂ) (r z) ∧ f p = w := fun z => by
      have h := Set.mem_iInter.mp (show w ∈ ⋂ z : Z, f '' ball (z:ℂ) (r z) from hwW) z
      rwa [mem_image] at h
    let φ : Z → (f ⁻¹' {w} ∩ U : Set ℂ) := fun z =>
      ⟨Classical.choose (hball z), by
        obtain ⟨hmem, hfw⟩ := Classical.choose_spec (hball z)
        refine ⟨by simpa using hfw, ?_⟩
        exact hOsub z ((hrsub z) hmem)⟩
    have hφinj : Function.Injective φ := by
      intro z z' hzz
      by_contra hne
      have hy : (φ z : ℂ) = (φ z') := by rw [hzz]
      have hzmem : (φ z : ℂ) ∈ ball (z:ℂ) (r z) := (Classical.choose_spec (hball z)).1
      have hz'mem : (φ z' : ℂ) ∈ ball (z':ℂ) (r z') := (Classical.choose_spec (hball z')).1
      rw [hy] at hzmem
      exact (Set.disjoint_left.mp (hrdisj z z' hne) hzmem) hz'mem
    have hφsurj : Function.Surjective φ := by
      intro p
      have hpU : (p:ℂ) ∈ U := p.2.2
      have hpw : f (p:ℂ) = w := by simpa using p.2.1
      have hpmem : (p:ℂ) ∈ ⋃ z : Z, ball (z:ℂ) (r z) := by
        by_contra hnot
        have hpK : (p:ℂ) ∈ K := by
          change (p:ℂ) ∈ closure U ∩ (⋃ z : Z, ball (z:ℂ) (r z))ᶜ
          exact ⟨subset_closure hpU, hnot⟩
        have hle := hδ (p:ℂ) hpK
        change δ ≤ ‖f (p:ℂ) - w₀‖ at hle
        rw [hpw] at hle
        exact absurd hle (not_le.mpr hwd)
      obtain ⟨z, hz⟩ := mem_iUnion.mp hpmem
      refine ⟨z, Subtype.ext ?_⟩
      have h1 : f (p:ℂ) = f (φ z : ℂ) := by
        rw [hpw]
        exact ((Classical.choose_spec (hball z)).2).symm
      have h2 : (p:ℂ) ∈ ball (z:ℂ) (r z) := hz
      have h3 : (φ z : ℂ) ∈ ball (z:ℂ) (r z) := (Classical.choose_spec (hball z)).1
      exact (hOinj z ((hrsub z) h2) ((hrsub z) h3) h1).symm
    let e : Z ≃ (f ⁻¹' {w} ∩ U : Set ℂ) := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
    exact (Set.ncard_congr' e).symm
  filter_upwards [hWnhds, ball_mem_nhds w₀ hδpos] with w hwW hwd
  simp only [mem_ball] at hwd
  have hwd' : dist w₀ w < δ := by rw [dist_comm]; exact hwd
  rw [hmain w hwW hwd', hZdef]

end Commons.Analysis.Complex