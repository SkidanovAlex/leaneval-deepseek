import Mathlib
import Submission.Work.Sard.wp.Defs
import Submission.Work.Sard.holder_two_fderiv_eq_zero
import Submission.Work.Sard.weakSardGlobalOne
import Submission.Work.Sard.exists_contDiff_eq_nhds_of_hasBump
import Submission.Work.Sard.weakSardNonflatGlobal

set_option autoImplicit false

namespace Work.Sard.prod

open scoped ContDiff Topology NNReal ENNReal
open Filter Set Metric

/-- **Surjectivity is open** for continuous linear maps into a finite dimensional space. -/
theorem isOpen_setOf_surjective_clm' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective (L₀ : E →ₗ[ℝ] F)
    (LinearMap.range_eq_top.mpr hL₀)
  have hRcont : Continuous R := LinearMap.continuous_of_finiteDimensional R
  let R' : F →L[ℝ] E := ⟨R, hRcont⟩
  have hR'coe : (R' : F → E) = R := rfl
  have hR' : L₀.comp R' = ContinuousLinearMap.id ℝ F := by
    ext x
    rw [ContinuousLinearMap.comp_apply, hR'coe, ContinuousLinearMap.id_apply]
    exact DFunLike.congr_fun hR x
  have hcont : Continuous fun L : E →L[ℝ] F => L.comp R' := by
    have h1 : Continuous fun L : E →L[ℝ] F =>
        ((ContinuousLinearMap.compL ℝ F E F) L) R' :=
      (ContinuousLinearMap.compL ℝ F E F).continuous.clm_apply continuous_const
    simpa [ContinuousLinearMap.compL_apply] using h1
  have hnbhd : {L : E →L[ℝ] F | ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ < 1} ∈ 𝓝 L₀ := by
    have hc : Continuous fun L : E →L[ℝ] F => ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ :=
      (hcont.sub continuous_const).norm
    refine (isOpen_lt hc (continuous_const : Continuous fun _ : E →L[ℝ] F => (1 : ℝ))).mem_nhds ?_
    show ‖L₀.comp R' - ContinuousLinearMap.id ℝ F‖ < 1
    rw [hR', sub_self, norm_zero]
    norm_num
  refine Filter.mem_of_superset hnbhd ?_
  intro L hL
  have hunit : IsUnit (L.comp R') := by
    have hsplit : L.comp R' = ContinuousLinearMap.id ℝ F -
        (ContinuousLinearMap.id ℝ F - L.comp R') := by abel
    rw [hsplit]
    exact isUnit_one_sub_of_norm_lt_one (by simpa [norm_sub_rev] using hL)
  have hbij : Function.Bijective (L.comp R') :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  intro y
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨R' x, hx⟩

/-- The non-surjective continuous linear maps form a closed set. -/
theorem isClosed_setOf_not_surjective_clm' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsClosed {L : E →L[ℝ] F | ¬ Function.Surjective L} := by
  have h : {L : E →L[ℝ] F | ¬ Function.Surjective L}
      = {L : E →L[ℝ] F | Function.Surjective L}ᶜ := by
    ext L; simp
  rw [h]
  exact isOpen_setOf_surjective_clm'.isClosed_compl

/-- The zero map is not surjective if the target has a nonzero vector. -/
theorem not_surjective_zero_of_nontrivial {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F] :
    ¬ Function.Surjective (0 : E →L[ℝ] F) := by
  intro h
  obtain ⟨y, hy⟩ : ∃ y : F, y ≠ 0 := exists_ne 0
  obtain ⟨x, hx⟩ := h y
  simp at hx
  exact hy hx.symm

/-- If `F` has dimension one then `F` is nontrivial. -/
theorem nontrivial_of_finrank_eq_one {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = 1) : Nontrivial F := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  haveI := hsub
  have h0 : Module.finrank ℝ F = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- **Empty interior from a Hausdorff dimension bound.** -/
theorem interior_eq_empty_of_dimH_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set F} (h : dimH S < (Module.finrank ℝ F : ℝ≥0∞)) :
    interior S = ∅ := by
  by_contra hne
  have hne' : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  rw [Real.dimH_of_nonempty_interior hne'] at h
  exact lt_irrefl _ h

/-- **Hölder maps with small dimensional image have empty-interior image.** -/
theorem interior_image_eq_empty_of_holder_dimH {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (S : Set E) (r : ℕ) (hr : 0 < r)
    (hH : ∀ x ∈ S, ∃ C : NNReal, ∃ t ∈ 𝓝[S] x, HolderOnWith C (r : ℝ≥0) f t)
    (hdim : dimH S / (r : ℝ≥0∞) < (Module.finrank ℝ F : ℝ≥0∞)) :
    interior (f '' S) = ∅ := by
  refine interior_eq_empty_of_dimH_lt ?_
  have hr0 : (0 : ℝ≥0) < (r : ℝ≥0) := by exact_mod_cast hr
  exact lt_of_le_of_lt (dimH_image_le_of_locally_holder_on hr0 hH) hdim


/-- **The flat stratum, `m ≥ 2`.**  For a globally smooth map with `finrank ℝ F = m ≥ 2` the image of the
set of points where the derivative vanishes has empty interior.  Indeed the map is `2`-Hölder on that
set (`Work.Sard.holder_two_fderiv_eq_zero`) and the set has Hausdorff dimension at most `m + 1`, so the
image has Hausdorff dimension at most `(m+1)/2 < m`. -/
theorem flat_image_interior_empty_of_two_le' {m : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hm : 2 ≤ m) (hE : Module.finrank ℝ E = m + 1)
    (hF : Module.finrank ℝ F = m) (ρ : E → F) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    interior (ρ '' {z : E | fderiv ℝ ρ z = 0}) = ∅ := by
  refine interior_image_eq_empty_of_holder_dimH ρ {z : E | fderiv ℝ ρ z = 0} 2 (by norm_num) ?_ ?_
  · intro x hx
    have h := Work.Sard.holder_two_fderiv_eq_zero ρ hρ (Set.univ : Set E) x (by simpa using hx)
    simpa [Set.inter_univ] using h
  · have hS : dimH {z : E | fderiv ℝ ρ z = 0} ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) :=
      le_trans (dimH_mono (Set.subset_univ _)) (le_of_eq (Real.dimH_univ_eq_finrank E))
    have hlt : (((m + 1 : ℕ) : ℝ≥0∞)) / 2 < ((m : ℕ) : ℝ≥0∞) := by
      have hlt_nn : (((m + 1 : ℕ) : ℝ≥0)) / 2 < ((m : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
        have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have harg : (((m : ℝ) + 1)) / 2 < (m : ℝ) := by linarith
        simpa using harg
      rw [← ENNReal.coe_natCast (m + 1), ← ENNReal.coe_natCast m, ← ENNReal.coe_ofNat,
        ← ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
      exact ENNReal.coe_lt_coe.mpr hlt_nn
    calc dimH {z : E | fderiv ℝ ρ z = 0} / (2 : ℝ≥0∞)
        ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) / 2 := ENNReal.div_le_div_right hS 2
      _ = (((m + 1 : ℕ) : ℝ≥0∞)) / 2 := by rw [hE]
      _ < ((Module.finrank ℝ F : ℕ) : ℝ≥0∞) := by rw [hF]; exact hlt


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- If the complement of `S` is "open at every point of `K`", then `K ∩ S` is compact as soon as `K` is. -/
lemma isCompact_inter_of_eventually_not {S K : Set E} (hK : IsCompact K)
    (h : ∀ z ∈ K, z ∉ S → ∀ᶠ w in 𝓝 z, w ∉ S) : IsCompact (K ∩ S) := by
  have hsub : K ∩ S = K ∩ closure S := by
    ext z
    constructor
    · intro hz; exact ⟨hz.1, subset_closure hz.2⟩
    · intro hz
      refine ⟨hz.1, ?_⟩
      by_contra hzS
      have hmem : {w | w ∉ S} ∈ 𝓝 z := h z hz.1 hzS
      have hne : ({w | w ∉ S} ∩ S).Nonempty :=
        mem_closure_iff_nhds.mp hz.2 {w | w ∉ S} hmem
      obtain ⟨w, hw1, hw2⟩ := hne
      exact hw1 hw2
  rw [hsub]
  exact hK.inter_right isClosed_closure

/-- The derivative is continuous at points of `U`. -/
lemma continuousAt_fderiv_of_contDiffOn {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {z : E} (hz : z ∈ U) :
    ContinuousAt (fun z : E => fderiv ℝ ρ z) z :=
  (hρ.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hz)

/-- The flat set meets a compact subset of `U` in a compact set. -/
lemma isCompact_inter_flat {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) : IsCompact (K ∩ {z : E | fderiv ℝ ρ z = 0}) := by
  refine isCompact_inter_of_eventually_not hK ?_
  intro z hzK hzS
  exact (continuousAt_fderiv_of_contDiffOn hU ρ hρ (hKU hzK)).eventually_ne hzS

/-- The critical set meets a compact subset of `U` in a compact set. -/
lemma isCompact_inter_crit {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) : IsCompact (K ∩ {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)}) := by
  refine isCompact_inter_of_eventually_not hK ?_
  intro z hzK hzS
  have hpre : (fun z : E => fderiv ℝ ρ z) ⁻¹'
      {L : E →L[ℝ] F | Function.Surjective L} ∈ 𝓝 z :=
    (continuousAt_fderiv_of_contDiffOn hU ρ hρ (hKU hzK)).preimage_mem_nhds
      ((isOpen_setOf_surjective_clm' (E := E) (F := F)).mem_nhds (not_not.mp hzS))
  show {w : E | w ∉ {z | ¬ Function.Surjective (fderiv ℝ ρ z)}} ∈ 𝓝 z
  simpa using hpre


/-- **Local flat statement.** Near a point of `U` where the derivative vanishes, the image of the
flat stratum has empty interior. -/
lemma flat_ball {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {m : ℕ} (hm : 0 < m)
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    {x : E} (hxU : x ∈ U) (hx : fderiv ℝ ρ x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ U ∧
      interior (ρ '' ({z : E | fderiv ℝ ρ z = 0} ∩ ball x ε)) = ∅ := by
  obtain ⟨G, hG, hGeq⟩ := Work.Sard.exists_contDiff_eq_nhds_of_hasBump ρ x U (hU.mem_nhds hxU) hρ
  have hGeq' : ∀ᶠ z in 𝓝 x, G z = ρ z := hGeq
  have hfdeq : (fun z => fderiv ℝ G z) =ᶠ[𝓝 x] (fun z => fderiv ℝ ρ z) := hGeq.fderiv
  have h4 : U ∩ {z | G z = ρ z} ∩ {z | fderiv ℝ G z = fderiv ℝ ρ z} ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hxU) hGeq') hfdeq
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h4
  have hGU : ball x ε ⊆ U := fun z hz => (hεsub hz).1.1
  have hGρ : ∀ z ∈ ball x ε, G z = ρ z := fun z hz => (hεsub hz).1.2
  have hD : ∀ z ∈ ball x ε, fderiv ℝ G z = fderiv ℝ ρ z := fun z hz => (hεsub hz).2
  have hGflat : interior (G '' {z : E | fderiv ℝ G z = 0}) = ∅ := by
    rcases (by omega : m = 1 ∨ 2 ≤ m) with hm1 | hm2
    · subst hm1
      have hnt : Nontrivial F := nontrivial_of_finrank_eq_one hF
      haveI := hnt
      have hcrit : interior (G '' {z : E | ¬ Function.Surjective (fderiv ℝ G z)}) = ∅ :=
        Work.Sard.weakSardGlobalOne E F hF (by omega) G hG
      have hsub : {z : E | fderiv ℝ G z = 0}
          ⊆ {z : E | ¬ Function.Surjective (fderiv ℝ G z)} := by
        intro z hz
        have hz' : fderiv ℝ G z = 0 := hz
        show ¬ Function.Surjective (fderiv ℝ G z)
        rw [hz']
        exact not_surjective_zero_of_nontrivial
      have hle : interior (G '' {z : E | fderiv ℝ G z = 0})
          ≤ interior (G '' {z : E | ¬ Function.Surjective (fderiv ℝ G z)}) :=
        interior_mono (Set.image_mono hsub)
      rw [hcrit] at hle
      exact le_bot_iff.mp hle
    · exact flat_image_interior_empty_of_two_le' hm2 hE hF G hG
  have hset : {z : E | fderiv ℝ ρ z = 0} ∩ ball x ε
      = {z : E | fderiv ℝ G z = 0} ∩ ball x ε := by
    ext z
    constructor
    · intro hz
      have hz1 : fderiv ℝ ρ z = 0 := hz.1
      exact ⟨show fderiv ℝ G z = 0 from by rw [hD z hz.2, hz1], hz.2⟩
    · intro hz
      have hz1 : fderiv ℝ G z = 0 := hz.1
      exact ⟨show fderiv ℝ ρ z = 0 from by rw [← hD z hz.2, hz1], hz.2⟩
  have himg : ρ '' ({z : E | fderiv ℝ ρ z = 0} ∩ ball x ε)
      = G '' ({z : E | fderiv ℝ G z = 0} ∩ ball x ε) := by
    rw [hset]
    exact Set.image_congr (fun z hz => (hGρ z hz.2).symm)
  refine ⟨ε, hε, hGU, ?_⟩
  rw [himg]
  have hle : interior (G '' ({z : E | fderiv ℝ G z = 0} ∩ ball x ε))
      ≤ interior (G '' {z : E | fderiv ℝ G z = 0}) :=
    interior_mono (Set.image_mono Set.inter_subset_left)
  rw [hGflat] at hle
  exact le_bot_iff.mp hle

/-- **Local non-flat statement.** Near a point of `U` where the derivative does not vanish, the
image of the critical set has empty interior. -/
lemma crit_ball {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {m : ℕ}
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ m' : ℕ, m' < m → Work.Sard.wp.WeakSardGlobal m')
    {x : E} (hxU : x ∈ U) (hx : fderiv ℝ ρ x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ U ∧
      interior (ρ '' ({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ ball x ε)) = ∅ := by
  obtain ⟨G, hG, hGeq⟩ := Work.Sard.exists_contDiff_eq_nhds_of_hasBump ρ x U (hU.mem_nhds hxU) hρ
  have hGeq' : ∀ᶠ z in 𝓝 x, G z = ρ z := hGeq
  have hfdeq : (fun z => fderiv ℝ G z) =ᶠ[𝓝 x] (fun z => fderiv ℝ ρ z) := hGeq.fderiv
  have h4 : U ∩ {z | G z = ρ z} ∩ {z | fderiv ℝ G z = fderiv ℝ ρ z} ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hxU) hGeq') hfdeq
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.mp h4
  have hGρ : ∀ z ∈ ball x ε₀, G z = ρ z := fun z hz => (hε₀sub hz).1.2
  have hD : ∀ z ∈ ball x ε₀, fderiv ℝ G z = fderiv ℝ ρ z := fun z hz => (hε₀sub hz).2
  have hxG : fderiv ℝ G x ≠ 0 := by
    rw [hGeq.fderiv_eq]
    exact hx
  obtain ⟨V, hVopen, hxV, hVint⟩ := Work.Sard.weakSardNonflatGlobal (m := m) hE hF IH G hG hxG
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hVopen.mem_nhds hxV) (Metric.ball_mem_nhds x hε₀))
  have hset : {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ ball x ε
      = {z : E | ¬ Function.Surjective (fderiv ℝ G z)} ∩ ball x ε := by
    ext z
    constructor
    · intro hz
      exact ⟨show ¬ Function.Surjective (fderiv ℝ G z) from by
        rw [hD z (hεsub hz.2).2]; exact hz.1, hz.2⟩
    · intro hz
      exact ⟨show ¬ Function.Surjective (fderiv ℝ ρ z) from by
        rw [← hD z (hεsub hz.2).2]; exact hz.1, hz.2⟩
  have himg : ρ '' ({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ ball x ε)
      = G '' ({z : E | ¬ Function.Surjective (fderiv ℝ G z)} ∩ ball x ε) := by
    rw [hset]
    exact Set.image_congr (fun z hz => (hGρ z (hεsub hz.2).2).symm)
  refine ⟨ε, hε, fun z hz => (hε₀sub (hεsub hz).2).1.1, ?_⟩
  rw [himg]
  have hsub2 : ({z : E | ¬ Function.Surjective (fderiv ℝ G z)} ∩ ball x ε)
      ⊆ (V ∩ {z : E | ¬ Function.Surjective (fderiv ℝ G z)}) := by
    intro z hz
    have hzV : z ∈ V := by
      have h := hεsub hz.2
      rw [Set.mem_inter_iff] at h
      exact h.1
    exact ⟨hzV, hz.1⟩
  have hle : interior (G '' ({z : E | ¬ Function.Surjective (fderiv ℝ G z)} ∩ ball x ε))
      ≤ interior (G '' (V ∩ {z : E | ¬ Function.Surjective (fderiv ℝ G z)})) :=
    interior_mono (Set.image_mono hsub2)
  rw [hVint] at hle
  exact le_bot_iff.mp hle


/-- The interior of the union of two closed sets with empty interior is empty. -/
lemma interior_union_eq_empty {X : Type*} [TopologicalSpace X] [BaireSpace X] {A B : Set X}
    (hA : IsClosed A) (hAi : interior A = ∅) (hB : IsClosed B) (hBi : interior B = ∅) :
    interior (A ∪ B) = ∅ := by
  have hunion : (⋃ b : Bool, bif b then A else B) = A ∪ B := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨b, hb⟩
      cases b with
      | false => exact Or.inr hb
      | true => exact Or.inl hb
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  have h := Work.Sard.wp.interior_eq_empty_iUnion_isClosed (ι := Bool)
    (F := fun b : Bool => bif b then A else B)
    (fun b => by cases b <;> simpa) (fun b => by cases b <;> simpa)
  rwa [hunion] at h

/-- **Assembly, compact version.** For a compact `K ⊆ U` the image under `ρ` of the critical points in
`K` has empty interior. -/
theorem interior_crit_image_eq_empty_of_compact {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {m : ℕ} (hm : 0 < m)
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ m' : ℕ, m' < m → Work.Sard.wp.WeakSardGlobal m')
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    interior (ρ '' ({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ K)) = ∅ := by
  classical
  set Sf : Set E := {z : E | fderiv ℝ ρ z = 0} with hSfdef
  set Sc : Set E := {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} with hScdef
  have hKf : IsCompact (K ∩ Sf) := isCompact_inter_flat hU ρ hρ hK hKU
  have hKc : IsCompact (K ∩ Sc) := isCompact_inter_crit hU ρ hρ hK hKU
  -- the open set where the derivative does not vanish
  set W : Set E := {z : E | fderiv ℝ ρ z ≠ 0} ∩ U with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzf, hzU⟩
    have hcont := (hρ.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hzU)
    exact Filter.inter_mem
      (hcont.preimage_mem_nhds ((isClosed_singleton.isOpen_compl).mem_nhds hzf))
      (hU.mem_nhds hzU)
  -- ### Stage 1: the flat stratum
  have hex1 : ∀ x : ↥(K ∩ Sf), ∃ ε : ℝ, 0 < ε ∧ interior (ρ '' (Sf ∩ ball (x : E) ε)) = ∅ := by
    intro x
    obtain ⟨ε, hε, -, hεi⟩ := flat_ball hU ρ hρ hm hE hF (hKU x.2.1) (by simpa [hSfdef] using x.2.2)
    exact ⟨ε, hε, by simpa [hSfdef] using hεi⟩
  choose ef hef using hex1
  have hbsub1 : (K ∩ Sf) ⊆ ⋃ x : ↥(K ∩ Sf), ball (x : E) (ef x / 4) := by
    intro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    rw [mem_ball, dist_self]
    have hpos : (0 : ℝ) < ef ⟨z, hz⟩ := (hef ⟨z, hz⟩).1
    linarith
  obtain ⟨t₁, ht₁⟩ := hKf.elim_finite_subcover (fun x : ↥(K ∩ Sf) => ball (x : E) (ef x / 4))
    (fun _ => isOpen_ball) hbsub1
  have hcov1 : (K ∩ Sf) ⊆ ⋃ x : ↥t₁, ball ((x : ↥(K ∩ Sf)) : E) (ef (x : ↥(K ∩ Sf)) / 4) := by
    intro z hz
    have h := ht₁ hz
    rw [Set.mem_iUnion] at h
    obtain ⟨w, hw⟩ := h
    rw [Set.mem_iUnion] at hw
    exact Set.mem_iUnion.mpr ⟨⟨w, hw.1⟩, hw.2⟩
  let E₁ : ↥(K ∩ Sf) → Set E := fun x => K ∩ Sf ∩ closedBall (x : E) (ef x / 2)
  have hE₁_int : ∀ x : ↥(K ∩ Sf), interior (ρ '' (E₁ x)) = ∅ := by
    intro x
    have hsub : E₁ x ⊆ Sf ∩ ball (x : E) (ef x) := by
      intro z hz
      refine ⟨hz.1.2, ?_⟩
      have hdist : dist z (x : E) ≤ ef x / 2 := mem_closedBall.mp hz.2
      rw [mem_ball]
      have hpos : (0 : ℝ) < ef x := (hef x).1
      linarith
    have hle : interior (ρ '' (E₁ x)) ≤ interior (ρ '' (Sf ∩ ball (x : E) (ef x))) :=
      interior_mono (Set.image_mono hsub)
    rw [(hef x).2] at hle
    exact le_bot_iff.mp hle
  have hE₁_cl : ∀ x : ↥(K ∩ Sf), IsClosed (ρ '' (E₁ x)) := by
    intro x
    have hc : IsCompact (E₁ x) := hKf.inter_right isClosed_closedBall
    exact (hc.image_of_continuousOn (hρ.continuousOn.mono (fun z hz => hKU hz.1.1))).isClosed
  have hE₁_compact : ∀ x : ↥(K ∩ Sf), IsCompact (E₁ x) :=
    fun x => hKf.inter_right isClosed_closedBall
  have hU₁ : interior (⋃ x : ↥t₁, ρ '' (E₁ (x : ↥(K ∩ Sf)))) = ∅ :=
    Work.Sard.wp.interior_eq_empty_iUnion_isClosed
      (fun x => hE₁_cl (x : ↥(K ∩ Sf))) (fun x => hE₁_int (x : ↥(K ∩ Sf)))
  have hcover1 : K ∩ Sf ⊆ ⋃ x : ↥t₁, E₁ (x : ↥(K ∩ Sf)) := by
    intro z hz
    have h := hcov1 hz
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨w, ?_⟩
    have hd : dist z ((w : ↥(K ∩ Sf)) : E) < ef (w : ↥(K ∩ Sf)) / 4 := mem_ball.mp hw
    have hpos : (0 : ℝ) < ef (w : ↥(K ∩ Sf)) := (hef (w : ↥(K ∩ Sf))).1
    exact ⟨hz, mem_closedBall.mpr (by linarith)⟩
  -- ### Stage 2: the non-flat critical points, through an exhaustion of `W`
  set Ω : ℕ → Set E := fun n => {z : E | ‖z‖ ≤ (n : ℝ) ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Wᶜ ∪ {0})} with hΩdef
  have hΩcomp : ∀ n : ℕ, IsCompact (Ω n) := by
    intro n
    have h1 : IsCompact (Metric.closedBall (0 : E) (n : ℝ)) := isCompact_closedBall _ _
    have h2 : IsClosed {z : E | (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Wᶜ ∪ {0})} :=
      isClosed_le continuous_const (Metric.continuous_infDist_pt (s := Wᶜ ∪ {0}))
    have h3 : Ω n = Metric.closedBall (0 : E) (n : ℝ)
        ∩ {z : E | (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Wᶜ ∪ {0})} := by
      rw [hΩdef]
      ext z
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [h3]
    exact h1.inter_right h2
  have hΩW : ∀ n : ℕ, Ω n ⊆ W := by
    intro n z hz
    obtain ⟨-, hzinf⟩ := hz
    by_contra hzW'
    have hmem : z ∈ Wᶜ ∪ {0} := Or.inl hzW'
    have hzero : Metric.infDist z (Wᶜ ∪ {0}) = 0 := Metric.infDist_zero_of_mem hmem
    have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hWsub : W \ {0} ⊆ ⋃ n, Ω n := by
    intro z hz
    obtain ⟨hzW, hz0⟩ := hz
    have hznot : z ∉ Wᶜ ∪ {0} := by
      rintro (h | h)
      · exact h hzW
      · exact hz0 h
    have hclosed : IsClosed (Wᶜ ∪ {0}) := hWopen.isClosed_compl.union isClosed_singleton
    have hne : (Wᶜ ∪ {0} : Set E).Nonempty := ⟨0, Or.inr rfl⟩
    have hpos : 0 < Metric.infDist z (Wᶜ ∪ {0}) :=
      (hclosed.notMem_iff_infDist_pos hne).mp hznot
    refine Set.mem_iUnion.mpr ⟨⌈‖z‖⌉₊ + ⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ + 1, ?_, ?_⟩
    · rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have h1 : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (0 : ℝ) ≤ (⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hceil : (Metric.infDist z (Wᶜ ∪ {0}))⁻¹ ≤
          (⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.le_ceil _
      have h0 : (0 : ℝ) ≤ (⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.cast_nonneg _
      rw [div_le_iff₀ (by positivity :
        (0 : ℝ) < (⌈‖z‖⌉₊ : ℝ) + (⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ : ℝ) + 1 + 1)]
      have key : (1 : ℝ) ≤
          (⌈(Metric.infDist z (Wᶜ ∪ {0}))⁻¹⌉₊ : ℝ) * Metric.infDist z (Wᶜ ∪ {0}) := by
        have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hpos)
        rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at h
      nlinarith [key, h0, hpos]
  -- local balls at the points of `Ω n ∩ (K ∩ Sc)`
  have hcrit2 : ∀ (n : ℕ) (z : ↥(Ω n ∩ (K ∩ Sc))),
      ∃ ε : ℝ, 0 < ε ∧ interior (ρ '' (Sc ∩ ball (z : E) ε)) = ∅ := by
    intro n z
    have hzW : (z : E) ∈ W := hΩW n z.2.1
    have hzW' : fderiv ℝ ρ (z : E) ≠ 0 := hzW.1
    have hzU : (z : E) ∈ U := hzW.2
    obtain ⟨ε, hε, -, hεi⟩ := crit_ball hU ρ hρ hE hF IH hzU hzW'
    exact ⟨ε, hε, by simpa [hScdef] using hεi⟩
  choose eg heg using hcrit2
  let P : (n : ℕ) → ↥(Ω n ∩ (K ∩ Sc)) → Set F := fun n z =>
    ρ '' (Ω n ∩ (K ∩ Sc) ∩ closedBall (z : E) (eg n z / 2))
  have hP_cl : ∀ (n : ℕ) (z : ↥(Ω n ∩ (K ∩ Sc))), IsClosed (P n z) := by
    intro n z
    have hc : IsCompact (Ω n ∩ (K ∩ Sc) ∩ closedBall (z : E) (eg n z / 2)) :=
      ((hΩcomp n).inter_right hKc.isClosed).inter_right isClosed_closedBall
    exact (hc.image_of_continuousOn (hρ.continuousOn.mono (fun w hw => hKU hw.1.2.1))).isClosed
  have hP_int : ∀ (n : ℕ) (z : ↥(Ω n ∩ (K ∩ Sc))), interior (P n z) = ∅ := by
    intro n z
    have hsub : Ω n ∩ (K ∩ Sc) ∩ closedBall (z : E) (eg n z / 2)
        ⊆ Sc ∩ ball (z : E) (eg n z) := by
      intro w hw
      refine ⟨hw.1.2.2, ?_⟩
      have hdist : dist w (z : E) ≤ eg n z / 2 := mem_closedBall.mp hw.2
      rw [mem_ball]
      have hpos : (0 : ℝ) < eg n z := (heg n z).1
      linarith
    have hle : interior (ρ '' (Ω n ∩ (K ∩ Sc) ∩ closedBall (z : E) (eg n z / 2)))
        ≤ interior (ρ '' (Sc ∩ ball (z : E) (eg n z))) :=
      interior_mono (Set.image_mono hsub)
    rw [(heg n z).2] at hle
    exact le_bot_iff.mp hle
  have ht₂ : ∀ n : ℕ, ∃ t : Finset ↥(Ω n ∩ (K ∩ Sc)),
      Ω n ∩ (K ∩ Sc) ⊆ ⋃ z ∈ t, ball (z : E) (eg n z / 4) := by
    intro n
    have hc : IsCompact (Ω n ∩ (K ∩ Sc)) := (hΩcomp n).inter_right hKc.isClosed
    refine hc.elim_finite_subcover (fun z : ↥(Ω n ∩ (K ∩ Sc)) => ball (z : E) (eg n z / 4))
      (fun _ => isOpen_ball) ?_
    intro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    rw [mem_ball, dist_self]
    have hpos : (0 : ℝ) < eg n ⟨z, hz⟩ := (heg n ⟨z, hz⟩).1
    linarith
  choose t₂ ht₂c using ht₂
  have hcov2 : ∀ n, Ω n ∩ (K ∩ Sc) ⊆ ⋃ z : ↥(t₂ n),
      (Ω n ∩ (K ∩ Sc) ∩ closedBall ((z : ↥(Ω n ∩ (K ∩ Sc))) : E)
        (eg n (z : ↥(Ω n ∩ (K ∩ Sc))) / 2)) := by
    intro n z hz
    have h := ht₂c n hz
    rw [Set.mem_iUnion] at h
    obtain ⟨w, hw⟩ := h
    rw [Set.mem_iUnion] at hw
    refine Set.mem_iUnion.mpr ⟨⟨w, hw.1⟩, ?_⟩
    have hd : dist z (w : E) < eg n w / 4 := mem_ball.mp hw.2
    have hpos : (0 : ℝ) < eg n w := (heg n w).1
    exact ⟨hz, mem_closedBall.mpr (by linarith)⟩
  have hZn_cl : ∀ n, IsClosed (⋃ z : ↥(t₂ n), P n (z : ↥(Ω n ∩ (K ∩ Sc)))) :=
    fun n => isClosed_iUnion_of_finite (fun z => hP_cl n (z : ↥(Ω n ∩ (K ∩ Sc))))
  have hZn_int : ∀ n, interior (⋃ z : ↥(t₂ n), P n (z : ↥(Ω n ∩ (K ∩ Sc)))) = ∅ :=
    fun n => Work.Sard.wp.interior_eq_empty_iUnion_isClosed
      (fun z => hP_cl n (z : ↥(Ω n ∩ (K ∩ Sc)))) (fun z => hP_int n (z : ↥(Ω n ∩ (K ∩ Sc))))
  -- ### The critical set is covered
  have hcover3 : K ∩ Sc ⊆ (K ∩ Sf) ∪ ({0} ∩ (K ∩ Sc)) ∪ ⋃ n, (Ω n ∩ (K ∩ Sc)) := by
    intro z hz
    by_cases hzSf : z ∈ Sf
    · exact Or.inl (Or.inl ⟨hz.1, hzSf⟩)
    · have hzW : z ∈ W := ⟨by simpa [hSfdef] using hzSf, hKU hz.1⟩
      by_cases hz0 : z = 0
      · exact Or.inl (Or.inr ⟨hz0, hz⟩)
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hWsub ⟨hzW, hz0⟩)
        exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨hn, hz⟩⟩)
  -- ### The final Baire step
  have hA : IsClosed (ρ '' (K ∩ Sf)) :=
    (hKf.image_of_continuousOn (hρ.continuousOn.mono (fun z hz => hKU hz.1))).isClosed
  have hAi : interior (ρ '' (K ∩ Sf)) = ∅ := by
    have himg : ρ '' (⋃ x : ↥t₁, E₁ (x : ↥(K ∩ Sf)))
        = ⋃ x : ↥t₁, ρ '' (E₁ (x : ↥(K ∩ Sf))) := by
      rw [Set.image_iUnion]
    have hle : interior (ρ '' (K ∩ Sf))
        ≤ interior (⋃ x : ↥t₁, ρ '' (E₁ (x : ↥(K ∩ Sf)))) := by
      rw [← himg]
      exact interior_mono (Set.image_mono hcover1)
    rw [hU₁] at hle
    exact le_bot_iff.mp hle
  have hB : IsClosed (ρ '' ({0} ∩ (K ∩ Sc))) :=
    ((isCompact_singleton.inter_right hKc.isClosed).image_of_continuousOn
      (hρ.continuousOn.mono (fun w hw => hKU hw.2.1))).isClosed
  have hBi : interior (ρ '' ({0} ∩ (K ∩ Sc))) = ∅ := by
    refine interior_eq_empty_of_dimH_lt ?_
    have hle : ρ '' ({0} ∩ (K ∩ Sc)) ⊆ ({ρ 0} : Set F) := by
      rintro y ⟨w, hw, rfl⟩
      have hw0 : w = 0 := hw.1
      rw [hw0]
      exact Set.mem_singleton _
    refine lt_of_le_of_lt (dimH_mono hle) ?_
    rw [dimH_singleton, hF]
    exact_mod_cast hm
  let V : ℕ → Set F := fun n => if n = 0 then ρ '' (K ∩ Sf)
    else if n = 1 then ρ '' ({0} ∩ (K ∩ Sc))
    else ⋃ z : ↥(t₂ (n - 2)), P (n - 2) (z : ↥(Ω (n - 2) ∩ (K ∩ Sc)))
  have hVc : ∀ n, IsClosed (V n) := by
    intro n
    by_cases h : n = 0
    · simp [V, h, hA]
    · by_cases h1 : n = 1
      · simp only [V, h, h1, if_true]
        exact hB
      · simp only [V, h, h1, if_false]
        exact hZn_cl (n - 2)
  have hVi : ∀ n, interior (V n) = ∅ := by
    intro n
    by_cases h : n = 0
    · simp [V, h, hAi]
    · by_cases h1 : n = 1
      · simp only [V, h, h1, if_true]
        exact hBi
      · simp only [V, h, h1, if_false]
        exact hZn_int (n - 2)
  have hVunion : (ρ '' (K ∩ Sf)) ∪ (ρ '' ({0} ∩ (K ∩ Sc))) ∪
      (⋃ n, ⋃ z : ↥(t₂ n), P n (z : ↥(Ω n ∩ (K ∩ Sc)))) ⊆ ⋃ n, V n := by
    rintro y ((hy | hy) | hy)
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [V] using hy⟩
    · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      simp only [V, if_true]
      exact hy
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨n + 2, by simp only [V, if_false, if_true, Nat.add_sub_cancel] ; exact hn⟩
  have hsub : ρ '' (K ∩ Sc) ⊆ ρ '' (K ∩ Sf) ∪ ρ '' ({0} ∩ (K ∩ Sc)) ∪
      (⋃ n, ⋃ z : ↥(t₂ n), P n (z : ↥(Ω n ∩ (K ∩ Sc)))) := by
    rintro y ⟨z, hz, rfl⟩
    rcases hcover3 hz with (h | h) | h
    · exact Or.inl (Or.inl (Set.mem_image_of_mem _ h))
    · exact Or.inl (Or.inr (Set.mem_image_of_mem _ h))
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      obtain ⟨w, hwmem⟩ := Set.mem_iUnion.mp (hcov2 n hn)
      exact Or.inr (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨w,
        Set.mem_image_of_mem _ hwmem⟩⟩)
  have hfinal : interior (ρ '' (K ∩ Sc)) = ∅ := by
    have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hVc hVi
    have hle : interior (ρ '' (K ∩ Sc)) ≤ interior (⋃ n, V n) :=
      interior_mono (hsub.trans hVunion)
    rw [hBaire] at hle
    exact le_bot_iff.mp hle
  simpa [hScdef, Set.inter_comm] using hfinal


/-- **From the compact version to the global statement on an open set.** -/
theorem interior_critWithin_image_eq_empty {U : Set E} (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {m : ℕ} (hm : 0 < m)
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ m' : ℕ, m' < m → Work.Sard.wp.WeakSardGlobal m') :
    interior (ρ '' (U ∩ {z : E | ¬ Function.Surjective (fderivWithin ℝ ρ U z)})) = ∅ := by
  classical
  have hset : U ∩ {z : E | ¬ Function.Surjective (fderivWithin ℝ ρ U z)}
      = U ∩ {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} := by
    ext z
    constructor
    · rintro ⟨hzU, hz⟩
      refine ⟨hzU, ?_⟩
      show ¬ Function.Surjective (fderiv ℝ ρ z)
      rwa [← fderivWithin_of_isOpen hU hzU]
    · rintro ⟨hzU, hz⟩
      refine ⟨hzU, ?_⟩
      show ¬ Function.Surjective (fderivWithin ℝ ρ U z)
      rwa [fderivWithin_of_isOpen hU hzU]
  rw [hset]
  set Sc : Set E := {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} with hScdef
  -- exhaustion of `U`
  set K : ℕ → Set E := fun n => {z : E | ‖z‖ ≤ (n : ℝ) ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Uᶜ ∪ {0})} with hKdef
  have hKcomp : ∀ n, IsCompact (K n) := by
    intro n
    have h1 : IsCompact (Metric.closedBall (0 : E) (n : ℝ)) := isCompact_closedBall _ _
    have h2 : IsClosed {z : E | (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Uᶜ ∪ {0})} :=
      isClosed_le continuous_const (Metric.continuous_infDist_pt (s := Uᶜ ∪ {0}))
    have h3 : K n = Metric.closedBall (0 : E) (n : ℝ)
        ∩ {z : E | (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist z (Uᶜ ∪ {0})} := by
      rw [hKdef]
      ext z
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [h3]
    exact h1.inter_right h2
  have hKU : ∀ n, K n ⊆ U := by
    intro n z hz
    obtain ⟨-, hzinf⟩ := hz
    by_contra hzU
    have hmem : z ∈ Uᶜ ∪ {0} := Or.inl hzU
    have hzero : Metric.infDist z (Uᶜ ∪ {0}) = 0 := Metric.infDist_zero_of_mem hmem
    have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hUcover : U ⊆ {0} ∪ ⋃ n, K n := by
    intro z hzU
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · have hznot : z ∉ Uᶜ ∪ {0} := by
        rintro (h | h)
        · exact h hzU
        · exact hz0 h
      have hclosed : IsClosed (Uᶜ ∪ {0}) := hU.isClosed_compl.union isClosed_singleton
      have hne : (Uᶜ ∪ {0} : Set E).Nonempty := ⟨0, Or.inr rfl⟩
      have hpos : 0 < Metric.infDist z (Uᶜ ∪ {0}) :=
        (hclosed.notMem_iff_infDist_pos hne).mp hznot
      refine Or.inr (Set.mem_iUnion.mpr ⟨⌈‖z‖⌉₊ + ⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ + 1, ?_, ?_⟩)
      · rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        have h1 : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (0 : ℝ) ≤ (⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.cast_nonneg _
        linarith
      · rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        have hceil : (Metric.infDist z (Uᶜ ∪ {0}))⁻¹ ≤
            (⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.le_ceil _
        have h0 : (0 : ℝ) ≤ (⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ : ℝ) := Nat.cast_nonneg _
        rw [div_le_iff₀ (by positivity :
          (0 : ℝ) < (⌈‖z‖⌉₊ : ℝ) + (⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ : ℝ) + 1 + 1)]
        have key : (1 : ℝ) ≤
            (⌈(Metric.infDist z (Uᶜ ∪ {0}))⁻¹⌉₊ : ℝ) * Metric.infDist z (Uᶜ ∪ {0}) := by
          have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hpos)
          rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at h
        nlinarith [key, h0, hpos]
  -- the pieces
  let V : ℕ → Set F := fun n => if n = 0 then ({ρ 0} : Set F) else ρ '' (K (n - 1) ∩ Sc)
  have hVc : ∀ n, IsClosed (V n) := by
    intro n
    by_cases h : n = 0
    · simp only [V, h, if_true]
      exact isClosed_singleton
    · simp only [V, h, if_false]
      exact ((isCompact_inter_crit hU ρ hρ (hKcomp (n - 1)) (hKU (n - 1))).image_of_continuousOn
        (hρ.continuousOn.mono (fun z hz => hKU (n - 1) hz.1))).isClosed
  have hVi : ∀ n, interior (V n) = ∅ := by
    intro n
    by_cases h : n = 0
    · simp only [V, h, if_true]
      refine interior_eq_empty_of_dimH_lt ?_
      rw [dimH_singleton, hF]
      exact_mod_cast hm
    · simp only [V, h, if_false]
      simpa [hScdef, Set.inter_comm] using
        interior_crit_image_eq_empty_of_compact hU ρ hρ hm hE hF IH (hKcomp (n - 1)) (hKU (n - 1))
  have hcover : U ∩ Sc ⊆ {0} ∪ ⋃ n, (K n ∩ Sc) := by
    intro z hz
    obtain ⟨hzU, hzc⟩ := hz
    rcases hUcover hzU with h0 | h0
    · exact Or.inl h0
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h0
      exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨hn, hzc⟩⟩)
  have hfinal : interior (ρ '' (U ∩ Sc)) = ∅ := by
    have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hVc hVi
    have heq : ρ '' ({0} ∪ ⋃ n, (K n ∩ Sc))
        = ({ρ 0} : Set F) ∪ ⋃ n, ρ '' (K n ∩ Sc) := by
      rw [Set.image_union, Set.image_iUnion, Set.image_singleton]
    have hle : interior (ρ '' (U ∩ Sc)) ≤ interior (⋃ n, V n) := by
      have hsub : ρ '' (U ∩ Sc) ⊆ ⋃ n, V n := by
        refine (Set.image_mono hcover).trans ?_
        rw [heq]
        rintro y (hy | hy)
        · exact Set.mem_iUnion.mpr ⟨0, by simp only [V, if_true]; exact hy⟩
        · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
          exact Set.mem_iUnion.mpr ⟨n + 1, by simpa [V] using hn⟩
      exact interior_mono hsub
    rw [hBaire] at hle
    exact le_bot_iff.mp hle
  simpa [hScdef] using hfinal


/-- **Weak Sard's theorem**, in the general form used for the induction. -/
theorem weakSard_all : ∀ m, Work.Sard.wp.WeakSard m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro E _ _ _ F _ _ _ hF hE U hU ρ hρ
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0
      haveI : Subsingleton F := Module.finrank_zero_iff.mp hF
      have hempty : (U ∩ {z : E | ¬ Function.Surjective (fderivWithin ℝ ρ U z)}) = ∅ := by
        ext z
        constructor
        · rintro ⟨-, hz⟩
          exact absurd (fun y => ⟨0, Subsingleton.elim _ _⟩) hz
        · intro hz
          exact absurd hz (Set.notMem_empty z)
      rw [hempty, Set.image_empty, interior_empty]
    · have IH : ∀ m' : ℕ, m' < m → Work.Sard.wp.WeakSardGlobal m' := by
        intro m' hm'
        intro E' _ _ _ F' _ _ _ hF' hE' ρ' hρ'
        have h := ih m' hm' E' F' hF' hE' Set.univ isOpen_univ ρ' hρ'.contDiffOn
        simpa [fderivWithin_univ] using h
      exact interior_critWithin_image_eq_empty (E := E) (F := F) hU ρ hρ hm (by omega) hF IH

end Work.Sard.prod

namespace Work.Sard

/-- **Inscribed rectangles in a smooth Jordan curve**: the weak Sard statement in the model
`ℝ × ℝⁿ → ℝⁿ`.  For a map `ρ` that is `C^∞` on an open set `U`, the image under `ρ` of the points of
`U` where the derivative is not surjective has empty interior. -/
theorem weak_interior_empty_open_prod {n : ℕ}
    {U : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (ρ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) :
    interior (ρ '' (U ∩ {z | ¬ Function.Surjective (fderivWithin ℝ ρ U z)})) = ∅ := by
  have h := Work.Sard.prod.weakSard_all n
  refine h (ℝ × EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ?_ ?_ U hU ρ hρ
  · exact finrank_euclideanSpace_fin
  · rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    omega

end Work.Sard
