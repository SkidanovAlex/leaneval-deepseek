import Mathlib
import Submission.Work.Sard.submersion_smooth
import Submission.Work.Sard.exists_contDiff_eq_nhds_of_hasBump
import Submission.Work.Sard.slice_image_interior_eq_empty
import Submission.Work.Sard.block_fderiv_prodMk
import Submission.Work.Sard.holder_two_fderiv_eq_zero
import Submission.Work.Sard.holder_three_snd_fderiv_eq_zero
import Submission.Work.Sard.dimH_levelSet_le

namespace Work.Sard

open MeasureTheory Metric Set Filter
open scoped Topology ContDiff NNReal ENNReal

universe u v

/-! ### Hausdorff-dimension helpers for the flat stratum

The following lemmas (Hausdorff dimension estimates for the "flat" critical stratum, the Baire
argument, and the closedness of the critical set) are self-contained copies, in this namespace, of
material needed by the strong induction `Work.Sard.weakSardAt_all` below.  They are used only for
the flat stratum `{fderiv ℝ f = 0}`; the non-flat stratum is handled by `Work.Sard.rank_chart_aux`. -/

lemma interior_eq_empty_iUnion_isClosed {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {ι : Type*} [Countable ι] {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    (hFi : ∀ i, interior (F i) = ∅) : interior (⋃ i, F i) = ∅ := by
  have hmeag : IsMeagre (⋃ i, F i) :=
    isMeagre_iUnion fun i => (hF i).isNowhereDense_iff.mpr (hFi i) |>.isMeagre
  rw [interior_eq_empty_iff_dense_compl]
  exact dense_of_mem_residual hmeag

/-! ### The critical set is closed -/

/-- Surjectivity is an open condition on continuous linear maps with finite-dimensional target. -/
lemma isOpen_setOf_surjective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
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

/-- The set of points where `fderiv ℝ f` is not surjective is closed, for a `C¹` map into a
finite-dimensional space. -/
lemma isClosed_setOf_not_surjective_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) :
    IsClosed {x : E | ¬ Function.Surjective (fderiv ℝ f x)} := by
  have hopen : IsOpen {x : E | Function.Surjective (fderiv ℝ f x)} := by
    have h := (hf.continuous_fderiv (by norm_num)).isOpen_preimage
      {L : E →L[ℝ] F | Function.Surjective L} isOpen_setOf_surjective_clm
    simpa using h
  simpa [Set.compl_ofPred] using hopen.isClosed_compl

/-! ### Hausdorff dimension helpers -/

/-- A set of Hausdorff dimension `< finrank ℝ F` has empty interior. -/
lemma interior_eq_empty_of_dimH_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {s : Set F}
    (h : dimH s < ((Module.finrank ℝ F : ℕ) : ℝ≥0∞)) : interior s = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  exact dense_compl_of_dimH_lt_finrank h

/-- If `f` is locally `r`-Hölder on `S` and `finrank E / r < finrank F`, then `f '' S` has empty
interior. -/
lemma interior_eq_empty_of_holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (S : Set E) (r : ℕ) (hr : 0 < r)
    (hH : ∀ x ∈ S, ∃ C : NNReal, ∃ t ∈ nhdsWithin x S, HolderOnWith C (r : NNReal) f t)
    (hdim : ((Module.finrank ℝ E : ℝ) / r) < (Module.finrank ℝ F : ℝ)) :
    interior (f '' S) = ∅ := by
  have hr0 : (0 : NNReal) < (r : NNReal) := by exact_mod_cast hr
  have hle : dimH (f '' S) ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) / (r : ℝ≥0∞) :=
    (dimH_image_le_of_locally_holder_on hr0 hH).trans
      (ENNReal.div_le_div_right (le_trans (dimH_mono (Set.subset_univ S))
        (le_of_eq (Real.dimH_univ_eq_finrank E))) _)
  refine interior_eq_empty_of_dimH_lt ?_
  have hne : dimH (f '' S) ≠ ⊤ := Real.dimH_ne_top _
  have hne' : (((Module.finrank ℝ E : ℕ) : ℝ≥0∞) / (r : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by simp [hr.ne'])
  rw [← ENNReal.toReal_lt_toReal hne (by simp)]
  have hFtop : (((Module.finrank ℝ F : ℕ) : ℝ≥0∞)) ≠ ⊤ := by simp
  have hdiv : ((((Module.finrank ℝ E : ℕ) : ℝ≥0∞) / (r : ℝ≥0∞))).toReal
      = (Module.finrank ℝ E : ℝ) / r := by
    rw [ENNReal.toReal_div]
    simp
  have := ENNReal.toReal_mono hne' hle
  rw [hdiv] at this
  simp only [ENNReal.toReal_natCast] at this ⊢
  linarith

/-! ### The flat case, `m ≥ 2` -/

/-- The image of `{fderiv f = 0}` under a smooth map with `finrank ℝ E = m + 1`, `finrank ℝ F = m`
has empty interior, provided `2 ≤ m`. -/
lemma flat_case_ge_two {m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m) (hm : 2 ≤ m)
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) :
    interior (f '' ({x : E | fderiv ℝ f x = 0} ∩ K)) = ∅ := by
  refine interior_eq_empty_of_holder f _ 2 (by norm_num) (Work.Sard.holder_two_fderiv_eq_zero f hf K) ?_
  rw [hE, hF]
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith


/-! ### The flat case for `m = 1` -/

/-- `fderiv` of a smooth map is smooth. -/
lemma contDiff_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
  (contDiff_infty_iff_fderiv.mp hf).2

/-- A finite union of sets of Hausdorff dimension at most `c` has Hausdorff dimension at most `c`. -/
lemma dimH_biUnion_finset_le {X : Type*} [EMetricSpace X] {ι : Type*} (t : Finset ι)
    (g : ι → Set X) (c : ℝ≥0∞) (h : ∀ i ∈ t, dimH (g i) ≤ c) :
    dimH (⋃ i ∈ t, g i) ≤ c := by
  have hEq : (⋃ i ∈ t, g i) = ⋃ i : {i // i ∈ t}, g i := by ext y; simp
  rw [hEq, dimH_iUnion]
  exact iSup_le fun i => h i i.2

/-- The image of the twice-flat set `{fderiv f = 0 ∧ fderiv (fderiv f) = 0}` has Hausdorff dimension
at most `2/3` when `finrank ℝ E = 2`. -/
lemma dimH_image_flat_two_set_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = 2) (hF : Module.finrank ℝ F = 1)
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) :
    dimH (f '' ({x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K)) ≤
      2 / 3 := by
  refine (dimH_image_le_of_locally_holder_on (r := 3) (by norm_num)
    (Work.Sard.holder_three_snd_fderiv_eq_zero f hf K)).trans ?_
  have h2 : dimH ({x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K)
      ≤ (2 : ℝ≥0∞) := by
    calc dimH ({x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K)
        ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ _)
      _ = ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) := Real.dimH_univ_eq_finrank E
      _ = 2 := by rw [hE]; norm_num
  exact (ENNReal.div_le_div_right h2 3).trans_eq (by norm_num)

/-- The image of the flat-but-not-twice-flat set has Hausdorff dimension at most `1/2`
when `finrank ℝ E = 2`. -/
lemma dimH_image_flat_one_crit_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = 2) (hF : Module.finrank ℝ F = 1)
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) (hK : IsCompact K) :
    dimH (f '' (({x : E | fderiv ℝ f x = 0} \
      {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K)) ≤ 1 / 2 := by
  classical
  have hf' := contDiff_fderiv hf
  have key : ∀ x ∈ ({x : E | fderiv ℝ f x = 0} \
      {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K,
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        dimH (f '' ({y : E | fderiv ℝ f y = 0} ∩ (U ∩ K))) ≤ 1 / 2 := by
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq] at hx
    obtain ⟨⟨hx0, hx1⟩, -⟩ := hx
    have hB : fderiv ℝ (fun y : E => fderiv ℝ f y) x ≠ 0 := hx1
    obtain ⟨v₁, hv₁⟩ : ∃ v : E, (fderiv ℝ (fun y : E => fderiv ℝ f y) x) v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (ContinuousLinearMap.ext fun v => by simpa using hc v)
    obtain ⟨v₂, hv₂⟩ :
        ∃ v : E, ((fderiv ℝ (fun y : E => fderiv ℝ f y) x) v₁) v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv₁ (ContinuousLinearMap.ext fun v => by simpa using hc v)
    obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_ne_zero (V := F) ℝ hv₂
    let l : F →L[ℝ] ℝ := ⟨l₀, LinearMap.continuous_of_finiteDimensional l₀⟩
    have hlw : l (((fderiv ℝ (fun y : E => fderiv ℝ f y) x) v₁) v₂) ≠ 0 := hl₀
    have hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : E => l ((fderiv ℝ f y) v₂)) := by
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => (fderiv ℝ f y) v₂) := by
        simpa only [ContinuousLinearMap.apply_apply] using
          (ContDiff.clm_apply (f := fun _ : E => (ContinuousLinearMap.apply ℝ F) v₂)
            contDiff_const hf')
      exact l.contDiff.comp h1
    have hgx0 : l ((fderiv ℝ f x) v₂) = 0 := by
      rw [hx0]; simp
    have hg_ne : fderiv ℝ (fun y : E => l ((fderiv ℝ f y) v₂)) x ≠ 0 := by
      have hc' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fun y : E => fderiv ℝ f y) x) x :=
        ((hf'.differentiable (by simp)).differentiableAt).hasFDerivAt
      have h1 : HasFDerivAt (fun y : E => (fderiv ℝ f y) v₂)
          ((fderiv ℝ (fun y : E => fderiv ℝ f y) x).flip v₂) x := by
        have h := hc'.clm_apply (hasFDerivAt_const v₂ x)
        simpa using h
      have h2 : HasFDerivAt (fun y : E => l ((fderiv ℝ f y) v₂))
          (l.comp ((fderiv ℝ (fun y : E => fderiv ℝ f y) x).flip v₂)) x :=
        (ContinuousLinearMap.hasFDerivAt l).comp x h1
      rw [h2.fderiv]
      intro hzero
      have h3 : (l.comp ((fderiv ℝ (fun y : E => fderiv ℝ f y) x).flip v₂)) v₁ = 0 := by
        rw [hzero]; rfl
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h3
      exact hlw h3
    obtain ⟨t, ht, hdt⟩ := Work.Sard.dimH_levelSet_le (fun y : E => l ((fderiv ℝ f y) v₂))
      hg_smooth x hg_ne
    have hdt' : dimH ({y : E | l ((fderiv ℝ f y) v₂) = 0} ∩ t) ≤ 1 := by
      rw [hgx0] at hdt
      refine hdt.trans (le_of_eq ?_)
      rw [hE, show ((2 : ℕ) : ℝ≥0∞) = 1 + 1 by norm_num]
      exact ENNReal.add_sub_cancel_right (by simp)
    have hsub : {y : E | fderiv ℝ f y = 0} ∩ (interior t ∩ K) ⊆
        {y : E | l ((fderiv ℝ f y) v₂) = 0} ∩ t := by
      intro y hy
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hy
      obtain ⟨hy0, hyt, -⟩ := hy
      exact ⟨by simp only [Set.mem_ofPred_eq]; rw [hy0]; simp, interior_subset hyt⟩
    have hle : dimH ({y : E | fderiv ℝ f y = 0} ∩ (interior t ∩ K)) ≤ 1 :=
      (dimH_mono hsub).trans hdt'
    have hH := Work.Sard.holder_two_fderiv_eq_zero f hf (interior t ∩ K)
    have hfin : dimH (f '' ({y : E | fderiv ℝ f y = 0} ∩ (interior t ∩ K))) ≤ 1 / 2 :=
      (dimH_image_le_of_locally_holder_on (r := 2) (by norm_num) hH).trans
        (ENNReal.div_le_div_right hle 2)
    exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht, hfin⟩
  -- cover the interesting set by the countably many compact sets
  -- `Lₙ = {fderiv f = 0} ∩ K ∩ {fderiv (fderiv f) ∉ ball 0 (1/(n+1))}`
  have hdecomp : (({x : E | fderiv ℝ f x = 0} \
      {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K) ⊆
      ⋃ n : ℕ, ({x : E | fderiv ℝ f x = 0} ∩ K ∩
        ((fderiv ℝ (fun y : E => fderiv ℝ f y)) ⁻¹'
          (Metric.ball (0 : E →L[ℝ] (E →L[ℝ] F)) (1 / (n + 1 : ℝ))))ᶜ) := by
    rintro x ⟨⟨hx0, hx1⟩, hxK⟩
    have hx1' : fderiv ℝ (fun y : E => fderiv ℝ f y) x ≠ 0 := hx1
    have hpos : 0 < dist (fderiv ℝ (fun y : E => fderiv ℝ f y) x) 0 := dist_pos.mpr hx1'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine Set.mem_iUnion.mpr ⟨n, ⟨⟨hx0, hxK⟩, ?_⟩⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, not_lt]
    exact le_of_lt hn
  have houter : dimH (f '' (({x : E | fderiv ℝ f x = 0} \
      {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K)) ≤
      ⨆ n : ℕ, dimH (f '' ({x : E | fderiv ℝ f x = 0} ∩ K ∩
        ((fderiv ℝ (fun y : E => fderiv ℝ f y)) ⁻¹'
          (Metric.ball (0 : E →L[ℝ] (E →L[ℝ] F)) (1 / (n + 1 : ℝ))))ᶜ)) := by
    refine (dimH_mono (Set.image_mono hdecomp)).trans ?_
    rw [Set.image_iUnion, dimH_iUnion]
  refine houter.trans (iSup_le fun n => ?_)
  set Ln : Set E := {x : E | fderiv ℝ f x = 0} ∩ K ∩
      ((fderiv ℝ (fun y : E => fderiv ℝ f y)) ⁻¹'
        (Metric.ball (0 : E →L[ℝ] (E →L[ℝ] F)) (1 / (n + 1 : ℝ))))ᶜ with hLn
  have hmem : ∀ x ∈ Ln, x ∈ ({x : E | fderiv ℝ f x = 0} \
      {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K := by
    intro x hx
    rw [hLn] at hx
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball,
      not_lt, Set.mem_setOf_eq] at hx
    obtain ⟨⟨hxA, hxK⟩, hxineq⟩ := hx
    refine ⟨⟨hxA, ?_⟩, hxK⟩
    intro hzero
    have hzero' : fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0 := hzero
    rw [hzero'] at hxineq
    rw [dist_self] at hxineq
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact one_div_pos.mpr this
    exact absurd hxineq (not_le_of_gt hpos)
  have hLc : IsCompact Ln := by
    rw [hLn]
    have hA : IsClosed {x : E | fderiv ℝ f x = 0} :=
      isClosed_eq (hf.continuous_fderiv (by norm_num)) continuous_const
    have hB : IsClosed ((fderiv ℝ (fun y : E => fderiv ℝ f y)) ⁻¹'
        (Metric.ball (0 : E →L[ℝ] (E →L[ℝ] F)) (1 / (n + 1 : ℝ))))ᶜ :=
      ((hf'.continuous_fderiv (by norm_num)).isOpen_preimage _
        Metric.isOpen_ball).isClosed_compl
    exact IsCompact.inter_right (IsCompact.inter_left hK hA) hB
  have keyLn : ∀ x : Ln, ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧
      dimH (f '' ({y : E | fderiv ℝ f y = 0} ∩ (U ∩ K))) ≤ 1 / 2 :=
    fun x => key x.1 (hmem x.1 x.2)
  choose U hUop hxU hUdim using keyLn
  let V : E → Set E := fun x => if h : x ∈ Ln then U ⟨x, h⟩ else ∅
  have hVopen : ∀ x : E, IsOpen (V x) := by
    intro x
    by_cases h : x ∈ Ln
    · rw [show V x = U ⟨x, h⟩ from dif_pos h]; exact hUop ⟨x, h⟩
    · rw [show V x = ∅ from dif_neg h]; exact isOpen_empty
  have hVdim : ∀ x : E, dimH (f '' ({y : E | fderiv ℝ f y = 0} ∩ (V x ∩ K))) ≤ 1 / 2 := by
    intro x
    by_cases h : x ∈ Ln
    · rw [show V x = U ⟨x, h⟩ from dif_pos h]; exact hUdim ⟨x, h⟩
    · rw [show V x = ∅ from dif_neg h]
      simp
  obtain ⟨s, hs⟩ := hLc.elim_finite_subcover V hVopen (fun x hx => by
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    rw [show V x = U ⟨x, hx⟩ from dif_pos hx]
    exact hxU ⟨x, hx⟩)
  have hsub2 : f '' Ln ⊆ ⋃ x ∈ s, f '' ({y : E | fderiv ℝ f y = 0} ∩ (V x ∩ K)) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨i, hi, hyV⟩ := Set.mem_iUnion₂.mp (hs hy)
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    refine Set.mem_image_of_mem f ⟨?_, hyV, ?_⟩
    · rw [hLn] at hy; exact hy.1.1
    · rw [hLn] at hy; exact hy.1.2
  refine le_trans (dimH_mono hsub2) (dimH_biUnion_finset_le s
    (fun x => f '' ({y : E | fderiv ℝ f y = 0} ∩ (V x ∩ K))) (1 / 2)
    fun x _ => hVdim x)


/-- **Flat case for `m = 1`.**  The image of `{fderiv f = 0}` has empty interior. -/
lemma flat_case_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = 2) (hF : Module.finrank ℝ F = 1)
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) (hK : IsCompact K) :
    interior (f '' ({x : E | fderiv ℝ f x = 0} ∩ K)) = ∅ := by
  have hsplit : ({x : E | fderiv ℝ f x = 0} ∩ K) =
      ({x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K) ∪
      (({x : E | fderiv ℝ f x = 0} \
        {x : E | fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0}) ∩ K) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
    tauto
  refine interior_eq_empty_of_dimH_lt ?_
  rw [hsplit, Set.image_union, hF, dimH_union]
  rw [max_lt_iff]
  constructor
  · refine lt_of_le_of_lt (dimH_image_flat_two_set_le hE hF f hf K) ?_
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  · refine lt_of_le_of_lt (dimH_image_flat_one_crit_le hE hF f hf K hK) ?_
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num

/-- **The weak Sard statement at level `m`, in `def` form.**  For a smooth map `f : E → F` between
finite dimensional real normed spaces with `finrank ℝ E = m + 1` and `finrank ℝ F = m`, the critical
values on a compact set have empty interior.

It is stated as a `def` (rather than as an explicit `∀`-statement) on purpose: the universe levels of
`E` and `F` are then *parameters of the definition*, so that every use of the statement can be
instantiated at its own universe levels.  This is what makes it usable as an induction hypothesis
for `Work.Sard.rank_chart_aux`. -/
def WeakSardAt (m : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
    Module.finrank ℝ E = m + 1 → Module.finrank ℝ F = m →
    ∀ (f : E → F), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ∀ K : Set E, IsCompact K →
      interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K)) = ∅

/-- **Chart at a non-flat critical point**, with the induction hypothesis in the `def`-form
`Work.Sard.WeakSardAt` so that it can be applied to the submodule types `ker (fderiv ℝ u x₀)` and
`W'` (which live in the universes of `E` and `F` respectively). -/
theorem rank_chart_aux {m : ℕ} {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ (m' : ℕ), m' < m → WeakSardAt.{u, v} m')
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) (hK : IsCompact K)
    (x₀ : E) (hcrit : ¬ Function.Surjective (fderiv ℝ f x₀)) (hne : fderiv ℝ f x₀ ≠ 0) :
    ∃ C : Set E, IsCompact C ∧ x₀ ∈ interior C ∧
      interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K ∩ C)) = ∅ := by

  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- ## The derivative `A = fderiv ℝ f x₀` and its range `A.range`
  set A : E →L[ℝ] F := fderiv ℝ f x₀ with hA
  have hfA : HasFDerivAt f A x₀ := by
    rw [hA]; exact (hf.differentiable hn).differentiableAt.hasFDerivAt
  have hr_le : Module.finrank ℝ A.range ≤ m := by rw [← hF]; exact Submodule.finrank_le _
  have hW_ne_top : A.range ≠ ⊤ := fun h => hcrit (LinearMap.range_eq_top.mp h)
  have hr_lt : Module.finrank ℝ A.range < m := by rw [← hF]; exact Submodule.finrank_lt hW_ne_top
  have hr_pos : 1 ≤ Module.finrank ℝ A.range := by
    by_contra h
    have h0 : Module.finrank ℝ A.range = 0 := by omega
    have hbot : A.range = ⊥ := Submodule.finrank_eq_zero.mp h0
    refine hne ?_
    ext v
    exact (Submodule.eq_bot_iff _).mp hbot (A v)
      (show A v ∈ (A : E →ₗ[ℝ] F).range from LinearMap.mem_range_self _ v)
  -- ## A complement `W'` of the range, and the projections
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl A.range
  have hW'fin : Module.finrank ℝ W' = m - Module.finrank ℝ A.range := by
    have h := Submodule.finrank_add_eq_of_isCompl hW'
    rw [hF] at h
    omega
  let P : F →ₗ[ℝ] A.range := Submodule.projectionOnto A.range W' hW'
  let P' : F →ₗ[ℝ] W' := Submodule.projectionOnto W' A.range hW'.symm
  let pw : F →L[ℝ] A.range := P.toContinuousLinearMap
  let pw' : F →L[ℝ] W' := P'.toContinuousLinearMap
  let Lf : F ≃L[ℝ] A.range × W' :=
    ((Submodule.prodEquivOfIsCompl A.range W' hW').symm).toContinuousLinearEquiv
  have hLf_apply : ∀ y : F, Lf y = (pw y, pw' y) := fun y =>
    Submodule.prodEquivOfIsCompl_symm_apply hW' y
  -- ## The map `u = π_W ∘ f : E → W` and the submersion chart
  let u : E → A.range := fun x => pw (f x)
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := pw.contDiff.comp hf
  have hfu₀ : fderiv ℝ u x₀ = pw.comp A := by
    have h : HasFDerivAt u (pw.comp A) x₀ := pw.hasFDerivAt.comp x₀ hfA
    exact h.fderiv
  have hsurj : Function.Surjective (fderiv ℝ u x₀) := by
    rw [hfu₀]
    intro y
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp y.2
    have hv' : (A v : F) = (y : F) := by simpa using hv
    refine ⟨v, ?_⟩
    show pw (A v) = y
    rw [hv']
    exact Submodule.projectionOnto_apply_left hW' y
  have hfinr : Module.finrank ℝ (fderiv ℝ u x₀).range = Module.finrank ℝ A.range := by
    have hrt : (fderiv ℝ u x₀).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [hrt, finrank_top]
  have hkr_sum : Module.finrank ℝ (fderiv ℝ u x₀).ker + Module.finrank ℝ A.range = m + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ u x₀ : E →L[ℝ] A.range) : E →ₗ[ℝ] A.range)
    rw [hfinr, hE] at h
    omega
  have hkrfin : Module.finrank ℝ (fderiv ℝ u x₀).ker = (m - Module.finrank ℝ A.range) + 1 := by
    omega
  obtain ⟨Cr, hCr⟩ := Submodule.exists_isCompl (fderiv ℝ u x₀).ker
  let π₀ : E →ₗ[ℝ] (fderiv ℝ u x₀).ker :=
    Submodule.projectionOnto (fderiv ℝ u x₀).ker Cr hCr
  let π : E →L[ℝ] (fderiv ℝ u x₀).ker := π₀.toContinuousLinearMap
  obtain ⟨Φ, O, hOopen, hy₀O, hΦsm, hΦfst, hΦbase, hΦΘ⟩ :=
    submersion_smooth u hu x₀ hsurj Cr hCr
  let y₀ : A.range × (fderiv ℝ u x₀).ker := (u x₀, π x₀)
  let Θ : E → A.range × (fderiv ℝ u x₀).ker := fun x => (u x, π x)
  have hΘc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := hu.prodMk π.contDiff
  -- ## The smooth map `ĝ = π_{W'} ∘ f ∘ Φ` on `O` and its global extension `gG`
  let ĝ : A.range × (fderiv ℝ u x₀).ker → W' := fun y => pw' (f (Φ y))
  have hĝsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ĝ O := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : A.range × (fderiv ℝ u x₀).ker => f (Φ y)) O :=
      hf.contDiffOn.comp hΦsm (Set.mapsTo_univ _ _)
    exact pw'.contDiff.comp_contDiffOn h1
  obtain ⟨gG, hgGsm, hgGeq⟩ :=
    exists_contDiff_eq_nhds_of_finiteDimensional ĝ y₀ O (hOopen.mem_nhds hy₀O) hĝsm
  let Ψ : A.range × (fderiv ℝ u x₀).ker → A.range × W' := fun z => (z.1, gG z)
  -- ## The open neighbourhood `T` of `x₀` on which all the identifications hold
  have hGTend : {x : E | gG (Θ x) = ĝ (Θ x)} ∈ nhds x₀ :=
    hgGeq.comp_tendsto hΘc.continuous.continuousAt
  have hT1 : {x : E | Φ (Θ x) = x} ∈ nhds x₀ := by
    filter_upwards [hΦΘ] with x hx
    show Φ (u x, π x) = x
    exact hx
  let T : Set E := interior {x : E | Φ (Θ x) = x} ∩ Θ ⁻¹' O ∩
    interior {x : E | gG (Θ x) = ĝ (Θ x)}
  have hTopen : IsOpen T :=
    (isOpen_interior.inter (hOopen.preimage hΘc.continuous)).inter isOpen_interior
  have hTmem : T ∈ nhds x₀ := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hT1)
    · exact (hOopen.preimage hΘc.continuous).mem_nhds hy₀O
    · exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hGTend)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hTmem
  -- ## The closed ball `L` about the base point where `gG = ĝ`
  have hV : O ∩ {y : A.range × (fderiv ℝ u x₀).ker | gG y = ĝ y} ∈ nhds y₀ :=
    Filter.inter_mem (hOopen.mem_nhds hy₀O) hgGeq
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hV
  let L : Set (A.range × (fderiv ℝ u x₀).ker) := closedBall y₀ (δ / 2)
  have hLsub : L ⊆ O ∩ {y | gG y = ĝ y} := by
    intro y hy
    apply hδsub
    rw [Metric.mem_ball]
    have h2 : dist y y₀ ≤ δ / 2 := hy
    linarith
  have hLc : IsCompact L := ProperSpace.isCompact_closedBall y₀ (δ / 2)
  -- ## The compact neighbourhood `C` of `x₀`
  let C : Set E := Θ ⁻¹' L ∩ closedBall x₀ (ε / 2)
  have hCclosed : IsClosed (Θ ⁻¹' L) := hLc.isClosed.preimage hΘc.continuous
  have hCc : IsCompact C := by
    show IsCompact (Θ ⁻¹' L ∩ closedBall x₀ (ε / 2))
    rw [Set.inter_comm]
    exact (ProperSpace.isCompact_closedBall x₀ (ε / 2)).inter_right hCclosed
  have hx₀C : x₀ ∈ interior C := by
    show x₀ ∈ interior (Θ ⁻¹' L ∩ closedBall x₀ (ε / 2))
    have hy₀int : y₀ ∈ interior L :=
      interior_maximal Metric.ball_subset_closedBall isOpen_ball
        (Metric.mem_ball_self (by positivity))
    have h1 : x₀ ∈ interior (Θ ⁻¹' L) :=
      interior_maximal (Set.preimage_mono interior_subset)
        (isOpen_interior.preimage hΘc.continuous) hy₀int
    have h2 : x₀ ∈ interior (closedBall x₀ (ε / 2)) :=
      mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds x₀ (by positivity))
    rw [interior_inter]
    exact ⟨h1, h2⟩
  -- ## The slice lemma: the critical values of `Ψ` on `L` have empty interior
  have hlt : m - Module.finrank ℝ A.range < m := by omega
  have hsliceIH : ∀ g : (fderiv ℝ u x₀).ker → W', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∀ L : Set (fderiv ℝ u x₀).ker, IsCompact L →
        interior (g '' ({x : (fderiv ℝ u x₀).ker |
          ¬ Function.Surjective (fderiv ℝ g x)} ∩ L)) = ∅ :=
    IH (m - Module.finrank ℝ A.range) hlt ↥((fderiv ℝ u x₀).ker) ↥W' hkrfin hW'fin
  have hslice : interior (Ψ '' ({z : A.range × (fderiv ℝ u x₀).ker |
      ¬ Function.Surjective (fderiv ℝ Ψ z)} ∩ L)) = ∅ :=
    slice_image_interior_eq_empty (G := A.range) (C := (fderiv ℝ u x₀).ker) (W := W')
      (m' := m - Module.finrank ℝ A.range) hkrfin hW'fin hsliceIH gG hgGsm L hLc
  -- ## Pointwise identification `Lf ∘ f = Ψ ∘ Θ` on `T`
  have hLfΨ : ∀ x ∈ T, Lf (f x) = Ψ (Θ x) := by
    intro x hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hxΦ : Φ (Θ x) = x := by
      have h := interior_subset hx1
      exact h
    have hxG : gG (Θ x) = ĝ (Θ x) := by
      have h := interior_subset hx3
      exact h
    have h3 : pw' (f x) = gG (Θ x) := by
      have h4 : pw' (f x) = pw' (f (Φ (Θ x))) := by rw [hxΦ]
      rw [h4]
      exact hxG.symm
    rw [hLf_apply (f x), h3]
  -- ## Transfer of the derivative along `Lf
  have hderiv : ∀ x ∈ T, (Lf : F →L[ℝ] A.range × W').comp (fderiv ℝ f x) = (fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x) := by
    intro x hx
    have hev : (fun x' => Lf (f x')) =ᶠ[nhds x] (fun x' => Ψ (Θ x')) := by
      filter_upwards [hTopen.mem_nhds hx] with x' hx'
      exact hLfΨ x' hx'
    have h1 : fderiv ℝ (fun x' => Lf (f x')) x = (Lf : F →L[ℝ] A.range × W').comp (fderiv ℝ f x) :=
      ((Lf : F →L[ℝ] A.range × W').hasFDerivAt.comp x
        ((hf.differentiable hn).differentiableAt.hasFDerivAt)).fderiv
    have h2 : fderiv ℝ (fun x' => Ψ (Θ x')) x
        = (fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x) := by
      have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (Θ x)) (Θ x) :=
        ((differentiableAt_fst (p := Θ x)).prodMk ((hgGsm.differentiable hn).differentiableAt)).hasFDerivAt
      have hΘd : HasFDerivAt Θ (fderiv ℝ Θ x) x :=
        ((hΘc.differentiable hn).differentiableAt).hasFDerivAt
      exact (hΨd.comp x hΘd).fderiv
    have hfd : fderiv ℝ (fun x' => Lf (f x')) x = fderiv ℝ (fun x' => Ψ (Θ x')) x :=
      hev.fderiv_eq
    rw [h1, h2] at hfd
    exact hfd
  -- ## `dΘ x` is an isomorphism for `x ∈ T`
  have hΘsurj : ∀ x ∈ T, Function.Surjective (fderiv ℝ Θ x) := by
    intro x hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hinj : Function.Injective (fderiv ℝ Θ x) := by
      have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (Θ x)) (Θ x) :=
        (((hΦsm.contDiffAt (hOopen.mem_nhds hx2)).differentiableAt hn)).hasFDerivAt
      have hΘd : HasFDerivAt Θ (fderiv ℝ Θ x) x :=
        ((hΘc.differentiable hn).differentiableAt).hasFDerivAt
      have hcomp : fderiv ℝ (fun x' => Φ (Θ x')) x
          = (fderiv ℝ Φ (Θ x)).comp (fderiv ℝ Θ x) := (hΦd.comp x hΘd).fderiv
      have hev : (fun x' : E => Φ (Θ x')) =ᶠ[nhds x] id :=
        mem_of_superset (isOpen_interior.mem_nhds hx1) interior_subset
      have hid : (fderiv ℝ Φ (Θ x)).comp (fderiv ℝ Θ x) = ContinuousLinearMap.id ℝ E := by
        rw [← hcomp, hev.fderiv_eq]
        simp
      have hid' : ∀ w : E, w = (fderiv ℝ Φ (Θ x)) (fderiv ℝ Θ x w) := by
        intro w
        have hcon := congrArg (fun (L : E →L[ℝ] E) => L w) hid
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcon
        exact hcon.symm
      intro u v huv
      calc u = (fderiv ℝ Φ (Θ x)) (fderiv ℝ Θ x u) := hid' u
        _ = (fderiv ℝ Φ (Θ x)) (fderiv ℝ Θ x v) := by rw [huv]
        _ = v := (hid' v).symm
    have hdim : Module.finrank ℝ E = Module.finrank ℝ (A.range × (fderiv ℝ u x₀).ker) := by
      rw [Module.finrank_prod]
      omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E)
      (V₂ := A.range × (fderiv ℝ u x₀).ker) hdim
      (f := ((fderiv ℝ Θ x : E →L[ℝ] A.range × (fderiv ℝ u x₀).ker) :
        E →ₗ[ℝ] A.range × (fderiv ℝ u x₀).ker))).mp hinj
  -- ## Criticality transfers along `Lf`
  have hcritiff : ∀ x ∈ T, (¬ Function.Surjective (fderiv ℝ f x)) ↔
      (¬ Function.Surjective (fderiv ℝ Ψ (Θ x))) := by
    intro x hx
    have hd := hderiv x hx
    have hΘs := hΘsurj x hx
    constructor
    · intro h hΨ
      have hcomp : Function.Surjective ((Lf : F →L[ℝ] A.range × W').comp (fderiv ℝ f x)) := by
        rw [hd]
        intro y
        obtain ⟨w, hw⟩ := hΨ y
        obtain ⟨v, hv⟩ := hΘs w
        exact ⟨v, by rw [ContinuousLinearMap.comp_apply, hv, hw]⟩
      refine h ?_
      intro y
      obtain ⟨v, hv⟩ := hcomp (Lf y)
      exact ⟨v, Lf.injective hv⟩
    · intro h hf'
      have hcomp : Function.Surjective ((fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x)) := by
        rw [← hd]
        intro y
        obtain ⟨v, hv⟩ := hf' (Lf.symm y)
        refine ⟨v, ?_⟩
        rw [ContinuousLinearMap.comp_apply, hv]
        exact Lf.apply_symm_apply y
      refine h ?_
      intro y
      obtain ⟨v, hv⟩ := hcomp y
      exact ⟨fderiv ℝ Θ x v, hv⟩
  -- ## The critical values of `f` on `K ∩ C` are the critical values of `Ψ` on `L`
  have hsub : f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K ∩ C) ⊆
      Lf.symm '' (Ψ '' ({z : A.range × (fderiv ℝ u x₀).ker |
        ¬ Function.Surjective (fderiv ℝ Ψ z)} ∩ L)) := by
    rintro y ⟨x, ⟨⟨hxcrit, hxK⟩, hxL, hxball⟩, rfl⟩
    have hxT : x ∈ T := by
      apply hεsub
      rw [Metric.mem_ball]
      have h2 : dist x x₀ ≤ ε / 2 := hxball
      linarith
    refine ⟨Ψ (Θ x), ?_, ?_⟩
    · exact ⟨Θ x, ⟨⟨(hcritiff x hxT).mp hxcrit, hxL⟩, rfl⟩⟩
    · rw [← hLfΨ x hxT]
      exact Lf.symm_apply_apply (f x)
  -- ## A homeomorphism preserves empty interior
  have hsymm : interior (Lf.symm '' (Ψ '' ({z : A.range × (fderiv ℝ u x₀).ker |
      ¬ Function.Surjective (fderiv ℝ Ψ z)} ∩ L))) = ∅ := by
    have hh := Homeomorph.image_interior (Lf.symm.toHomeomorph)
      (Ψ '' ({z : A.range × (fderiv ℝ u x₀).ker |
        ¬ Function.Surjective (fderiv ℝ Ψ z)} ∩ L))
    rw [hslice, Set.image_empty] at hh
    exact hh.symm
  refine ⟨C, hCc, hx₀C, ?_⟩
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  have h1 : y ∈ interior (Lf.symm '' (Ψ '' ({z : A.range × (fderiv ℝ u x₀).ker |
      ¬ Function.Surjective (fderiv ℝ Ψ z)} ∩ L))) := interior_mono hsub hy
  rw [hsymm] at h1
  exact h1

/-- **Weak Sard's theorem at every level**, by strong induction on `m`.  The "flat" stratum is
`flat_case_one` / `flat_case_ge_two` (Hausdorff dimension estimates); the
non-flat stratum is covered by the chart lemma `Work.Sard.rank_chart_aux`, whose induction
hypothesis is the statement at the lower level `m - r` of the rank `r` of the derivative. -/
theorem weakSardAt_all (m : ℕ) : WeakSardAt.{u, v} m := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ _ F _ _ _ hE hF f hf K hK
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hsub : Subsingleton F := Module.finrank_zero_iff.mp (by simpa using hF)
      have hcrit : {x : E | ¬ Function.Surjective (fderiv ℝ f x)} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hx ?_
        intro y
        exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩
      rw [hcrit, Set.empty_inter, Set.image_empty, interior_empty]
    · -- `m ≥ 1`
      have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
      have hcrit_closed : IsClosed {x : E | ¬ Function.Surjective (fderiv ℝ f x)} :=
        isClosed_setOf_not_surjective_fderiv f hf1
      set X1 : Set E := {x : E | fderiv ℝ f x = 0} with hX1
      -- the flat part
      have hflat : interior (f '' (X1 ∩ K)) = ∅ := by
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1 : m = 1 := by omega
          refine flat_case_one (E := E) (F := F) ?_ ?_ f hf K hK
          · rw [hE, hm1]
          · rw [hF, hm1]
        · exact flat_case_ge_two hE hF hm2 f hf K
      -- the pieces where the derivative does not vanish
      have hpieces : ∀ n : ℕ, interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩
          (K ∩ ((fderiv ℝ f) ⁻¹' (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ))) = ∅ := by
        intro n
        set L : Set E := K ∩ ((fderiv ℝ f) ⁻¹'
          (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ with hL
        set A : Set E := {x : E | ¬ Function.Surjective (fderiv ℝ f x)} with hA
        show interior (f '' (A ∩ L)) = ∅
        have hLclosed : IsClosed L := hK.isClosed.inter
          ((hf.continuous_fderiv (by norm_num)).isOpen_preimage _
            Metric.isOpen_ball).isClosed_compl
        have hLc : IsCompact L := hK.of_isClosed_subset hLclosed (by rw [hL]; exact Set.inter_subset_left)
        have hAc : IsClosed A := hcrit_closed
        have hne_mem : ∀ x ∈ A ∩ L, fderiv ℝ f x ≠ 0 := by
          intro x hx hzero
          have hxL : x ∈ ((fderiv ℝ f) ⁻¹'
              (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ := by
            rw [hL] at hx; exact hx.2.2
          simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball] at hxL
          rw [hzero, dist_self] at hxL
          have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
            have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
            exact one_div_pos.mpr this
          exact hxL hpos
        have hchart : ∀ x : ↥(A ∩ L), ∃ C : Set E, IsCompact C ∧ (x : E) ∈ interior C ∧
            interior (f '' (A ∩ L ∩ C)) = ∅ := by
          intro x
          exact rank_chart_aux hE hF ih f hf L hLc x.1 x.2.1 (hne_mem x.1 x.2)
        choose C hCc hxC hCint using hchart
        let Cd : E → Set E := fun x => if h : x ∈ A ∩ L then C ⟨x, h⟩ else ∅
        have hxC' : ∀ x ∈ A ∩ L, x ∈ interior (Cd x) := by
          intro x hx
          rw [show Cd x = C ⟨x, hx⟩ from dif_pos hx]
          exact hxC ⟨x, hx⟩
        have hCdclosed : ∀ x : E, IsClosed (Cd x) := by
          intro x
          by_cases h : x ∈ A ∩ L
          · rw [show Cd x = C ⟨x, h⟩ from dif_pos h]; exact (hCc ⟨x, h⟩).isClosed
          · rw [show Cd x = ∅ from dif_neg h]; exact isClosed_empty
        have hCdempty : ∀ x : E, interior (f '' (A ∩ L ∩ Cd x)) = ∅ := by
          intro x
          by_cases h : x ∈ A ∩ L
          · rw [show Cd x = C ⟨x, h⟩ from dif_pos h]; exact hCint ⟨x, h⟩
          · rw [show Cd x = ∅ from dif_neg h]; simp
        have hcover : A ∩ L ⊆ ⋃ x, interior (Cd x) := fun x hx =>
          Set.mem_iUnion.mpr ⟨x, hxC' x hx⟩
        obtain ⟨s, hs⟩ := (IsCompact.inter_left hLc hAc).elim_finite_subcover
          (fun x => interior (Cd x)) (fun _ => isOpen_interior) hcover
        have hsub2 : f '' (A ∩ L) ⊆ ⋃ x ∈ s, f '' (A ∩ L ∩ Cd x) := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := hz
          obtain ⟨i, hi, hyC⟩ := Set.mem_iUnion₂.mp (hs hy)
          exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_image_of_mem f ⟨hy, interior_subset hyC⟩⟩
        have hsub3 : interior (f '' (A ∩ L)) ⊆ ∅ := by
          have hunion : interior (⋃ x ∈ s, f '' (A ∩ L ∩ Cd x)) = ∅ := by
            rw [show (⋃ x ∈ s, f '' (A ∩ L ∩ Cd x)) =
                ⋃ x : {x // x ∈ s}, f '' (A ∩ L ∩ Cd x) from by ext y; simp]
            refine interior_eq_empty_iUnion_isClosed (fun i => ?_) (fun i => ?_)
            · exact (IsCompact.image (IsCompact.inter_right (IsCompact.inter_left hLc hAc)
                (hCdclosed i)) hf.continuous).isClosed
            · exact hCdempty i
          rw [← hunion]
          exact interior_mono hsub2
        exact Set.eq_empty_iff_forall_notMem.mpr fun y hy => hsub3 hy

      -- assemble everything
      have hsub : ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K) ⊆
          (X1 ∩ K) ∪ ⋃ n : ℕ, ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩
            (K ∩ ((fderiv ℝ f) ⁻¹' (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ)) := by
        rintro x ⟨hxcrit, hxK⟩
        by_cases h0 : fderiv ℝ f x = 0
        · exact Or.inl ⟨h0, hxK⟩
        · right
          have hpos : 0 < dist (fderiv ℝ f x) 0 := dist_pos.mpr h0
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
          refine Set.mem_iUnion.mpr ⟨n, hxcrit, hxK, ?_⟩
          simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, not_lt]
          exact le_of_lt hn
      let G : Option ℕ → Set F := fun o => match o with
        | none => f '' (X1 ∩ K)
        | some n => f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩
            (K ∩ ((fderiv ℝ f) ⁻¹' (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ))
      have hclosedG : ∀ o : Option ℕ, IsClosed (G o) := by
        intro o
        cases o with
        | none =>
          have : IsCompact (X1 ∩ K) := by
            refine IsCompact.inter_left hK ?_
            exact isClosed_eq (hf.continuous_fderiv (by norm_num)) continuous_const
          exact this.image hf.continuous |>.isClosed
        | some n =>
          have hLn : IsClosed (K ∩ ((fderiv ℝ f) ⁻¹'
              (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ) :=
            hK.isClosed.inter ((hf.continuous_fderiv (by norm_num)).isOpen_preimage _
              Metric.isOpen_ball).isClosed_compl
          have : IsCompact ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩
              (K ∩ ((fderiv ℝ f) ⁻¹' (Metric.ball (0 : E →L[ℝ] F) (1 / (n + 1 : ℝ))))ᶜ)) :=
            IsCompact.inter_left (hK.of_isClosed_subset hLn Set.inter_subset_left) hcrit_closed
          exact this.image hf.continuous |>.isClosed
      have hemptyG : ∀ o : Option ℕ, interior (G o) = ∅ := by
        intro o
        cases o with
        | none => exact hflat
        | some n => exact hpieces n
      have hsubG : f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K) ⊆ ⋃ o, G o := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := hz
        rcases hsub hy with hyflat | hyn
        · exact Set.mem_iUnion.mpr ⟨none, Set.mem_image_of_mem f hyflat⟩
        · obtain ⟨n, hyn'⟩ := Set.mem_iUnion.mp hyn
          exact Set.mem_iUnion.mpr ⟨some n, Set.mem_image_of_mem f hyn'⟩
      have hmain := interior_eq_empty_iUnion_isClosed hclosedG hemptyG
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have h3 : interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K)) ⊆
          interior (⋃ o : Option ℕ, G o) := interior_mono hsubG
      rw [hmain] at h3
      exact h3 hy

/-- **Chart at a non-flat critical point.**  If `x₀` is critical and `fderiv ℝ f x₀ ≠ 0`, then there
is a *compact* neighbourhood `C` of `x₀` whose contribution to the critical values has empty interior.
(The conclusion is a strengthening, at the same path, of the reviewed "∃ open V" version: a compact
neighbourhood is what the caller's finite-subcover argument needs.)

Proof sketch: let `W := (fderiv ℝ f x₀).range`, `r := finrank ℝ W ≥ 1`, let `W'` be a complement of `W`
in `F`, `Kr := ker (fderiv ℝ f x₀)`, and let `Cr` be a complement of `Kr`.  Put
`u := π_W ∘ f : E → W`; its derivative at `x₀` is surjective with kernel `Kr`.  Apply
`Work.Sard.submersion_smooth` to `u` with the complement `Cr`: get `Φ : W × Kr → E` and an open
`O ∋ (u x₀, π x₀)` with `ContDiffOn ℝ ∞ Φ O`, `u (Φ y) = y.1` for `y ∈ O`, `Φ (u x₀, π x₀) = x₀` and
`Φ (u x, π x) = x` eventually near `x₀`.  Since `finrank ℝ Kr = m + 1 - r` and `finrank ℝ W' = m - r`
(with `1 ≤ r ≤ m-1`, so `m - r < m`), the induction hypothesis `IH (m-r)` applies to maps
`Kr → W'`.  Extend `ĝ := π_{W'} ∘ f ∘ Φ` (smooth on `O`) to a globally smooth `G` with `G =ᶠ ĝ` near
the base point using `Work.Sard.exists_contDiff_eq_nhds_of_finiteDimensional`, and take a small closed
ball `L` around the base point inside the region where `G = ĝ`, `Φ (u x, π x) = x` and `Θ x ∈ O`
(`Θ x := (u x, π x)`).  Apply `Work.Sard.slice_image_interior_eq_empty` to `G` and `L`, giving
`interior (Ψ '' (crit Ψ ∩ L)) = ∅` for `Ψ z = (z.1, G z)`.  Finally transport along the linear
isomorphism `Lf : F → W × W'`, `y ↦ (π_W y, π_{W'} y)`: near `x₀` one has `Lf ∘ f = Ψ ∘ Θ`, and
`dΘ` is an isomorphism there (it is injective because `Φ ∘ Θ = id` on a neighbourhood and the
dimensions `finrank ℝ E = finrank ℝ (W × Kr)` agree), so `x ∈ crit f ↔ Θ x ∈ crit Ψ` and
`f '' (crit f ∩ K ∩ C) ⊆ Lf.symm '' (Ψ '' (crit Ψ ∩ L))` for the compact set
`C := Θ ⁻¹' L ∩ closedBall x₀ ε`; a homeomorphism preserves empty interior. -/
theorem rank_chart {m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ (m' : ℕ), m' < m → ∀ (E' F' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'],
      Module.finrank ℝ E' = m' + 1 → Module.finrank ℝ F' = m' →
      ∀ (g : E' → F'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ K : Set E', IsCompact K →
        interior (g '' ({x : E' | ¬ Function.Surjective (fderiv ℝ g x)} ∩ K)) = ∅)
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) (hK : IsCompact K)
    (x₀ : E) (hcrit : ¬ Function.Surjective (fderiv ℝ f x₀)) (hne : fderiv ℝ f x₀ ≠ 0) :
    ∃ C : Set E, IsCompact C ∧ x₀ ∈ interior C ∧
      interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K ∩ C)) = ∅ :=
  -- The induction hypothesis `IH` of the statement quantifies over types in *fixed* universes,
  -- which need not be the universes of `E` and `F`; the chart argument needs the theorem at the
  -- level `m - r < m` for maps between the submodules `ker (fderiv ℝ (fderiv-projection))` and
  -- `W' ⊆ F`, i.e. in the universes of `E` and `F`.  So we use instead the self-contained strong
  -- induction `Work.Sard.weakSardAt_all` (whose statement is a `def`, hence instantiable at any
  -- pair of universe levels) — `IH` is therefore not needed.
  rank_chart_aux hE hF (fun m' _ => weakSardAt_all m') f hf K hK x₀ hcrit hne

end Work.Sard
