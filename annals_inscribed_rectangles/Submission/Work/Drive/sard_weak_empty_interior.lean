import Mathlib
import Submission.Work.Sard.block_fderiv_prodMk
import Submission.Work.Sard.holder_two_fderiv_eq_zero
import Submission.Work.Sard.holder_three_snd_fderiv_eq_zero
import Submission.Work.Sard.dimH_levelSet_le
import Submission.Work.Sard.slice_image_interior_eq_empty
import Submission.Work.Sard.submersion_param
import Submission.Work.Sard.submersion_smooth
import Submission.Work.Sard.exists_contDiff_eq_nhds_of_hasBump
import Submission.Work.Sard.rank_chart

/-!
# The weak (`empty interior`) form of Sard's theorem for maps `ℝ^{m+1} → ℝ^m`

The final theorem of this file, `Work.Drive.sard_weak_empty_interior`, says that for a smooth
map `f : E → F` between real normed spaces with `finrank E = finrank F + 1`, the critical values
of `f` on a compact set have empty interior.

The proof is by strong induction on `m = finrank ℝ F`.

* If `fderiv ℝ f x₀ = 0` ("flat" critical point) then `f` is locally `2`-Hölder on
  `{fderiv ℝ f = 0}`, so the image of that set has Hausdorff dimension at most
  `(m+1)/2 < m` for `m ≥ 2`; for `m = 1` the set is split further into the part where the second
  derivative vanishes (Hölder exponent `3`, dimension `≤ 2/3`) and the part where it does not
  (where `{fderiv f = 0}` is locally contained in a level curve, giving dimension `≤ 1`, and hence
  image dimension `≤ 1/2` after the `2`-Hölder estimate).

* If `fderiv ℝ f x₀ ≠ 0`, composing with the projection onto `range (fderiv ℝ f x₀)` and applying
  the inverse function theorem writes `f`, locally, as `(w, c) ↦ (w, g w c)` with `w` in a space of
  dimension `r ≥ 1`; the critical points are exactly the points where the slice derivative
  `c ↦ g (w, c)` is not surjective, so the induction hypothesis applies slice by slice, and a purely
  topological "box" argument finishes.
-/

namespace Work.Drive

open scoped ContDiff Topology NNReal ENNReal
open MeasureTheory Filter

/-! ### Elementary topological helpers -/

/-- **Box argument.** If each slice `S u` has empty interior, then so has the union of the
"slices" `{u} ×ˢ S u`. -/
lemma interior_iUnion_slices_eq_empty {G W : Type*} [TopologicalSpace G] [TopologicalSpace W]
    (S : G → Set W) (hS : ∀ u, interior (S u) = ∅) :
    interior (⋃ u : G, ({u} : Set G) ×ˢ S u) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro p
  rw [mem_closure_iff_nhds]
  rintro T hT
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hT
  have hnotsub : ¬ (T ⊆ ⋃ u : G, ({u} : Set G) ×ˢ S u) := by
    intro hsubT
    obtain ⟨u, hu⟩ := Filter.nonempty_of_mem hU
    have hsub : V ⊆ S u := by
      intro w' hw'
      have h1 : (u, w') ∈ (⋃ u : G, ({u} : Set G) ×ˢ S u) := hsubT (hUV ⟨hu, hw'⟩)
      obtain ⟨u', h2⟩ := Set.mem_iUnion.mp h1
      rw [Set.mem_prod] at h2
      have h3 : u' = u := (Set.mem_singleton_iff.mp h2.1).symm
      simpa [h3] using h2.2
    have hmem : p.2 ∈ interior (S u) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hV hsub)
    rw [hS u] at hmem
    exact hmem
  obtain ⟨x, hxT, hxU⟩ := Set.not_subset.mp hnotsub
  exact ⟨x, hxT, hxU⟩

/-- **Baire.** A countable union of closed sets with empty interior has empty interior. -/
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

/-- **The weak Sard statement at level `m`.**  For a smooth map `f : E → F` between finite
dimensional real normed spaces with `finrank ℝ E = m + 1` and `finrank ℝ F = m`, the critical values
on a compact set have empty interior.  (Stated as a `def` so that each use can be instantiated at
its own universe level.) -/
def WeakSardAt (m : ℕ) : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
    Module.finrank ℝ E = m + 1 → Module.finrank ℝ F = m →
    ∀ (f : E → F), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ∀ K : Set E, IsCompact K →
      interior (f '' ({x : E | ¬ Function.Surjective (fderiv ℝ f x)} ∩ K)) = ∅

theorem sard_aux_def (m : ℕ) : WeakSardAt m := by
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
          exact Work.Sard.rank_chart hE hF
            (fun m' hm' E' F' _ _ _ _ _ _ h1 h2 g hg L' hL' =>
              ih m' hm' E' F' h1 h2 g hg L' hL') f hf L hLc x.1 x.2.1 (hne_mem x.1 x.2)
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

/-- **Sard's result, weak (`empty interior`) form, for maps `ℝ^{m+1} → ℝ^m`.**  The set of critical values of a smooth map `f : ℝ^{m+1} → ℝ^m` restricted to a compact set `K` does not contain a nonempty open set.

Route: the classical Sard result says that the critical values form a *null* set; the `empty interior` conclusion is the weak consequence needed here.  One workable route, using the equal-dimension case available in this workspace and in `Mathlib` (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) as the only hard input: stratify the critical set by the rank of the derivative; the strata of rank `≤ m-1` have Hausdorff dimension `≤ m`, so their images have Hausdorff dimension `≤ m`, and near a point of rank exactly `m-1` the implicit-function normal form writes the map locally as `(u,v) ↦ (u, g u v)` with `v` one-dimensional, so that the one-variable Sard argument plus Fubini bounds the critical values near there.  Warning: applying the equal-dimension case to `x ↦ (f x, 0) ∈ ℝ^{m+1}` only shows that the graph `{(f x, 0)}` is null, which does **not** suffice; the rank stratification is the honest route. -/
theorem sard_weak_empty_interior {m : ℕ}
    (f : EuclideanSpace ℝ (Fin (m+1)) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (K : Set (EuclideanSpace ℝ (Fin (m+1)))) (hK : IsCompact K) :
    interior (f '' ({x : EuclideanSpace ℝ (Fin (m+1)) |
      ¬ Function.Surjective (fderiv ℝ f x)} ∩ K)) = ∅ := by
  have h := sard_aux_def m
  exact h (EuclideanSpace ℝ (Fin (m+1))) (EuclideanSpace ℝ (Fin m)) (by simp) (by simp) f hf K hK

end Work.Drive
