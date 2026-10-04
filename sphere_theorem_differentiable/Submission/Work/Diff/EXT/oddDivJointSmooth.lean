import Mathlib
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.factor_smul_of_vanishing_slice
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT

noncomputable section

universe u v

/-- **The slice derivative on a slab.** -/
lemma hasDerivAt_slice_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {σ : Set E} {u : ℝ × E → Z} {p : ℝ × E}
    (hp : p ∈ Set.Ioo (-T) T ×ˢ σ)
    (hd : DifferentiableWithinAt ℝ u (Set.Ioo (-T) T ×ˢ σ) p) :
    HasDerivAt (fun s : ℝ => u (s, p.2))
      (fderivWithin ℝ u (Set.Ioo (-T) T ×ˢ σ) p (1, 0)) p.1 := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hpT1, hpT2⟩ := hp1
  have hδpos : 0 < min (p.1 + T) (T - p.1) := lt_min (by linarith) (by linarith)
  have hsub : Set.Ioo (p.1 - min (p.1 + T) (T - p.1)) (p.1 + min (p.1 + T) (T - p.1))
      ⊆ Set.Ioo (-T) T := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have h := min_le_left (p.1 + T) (T - p.1); linarith [hs.1]
    · have h := min_le_right (p.1 + T) (T - p.1); linarith [hs.2]
  have hIoo : Set.Ioo (p.1 - min (p.1 + T) (T - p.1)) (p.1 + min (p.1 + T) (T - p.1)) ∈ 𝓝 p.1 :=
    IsOpen.mem_nhds isOpen_Ioo
      (show p.1 ∈ Set.Ioo (p.1 - min (p.1 + T) (T - p.1)) (p.1 + min (p.1 + T) (T - p.1)) from
        ⟨by linarith [hδpos], by linarith [hδpos]⟩)
  have h2 : HasFDerivWithinAt (fun s : ℝ => (s, p.2)) (ContinuousLinearMap.inl ℝ ℝ E)
      (Set.Ioo (p.1 - min (p.1 + T) (T - p.1)) (p.1 + min (p.1 + T) (T - p.1))) p.1 := by
    have h2at : HasFDerivAt (fun s : ℝ => ((s, (0 : E)) + ((0 : ℝ), p.2)))
        (ContinuousLinearMap.inl ℝ ℝ E) p.1 :=
      ((ContinuousLinearMap.inl ℝ ℝ E).hasFDerivAt).add_const ((0 : ℝ), p.2)
    have heq : (fun s : ℝ => (s, p.2)) = fun s : ℝ => ((s, (0 : E)) + ((0 : ℝ), p.2)) := by
      funext s; simp
    rw [heq]; exact h2at.hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun s : ℝ => u (s, p.2))
      ((fderivWithin ℝ u (Set.Ioo (-T) T ×ˢ σ) p).comp (ContinuousLinearMap.inl ℝ ℝ E))
      (Set.Ioo (p.1 - min (p.1 + T) (T - p.1)) (p.1 + min (p.1 + T) (T - p.1))) p.1 :=
    hd.hasFDerivWithinAt.comp p.1 h2
      (fun s hs => show (s, p.2) ∈ Set.Ioo (-T) T ×ˢ σ from ⟨hsub hs, hp2⟩)
  have hAt := hcomp.hasFDerivAt hIoo
  have := hAt.hasDerivAt
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using this

/-- **The slice derivative on a slab, as a `deriv`.** -/
lemma deriv_slice_eq_fderivWithin_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} {σ : Set E} {u : ℝ × E → Z} {p : ℝ × E}
    (hp : p ∈ Set.Ioo (-T) T ×ˢ σ)
    (hd : DifferentiableWithinAt ℝ u (Set.Ioo (-T) T ×ˢ σ) p) :
    deriv (fun s : ℝ => u (s, p.2)) p.1 = fderivWithin ℝ u (Set.Ioo (-T) T ×ˢ σ) p (1, 0) :=
  (hasDerivAt_slice_slab hp hd).deriv

/-- **The `τ`-derivative of a `C^{k+1}` function on a slab is `C^k`.**

Level-indexed version, on a two-sided slab with a possibly non-open parameter set. -/
theorem tDeriv_slab_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {σ : Set E} (hd : UniqueDiffOn ℝ σ) (k : ℕ)
    {u : ℝ × E → ℝ}
    (hu : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞ω) u (Set.Ioo (-T) T ×ˢ σ)) :
    ContDiffOn ℝ (k : ℕ∞ω) (fun p : ℝ × E => deriv (fun τ : ℝ => u (τ, p.2)) p.1)
      (Set.Ioo (-T) T ×ˢ σ) := by
  have hKuniq : UniqueDiffOn ℝ (Set.Ioo (-T) T ×ˢ σ) := (uniqueDiffOn_Ioo _ _).prod hd
  have hdiffOn : DifferentiableOn ℝ u (Set.Ioo (-T) T ×ˢ σ) := hu.differentiableOn (by simp)
  intro p hp
  have hbase : ContDiffWithinAt ℝ (k : ℕ∞ω)
      (fun q : ℝ × E => fderivWithin ℝ u (Set.Ioo (-T) T ×ˢ σ) q (1, 0))
      (Set.Ioo (-T) T ×ˢ σ) p :=
    (hu.contDiffWithinAt hp).fderivWithin_right_apply contDiffWithinAt_const hKuniq (le_refl _) hp
  refine hbase.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hqmem
    exact deriv_slice_eq_fderivWithin_slab hqmem (hdiffOn q hqmem)
  · exact deriv_slice_eq_fderivWithin_slab hp (hdiffOn p hp)

/-- **Single differentiation step for the two-sided ray integral.** -/
theorem rayInt_twoSided_single
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} (hT : 0 < T) {σ : Set E} (hc : Convex ℝ σ) (hd : UniqueDiffOn ℝ σ)
    {M : (ℝ × E) × ℝ → Z}
    (hM : ContDiffOn ℝ (1 : ℕ∞) M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ p ∈ Set.Ioo (-T) T ×ˢ σ,
      HasFDerivWithinAt (rayInt M)
        (rayInt (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) p)
        (Set.Ioo (-T) T ×ˢ σ) p := by
  intro p₀ hp₀
  have hTabs : |p₀.1| < T := abs_lt.mpr ⟨hp₀.1.1, hp₀.1.2⟩
  set K : Set ((ℝ × E) × ℝ) := (Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1 with hK
  have hK_unique : UniqueDiffOn ℝ K :=
    ((uniqueDiffOn_Ioo (-T) T).prod hd).prod (uniqueDiffOn_Icc zero_lt_one)
  -- membership of the "ray" points in `K`
  have hray_mem : ∀ (x : ℝ × E) (a : ℝ), x ∈ Set.Ioo (-T) T ×ˢ σ →
      a ∈ Set.Icc (0 : ℝ) 1 → ((a * x.1, x.2), a) ∈ K := by
    intro x a hx ha
    refine ⟨⟨abs_lt.mp ?_, hx.2⟩, ha⟩
    rw [abs_mul, abs_of_nonneg ha.1]
    have h2 : a * |x.1| ≤ |x.1| := by
      simpa using mul_le_mul_of_nonneg_right ha.2 (abs_nonneg x.1)
    exact lt_of_le_of_lt h2 (abs_lt.mpr ⟨hx.1.1, hx.1.2⟩)
  have hKmem' : ∀ a ∈ Set.Icc (0 : ℝ) 1, ((p₀.1 * a, p₀.2), a) ∈ K := by
    intro a ha
    simpa only [mul_comm] using hray_mem p₀ a hp₀ ha
  -- the compact family of base points of the rays through `p₀`
  set Cfam : Set ((ℝ × E) × ℝ) :=
    (fun a : ℝ => ((p₀.1 * a, p₀.2), a)) '' (Set.Icc (0 : ℝ) 1) with hCfam
  have hCfam_ne : Cfam.Nonempty :=
    ⟨((p₀.1 * 0, p₀.2), 0), 0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hCfam_sub : Cfam ⊆ K := by
    rw [hCfam]
    rintro _ ⟨a, ha, rfl⟩
    exact hKmem' a ha
  have hCfam_cpt : IsCompact Cfam := by
    rw [hCfam]
    exact IsCompact.image isCompact_Icc
      (((continuous_const.mul continuous_id).prodMk continuous_const).prodMk continuous_id)
  -- continuity of the formal derivative family on `K`
  have hRD : ContDiffOn ℝ (0 : ℕ∞) (rayDeriv K M) K := by
    have hD : ContDiffOn ℝ (0 : ℕ∞) (fun qs : (ℝ × E) × ℝ => fderivWithin ℝ M K qs) K :=
      hM.fderivWithin hK_unique (m := (0 : ℕ∞)) (by norm_num)
    have hP : ContDiffOn ℝ (0 : ℕ∞) (rayPartial K M) K := by
      have hfun : rayPartial K M = fun qs : (ℝ × E) × ℝ =>
          (fderivWithin ℝ M K qs).comp (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ) := rfl
      rw [hfun]
      exact hD.clm_comp contDiffOn_const
    have hL : ContDiffOn ℝ (0 : ℕ∞) (fun qs : (ℝ × E) × ℝ => rayL (E := E) qs.2) K :=
      ((contDiff_rayL (E := E)).of_le (by simp)).comp_contDiffOn contDiffOn_snd
    have hfun : rayDeriv K M = fun qs : (ℝ × E) × ℝ =>
        (rayPartial K M qs).comp (rayL (E := E) qs.2) := rfl
    rw [hfun]
    exact hP.clm_comp hL
  obtain ⟨rb, hrb, M₀, hM₀⟩ := exists_bound_near_compact_of_continuousWithinAt hCfam_ne
    hCfam_sub hCfam_cpt (fun qs hqs => hRD.continuousOn.continuousWithinAt hqs)
  set C₀ : ℝ := max M₀ 0 + 1 with hC₀
  -- the convex set `B` on which the slices are controlled
  set B : Set (ℝ × E) := Set.Ioo (-T) T ×ˢ σ ∩ Metric.ball p₀ rb with hB
  have hBmem : ∀ x : ℝ × E, x ∈ B ↔
      x ∈ Set.Ioo (-T) T ×ˢ σ ∧ x ∈ Metric.ball p₀ rb := by
    intro x; rw [hB, Set.mem_inter_iff]
  have hBconv : Convex ℝ B := ((convex_Ioo (-T) T).prod hc).inter (convex_ball p₀ rb)
  have hB_sub : B ⊆ Set.Ioo (-T) T ×ˢ σ := Set.inter_subset_left
  have hp₀B : p₀ ∈ B := ⟨hp₀, Metric.mem_ball_self hrb⟩
  have hB_nhds : B ∈ 𝓝[Set.Ioo (-T) T ×ˢ σ] p₀ := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.ball p₀ rb, Metric.ball_mem_nhds p₀ hrb, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  -- the family and its formal derivative
  set F : (ℝ × E) → ℝ → Z := fun x a => M ((a * x.1, x.2), a) with hF
  set F' : ℝ → (ℝ × E) →L[ℝ] Z := fun a => rayDeriv K M ((a * p₀.1, p₀.2), a) with hF'
  -- the norm bound on the formal derivative
  have hray_bound : ∀ (x : ℝ × E) (a : ℝ), x ∈ B → a ∈ Set.Icc (0:ℝ) 1 →
      ‖rayDeriv K M ((a * x.1, x.2), a)‖ ≤ C₀ := by
    intro x a hxB ha
    obtain ⟨hxslab, hxball⟩ := (hBmem x).mp hxB
    have hmemC : ((p₀.1 * a, p₀.2), a) ∈ Cfam := by rw [hCfam]; exact ⟨a, ha, rfl⟩
    have hx0 : ‖x - p₀‖ < rb := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hxball
    have hd : dist ((a * x.1, x.2), a) ((p₀.1 * a, p₀.2), a) < rb := by
      have h1 : ‖a * x.1 - p₀.1 * a‖ ≤ ‖x - p₀‖ := by
        rw [show a * x.1 - p₀.1 * a = a * (x.1 - p₀.1) by ring, Real.norm_eq_abs, abs_mul]
        refine le_trans (mul_le_of_le_one_left (abs_nonneg _) ?_) ?_
        · rw [abs_of_nonneg ha.1]; exact ha.2
        · rw [← Real.norm_eq_abs, Prod.norm_def]
          exact le_max_left _ _
      have h2 : ‖x.2 - p₀.2‖ ≤ ‖x - p₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      rw [dist_eq_norm, Prod.norm_def, Prod.norm_def]
      exact max_lt (max_lt (lt_of_le_of_lt h1 hx0) (lt_of_le_of_lt h2 hx0)) (by simpa using hrb)
    have hxK : ((a * x.1, x.2), a) ∈ K := hray_mem x a hxslab ha
    have hDbound : ‖rayDeriv K M ((a * x.1, x.2), a)‖ ≤ M₀ := hM₀ _ hxK ⟨_, hmemC, hd⟩
    exact le_trans hDbound (by rw [hC₀]; linarith [le_max_left M₀ 0, le_max_right M₀ 0])
  -- the chain rule for the slices
  have hchain : ∀ (x : ℝ × E) (a : ℝ), x ∈ B → a ∈ Set.Icc (0:ℝ) 1 →
      HasFDerivWithinAt (fun x' : ℝ × E => M ((rayL (E := E) a x', a)))
        (rayDeriv K M ((a * x.1, x.2), a)) B x := by
    intro x a hxB ha
    obtain ⟨hxslab, -⟩ := (hBmem x).mp hxB
    have hq : ((a * x.1, x.2), a) ∈ K := hray_mem x a hxslab ha
    have hMK : HasFDerivWithinAt M (fderivWithin ℝ M K ((a * x.1, x.2), a)) K
        ((a * x.1, x.2), a) :=
      ((hM.contDiffWithinAt hq).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hψ : HasFDerivWithinAt (fun x' : ℝ × E => (rayL (E := E) a x', a))
        ((rayL (E := E) a).prod 0) B x :=
      (((rayL (E := E) a).hasFDerivAt).prodMk (hasFDerivAt_const a x)).hasFDerivWithinAt
    have hmap : MapsTo (fun x' : ℝ × E => (rayL (E := E) a x', a)) B K := by
      intro x' hx'B
      obtain ⟨hx'slab, -⟩ := (hBmem x').mp hx'B
      simpa only [rayL_apply] using hray_mem x' a hx'slab ha
    have hcomp : HasFDerivWithinAt (fun x' : ℝ × E => M ((rayL (E := E) a x', a)))
        ((fderivWithin ℝ M K ((a * x.1, x.2), a)).comp ((rayL (E := E) a).prod 0)) B x :=
      HasFDerivWithinAt.comp (f := fun x' : ℝ × E => (rayL (E := E) a x', a)) (g := M)
        (x := x) hMK hψ hmap
    have hder : (fderivWithin ℝ M K ((a * x.1, x.2), a)).comp ((rayL (E := E) a).prod 0)
        = rayDeriv K M ((a * x.1, x.2), a) := by
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [rayDeriv, rayPartial, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, rayL_apply, ContinuousLinearMap.inl_apply, zero_apply]
    rwa [hder] at hcomp
  -- the slices are continuous (hence interval integrable) and satisfy the Lipschitz bound
  have hF_int : ∀ x ∈ B, IntervalIntegrable (F x) MeasureTheory.volume (0 : ℝ) 1 := by
    intro x hxB
    obtain ⟨hxslab, -⟩ := (hBmem x).mp hxB
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => ((a * x.1, x.2), a)) :=
      ((contDiff_id.mul contDiff_const).prodMk contDiff_const).prodMk contDiff_id
    have hmap : MapsTo (fun a : ℝ => ((a * x.1, x.2), a)) (Set.uIcc (0:ℝ) 1) K := by
      intro a ha
      rw [Set.uIcc_of_le zero_le_one] at ha
      exact hray_mem x a hxslab ha
    have hcomp := hM.comp (hφ.contDiffOn.of_le (by simp)) hmap
    have hcont : ContinuousOn (fun a : ℝ => F x a) (Set.uIcc (0:ℝ) 1) :=
      hcomp.continuousOn.congr (fun a _ => by simp only [hF, Function.comp_apply])
    exact hcont.intervalIntegrable
  have hlip : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ B, ‖F x a - F p₀ a‖ ≤ C₀ * ‖x - p₀‖ := by
    intro a ha x hxB
    have hderiv : ∀ x' ∈ B, HasFDerivWithinAt (fun x' : ℝ × E => F x' a)
        (rayDeriv K M ((a * x'.1, x'.2), a)) B x' := by
      intro x' hx'B
      have h := hchain x' a hx'B ha
      simpa only [hF, rayL_apply] using h
    have hmvt := hBconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv
      (fun x' hx'B => hray_bound x' a hx'B ha) hp₀B hxB
    simpa only [hF] using hmvt
  have hcont_F' : ContinuousOn F' (Set.uIcc (0:ℝ) 1) := by
    have hmap : MapsTo (fun a : ℝ => ((a * p₀.1, p₀.2), a)) (Set.uIcc (0:ℝ) 1) K := by
      intro a ha
      rw [Set.uIcc_of_le zero_le_one] at ha
      simpa only [mul_comm] using hKmem' a ha
    have hφc : Continuous (fun a : ℝ => ((a * p₀.1, p₀.2), a)) :=
      ((continuous_id.mul continuous_const).prodMk continuous_const).prodMk continuous_id
    exact (hRD.continuousOn.comp hφc.continuousOn hmap).congr
      (fun a _ => by simp only [hF', Function.comp_apply])
  have hF'_int : IntervalIntegrable F' MeasureTheory.volume (0 : ℝ) 1 := hcont_F'.intervalIntegrable
  have hF'_meas : MeasureTheory.AEStronglyMeasurable F'
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    have h := hF'_int.aestronglyMeasurable
    rw [Set.uIoc_of_le zero_le_one]
    exact h
  have huIcc : ∀ a : ℝ, a ∈ Set.uIoc (0:ℝ) 1 → a ∈ Set.Icc (0:ℝ) 1 := by
    intro a ha
    rw [Set.uIoc_of_le zero_le_one] at ha
    exact ⟨le_of_lt ha.1, ha.2⟩
  have hae : ∀ (P : ℝ → Prop), (∀ a ∈ Set.uIoc (0:ℝ) 1, P a) →
      Filter.Eventually P (MeasureTheory.ae
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1))) := by
    intro P hP
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun a ha => hP a ha
  have h_lip : Filter.Eventually
      (fun a : ℝ => ∀ x ∈ B, ‖F x a - F p₀ a‖ ≤ (fun _ : ℝ => C₀) a * ‖x - p₀‖)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.uIoc (0 : ℝ) 1))) :=
    hae _ (fun a ha => hlip a (huIcc a ha))
  have h_diff : Filter.Eventually
      (fun a : ℝ => HasFDerivWithinAt (fun x => F x a) (F' a) B p₀)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.uIoc (0 : ℝ) 1))) := by
    refine hae _ (fun a ha => ?_)
    have h := hchain p₀ a hp₀B (huIcc a ha)
    simpa only [hF, hF', rayL_apply] using h
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C₀) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hmain := hasFDerivWithinAt_intervalIntegral_of_lipschitz (B := B) (x₀ := p₀)
    (F := F) (F' := F') (bound := fun _ : ℝ => C₀) hF_int hF'_int hF'_meas h_lip hbound_int h_diff
  have hfilter : 𝓝[B] p₀ = 𝓝[Set.Ioo (-T) T ×ˢ σ] p₀ := by
    have h := nhdsWithin_inter_of_mem' hB_nhds
    rwa [Set.inter_eq_right.mpr hB_sub] at h
  have hgoal : HasFDerivWithinAt
      (fun x => intervalIntegral (fun a => F x a) (0 : ℝ) 1 MeasureTheory.volume)
      (intervalIntegral F' (0 : ℝ) 1 MeasureTheory.volume) (Set.Ioo (-T) T ×ˢ σ) p₀ := by
    simpa only [HasFDerivWithinAt, hfilter] using hmain
  have h1 : (fun x : ℝ × E => intervalIntegral (fun a => F x a) (0 : ℝ) 1 MeasureTheory.volume)
      = rayInt M := by
    funext x
    simp only [rayInt, intervalIntegral, hF]
  have h2 : intervalIntegral F' (0 : ℝ) 1 MeasureTheory.volume
      = rayInt (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) p₀ := by
    rw [hF']
    simp only [rayInt, intervalIntegral, hK]
  rw [h1, h2] at hgoal
  exact hgoal

/-- **Smoothness of the two-sided ray integral** (stable form). -/
theorem rayInt_twoSided_stable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {σ : Set E} (hc : Convex ℝ σ) (hd : UniqueDiffOn ℝ σ) :
    ∀ (n : ℕ) (W : Type (max u v)) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (M : (ℝ × E) × ℝ → W),
      ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞) M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) →
      ContDiffOn ℝ (n : ℕ∞) (rayInt M) (Set.Ioo (-T) T ×ˢ σ) := by
  intro n
  induction n with
  | zero =>
      intro W _ _ _ M hM
      exact (contDiffOn_zero (𝕜 := ℝ)).2 fun p hp =>
        (rayInt_twoSided_single hT hc hd (hM.of_le le_rfl) p hp).continuousWithinAt
  | succ n ih =>
      intro W _ _ _ M hM
      have hK_unique : UniqueDiffOn ℝ ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
        ((uniqueDiffOn_Ioo (-T) T).prod hd).prod (uniqueDiffOn_Icc zero_lt_one)
      have hRD : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
          (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M)
          ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        have hD : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (fun qs : (ℝ × E) × ℝ => fderivWithin ℝ M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0:ℝ) 1) qs)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
          hM.fderivWithin hK_unique (m := (((n + 1 : ℕ)) : ℕ∞))
             (by rw [show (((((n + 1 : ℕ)) : ℕ∞)) : ℕ∞ω) + 1 = (((((n + 1 + 1 : ℕ)) : ℕ∞)) : ℕ∞ω) from by push_cast; ring])
        have hL : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (fun qs : (ℝ × E) × ℝ => rayL (E := E) qs.2)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
          ((contDiff_rayL (E := E)).of_le (by simp)).comp_contDiffOn contDiffOn_snd
        have hP : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) := by
          have hfun : rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M
              = fun qs : (ℝ × E) × ℝ =>
                (fderivWithin ℝ M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0:ℝ) 1) qs).comp
                  (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ) := rfl
          rw [hfun]
          exact hD.clm_comp contDiffOn_const
        have hfun : rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M
            = fun qs : (ℝ × E) × ℝ =>
              (rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M qs).comp
                (rayL (E := E) qs.2) := rfl
        rw [hfun]
        exact hP.clm_comp hL
      have ih' := ih ((ℝ × E) →L[ℝ] W)
        (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) hRD
      rw [show (((n + 1 : ℕ)) : ℕ∞) = (n : ℕ∞) + 1 from by push_cast; ring]
      intro p hp
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := (n : ℕ∞)) (by simp)).2
        ⟨Set.Ioo (-T) T ×ˢ σ, ?_, subset_insert _ _, fun h => absurd h (by simp),
          fun x => rayInt (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) x, ?_, ?_⟩
      · rw [insert_eq_of_mem hp]; exact self_mem_nhdsWithin
      · intro x hx
        exact rayInt_twoSided_single hT hc hd (hM.of_le (by norm_num)) x hx
      · exact ih'.contDiffWithinAt hp

/-- **Smoothness of the two-sided ray integral.** -/
theorem rayInt_twoSided_level {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {σ : Set E} (hc : Convex ℝ σ) (hd : UniqueDiffOn ℝ σ) :
    ∀ (n : ℕ) (W : Type v) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (M : (ℝ × E) × ℝ → W),
      ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞) M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) →
      ContDiffOn ℝ (n : ℕ∞) (rayInt M) (Set.Ioo (-T) T ×ˢ σ) := by
  intro n
  induction n with
  | zero =>
      intro W _ _ _ M hM
      exact (contDiffOn_zero (𝕜 := ℝ)).2 fun p hp =>
        (rayInt_twoSided_single hT hc hd (hM.of_le le_rfl) p hp).continuousWithinAt
  | succ n _ih =>
      intro W _ _ _ M hM
      have hK_unique : UniqueDiffOn ℝ ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
        ((uniqueDiffOn_Ioo (-T) T).prod hd).prod (uniqueDiffOn_Icc zero_lt_one)
      have hRD : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
          (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M)
          ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        have hD : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (fun qs : (ℝ × E) × ℝ => fderivWithin ℝ M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0:ℝ) 1) qs)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
          hM.fderivWithin hK_unique (m := (((n + 1 : ℕ)) : ℕ∞))
             (by rw [show (((((n + 1 : ℕ)) : ℕ∞)) : ℕ∞ω) + 1 = (((((n + 1 + 1 : ℕ)) : ℕ∞)) : ℕ∞ω) from by push_cast; ring])
        have hL : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (fun qs : (ℝ × E) × ℝ => rayL (E := E) qs.2)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) :=
          ((contDiff_rayL (E := E)).of_le (by simp)).comp_contDiffOn contDiffOn_snd
        have hP : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞)
            (rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M)
            ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) := by
          have hfun : rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M
              = fun qs : (ℝ × E) × ℝ =>
                (fderivWithin ℝ M ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0:ℝ) 1) qs).comp
                  (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ) := rfl
          rw [hfun]
          exact hD.clm_comp contDiffOn_const
        have hfun : rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M
            = fun qs : (ℝ × E) × ℝ =>
              (rayPartial ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M qs).comp
                (rayL (E := E) qs.2) := rfl
        rw [hfun]
        exact hP.clm_comp hL
      have ih' := rayInt_twoSided_stable (E := E) hT hc hd
        n ((ℝ × E) →L[ℝ] W) (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) hRD
      rw [show (((n + 1 : ℕ)) : ℕ∞) = (n : ℕ∞) + 1 from by push_cast; ring]
      intro p hp
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := (n : ℕ∞)) (by simp)).2
        ⟨Set.Ioo (-T) T ×ˢ σ, ?_, subset_insert _ _, fun h => absurd h (by simp),
          fun x => rayInt (rayDeriv ((Set.Ioo (-T) T ×ˢ σ) ×ˢ Set.Icc (0 : ℝ) 1) M) x, ?_, ?_⟩
      · rw [insert_eq_of_mem hp]; exact self_mem_nhdsWithin
      · intro x hx
        exact rayInt_twoSided_single hT hc hd (hM.of_le (by norm_num)) x hx
      · exact ih'.contDiffWithinAt hp

/-- **The odd quotient extends smoothly through `τ = 0`.**

If `N : ℝ × M → ℝ` is jointly `C^∞` at `(0, y₀)` and odd in its first variable, then
`(τ, y) ↦ N (τ, y) / τ` (with the value `∂_τ N (0, y)` at `τ = 0`) is jointly `C^∞` at `(0, y₀)`.

Route: oddness gives `N (0, y) = 0`, hence `N (τ, y) = ∫_0^τ ∂_σ N (σ, y) dσ`, and so for `τ ≠ 0`
`N (τ, y)/τ = ∫_0^1 ∂_σ N (t τ, y) dt`, while at `τ = 0` the right-hand side is
`∂_σ N (0, y) = deriv (fun τ => N (τ, y)) 0`.  So near `(0,y₀)` the function of the statement agrees
with the parameter-dependent integral `(τ,y) ↦ ∫_0^1 ∂_σ N (tτ, y) dt`, which is jointly `C^∞` there
because the partial derivative `∂_σ N` of a jointly `C^∞` family is jointly `C^∞` (the workspace's
`Work.Diff.EXT.jointSmoothAt_tDeriv`) and integration over the compact interval `[0,1]` preserves
that.  Since the conclusion is local, shrink the neighbourhood of `hN` to a product
`B_ε(0) × V` and argue by `Filter.EventuallyEq`/`congr_of_eventuallyEq`. -/
theorem oddDivJointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {N : ℝ × M → ℝ} {y₀ : M}
    (hN : Work.Diff.EXT.JointSmoothAt I M N 0 y₀)
    (hodd : ∀ τ y, N (-τ, y) = - N (τ, y)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => if p.1 = 0 then deriv (fun τ : ℝ => N (τ, p.2)) 0 else N p / p.1) 0 y₀ := by
  have hN0 : ∀ y : M, N (0, y) = 0 := by
    intro y
    have h := hodd 0 y
    rw [neg_zero] at h
    linarith
  let e : PartialEquiv M E := extChartAt I y₀
  let ξ₀ : E := e y₀
  let u : ℝ × E → ℝ := fun p => N (p.1, e.symm p.2)
  have hu0 : ∀ ξ : E, u (0, ξ) = 0 := fun ξ => hN0 _
  have hkey : ∀ n : ℕ, ContDiffWithinAt ℝ (n : ℕ∞ω)
      (fun p : ℝ × E => if p.1 = 0 then deriv (fun τ : ℝ => u (τ, p.2)) 0 else u p / p.1)
      (univ ×ˢ Set.range I) (0, ξ₀) := by
    intro n
    -- the chart target coincides with `range I` near `ξ₀`
    obtain ⟨V₀, hV₀open, hV₀mem, hV₀sub⟩ :=
      mem_nhdsWithin.mp (show e.target ∈ 𝓝[Set.range I] ξ₀ from
        extChartAt_target_mem_nhdsWithin (I := I) (x := y₀))
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hV₀open.mem_nhds hV₀mem)
    -- the chart-written family is `C^{n+2}` at the point
    have hch : ContDiffWithinAt ℝ (((n + 2 : ℕ)) : ℕ∞ω) u (univ ×ˢ e.target) (0, ξ₀) := by
      have h := contDiffWithinAt_chart_family (I := I) (M := M) (F := ℝ) (n + 2) hN
      simpa only [u, e, ξ₀] using h
    obtain ⟨Ω, hΩmem, pΩ, hΩft⟩ := contDiffWithinAt_nat.mp hch
    have hΩsm : ContDiffOn ℝ (((n + 2 : ℕ)) : ℕ∞ω) u Ω := hΩft.contDiffOn
    obtain ⟨V, hVopen, hVmem, hVsub⟩ := mem_nhdsWithin.mp hΩmem
    obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hVmem)
    have hδ'pos : 0 < min δ ρ := lt_min hδpos hρpos
    let σ : Set E := Set.range I ∩ Metric.ball ξ₀ (min δ ρ)
    let K : Set (ℝ × E) := Set.Ioo (-(min δ ρ)) (min δ ρ) ×ˢ σ
    have hσc : Convex ℝ σ := I.convex_range.inter (convex_ball ξ₀ _)
    have hσd : UniqueDiffOn ℝ σ := I.uniqueDiffOn.inter Metric.isOpen_ball
    have hKuniq : UniqueDiffOn ℝ K := (uniqueDiffOn_Ioo _ _).prod hσd
    have hKsm : ContDiffOn ℝ (((n + 2 : ℕ)) : ℕ∞ω) u K := by
      refine hΩsm.mono ?_
      intro q hq
      obtain ⟨hq1, hq2⟩ := hq
      obtain ⟨hq2a, hq2b⟩ := hq2
      have hq2ρ : q.2 ∈ Metric.ball ξ₀ ρ :=
        Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hq2b) (min_le_right δ ρ))
      have hmemT : q.2 ∈ e.target := hV₀sub ⟨hρsub hq2ρ, hq2a⟩
      have hdist : dist q ((0:ℝ), ξ₀) < δ := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
        exact ⟨lt_of_lt_of_le (abs_lt.mpr ⟨hq1.1, hq1.2⟩) (min_le_left δ ρ),
          lt_of_lt_of_le (Metric.mem_ball.mp hq2b) (min_le_left δ ρ)⟩
      exact hVsub ⟨hδV hdist, Or.inr ⟨mem_univ _, hmemT⟩⟩
    have hdiffOn : DifferentiableOn ℝ u K := hKsm.differentiableOn (by simp)
    -- the time-derivative family and its smoothness on the slab
    let Mf : (ℝ × E) × ℝ → ℝ := fun q => deriv (fun τ : ℝ => u (τ, q.1.2)) q.1.1
    have htder : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞ω)
        (fun p : ℝ × E => deriv (fun τ : ℝ => u (τ, p.2)) p.1) K :=
      tDeriv_slab_self (T := min δ ρ) hδ'pos hσd (n + 1) hKsm
    have hMsmooth : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞ω) Mf (K ×ˢ Set.Icc (0:ℝ) 1) :=
      htder.comp contDiffOn_fst (fun q hq => hq.1)
    have hray := rayInt_twoSided_level (E := E) hδ'pos hσc hσd n ℝ Mf hMsmooth
    have hEqOn : ∀ p ∈ K, rayInt Mf p
        = (if p.1 = 0 then deriv (fun τ : ℝ => u (τ, p.2)) 0 else u p / p.1) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hp1T1, hp1T2⟩ := hp1
      have hmemK : ∀ x : ℝ, x ∈ Set.uIcc (0:ℝ) p.1 → (x, p.2) ∈ K := by
        intro x hx
        rcases le_total 0 p.1 with h | h
        · rw [Set.uIcc_of_le h] at hx
          obtain ⟨hx1, hx2⟩ := hx
          exact ⟨⟨by linarith [hδ'pos], by linarith [hp1T2]⟩, hp2⟩
        · rw [Set.uIcc_of_ge h] at hx
          obtain ⟨hx1, hx2⟩ := hx
          exact ⟨⟨by linarith [hp1T1], by linarith [hδ'pos]⟩, hp2⟩
      have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) p.1,
          HasDerivAt (fun s : ℝ => u (s, p.2)) (deriv (fun τ : ℝ => u (τ, p.2)) x) x := by
        intro x hx
        have h1 := hasDerivAt_slice_slab (T := min δ ρ) (σ := σ) (hmemK x hx)
          (hdiffOn (x, p.2) (hmemK x hx))
        have h2 : fderivWithin ℝ u K (x, p.2) (1, 0) = deriv (fun τ : ℝ => u (τ, p.2)) x :=
          h1.deriv.symm
        rwa [h2] at h1
      have hcont : ContinuousOn (fun x : ℝ => deriv (fun τ : ℝ => u (τ, p.2)) x) (Set.uIcc 0 p.1) :=
        htder.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun x hx => hmemK x hx)
      have hFTC : ∫ x in (0:ℝ)..p.1, deriv (fun τ : ℝ => u (τ, p.2)) x
          = u (p.1, p.2) - u (0, p.2) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      have hsub : (p.1 : ℝ) • (∫ s in (0:ℝ)..1, deriv (fun τ : ℝ => u (τ, p.2)) (s * p.1))
          = ∫ x in (0:ℝ)..p.1, deriv (fun τ : ℝ => u (τ, p.2)) x := by
        have h := intervalIntegral.smul_integral_comp_mul_right
          (f := fun x : ℝ => deriv (fun τ : ℝ => u (τ, p.2)) x) p.1 (a := (0:ℝ)) (b := (1:ℝ))
        simpa only [zero_mul, one_mul] using h
      have hrayEq : rayInt Mf p
          = ∫ s in (0:ℝ)..1, deriv (fun τ : ℝ => u (τ, p.2)) (s * p.1) := by
        simp only [rayInt, Mf]
      have hprod : (p.1 : ℝ) * rayInt Mf p = u p := by
        rw [hrayEq, ← smul_eq_mul, hsub, hFTC, hu0 p.2, sub_zero]
      by_cases hp0 : p.1 = 0
      · rw [hrayEq, hp0, if_pos rfl]
        have hc : (fun s : ℝ => deriv (fun τ : ℝ => u (τ, p.2)) (s * 0))
            = fun _ : ℝ => deriv (fun τ : ℝ => u (τ, p.2)) 0 := by
          funext s; rw [mul_zero]
        rw [hc, intervalIntegral.integral_const, sub_zero, one_smul]
      · rw [if_neg hp0]
        have h2 : p.1 * (u p / p.1) = u p := by field_simp
        exact mul_left_cancel₀ hp0 (by rw [hprod, h2])
    have hsmK : ContDiffOn ℝ (n : ℕ∞ω)
        (fun p : ℝ × E => if p.1 = 0 then deriv (fun τ : ℝ => u (τ, p.2)) 0 else u p / p.1) K :=
      hray.congr (fun p hp => (hEqOn p hp).symm)
    have hξ₀K : (0, ξ₀) ∈ K :=
      ⟨⟨by linarith [hδ'pos], by linarith [hδ'pos]⟩,
        ⟨extChartAt_target_subset_range (I := I) y₀ (mem_extChartAt_target y₀),
          Metric.mem_ball_self hδ'pos⟩⟩
    have hKeq : K =ᶠ[𝓝 ((0:ℝ), ξ₀)] (univ ×ˢ Set.range I) := by
      have hV' : Set.Ioo (-(min δ ρ)) (min δ ρ) ×ˢ Metric.ball ξ₀ (min δ ρ) ∈ 𝓝 ((0:ℝ), ξ₀) :=
        IsOpen.mem_nhds (isOpen_Ioo.prod Metric.isOpen_ball)
          ⟨⟨by linarith [hδ'pos], by linarith [hδ'pos]⟩, Metric.mem_ball_self hδ'pos⟩
      filter_upwards [hV'] with q hq
      exact propext ⟨fun hqk => ⟨trivial, hqk.2.1⟩, fun hq' => ⟨hq.1, ⟨hq'.2, hq.2⟩⟩⟩
    exact (contDiffWithinAt_congr_set hKeq).1 (hsmK.contDiffWithinAt hξ₀K)
  have hmain : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => if p.1 = 0 then deriv (fun τ : ℝ => u (τ, p.2)) 0 else u p / p.1)
      (univ ×ˢ Set.range I) (0, ξ₀) :=
    contDiffWithinAt_infty.mpr hkey
  refine (contMDiffAt_iff_source (I := (𝓘(ℝ,ℝ)).prod I) (I' := 𝓘(ℝ,ℝ)) (x := ((0:ℝ), y₀))).2 ?_
  rw [show ((fun p : ℝ × M => if p.1 = 0 then deriv (fun τ : ℝ => N (τ, p.2)) 0 else N p / p.1)
        ∘ (extChartAt (𝓘(ℝ,ℝ).prod I) ((0:ℝ), y₀)).symm)
        = (fun p : ℝ × E => if p.1 = 0 then deriv (fun τ : ℝ => u (τ, p.2)) 0 else u p / p.1) from by
      rw [extChartAt_prod_symm (0:ℝ) y₀]; rfl,
    extChartAt_prod_apply (0:ℝ) y₀, range_prod_modelWithCorners]
  exact hmain.contMDiffWithinAt

end

end Work.Diff.EXT
