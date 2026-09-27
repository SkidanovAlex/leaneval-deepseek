import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Drive.Rays.oneSidedGlobalize
import Submission.Work.Routing.straightenedChartStretch
import Submission.Work.Compat.MFDerivCongrV433

/-!
# Straightening the germ of an immersed ray

`Work.Drive.Rays.rayStraightening`: an immersion `r` of the half-line `[0,∞)` into a smooth
`n`-manifold (`n ≥ 2`) is, at every `t₀ ≥ 0`, the straight chart line in some chart of the maximal
atlas, with the *original* parameter `t` as the chart parameter.

The case `t₀ = 0` is the interesting one: there `r` is only smooth one-sidedly, so the germ of the
chart expression of `r` at `0` is first globalised to a two-sided smooth function with the same
infinite jet (`Work.Drive.Rays.oneSidedGlobalize`, proved with Borel's theorem), after which the
Euclidean straightening `exists_straightening` applies.  For `t₀ > 0` the curve is smooth near
`t₀` and is globalised by a squash of the parameter, after which `localStraighteningAt` applies.
-/

namespace Work.Drive.Rays

open Set Filter Topology

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
theorem rayStraightening {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      w ≠ 0 ∧ 0 < e ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ r t₀ ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → |t - t₀| ≤ e →
        r t = c.symm (c (r t₀) + (t - t₀) • w)) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  rcases eq_or_lt_of_le ht₀ with rfl | ht₀pos
  · -- ## the case `t₀ = 0`
    -- the chart `cq` at `p = r 0`
    set p : M := r 0 with hp
    set cq : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) p with hcq
    have hcqsrc : p ∈ cq.source := mem_chart_source _ p
    have hcqmax : cq ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
      IsManifold.chart_mem_maximalAtlas p
    have hcqc : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq) cq.source :=
      contMDiffOn_of_mem_maximalAtlas hcqmax
    have hcqs : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq.symm) cq.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hcqmax
    -- `r` stays in the source of the chart near `0` from the right
    have hmem : r ⁻¹' cq.source ∈ 𝓝[Set.Ici (0:ℝ)] 0 :=
      (hrsm.continuousOn.continuousWithinAt (Set.mem_Ici.mpr le_rfl)).preimage_mem_nhdsWithin
        (cq.open_source.mem_nhds hcqsrc)
    obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → r t ∈ cq.source := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
      refine ⟨ε/2, by linarith, fun t ht hlt => hεsub ⟨?_, ht⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]
      linarith
    -- the chart expression of `r`
    set η : ℝ → EuclideanSpace ℝ (Fin n) := fun t => cq (r t) with hη
    have hηsm : ContDiffOn ℝ smoothOrder η (Set.Ioo 0 δ) := by
      have hr : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ioo 0 δ) :=
        fun t ht => (hrsm t (Set.mem_Ioo.mp ht).1.le).mono (fun y hy => (Set.mem_Ioo.mp hy).1.le)
      have hcomp : ContMDiffOn MCreal (MC n) smoothOrder (fun t => cq (r t)) (Set.Ioo 0 δ) :=
        hcqc.comp hr (fun t ht => hδsub t (Set.mem_Ioo.mp ht).1.le (Set.mem_Ioo.mp ht).2)
      exact contMDiffOn_iff_contDiffOn.mp (by simpa only [hη] using hcomp)
    have hη0' : ContDiffWithinAt ℝ smoothOrder η (Set.Ici (0:ℝ)) 0 := by
      have hcomp : ContMDiffWithinAt MCreal (MC n) smoothOrder (fun t => cq (r t))
          (Set.Ici (0:ℝ) ∩ r ⁻¹' cq.source) 0 :=
        ContMDiffWithinAt.comp 0 (hcqc p hcqsrc)
          ((hrsm 0 (Set.mem_Ici.mpr le_rfl)).mono Set.inter_subset_left)
          (fun t ht => ht.2)
      have hmem2 : Set.Ici (0:ℝ) ∩ r ⁻¹' cq.source ∈ 𝓝[Set.Ici (0:ℝ)] 0 :=
        Filter.inter_mem self_mem_nhdsWithin hmem
      have hbig := hcomp.mono_of_mem_nhdsWithin hmem2
      exact contMDiffWithinAt_iff_contDiffWithinAt.mp (by simpa only [hη] using hbig)
    -- the two-sided globalisation of the germ
    obtain ⟨F, hFsm, hFagree⟩ := oneSidedGlobalize (E := EuclideanSpace ℝ (Fin n)) hδpos hη0' hηsm
    -- ## the derivative of the globalised germ at `0` is nonzero
    have hne : mfderiv MCreal (MC n) r 0 ≠ 0 := by
      intro h0
      have h01 : (mfderiv MCreal (MC n) r 0) (0:ℝ) = (mfderiv MCreal (MC n) r 0) (1:ℝ) := by
        rw [h0]
        exact (zero_apply (0:ℝ)).trans (zero_apply (1:ℝ)).symm
      have h := hrimm 0 le_rfl h01
      have h' : (0:ℝ) = 1 := h
      norm_num at h'
    have hmd : MDifferentiableAt MCreal (MC n) r 0 := by
      by_contra h
      exact hne (mfderiv_zero_of_not_mdifferentiableAt (I := MCreal) (I' := MC n) h)
    have huniq : UniqueMDiffAt[Set.Ici (0:ℝ)] (0:ℝ) :=
      uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffWithinAt_Ici 0)
    have hwd : mfderivWithin MCreal (MC n) r (Set.Ici (0:ℝ)) 0 = mfderiv MCreal (MC n) r 0 :=
      mfderivWithin_eq_mfderiv (I := MCreal) (I' := MC n) (M := ℝ) (M' := M) (f := r) (x := 0)
        (s := Set.Ici (0:ℝ)) huniq hmd
    have hchain := mfderiv_comp_mfderivWithin (I := MCreal) (I' := MC n) (I'' := MC n)
      (M := ℝ) (M' := M) (M'' := EuclideanSpace ℝ (Fin n))
      (f := r) (g := (↑cq : M → EuclideanSpace ℝ (Fin n))) (s := Set.Ici (0:ℝ)) 0
      ((hcqc.contMDiffAt (cq.open_source.mem_nhds hcqsrc)).mdifferentiableAt hn0)
      ((hrsm 0 (Set.mem_Ici.mpr le_rfl)).mdifferentiableWithinAt hn0) huniq
    have hinj1 : Function.Injective
        (mfderiv (MC n) (MC n) (↑cq : M → EuclideanSpace ℝ (Fin n)) p) :=
      mfderiv_chart_injective (n := n) cq hcqc hcqs hcqsrc
    have hinj2 : Function.Injective (mfderivWithin MCreal (MC n) r (Set.Ici (0:ℝ)) 0) := by
      rw [hwd]; exact hrimm 0 le_rfl
    have hinj3 : Function.Injective
        (mfderivWithin MCreal (MC n) (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0) := by
      rw [show mfderivWithin MCreal (MC n) (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0
          = mfderiv (MC n) (MC n) (↑cq : M → EuclideanSpace ℝ (Fin n)) p
            ∘SL mfderivWithin MCreal (MC n) r (Set.Ici (0:ℝ)) 0 from hchain]
      simpa only [ContinuousLinearMap.coe_comp] using hinj1.comp hinj2
    have hfinj : Function.Injective
        (fderivWithin ℝ (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0) := by
      have h := hinj3
      rwa [mfderivWithin_eq_fderivWithin (𝕜 := ℝ) (f := fun t : ℝ => cq (r t))
        (s := Set.Ici (0:ℝ)) (x := 0)] at h
    have hL1 : (fderivWithin ℝ (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0) 1 ≠ 0 := by
      intro h1
      have h01 : (fderivWithin ℝ (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0) 0
          = (fderivWithin ℝ (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0) 1 := by
        simp [h1]
      have h20 : (0:ℝ) = (1:ℝ) := hfinj h01
      norm_num at h20
    have hderivne : derivWithin (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0 ≠ 0 := hL1
    have hFe : F =ᶠ[𝓝[Set.Ici (0:ℝ)] 0] (fun t : ℝ => cq (r t)) := by
      filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδpos)]
        with t ht0 htδ
      exact hFagree t (Set.mem_Ici.mp ht0) htδ
    have hF0 : F 0 = (fun t : ℝ => cq (r t)) 0 := hFagree 0 le_rfl hδpos
    have hFderiv : (fderiv ℝ F 0) 1 ≠ 0 := by
      have hwit := hFe.iteratedDerivWithin_eq hF0 (n := 1)
      have hdiff : DifferentiableAt ℝ F 0 :=
        (hFsm.contDiffAt (Ioo_mem_nhds (by linarith) hδpos)).differentiableAt hn0
      have h3 : derivWithin F (Set.Ici (0:ℝ)) 0 = (fderiv ℝ F 0) 1 :=
        (hdiff.hasFDerivAt.hasFDerivWithinAt.hasDerivWithinAt).derivWithin
          (uniqueDiffWithinAt_Ici 0)
      have h2 : iteratedDerivWithin 1 F (Set.Ici (0:ℝ)) 0 = derivWithin F (Set.Ici (0:ℝ)) 0 := by
        rw [iteratedDerivWithin_one]
      have h4 : iteratedDerivWithin 1 (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0
          = derivWithin (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0 := by
        rw [iteratedDerivWithin_one]
      have hEq : (fderiv ℝ F 0) 1
          = derivWithin (fun t : ℝ => cq (r t)) (Set.Ici (0:ℝ)) 0 := by
        rw [← h3, ← h2, hwit, h4]
      rw [hEq]; exact hderivne
    -- ## the straightening of the globalised germ, at parameter `1`
    set K : ℝ → EuclideanSpace ℝ (Fin n) := fun u => F (u - 1) with hK
    have hVopen : IsOpen (Set.Ioo (-δ + 1) (δ + 1)) := isOpen_Ioo
    have h1V : (1:ℝ) ∈ Set.Ioo (-δ + 1) (δ + 1) := ⟨by linarith, by linarith⟩
    have hKsm : ContDiffOn ℝ smoothOrder K (Set.Ioo (-δ + 1) (δ + 1)) := by
      have hsub : ContDiffOn ℝ smoothOrder (fun u : ℝ => u - 1) (Set.Ioo (-δ + 1) (δ + 1)) := by
        fun_prop
      have hmap : Set.Ioo (-δ + 1) (δ + 1)
          ⊆ (fun u : ℝ => u - 1) ⁻¹' Set.Ioo (-δ) δ := by
        intro u hu
        rw [Set.mem_Ioo] at hu
        rw [Set.mem_preimage, Set.mem_Ioo]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hcomp := hFsm.comp hsub hmap
      simpa only [hK, Function.comp_def] using hcomp
    have hK1 : K 1 = cq p := by
      show F (1 - 1) = cq p
      rw [sub_self, hFagree 0 le_rfl hδpos]
    have hKd : (fderiv ℝ K 1) 1 = (fderiv ℝ F 0) 1 := by
      have h10 : (1:ℝ) - 1 = 0 := by ring
      have h1 : HasFDerivAt (fun u : ℝ => u - 1) (ContinuousLinearMap.id ℝ ℝ) 1 :=
        (hasFDerivAt_id (1:ℝ)).sub_const 1
      have h2 : HasFDerivAt F (fderiv ℝ F (1 - 1)) (1 - 1) := by
        simpa only [h10] using
          ((hFsm.contDiffAt (Ioo_mem_nhds (by linarith) hδpos)).differentiableAt hn0).hasFDerivAt
      have h3 : HasFDerivAt K ((fderiv ℝ F (1 - 1)).comp (ContinuousLinearMap.id ℝ ℝ)) 1 := by
        have hh := HasFDerivAt.comp (f := fun u : ℝ => u - 1) (g := F) 1 h2 h1
        simpa only [hK, Function.comp_def] using hh
      rw [h3.fderiv]
      simp
    obtain ⟨Φ, ρ, hρpos, hΦsm, hΦsm', hΦx₀, hΦsx₀, hΦgerm⟩ :=
      exists_straightening (k := K) (x₀ := cq p) (v := (fderiv ℝ F 0) 1)
        hVopen h1V hKsm hK1 hKd hFderiv
    -- ## the straightened chart
    set c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := cq ≫ₕ Φ.symm with hc'def
    have hc'src : c'.source = cq.source ∩ ↑cq ⁻¹' Φ.target := by
      rw [hc'def, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    have hc'tgt : c'.target = Φ.source ∩ ↑Φ ⁻¹' cq.target := by
      rw [hc'def, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.symm_target]
    have hc'max : c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M := by
      rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
      constructor
      · rw [hc'src]
        have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ.symm) Φ.target :=
          fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm' z hz).contDiffWithinAt
        have h2 := h1.comp (hcqc.mono inter_subset_left) (fun x hx => hx.2)
        simpa only [hc'def, OpenPartialHomeomorph.coe_trans] using h2
      · rw [hc'tgt]
        have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ) Φ.source :=
          fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm z hz).contDiffWithinAt
        have h2 := hcqs.comp (h1.mono inter_subset_left) (fun x hx => hx.2)
        simpa only [hc'def, OpenPartialHomeomorph.coe_trans_symm,
          OpenPartialHomeomorph.symm_symm] using h2
    refine ⟨c', (fderiv ℝ F 0) 1, min ρ (δ/2), hFderiv, lt_min hρpos (by linarith), hc'max, ?_, ?_⟩
    · rw [hc'src]
      refine ⟨hcqsrc, ?_⟩
      rw [Set.mem_preimage]
      have h := (hΦgerm 1 (by rw [sub_self, abs_zero]; exact hρpos.le)).1
      simpa only [hK1] using h
    · intro t ht0 hte
      have htρ : |t - 0| ≤ ρ := le_trans hte (min_le_left _ _)
      have htδ : t < δ := by
        have h2 := le_trans hte (min_le_right ρ (δ/2))
        rw [sub_zero, abs_of_nonneg ht0] at h2
        linarith
      have hsrc : r t ∈ cq.source := hδsub t ht0 htδ
      have hFt : F t = cq (r t) := hFagree t ht0 htδ
      have hgt : |(t + 1) - 1| ≤ ρ := by
        have hsub : t + 1 - 1 = t := by ring
        rw [hsub]
        simpa only [sub_zero] using htρ
      obtain ⟨hKtgt, hKval⟩ := hΦgerm (t + 1) hgt
      have hKt : K (t + 1) = cq (r t) := by
        show F (t + 1 - 1) = cq (r t)
        have hsub : t + 1 - 1 = t := by ring
        rw [hsub]; exact hFt
      have hsrc' : r t ∈ c'.source := by
        rw [hc'src]
        exact ⟨hsrc, by rw [Set.mem_preimage, ← hKt]; exact hKtgt⟩
      have h1 : c' (r t) = c' (r 0) + (t - 0) • (fderiv ℝ F 0) 1 := by
        have h2 : Φ.symm (cq (r t)) = cq p + ((t + 1) - 1) • (fderiv ℝ F 0) 1 := by
          rw [← hKt]; exact hKval
        have h3 : Φ.symm (cq (r 0)) = cq p := by
          simpa only [hp] using hΦsx₀
        show Φ.symm (cq (r t)) = Φ.symm (cq (r 0)) + (t - 0) • (fderiv ℝ F 0) 1
        rw [h2, h3]
        simp only [add_sub_cancel_right, sub_zero]
      rw [← OpenPartialHomeomorph.left_inv c' hsrc', h1]
  · -- ## the case `0 < t₀`
    have hq : (0:ℝ) < t₀/4 := by linarith
    -- a squash of the parameter which fixes a neighbourhood of `t₀` and stays positive
    set χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - t₀/4)/(t₀/4)) with hχdef
    have hχsm : ContDiff ℝ smoothOrder χ := by
      rw [hχdef]
      have h1 : ContDiff ℝ smoothOrder (fun t : ℝ => (t - t₀/4)/(t₀/4)) := by fun_prop
      exact (Real.smoothTransition.contDiff (n := ⊤)).comp h1
    have hχ0 : ∀ t : ℝ, t ≤ t₀/4 → χ t = 0 := by
      intro t ht
      rw [hχdef]
      exact Real.smoothTransition.zero_of_nonpos (by
        rw [div_nonpos_iff]
        exact Or.inr ⟨by linarith, hq.le⟩)
    have hχ1 : ∀ t : ℝ, t₀/2 ≤ t → χ t = 1 := by
      intro t ht
      rw [hχdef]
      exact Real.smoothTransition.one_of_one_le (by rw [one_le_div hq]; linarith)
    have hχnn : ∀ t : ℝ, 0 ≤ χ t := fun t => Real.smoothTransition.nonneg _
    have hχle : ∀ t : ℝ, χ t ≤ 1 := fun t => Real.smoothTransition.le_one _
    set σ : ℝ → ℝ := fun t => t * χ t + (t₀/2) * (1 - χ t) with hσdef
    have hσsm : ContDiff ℝ smoothOrder σ := by
      rw [hσdef]; fun_prop
    have hσid : ∀ t : ℝ, t₀/2 ≤ t → σ t = t := by
      intro t ht
      simp only [hσdef, hχ1 t ht, mul_one, sub_self, mul_zero, add_zero]
    have hσpos : ∀ t : ℝ, 0 < σ t := by
      intro t
      rcases le_or_gt t (t₀/4) with ht | ht
      · simp only [hσdef, hχ0 t ht, mul_zero, sub_zero, mul_one]
        linarith
      · have hconv : σ t = χ t * t + (1 - χ t) * (t₀/2) := by rw [hσdef]; ring
        nlinarith [hχnn t, hχle t, hconv]
    -- the globally smooth curve
    set ρ : ℝ → M := fun t => r (σ t) with hρdef
    have hρsm : ContMDiff MCreal (MC n) smoothOrder ρ := by
      have hσcm : ContMDiff MCreal MCreal smoothOrder σ := by
        rw [contMDiff_iff_contDiff]; exact hσsm
      have hcomp := hrsm.comp (contMDiffOn_univ.mpr hσcm) (fun t _ => (hσpos t).le)
      rwa [contMDiffOn_univ] at hcomp
    have hρeq : ρ =ᶠ[𝓝 t₀] r := by
      filter_upwards [Ici_mem_nhds (show t₀/2 < t₀ by linarith)] with t ht
      exact congrArg r (hσid t ht)
    have hρmd : mfderiv MCreal (MC n) ρ t₀ = mfderiv MCreal (MC n) r t₀ := hρeq.mfderiv_eq_v433
    obtain ⟨c, u, e, hepos, hune, hcmax, hcsrc, hcgerm⟩ :=
      Work.Routing.localStraighteningAt (n := n) hρsm t₀ (by rw [hρmd]; exact hrimm t₀ ht₀pos.le)
    have hσ₀ : σ t₀ = t₀ := hσid t₀ (by linarith)
    refine ⟨c, u, min e (t₀/2), hune, lt_min hepos (by linarith), hcmax, ?_, ?_⟩
    · rw [show r t₀ = ρ t₀ from (congrArg r hσ₀).symm]
      exact hcsrc
    · intro t ht0 hte
      have htρ : |t - t₀| ≤ e := le_trans hte (min_le_left _ _)
      have ht1 : t₀/2 ≤ t := by
        have h2 := le_trans hte (min_le_right e (t₀/2))
        rw [abs_le] at h2
        linarith [h2.1]
      have hrt : r t = ρ t := congrArg r (hσid t ht1).symm
      obtain ⟨hsrc, hval⟩ := hcgerm t htρ
      rw [hrt, show r t₀ = ρ t₀ from (congrArg r hσ₀).symm]
      rw [← OpenPartialHomeomorph.left_inv c hsrc, hval]

end Work.Drive.Rays
