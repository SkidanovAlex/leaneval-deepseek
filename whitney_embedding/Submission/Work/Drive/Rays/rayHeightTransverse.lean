import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Crux.exists_contDiff_iteratedDeriv
import Submission.Work.Crux.globalize_oneDim
import Submission.Work.Noncompact.ProperLine.flatGlue2
import Submission.Work.Drive.RayTube.RaySetup
import Submission.Work.Drive.RayTube.ray_transverse_on_Icc
import Submission.Work.Drive.RayTube.ray_fwd_family
import Submission.Work.Drive.RayTube.exists_height_of_ray
import Submission.Work.Drive.RayTube.exists_transverse_of_ray
import Submission.Work.Drive.Rays.oneSidedGlobalize
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.Rays

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

/-- **Two maps which agree on `[0,∞)` and are both differentiable at `0` have the same manifold
derivative at `0`.** -/
lemma mfderiv_eq_of_eqOn_Ici {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {f g : ℝ → M} (hf : MDifferentiableAt MCreal (MC n) f 0)
    (hg : MDifferentiableAt MCreal (MC n) g 0) (h : ∀ t : ℝ, 0 ≤ t → f t = g t) :
    mfderiv MCreal (MC n) f 0 = mfderiv MCreal (MC n) g 0 := by
  have huniq : UniqueMDiffAt[Set.Ici (0:ℝ)] (0:ℝ) :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffWithinAt_Ici 0)
  have hgerm : f =ᶠ[𝓝[Set.Ici (0:ℝ)] 0] g :=
    Filter.Eventually.mono eventually_mem_nhdsWithin (fun t ht => h t ht)
  have h0 : f 0 = g 0 := h 0 le_rfl
  rw [← mfderivWithin_eq_mfderiv (s := Set.Ici (0:ℝ)) huniq hf,
    ← mfderivWithin_eq_mfderiv (s := Set.Ici (0:ℝ)) huniq hg]
  exact Filter.EventuallyEq.mfderivWithin_eq_v433 hgerm h0

/-- **Globalising a ray.**  A map `r : ℝ → M` which is `C^∞` on `[0,∞)` (one-sidedly at `0`),
injective, proper and an immersion *on* `[0,∞)` admits a globally `C^∞` extension `ρ` agreeing with
`r` on `[0,∞)`.

The input `hP1` is the one-dimensional one-sided globalisation of
`Submission/Work/Drive/Rays/oneSidedGlobalize.lean`: it turns the one-sided chart expression of `r`
at `0` into a two-sided smooth function, which is pushed back into the chart and glued (on the
right) to `r` itself. -/
theorem rayGlobalize {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    (hP1 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {h : ℝ → E} {δ : ℝ}, 0 < δ →
      ContDiffWithinAt ℝ smoothOrder h (Set.Ici (0:ℝ)) 0 →
      ContDiffOn ℝ smoothOrder h (Set.Ioo (0:ℝ) δ) →
      ∃ F : ℝ → E, ContDiffOn ℝ smoothOrder F (Set.Ioo (-δ) δ) ∧
        ∀ t : ℝ, 0 ≤ t → t < δ → F t = h t) :
    ∃ ρ : ℝ → M, ContMDiff MCreal (MC n) smoothOrder ρ ∧
      (∀ t : ℝ, 0 ≤ t → ρ t = r t) ∧
      (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t)) := by
  classical
  set E := EuclideanSpace ℝ (Fin n) with hE
  set c : OpenPartialHomeomorph M E := chartAt E (r 0) with hc_def
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (r 0)
  have hmem : r 0 ∈ c.source := mem_chart_source E (r 0)
  -- `r` stays in the chart on a right-neighbourhood of `0`
  have hcont0 : ContinuousWithinAt r (Set.Ici (0:ℝ)) 0 :=
    (hrsm 0 (Set.mem_Ici.mpr le_rfl)).continuousWithinAt
  have hpre : r ⁻¹' c.source ∈ 𝓝[Set.Ici (0:ℝ)] 0 :=
    hcont0.preimage_mem_nhdsWithin (c.open_source.mem_nhds hmem)
  obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → r t ∈ c.source := by
    rcases Metric.mem_nhdsWithin_iff.mp hpre with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, fun t ht0 hlt => hsub ?_⟩
    exact ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]; exact hlt, ht0⟩
  -- the chart expression `h = c ∘ r`
  set h : ℝ → E := fun t => c (r t) with hh_def
  -- smoothness on the right
  have hsm : ContDiffOn ℝ smoothOrder h (Set.Ioo (0:ℝ) δ) := by
    have hr' : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ioo (0:ℝ) δ) :=
      hrsm.mono (fun t ht => le_of_lt (Set.mem_Ioo.mp ht).1)
    have hc' : ContMDiffOn (MC n) (MC n) smoothOrder (c : M → E) c.source :=
      contMDiffOn_of_mem_maximalAtlas hc
    have hcomp : ContMDiffOn MCreal (MC n) smoothOrder (c ∘ r) (Set.Ioo (0:ℝ) δ) :=
      hc'.comp hr' (fun t ht => hδsub t (le_of_lt (Set.mem_Ioo.mp ht).1) (Set.mem_Ioo.mp ht).2)
    have := contMDiffOn_iff_contDiffOn.mp hcomp
    simpa [hh_def, Function.comp_def] using this
  -- one-sided smoothness at `0`
  have h0 : ContDiffWithinAt ℝ smoothOrder h (Set.Ici (0:ℝ)) 0 := by
    set s : Set ℝ := Set.Ici (0:ℝ) ∩ Set.Ioo (-δ) δ with hs_def
    have hr'' : ContMDiffWithinAt MCreal (MC n) smoothOrder r s 0 :=
      (hrsm 0 (Set.mem_Ici.mpr le_rfl)).mono (Set.inter_subset_left)
    have hc' : ContMDiffOn (MC n) (MC n) smoothOrder (c : M → E) c.source :=
      contMDiffOn_of_mem_maximalAtlas hc
    have hc'' : ContMDiffWithinAt (MC n) (MC n) smoothOrder (c : M → E) c.source (r 0) :=
      hc' (r 0) hmem
    have hcomp : ContMDiffWithinAt MCreal (MC n) smoothOrder (c ∘ r) s 0 :=
      hc''.comp 0 hr'' (fun t ht => by
        have ht1 : t ∈ Set.Ici (0:ℝ) := ((Set.mem_inter_iff t _ _).mp ht).1
        have ht2 : t ∈ Set.Ioo (-δ) δ := ((Set.mem_inter_iff t _ _).mp ht).2
        exact hδsub t ht1 (by linarith [(Set.mem_Ioo.mp ht2).2]))
    have hcd : ContDiffWithinAt ℝ smoothOrder (c ∘ r) s 0 :=
      contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
    have hmono : ContDiffWithinAt ℝ smoothOrder (c ∘ r) (Set.Ici (0:ℝ)) 0 :=
      hcd.mono_of_mem_nhdsWithin (by
        rw [Metric.mem_nhdsWithin_iff]
        refine ⟨δ, hδpos, fun y hy => ?_⟩
        have hy1 : y ∈ Set.Ici (0:ℝ) := hy.2
        have hyball : |y| < δ := by
          have h := hy.1
          rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at h
        exact ⟨hy1, by
          rw [Set.mem_Ioo]
          exact ⟨by linarith [(abs_lt.mp hyball).1], (abs_lt.mp hyball).2⟩⟩)
    simpa [hh_def, Function.comp_def] using hmono
  -- the two-sided smooth chart function
  obtain ⟨F, hFsm, hFeq⟩ := hP1 (E := E) (h := h) (δ := δ) hδpos h0 hsm
  -- a radius around `c (r 0)` inside the chart target
  have hF0 : F 0 = c (r 0) := by
    simpa [hh_def] using hFeq 0 le_rfl hδpos
  have hF0mem : F 0 ∈ c.target := by rw [hF0]; exact c.map_source hmem
  have hFcont : ContinuousAt F 0 :=
    (hFsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).continuousAt
  obtain ⟨η₁, hη₁pos, hη₁⟩ : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ y : ℝ, |y| < η₁ → F y ∈ c.target := by
    have hmem' : F ⁻¹' c.target ∈ 𝓝 (0:ℝ) :=
      hFcont.preimage_mem_nhds (c.open_target.mem_nhds hF0mem)
    rcases Metric.mem_nhds_iff.mp hmem' with ⟨η₁, hη₁pos, hsub⟩
    exact ⟨η₁, hη₁pos, fun y hy => hsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hy)⟩
  -- confinement of the parameter
  set η : ℝ := min (δ / 4) (η₁ / 2) with hη_def
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hηδ : η ≤ δ / 4 := min_le_left _ _
  have hηη₁ : η ≤ η₁ / 2 := min_le_right _ _
  set σ : ℝ → ℝ := Work.Crux.confine η with hσ_def
  have hσsm : ContDiff ℝ smoothOrder σ := Work.Crux.confine_contDiff η
  have hσid : ∀ x : ℝ, |x| ≤ η / 2 → σ x = x := fun x hx => Work.Crux.confine_id_of_abs_le hηpos hx
  have hσbd : ∀ x : ℝ, |σ x| ≤ η := fun x => Work.Crux.confine_abs_le hηpos x
  -- the confined chart function
  set F₀ : ℝ → E := fun t => F (σ t) with hF₀_def
  have hF₀sm : ContDiff ℝ smoothOrder F₀ := by
    have h1 : ContDiffOn ℝ smoothOrder F (Set.Ioo (-δ) δ) := hFsm
    have h2 : ContDiffOn ℝ smoothOrder σ Set.univ := hσsm.contDiffOn
    have h3 : Set.MapsTo σ Set.univ (Set.Ioo (-δ) δ) := by
      intro x _
      have hx := abs_le.mp (hσbd x)
      rw [Set.mem_Ioo]
      constructor <;> linarith [hηδ]
    have := contDiffOn_univ.mp (h1.comp h2 h3)
    simpa [hF₀_def, Function.comp_def] using this
  have hF₀mem : ∀ t : ℝ, F₀ t ∈ c.target := by
    intro t
    refine hη₁ (σ t) ?_
    have h1 : |σ t| ≤ η := hσbd t
    linarith [hηη₁]
  -- the curve into the chart
  set ρ₀ : ℝ → M := fun t => c.symm (F₀ t) with hρ₀_def
  have hρ₀sm : ContMDiff MCreal (MC n) smoothOrder ρ₀ := by
    have hcs : ContMDiffOn (MC n) (MC n) smoothOrder (c.symm : E → M) c.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hc
    have hF₀c : ContMDiffOn MCreal (MC n) smoothOrder F₀ Set.univ :=
      (contMDiffOn_iff_contDiffOn.mpr hF₀sm.contDiffOn)
    have hcomp : ContMDiffOn MCreal (MC n) smoothOrder (c.symm ∘ F₀) Set.univ :=
      hcs.comp hF₀c (fun t _ => hF₀mem t)
    exact contMDiffOn_univ.mp (by simpa [hρ₀_def, Function.comp_def] using hcomp)
  have hρ₀eq : ∀ y : ℝ, 0 ≤ y → y ≤ η / 2 → ρ₀ y = r y := by
    intro y hy0 hyη
    have hyabs : |y| ≤ η / 2 := abs_le.mpr ⟨by linarith, hyη⟩
    have hσy : σ y = y := hσid y hyabs
    have hylt : y < δ := by linarith [hηδ]
    have hFy : F y = h y := hFeq y hy0 hylt
    have hyc : r y ∈ c.source := hδsub y hy0 hylt
    have h1 : ρ₀ y = c.symm (F (σ y)) := rfl
    rw [h1, hσy, hFy, hh_def]
    exact c.left_inv hyc
  -- the global curve
  set ρ : ℝ → M := fun t => if t ≤ η / 2 then ρ₀ t else r t with hρ_def
  have hρeq : ∀ t : ℝ, 0 ≤ t → ρ t = r t := by
    intro t ht
    by_cases h : t ≤ η / 2
    · simp only [hρ_def, if_pos h]
      exact hρ₀eq t ht h
    · simp only [hρ_def, if_neg h]
  have hrAt : ∀ t : ℝ, 0 < t → ContMDiffAt MCreal (MC n) smoothOrder r t := by
    intro t ht
    exact (hrsm t (le_of_lt ht)).contMDiffAt
      (Filter.mem_of_superset (isOpen_Ioi.mem_nhds ht) (fun y hy => le_of_lt (Set.mem_Ioi.mp hy)))
  -- smoothness of `ρ`
  have hρsm : ContMDiff MCreal (MC n) smoothOrder ρ := by
    intro t
    rcases lt_trichotomy t (η / 2) with ht | ht | ht
    · -- left of the switch
      refine hρ₀sm.contMDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
      simp only [hρ_def, if_pos (le_of_lt (Set.mem_Iio.mp hy))]
    · -- at the switch: `ρ` agrees with `r` nearby
      subst ht
      have hne : (Set.Ioo (η / 4) η) ∈ 𝓝 (η / 2) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      have hev : ρ =ᶠ[𝓝 (η / 2)] r := by
        filter_upwards [hne] with y hy
        by_cases h : y ≤ η / 2
        · simp only [hρ_def, if_pos h]
          exact hρ₀eq y (by linarith [(Set.mem_Ioo.mp hy).1]) h
        · simp only [hρ_def, if_neg h]
      exact (hrAt (η / 2) (by linarith)).congr_of_eventuallyEq hev
    · -- right of the switch
      refine (hrAt t (by linarith)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
      simp only [hρ_def, if_neg (not_le.mpr (Set.mem_Ioi.mp hy))]
  -- the ray property
  have hρprop : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
      have hρD : MDifferentiableAt MCreal (MC n) ρ 0 := hρsm.mdifferentiableAt hn0
      have hrD : MDifferentiableAt MCreal (MC n) r 0 := by
        by_contra hcon
        have hz : mfderiv MCreal (MC n) r 0 = 0 := mfderiv_zero_of_not_mdifferentiableAt hcon
        have hinj : Function.Injective
            (0 : TangentSpace MCreal (0:ℝ) →L[ℝ] TangentSpace (MC n) (r 0)) := by
          rw [← hz]
          exact hrimm 0 le_rfl
        have h10 : (1:ℝ) = (0:ℝ) :=
          hinj (a₁ := (1 : TangentSpace MCreal (0:ℝ)))
            (a₂ := (0 : TangentSpace MCreal (0:ℝ))) (by simp)
        norm_num at h10
      rw [mfderiv_eq_of_eqOn_Ici hρD hrD hρeq]
      exact hrimm 0 le_rfl
    · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hgerm : ρ =ᶠ[𝓝 t] r := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
        exact hρeq y (le_of_lt hy)
      rw [hgerm.mfderiv_eq_v433 (I := MCreal) (I' := MC n)]
      exact hrimm t ht
  exact ⟨ρ, hρsm, hρeq, hρprop⟩

end

end Work.Drive.Rays

namespace Work.Drive.Rays

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
theorem rayHeightTransverse {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrinj : Set.InjOn r (Set.Ici (0:ℝ)))
    (hrp : IsProperMap (fun t : Set.Ici (0:ℝ) => r t))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    (hrW : ∀ t : ℝ, 0 ≤ t → r t ∈ W) :
    ∃ (g : M → ℝ) (P : M → EuclideanSpace ℝ (Fin (n - 1))),
      ContMDiff (MC n) MCreal smoothOrder g ∧
      ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
      (∀ t : ℝ, 0 ≤ t → g (r t) = t) ∧
      (∀ t : ℝ, 0 ≤ t → P (r t) = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : TangentSpace (MC n) (r t),
        mfderiv (MC n) (MC (n - 1)) P (r t) v = 0 →
        mfderiv (MC n) MCreal g (r t) v = 0 → v = 0) := by
  have hP1 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {h : ℝ → E} {δ : ℝ}, 0 < δ →
      ContDiffWithinAt ℝ smoothOrder h (Set.Ici (0:ℝ)) 0 →
      ContDiffOn ℝ smoothOrder h (Set.Ioo (0:ℝ) δ) →
      ∃ F : ℝ → E, ContDiffOn ℝ smoothOrder F (Set.Ioo (-δ) δ) ∧
        ∀ t : ℝ, 0 ≤ t → t < δ → F t = h t :=
    fun hδ h0 hsm => oneSidedGlobalize hδ h0 hsm
  obtain ⟨ρ, hρsm, hρeq, hρimm⟩ := rayGlobalize (n := n) hn hrsm hrimm hP1
  have hρinj : Set.InjOn ρ (Set.Ici (0:ℝ)) := by
    intro s hs t ht hst
    rw [hρeq s hs, hρeq t ht] at hst
    exact hrinj hs ht hst
  have hρprop : IsProperMap (fun t : Set.Ici (0:ℝ) => ρ t) := by
    have heq : (fun t : Set.Ici (0:ℝ) => ρ t) = (fun t : Set.Ici (0:ℝ) => r t) :=
      funext fun t => hρeq t t.2
    rw [heq]
    exact hrp
  obtain ⟨g, hgsm, hgc⟩ :=
    Work.Drive.RayTube.exists_height_of_ray (n := n) hn hρsm hρinj hρprop hρimm
  obtain ⟨P, hPsm, hPc, hPtr⟩ :=
    Work.Drive.RayTube.exists_transverse_of_ray (n := n) hn hρsm hρinj hρprop hρimm hgsm hgc
  refine ⟨g, P, hgsm, hPsm, ?_, ?_, ?_⟩
  · intro t ht
    rw [← hρeq t ht]
    exact hgc t ht
  · intro t ht
    rw [← hρeq t ht]
    exact hPc t ht
  · intro t ht
    have h : ∀ v : TangentSpace (MC n) (ρ t),
        mfderiv (MC n) (MC (n - 1)) P (ρ t) v = 0 →
        mfderiv (MC n) MCreal g (ρ t) v = 0 → v = 0 := hPtr t ht
    rw [hρeq t ht] at h
    intro v hv1 hv2
    exact h v hv1 hv2

end Work.Drive.Rays
