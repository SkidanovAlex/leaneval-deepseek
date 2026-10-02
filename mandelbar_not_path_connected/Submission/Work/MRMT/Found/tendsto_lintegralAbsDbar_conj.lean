import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_of_ae_tendsto_zero
import Submission.Work.MRMT.Found.differentiableOn_comp_principal_symm
import Submission.Work.MRMT.Found.comp_l2_bound
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.lintegral_comp_le_of_isCompact_disjoint
import Submission.Work.MRMT.Found.conjAux
import Submission.Work.MRMT.Found.dzbar_star_comp
import Submission.Work.MRMT.Found.dzSq_integral_le_area
import Submission.Work.MRMT.Found.uniform_dz_bound
import Submission.Work.MRMT.Found.contDiff_one_of_antiholo
import Submission.Work.MRMT.Found.dzbar_eq_star_deriv_of_antiholo
import Submission.Work.MRMT.Found.norm_pullRev_le
import Submission.Work.MRMT.Found.aestronglyMeasurable_pullRev_sub
import Submission.Work.MRMT.Found.pullback_le_of_antiholo
import Submission.Work.MRMT.AhlforsBers.null_preimage_entire
import Submission.Work.MRMT.Found.ae_tendsto_pullRev_sub
import Submission.Work.MRMT.Found.dz_lintegral_cauchy
import Submission.Work.MRMT.Found.dz_lintegral_bdd
import Submission.Work.MRMT.Found.lintegralAbsDbar_conj_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-- A compact neighbourhood `K₀` of `φ⁻¹(L)` on which `∂̄f` does not vanish. -/
private theorem exists_compact_neighborhood_of_antiholo {μ : ℂ → ℂ}
    (d : PrincipalData μ) {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f))
    {L : Set ℂ} (hL : IsCompact L)
    (hLZ : L ⊆ ((d.φ : ℂ → ℂ) '' {z : ℂ | deriv (star ∘ f) z = 0})ᶜ) :
    ∃ K0 : Set ℂ, IsCompact K0 ∧ (∀ z ∈ K0, dzbar f z ≠ 0) ∧
      (∀ᶠ n in Filter.atTop, ((d.Fn n).symm : ℂ → ℂ) '' L ⊆ K0) := by
  have hKL : IsCompact (((d.φ).symm : ℂ → ℂ) '' L) := hL.image d.φ.symm.continuous
  have hZclosed : IsClosed {z : ℂ | deriv (star ∘ f) z = 0} :=
    isClosed_eq (hf.contDiff.continuous_deriv le_rfl) continuous_const
  have hdisj : ((d.φ).symm : ℂ → ℂ) '' L ⊆ ({z : ℂ | deriv (star ∘ f) z = 0})ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rintro hzZ
    obtain ⟨w, hwL, rfl⟩ := hz
    exact hLZ hwL ⟨((d.φ).symm : ℂ → ℂ) w, hzZ, by simp⟩
  obtain ⟨δ, hδpos, hδsub⟩ := hKL.exists_cthickening_subset_open hZclosed.isOpen_compl hdisj
  refine ⟨Metric.cthickening δ (((d.φ).symm : ℂ → ℂ) '' L), hKL.cthickening, ?_, ?_⟩
  · intro z hz
    have h1 : deriv (star ∘ f) z ≠ 0 := fun h0 => hδsub hz (by simpa using h0)
    rw [dzbar_eq_star_deriv_of_antiholo hf z]
    simpa using h1
  · have hUnif : TendstoUniformlyOn (fun n => ((d.Fn n).symm : ℂ → ℂ))
        ((d.φ).symm : ℂ → ℂ) Filter.atTop L :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_symm_Fn) L hL
    have hε := (Metric.tendstoUniformlyOn_iff.mp hUnif) δ hδpos
    filter_upwards [hε] with n hn y hy
    obtain ⟨w, hwL, rfl⟩ := hy
    refine Metric.mem_cthickening_of_dist_le (((d.Fn n).symm : ℂ → ℂ) w)
      (((d.φ).symm : ℂ → ℂ) w) δ _ (Set.mem_image_of_mem _ hwL) ?_
    rw [dist_comm]; exact (hn w hwL).le

theorem tendsto_lintegralAbsDbar_conj {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ)
    (d : Work.MRMT.Found.PrincipalData μ) {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f))
    (hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      μ z = star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z))
    {L : Set ℂ} (hL : IsCompact L)
    (hLZ : L ⊆ ((d.φ : ℂ → ℂ) '' {z : ℂ | deriv (star ∘ f) z = 0})ᶜ) :
    Filter.Tendsto (fun n => Work.MRMT.Found.lintegralAbsDbar
      (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) L) Filter.atTop (nhds 0) := by
  classical
  by_cases hconst : ∃ c : ℂ, ∀ z, (star ∘ f) z = c
  · -- `star ∘ f` is constant: then `{deriv = 0} = univ` and `L = ∅`
    obtain ⟨c, hc⟩ := hconst
    have hLempty : L = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      obtain ⟨x, hx⟩ := d.φ.surjective z
      refine hLZ hz ⟨x, ?_, hx⟩
      rw [show (star ∘ f) = fun _ => c from funext hc]
      simp
    rw [hLempty]
    have : (fun n : ℕ => lintegralAbsDbar
        (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) (∅ : Set ℂ))
        = fun _ => 0 := by
      funext n; simp [lintegralAbsDbar]
    rw [this]; exact tendsto_const_nhds
  · push_neg at hconst
    have hnc : ¬ ∃ c : ℂ, ∀ z, (star ∘ f) z = c := by
      rintro ⟨c, hc⟩; obtain ⟨z, hz⟩ := hconst c; exact hz (hc z)
    have hfcd : ContDiff ℝ 1 f := contDiff_one_of_antiholo hf
    have hfcont : Continuous f := hfcd.continuous
    have hdzf : ∀ z : ℂ, Work.MRMT.dz f z = 0 := fun z =>
      Work.MRMT.Wirtinger.dz_of_antiholo (hf z)
    have hdzbcont : Continuous (Work.MRMT.dzbar f) := by
      have h1 : Work.MRMT.dzbar f = fun z => star (deriv (star ∘ f) z) :=
        funext fun z => dzbar_eq_star_deriv_of_antiholo hf z
      rw [h1]
      exact continuous_star.comp (hf.contDiff.continuous_deriv le_rfl)
    -- the compact neighbourhood
    obtain ⟨K0, hK0cpt, hK0dzb, hevK⟩ := exists_compact_neighborhood_of_antiholo d hf hL hLZ
    have hΦcpt : IsCompact (f '' K0) := hK0cpt.image hfcont
    -- the uniform bound on `‖∂̄f‖` over `K₀`
    obtain ⟨CF, hCF0, hCF⟩ : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ z ∈ K0, ‖dzbar f z‖ ≤ CF := by
      obtain ⟨M, hM⟩ := hK0cpt.exists_bound_of_continuousOn hdzbcont.continuousOn
      exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩
    -- the pull-back bound
    obtain ⟨Cp, hCp, hpull⟩ := pullback_le_of_antiholo hf hK0cpt hK0dzb
    -- the coefficient `ν n = pullRev (μn n) f - μn n`
    have hνmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun z => pullRev (d.μn n) f z - d.μn n z) (volume : Measure ℂ) := fun n =>
      aestronglyMeasurable_pullRev_sub hf (d.contDiff_μn n).continuous
    have hν0 : ∀ᵐ z ∂(volume : Measure ℂ),
        Tendsto (fun n => pullRev (d.μn n) f z - d.μn n z) atTop (𝓝 0) :=
      ae_tendsto_pullRev_sub d hf hnc hinv
    have hνb : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
        ‖pullRev (d.μn n) f z - d.μn n z‖ ≤ B := by
      refine ⟨2, by norm_num, fun n => Eventually.of_forall fun z => ?_⟩
      have h1 : ‖pullRev (d.μn n) f z - d.μn n z‖
          ≤ ‖d.μn n (f z)‖ + ‖d.μn n z‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_pullRev_le (hdzf z)
      have h2 := d.norm_μn n (f z)
      have h3 := d.norm_μn n z
      linarith [h1, h2, h3, d.hk]
    -- the `L²`-bounds for `dz (F n)`
    have hρmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z) (volume : Measure ℂ) := fun n =>
      (Work.MRMT.QC.measurable_dz _).aestronglyMeasurable
    have hρcau := dz_lintegral_cauchy d (hK0cpt.union hΦcpt)
    have hρbdd := dz_lintegral_bdd d (hK0cpt.union hΦcpt)
    have hmain := tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2 (Ω := K0) (Φ := f '' K0)
      hK0cpt.measurableSet hK0cpt.measure_lt_top.ne hΦcpt.measurableSet
      hΦcpt.measure_lt_top.ne hfcont ⟨Cp, hCp, hpull⟩ hνmeas hν0 hνb hρmeas hρcau hρbdd
    -- squeeze
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n => ENNReal.ofReal CF * ∫⁻ z in K0,
        ENNReal.ofReal (‖pullRev (d.μn n) f z - d.μn n z‖
          * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
          * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖))
      tendsto_const_nhds ?_ (Eventually.of_forall fun n => bot_le) ?_
    · have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CF) hmain
        (Or.inr ENNReal.ofReal_ne_top)
      simpa [mul_zero] using h
    · filter_upwards [hevK] with n hn
      have him : ((d.Fn n) : ℂ → ℂ) '' (((d.Fn n).symm : ℂ → ℂ) '' L) = L := by
        rw [Set.image_image]
        have h : (fun x => (d.Fn n) ((d.Fn n).symm x)) = id := by
          funext x; exact Homeomorph.apply_symm_apply _ x
        rw [h, Set.image_id]
      have hKncpt : IsCompact (((d.Fn n).symm : ℂ → ℂ) '' L) :=
        hL.image (d.contDiff_symm_Fn n).continuous
      calc lintegralAbsDbar (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) L
          = lintegralAbsDbar (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ))
              (((d.Fn n) : ℂ → ℂ) '' (((d.Fn n).symm : ℂ → ℂ) '' L)) := by rw [him]
        _ ≤ ENNReal.ofReal CF * ∫⁻ z in (((d.Fn n).symm : ℂ → ℂ) '' L),
              ENNReal.ofReal (‖pullRev (d.μn n) f z - d.μn n z‖
                * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
                * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) :=
            lintegralAbsDbar_conj_le d hf hKncpt hCF0 (fun z hz => hCF z (hn hz)) n
        _ ≤ ENNReal.ofReal CF * ∫⁻ z in K0,
              ENNReal.ofReal (‖pullRev (d.μn n) f z - d.μn n z‖
                * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖
                * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) := by
            gcongr

end Work.MRMT.Found
