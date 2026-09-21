import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Analysis.Abel.hasDerivAt_invSqrt_weighted_affine

noncomputable section

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Commons.Analysis.Abel

lemma continuousOn_K_affine_slice_of_mem_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b x σ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo a b) :
    ContinuousOn (fun τ : ℝ => K (x + τ * (σ - x)) σ) (Set.uIcc (0:ℝ) 1) := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  have hG_cont : ContinuousOn G (Set.Icc a b ×ˢ Set.Icc a b) := hK_cont.continuousOn
  have hpath_cont : ContinuousOn (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) := by
    have hc1 : Continuous (fun τ : ℝ => x + τ * (σ - x)) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (hc1.prodMk continuous_const).continuousOn
  have hpath_mem : Set.MapsTo (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1)
      (Set.Icc a b ×ˢ Set.Icc a b) := by
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    let y : ℝ := x + τ * (σ - x)
    have hy_mem : y ∈ Set.Ioo a b := by
      have hconv : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
      have hmem := hconv.add_smul_sub_mem hx hσ hτ'
      dsimp [y]
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    constructor
    · exact ⟨le_of_lt hy_mem.1, le_of_lt hy_mem.2⟩
    · exact ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  have hcomp : ContinuousOn (fun τ : ℝ => G (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) :=
    hG_cont.comp' hpath_cont hpath_mem
  simpa [G] using hcomp

lemma continuousOn_fderiv_K_affine_slice_of_mem_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b x σ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo a b) :
    ContinuousOn (fun τ : ℝ => fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2)
      (x + τ * (σ - x), σ) (1, 0)) (Set.uIcc (0:ℝ) 1) := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  let O : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo a b
  have hG_contOnO : ContDiffOn ℝ 2 G O := by
    exact hK_cont.mono (by
      intro p hp
      exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩)
  have hfd_contO : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G p) O := by
    have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ G p) O :=
      hG_contOnO.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_Ioo) (by norm_num : (0:WithTop ℕ∞) + 1 ≤ 2)
    exact h1.continuousOn
  have hpath_cont : ContinuousOn (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) := by
    have hc1 : Continuous (fun τ : ℝ => x + τ * (σ - x)) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (hc1.prodMk continuous_const).continuousOn
  have hpath_mem : Set.MapsTo (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) O := by
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    let y : ℝ := x + τ * (σ - x)
    have hy_mem : y ∈ Set.Ioo a b := by
      have hconv : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
      have hmem := hconv.add_smul_sub_mem hx hσ hτ'
      dsimp [y]
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    exact ⟨hy_mem, hσ⟩
  have hfd : ContinuousOn (fun τ : ℝ => fderiv ℝ G (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) :=
    hfd_contO.comp' hpath_cont hpath_mem
  have happly : ContinuousOn (fun τ : ℝ => (fderiv ℝ G (x + τ * (σ - x), σ)) (1, 0))
      (Set.uIcc (0:ℝ) 1) :=
    hfd.clm_apply continuousOn_const
  simpa [G] using happly

lemma hasDerivAt_K_affine_slice_of_mem_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b x σ τ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo a b) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun v : ℝ => K (v + τ * (σ - v)) σ)
      ((1 - τ) • fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2)
        (x + τ * (σ - x), σ) (1, 0)) x := by
  let K2 : ℝ × ℝ → E := fun p => K p.1 p.2
  have hK2 : ContDiffOn ℝ 2 K2 (Set.Icc a b ×ˢ Set.Icc a b) := by simpa [K2] using hK_cont
  let p : ℝ × ℝ := (x + τ * (σ - x), σ)
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < 1 := hτ.2
  have h1τ_pos : 0 < 1 - τ := by linarith
  have hp_mem : p ∈ Set.Ioo a b ×ˢ Set.Ioo a b := by
    constructor
    · dsimp [p]
      rw [Set.mem_Ioo]
      constructor
      · have hxa : a < x := hx.1
        have hσa : a < σ := hσ.1
        have h1 : a = (1 - τ) * a + τ * a := by ring
        rw [h1]
        have hmul1 : (1 - τ) * a < (1 - τ) * x := mul_lt_mul_of_pos_left hxa h1τ_pos
        have hmul2 : τ * a < τ * σ := mul_lt_mul_of_pos_left hσa hτ0
        nlinarith
      · have hxb : x < b := hx.2
        have hσb : σ < b := hσ.2
        have h1 : b = (1 - τ) * b + τ * b := by ring
        rw [h1]
        have hmul1 : (1 - τ) * x < (1 - τ) * b := mul_lt_mul_of_pos_left hxb h1τ_pos
        have hmul2 : τ * σ < τ * b := mul_lt_mul_of_pos_left hσb hτ0
        nlinarith
    · exact hσ
  have h_open : IsOpen (Set.Ioo a b ×ˢ Set.Ioo a b) := (isOpen_Ioo.prod isOpen_Ioo)
  have h_nhds : Set.Ioo a b ×ˢ Set.Ioo a b ∈ 𝓝 p := h_open.mem_nhds hp_mem
  have h_sub : Set.Ioo a b ×ˢ Set.Ioo a b ⊆ Set.Icc a b ×ˢ Set.Icc a b := by
    intro q hq
    exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
  have h_nhds2 : Set.Icc a b ×ˢ Set.Icc a b ∈ 𝓝 p := mem_of_superset h_nhds h_sub
  have hK2diff : DifferentiableAt ℝ K2 p := by
    have hcont := hK2.contDiffAt (s := Set.Icc a b ×ˢ Set.Icc a b) h_nhds2
    exact hcont.differentiableAt (by norm_num)
  have hK2fderiv : HasFDerivAt K2 (fderiv ℝ K2 p) p := hK2diff.hasFDerivAt
  have hγ1 : HasDerivAt (fun v : ℝ => v + τ * (σ - v)) (1 - τ) x := by
    have h1 : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun v : ℝ => τ * (σ - v)) (-τ) x := by
      have hx : HasDerivAt (fun v : ℝ => σ - v) (-1) x := (hasDerivAt_id x).const_sub σ
      simpa using hx.const_mul τ
    have hsum : HasDerivAt (fun v : ℝ => v + τ * (σ - v)) (1 + (-τ)) x := h1.add h2
    simpa [sub_eq_add_neg] using hsum
  have hγ2 : HasDerivAt (fun _ : ℝ => σ) 0 x := hasDerivAt_const x σ
  have hγ : HasDerivAt (fun v : ℝ => (v + τ * (σ - v), σ)) (1 - τ, 0) x :=
    hγ1.prodMk hγ2
  have hcomp := hK2fderiv.comp_hasDerivAt x hγ
  have hlin : fderiv ℝ K2 p (1 - τ, 0) = (1 - τ) • fderiv ℝ K2 p (1, 0) := by
    have hvec : ((1 - τ, 0) : ℝ × ℝ) = (1 - τ) • ((1, 0) : ℝ × ℝ) := by
      ext <;> simp [mul_zero]
    rw [hvec, map_smul]
  have hcomp' : HasDerivAt (fun v : ℝ => K2 (v + τ * (σ - v), σ))
      ((1 - τ) • fderiv ℝ K2 p (1, 0)) x := hcomp.congr_deriv hlin
  simpa [K2, p] using hcomp'

lemma hasDerivAt_invSqrt_weighted_affine_of_mem_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b x σ : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo a b) :
    HasDerivAt
      (fun u : ℝ => ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      (∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          ((1 - τ) • fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2)
            (x + τ * (σ - x), σ) (1, 0))) x := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  let F : ℝ → ℝ → E := fun u τ => w τ • K (u + τ * (σ - u)) σ
  let F' : ℝ → ℝ → E :=
    fun u τ => w τ • ((1 - τ) • fderiv ℝ G (u + τ * (σ - u), σ) (1, 0))

  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight

  have hmeas_weight : Measurable w := by
    unfold w
    fun_prop

  let m : ℝ := min (min (x - a) (b - x)) (min (σ - a) (b - σ))
  let δ : ℝ := m / 2
  have hxa_pos : 0 < x - a := sub_pos.mpr hx.1
  have hbx_pos : 0 < b - x := sub_pos.mpr hx.2
  have hσa_pos : 0 < σ - a := sub_pos.mpr hσ.1
  have hbσ_pos : 0 < b - σ := sub_pos.mpr hσ.2
  have hmin1_pos : 0 < min (x - a) (b - x) := lt_min hxa_pos hbx_pos
  have hmin2_pos : 0 < min (σ - a) (b - σ) := lt_min hσa_pos hbσ_pos
  have hm_pos : 0 < m := by dsimp [m]; exact lt_min hmin1_pos hmin2_pos
  have hm_le_xa : m ≤ x - a := by dsimp [m]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hm_le_bx : m ≤ b - x := by dsimp [m]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hm_le_σa : m ≤ σ - a := by dsimp [m]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm_le_bσ : m ≤ b - σ := by dsimp [m]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδpos : 0 < δ := by dsimp [δ]; exact half_pos hm_pos
  let U : Set ℝ := Metric.ball x δ
  have hU_nhds : U ∈ 𝓝 x := by
    dsimp [U]
    exact Metric.ball_mem_nhds x hδpos
  have hU_mem : ∀ v ∈ U, v ∈ Set.Ioo a b := by
    intro v hv
    have hdist : |v - x| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hv
    have hδ_lt_xa : δ < x - a := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_xa
    have hδ_lt_bx : δ < b - x := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_bx
    have h1 : |v - x| < x - a := lt_trans hdist hδ_lt_xa
    have h2 : |v - x| < b - x := lt_trans hdist hδ_lt_bx
    constructor
    · have h1' : -(x - a) < v - x ∧ v - x < x - a := abs_lt.mp h1
      linarith
    · have h2' : -(b - x) < v - x ∧ v - x < b - x := abs_lt.mp h2
      linarith

  have hF_meas : ∀ᶠ v in 𝓝 x, AEStronglyMeasurable (F v) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hU_nhds] with v hv
    have hv' := hU_mem v hv
    have hg_cont : ContinuousOn (fun τ : ℝ => K (v + τ * (σ - v)) σ) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_K_affine_slice_of_mem_Ioo (E := E) hK_cont hv' hσ
    have hg_ae : AEStronglyMeasurable (fun τ : ℝ => K (v + τ * (σ - v)) σ)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hg_cont.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) :=
      hmeas_weight.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun τ : ℝ => w τ • K (v + τ * (σ - v)) σ)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hg_ae
    simpa [F] using hprod

  have hF_int : IntervalIntegrable (F x) volume (0:ℝ) 1 := by
    have hg_cont : ContinuousOn (fun τ : ℝ => K (x + τ * (σ - x)) σ) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_K_affine_slice_of_mem_Ioo (E := E) hK_cont hx hσ
    have h := hw_int.smul_continuousOn hg_cont
    simpa [F] using h

  have hF'_meas : AEStronglyMeasurable (F' x) (volume.restrict (Ι (0:ℝ) 1)) := by
    have hfd_cont0 : ContinuousOn
        (fun τ : ℝ => fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)) (Set.uIcc (0:ℝ) 1) := by
      simpa [G] using continuousOn_fderiv_K_affine_slice_of_mem_Ioo (E := E) hK_cont hx hσ
    have hD_cont : ContinuousOn
        (fun τ : ℝ => (1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)) (Set.uIcc (0:ℝ) 1) := by
      have hscalar : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.uIcc (0:ℝ) 1) := by
        exact (continuousOn_const.sub continuousOn_id : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.uIcc (0:ℝ) 1))
      exact hscalar.smul hfd_cont0
    have hD_ae : AEStronglyMeasurable
        (fun τ : ℝ => (1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0))
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hD_cont.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) :=
      hmeas_weight.aestronglyMeasurable
    have hprod : AEStronglyMeasurable
        (fun τ : ℝ => w τ • ((1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)))
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hD_ae
    simpa [F', G] using hprod

  let A : ℝ := min (x - δ) σ
  let B : ℝ := max (x + δ) σ
  let Cset : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc σ σ
  let O : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo a b
  have hδ_lt_xa : δ < x - a := by
    dsimp [δ]
    exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_xa
  have hδ_lt_bx : δ < b - x := by
    dsimp [δ]
    exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_bx
  have hδ_lt_σa : δ < σ - a := by
    dsimp [δ]
    exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_σa
  have hδ_lt_bσ : δ < b - σ := by
    dsimp [δ]
    exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_bσ
  have hA_gt_a : a < A := by
    dsimp [A]
    have hxa : a < x - δ := by linarith
    have hσa : a < σ := hσ.1
    exact lt_min hxa hσa
  have hB_lt_b : B < b := by
    dsimp [B]
    have hxb : x + δ < b := by linarith
    have hσb : σ < b := hσ.2
    exact max_lt hxb hσb
  have hCset_sub_O : Cset ⊆ O := by
    intro q hq
    have hq1 := hq.1
    have hq2 := hq.2
    have hq2_eq : q.2 = σ := le_antisymm hq2.2 hq2.1
    constructor
    · constructor
      · exact lt_of_lt_of_le hA_gt_a hq1.1
      · exact lt_of_le_of_lt hq1.2 hB_lt_b
    · constructor
      · rw [hq2_eq]; exact hσ.1
      · rw [hq2_eq]; exact hσ.2
  have hG_contOnO : ContDiffOn ℝ 2 G O := by
    exact hK_cont.mono (by
      intro p hp
      exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩)
  have hfd_contO : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G p) O := by
    have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ G p) O :=
      hG_contOnO.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_Ioo) (by norm_num : (0:WithTop ℕ∞) + 1 ≤ 2)
    exact h1.continuousOn
  have hfd_apply_contO : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) O :=
    hfd_contO.clm_apply continuousOn_const
  have hCset_compact : IsCompact Cset := by
    dsimp [Cset]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hCset_compact.exists_bound_of_continuousOn (hfd_apply_contO.mono hCset_sub_O)
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ q ∈ Cset, ‖fderiv ℝ G q (1, 0)‖ ≤ C := by
    intro q hq
    exact le_trans (hC0 q hq) (by dsimp [C]; exact le_max_left _ _)

  have hpt_Cset : ∀ v ∈ U, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      (v + τ * (σ - v), σ) ∈ Cset := by
    intro v hv τ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hdist : |v - x| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hv
    have hv_gt : x - δ < v := by
      have h' : -(δ) < v - x := (abs_lt.mp hdist).1
      linarith
    have hv_lt : v < x + δ := by
      have h' : v - x < δ := (abs_lt.mp hdist).2
      linarith
    have hv_in : v ∈ Set.Icc A B := by
      constructor
      · dsimp [A]; exact le_trans (min_le_left _ _) (le_of_lt hv_gt)
      · dsimp [B]; exact le_of_lt (lt_of_lt_of_le hv_lt (le_max_left _ _))
    have hσ_in : σ ∈ Set.Icc A B := by
      constructor
      · dsimp [A]; exact min_le_right _ _
      · dsimp [B]; exact le_max_right _ _
    have hconv : Convex ℝ (Set.Icc A B) := convex_Icc A B
    have hy_mem : v + τ * (σ - v) ∈ Set.Icc A B := by
      have hmem := hconv.add_smul_sub_mem hv_in hσ_in hτ
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    constructor
    · exact hy_mem
    · exact ⟨le_rfl, le_rfl⟩

  have hbound_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
    simpa using hw_int.const_mul C

  have h_bound : ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ∀ v ∈ U, ‖F' v τ‖ ≤ C * w τ := by
    filter_upwards with τ hτ
    intro v hv
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hτ_rect : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ0, hτ1⟩
    have hpt := hpt_Cset v hv τ hτ_rect
    have hfderiv_norm : ‖fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖ ≤ C := hC_bound _ hpt
    have hw_nonneg : 0 ≤ w τ := by
      unfold w
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h_abs_1_sub : |1 - τ| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hτ1)]
      linarith
    have hDnorm : ‖(1 - τ) • fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖ ≤ C := by
      calc
        ‖(1 - τ) • fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖
            = |1 - τ| * ‖fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖ := norm_smul _ _
        _ ≤ 1 * C := mul_le_mul h_abs_1_sub hfderiv_norm (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    calc
      ‖F' v τ‖ = ‖w τ • ((1 - τ) • fderiv ℝ G (v + τ * (σ - v), σ) (1, 0))‖ := by
        simp [F', G]
      _ = |w τ| * ‖(1 - τ) • fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖ := norm_smul _ _
      _ = w τ * ‖(1 - τ) • fderiv ℝ G (v + τ * (σ - v), σ) (1, 0)‖ := by
        rw [abs_of_nonneg hw_nonneg]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hDnorm hw_nonneg
      _ = C * w τ := mul_comm _ _

  have h_diff : ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ∀ v ∈ U,
      HasDerivAt (fun u : ℝ => F u τ) (F' v τ) v := by
    filter_upwards with τ hτ
    intro v hv
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 < τ := hτ'.1
    have hv' := hU_mem v hv
    by_cases hτeq : τ = 1
    · subst τ
      have hfun : (fun u : ℝ => F u 1) = fun _ => 0 := by
        funext u
        simp [F, w]
      have hder : HasDerivAt (fun u : ℝ => F u 1) (F' v 1) v := by
        rw [hfun]
        simp [F', w, G]
        exact hasDerivAt_const v 0
      simpa using hder
    · have hτ_oo : τ ∈ Set.Ioo (0:ℝ) 1 := ⟨hτ0, lt_of_le_of_ne hτ'.2 hτeq⟩
      have hderivK := hasDerivAt_K_affine_slice_of_mem_Ioo (E := E) hK_cont hv' hσ hτ_oo
      have hderivF := hderivK.const_smul (w τ)
      have hfun_event : (fun u : ℝ => w τ • K (u + τ * (σ - u)) σ) =ᶠ[𝓝 v]
          (w τ • fun u : ℝ => K (u + τ * (σ - u)) σ) := by
        apply Filter.Eventually.of_forall
        intro u
        rfl
      have hderivF' := hderivF.congr_of_eventuallyEq hfun_event
      simpa [F, F', G, w] using hderivF'

  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := E) (a := (0:ℝ)) (b := (1:ℝ))
    (F := F) (F' := F') (x₀ := x) (s := U) (bound := fun τ : ℝ => C * w τ)
    hU_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hmain := hdom.2
  simpa [F, F', G, w] using hmain



lemma continuousOn_fderivWithin_K_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      fderivWithin ℝ (fun q : ℝ × ℝ => K q.1 q.2) (Set.Icc a b ×ˢ Set.Icc a b) p (1, 0))
      (Set.Icc a b ×ˢ Set.Icc a b) := by
  let K2 : ℝ × ℝ → E := fun p => K p.1 p.2
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  have hK2 : ContDiffOn ℝ 2 K2 S := by simpa [K2, S] using hK_cont
  have hUnique : UniqueDiffOn ℝ S := by
    dsimp [S]
    exact (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hab)
  have hfd : ContDiffOn ℝ 0 (fderivWithin ℝ K2 S) S :=
    hK2.fderivWithin hUnique (by norm_num : (0:WithTop ℕ∞) + 1 ≤ 2)
  have hfd_cont : ContinuousOn (fderivWithin ℝ K2 S) S := hfd.continuousOn
  have happly : ContinuousOn (fun p : ℝ × ℝ => fderivWithin ℝ K2 S p (1, 0)) S :=
    hfd_cont.clm_apply continuousOn_const
  simpa [K2, S] using happly



lemma continuousOn_K_affine_slice_fixed_first
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b v σ : ℝ} {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hv : v ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) :
    ContinuousOn (fun τ : ℝ => K (v + τ * (σ - v)) σ) (Set.uIcc (0:ℝ) 1) := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  have hpath_cont : ContinuousOn (fun τ : ℝ => (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1) := by
    have hc1 : Continuous (fun τ : ℝ => v + τ * (σ - v)) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (hc1.prodMk continuous_const).continuousOn
  have hpath_mem : Set.MapsTo (fun τ : ℝ => (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1)
      (Set.Icc a b ×ˢ Set.Icc a b) := by
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hv hσ hτ'
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    exact ⟨hfirst, hσ⟩
  have hcomp : ContinuousOn (fun τ : ℝ => G (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1) :=
    hK_cont.comp' hpath_cont hpath_mem
  simpa [G] using hcomp

lemma continuousOn_K_affine_slice_fixed_first_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b v τ c d : ℝ} {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hv : v ∈ Set.Icc a b) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc a b) :
    ContinuousOn (fun σ : ℝ => K (v + τ * (σ - v)) σ) (Set.Icc c d) := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  have hpath_cont : ContinuousOn (fun σ : ℝ => (v + τ * (σ - v), σ)) (Set.Icc c d) := by
    have hc1 : Continuous (fun σ : ℝ => v + τ * (σ - v)) :=
      continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
    exact (hc1.prodMk continuous_id).continuousOn
  have hpath_mem : Set.MapsTo (fun σ : ℝ => (v + τ * (σ - v), σ)) (Set.Icc c d)
      (Set.Icc a b ×ˢ Set.Icc a b) := by
    intro σ hσ
    have hσ_ab : σ ∈ Set.Icc a b := hcd_sub hσ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ0, hτ1⟩
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hv hσ_ab hτ'
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    exact ⟨hfirst, hσ_ab⟩
  have hcomp : ContinuousOn (fun σ : ℝ => G (v + τ * (σ - v), σ)) (Set.Icc c d) :=
    hK_cont.comp' hpath_cont hpath_mem
  simpa [G] using hcomp

lemma continuousOn_intervalIntegral_weighted_smul_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w ρ : ℝ → ℝ} {H : ℝ → ℝ → E} {a b v c d : ℝ}
    (hw_int : IntervalIntegrable w volume (0:ℝ) 1)
    (hmeas_w : Measurable w)
    (hw_nonneg : ∀ τ, 0 ≤ w τ)
    (hρ_cont : ContinuousOn ρ (Set.uIcc (0:ℝ) 1))
    (hρ_bound : ∀ τ ∈ Set.uIcc (0:ℝ) 1, |ρ τ| ≤ 1)
    (hH_cont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hv : v ∈ Set.Icc a b) (hcd_sub : Set.Icc c d ⊆ Set.Icc a b) :
    ContinuousOn (fun σ : ℝ => ∫ τ in (0:ℝ)..(1:ℝ),
      w τ • (ρ τ • H (v + τ * (σ - v)) σ)) (Set.Icc c d) := by
  let F : ℝ → ℝ → E := fun σ τ => w τ • (ρ τ • H (v + τ * (σ - v)) σ)
  let H2 : ℝ × ℝ → E := fun p => H p.1 p.2
  have hH2_cont : ContinuousOn H2 (Set.Icc a b ×ˢ Set.Icc a b) := hH_cont
  have hcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcomp.exists_bound_of_continuousOn hH2_cont.norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc a b, ‖H2 p‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  have hbound_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
    simpa using hw_int.const_mul C

  have hbound_all : ∀ σ ∈ Set.Icc c d, ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ‖F σ τ‖ ≤ C * w τ := by
    intro σ hσ
    filter_upwards with τ hτ
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hσ_ab : σ ∈ Set.Icc a b := hcd_sub hσ
    have hτ_rect : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ0, hτ1⟩
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hv hσ_ab hτ_rect
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hH_norm : ‖H (v + τ * (σ - v)) σ‖ ≤ C := by
      simpa [H2] using hC_bound (v + τ * (σ - v), σ) ⟨hfirst, hσ_ab⟩
    have hρ_le : |ρ τ| ≤ 1 := hρ_bound τ (by simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ_rect)
    have hDnorm : ‖ρ τ • H (v + τ * (σ - v)) σ‖ ≤ C := by
      calc
        ‖ρ τ • H (v + τ * (σ - v)) σ‖ = |ρ τ| * ‖H (v + τ * (σ - v)) σ‖ := norm_smul _ _
        _ ≤ 1 * C := mul_le_mul hρ_le hH_norm (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    calc
      ‖F σ τ‖ = ‖w τ • (ρ τ • H (v + τ * (σ - v)) σ)‖ := by simp [F]
      _ = |w τ| * ‖ρ τ • H (v + τ * (σ - v)) σ‖ := norm_smul _ _
      _ = w τ * ‖ρ τ • H (v + τ * (σ - v)) σ‖ := by rw [abs_of_nonneg (hw_nonneg τ)]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hDnorm (hw_nonneg τ)
      _ = C * w τ := mul_comm _ _

  have hF_meas_event : ∀ σ₀ ∈ Set.Icc c d, ∀ᶠ σ in 𝓝[Set.Icc c d] σ₀,
      AEStronglyMeasurable (F σ) (volume.restrict (Ι (0:ℝ) 1)) := by
    intro σ₀ hσ₀
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hH_slice : ContinuousOn (fun τ : ℝ => H (v + τ * (σ - v)) σ) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_K_affine_slice_fixed_first (E := E) hH_cont hv (hcd_sub hσ)
    have hD_slice : ContinuousOn (fun τ : ℝ => ρ τ • H (v + τ * (σ - v)) σ) (Set.uIcc (0:ℝ) 1) :=
      hρ_cont.smul hH_slice
    have hD_ae : AEStronglyMeasurable (fun τ : ℝ => ρ τ • H (v + τ * (σ - v)) σ)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hD_slice.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) :=
      hmeas_w.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun τ : ℝ => w τ • (ρ τ • H (v + τ * (σ - v)) σ))
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hD_ae
    simpa [F] using hprod

  have h_cont_event : ∀ σ₀ ∈ Set.Icc c d, ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 →
      ContinuousWithinAt (fun σ : ℝ => F σ τ) (Set.Icc c d) σ₀ := by
    intro σ₀ hσ₀
    filter_upwards with τ hτ
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hH_sigma : ContinuousOn (fun σ : ℝ => H (v + τ * (σ - v)) σ) (Set.Icc c d) :=
      continuousOn_K_affine_slice_fixed_first_sigma (E := E) hH_cont hv hτ0 hτ1 hcd_sub
    have hF_sigma : ContinuousOn (fun σ : ℝ => w τ • (ρ τ • H (v + τ * (σ - v)) σ)) (Set.Icc c d) := by
      have h1 : ContinuousOn (fun σ : ℝ => ρ τ • H (v + τ * (σ - v)) σ) (Set.Icc c d) :=
        hH_sigma.const_smul (ρ τ)
      change ContinuousOn (fun σ : ℝ => w τ • (ρ τ • H (v + τ * (σ - v)) σ)) (Set.Icc c d)
      exact (continuousOn_const.smul h1 : ContinuousOn (fun σ : ℝ => (fun _ : ℝ => w τ) σ • (fun σ : ℝ => ρ τ • H (v + τ * (σ - v)) σ) σ) (Set.Icc c d))
    exact hF_sigma.continuousWithinAt hσ₀

  intro σ₀ hσ₀
  have h := intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := F) (x₀ := σ₀) (bound := fun τ : ℝ => C * w τ) (a := (0:ℝ)) (b := (1:ℝ))
    (s := Set.Icc c d)
    (hF_meas_event σ₀ hσ₀)
    ?_ hbound_int (h_cont_event σ₀ hσ₀)
  · simpa [F] using h
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact hbound_all σ hσ






lemma continuousAt_invSqrt_weighted_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b u0 σ0 : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hu0 : u0 ∈ Set.Ioo a b) (hσ0 : σ0 ∈ Set.Ioo a b) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ τ in (0:ℝ)..(1:ℝ),
      (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (p.1 + τ * (p.2 - p.1)) p.2)
      (u0, σ0) := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let F : ℝ × ℝ → ℝ → E := fun p τ => w τ • K (p.1 + τ * (p.2 - p.1)) p.2
  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have hmeas_w : Measurable w := by
    unfold w
    fun_prop
  have hw_nonneg : ∀ τ, 0 ≤ w τ := by
    intro τ; unfold w; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hS_compact : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hK_cont.norm
  let C : ℝ := max C0 0
  have hC_bound : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc a b, ‖K p.1 p.2‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  have hbound_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
    simpa using hw_int.const_mul C

  let m : ℝ := min (min (u0 - a) (b - u0)) (min (σ0 - a) (b - σ0))
  let δ : ℝ := m / 2
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_min (lt_min (sub_pos.mpr hu0.1) (sub_pos.mpr hu0.2))
      (lt_min (sub_pos.mpr hσ0.1) (sub_pos.mpr hσ0.2))
  have hδpos : 0 < δ := by dsimp [δ]; exact half_pos hm_pos
  let U : Set (ℝ × ℝ) := Metric.ball (u0, σ0) δ
  have hU_nhds : U ∈ 𝓝 (u0, σ0) := by
    dsimp [U]
    exact Metric.ball_mem_nhds (u0, σ0) hδpos
  have hU_mem : ∀ p ∈ U, p.1 ∈ Set.Ioo a b ∧ p.2 ∈ Set.Ioo a b := by
    intro p hp
    have hdist : dist p (u0, σ0) < δ := by
      simpa [U, Metric.mem_ball] using hp
    have hnorm : max |p.1 - u0| |p.2 - σ0| < δ := by
      simpa [Prod.dist_eq, Real.dist_eq] using hdist
    have h1 : |p.1 - u0| < δ := lt_of_le_of_lt (le_max_left _ _) hnorm
    have h2 : |p.2 - σ0| < δ := lt_of_le_of_lt (le_max_right _ _) hnorm
    have hm_le_u0a : m ≤ u0 - a := by dsimp [m]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hm_le_bu0 : m ≤ b - u0 := by dsimp [m]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm_le_σ0a : m ≤ σ0 - a := by dsimp [m]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hm_le_bσ0 : m ≤ b - σ0 := by dsimp [m]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ_lt_u0a : δ < u0 - a := by dsimp [δ]; exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_u0a
    have hδ_lt_bu0 : δ < b - u0 := by dsimp [δ]; exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_bu0
    have hδ_lt_σ0a : δ < σ0 - a := by dsimp [δ]; exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_σ0a
    have hδ_lt_bσ0 : δ < b - σ0 := by dsimp [δ]; exact lt_of_lt_of_le (half_lt_self hm_pos) hm_le_bσ0
    have h1a : |p.1 - u0| < u0 - a := lt_trans h1 hδ_lt_u0a
    have h1b : |p.1 - u0| < b - u0 := lt_trans h1 hδ_lt_bu0
    have h2a : |p.2 - σ0| < σ0 - a := lt_trans h2 hδ_lt_σ0a
    have h2b : |p.2 - σ0| < b - σ0 := lt_trans h2 hδ_lt_bσ0
    constructor
    · constructor
      · have h' : -(u0 - a) < p.1 - u0 ∧ p.1 - u0 < u0 - a := abs_lt.mp h1a
        linarith
      · have h' : -(b - u0) < p.1 - u0 ∧ p.1 - u0 < b - u0 := abs_lt.mp h1b
        linarith
    · constructor
      · have h' : -(σ0 - a) < p.2 - σ0 ∧ p.2 - σ0 < σ0 - a := abs_lt.mp h2a
        linarith
      · have h' : -(b - σ0) < p.2 - σ0 ∧ p.2 - σ0 < b - σ0 := abs_lt.mp h2b
        linarith

  have hF_meas : ∀ᶠ p in 𝓝 (u0, σ0), AEStronglyMeasurable (F p) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hU_nhds] with p hp
    have hp' := hU_mem p hp
    have hp1_Icc : p.1 ∈ Set.Icc a b := ⟨le_of_lt hp'.1.1, le_of_lt hp'.1.2⟩
    have hp2_Icc : p.2 ∈ Set.Icc a b := ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩
    have hK_slice : ContinuousOn (fun τ : ℝ => K (p.1 + τ * (p.2 - p.1)) p.2) (Set.uIcc (0:ℝ) 1) := by
      have hpath_cont : ContinuousOn (fun τ : ℝ => (p.1 + τ * (p.2 - p.1), p.2)) (Set.uIcc (0:ℝ) 1) := by
        have hc1 : Continuous (fun τ : ℝ => p.1 + τ * (p.2 - p.1)) :=
          continuous_const.add (continuous_id.mul continuous_const)
        exact (hc1.prodMk continuous_const).continuousOn
      have hpath_mem : Set.MapsTo (fun τ : ℝ => (p.1 + τ * (p.2 - p.1), p.2)) (Set.uIcc (0:ℝ) 1)
          (Set.Icc a b ×ˢ Set.Icc a b) := by
        intro τ hτ
        have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
          simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
        have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
        have hfirst : p.1 + τ * (p.2 - p.1) ∈ Set.Icc a b := by
          have hmem := hconv.add_smul_sub_mem hp1_Icc hp2_Icc hτ'
          simpa [Algebra.smul_def, smul_eq_mul] using hmem
        exact ⟨hfirst, hp2_Icc⟩
      exact hK_cont.comp' hpath_cont hpath_mem
    have hK_ae : AEStronglyMeasurable (fun τ : ℝ => K (p.1 + τ * (p.2 - p.1)) p.2)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hK_slice.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) := hmeas_w.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun τ : ℝ => w τ • K (p.1 + τ * (p.2 - p.1)) p.2)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hK_ae
    simpa [F] using hprod

  have h_bound : ∀ᶠ p in 𝓝 (u0, σ0), ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ‖F p τ‖ ≤ C * w τ := by
    filter_upwards [hU_nhds] with p hp
    filter_upwards with τ hτ
    have hp' := hU_mem p hp
    have hp1_Icc : p.1 ∈ Set.Icc a b := ⟨le_of_lt hp'.1.1, le_of_lt hp'.1.2⟩
    have hp2_Icc : p.2 ∈ Set.Icc a b := ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ_rect : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ'.1, hτ'.2⟩
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : p.1 + τ * (p.2 - p.1) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hp1_Icc hp2_Icc hτ_rect
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hK_norm : ‖K (p.1 + τ * (p.2 - p.1)) p.2‖ ≤ C :=
      hC_bound (p.1 + τ * (p.2 - p.1), p.2) ⟨hfirst, hp2_Icc⟩
    calc
      ‖F p τ‖ = ‖w τ • K (p.1 + τ * (p.2 - p.1)) p.2‖ := by simp [F]
      _ = |w τ| * ‖K (p.1 + τ * (p.2 - p.1)) p.2‖ := norm_smul _ _
      _ = w τ * ‖K (p.1 + τ * (p.2 - p.1)) p.2‖ := by rw [abs_of_nonneg (hw_nonneg τ)]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hK_norm (hw_nonneg τ)
      _ = C * w τ := mul_comm _ _

  have h_cont : ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 →
      ContinuousAt (fun p : ℝ × ℝ => F p τ) (u0, σ0) := by
    filter_upwards with τ hτ
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hK_at : ContinuousAt (fun p : ℝ × ℝ => K (p.1 + τ * (p.2 - p.1)) p.2) (u0, σ0) := by
      have hpath : ContinuousAt (fun p : ℝ × ℝ => (p.1 + τ * (p.2 - p.1), p.2)) (u0, σ0) := by
        exact (continuous_fst.add (continuous_const.mul (continuous_snd.sub continuous_fst))).continuousAt.prodMk continuous_snd.continuousAt
      have hp_oo : (u0 + τ * (σ0 - u0), σ0) ∈ Set.Ioo a b ×ˢ Set.Ioo a b := by
        have hconv_oo : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
        have hfirst_oo : u0 + τ * (σ0 - u0) ∈ Set.Ioo a b := by
          have hmem := hconv_oo.add_smul_sub_mem hu0 hσ0 ⟨hτ0, hτ1⟩
          simpa [Algebra.smul_def, smul_eq_mul] using hmem
        exact ⟨hfirst_oo, hσ0⟩
      have h_open : IsOpen (Set.Ioo a b ×ˢ Set.Ioo a b) := (isOpen_Ioo.prod isOpen_Ioo)
      have h_nhds : Set.Ioo a b ×ˢ Set.Ioo a b ∈ 𝓝 (u0 + τ * (σ0 - u0), σ0) := h_open.mem_nhds hp_oo
      have h_sub : Set.Ioo a b ×ˢ Set.Ioo a b ⊆ Set.Icc a b ×ˢ Set.Icc a b := by
        intro q hq
        exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
      have hS_nhds : Set.Icc a b ×ˢ Set.Icc a b ∈ 𝓝 (u0 + τ * (σ0 - u0), σ0) := mem_of_superset h_nhds h_sub
      have hK_contAt : ContinuousAt (fun p : ℝ × ℝ => K p.1 p.2) (u0 + τ * (σ0 - u0), σ0) :=
        hK_cont.continuousAt hS_nhds
      have hcomp := ContinuousAt.comp' (f := fun p : ℝ × ℝ => (p.1 + τ * (p.2 - p.1), p.2))
        (g := fun q : ℝ × ℝ => K q.1 q.2) hK_contAt hpath
      simpa using hcomp
    exact hK_at.const_smul (w τ)

  have hdom := intervalIntegral.continuousAt_of_dominated_interval
    (F := F) (x₀ := (u0, σ0)) (bound := fun τ : ℝ => C * w τ) (a := (0:ℝ)) (b := (1:ℝ))
    hF_meas h_bound hbound_int h_cont
  simpa [F] using hdom




lemma norm_invSqrt_weighted_affine_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b v σ : ℝ} {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC_bound : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc a b, ‖K p.1 p.2‖ ≤ C)
    (hv : v ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) :
    ‖∫ τ in (0:ℝ)..(1:ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (v + τ * (σ - v)) σ‖
      ≤ C * (∫ τ in (0:ℝ)..(1:ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹) := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have hw_nonneg : ∀ τ, 0 ≤ w τ := by
    intro τ; unfold w; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hle : ‖∫ τ in (0:ℝ)..(1:ℝ), w τ • K (v + τ * (σ - v)) σ‖
      ≤ ∫ τ in (0:ℝ)..(1:ℝ), ‖w τ • K (v + τ * (σ - v)) σ‖ := by
    simpa using intervalIntegral.norm_integral_le_integral_norm (show (0:ℝ) ≤ 1 by norm_num)
  have hK_slice : ContinuousOn (fun τ : ℝ => K (v + τ * (σ - v)) σ) (Set.uIcc (0:ℝ) 1) := by
    have hpath_cont : ContinuousOn (fun τ : ℝ => (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1) := by
      have hc1 : Continuous (fun τ : ℝ => v + τ * (σ - v)) :=
        continuous_const.add (continuous_id.mul continuous_const)
      exact (hc1.prodMk continuous_const).continuousOn
    have hpath_mem : Set.MapsTo (fun τ : ℝ => (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1)
        (Set.Icc a b ×ˢ Set.Icc a b) := by
      intro τ hτ
      have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
      have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
      have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
        have hmem := hconv.add_smul_sub_mem hv hσ hτ'
        simpa [Algebra.smul_def, smul_eq_mul] using hmem
      exact ⟨hfirst, hσ⟩
    exact hK_cont.comp' hpath_cont hpath_mem
  have hvec_int : IntervalIntegrable (fun τ : ℝ => w τ • K (v + τ * (σ - v)) σ) volume (0:ℝ) 1 :=
    hw_int.smul_continuousOn hK_slice
  have hnorm_int : IntervalIntegrable (fun τ : ℝ => ‖w τ • K (v + τ * (σ - v)) σ‖) volume (0:ℝ) 1 := hvec_int.norm
  have hg_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
    simpa using hw_int.const_mul C
  have hmono : (∫ τ in (0:ℝ)..(1:ℝ), ‖w τ • K (v + τ * (σ - v)) σ‖)
      ≤ ∫ τ in (0:ℝ)..(1:ℝ), C * w τ := by
    apply intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) hnorm_int hg_int
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hv hσ hτ'
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hK_norm : ‖K (v + τ * (σ - v)) σ‖ ≤ C :=
      hC_bound (v + τ * (σ - v), σ) ⟨hfirst, hσ⟩
    calc
      ‖w τ • K (v + τ * (σ - v)) σ‖ = |w τ| * ‖K (v + τ * (σ - v)) σ‖ := norm_smul _ _
      _ = w τ * ‖K (v + τ * (σ - v)) σ‖ := by rw [abs_of_nonneg (hw_nonneg τ)]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hK_norm (hw_nonneg τ)
      _ = C * w τ := mul_comm _ _
  have hconst : (∫ τ in (0:ℝ)..(1:ℝ), C * w τ) = C * (∫ τ in (0:ℝ)..(1:ℝ), w τ) := by
    rw [intervalIntegral.integral_const_mul]
  exact hle.trans (hmono.trans_eq hconst)

lemma hasDerivAt_smul_sub_of_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {s : ℝ} (hf : ContinuousAt f s) :
    HasDerivAt (fun u : ℝ => (s - u) • f u) (-(f s)) s := by
  rw [hasDerivAt_iff_tendsto]
  have hnorm_eq : ∀ u : ℝ,
      |u - s|⁻¹ * ‖(s - u) • f u + (u - s) • f s‖ = ‖f u - f s‖ := by
    intro u
    have hcalc : (s - u) • f u + (u - s) • f s = (s - u) • (f u - f s) := by
      simp only [sub_eq_add_neg, smul_neg]
      module
    rw [hcalc, norm_smul]
    by_cases h : u = s
    · subst u; simp
    · have hne : u - s ≠ 0 := sub_ne_zero.mpr h
      have hnorm_su : ‖s - u‖ = |u - s| := by
        rw [Real.norm_eq_abs, abs_sub_comm]
      rw [hnorm_su]
      field_simp [sub_ne_zero.mpr h]
  have hlim : Tendsto (fun u : ℝ => ‖f u - f s‖) (𝓝 s) (𝓝 0) := by
    have h := hf.sub (continuousAt_const (x := s) (y := f s))
    simpa using (h.norm).tendsto
  simpa [hnorm_eq] using hlim



lemma continuousAt_invSqrt_weighted_affine_H
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b s : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hs : s ∈ Set.Ioo a b) :
    ContinuousAt (fun u : ℝ => ∫ t in (0:ℝ)..(1:ℝ),
      ∫ τ in (0:ℝ)..(1:ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * ((u + t * (s - u)) - u)) (u + t * (s - u))) s := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let I : ℝ := ∫ τ in (0:ℝ)..(1:ℝ), w τ
  let G : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ
  let F : ℝ → ℝ → E := fun u t => G u (u + t * (s - u))
  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have hS_compact : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hK_cont.norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc a b, ‖K p.1 p.2‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C * I) volume (0:ℝ) 1 := intervalIntegrable_const

  let δ : ℝ := min (s - a) (b - s) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))
  let U : Set ℝ := Metric.ball s δ
  have hU_nhds : U ∈ 𝓝 s := by
    dsimp [U]
    exact Metric.ball_mem_nhds s hδpos
  have hU_mem : ∀ u ∈ U, u ∈ Set.Ioo a b := by
    intro u hu
    have hdist : |u - s| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hu
    have hδ_lt_sa : δ < s - a := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_left _ _)
    have hδ_lt_bs : δ < b - s := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_right _ _)
    have h1 : |u - s| < s - a := lt_trans hdist hδ_lt_sa
    have h2 : |u - s| < b - s := lt_trans hdist hδ_lt_bs
    constructor
    · have h' : -(s - a) < u - s ∧ u - s < s - a := abs_lt.mp h1
      linarith
    · have h' : -(b - s) < u - s ∧ u - s < b - s := abs_lt.mp h2
      linarith
  have hU_mem_Icc : ∀ u ∈ U, u ∈ Set.Icc a b := by
    intro u hu
    exact ⟨le_of_lt (hU_mem u hu).1, le_of_lt (hU_mem u hu).2⟩
  have hs_Icc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩

  have hF_meas : ∀ᶠ u in 𝓝 s, AEStronglyMeasurable (F u) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hU_nhds] with u hu
    let c : ℝ := min u s
    let d : ℝ := max u s
    have hcd_sub : Set.Icc c d ⊆ Set.Icc a b := by
      intro σ hσ
      have hu_ab := hU_mem_Icc u hu
      have hs_ab : s ∈ Set.Icc a b := hs_Icc
      constructor
      · have hmin_le : c ≤ σ := hσ.1
        have hc_ge : a ≤ c := by
          dsimp [c]
          exact le_min hu_ab.1 hs_ab.1
        exact le_trans hc_ge hmin_le
      · have hσ_le : σ ≤ d := hσ.2
        have hd_le : d ≤ b := by
          dsimp [d]
          exact max_le hu_ab.2 hs_ab.2
        exact le_trans hσ_le hd_le
    have hG_cont : ContinuousOn (fun σ : ℝ => G u σ) (Set.Icc c d) := by
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun _ : ℝ => (1:ℝ)) (H := K) (a := a) (b := b)
        (v := u) (c := c) (d := d)
        hw_int (by unfold w; fun_prop) (by intro τ; unfold w; exact inv_nonneg.mpr (Real.sqrt_nonneg _))
        continuousOn_const (by intro τ hτ; simp) hK_cont (hU_mem_Icc u hu) hcd_sub
      simpa [G, one_smul] using h
    have hpath_cont : ContinuousOn (fun t : ℝ => u + t * (s - u)) (Set.uIcc (0:ℝ) 1) := by
      exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    have hpath_mem : Set.MapsTo (fun t : ℝ => u + t * (s - u)) (Set.uIcc (0:ℝ) 1) (Set.Icc c d) := by
      intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
      have hconv : Convex ℝ (Set.Icc c d) := convex_Icc c d
      have hu_cd : u ∈ Set.Icc c d := by
        dsimp [c, d]
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hs_cd : s ∈ Set.Icc c d := by
        dsimp [c, d]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      have hmem := hconv.add_smul_sub_mem hu_cd hs_cd ht'
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hF_cont_t : ContinuousOn (fun t : ℝ => G u (u + t * (s - u))) (Set.uIcc (0:ℝ) 1) :=
      hG_cont.comp' hpath_cont hpath_mem
    have hAE : AEStronglyMeasurable (fun t : ℝ => G u (u + t * (s - u))) (volume.restrict (Ι (0:ℝ) 1)) :=
      hF_cont_t.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    simpa [F] using hAE

  have h_bound : ∀ᶠ u in 𝓝 s, ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → ‖F u t‖ ≤ C * I := by
    filter_upwards [hU_nhds] with u hu
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
    have ht_rect : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht'.1, ht'.2⟩
    have hu_ab := hU_mem_Icc u hu
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hσ_ab : u + t * (s - u) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem hu_ab hs_Icc ht_rect
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hnorm := norm_invSqrt_weighted_affine_le (E := E) hK_cont hC_nonneg hC_bound hu_ab hσ_ab
    simpa [F, G, w, I] using hnorm

  have h_cont : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 →
      ContinuousAt (fun u : ℝ => F u t) s := by
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
    have hG_contAt : ContinuousAt (fun p : ℝ × ℝ => G p.1 p.2) (s, s) := by
      have h := continuousAt_invSqrt_weighted_affine (E := E) hab hK_cont hs hs
      simpa [G] using h
    have hpath_contAt : ContinuousAt (fun u : ℝ => (u, u + t * (s - u))) s := by
      have h1 : ContinuousAt (fun u : ℝ => u) s := continuousAt_id
      have h2 : ContinuousAt (fun u : ℝ => u + t * (s - u)) s := by
        exact continuousAt_id.add ((continuous_const.mul (continuous_const.sub continuous_id)).continuousAt)
      exact h1.prodMk h2
    have hG_contAt' : ContinuousAt (fun p : ℝ × ℝ => G p.1 p.2) (s, s + t * (s - s)) := by
      simpa using hG_contAt
    have hcomp := ContinuousAt.comp' (f := fun u : ℝ => (u, u + t * (s - u)))
      (g := fun p : ℝ × ℝ => G p.1 p.2) hG_contAt' hpath_contAt
    simpa [F] using hcomp

  have hdom := intervalIntegral.continuousAt_of_dominated_interval
    (F := F) (x₀ := s) (bound := fun _ : ℝ => C * I) (a := (0:ℝ)) (b := (1:ℝ))
    hF_meas h_bound hbound_int h_cont
  simpa [F, G, w] using hdom


lemma hasDerivAt_intervalIntegral_lower_invSqrt_weighted_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b s : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hs : s ∈ Set.Ioo a b) :
    HasDerivAt
      (fun u : ℝ => ∫ σ in u..s, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      (- (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s)) s := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let G : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ
  let H : ℝ → E := fun u => ∫ t in (0:ℝ)..(1:ℝ), G u (u + t * (s - u))
  have hK_contOn : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hK_cont.continuousOn
  have hH_cont : ContinuousAt H s := by
    have h := continuousAt_invSqrt_weighted_affine_H (E := E) hab hK_contOn hs
    simpa [H, G, w] using h
  have hprod := hasDerivAt_smul_sub_of_continuousAt (f := H) (s := s) hH_cont
  have hHs : H s = G s s := by
    dsimp [H, G]
    have h1 : (∫ t in (0:ℝ)..(1:ℝ),
        ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (s + τ * (s + t * (s - s) - s)) (s + t * (s - s)))
        = ∫ t in (0:ℝ)..(1:ℝ), (∫ τ in (0:ℝ)..(1:ℝ), w τ • K s s) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
      intro t ht
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
      intro τ hτ
      congr 2
      ring_nf
    rw [h1, intervalIntegral.integral_const]
    simp [G, one_smul]
  have hprod' := hprod.congr_deriv (by rw [hHs])
  have hfun : (fun u : ℝ => ∫ σ in u..s, G u σ) = fun u : ℝ => (s - u) • H u := by
    funext u
    have h1 := intervalIntegral.smul_integral_comp_mul_add (f := G u) (c := s - u) (d := u)
      (a := (0:ℝ)) (b := (1:ℝ))
    have h2 : (s - u) • H u = ∫ σ in u..s, G u σ := by
      dsimp [H]
      simpa [G, w, mul_comm, add_comm, add_assoc, sub_eq_add_neg] using h1
    exact h2.symm
  have hmain := hprod'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by exact congrFun hfun u))
  simpa [G, w] using hmain



lemma hasDerivAt_intervalIntegral_invSqrt_weighted_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b s : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hs : s ∈ Set.Ioo a b) :
    HasDerivAt
      (fun u : ℝ => ∫ σ in s..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      (∫ σ in s..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          ((1 - τ) • fderivWithin ℝ (fun p : ℝ × ℝ => K p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc a b) (s + τ * (σ - s), σ) (1, 0))) s := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  let K2 : ℝ × ℝ → E := fun p => K p.1 p.2
  let DK : ℝ × ℝ → E := fun p => fderivWithin ℝ K2 S p (1, 0)
  let F : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ
  let F' : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • ((1 - τ) • DK (u + τ * (σ - u), σ))

  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have hmeas_w : Measurable w := by
    unfold w
    fun_prop
  have hw_nonneg : ∀ τ, 0 ≤ w τ := by
    intro τ
    unfold w
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)

  have hK2_contOn : ContinuousOn K2 S := by
    simpa [K2, S] using hK_cont.continuousOn
  have hDK_contOn : ContinuousOn DK S := by
    simpa [DK, S] using continuousOn_fderivWithin_K_apply (E := E) hab hK_cont

  -- A small ball around s inside (a,b)
  let δ : ℝ := min (s - a) (b - s) / 2
  have hsa_pos : 0 < s - a := sub_pos.mpr hs.1
  have hbs_pos : 0 < b - s := sub_pos.mpr hs.2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos (lt_min hsa_pos hbs_pos)
  let U : Set ℝ := Metric.ball s δ
  have hU_nhds : U ∈ 𝓝 s := by
    dsimp [U]
    exact Metric.ball_mem_nhds s hδpos
  have hU_mem : ∀ v ∈ U, v ∈ Set.Ioo a b := by
    intro v hv
    have hdist : |v - s| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hv
    have hδ_lt_sa : δ < s - a := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min hsa_pos hbs_pos)) (min_le_left _ _)
    have hδ_lt_bs : δ < b - s := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min hsa_pos hbs_pos)) (min_le_right _ _)
    have h1 : |v - s| < s - a := lt_trans hdist hδ_lt_sa
    have h2 : |v - s| < b - s := lt_trans hdist hδ_lt_bs
    constructor
    · have h1' : -(s - a) < v - s ∧ v - s < s - a := abs_lt.mp h1
      linarith
    · have h2' : -(b - s) < v - s ∧ v - s < b - s := abs_lt.mp h2
      linarith
  have hU_mem_Icc : ∀ v ∈ U, v ∈ Set.Icc a b := by
    intro v hv
    exact ⟨le_of_lt (hU_mem v hv).1, le_of_lt (hU_mem v hv).2⟩
  have hs_Icc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hb_Icc : b ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hs.1 hs.2), le_rfl⟩
  have hcd_sub : Set.Icc s b ⊆ Set.Icc a b := by
    intro σ hσ
    exact ⟨le_trans (le_of_lt hs.1) hσ.1, hσ.2⟩
  have hsub_meas : Ι s b ⊆ Set.Icc s b := by
    simpa [Set.uIcc_of_le (le_of_lt hs.2)] using (Set.uIoc_subset_uIcc : Ι s b ⊆ Set.uIcc s b)

  -- continuity for measurability of F and F'
  have hρ1_cont : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.uIcc (0:ℝ) 1) := continuousOn_const
  have hρ1_bound : ∀ τ ∈ Set.uIcc (0:ℝ) 1, |(1:ℝ)| ≤ 1 := by intro τ hτ; simp
  have hρ_sub_cont : ContinuousOn (fun τ : ℝ => 1 - τ) (Set.uIcc (0:ℝ) 1) := by
    exact (continuousOn_const.sub continuousOn_id : ContinuousOn (fun τ : ℝ => (1:ℝ) - τ) (Set.uIcc (0:ℝ) 1))
  have hρ_sub_bound : ∀ τ ∈ Set.uIcc (0:ℝ) 1, |1 - τ| ≤ 1 := by
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    rw [abs_of_nonneg (sub_nonneg.mpr hτ'.2)]
    nlinarith [hτ'.1, hτ'.2]

  have hF_meas : ∀ᶠ v in 𝓝 s, AEStronglyMeasurable (F v) (volume.restrict (Ι s b)) := by
    filter_upwards [hU_nhds] with v hv
    have hcont : ContinuousOn (fun σ : ℝ => F v σ) (Set.Icc s b) := by
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun _ : ℝ => (1:ℝ)) (H := K) (a := a) (b := b)
        (v := v) (c := s) (d := b)
        hw_int hmeas_w hw_nonneg hρ1_cont hρ1_bound hK2_contOn (hU_mem_Icc v hv) hcd_sub
      simpa [F, one_smul] using h
    have hAE : AEStronglyMeasurable (fun σ : ℝ => F v σ) (volume.restrict (Ι s b)) :=
      hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_uIoc
        hsub_meas
    simpa using hAE

  have hF_int : IntervalIntegrable (F s) volume s b := by
    have hcont : ContinuousOn (fun σ : ℝ => F s σ) (Set.Icc s b) := by
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun _ : ℝ => (1:ℝ)) (H := K) (a := a) (b := b)
        (v := s) (c := s) (d := b)
        hw_int hmeas_w hw_nonneg hρ1_cont hρ1_bound hK2_contOn hs_Icc hcd_sub
      simpa [F, one_smul] using h
    have hcont_u : ContinuousOn (fun σ : ℝ => F s σ) (Set.uIcc s b) := by
      simpa [Set.uIcc_of_le (le_of_lt hs.2)] using hcont
    exact hcont_u.intervalIntegrable

  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι s b)) := by
    have hcont : ContinuousOn (fun σ : ℝ => F' s σ) (Set.Icc s b) := by
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun τ : ℝ => 1 - τ)
        (H := fun x y : ℝ => DK (x, y)) (a := a) (b := b)
        (v := s) (c := s) (d := b)
        hw_int hmeas_w hw_nonneg hρ_sub_cont hρ_sub_bound
        (by simpa [S, Set.Icc_prod_Icc] using hDK_contOn) hs_Icc hcd_sub
      simpa [F', DK] using h
    exact hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_uIoc
      hsub_meas

  -- bound on DK over S
  have hS_compact : IsCompact S := by dsimp [S]; exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hDK_contOn.norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ p ∈ S, ‖DK p‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  let I : ℝ := ∫ τ in (0:ℝ)..(1:ℝ), w τ
  have hbound_int_outer : IntervalIntegrable (fun _ : ℝ => C * I) volume s b := by
    exact intervalIntegrable_const

  have h_inner_norm_bound : ∀ v ∈ U, ∀ σ ∈ Set.Icc s b, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))‖ ≤ C * w τ := by
    intro v hv σ hσ τ hτ
    have hv_oo := hU_mem v hv
    have hτ0 : 0 ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hσ_ab : σ ∈ Set.Icc a b := hcd_sub hσ
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hfirst : v + τ * (σ - v) ∈ Set.Icc a b := by
      have hmem := hconv.add_smul_sub_mem (hU_mem_Icc v hv) hσ_ab hτ
      simpa [Algebra.smul_def, smul_eq_mul] using hmem
    have hpt : (v + τ * (σ - v), σ) ∈ S := by dsimp [S]; exact ⟨hfirst, hσ_ab⟩
    have hDnorm : ‖(1 - τ) • DK (v + τ * (σ - v), σ)‖ ≤ C := by
      have hDK_norm : ‖DK (v + τ * (σ - v), σ)‖ ≤ C := hC_bound _ hpt
      have h_abs : |1 - τ| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hτ1)]
        linarith
      calc
        ‖(1 - τ) • DK (v + τ * (σ - v), σ)‖ = |1 - τ| * ‖DK (v + τ * (σ - v), σ)‖ := norm_smul _ _
        _ ≤ 1 * C := mul_le_mul h_abs hDK_norm (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    calc
      ‖w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))‖
          = |w τ| * ‖(1 - τ) • DK (v + τ * (σ - v), σ)‖ := norm_smul _ _
      _ = w τ * ‖(1 - τ) • DK (v + τ * (σ - v), σ)‖ := by rw [abs_of_nonneg (hw_nonneg τ)]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hDnorm (hw_nonneg τ)
      _ = C * w τ := mul_comm _ _

  have h_bound : ∀ᵐ σ ∂volume, σ ∈ Ι s b → ∀ v ∈ U, ‖F' v σ‖ ≤ C * I := by
    filter_upwards with σ hσ
    intro v hv
    have hσ' : σ ∈ Set.Ioc s b := by
      simpa [Set.uIoc_of_le (le_of_lt hs.2)] using hσ
    have hσ_cc : σ ∈ Set.Icc s b := ⟨le_of_lt hσ'.1, hσ'.2⟩
    have hle : ‖F' v σ‖ ≤ ∫ τ in (0:ℝ)..(1:ℝ), ‖w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))‖ := by
      simpa [F'] using intervalIntegral.norm_integral_le_integral_norm (show (0:ℝ) ≤ 1 by norm_num)
    have hvec_int : IntervalIntegrable (fun τ : ℝ => w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))) volume (0:ℝ) 1 := by
      have hD_cont : ContinuousOn (fun τ : ℝ => (1 - τ) • DK (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1) := by
        have hDK_slice : ContinuousOn (fun τ : ℝ => DK (v + τ * (σ - v), σ)) (Set.uIcc (0:ℝ) 1) := by
          have hDK_curry : ContinuousOn (fun p : ℝ × ℝ => DK (p.1, p.2)) (Set.Icc a b ×ˢ Set.Icc a b) := by
            change ContinuousOn DK (Set.Icc a b ×ˢ Set.Icc a b)
            simpa [S, Set.Icc_prod_Icc] using hDK_contOn
          have h := continuousOn_K_affine_slice_fixed_first (E := E) (K := fun x y : ℝ => DK (x, y))
            hDK_curry (hU_mem_Icc v hv) (hcd_sub hσ_cc)
          simpa [DK] using h
        exact hρ_sub_cont.smul hDK_slice
      exact hw_int.smul_continuousOn hD_cont
    have hnorm_int : IntervalIntegrable (fun τ : ℝ => ‖w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))‖) volume (0:ℝ) 1 := hvec_int.norm
    have hg_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
      simpa using hw_int.const_mul C
    have hmono : (∫ τ in (0:ℝ)..(1:ℝ), ‖w τ • ((1 - τ) • DK (v + τ * (σ - v), σ))‖)
        ≤ ∫ τ in (0:ℝ)..(1:ℝ), C * w τ := by
      apply intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) hnorm_int hg_int
      intro τ hτ
      have hτ_cc : τ ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
      exact h_inner_norm_bound v hv σ hσ_cc τ hτ_cc
    have hconst : (∫ τ in (0:ℝ)..(1:ℝ), C * w τ) = C * I := by
      rw [intervalIntegral.integral_const_mul]
    exact hle.trans (hmono.trans_eq hconst)

  have hσ_ne_b : ∀ᵐ σ ∂volume, σ ≠ b := by
    rw [ae_iff]
    simp [measure_singleton]
  have h_diff : ∀ᵐ σ ∂volume, σ ∈ Ι s b → ∀ v ∈ U,
      HasDerivAt (fun u : ℝ => F u σ) (F' v σ) v := by
    filter_upwards [hσ_ne_b] with σ hσb
    intro hσ v hv
    have hσ' : σ ∈ Set.Ioc s b := by
      simpa [Set.uIoc_of_le (le_of_lt hs.2)] using hσ
    have hσ_ioo : σ ∈ Set.Ioo s b := ⟨hσ'.1, lt_of_le_of_ne hσ'.2 hσb⟩
    have hσ_ab : σ ∈ Set.Ioo a b := ⟨lt_trans hs.1 hσ_ioo.1, hσ_ioo.2⟩
    have hv_oo := hU_mem v hv
    have hder := hasDerivAt_invSqrt_weighted_affine_of_mem_Ioo (E := E) hab hK_cont hv_oo hσ_ab
    have hder_eq : (∫ τ in (0:ℝ)..(1:ℝ),
        w τ • ((1 - τ) • fderiv ℝ K2 (v + τ * (σ - v), σ) (1, 0)))
        = F' v σ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
      intro τ hτ
      have hτ0 : 0 < τ := hτ.1
      have hτ1 : τ < 1 := hτ.2
      have h1τ_pos : 0 < 1 - τ := by linarith
      have hp_mem : (v + τ * (σ - v), σ) ∈ Set.Ioo a b ×ˢ Set.Ioo a b := by
        constructor
        · rw [Set.mem_Ioo]
          constructor
          · have hva : a < v := hv_oo.1
            have hσa : a < σ := hσ_ab.1
            have h1 : a = (1 - τ) * a + τ * a := by ring
            rw [h1]
            have hmul1 : (1 - τ) * a < (1 - τ) * v := mul_lt_mul_of_pos_left hva h1τ_pos
            have hmul2 : τ * a < τ * σ := mul_lt_mul_of_pos_left hσa hτ0
            nlinarith
          · have hvb : v < b := hv_oo.2
            have hσb : σ < b := hσ_ab.2
            have h1 : b = (1 - τ) * b + τ * b := by ring
            rw [h1]
            have hmul1 : (1 - τ) * v < (1 - τ) * b := mul_lt_mul_of_pos_left hvb h1τ_pos
            have hmul2 : τ * σ < τ * b := mul_lt_mul_of_pos_left hσb hτ0
            nlinarith
        · exact hσ_ab
      have h_open : IsOpen (Set.Ioo a b ×ˢ Set.Ioo a b) := (isOpen_Ioo.prod isOpen_Ioo)
      have h_nhds : Set.Ioo a b ×ˢ Set.Ioo a b ∈ 𝓝 (v + τ * (σ - v), σ) := h_open.mem_nhds hp_mem
      have h_sub : Set.Ioo a b ×ˢ Set.Ioo a b ⊆ S := by
        intro q hq
        exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
      have hS_nhds : S ∈ 𝓝 (v + τ * (σ - v), σ) := mem_of_superset h_nhds h_sub
      have hfd : fderivWithin ℝ K2 S (v + τ * (σ - v), σ) (1, 0)
          = fderiv ℝ K2 (v + τ * (σ - v), σ) (1, 0) := by
        rw [fderivWithin_of_mem_nhds hS_nhds]
      simp [F', DK, hfd]
    have hder' := hder.congr_deriv hder_eq
    simpa [F] using hder'

  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := E) (a := s) (b := b)
    (F := F) (F' := F') (x₀ := s) (s := U) (bound := fun _ : ℝ => C * I)
    hU_nhds hF_meas hF_int hF'_meas h_bound hbound_int_outer h_diff
  have hmain := hdom.2
  simpa [F, F', DK, S] using hmain




lemma volterra_integral_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    ∀ s ∈ Set.Ioo a b,
      HasDerivAt
        (fun u : ℝ => ∫ σ in u..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
          (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
        (- (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s) +
          (∫ σ in s..b, deriv (fun u : ℝ =>
            ∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s))
        s := by
  intro s hs
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  let K2 : ℝ × ℝ → E := fun p => K p.1 p.2
  let DK : ℝ × ℝ → E := fun p => fderivWithin ℝ K2 S p (1, 0)
  let G : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ
  let G' : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • ((1 - τ) • DK (u + τ * (σ - u), σ))
  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have houter := hasDerivAt_intervalIntegral_invSqrt_weighted_affine (E := E) hab hK_cont hs
  have hlower := hasDerivAt_intervalIntegral_lower_invSqrt_weighted_affine (E := E) hab hK_cont hs
  have houterG : HasDerivAt (fun u : ℝ => ∫ σ in s..b, G u σ) (∫ σ in s..b, G' s σ) s := by
    simpa [G, G', w, DK, S] using houter
  have hlowerG : HasDerivAt (fun u : ℝ => ∫ σ in u..s, G u σ)
      (- (∫ τ in (0:ℝ)..(1:ℝ), w τ • K s s)) s := by
    simpa [G, w] using hlower
  have hderiv_inner_eq : ∀ σ ∈ Set.Ioo s b, deriv (fun u : ℝ => G u σ) s = G' s σ := by
    intro σ hσ
    have hσ_ab : σ ∈ Set.Ioo a b := ⟨lt_trans hs.1 hσ.1, hσ.2⟩
    have hder := hasDerivAt_invSqrt_weighted_affine_of_mem_Ioo (E := E) hab hK_cont hs hσ_ab
    have hder_eq : (∫ τ in (0:ℝ)..(1:ℝ),
        w τ • ((1 - τ) • fderiv ℝ K2 (s + τ * (σ - s), σ) (1, 0))) = G' s σ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
      intro τ hτ
      have hτ0 : 0 < τ := hτ.1
      have hτ1 : τ < 1 := hτ.2
      have h1τ_pos : 0 < 1 - τ := by linarith
      have hp_mem : (s + τ * (σ - s), σ) ∈ Set.Ioo a b ×ˢ Set.Ioo a b := by
        constructor
        · rw [Set.mem_Ioo]
          constructor
          · have hsa : a < s := hs.1
            have hσa : a < σ := hσ_ab.1
            have h1 : a = (1 - τ) * a + τ * a := by ring
            rw [h1]
            have hmul1 : (1 - τ) * a < (1 - τ) * s := mul_lt_mul_of_pos_left hsa h1τ_pos
            have hmul2 : τ * a < τ * σ := mul_lt_mul_of_pos_left hσa hτ0
            nlinarith
          · have hsb : s < b := hs.2
            have hσb : σ < b := hσ_ab.2
            have h1 : b = (1 - τ) * b + τ * b := by ring
            rw [h1]
            have hmul1 : (1 - τ) * s < (1 - τ) * b := mul_lt_mul_of_pos_left hsb h1τ_pos
            have hmul2 : τ * σ < τ * b := mul_lt_mul_of_pos_left hσb hτ0
            nlinarith
        · exact hσ_ab
      have h_open : IsOpen (Set.Ioo a b ×ˢ Set.Ioo a b) := (isOpen_Ioo.prod isOpen_Ioo)
      have h_nhds : Set.Ioo a b ×ˢ Set.Ioo a b ∈ 𝓝 (s + τ * (σ - s), σ) := h_open.mem_nhds hp_mem
      have h_sub : Set.Ioo a b ×ˢ Set.Ioo a b ⊆ S := by
        intro q hq
        exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
      have hS_nhds : S ∈ 𝓝 (s + τ * (σ - s), σ) := mem_of_superset h_nhds h_sub
      have hfd : fderivWithin ℝ K2 S (s + τ * (σ - s), σ) (1, 0)
          = fderiv ℝ K2 (s + τ * (σ - s), σ) (1, 0) := by
        rw [fderivWithin_of_mem_nhds hS_nhds]
      simp [G', DK, hfd]
    rw [hder.deriv]
    exact hder_eq
  have houter_eq : (∫ σ in s..b, G' s σ) = ∫ σ in s..b, deriv (fun u : ℝ => G u σ) s := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)]
    intro σ hσ
    exact (hderiv_inner_eq σ hσ).symm
  have houter_deriv : HasDerivAt (fun u : ℝ => ∫ σ in s..b, G u σ)
      (∫ σ in s..b, deriv (fun u : ℝ => G u σ) s) s :=
    houterG.congr_deriv houter_eq

  let δ : ℝ := min (s - a) (b - s) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))
  let U : Set ℝ := Metric.ball s δ
  have hU_nhds : U ∈ 𝓝 s := by
    dsimp [U]
    exact Metric.ball_mem_nhds s hδpos
  have hU_mem : ∀ u ∈ U, u ∈ Set.Ioo a b := by
    intro u hu
    have hdist : |u - s| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hu
    have hδ_lt_sa : δ < s - a := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_left _ _)
    have hδ_lt_bs : δ < b - s := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_right _ _)
    have h1 : |u - s| < s - a := lt_trans hdist hδ_lt_sa
    have h2 : |u - s| < b - s := lt_trans hdist hδ_lt_bs
    constructor
    · have h' : -(s - a) < u - s ∧ u - s < s - a := abs_lt.mp h1
      linarith
    · have h' : -(b - s) < u - s ∧ u - s < b - s := abs_lt.mp h2
      linarith
  have hU_mem_Icc : ∀ u ∈ U, u ∈ Set.Icc a b := by
    intro u hu
    exact ⟨le_of_lt (hU_mem u hu).1, le_of_lt (hU_mem u hu).2⟩
  have hs_Icc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hcd_sb : Set.Icc s b ⊆ Set.Icc a b := by
    intro σ hσ
    exact ⟨le_trans (le_of_lt hs.1) hσ.1, hσ.2⟩
  have hdecomp_event : (fun u : ℝ => ∫ σ in u..b, G u σ) =ᶠ[𝓝 s]
      (fun u : ℝ => (∫ σ in u..s, G u σ) + ∫ σ in s..b, G u σ) := by
    filter_upwards [hU_nhds] with u hu
    have hu_Icc := hU_mem_Icc u hu
    have hG_cont_cd : ∀ c d : ℝ, Set.Icc c d ⊆ Set.Icc a b → ContinuousOn (fun σ : ℝ => G u σ) (Set.Icc c d) := by
      intro c d hcd_sub
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun _ : ℝ => (1:ℝ)) (H := K) (a := a) (b := b)
        (v := u) (c := c) (d := d)
        hw_int (by unfold w; fun_prop) (by intro τ; unfold w; exact inv_nonneg.mpr (Real.sqrt_nonneg _))
        continuousOn_const (by intro τ hτ; simp) hK_cont.continuousOn hu_Icc hcd_sub
      simpa [G, one_smul] using h
    have hG_cont_sb : ContinuousOn (fun σ : ℝ => G u σ) (Set.Icc s b) := hG_cont_cd s b hcd_sb
    have hint_sb : IntervalIntegrable (fun σ : ℝ => G u σ) volume s b := by
      have hcont_u : ContinuousOn (fun σ : ℝ => G u σ) (Set.uIcc s b) := by
        simpa [Set.uIcc_of_le (le_of_lt hs.2)] using hG_cont_sb
      exact hcont_u.intervalIntegrable
    have hint_us : IntervalIntegrable (fun σ : ℝ => G u σ) volume u s := by
      by_cases hle : u ≤ s
      · have hcd_sub : Set.Icc u s ⊆ Set.Icc a b := by
          intro σ hσ
          exact ⟨le_trans (le_of_lt (hU_mem u hu).1) hσ.1, le_trans hσ.2 (le_of_lt hs.2)⟩
        have hG_cont : ContinuousOn (fun σ : ℝ => G u σ) (Set.Icc u s) := hG_cont_cd u s hcd_sub
        have hcont_u : ContinuousOn (fun σ : ℝ => G u σ) (Set.uIcc u s) := by
          simpa [Set.uIcc_of_le hle] using hG_cont
        exact hcont_u.intervalIntegrable
      · have hle2 : s ≤ u := le_of_not_ge hle
        have hcd_sub : Set.Icc s u ⊆ Set.Icc a b := by
          intro σ hσ
          exact ⟨le_trans (le_of_lt hs.1) hσ.1, le_trans hσ.2 (le_of_lt (hU_mem u hu).2)⟩
        have hG_cont : ContinuousOn (fun σ : ℝ => G u σ) (Set.Icc s u) := hG_cont_cd s u hcd_sub
        have hcont_u : ContinuousOn (fun σ : ℝ => G u σ) (Set.uIcc u s) := by
          rw [Set.uIcc_comm]
          simpa [Set.uIcc_of_le hle2] using hG_cont
        exact hcont_u.intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume) hint_us hint_sb).symm

  have hsum_deriv := hlowerG.add houter_deriv
  have hsum_fun := hsum_deriv.congr_of_eventuallyEq hdecomp_event
  have hderiv_val : (- (∫ τ in (0:ℝ)..(1:ℝ), w τ • K s s) +
        ∫ σ in s..b, deriv (fun u : ℝ => G u σ) s)
      = (- (∫ τ in (0:ℝ)..(1:ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s) +
        ∫ σ in s..b, deriv (fun u : ℝ =>
          ∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s) := by
    simp [w, G]
  have hfinal := hsum_fun.congr_deriv hderiv_val
  simpa [G, w] using hfinal


end Commons.Analysis.Abel