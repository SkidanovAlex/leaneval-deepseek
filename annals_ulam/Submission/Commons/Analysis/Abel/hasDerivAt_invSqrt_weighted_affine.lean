import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt

set_option linter.unusedVariables false

namespace Commons.Analysis.Abel

open Filter Topology MeasureTheory
open scoped Topology Interval

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The singular weight `1 / sqrt (τ * (1 - τ))` is interval-integrable on `(0,1)`. -/
lemma intervalIntegrable_invSqrt_weight :
    IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0:ℝ) 1 := by
  let g : ℝ → ℝ := fun x => (Real.sqrt (1 - x ^ 2))⁻¹
  have hbase : IntervalIntegrable g volume (-1:ℝ) 1 := by
    simpa [g] using Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hmul : IntervalIntegrable (fun x : ℝ => g (2 * x)) volume ((-1:ℝ)/2) (1/2) := by
    simpa using hbase.comp_mul_left (c := 2)
  have hadd : IntervalIntegrable (fun τ : ℝ => g (2 * (τ + (-1/2:ℝ)))) volume (0:ℝ) 1 := by
    have h := hmul.comp_add_right (-1/2:ℝ)
    simpa [show (2:ℝ)⁻¹ - -1/2 = 1 by norm_num] using h
  have hmain : IntervalIntegrable (fun τ : ℝ => g (2 * τ - 1)) volume (0:ℝ) 1 := by
    have hfun : (fun τ : ℝ => g (2 * (τ + (-1/2:ℝ)))) = fun τ : ℝ => g (2 * τ - 1) := by
      funext τ; ring_nf
    simpa [hfun] using hadd
  have hmain_const : IntervalIntegrable (fun τ : ℝ => 2 * g (2 * τ - 1)) volume (0:ℝ) 1 :=
    hmain.const_mul 2
  have hEq : Set.EqOn (fun τ : ℝ => 2 * g (2 * τ - 1))
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) (Set.uIoc (0:ℝ) 1) := by
    intro τ hτ
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ_nonneg : 0 ≤ τ := le_of_lt hτ'.1
    have hτ_le1 : τ ≤ 1 := hτ'.2
    have hnonneg : 0 ≤ τ * (1 - τ) := mul_nonneg hτ_nonneg (sub_nonneg.mpr hτ_le1)
    have h1 : 1 - (2 * τ - 1) ^ 2 = 4 * (τ * (1 - τ)) := by ring
    have hsqrt_eq : Real.sqrt (1 - (2 * τ - 1) ^ 2) = 2 * Real.sqrt (τ * (1 - τ)) := by
      rw [h1, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (τ * (1 - τ)),
        Real.sqrt_mul hτ_nonneg (1 - τ)]
      norm_num
    simp only [g]
    by_cases hτeq : τ = 1
    · subst τ; norm_num
    · have hτ_ne_one : τ ≠ 1 := hτeq
      have hτ_lt_one : τ < 1 := lt_of_le_of_ne hτ_le1 hτ_ne_one
      have hpos : 0 < τ * (1 - τ) := mul_pos hτ'.1 (sub_pos.mpr hτ_lt_one)
      have hsqrt_pos : 0 < Real.sqrt (τ * (1 - τ)) := Real.sqrt_pos_of_pos hpos
      rw [hsqrt_eq]
      field_simp [hsqrt_pos.ne']
  exact hmain_const.congr hEq

/-- The slice `τ ↦ K (x + τ * (σ - x), σ)` is continuous on `[0,1]` when the affine image
lies in the rectangle where `K` is known to be smooth. -/
lemma continuousOn_K_affine_slice
    {a b x σ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo x b) :
    ContinuousOn (fun τ : ℝ => K (x + τ * (σ - x)) σ) (Set.uIcc (0:ℝ) 1) := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  have hG_cont : ContinuousOn G (Set.Icc a b ×ˢ Set.Icc a b) :=
    hK_cont.continuousOn
  have hpath_cont : ContinuousOn (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) := by
    have hc1 : Continuous (fun τ : ℝ => x + τ * (σ - x)) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (hc1.prodMk continuous_const).continuousOn
  have hpath_mem : Set.MapsTo (fun τ : ℝ => (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1)
      (Set.Icc a b ×ˢ Set.Icc a b) := by
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hx_le_p : x ≤ x + τ * (σ - x) := by
      have hnonneg : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    have hp_le_σ : x + τ * (σ - x) ≤ σ := by
      have hle : τ * (σ - x) ≤ 1 * (σ - x) :=
        mul_le_mul_of_nonneg_right hτ1 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    constructor
    · constructor
      · exact le_trans (le_of_lt hx.1) hx_le_p
      · exact le_trans hp_le_σ (le_of_lt hσ.2)
    · constructor
      · exact le_of_lt (lt_trans hx.1 hσ.1)
      · exact le_of_lt hσ.2
  have hcomp : ContinuousOn (fun τ : ℝ => G (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) :=
    hG_cont.comp' hpath_cont hpath_mem
  simpa [G] using hcomp

/-- The first partial derivative of `K` along the same affine slice is continuous on `[0,1]`. -/
lemma continuousOn_fderiv_K_affine_slice
    {a b x σ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo x b) :
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
    have hτ0 : 0 ≤ τ := hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hx_le_p : x ≤ x + τ * (σ - x) := by
      have hnonneg : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    have hp_le_σ : x + τ * (σ - x) ≤ σ := by
      have hle : τ * (σ - x) ≤ 1 * (σ - x) :=
        mul_le_mul_of_nonneg_right hτ1 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    constructor
    · constructor
      · exact lt_of_lt_of_le hx.1 hx_le_p
      · exact lt_of_le_of_lt hp_le_σ hσ.2
    · constructor
      · exact lt_trans hx.1 hσ.1
      · exact hσ.2
  have hfd : ContinuousOn (fun τ : ℝ => fderiv ℝ G (x + τ * (σ - x), σ)) (Set.uIcc (0:ℝ) 1) :=
    hfd_contO.comp' hpath_cont hpath_mem
  have happly : ContinuousOn (fun τ : ℝ => (fderiv ℝ G (x + τ * (σ - x), σ)) (1, 0))
      (Set.uIcc (0:ℝ) 1) :=
    hfd.clm_apply continuousOn_const
  simpa [G] using happly

/-- Derivative of the affine slice of `K` in the first parameter. -/
lemma hasDerivAt_K_affine_slice
    {a b x σ τ : ℝ}
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo x b) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    HasDerivAt (fun v : ℝ => K (v + τ * (σ - v)) σ)
      ((1 - τ) • fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2)
        (x + τ * (σ - x), σ) (1, 0)) x := by
  let G : ℝ × ℝ → E := fun p => K p.1 p.2
  let p : ℝ × ℝ := (x + τ * (σ - x), σ)
  have hdiffOn : DifferentiableOn ℝ G (Set.Icc a b ×ˢ Set.Icc a b) :=
    hK_cont.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hp_orect : p ∈ Set.Ioo a b ×ˢ Set.Ioo a b := by
    have hx_le_p : x ≤ x + τ * (σ - x) := by
      have hnonneg : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    have hp_le_σ : x + τ * (σ - x) ≤ σ := by
      have hle : τ * (σ - x) ≤ 1 * (σ - x) :=
        mul_le_mul_of_nonneg_right hτ1 (sub_nonneg.mpr (le_of_lt hσ.1))
      linarith
    constructor
    · constructor
      · exact lt_of_lt_of_le hx.1 hx_le_p
      · exact lt_of_le_of_lt hp_le_σ hσ.2
    · constructor
      · exact lt_trans hx.1 hσ.1
      · exact hσ.2
  have hrect_nhds : (Set.Icc a b ×ˢ Set.Icc a b) ∈ 𝓝 p := by
    apply Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp_orect)
    intro q hq
    exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
  have hdiffG : DifferentiableAt ℝ G p := hdiffOn.differentiableAt hrect_nhds
  have hderiv_affine : HasDerivAt (fun v : ℝ => (v + τ * (σ - v), σ)) ((1 - τ), 0) x := by
    have hfirst : HasDerivAt (fun v : ℝ => v + τ * (σ - v)) (1 - τ) x := by
      have h := ((hasDerivAt_id x).const_mul (1 - τ)).add (hasDerivAt_const x (τ * σ))
      have hfun : (fun v : ℝ => (1 - τ) * v + τ * σ) =ᶠ[𝓝 x]
          ((fun y => (1 - τ) * y) + fun x => τ * σ) := by
        apply Filter.Eventually.of_forall
        intro v
        rfl
      have h' := h.congr_of_eventuallyEq hfun
      have hderiv : ((1 - τ) * 1 + 0) = 1 - τ := by ring
      have h'' := h'.congr_deriv hderiv
      have hfun2 : (fun v : ℝ => v + τ * (σ - v)) = fun v : ℝ => (1 - τ) * v + τ * σ := by
        funext v; ring
      rw [hfun2]
      exact h''
    exact hfirst.prodMk (hasDerivAt_const x σ)
  have hcomp := hdiffG.hasFDerivAt.comp_hasDerivAt x hderiv_affine
  have hval : fderiv ℝ G p ((1 - τ), 0) = (1 - τ) • fderiv ℝ G p (1, 0) := by
    have hvec : ((1 - τ), 0) = (1 - τ) • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp [smul_eq_mul]
    rw [hvec, map_smul]
  have hcomp' : HasDerivAt ((fun p : ℝ × ℝ => K p.1 p.2) ∘ (fun v : ℝ => (v + τ * (σ - v), σ)))
      ((1 - τ) • fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2) (x + τ * (σ - x), σ) (1, 0)) x := by
    simpa [G, p, hval] using hcomp
  refine hcomp'.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro v
  rfl

end Helpers

lemma hasDerivAt_invSqrt_weighted_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b s σ : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hs : s ∈ Set.Ioo a b) (hσ : σ ∈ Set.Ioo s b) :
    HasDerivAt
      (fun u : ℝ => ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      (∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          ((1 - τ) • fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2)
            (s + τ * (σ - s), σ) (1, 0))) s := by
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

  -- A neighbourhood of `s` on which all affine slices stay strictly inside `(a,b)`.
  let δ : ℝ := min (s - a) (σ - s) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hσ.1))
  let U : Set ℝ := Metric.ball s δ
  have hU_nhds : U ∈ 𝓝 s := by
    dsimp [U]
    exact Metric.ball_mem_nhds s hδpos
  have hU_mem : ∀ x ∈ U, x ∈ Set.Ioo a b ∧ σ ∈ Set.Ioo x b := by
    intro x hx
    have hdist : |x - s| < δ := by
      simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hx
    have hsa : 0 < s - a := sub_pos.mpr hs.1
    have hσs : 0 < σ - s := sub_pos.mpr hσ.1
    have hδ_lt_sa : δ < s - a := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min hsa hσs)) (min_le_left _ _)
    have hδ_lt_σs : δ < σ - s := by
      dsimp [δ]
      exact lt_of_lt_of_le (half_lt_self (lt_min hsa hσs)) (min_le_right _ _)
    have h1 : |x - s| < s - a := lt_trans hdist hδ_lt_sa
    have h2 : |x - s| < σ - s := lt_trans hdist hδ_lt_σs
    have hax : a < x := by
      have h1' : -(s - a) < x - s ∧ x - s < s - a := abs_lt.mp h1
      linarith
    have hxσ : x < σ := by
      have h2' : -(σ - s) < x - s ∧ x - s < σ - s := abs_lt.mp h2
      linarith
    have hxb : x < b := lt_trans hxσ hσ.2
    exact ⟨⟨hax, hxb⟩, ⟨hxσ, hσ.2⟩⟩

  -- Measurability hypotheses.
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (F x) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hU_nhds] with x hx
    have hx' := hU_mem x hx
    have hg_cont : ContinuousOn (fun τ : ℝ => K (x + τ * (σ - x)) σ) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_K_affine_slice (E := E) hK_cont hx'.1 hx'.2
    have hg_ae : AEStronglyMeasurable (fun τ : ℝ => K (x + τ * (σ - x)) σ)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hg_cont.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) :=
      hmeas_weight.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun τ : ℝ => w τ • K (x + τ * (σ - x)) σ)
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hg_ae
    simpa [F] using hprod

  have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
    have hg_cont : ContinuousOn (fun τ : ℝ => K (s + τ * (σ - s)) σ) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_K_affine_slice (E := E) hK_cont hs hσ
    have h := hw_int.smul_continuousOn hg_cont
    simpa [F] using h

  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι (0:ℝ) 1)) := by
    have hfd_cont0 : ContinuousOn
        (fun τ : ℝ => fderiv ℝ G (s + τ * (σ - s), σ) (1, 0)) (Set.uIcc (0:ℝ) 1) := by
      simpa [G] using continuousOn_fderiv_K_affine_slice (E := E) hK_cont hs hσ
    have hD_cont : ContinuousOn
        (fun τ : ℝ => (1 - τ) • fderiv ℝ G (s + τ * (σ - s), σ) (1, 0)) (Set.uIcc (0:ℝ) 1) := by
      have hscalar : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.uIcc (0:ℝ) 1) := by
        exact (continuousOn_const.sub continuousOn_id : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.uIcc (0:ℝ) 1))
      exact hscalar.smul hfd_cont0
    have hD_ae : AEStronglyMeasurable
        (fun τ : ℝ => (1 - τ) • fderiv ℝ G (s + τ * (σ - s), σ) (1, 0))
        (volume.restrict (Ι (0:ℝ) 1)) :=
      hD_cont.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
        Set.uIoc_subset_uIcc
    have hw_ae : AEStronglyMeasurable w (volume.restrict (Ι (0:ℝ) 1)) :=
      hmeas_weight.aestronglyMeasurable
    have hprod : AEStronglyMeasurable
        (fun τ : ℝ => w τ • ((1 - τ) • fderiv ℝ G (s + τ * (σ - s), σ) (1, 0)))
        (volume.restrict (Ι (0:ℝ) 1)) :=
      continuous_smul.comp_aestronglyMeasurable₂ hw_ae hD_ae
    simpa [F', G] using hprod

  -- Uniform bound on the partial derivative of `K` on the compact segment used by `U`.
  let A : ℝ := s - δ
  let Cset : Set (ℝ × ℝ) := Set.Icc A σ ×ˢ Set.Icc σ σ
  let O : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo a b
  have hsa : 0 < s - a := sub_pos.mpr hs.1
  have hσs : 0 < σ - s := sub_pos.mpr hσ.1
  have hδ_lt_sa : δ < s - a := by
    dsimp [δ]
    exact lt_of_lt_of_le (half_lt_self (lt_min hsa hσs)) (min_le_left _ _)
  have hA_gt_a : a < A := by
    dsimp [A]
    linarith
  have hA_lt_σ : A < σ := by
    dsimp [A]
    linarith
  have hCset_sub_O : Cset ⊆ O := by
    intro q hq
    have hq1 := hq.1
    have hq2 := hq.2
    have hq2_eq : q.2 = σ := le_antisymm hq2.2 hq2.1
    constructor
    · constructor
      · exact lt_of_lt_of_le hA_gt_a hq1.1
      · exact lt_of_le_of_lt hq1.2 hσ.2
    · constructor
      · rw [hq2_eq]; exact lt_trans hs.1 hσ.1
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

  have hpt_Cset : ∀ x ∈ U, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      (x + τ * (σ - x), σ) ∈ Cset := by
    intro x hx τ hτ
    have hx_gt_a : a < x := (hU_mem x hx).1.1
    have hx_lt_σ : x < σ := (hU_mem x hx).2.1
    have hτ0 : 0 ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hx_ge_A : A ≤ x := by
      have hdist : |x - s| < δ := by
        simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hx
      have hneg : -(δ) < x - s := (abs_lt.mp hdist).1
      dsimp [A]
      linarith
    have hp_ge_x : x ≤ x + τ * (σ - x) := by
      have hnonneg : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (sub_nonneg.mpr (le_of_lt hx_lt_σ))
      linarith
    have hp_le_σ : x + τ * (σ - x) ≤ σ := by
      have hle : τ * (σ - x) ≤ 1 * (σ - x) :=
        mul_le_mul_of_nonneg_right hτ1 (sub_nonneg.mpr (le_of_lt hx_lt_σ))
      linarith
    constructor
    · constructor
      · exact le_trans hx_ge_A hp_ge_x
      · exact hp_le_σ
    · constructor
      · exact le_rfl
      · exact le_rfl

  have hbound_int : IntervalIntegrable (fun τ : ℝ => C * w τ) volume (0:ℝ) 1 := by
    simpa using hw_int.const_mul C

  have h_bound : ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ∀ x ∈ U, ‖F' x τ‖ ≤ C * w τ := by
    filter_upwards with τ hτ
    intro x hx
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hτ_rect : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ0, hτ1⟩
    have hpt := hpt_Cset x hx τ hτ_rect
    have hfderiv_norm : ‖fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖ ≤ C := hC_bound _ hpt
    have hw_nonneg : 0 ≤ w τ := by
      unfold w
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h_abs_1_sub : |1 - τ| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hτ1)]
      linarith
    have hDnorm : ‖(1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖ ≤ C := by
      calc
        ‖(1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖
            = |1 - τ| * ‖fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖ := norm_smul _ _
        _ ≤ 1 * C := mul_le_mul h_abs_1_sub hfderiv_norm (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    calc
      ‖F' x τ‖ = ‖w τ • ((1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0))‖ := by
        simp [F', G]
      _ = |w τ| * ‖(1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖ := norm_smul _ _
      _ = w τ * ‖(1 - τ) • fderiv ℝ G (x + τ * (σ - x), σ) (1, 0)‖ := by
        rw [abs_of_nonneg hw_nonneg]
      _ ≤ w τ * C := mul_le_mul_of_nonneg_left hDnorm hw_nonneg
      _ = C * w τ := mul_comm _ _

  have h_diff : ∀ᵐ τ ∂volume, τ ∈ Ι (0:ℝ) 1 → ∀ x ∈ U,
      HasDerivAt (fun v : ℝ => F v τ) (F' x τ) x := by
    filter_upwards with τ hτ
    intro x hx
    have hτ' : τ ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ'.1
    have hτ1 : τ ≤ 1 := hτ'.2
    have hx' := hU_mem x hx
    have hderivK := hasDerivAt_K_affine_slice (E := E) hK_cont hx'.1 hx'.2 hτ0 hτ1
    have hderivF := hderivK.const_smul (w τ)
    have hfun_event : (fun v : ℝ => w τ • K (v + τ * (σ - v)) σ) =ᶠ[𝓝 x]
        (w τ • fun v : ℝ => K (v + τ * (σ - v)) σ) := by
      apply Filter.Eventually.of_forall
      intro v
      rfl
    have hderivF' := hderivF.congr_of_eventuallyEq hfun_event
    simpa [F, F', G, w] using hderivF' 

  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := E) (a := (0:ℝ)) (b := (1:ℝ))
    (F := F) (F' := F') (x₀ := s) (s := U) (bound := fun τ : ℝ => C * w τ)
    hU_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hmain := hdom.2
  simpa [F, F', G, w] using hmain

end Commons.Analysis.Abel