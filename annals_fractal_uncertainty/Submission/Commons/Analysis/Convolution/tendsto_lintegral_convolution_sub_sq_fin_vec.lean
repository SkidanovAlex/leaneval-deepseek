import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero
import Submission.Commons.Analysis.Convolution.aemeasurable_uncurry_ofReal_mul_enorm_sq
import Submission.Commons.Measure.Integral.integral_smoothing_rpow_le_of_integrable

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal

/-- `ENNReal.ofReal` of a squared norm is the squared `enorm`. -/
lemma ofReal_norm_sq_eq_fin_vec {F : Type*} [SeminormedAddCommGroup F] (z : F) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]

/-- The `ℝ≥0∞`-integral of a nonnegative probability density is `1`. -/
lemma lintegral_ofReal_eq_one_fin_vec {d : ℕ} {ρ : (Fin d → ℂ) → ℝ} (hρnn : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ (volume : Measure (Fin d → ℂ)))
    (hρ1 : ∫ x, ρ x ∂(volume : Measure (Fin d → ℂ)) = 1) :
    ∫⁻ x, ENNReal.ofReal (ρ x) ∂(volume : Measure (Fin d → ℂ)) = 1 := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρnn), hρ1]
  simp

set_option synthInstance.maxSize 1024 in
/-- **Translation is continuous in `L²`.**  For `u ∈ L²(ℂᵈ, E)`, the `L²`-mass of the difference
`x ↦ u (x - y) - u x` tends to `0` as `y → 0`. -/
private theorem tendsto_lintegral_translate_sub_fin_vec_aux {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (u : (Fin d → ℂ) → E)
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    Tendsto (fun y : (Fin d → ℂ) => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ)
      ∂(volume : Measure (Fin d → ℂ))) (𝓝 0) (𝓝 0) := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hcont : Continuous fun y : (Fin d → ℂ) =>
      DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))) := by
    fun_prop
  have hsubmp : ∀ y : (Fin d → ℂ),
      Measure.QuasiMeasurePreserving (fun x : (Fin d → ℂ) => -y +ᵥ x)
        (volume : Measure (Fin d → ℂ)) (volume : Measure (Fin d → ℂ)) :=
    fun y => (measurePreserving_vadd (-y) volume).quasiMeasurePreserving
  have hFae : ∀ y : (Fin d → ℂ),
      (↑↑(DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))) =ᵐ[volume]
        fun x => u (x - y) := by
    intro y
    have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ)))
    have h2 := (hsubmp y).ae_eq_comp hu.coeFn_toLp
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.comp_apply] at hx1 hx2 ⊢
    rw [hx1, hx2]
    congr 1
    abel
  have hdist : Tendsto (fun y : (Fin d → ℂ) =>
      dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))
        ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ)))) (𝓝 0) (𝓝 0) := by
    have hconst : Continuous fun _ : (Fin d → ℂ) => ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))) := continuous_const
    have hcd : Continuous fun y : (Fin d → ℂ) =>
        dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))
          ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))) := hcont.dist hconst
    have h := hcd.tendsto (0 : Fin d → ℂ)
    simpa using h
  have hkey : ∀ y : (Fin d → ℂ),
      dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))
        ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ)))
      = (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal := by
    intro y
    rw [Lp.dist_eq_eLpNorm_neg_add]
    congr 1
    have hae : (-(↑↑(DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))) + ↑↑((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))) : (Fin d → ℂ) → E)
        =ᵐ[volume] -(fun x : (Fin d → ℂ) => u (x - y) - u x) := by
      filter_upwards [hFae y, hu.coeFn_toLp] with x h3 h4
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [h3, h4]
      abel
    rw [eLpNorm_congr_ae hae, eLpNorm_neg]
  have hG : Tendsto (fun y : (Fin d → ℂ) => (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal) (𝓝 0) (𝓝 0) := by
    rw [show (fun y : (Fin d → ℂ) => (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal)
        = (fun y : (Fin d → ℂ) => dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ))))
            ((hu.toLp u) : Lp E 2 (volume : Measure (Fin d → ℂ)))) from funext fun y => (hkey y).symm]
    exact hdist
  have hfin : ∀ y : (Fin d → ℂ), eLpNorm (fun x => u (x - y) - u x) 2 volume ≠ ⊤ := by
    intro y
    have h1 : MemLp (fun x : (Fin d → ℂ) => u (x - y)) 2 (volume : Measure (Fin d → ℂ)) :=
      hu.comp_measurePreserving (measurePreserving_sub_right volume y)
    exact (h1.sub hu).eLpNorm_ne_top
  have hE : Tendsto (fun y : (Fin d → ℂ) => eLpNorm (fun x => u (x - y) - u x) 2 volume) (𝓝 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with h | h
    · exact Eventually.of_forall fun y => h ▸ le_top
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) h
      filter_upwards [hG.eventually (isOpen_Iio.mem_nhds (by simpa using hpos))] with y hy
      rw [← ENNReal.ofReal_toReal (hfin y), ← ENNReal.ofReal_toReal h,
        ENNReal.ofReal_le_ofReal_iff hpos.le]
      exact le_of_lt hy
  rw [ENNReal.tendsto_nhds_zero] at hE ⊢
  intro ε hε
  have hmin : (0:ℝ≥0∞) < min ε 1 := lt_min hε one_pos
  filter_upwards [hE (min ε 1) hmin] with y hy
  have hsplit : (∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂(volume : Measure (Fin d → ℂ)))
      = (eLpNorm (fun x => u (x - y) - u x) 2 volume) ^ (2:ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hsplit]
  calc (eLpNorm (fun x => u (x - y) - u x) 2 volume) ^ (2:ℝ)
      ≤ (min ε 1) ^ (2:ℝ) := ENNReal.rpow_le_rpow hy (by norm_num)
    _ ≤ min ε 1 := by
        rw [ENNReal.rpow_two]
        calc (min ε 1) ^ 2 = (min ε 1) * (min ε 1) := pow_two _
          _ ≤ 1 * (min ε 1) := by gcongr; exact min_le_right _ _
          _ = min ε 1 := one_mul _
    _ ≤ ε := min_le_left _ _

/-- The squared `L²`-mass of a `MemLp 2` function into `E` is finite. -/
private theorem lintegral_enorm_rpow_two_lt_top_fin_vec {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {u : (Fin d → ℂ) → E}
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    ∫⁻ z, ‖u z‖ₑ ^ (2:ℝ) < ⊤ := by
  have hInt : Integrable (fun z : Fin d → ℂ => ‖u z‖ ^ (2:ℝ))
      (volume : Measure (Fin d → ℂ)) := by
    simpa using hu.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
  have hfin : ∫⁻ z, ‖(‖u z‖ ^ (2:ℝ))‖ₑ < ⊤ :=
    MeasureTheory.hasFiniteIntegral_iff_enorm.mp hInt.2
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  apply lintegral_congr
  intro z
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) 2),
    show ‖u z‖ₑ = ENNReal.ofReal ‖u z‖ by simp [enorm],
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]

/-- For `ρ ∈ L¹` and `u ∈ L²`, the weighted `L²`-mass of `u` is finite for a.e. `x`. -/
private theorem ae_lintegral_enorm_mul_enorm_rpow_two_lt_top_fin_vec {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {ρ : (Fin d → ℂ) → ℝ} {u : (Fin d → ℂ) → E}
    (hρi : Integrable ρ (volume : Measure (Fin d → ℂ)))
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)),
      (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ)) < ⊤ := by
  set F : (Fin d → ℂ) → ℝ≥0∞ := fun x => ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) with hFdef
  have hΦ : AEMeasurable (Function.uncurry fun (x y : (Fin d → ℂ)) =>
      ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ))
      ((volume : Measure (Fin d → ℂ)).prod volume) := by
    have h1 : AEMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖ρ p.2‖ₑ)
        ((volume : Measure (Fin d → ℂ)).prod volume) :=
      hρi.aestronglyMeasurable.enorm.comp_snd
    have h2 : AEMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖u (p.1 - p.2)‖ₑ)
        ((volume : Measure (Fin d → ℂ)).prod volume) :=
      (hu.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact h1.mul (h2.pow_const (2:ℝ))
  have hFae : AEMeasurable F (volume : Measure (Fin d → ℂ)) := by
    rw [hFdef]; exact hΦ.lintegral_prod_right'
  have hInt : ∫⁻ x, F x ∂(volume : Measure (Fin d → ℂ)) < ⊤ := by
    rw [hFdef]
    rw [lintegral_lintegral_swap hΦ]
    have hinner : ∀ y : (Fin d → ℂ),
        (∫⁻ x, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ))
          = ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) := by
      intro y
      rw [lintegral_const_mul'']
      · congr 1
        exact lintegral_sub_right_eq_self (fun z => ‖u z‖ₑ ^ (2:ℝ)) y
      · exact (hu.aestronglyMeasurable.enorm.pow_const (2:ℝ)).comp_quasiMeasurePreserving
          (by simpa [sub_eq_add_neg] using
            (measurePreserving_add_right volume (-y)).quasiMeasurePreserving)
    simp_rw [hinner]
    calc ∫⁻ y, ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ))
        = (∫⁻ y, ‖ρ y‖ₑ) * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) :=
          lintegral_mul_const'' _ hρi.aestronglyMeasurable.enorm
      _ < ⊤ := ENNReal.mul_lt_top hρi.2 (lintegral_enorm_rpow_two_lt_top_fin_vec hu)
  exact ae_lt_top' hFae (ne_of_lt hInt)

/-- If `ρ ∈ L¹` and `u ∈ L²`, then `y ↦ ρ y • u (x - y)` is Bochner integrable for a.e. `x`. -/
private theorem ae_integrable_smul_convolution_fin_vec {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ : (Fin d → ℂ) → ℝ} {u : (Fin d → ℂ) → E}
    (hρi : Integrable ρ (volume : Measure (Fin d → ℂ)))
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)),
      Integrable (fun y => ρ y • u (x - y)) (volume : Measure (Fin d → ℂ)) := by
  filter_upwards [ae_lintegral_enorm_mul_enorm_rpow_two_lt_top_fin_vec hρi hu] with x hx
  have hsub : AEStronglyMeasurable (fun y : Fin d → ℂ => u (x - y))
      (volume : Measure (Fin d → ℂ)) :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  refine ⟨hρi.aestronglyMeasurable.smul hsub, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hfa : AEMeasurable (fun y : Fin d → ℂ => ‖u (x - y)‖ₑ)
      (volume : Measure (Fin d → ℂ)) := hsub.enorm
  have hga : AEMeasurable (fun y : Fin d → ℂ => ‖ρ y‖ₑ)
      (volume : Measure (Fin d → ℂ)) := hρi.aestronglyMeasurable.enorm
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le
    (ν := (volume : Measure (Fin d → ℂ))) (q := 2) (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y)‖ₑ * ‖ρ y‖ₑ)
        = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y)‖ₑ ^ (2:ℝ) * ‖ρ y‖ₑ)
        = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hCS
  have hbound : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt hCS (ENNReal.mul_lt_top hx hρi.2)
  have hfin' : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) < ⊤ := by
    by_contra hc
    rw [not_lt] at hc
    have htop : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) = ⊤ := top_le_iff.mp hc
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hbound
    exact lt_irrefl _ hbound
  exact lt_of_eq_of_lt (lintegral_congr fun y => by rw [enorm_smul]) hfin'

/-- **Convolution is close to the identity in a weighted `L²` sense.**  For a nonnegative integrable
`ρ` with `∫ ρ = 1` and any `u ∈ L²`, almost every `x` satisfies
`‖(ρ ⋆ u)(x) - u x‖ₑ ^ 2 ≤ ∫⁻ y, ρ y ‖u (x - y) - u x‖ₑ ^ 2`. -/
theorem enorm_convolution_sub_le_fin_vec {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ρ : (Fin d → ℂ) → ℝ}
    (hρnn : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ (volume : Measure (Fin d → ℂ)))
    (hρ1 : ∫ x, ρ x ∂(volume : Measure (Fin d → ℂ)) = 1)
    (u : (Fin d → ℂ) → E)
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    Filter.Eventually (fun x => ‖(∫ y, ρ y • u (x - y) ∂(volume : Measure (Fin d → ℂ))) - u x‖ₑ ^ 2
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2
        ∂(volume : Measure (Fin d → ℂ)))
      (ae (volume : Measure (Fin d → ℂ))) := by
  filter_upwards [ae_integrable_smul_convolution_fin_vec hρi hu] with x hx
  have hconst : ∫ y, ρ y • u x ∂(volume : Measure (Fin d → ℂ)) = u x := by
    rw [integral_smul_const, hρ1, one_smul]
  have hsplit : (∫ y, ρ y • u (x - y) ∂(volume : Measure (Fin d → ℂ))) - u x
      = ∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure (Fin d → ℂ)) := by
    conv_lhs => rw [← hconst]
    rw [← integral_sub hx (hρi.smul_const (u x))]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_sub]
  rw [hsplit]
  have hD : ‖∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure (Fin d → ℂ))‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂(volume : Measure (Fin d → ℂ)) := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    rw [enorm_smul, Real.enorm_eq_ofReal (hρnn y)]
  have hD2 : ‖∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure (Fin d → ℂ))‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂(volume : Measure (Fin d → ℂ))) ^ (2:ℝ) :=
    ENNReal.rpow_le_rpow hD (by norm_num)
  have hfa : AEMeasurable (fun y : Fin d → ℂ => ‖u (x - y) - u x‖ₑ)
      (volume : Measure (Fin d → ℂ)) := by
    have hsub : AEStronglyMeasurable (fun y : Fin d → ℂ => u (x - y))
        (volume : Measure (Fin d → ℂ)) :=
      hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    exact (hsub.sub aestronglyMeasurable_const).enorm
  have hga : AEMeasurable (fun y : Fin d → ℂ => ENNReal.ofReal (ρ y))
      (volume : Measure (Fin d → ℂ)) := hρi.aemeasurable.ennreal_ofReal
  have ha1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(volume : Measure (Fin d → ℂ)) = 1 :=
    lintegral_ofReal_eq_one_fin_vec hρnn hρi hρ1
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le
    (ν := (volume : Measure (Fin d → ℂ))) (q := 2) (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y) - u x‖ₑ * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      ha1, show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, mul_one] at hCS
  simpa [ENNReal.rpow_two] using hD2.trans hCS

/-- **A.e.-measurability of the convolution integrand.** -/
theorem aemeasurable_uncurry_ofReal_mul_enorm_sq_fin_vec {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {ρ : (Fin d → ℂ) → ℝ}
    (hρi : Integrable ρ (volume : Measure (Fin d → ℂ)))
    (u : (Fin d → ℂ) → E)
    (hu : MemLp u 2 (volume : Measure (Fin d → ℂ))) :
    AEMeasurable (Function.uncurry fun x y : (Fin d → ℂ) =>
        ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2)
      ((volume : Measure (Fin d → ℂ)).prod (volume : Measure (Fin d → ℂ))) := by
  have h1 : AEMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ENNReal.ofReal (ρ p.2))
      ((volume : Measure (Fin d → ℂ)).prod (volume : Measure (Fin d → ℂ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hρi.aemeasurable.comp_snd
  have hsub : AEStronglyMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => u (p.1 - p.2))
      ((volume : Measure (Fin d → ℂ)).prod (volume : Measure (Fin d → ℂ))) :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  have hfst : AEStronglyMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => u p.1)
      ((volume : Measure (Fin d → ℂ)).prod (volume : Measure (Fin d → ℂ))) :=
    hu.aestronglyMeasurable.comp_fst
  have h5 : AEMeasurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2)
      ((volume : Measure (Fin d → ℂ)).prod (volume : Measure (Fin d → ℂ))) :=
    (hsub.sub hfst).enorm.pow_const 2
  exact h1.mul h5

theorem tendsto_lintegral_convolution_sub_sq_fin_vec {d : ℕ} {ι : Type*} {l : Filter ι}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ρ : ι → (Fin d → ℂ) → ℝ) (hρnn : ∀ i x, 0 ≤ ρ i x)
    (hρi : ∀ i, MeasureTheory.Integrable (ρ i) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 1)
    (R : ι → ℝ) (hRpos : ∀ i, 0 ≤ R i) (hR : Filter.Tendsto R l (nhds 0))
    (hRs : ∀ i, ∀ x, R i < ‖x‖ → ρ i x = 0)
    (u : (Fin d → ℂ) → E)
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :
    Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal
      (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) l (nhds 0) := by
  let G : (Fin d → ℂ) → ℝ≥0∞ := fun y => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ)
    ∂(volume : Measure (Fin d → ℂ))
  have hGtend : Tendsto G (𝓝 0) (𝓝 0) := tendsto_lintegral_translate_sub_fin_vec_aux u hu
  have hS : Tendsto (fun i => ⨆ y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G y) l (𝓝 0) :=
    Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero hGtend R hR
  have hbound : ∀ i, (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure (Fin d → ℂ))) - u x‖ ^ 2)
        ∂(volume : Measure (Fin d → ℂ)))
      ≤ ⨆ y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G y := by
    intro i
    calc (∫⁻ x, ENNReal.ofReal (‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure (Fin d → ℂ))) - u x‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ)))
        = ∫⁻ x, ‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure (Fin d → ℂ))) - u x‖ₑ ^ (2:ℝ)
            ∂(volume : Measure (Fin d → ℂ)) :=
          lintegral_congr fun x => ofReal_norm_sq_eq_fin_vec _
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ)
            ∂(volume : Measure (Fin d → ℂ)) ∂(volume : Measure (Fin d → ℂ)) := by
          apply lintegral_mono_ae
          filter_upwards [enorm_convolution_sub_le_fin_vec (hρnn i) (hρi i) (hρ1 i) u hu] with x hx
          simpa only [ENNReal.rpow_two] using hx
      _ = ∫⁻ y, ENNReal.ofReal (ρ i y) * G y ∂(volume : Measure (Fin d → ℂ)) := by
          rw [MeasureTheory.lintegral_lintegral_swap
            (f := fun x y => ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ))
            (by
              have h := aemeasurable_uncurry_ofReal_mul_enorm_sq_fin_vec (hρi i) u hu
              simpa only [ENNReal.rpow_two] using h)]
          apply lintegral_congr; intro y
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (∫⁻ y, ENNReal.ofReal (ρ i y) ∂(volume : Measure (Fin d → ℂ))) *
            (⨆ y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G y) := by
          by_cases hStop : (⨆ y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G y) = ⊤
          · rw [hStop, lintegral_ofReal_eq_one_fin_vec (hρnn i) (hρi i) (hρ1 i), one_mul]
            exact le_top
          · rw [← MeasureTheory.lintegral_mul_const' _ _ hStop]
            apply lintegral_mono; intro y
            by_cases h : ρ i y = 0
            · simp [h]
            · have hy : y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i) := by
                by_contra hcon
                refine h (hRs i y ?_)
                have hle : ¬ dist y 0 ≤ R i := fun hc => hcon (Metric.mem_closedBall.mpr hc)
                have := not_le.mp hle
                simpa [dist_eq_norm] using this
              have hle : G y ≤ ⨆ z ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G z :=
                le_iSup₂_of_le y hy le_rfl
              exact mul_le_mul_right hle (ENNReal.ofReal (ρ i y))
      _ = ⨆ y ∈ Metric.closedBall (0 : Fin d → ℂ) (R i), G y := by
          rw [lintegral_ofReal_eq_one_fin_vec (hρnn i) (hρi i) (hρ1 i), one_mul]
  rw [ENNReal.tendsto_nhds_zero] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with i hi
  exact le_trans (hbound i) hi

end Commons.Analysis.Convolution