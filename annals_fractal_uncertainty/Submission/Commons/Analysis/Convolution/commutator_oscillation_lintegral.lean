import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Convolution

lemma rpow_half_sq {x : ℝ≥0∞} : (x ^ (1/2:ℝ)) ^ (2:ℕ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, show (1/2:ℝ) * ((2:ℕ):ℝ) = 1 by norm_num,
    ENNReal.rpow_one]

lemma rpow_half_mul {x : ℝ≥0∞} : x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x := by
  rw [← sq, rpow_half_sq]

lemma sq_lintegral_mul_le_mul_lintegral_mul_sq {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f h : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) :
    (∫⁻ a, f a * h a ∂μ) ^ 2 ≤ (∫⁻ a, f a ∂μ) * ∫⁻ a, f a * h a ^ 2 ∂μ := by
  have hconj : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; exact ⟨by norm_num, by norm_num⟩
  have hF : AEMeasurable (fun a => f a ^ (1/2:ℝ)) μ := hf.pow_const _
  have hH : AEMeasurable (fun a => f a ^ (1/2:ℝ) * h a) μ := hF.mul hh
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hF hH
  have hL : ∫⁻ a, (f a ^ (1/2:ℝ)) * (f a ^ (1/2:ℝ) * h a) ∂μ = ∫⁻ a, f a * h a ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [← mul_assoc, rpow_half_mul]
  have hF2 : ∫⁻ a, (f a ^ (1/2:ℝ)) ^ (2:ℝ) ∂μ = ∫⁻ a, f a ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.rpow_two, rpow_half_sq]
  have hH2 : ∫⁻ a, (f a ^ (1/2:ℝ) * h a) ^ (2:ℝ) ∂μ = ∫⁻ a, f a * h a ^ 2 ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), ENNReal.rpow_two, rpow_half_sq,
      ENNReal.rpow_two]
  have key2 : ∫⁻ a, f a * h a ∂μ
      ≤ (∫⁻ a, f a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, f a * h a ^ 2 ∂μ) ^ (1/2:ℝ) := by
    rw [← hL, ← hF2, ← hH2]
    exact key
  calc (∫⁻ a, f a * h a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, f a * h a ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 :=
        pow_le_pow_left' key2 2
    _ = (∫⁻ a, f a ∂μ) * ∫⁻ a, f a * h a ^ 2 ∂μ := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]

lemma map_sub_left_eq_self_volume {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin n) => x - y) volume = volume := by
  have hc : (fun y : EuclideanSpace ℝ (Fin n) => x - y)
      = (fun z : EuclideanSpace ℝ (Fin n) => z + x) ∘ Neg.neg := by
    funext y; simp only [Function.comp_apply]; abel
  rw [hc]
  have hcomp : Measure.map ((fun z : EuclideanSpace ℝ (Fin n) => z + x) ∘ Neg.neg) volume
      = Measure.map (fun z : EuclideanSpace ℝ (Fin n) => z + x) (Measure.map Neg.neg volume) :=
    (Measure.map_map (g := fun z : EuclideanSpace ℝ (Fin n) => z + x) (f := Neg.neg)
      (μ := volume) (measurable_id.add measurable_const) measurable_neg).symm
  rw [hcomp, Measure.map_neg_eq_self, map_add_right_eq_self]

lemma ae_eq_comp_sub_left {n : ℕ} {f f' : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : f =ᵐ[volume] f') (x : EuclideanSpace ℝ (Fin n)) :
    (fun y => f (x - y)) =ᵐ[volume] (fun y => f' (x - y)) := by
  have hφ : Measurable (fun y : EuclideanSpace ℝ (Fin n) => x - y) := measurable_const.sub measurable_id
  exact ae_eq_comp hφ.aemeasurable (by rw [map_sub_left_eq_self_volume x]; exact h)

lemma aemeasurable_comp_sub_left {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hg : AEMeasurable g volume) (x : EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (fun y => g (x - y)) volume := by
  have hφ : Measurable (fun y : EuclideanSpace ℝ (Fin n) => x - y) := measurable_const.sub measurable_id
  have h1 : AEMeasurable g (Measure.map (fun y : EuclideanSpace ℝ (Fin n) => x - y) volume) := by
    rw [map_sub_left_eq_self_volume x]; exact hg
  exact h1.comp_measurable hφ

theorem commutator_oscillation_lintegral {n : ℕ}
    {a u : EuclideanSpace ℝ (Fin n) → ℂ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {ω : ℝ}
    (hρnn : ∀ x, 0 ≤ ρ x) (hρint : Integrable ρ volume) (hρ1 : ∫ x, ρ x ∂volume = 1)
    (hω : 0 ≤ ω) (hosc : ∀ x y, ρ y ≠ 0 → ‖a x - a (x - y)‖ ≤ ω)
    (hu : MemLp u 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∫⁻ x, ENNReal.ofReal
        (‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2) ∂volume
      ≤ ENNReal.ofReal (ω ^ 2) * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂volume := by
  set ρ' : EuclideanSpace ℝ (Fin n) → ℝ := hρint.aestronglyMeasurable.mk with hρ'def
  set u' : EuclideanSpace ℝ (Fin n) → ℂ := hu.aestronglyMeasurable.mk with hu'def
  have hρ'_meas : Measurable ρ' := by rw [hρ'def]; exact hρint.aestronglyMeasurable.measurable_mk
  have hu'_meas : Measurable u' := by rw [hu'def]; exact hu.aestronglyMeasurable.measurable_mk
  have hρ'_ae : ρ =ᵐ[volume] ρ' := by rw [hρ'def]; exact hρint.aestronglyMeasurable.ae_eq_mk
  have hu'_ae : u =ᵐ[volume] u' := by rw [hu'def]; exact hu.aestronglyMeasurable.ae_eq_mk
  have hρe'_meas : Measurable (fun y => ENNReal.ofReal (ρ' y)) := hρ'_meas.ennreal_ofReal
  have hg'_meas : Measurable (fun z => ENNReal.ofReal (‖u' z‖ ^ 2)) :=
    ((hu'_meas.norm).pow_const 2).ennreal_ofReal
  have hρe_ae : (fun y => ENNReal.ofReal (ρ y)) =ᵐ[volume] (fun y => ENNReal.ofReal (ρ' y)) :=
    hρ'_ae.fun_comp ENNReal.ofReal
  have hnorm_ae : (fun z => ‖u z‖) =ᵐ[volume] (fun z => ‖u' z‖) := hu'_ae.fun_comp (fun z => ‖z‖)
  have hsq_ae : (fun z => ‖u z‖ ^ 2) =ᵐ[volume] (fun z => ‖u' z‖ ^ 2) := by
    filter_upwards [hnorm_ae.mul hnorm_ae] with z hz
    simpa [pow_two] using hz
  have hg_ae : (fun z => ENNReal.ofReal (‖u z‖ ^ 2)) =ᵐ[volume]
      (fun z => ENNReal.ofReal (‖u' z‖ ^ 2)) := hsq_ae.fun_comp ENNReal.ofReal
  have huncurry : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (ρ' p.2) * ENNReal.ofReal (‖u' (p.1 - p.2)‖ ^ 2)) :=
    (hρe'_meas.comp measurable_snd).mul (hg'_meas.comp (measurable_fst.sub measurable_snd))
  have hton : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume ∂volume
      = (∫⁻ y, ENNReal.ofReal (ρ' y) ∂volume) * ∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂volume := by
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume ∂volume
        = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume ∂volume :=
          lintegral_lintegral_swap huncurry.aemeasurable
      _ = ∫⁻ y, ENNReal.ofReal (ρ' y) * (∫⁻ x, ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume) ∂volume := by
          refine lintegral_congr (fun y => ?_)
          exact lintegral_const_mul _ (hg'_meas.comp (measurable_id.sub measurable_const))
      _ = ∫⁻ y, ENNReal.ofReal (ρ' y) * (∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂volume) ∂volume := by
          refine lintegral_congr (fun y => ?_)
          congr 1
          rw [show (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖u' (x - y)‖ ^ 2))
                = (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖u' (x + (-y))‖ ^ 2)) by
                funext x; rw [sub_eq_add_neg]]
          exact lintegral_add_right_eq_self (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖u' x‖ ^ 2)) (-y)
      _ = (∫⁻ y, ENNReal.ofReal (ρ' y) ∂volume) * ∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂volume := by
          rw [lintegral_mul_const _ hρe'_meas]
  have hG_eq_pt : ∀ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume)
      = ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume := by
    intro x
    refine lintegral_congr_ae ?_
    filter_upwards [hρe_ae, ae_eq_comp_sub_left hg_ae x] with y hy1 hy2
    rw [hy1, hy2]
  have hG_eq : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) ∂volume
      = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume) ∂volume :=
    lintegral_congr hG_eq_pt
  have hρe_int : (∫⁻ y, ENNReal.ofReal (ρ y) ∂volume) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ hρnn), hρ1]
    simp
  have hρe'_int : (∫⁻ y, ENNReal.ofReal (ρ' y) ∂volume) = 1 := by
    rw [lintegral_congr_ae hρe_ae.symm, hρe_int]
  have hg'_int : (∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂volume)
      = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂volume := by
    rw [lintegral_congr_ae hg_ae.symm]
  have hG_eq' : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) ∂volume
      = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂volume := by
    rw [hG_eq, hton, hρe'_int, hg'_int, one_mul]
  -- finiteness a.e. of the convolution density
  have hgu_int : Integrable (fun x => ‖u x‖ ^ 2) volume := hu.integrable_norm_pow (by norm_num)
  have hg_lt_top : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂volume < ⊤ := hgu_int.lintegral_lt_top
  have hG'_meas : Measurable
      (fun x => ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume) :=
    huncurry.lintegral_prod_right
  have hG_meas : AEMeasurable
      (fun x => ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) volume :=
    hG'_meas.aemeasurable.congr (by filter_upwards with x; exact (hG_eq_pt x).symm)
  have hGfin : ∀ᵐ x ∂volume,
      (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) < ⊤ := by
    have h1 : ∀ᵐ x ∂volume,
        (∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂volume) < ⊤ :=
      ae_lt_top hG'_meas (by rw [hton, hρe'_int, one_mul, hg'_int]; exact ne_of_lt hg_lt_top)
    filter_upwards [h1] with x hx
    rwa [hG_eq_pt x]
  -- pointwise estimate
  have hpt : ∀ᵐ x ∂volume, ENNReal.ofReal
        (‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2)
      ≤ ENNReal.ofReal (ω ^ 2) * (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) := by
    filter_upwards [hGfin] with x hx
    set Ax : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal ‖u (x - y)‖ ∂volume with hAxdef
    set Gx : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume with hGxdef
    have hx' : Gx < ⊤ := by rw [hGxdef]; exact hx
    have hf_aem : AEMeasurable (fun y => ENNReal.ofReal (ρ y)) volume :=
      hρint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hh_aem : AEMeasurable (fun y => ENNReal.ofReal ‖u (x - y)‖) volume :=
      aemeasurable_comp_sub_left (hu.aemeasurable.norm).ennreal_ofReal x
    have hA_aem : AEMeasurable
        (fun y => ENNReal.ofReal (ρ y) * ENNReal.ofReal ‖u (x - y)‖) volume := hf_aem.mul hh_aem
    have hCS : Ax ^ 2 ≤ Gx := by
      have h := sq_lintegral_mul_le_mul_lintegral_mul_sq hf_aem hh_aem
      have hfac : (fun y => ENNReal.ofReal (ρ y) * (ENNReal.ofReal ‖u (x - y)‖) ^ 2)
          = (fun y => ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)) := by
        funext y; rw [ENNReal.ofReal_pow (norm_nonneg _)]
      rw [hfac, hρe_int, one_mul, ← hAxdef, ← hGxdef] at h
      exact h
    have hL_le_B : (∫⁻ y, ENNReal.ofReal ‖ρ y • ((a x - a (x - y)) * u (x - y))‖) ≤
        ∫⁻ y, ENNReal.ofReal (ρ y * ω * ‖u (x - y)‖) := by
      refine lintegral_mono (fun y => ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have hnorm_eq : ‖ρ y • ((a x - a (x - y)) * u (x - y))‖
          = ρ y * (‖a x - a (x - y)‖ * ‖u (x - y)‖) := by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (hρnn y)]
      have h1 : ρ y * ‖a x - a (x - y)‖ ≤ ρ y * ω := by
        rcases eq_or_lt_of_le (hρnn y) with h0 | hpos
        · rw [← h0]; simp
        · exact mul_le_mul_of_nonneg_left (hosc x y (ne_of_gt hpos)) (hρnn y)
      rw [hnorm_eq]
      calc ρ y * (‖a x - a (x - y)‖ * ‖u (x - y)‖)
          = (ρ y * ‖a x - a (x - y)‖) * ‖u (x - y)‖ := by ring
        _ ≤ (ρ y * ω) * ‖u (x - y)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ρ y * ω * ‖u (x - y)‖ := by ring
    have hB_eq : (∫⁻ y, ENNReal.ofReal (ρ y * ω * ‖u (x - y)‖))
        = ENNReal.ofReal ω * Ax := by
      have hpt2 : ∀ y, ENNReal.ofReal (ρ y * ω * ‖u (x - y)‖)
          = ENNReal.ofReal ω * (ENNReal.ofReal (ρ y) * ENNReal.ofReal ‖u (x - y)‖) := by
        intro y
        rw [ENNReal.ofReal_mul (mul_nonneg (hρnn y) hω), ENNReal.ofReal_mul (hρnn y)]
        ring
      rw [hAxdef]
      simp only [hpt2]
      rw [lintegral_const_mul'' (ENNReal.ofReal ω) hA_aem]
    have hAx_ne_top : Ax ≠ ⊤ := by
      intro h
      have h2 : Ax ^ 2 = ⊤ := by rw [h]; simp
      have htop : Gx = ⊤ := top_le_iff.mp (by rw [← h2]; exact hCS)
      exact absurd htop (ne_of_lt hx')
    have hB_ne_top : (∫⁻ y, ENNReal.ofReal (ρ y * ω * ‖u (x - y)‖)) ≠ ⊤ := by
      rw [hB_eq]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAx_ne_top
    have hnorm_le : ‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖
        ≤ ω * Ax.toReal := by
      have h1 := (norm_integral_le_lintegral_norm
        (fun y => ρ y • ((a x - a (x - y)) * u (x - y)))).trans
        (ENNReal.toReal_mono hB_ne_top hL_le_B)
      rwa [hB_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal hω] at h1
    have hp : (Ax ^ 2).toReal = Ax.toReal ^ 2 := by rw [pow_two, pow_two, ENNReal.toReal_mul]
    have key : ‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2 ≤ ω ^ 2 * Gx.toReal := by
      calc ‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2
          ≤ (ω * Ax.toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
        _ = ω ^ 2 * (Ax ^ 2).toReal := by rw [hp]; ring
        _ ≤ ω ^ 2 * Gx.toReal := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ω)
            exact ENNReal.toReal_mono (ne_of_lt hx') hCS
    have hstep : ENNReal.ofReal
          (‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2)
        ≤ ENNReal.ofReal (ω ^ 2) * Gx := by
      calc ENNReal.ofReal (‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2)
          ≤ ENNReal.ofReal (ω ^ 2 * Gx.toReal) := ENNReal.ofReal_le_ofReal key
        _ = ENNReal.ofReal (ω ^ 2) * ENNReal.ofReal Gx.toReal := ENNReal.ofReal_mul (sq_nonneg ω)
        _ ≤ ENNReal.ofReal (ω ^ 2) * Gx := by
            apply mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le
            positivity
    rw [hGxdef]; exact hstep
  -- final assembly
  calc ∫⁻ x, ENNReal.ofReal (‖∫ y, ρ y • ((a x - a (x - y)) * u (x - y)) ∂volume‖ ^ 2) ∂volume
      ≤ ∫⁻ x, ENNReal.ofReal (ω ^ 2) *
          (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) ∂volume :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (ω ^ 2) *
          ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2) ∂volume) ∂volume := by
        rw [lintegral_const_mul'' (ENNReal.ofReal (ω ^ 2)) hG_meas]
    _ = ENNReal.ofReal (ω ^ 2) * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂volume := by rw [hG_eq']

end Commons.Analysis.Convolution