import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinFactor
import Submission.Work.Elliptic.DivSinMixedExpansion
import Submission.Work.Elliptic.DivSinSliceIdent
import Submission.Work.Elliptic.DthIter_slice
import Submission.Work.Elliptic.pth_DzIter
import Submission.Work.Elliptic.DivSinHardy
import Submission.Work.Elliptic.DivSinIterUnif
import Submission.Work.Elliptic.DivSinSliceFacts
import Submission.Work.Elliptic.sharp_hardy_sin_two
import Submission.Work.Elliptic.sin_l2_weight_bound
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.Elliptic

set_option linter.unusedVariables false

/-! ## a.e. facts on `Iθ` -/

lemma dtw_ae_mem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi/2) := by
  have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi/2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [hμ]; exact ae_restrict_mem measurableSet_Ioo

lemma dtw_ae_sin_pos : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 < Real.sin (2*θ) :=
  dtw_ae_mem.mono (fun θ hθ => Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))

/-! ## pointwise algebra -/

lemma dtw_div_sin_mul_weight_sq (a c s η : ℝ) (hs : 0 < s) :
    (a / s * (c / s ^ (η/2)))^2 = c^2 * (a^2 / s^(2+η)) := by
  have hS : (s ^ (η/2))^2 = s^η := by
    rw [← Real.rpow_natCast (s ^ (η/2)) 2, ← Real.rpow_mul hs.le]
    norm_num
  have hsplit : s^2 * s^η = s^(2+η) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]
    norm_num
  have h1 : (a / s * (c / s ^ (η/2)))^2 = a^2 * c^2 / (s^2 * s^η) := by
    rw [div_mul_div_comm, div_pow, mul_pow, mul_pow, hS]
  rw [h1, hsplit]
  ring

lemma dtw_mul_div_weight_sq (a c s η : ℝ) (hs : 0 < s) :
    (a * (c / s ^ (η/2)))^2 = c^2 * (a^2 / s^η) := by
  have hS : (s ^ (η/2))^2 = s^η := by
    rw [← Real.rpow_natCast (s ^ (η/2)) 2, ← Real.rpow_mul hs.le]
    norm_num
  rw [mul_pow, div_pow, hS]
  ring

lemma dtw_mul_wTheta_sq (x c s γ : ℝ) (hs : 0 < s) (hγ : γ ≠ 0) :
    (x * (c * s^(-(γ/2))))^2 = c^2 * (x^2 / s^γ) := by
  have hS : (s ^ (-(γ/2)))^2 = s^(-γ) := by
    have hne : -(γ/2) + -(γ/2) ≠ 0 := by
      have : -(γ/2) + -(γ/2) = -γ := by ring
      rw [this]; exact neg_ne_zero.mpr hγ
    rw [pow_two, ← Real.rpow_add' hs.le hne, show -(γ/2) + -(γ/2) = -γ by ring]
  rw [mul_pow, mul_pow, hS, Real.rpow_neg hs.le, inv_eq_one_div]
  ring

/-! ## the two slice-level estimates -/

lemma dtw_SliceHardy {K : ℝ}
    (hHardy : ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 → h (Real.pi/2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ ^ 2 / (Real.sin (2*θ)) ^ (2 + Work.Spaces.eta))
        ≤ K * ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ)) ^ Work.Spaces.eta)
    (h : ℝ → ℝ) (c : ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0) (hp : h (Real.pi/2) = 0) :
    (∫ θ in Work.Spaces.Iθ, (h θ / Real.sin (2*θ) * (c / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2)
      ≤ K * ∫ θ in Work.Spaces.Iθ, (deriv h θ * (c / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2 := by
  have hsin := dtw_ae_sin_pos
  have hA : (∫ θ in Work.Spaces.Iθ, (h θ / Real.sin (2*θ) * (c / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2)
      = ∫ θ in Work.Spaces.Iθ, c^2 * ((h θ)^2 / (Real.sin (2*θ))^(2 + Work.Spaces.eta)) :=
    integral_congr_ae (hsin.mono (fun θ hθ => dtw_div_sin_mul_weight_sq (h θ) c (Real.sin (2*θ)) Work.Spaces.eta hθ))
  have hB : (∫ θ in Work.Spaces.Iθ, (deriv h θ * (c / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2)
      = ∫ θ in Work.Spaces.Iθ, c^2 * ((deriv h θ)^2 / (Real.sin (2*θ))^(Work.Spaces.eta)) :=
    integral_congr_ae (hsin.mono (fun θ hθ => dtw_mul_div_weight_sq (deriv h θ) c (Real.sin (2*θ)) Work.Spaces.eta hθ))
  rw [hA, hB, integral_const_mul, integral_const_mul]
  calc c^2 * ∫ θ in Work.Spaces.Iθ, (h θ)^2 / (Real.sin (2*θ))^(2 + Work.Spaces.eta)
      ≤ c^2 * (K * ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left (hHardy h hsm h0 hp) (sq_nonneg c)
    _ = K * (c^2 * ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^(Work.Spaces.eta)) := by ring

lemma dtw_SliceIter {C0 : ℝ}
    (hIter : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 → h (Real.pi/2) = 0 →
        ∀ i ∈ Finset.Icc 1 4,
          (∫ θ in Work.Spaces.Iθ, (Dth1Iter i (SinQ h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α))
            ≤ C0 * ((∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Dth1Iter m (deriv h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) (c : ℝ)
    (hsm : SmoothSlice h) (h0 : h 0 = 0) (hp : h (Real.pi/2) = 0) (i : ℕ) (hi : i ∈ Finset.Icc 1 4) :
    (∫ θ in Work.Spaces.Iθ,
        (Dth1Iter i (SinQ h) θ * (c * (Real.sin (2*θ))^(-(Work.Spaces.gam α/2))))^2)
      ≤ C0 * ((∫ θ in Work.Spaces.Iθ,
            (deriv h θ * (c / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
        + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Dth1Iter m (deriv h) θ * (c * (Real.sin (2*θ))^(-(Work.Spaces.gam α/2))))^2)) := by
  have hγ : Work.Spaces.gam α ≠ 0 := by
    have h1 := Work.Spaces.one_lt_gam hα
    linarith [h1]
  have hsin := dtw_ae_sin_pos
  have hA : (∫ θ in Work.Spaces.Iθ,
        (Dth1Iter i (SinQ h) θ * (c * (Real.sin (2*θ))^(-(Work.Spaces.gam α/2))))^2)
      = ∫ θ in Work.Spaces.Iθ,
          c^2 * ((Dth1Iter i (SinQ h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α)) :=
    integral_congr_ae (hsin.mono (fun θ hθ =>
      dtw_mul_wTheta_sq (Dth1Iter i (SinQ h) θ) c (Real.sin (2*θ)) (Work.Spaces.gam α) hθ hγ))
  have hP : (∫ θ in Work.Spaces.Iθ, (deriv h θ * (c / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
      = ∫ θ in Work.Spaces.Iθ, c^2 * ((deriv h θ)^2 / (Real.sin (2*θ))^(Work.Spaces.eta)) :=
    integral_congr_ae (hsin.mono (fun θ hθ =>
      dtw_mul_div_weight_sq (deriv h θ) c (Real.sin (2*θ)) Work.Spaces.eta hθ))
  have hB : ∀ m ∈ Finset.Icc 1 i,
      (∫ θ in Work.Spaces.Iθ,
          (Dth1Iter m (deriv h) θ * (c * (Real.sin (2*θ))^(-(Work.Spaces.gam α/2))))^2)
        = ∫ θ in Work.Spaces.Iθ,
            c^2 * ((Dth1Iter m (deriv h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α)) :=
    fun m _ => integral_congr_ae (hsin.mono (fun θ hθ =>
      dtw_mul_wTheta_sq (Dth1Iter m (deriv h) θ) c (Real.sin (2*θ)) (Work.Spaces.gam α) hθ hγ))
  rw [hA, integral_const_mul, hP, integral_const_mul,
      Finset.sum_congr rfl (fun m hm => by rw [hB m hm, integral_const_mul])]
  calc c^2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter i (SinQ h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α))
      ≤ c^2 * (C0 * ((∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
          + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
              (Dth1Iter m (deriv h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_left (hIter α hα hα1 h hsm h0 hp i hi) (sq_nonneg c)
    _ = C0 * (c^2 * (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
          + ∑ m ∈ Finset.Icc 1 i,
              c^2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter m (deriv h) θ)^2 / (Real.sin (2*θ))^(Work.Spaces.gam α))) := by
        rw [← Finset.mul_sum]; ring

end Work.Elliptic

namespace Work.Elliptic

/-! ## identification of the slices -/

/-- `D_θ`-iterates at a point only see the `θ`-slice at that `z`. -/
lemma dtw_DthIter_slice_at (f : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i (fun _ θ' => f z θ') z θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ n ih =>
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    congr 1
    have h : (fun θ' => Work.Spaces.DthIter n f z θ')
        = fun θ' => Work.Spaces.DthIter n (fun _ θ' => f z θ') z θ' := by
      funext θ'; exact ih θ'
    rw [h]

lemma dtw_deriv_DzIter_slice (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ) (j : ℕ)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    deriv (fun θ' => Work.Spaces.DzIter j Φ z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ :=
  pth_DzIter Φ hΦ j z θ hz hθ

lemma dtw_DthIter_congr_nbhU {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') Work.Spaces.nbhU) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) Work.Spaces.nbhU := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [Work.Spaces.DthIter_succ] using Work.Spaces.Dth_congr ih

lemma dtw_mixed_div_eq_Dth1Iter (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ)
    (j i : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2*θ)) z θ
      = Dth1Iter i (SinQ (fun θ' => Work.Spaces.DzIter j Φ z θ')) θ := by
  have h1 := DivSinMixedExpansion Φ hΦ j i z θ hz hθ
  have h2 := dtw_DthIter_slice_at (fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2*θ)) i z θ
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2*θ))) z θ = _
  rw [h1, h2]
  exact DivSinSliceIdent (fun θ' => Work.Spaces.DzIter j Φ z θ') i z θ hθ

lemma dtw_Dth1Iter_deriv_eq_mixed (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ)
    (j m : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hpth : Work.Spaces.SmoothNbhd (Work.Spaces.pth Φ) :=
    Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hΦ
  have hfun : (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ')
      = fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ' := by
    funext a θ'; rfl
  calc Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.DthIter m
          (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ :=
        (DthIter_const m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ).symm
    _ = Work.Spaces.DthIter m (fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ') z θ := by
        rw [hfun]
    _ = Work.Spaces.DthIter m (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) z θ :=
        (dtw_DthIter_slice_at (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) m z θ).symm
    _ = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) z θ :=
        dtw_DthIter_congr_nbhU (pth_DzIter_eqOn Φ hΦ j) m hy
    _ = Work.Spaces.DzIter j (Work.Spaces.DthIter m (Work.Spaces.pth Φ)) z θ :=
        Work.Spaces.DthIter_DzIter_comm_eqOn hpth j m hy
    _ = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := rfl

end Work.Elliptic

namespace Work.Elliptic

lemma dtw_smoothSlice_c1 {h : ℝ → ℝ} (hsm : SmoothSlice h) :
    ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi/2)) := by
  have hsub : Set.Icc (0:ℝ) (Real.pi/2) ⊆ Set.Ioo (-1) (Real.pi/2 + 1) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  exact (hsm.mono hsub).of_le le_top

lemma dtw_sin_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

lemma dtw_sin_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2*θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

lemma dtw_integrable_deriv_sq_div_sin (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi/2) = 0) :
    IntegrableOn (fun θ => (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta) Work.Spaces.Iθ := by
  obtain ⟨A, hA0, -, hAb⟩ := contDiffOn_one_bounds (dtw_smoothSlice_c1 hsm) h0 hp
  have hsin : IntegrableOn (fun θ => (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Work.Spaces.eta)
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
  have hmaj : Integrable (fun θ => A^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (volume.restrict Work.Spaces.Iθ) := hsin.const_mul (A^2)
  refine hmaj.mono' ?_ ?_
  · exact (((measurable_deriv h).pow_const 2).div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const
        Work.Spaces.eta)).aestronglyMeasurable
  · filter_upwards [dtw_ae_mem] with θ hθ
    have hs := dtw_sin_pos_of_mem hθ
    have hbθ : ‖deriv h θ‖ ≤ A := hAb θ hθ
    rw [Real.norm_eq_abs] at hbθ
    have hsq : (deriv h θ)^2 ≤ A^2 := by
      rw [sq_le_sq, abs_of_nonneg hA0]
      exact hbθ
    have hval : (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta
        = (deriv h θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hs.le]
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)), hval]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs.le _)

lemma dtw_integrable_h_sq_mul (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi/2) = 0) :
    IntegrableOn (fun θ => (h θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ := by
  obtain ⟨A, hA0, hAb, -⟩ := contDiffOn_one_bounds (dtw_smoothSlice_c1 hsm) h0 hp
  have hsin : IntegrableOn (fun θ => (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Work.Spaces.eta)
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
  have hmaj : Integrable (fun θ => (A*(Real.pi/2))^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (volume.restrict Work.Spaces.Iθ) := hsin.const_mul _
  have hh_aesm : AEStronglyMeasurable h (volume.restrict Work.Spaces.Iθ) :=
    (dtw_smoothSlice_c1 hsm).continuousOn.aestronglyMeasurable measurableSet_Icc
  refine hmaj.mono' ?_ ?_
  · exact ((hh_aesm.pow 2).mul hsin.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hb : |h θ| ≤ A * min θ (Real.pi/2 - θ) := hAb θ hθ
    have hmin : min θ (Real.pi/2 - θ) ≤ Real.pi/2 := by
      rcases le_total θ (Real.pi/2 - θ) with hh | hh
      · rw [min_eq_left hh]; linarith [hθ.2]
      · rw [min_eq_right hh]; linarith [hθ.1]
    have hbound : (h θ)^2 ≤ (A*(Real.pi/2))^2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hA0 (by positivity))]
      calc |h θ| ≤ A * min θ (Real.pi/2 - θ) := hb
        _ ≤ A * (Real.pi/2) := mul_le_mul_of_nonneg_left hmin hA0
    have hsnn : 0 ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) :=
      Real.rpow_nonneg (dtw_sin_nonneg_of_mem hθ) _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
    exact mul_le_mul_of_nonneg_right hbound hsnn

lemma dtw_hardy :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 → h (Real.pi/2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ^2 / (Real.sin (2*θ))^(2 + Work.Spaces.eta))
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta := by
  obtain ⟨C, hCpos, hC⟩ :=
    sharp_hardy_sin_two Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  obtain ⟨K1, hK1pos, hK1⟩ := sin_l2_weight_bound (η := 0) le_rfl zero_lt_one
  refine ⟨1/(Work.Spaces.eta+1)^2 + C*(K1+1) + 1, by positivity, ?_⟩
  intro h hsm h0 hp
  have hc1 := dtw_smoothSlice_c1 hsm
  have hsharp := hC h hc1 h0 hp
  have hInt1 := dtw_integrable_h_sq_mul h hsm h0 hp
  have hInt2 := dtw_integrable_deriv_sq_div_sin h hsm h0 hp
  -- `∫ h² ≤ ∫ h² s^{-η}`
  have hA_le : (∫ θ in Work.Spaces.Iθ, (h θ)^2)
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hInt1 ?_
    filter_upwards [dtw_ae_mem] with θ hθ
    have hs := dtw_sin_pos_of_mem hθ
    have hs1 : (Real.sin (2*θ))^Work.Spaces.eta ≤ 1 :=
      Real.rpow_le_one hs.le (Real.sin_le_one _) Work.Spaces.eta_pos.le
    have hinv : 1 ≤ ((Real.sin (2*θ))^Work.Spaces.eta)⁻¹ :=
      (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr hs1
    rw [Real.rpow_neg hs.le]
    exact le_mul_of_one_le_right (sq_nonneg _) hinv
  -- Poincaré (η = 0)
  have hB : (∫ θ in Work.Spaces.Iθ, (h θ)^2)
      ≤ K1 * ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 := by
    have hh := hK1 h hc1 h0
    rw [Work.Spaces.Iθ]
    simpa using hh
  -- `∫ (h')² ≤ ∫ (h')² / s^η`
  have hX0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (dtw_sin_nonneg_of_mem hθ) _)
  have hC_le : (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hInt2 ?_
    filter_upwards [dtw_ae_mem] with θ hθ
    have hs := dtw_sin_pos_of_mem hθ
    have hs1 : (Real.sin (2*θ))^Work.Spaces.eta ≤ 1 :=
      Real.rpow_le_one hs.le (Real.sin_le_one _) Work.Spaces.eta_pos.le
    have hinv : 1 ≤ ((Real.sin (2*θ))^Work.Spaces.eta)⁻¹ :=
      (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr hs1
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right (sq_nonneg _) hinv
  have hpoin : (∫ θ in Work.Spaces.Iθ, (h θ)^2) ≤ K1 * ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 := hB
  have hB0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  calc (∫ θ in Work.Spaces.Iθ, h θ^2 / (Real.sin (2*θ))^(2 + Work.Spaces.eta))
      ≤ 1/(Work.Spaces.eta+1)^2 * (∫ θ in Work.Spaces.Iθ,
            (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
          + C * ((∫ θ in Work.Spaces.Iθ, (h θ)^2) + ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2) :=
        hsharp
    _ ≤ 1/(Work.Spaces.eta+1)^2 * (∫ θ in Work.Spaces.Iθ,
            (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
          + C * (K1 * (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2)
              + ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2) := by
        have h2 : (∫ θ in Work.Spaces.Iθ, (h θ)^2) + ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2
            ≤ K1 * (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2)
              + ∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 := add_le_add hpoin le_rfl
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 hCpos.le)
    _ = 1/(Work.Spaces.eta+1)^2 * (∫ θ in Work.Spaces.Iθ,
            (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta)
          + C * (K1+1) * (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2) := by ring
    _ ≤ (1/(Work.Spaces.eta+1)^2 + C*(K1+1) + 1) * (∫ θ in Work.Spaces.Iθ,
            (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta) := by
        have h1 : C * (K1+1) * (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2)
            ≤ C * (K1+1) * (∫ θ in Work.Spaces.Iθ,
              (deriv h θ)^2 / (Real.sin (2*θ))^Work.Spaces.eta) :=
          mul_le_mul_of_nonneg_left hC_le (by positivity)
        nlinarith [h1, hX0]

/-- The per-`z` comparison of every summand of the `H^4` integrand of `Φ/sin(2θ)` against
the summands of the `H^4` integrand of `∂_θΦ`, with a constant independent of `α` and of `Φ`.
Outline: the pure-`z` summands reduce by `DivSinFactor` to the weighted Hardy inequality
`DivSinHardy` applied to the slice `θ ↦ DzIter i Φ z θ` (whose `θ`-derivative is
`DzIter i (pth Φ) z θ` by `pth_DzIter`); the mixed summands reduce by `DivSinMixedExpansion`
and `DivSinSliceIdent` to `DivSinIterUnif` applied to the slice `θ ↦ DzIter j Φ z θ`, whose
`m`-th `Dth1` iterate of its derivative is `mixed j m (pth Φ) z θ` by `pth_DzIter` and
`mixed_comm`.  The slices are smooth and vanish at `θ = 0, π/2` by `DivSinSliceFacts`. -/
theorem DivSinTermwise :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (Φ : ℝ → ℝ → ℝ),
      Work.Spaces.SmoothNbhd Φ → Work.Spaces.VanishTheta Φ → ∀ (z : ℝ), z ∈ Work.Spaces.Iz →
      (∀ i ∈ Finset.range 5,
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ∧ (∀ i ∈ Finset.Icc 1 4, ∀ j ∈ Finset.range 5, i + j ≤ 4 →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))) := by
  obtain ⟨K, hKpos, hHardy⟩ := dtw_hardy
  obtain ⟨C0, hC0pos, hIter⟩ := DivSinIterUnif
  refine ⟨max K C0, lt_of_lt_of_le hKpos (le_max_left K C0), ?_⟩
  intro α hα hα1 Φ hΦ hv z hz
  constructor
  · intro i hi
    obtain ⟨hsm, h0, hp⟩ := DivSinSliceFacts Φ hΦ hv i z hz
    have hslice := dtw_SliceHardy hHardy (fun θ => Work.Spaces.DzIter i Φ z θ) (Work.Spaces.w z) hsm h0 hp
    have hL : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i Φ z θ / Real.sin (2*θ)
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [dtw_ae_mem] with θ hθ
      rw [DivSinFactor Φ i z θ hθ]
    have hR : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.Spaces.DzIter i Φ z θ') θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [← dtw_deriv_DzIter_slice Φ hΦ i z θ hz hθ]
    rw [hL, hR]
    exact le_trans hslice (mul_le_mul_of_nonneg_right (le_max_left K C0)
      (integral_nonneg (fun θ => sq_nonneg _)))
  · intro i hi j hj hij
    obtain ⟨hsm, h0, hp⟩ := DivSinSliceFacts Φ hΦ hv j z hz
    have hslice := dtw_SliceIter hIter α hα hα1 (fun θ => Work.Spaces.DzIter j Φ z θ)
      (Work.Spaces.w z) hsm h0 hp i hi
    have hL : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Dth1Iter i (SinQ (fun θ' => Work.Spaces.DzIter j Φ z θ')) θ
              * (Work.Spaces.w z * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α / 2))))^2 := by
      apply integral_congr_ae
      filter_upwards [dtw_ae_mem] with θ hθ
      rw [dtw_mixed_div_eq_Dth1Iter Φ hΦ j i z θ hz hθ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    have hR1 : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.Spaces.DzIter j Φ z θ') θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [← dtw_deriv_DzIter_slice Φ hΦ j z θ hz hθ]
    have hR2 : ∀ m ∈ Finset.Icc 1 i,
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
              * (Work.Spaces.w z * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α / 2))))^2 := by
      intro m hm
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [dtw_Dth1Iter_deriv_eq_mixed Φ hΦ j m z θ hz hθ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [hL, hR1, Finset.sum_congr rfl (fun m hm => hR2 m hm)]
    refine le_trans hslice (mul_le_mul_of_nonneg_right (le_max_right K C0) ?_)
    exact add_nonneg (integral_nonneg (fun θ => sq_nonneg _))
      (Finset.sum_nonneg (fun m _ => integral_nonneg (fun θ => sq_nonneg _)))


end Work.Elliptic
