import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Defs
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HProductRule_Zsummand
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

open Work.Spaces

/-! ## Elementary angular and weight identities -/

/-- `Iθ` is a measurable set (in the folded form used by the set integrals of this file). -/
lemma measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

/-- `Iz` is a measurable set (in the folded form used by the set integrals of this file). -/
lemma measurableSet_Iz : MeasurableSet Iz := measurableSet_Ici

/-- `sin(2θ) ≥ 0` on the closed quadrant. -/
lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(w z / sin(2θ)^{η/2})² = w(z)² · sin(2θ)^{-η}` on the closed quadrant (both sides also
vanish at the two angular endpoints). -/
lemma H_weight_sq (z θ : ℝ) (hθ : θ ∈ Iθ) :
    (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
  have hs := sin_two_nonneg hθ
  have hstep : (Real.sin (2 * θ) ^ (eta / 2)) ^ 2 = Real.sin (2 * θ) ^ eta := by
    rw [pow_two, ← Real.rpow_add' hs (by linarith [eta_pos] : eta / 2 + eta / 2 ≠ 0)]
    congr 1
    ring
  rw [div_pow, hstep, div_eq_mul_inv, ← Real.rpow_neg hs eta]

/-- `(w z · sin(2θ)^{-γ/2})² = w(z)² · sin(2θ)^{-γ}` on the closed quadrant. -/
lemma Wt_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Iθ) :
    (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := sin_two_nonneg hθ
  have hne : (-(gam α / 2)) + (-(gam α / 2)) ≠ 0 := by
    have := gam_pos hα
    intro h
    linarith
  rw [mul_pow, pow_two, pow_two, ← Real.rpow_add' hs hne]
  congr 1
  ring

/-- `(∂_θ u)² sin(2θ)^{2-γ} = (D_θ u)² sin(2θ)^{-γ}` on the closed quadrant. -/
lemma pth_sq_mul_sin_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Iθ) :
    (pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (Dth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := sin_two_nonneg hθ
  have hne : 2 + (-(gam α)) ≠ 0 := by
    have hg1 : gam α ≤ 11 / 10 := by rw [gam]; linarith
    intro h
    linarith
  have hD : Dth u z θ = Real.sin (2 * θ) * pth u z θ := rfl
  rw [hD, mul_pow, show 2 - gam α = 2 + (-(gam α)) by ring, Real.rpow_add' hs hne]
  simp only [mul_assoc, mul_left_comm, mul_comm, Real.rpow_two]

/-- The angular slice `θ ↦ u z θ` of a `SmoothNbhd` function is continuous on `[0, π/2]`. -/
lemma slice_continuousOn {u : ℝ → ℝ → ℝ} (hsm : SmoothNbhd u) {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ => u z θ) Iθ := by
  have hz1 : (-1 : ℝ) < z := by
    have h := hz
    simp only [Iz, Set.mem_Ici] at h
    linarith
  have hU : ContDiffOn ℝ ⊤ (fun t : ℝ => u z t) (Set.Ioo (-1 : ℝ) (π/2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  exact hU.continuousOn.mono
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩)

/-! ## `SmoothNbhd` of the slice subtraction -/

lemma smoothNbhd_zero_slice {u : ℝ → ℝ → ℝ} (h : SmoothNbhd u) :
    SmoothNbhd (fun z θ => u z 0) := by
  have hφ : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) nbhU :=
    contDiffOn_fst.prodMk contDiffOn_const
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) nbhU nbhU := fun p hp =>
    ⟨hp.1, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  have hcomp : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => Function.uncurry u ((fun p : ℝ × ℝ => (p.1, (0 : ℝ))) p)) nbhU :=
    h.comp hφ hmap
  have heq : Function.uncurry (fun z θ => u z 0)
      = fun p : ℝ × ℝ => Function.uncurry u ((fun p : ℝ × ℝ => (p.1, (0 : ℝ))) p) := rfl
  rw [SmoothNbhd, heq]
  exact hcomp

lemma smoothNbhd_slice_zero_sub {u : ℝ → ℝ → ℝ} (h : SmoothNbhd u) :
    SmoothNbhd (fun z θ => u z θ - u z 0) := by
  have hsub : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ =>
      Function.uncurry u p - Function.uncurry (fun z θ => u z 0) p) nbhU :=
    h.sub (smoothNbhd_zero_slice h)
  have heq : Function.uncurry (fun z θ => u z θ - u z 0)
      = fun p : ℝ × ℝ => Function.uncurry u p - Function.uncurry (fun z θ => u z 0) p := rfl
  rw [SmoothNbhd, heq]
  exact hsub

/-! ## The angular Hardy inequality for the oscillation away from `θ = 0` -/

theorem HardyTheta_sub_zero' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd u) (z : ℝ) (hz : 0 ≤ z)
    (hint : IntegrableOn
      (fun θ => (pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) Iθ) :
    ∀ θ ∈ Iθ, (u z θ - u z 0) ^ 2 ≤
      (100 / (gam α - 1)) * ∫ σ in Iθ,
        (pth u z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
  have h0 : (fun z θ => u z θ - u z 0) z 0 = 0 := by simp
  have hsm' : SmoothNbhd (fun z θ => u z θ - u z 0) := smoothNbhd_slice_zero_sub hsm
  have hpth : ∀ σ : ℝ, pth (fun z θ => u z θ - u z 0) z σ = pth u z σ := by
    intro σ
    show deriv (fun θ' => u z θ' - u z 0) σ = deriv (fun θ' => u z θ') σ
    have hfun : (fun θ' => u z θ' - u z 0) = fun θ' => u z θ' + (-(u z 0)) := by
      funext θ'
      ring
    rw [hfun, deriv_add_const]
  have hint' : IntegrableOn
      (fun σ => (pth (fun z θ => u z θ - u z 0) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
    simpa only [hpth] using hint
  intro θ hθ
  have hmain := HardyTheta α hα hα1 (fun z θ => u z θ - u z 0) z hsm' hz h0 hint' θ hθ
  have hint_eq : (∫ σ in Iθ, (pth (fun z θ => u z θ - u z 0) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α))
      = ∫ σ in Iθ, (pth u z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
    setIntegral_congr_fun measurableSet_Iθ (fun σ _ => by rw [hpth σ])
  rw [hint_eq] at hmain
  exact hmain

/-! ## The radial Hardy inequality at almost every angle, `φ`-weighted -/

theorem hardyZ_aeAngle_int (u : ℝ → ℝ → ℝ) (hsm : SmoothNbhd u) (φ : ℝ → ℝ)
    (hφnn : ∀ᵐ θ ∂(volume.restrict Iθ), 0 ≤ φ θ)
    (hdec : ∀ᵐ θ ∂(volume.restrict Iθ), Tendsto (fun z => u z θ) atTop (𝓝 0))
    (hint : ∀ᵐ θ ∂(volume.restrict Iθ),
      IntegrableOn (fun z => (Dz u z θ) ^ 2 * (w z) ^ 2) Iz)
    (hmaj : Integrable (fun θ => φ θ * ∫ z in Iz, (Dz u z θ) ^ 2 * (w z) ^ 2)
      (volume.restrict Iθ)) :
    (∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
          (u z θ) ^ 2 ≤ ∫ z' in Iz, (Dz u z' θ) ^ 2 * (w z') ^ 2)
    ∧ (∀ z ∈ Iz,
        (∫ θ in Iθ, φ θ * (u z θ) ^ 2)
          ≤ ∫ θ in Iθ, φ θ *
              (∫ z' in Iz, (Dz u z' θ) ^ 2 * (w z') ^ 2)) := by
  have hpoint : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      (u z θ) ^ 2 ≤ ∫ z' in Iz, (Dz u z' θ) ^ 2 * (w z') ^ 2 := by
    filter_upwards [hdec, hint, ae_restrict_mem measurableSet_Iθ] with θ hd hi hθmem
    exact HardyZ u θ hsm hθmem hd hi
  refine ⟨hpoint, fun z hz => ?_⟩
  refine integral_mono_of_nonneg ?_ hmaj ?_
  · filter_upwards [hφnn] with θ hφ
    exact mul_nonneg hφ (sq_nonneg _)
  · filter_upwards [hpoint, hφnn] with θ hp hφ
    exact mul_le_mul_of_nonneg_left (hp z hz) hφ

/-! ## `Z = ∫ sin(2θ)^{-η}` is bigger than `1` -/

lemma one_le_Z : 1 ≤ ∫ θ in Iθ, (Real.sin (2 * θ)) ^ (-(eta)) := by
  have haeeq : Set.Ioo (0 : ℝ) (π/2) =ᵐ[volume] Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π/2)) :=
    Measure.restrict_congr_set haeeq.symm
  have hint := (sin_two_rpow (-(eta)) (by linarith [eta_lt_one]) (by linarith [eta_pos])).1
  have hint' : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(eta)))
      (volume.restrict (Set.Ioo (0 : ℝ) (π/2))) := by
    rw [← hIoo]
    exact hint
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (π/2), (1 : ℝ))
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π/2), (Real.sin (2 * θ)) ^ (-(eta)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall (fun θ => zero_le_one)) hint' ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h := Real.rpow_le_rpow_of_nonpos hsin hle1
        (show -(eta) ≤ 0 by linarith [eta_pos])
      simpa [Real.one_rpow] using h)
  have hconst : (∫ θ in Set.Ioo (0 : ℝ) (π/2), (1 : ℝ)) = Real.pi / 2 := by
    have hvol : volume.real (Set.Ioo (0 : ℝ) (π/2)) = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, hvol]
  rw [hIoo]
  calc (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    _ = ∫ θ in Set.Ioo (0 : ℝ) (π/2), (1 : ℝ) := hconst.symm
    _ ≤ ∫ θ in Set.Ioo (0 : ℝ) (π/2), (Real.sin (2 * θ)) ^ (-(eta)) := hmono

/-! ## `VanishTheta` for mixed derivatives with positive `θ`-order -/

lemma VanishTheta_DthIter_of_pos (g : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a g) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * pth (DthIter a' g) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth (DthIter a' g) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

lemma VanishTheta_DzIter {g : ℝ → ℝ → ℝ} (h : VanishTheta g) (n : ℕ) :
    VanishTheta (DzIter n g) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => DzIter m g z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [DzIter_succ, Dz, pz, hfun]
      · intro z
        have hfun : (fun z' => DzIter m g z' (π / 2)) = fun _ => (0 : ℝ) := funext ih.2
        simp [DzIter_succ, Dz, pz, hfun]

lemma VanishTheta_mixed_of_theta_pos (g : ℝ → ℝ → ℝ) (b a : ℕ) (ha : 1 ≤ a) :
    VanishTheta (mixed b a g) := by
  have h1 : VanishTheta (DthIter a g) := VanishTheta_DthIter_of_pos g ha
  simpa [mixed] using VanishTheta_DzIter h1 b

/-! ## The weight identities in integral form -/

/-- The `w`-weighted radial majorant of the pure `D_z` summand, integrated against
`sin(2θ)^{-η}`, is the `θ`-first form of the `H^k`-summand. -/
lemma maj_eq_T1 (i : ℕ) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (-(eta)) *
        ∫ z in Iz, (DzIter i f z θ) ^ 2 * (w z) ^ 2)
      = ∫ θ in Iθ, ∫ z in Iz,
          (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [mul_pow, H_weight_sq z θ hθ]
  ring

/-- The `w`-weighted radial majorant of a mixed summand, integrated against
`sin(2θ)^{-γ}`, is the `θ`-first form of the corresponding `H^4`-summand. -/
lemma maj_eq_T2 (α : ℝ) (hα : 0 < α) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (-(gam α)) *
        ∫ z in Iz, (DzIter (j + 1) (DthIter i f) z θ) ^ 2 * (w z) ^ 2)
      = ∫ θ in Iθ, ∫ z in Iz, (mixed (j + 1) i f z θ * Wt α z θ) ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  simp only [mixed]
  rw [show Wt α z θ = w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)) from rfl, mul_pow,
    Wt_sq α hα z θ hθ]
  ring

/-! ## The `θ`-first forms of the two `H^4`-terms -/

theorem zTermSwap (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hsm : SmoothNbhd f) (hmem : HkMem α k f)
    (i : ℕ) (hi : i ≤ k) :
    (∫ θ in Iθ, ∫ z in Iz,
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
      ≤ HkSq α k f
    ∧ IntegrableOn (fun θ => ∫ z in Iz,
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) Iθ
    ∧ (∀ᵐ θ ∂(volume.restrict Iθ),
        IntegrableOn (fun z => (DzIter i f z θ) ^ 2 * (w z) ^ 2) Iz) := by
  set G : ℝ → ℝ → ℝ := fun z θ =>
    (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 with hG
  have hGnn : ∀ z θ, 0 ≤ G z θ := fun z θ => sq_nonneg _
  have hAE : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := by
    have h := HPRZ.aesm_DzIter_H_weight_prod f hsm i
    have heq : Function.uncurry G = fun p : ℝ × ℝ =>
        (DzIter i f p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2 := rfl
    rw [heq]
    exact h.pow 2
  have hslice : ∀ᵐ z ∂(volume.restrict Iz), Integrable (fun θ => G z θ) (volume.restrict Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    refine Integrable.mono' (hmem.1 z hz) ((HPRZ.aesm_DzIter_H_weight_slice f hsm i hz).pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iθ] with θ _
    rw [Real.norm_of_nonneg (hGnn z θ)]
    exact sq_le_HkIntegrand_z α k f z θ i hi
  have houter : Integrable (fun z => ∫ θ, G z θ ∂(volume.restrict Iθ)) (volume.restrict Iz) := by
    refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => hGnn z θ)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ => hGnn z θ))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Iθ
        (fun θ _ => sq_le_HkIntegrand_z α k f z θ i hi))
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hGnn hAE hslice houter
  have hswap := MeasureTheory.integral_integral_swap hint
  have hL2 : (∫ z in Iz, ∫ θ in Iθ, G z θ) ≤ HkSq α k f := by
    simpa only [L2Sq] using L2Sq_DzIter_le_HkSq α k f hmem i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hswap]
    exact hL2
  · exact hint.integral_prod_right
  · have haeeq : Set.Ioo (0 : ℝ) (π/2) =ᵐ[volume] Iθ := MeasureTheory.Ioo_ae_eq_Icc
    have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π/2)) :=
      Measure.restrict_congr_set haeeq.symm
    rw [hIoo] at hint ⊢
    filter_upwards [hint.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with θ hsliceθ hθmem
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθmem.1, le_of_lt hθmem.2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθmem.1]) (by linarith [hθmem.2, Real.pi_pos])
    have hmul : (Real.sin (2 * θ)) ^ eta * (Real.sin (2 * θ)) ^ (-(eta)) = 1 := by
      rw [← Real.rpow_add hsin, show eta + -(eta) = 0 by ring, Real.rpow_zero]
    have hEq : (fun z => (DzIter i f z θ) ^ 2 * (w z) ^ 2)
        = fun z => (Real.sin (2 * θ)) ^ eta * G z θ := by
      funext z
      change (DzIter i f z θ) ^ 2 * (w z) ^ 2
        = (Real.sin (2 * θ)) ^ eta
            * (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      rw [mul_pow, H_weight_sq z θ hθI]
      rw [show (Real.sin (2 * θ)) ^ eta
            * ((DzIter i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))))
          = ((DzIter i f z θ) ^ 2 * (w z) ^ 2)
              * ((Real.sin (2 * θ)) ^ eta * (Real.sin (2 * θ)) ^ (-(eta))) by ring,
        hmul, mul_one]
    rw [hEq]
    exact hsliceθ.const_mul _

theorem mixedTermSwap (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hsm : SmoothNbhd f)
    (hmem : HkMem α 4 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∫ θ in Iθ, ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f
    ∧ IntegrableOn (fun θ => ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) Iθ
    ∧ (∀ᵐ θ ∂(volume.restrict Iθ),
        IntegrableOn (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2) Iz) := by
  set G : ℝ → ℝ → ℝ := fun z θ => (mixed j i f z θ * Wt α z θ) ^ 2 with hG
  obtain ⟨hint, hval⟩ := bt_prod_integrable α f hsm hmem j i hi hij
  have hint' : Integrable (Function.uncurry G)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := hint
  have hswap := MeasureTheory.integral_integral_swap hint'
  have hL2 : (∫ z in Iz, ∫ θ in Iθ, G z θ) ≤ HkSq α 4 f := by
    simpa only [L2Sq] using L2Sq_mixed_le_HkSq α 4 f hmem i j hi hij
  refine ⟨?_, ?_, ?_⟩
  · rw [← hswap]
    exact hL2
  · exact hint'.integral_prod_right
  · have haeeq : Set.Ioo (0 : ℝ) (π/2) =ᵐ[volume] Iθ := MeasureTheory.Ioo_ae_eq_Icc
    have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π/2)) :=
      Measure.restrict_congr_set haeeq.symm
    rw [hIoo] at hint' ⊢
    filter_upwards [hint'.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with θ hsliceθ hθmem
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθmem.1, le_of_lt hθmem.2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθmem.1]) (by linarith [hθmem.2, Real.pi_pos])
    have hmul : (Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α)) = 1 := by
      rw [← Real.rpow_add hsin, show gam α + -(gam α) = 0 by ring, Real.rpow_zero]
    have hEq : (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2)
        = fun z => (Real.sin (2 * θ)) ^ gam α * G z θ := by
      funext z
      change (mixed j i f z θ) ^ 2 * (w z) ^ 2
        = (Real.sin (2 * θ)) ^ gam α * (mixed j i f z θ * Wt α z θ) ^ 2
      rw [show Wt α z θ = w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)) from rfl, mul_pow,
        Wt_sq α hα z θ hθI]
      rw [show (Real.sin (2 * θ)) ^ gam α
            * ((mixed j i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))))
          = ((mixed j i f z θ) ^ 2 * (w z) ^ 2)
              * ((Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α))) by ring,
        hmul, mul_one]
    rw [hEq]
    exact hsliceθ.const_mul _

/-- Elgindi, Corollary `SecondDerivativesBounded` (tex 1094), in the form needed by the
transport estimates: any `D_z`/`D_θ`-derivative of order at most `2` of a function of `ℋ⁴` is
bounded by `C/√(γ-1) |f|_{ℋ⁴}`.

The paper derives this from Lemma `infinity_separated`, which is stated for functions vanishing
on the angular boundary; here we must *not* assume `VanishTheta f` (the velocity coefficient of
`Transport1`/`Transport2` is `U(Φ)/sin 2θ`, which does not vanish at `θ = 0`).  The route that
avoids `VanishTheta` is:

* for `a ≥ 1` (so `mixed b a f` vanishes at `θ = 0`), the angular Hardy inequality
  `sup_θ |u(·,θ)|² ≤ C/(γ-1) ∫_θ (∂_θ u)² sin(2θ)^{2-γ} dθ` together with the *radial* Hardy
  inequality `HardyZ` applied to `∂_θ u` at each fixed `θ` gives
  `supAbs (mixed b a f)² ≤ C/(γ-1) ∫∫ (mixed (b+1) (a+1) f)² W²`, which is an `ℋ⁴`-term (note
  `D_θ^{a+1}D_z^{b+1}f = sin(2θ) ∂_θ(D_z (mixed b a f))` and
  `sin²(2θ) sin(2θ)^{-γ} = sin(2θ)^{2-γ}`, exactly the Hardy weight);
* for `a = 0` one adds the two `θ`-boundary terms: write
  `sup_θ|u(z,θ)|² ≤ 2|u(z,0)|² + 2 sup_θ|u(z,θ) - u(z,0)|²` and bound `|u(z,0)|²` by the
  `θ`-average of `u²` plus the oscillation, then use `HardyZ` on `u` and on `∂_θu`; the
  resulting `∫∫(D_z^{b+1}f)²w²` and `∫∫(mixed 1 (b+1) f)²W²` are again `ℋ⁴`-terms (for
  `b ≤ 2`).  The factor `(γ-1)^{-1}` (rather than `(γ-1)^{-1/2}`) may be weakened to
  `(γ-1)^{-1/2}` at the end using `γ - 1 ≤ 1`. -/
theorem SupMixedLeH4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
    a + b ≤ 2 → Work.Spaces.SmoothNbhd f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.supAbs (Work.Spaces.mixed b a f)
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  refine ⟨100, by norm_num, ?_⟩
  intro α f b a hα hα1 hab hsm hdec hmem
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hcoef : 0 ≤ 100 / Real.sqrt (gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ### Case `a = 0`
    subst ha0
    have hb : b ≤ 2 := by omega
    have hsm_u : SmoothNbhd (DzIter b f) := smoothNbhd_DzIter hsm b
    obtain ⟨hT1le, hT1int, hT1slice⟩ := zTermSwap α 4 f hsm hmem (b + 1) (by omega)
    obtain ⟨hT2le, hT2int, hT2slice⟩ :=
      mixedTermSwap α hα f hsm hmem 1 (b + 1) le_rfl (by omega)
    set T1 : ℝ := ∫ θ in Iθ, ∫ z in Iz,
        (DzIter (b + 1) f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 with hT1def
    set T2 : ℝ := ∫ θ in Iθ, ∫ z in Iz, (mixed (b + 1) 1 f z θ * Wt α z θ) ^ 2 with hT2def
    have hT1le' : T1 ≤ HkSq α 4 f := by rw [hT1def]; exact hT1le
    have hT2le' : T2 ≤ HkSq α 4 f := by rw [hT2def]; exact hT2le
    have hT1nn : 0 ≤ T1 := by
      rw [hT1def]
      exact integral_nonneg fun θ => integral_nonneg fun z => sq_nonneg _
    have hT2nn : 0 ≤ T2 := by
      rw [hT2def]
      exact integral_nonneg fun θ => integral_nonneg fun z => sq_nonneg _
    -- the angular integrability needed by the angular Hardy inequality
    have hint_diff : ∀ z ∈ Iz, IntegrableOn
        (fun σ => (pth (DzIter b f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
      intro z hz
      have h2gam : 0 < 2 - gam α := by rw [gam]; linarith
      have hcont : ContinuousOn
          (fun σ => (pth (DzIter b f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
        have h1 : ContinuousOn (fun σ => pth (DzIter b f) z σ) Iθ :=
          (pth_integral (DzIter b f) z hsm_u hz (π / 2) pi_half_mem_Iθ).2
        have h2 : ContinuousOn (fun σ => (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
            (fun σ _ => Or.inr h2gam.le)
        exact (h1.pow 2).mul h2
      exact hcont.integrableOn_compact isCompact_Icc
    -- the two Hardy applications at a.e. angle
    have hφnn1 : ∀ᵐ σ ∂(volume.restrict Iθ), 0 ≤ (Real.sin (2 * σ)) ^ (-(eta)) :=
      ae_restrict_of_forall_mem measurableSet_Iθ
        (fun σ hσ => Real.rpow_nonneg (sin_two_nonneg hσ) _)
    have hφnn2 : ∀ᵐ σ ∂(volume.restrict Iθ), 0 ≤ (Real.sin (2 * σ)) ^ (-(gam α)) :=
      ae_restrict_of_forall_mem measurableSet_Iθ
        (fun σ hσ => Real.rpow_nonneg (sin_two_nonneg hσ) _)
    have hdec1 : ∀ᵐ σ ∂(volume.restrict Iθ), Tendsto (fun z' => DzIter b f z' σ) atTop (𝓝 0) :=
      ae_restrict_of_forall_mem measurableSet_Iθ
        (fun σ hσ => hdec.2 0 b (by omega) σ hσ)
    have hdec2 : ∀ᵐ σ ∂(volume.restrict Iθ), Tendsto (fun z' => mixed b 1 f z' σ) atTop (𝓝 0) :=
      ae_restrict_of_forall_mem measurableSet_Iθ
        (fun σ hσ => hdec.2 1 b (by omega) σ hσ)
    have hmaj1 : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(eta)) *
        ∫ z' in Iz, (DzIter (b + 1) f z' σ) ^ 2 * (w z') ^ 2) (volume.restrict Iθ) :=
      hT1int.congr_fun (fun σ hσ => by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ici (fun z' _ => ?_)
        rw [mul_pow, H_weight_sq z' σ hσ]
        ring) measurableSet_Iθ
    have hmaj2 : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) *
        ∫ z' in Iz, (DzIter (b + 1) (DthIter 1 f) z' σ) ^ 2 * (w z') ^ 2) (volume.restrict Iθ) :=
      hT2int.congr_fun (fun σ hσ => by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ici (fun z' _ => ?_)
        simp only [mixed]
        rw [show Wt α z' σ = w z' * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
          Wt_sq α hα z' σ hσ]
        ring) measurableSet_Iθ
    obtain ⟨hpt1, hInt1⟩ := hardyZ_aeAngle_int (DzIter b f) hsm_u
      (fun σ => (Real.sin (2 * σ)) ^ (-(eta))) hφnn1 hdec1 hT1slice hmaj1
    obtain ⟨hpt2, hInt2⟩ := hardyZ_aeAngle_int (mixed b 1 f) (smoothNbhd_mixed hsm b 1)
      (fun σ => (Real.sin (2 * σ)) ^ (-(gam α))) hφnn2 hdec2 hT2slice hmaj2
    -- bound of the angular `∂_θ`-integral by `T2`
    have hA_le : ∀ z ∈ Iz, (∫ σ in Iθ, (pth (DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α)) ≤ T2 := by
      intro z hz
      have hstep1 : (∫ σ in Iθ, (pth (DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - gam α))
          = ∫ σ in Iθ, (Dth (DzIter b f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) :=
        setIntegral_congr_fun measurableSet_Iθ
          (fun σ hσ => pth_sq_mul_sin_eq α hα hα1 (DzIter b f) z σ hσ)
      have hstep2 : (∫ σ in Iθ, (Dth (DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(gam α)))
          = ∫ σ in Iθ, (mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) := by
        refine setIntegral_congr_fun measurableSet_Iθ (fun σ hσ => ?_)
        have hc := Dth_DzIter_comm_eqOn hsm b (mem_nbhU hz hσ)
        have hc' : Dth (DzIter b f) z σ = DzIter b (Dth f) z σ := by
          simpa only [Function.uncurry] using hc
        have hc'' : DzIter b (Dth f) z σ = mixed b 1 f z σ := rfl
        rw [hc', hc'']
      have hstep3 : (∫ σ in Iθ, (mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)))
          = ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * (mixed b 1 f z σ) ^ 2 :=
        setIntegral_congr_fun measurableSet_Iθ (fun σ _ => by
          simp only [mul_left_comm, mul_comm])
      rw [hstep1, hstep2, hstep3]
      refine le_trans (hInt2 z hz) ?_
      rw [hT2def]
      exact le_of_eq (maj_eq_T2 α hα b 1 f)
    -- bound of the `θ`-average by `T1`
    have hB_le : ∀ z ∈ Iz, (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta))
        * (DzIter b f z σ) ^ 2) ≤ T1 := by
      intro z hz
      refine le_trans (hInt1 z hz) ?_
      rw [hT1def]
      exact le_of_eq (maj_eq_T1 (b + 1) f)
    -- ### the pointwise bound on the sup-norm
    have key : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
        (DzIter b f z θ) ^ 2 ≤ (2400 / (gam α - 1)) * HkSq α 4 f := by
      intro z hz θ hθ
      -- oscillation term
      have hosc : (DzIter b f z θ - DzIter b f z 0) ^ 2 ≤ (100 / (gam α - 1)) * T2 := by
        have hHT := HardyTheta_sub_zero' α hα hα1 (DzIter b f) hsm_u z hz (hint_diff z hz) θ hθ
        exact le_trans hHT (mul_le_mul_of_nonneg_left (hA_le z hz) (by positivity))
      -- the boundary value `u(z,0)`, through the θ-average
      have hmean : (DzIter b f z 0) ^ 2 ≤ 2 * T1 + (200 / (gam α - 1)) * T2 := by
        set A : ℝ := ∫ σ in Iθ, (pth (DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
        set Z : ℝ := ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta)) with hZdef
        have hZ1 : 1 ≤ Z := one_le_Z
        have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
        have haesm1 : AEStronglyMeasurable
            (fun σ => (Real.sin (2 * σ)) ^ (-(eta)) * (DzIter b f z σ) ^ 2)
            (volume.restrict Iθ) :=
          ((Measurable.pow_const (Real.measurable_sin.comp
              (measurable_const.mul measurable_id)) (-(eta))).aestronglyMeasurable).mul
            (((slice_continuousOn hsm_u hz).pow 2).aestronglyMeasurable measurableSet_Iθ)
        have haesm2 : AEStronglyMeasurable
            (fun σ => (Real.sin (2 * σ)) ^ (-(eta))
              * (DzIter b f z σ - DzIter b f z 0) ^ 2) (volume.restrict Iθ) :=
          ((Measurable.pow_const (Real.measurable_sin.comp
              (measurable_const.mul measurable_id)) (-(eta))).aestronglyMeasurable).mul
            ((((slice_continuousOn hsm_u hz).sub continuousOn_const).pow 2).aestronglyMeasurable
              measurableSet_Iθ)
        have hbase_int : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(eta)))
            (volume.restrict Iθ) :=
          (sin_two_rpow (-(eta)) (by linarith [eta_lt_one]) (by linarith [eta_pos])).1
        have hM1 : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(eta)) * (DzIter b f z σ) ^ 2)
            (volume.restrict Iθ) := by
          refine Integrable.mono' hmaj1 haesm1 ?_
          filter_upwards [hpt1, hφnn1] with σ hp hφ
          rw [Real.norm_of_nonneg (mul_nonneg hφ (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_left (hp z hz) hφ
        have hHTu : ∀ σ ∈ Iθ, (DzIter b f z σ - DzIter b f z 0) ^ 2
            ≤ (100 / (gam α - 1)) * A :=
          fun σ hσ => HardyTheta_sub_zero' α hα hα1 (DzIter b f) hsm_u z hz
            (hint_diff z hz) σ hσ
        have hM2 : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(eta))
              * (DzIter b f z σ - DzIter b f z 0) ^ 2) (volume.restrict Iθ) := by
          refine Integrable.mono' (hbase_int.mul_const ((100 / (gam α - 1)) * A)) haesm2 ?_
          filter_upwards [ae_restrict_of_forall_mem measurableSet_Iθ hHTu, hφnn1] with σ hb hφ
          rw [Real.norm_of_nonneg (mul_nonneg hφ (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_left hb hφ
        -- the mean-value inequality for the θ-average
        have hptave : (fun σ => (DzIter b f z 0) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
            ≤ᵐ[volume.restrict Iθ]
            (fun σ => 2 * ((Real.sin (2 * σ)) ^ (-(eta)) * (DzIter b f z σ) ^ 2)
              + 2 * ((Real.sin (2 * σ)) ^ (-(eta))
                  * (DzIter b f z σ - DzIter b f z 0) ^ 2)) := by
          refine ae_restrict_of_forall_mem measurableSet_Iθ (fun σ hσ => ?_)
          show (DzIter b f z 0) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta))
              ≤ 2 * ((Real.sin (2 * σ)) ^ (-(eta)) * (DzIter b f z σ) ^ 2)
                + 2 * ((Real.sin (2 * σ)) ^ (-(eta))
                    * (DzIter b f z σ - DzIter b f z 0) ^ 2)
          have hnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(eta)) := Real.rpow_nonneg (sin_two_nonneg hσ) (-(eta))
          have hbase : (DzIter b f z 0) ^ 2 ≤ 2 * (DzIter b f z σ) ^ 2
              + 2 * (DzIter b f z σ - DzIter b f z 0) ^ 2 := by
            nlinarith [sq_nonneg (DzIter b f z 0 + 2 * (DzIter b f z σ - DzIter b f z 0))]
          nlinarith [hbase, hnn, sq_nonneg (DzIter b f z σ), sq_nonneg (DzIter b f z 0)]
        have h3 : (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta))
              * (DzIter b f z σ - DzIter b f z 0) ^ 2) ≤ ((100 / (gam α - 1)) * A) * Z := by
          have hmono : (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta))
                * (DzIter b f z σ - DzIter b f z 0) ^ 2)
              ≤ ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta)) * ((100 / (gam α - 1)) * A) :=
            integral_mono_of_nonneg
              (ae_restrict_of_forall_mem measurableSet_Iθ
                (fun σ hσ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hσ) (-(eta)))
                  (sq_nonneg (DzIter b f z σ - DzIter b f z 0))))
              (hbase_int.mul_const ((100 / (gam α - 1)) * A))
              (ae_restrict_of_forall_mem measurableSet_Iθ (fun σ hσ =>
                mul_le_mul_of_nonneg_left (hHTu σ hσ)
                  (Real.rpow_nonneg (sin_two_nonneg hσ) (-(eta)))))
          have hval : (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta)) * ((100 / (gam α - 1)) * A))
              = ((100 / (gam α - 1)) * A) * Z := by
            rw [hZdef]
            rw [show (fun σ => (Real.sin (2 * σ)) ^ (-(eta)) * ((100 / (gam α - 1)) * A))
                = fun σ => ((100 / (gam α - 1)) * A) * (Real.sin (2 * σ)) ^ (-(eta)) from
              funext fun σ => by ring, integral_const_mul]
          rw [hval] at hmono
          exact hmono
        have hIntave : (∫ σ in Iθ, (DzIter b f z 0) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
            ≤ 2 * (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta)) * (DzIter b f z σ) ^ 2)
              + 2 * (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(eta))
                  * (DzIter b f z σ - DzIter b f z 0) ^ 2) := by
          have h1 := integral_mono_of_nonneg
            (ae_restrict_of_forall_mem measurableSet_Iθ
              (fun σ hσ => mul_nonneg (sq_nonneg (DzIter b f z 0))
                (Real.rpow_nonneg (sin_two_nonneg hσ) (-(eta)))))
            ((hM1.const_mul 2).add (hM2.const_mul 2)) hptave
          simp only [Pi.add_apply] at h1
          rw [integral_add (hM1.const_mul 2) (hM2.const_mul 2)] at h1
          simpa only [integral_const_mul] using h1
        have hone : (∫ σ in Iθ, (DzIter b f z 0) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
            = (DzIter b f z 0) ^ 2 * Z := by
          rw [hZdef, integral_const_mul]
        have hmain : (DzIter b f z 0) ^ 2 * Z
            ≤ 2 * T1 + 2 * (((100 / (gam α - 1)) * T2) * Z) := by
          have hAT : 2 * (((100 / (gam α - 1)) * A) * Z)
              ≤ 2 * (((100 / (gam α - 1)) * T2) * Z) := by
            have hAZ : ((100 / (gam α - 1)) * A) * Z ≤ ((100 / (gam α - 1)) * T2) * Z :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hA_le z hz) (by positivity)) (le_of_lt hZpos)
            linarith
          rw [← hone]
          linarith [hIntave, hB_le z hz, h3, hAT]
        have hdiv : (DzIter b f z 0) ^ 2
            ≤ (2 * T1 + 2 * (((100 / (gam α - 1)) * T2) * Z)) / Z := by
          rw [le_div_iff₀ hZpos]
          exact hmain
        have hX : (2 * T1 + 2 * (((100 / (gam α - 1)) * T2) * Z)) / Z
            = 2 * T1 / Z + (200 / (gam α - 1)) * T2 := by
          field_simp
          ring
        rw [hX] at hdiv
        have h2T1Z : 2 * T1 / Z ≤ 2 * T1 := by
          rw [div_le_iff₀ hZpos]
          nlinarith [hZ1, hT1nn]
        linarith [hdiv, h2T1Z]
      -- ### conclusion of the pointwise bound
      have hsqθ : (DzIter b f z θ) ^ 2 ≤ 2 * (DzIter b f z 0) ^ 2
          + 2 * (DzIter b f z θ - DzIter b f z 0) ^ 2 := by
        nlinarith [sq_nonneg (DzIter b f z 0 - (DzIter b f z θ - DzIter b f z 0))]
      have hmean'' : ((DzIter b f z 0) ^ 2) * (gam α - 1) ≤ 2 * T1 * (gam α - 1) + 200 * T2 := by
        have h := mul_le_mul_of_nonneg_right hmean hγ1.le
        rw [show (2 * T1 + (200 / (gam α - 1)) * T2) * (gam α - 1)
            = 2 * T1 * (gam α - 1) + 200 * T2 by
          field_simp] at h
        exact h
      have hosc'' : ((DzIter b f z θ - DzIter b f z 0) ^ 2) * (gam α - 1) ≤ 100 * T2 := by
        have h := mul_le_mul_of_nonneg_right hosc hγ1.le
        rw [show ((100 / (gam α - 1)) * T2) * (gam α - 1) = 100 * T2 by
          field_simp] at h
        exact h
      have hfin : ((DzIter b f z θ) ^ 2) * (gam α - 1) ≤ 2400 * HkSq α 4 f := by
        have h := mul_le_mul_of_nonneg_right hsqθ hγ1.le
        nlinarith [h, hmean'', hosc'', hT1le', hT2le', hT1nn, hT2nn, HkSq_nonneg α 4 f, hγle,
          hγ1.le]
      calc (DzIter b f z θ) ^ 2
          = (((DzIter b f z θ) ^ 2) * (gam α - 1)) / (gam α - 1) := by field_simp
        _ ≤ (2400 * HkSq α 4 f) / (gam α - 1) := div_le_div_of_nonneg_right hfin hγ1.le
        _ = (2400 / (gam α - 1)) * HkSq α 4 f := by ring
    have hsup : supAbs (DzIter b f) ≤ Real.sqrt ((2400 / (gam α - 1)) * HkSq α 4 f) :=
      supAbs_le (fun z hz θ hθ => Real.abs_le_sqrt (key z hz θ hθ))
    have hAle : (2400 / (gam α - 1)) * HkSq α 4 f
        ≤ (100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 4 f := by
      have h1 : (2400 : ℝ) ≤ 100 ^ 2 := by norm_num
      have h3 : 2400 / (gam α - 1) ≤ (100 / Real.sqrt (gam α - 1)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hγ1.le]
        exact div_le_div_of_nonneg_right h1 hγ1.le
      exact mul_le_mul_of_nonneg_right h3 (HkSq_nonneg α 4 f)
    have hsqrt : Real.sqrt ((2400 / (gam α - 1)) * HkSq α 4 f)
        ≤ (100 / Real.sqrt (gam α - 1)) * HkNorm α 4 f := by
      calc Real.sqrt ((2400 / (gam α - 1)) * HkSq α 4 f)
          ≤ Real.sqrt ((100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 4 f) :=
            Real.sqrt_le_sqrt hAle
        _ = (100 / Real.sqrt (gam α - 1)) * Real.sqrt (HkSq α 4 f) := by
            rw [Real.sqrt_mul (sq_nonneg _),
              Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
        _ = (100 / Real.sqrt (gam α - 1)) * HkNorm α 4 f := rfl
    have hthis : supAbs (DzIter b f) ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 4 f :=
      le_trans hsup hsqrt
    simpa only [mixed_zero_right] using hthis
  · -- ### Case `a ≥ 1`: `mixed b a f` vanishes on the angular boundary
    have hsm' : SmoothNbhd (mixed b a f) := smoothNbhd_mixed hsm b a
    have hvt' : VanishTheta (mixed b a f) := VanishTheta_mixed_of_theta_pos f b a hapos
    have hdec' : ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a f z θ) atTop (𝓝 0) :=
      fun θ hθ => hdec.2 a b (by omega) θ hθ
    have hmem' : HkMem α 2 (mixed b a f) := HkMem_mixed_le α hα hα1 f hsm hmem b a hab
    have h1 := Linf_H2_of_decay α hα hα1 (mixed b a f) hsm' hvt' hdec' hmem'
    have h2 : HkNorm α 2 (mixed b a f) ≤ HkNorm α 4 f := by
      rw [HkNorm, HkNorm]
      exact Real.sqrt_le_sqrt (HkSq_mixed_le α hα hα1 f hsm hmem b a hab)
    calc supAbs (mixed b a f)
        ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 2 (mixed b a f) := h1
      _ ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 4 f :=
          mul_le_mul_of_nonneg_left h2 hcoef

end Work.FTS.H2
