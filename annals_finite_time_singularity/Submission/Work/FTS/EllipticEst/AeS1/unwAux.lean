import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false

local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## Small facts about the weights -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
  exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- The open interval `(0, π/2)` is conull inside `Iθ`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The measure of the angular interval is finite. -/
theorem volume_Iθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-! ## The level-`0` `H`-integrand and the plain weighted square -/

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem sq_mul_w_sq_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (f z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt h0) (Real.sin_le_one _)
      (by have := Work.Spaces.eta_pos; linarith)
  have hs0 : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos h0 _
  have hw := w_nonneg z
  have hquot : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hs0]
    calc Work.Spaces.w z * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hs1 hw
      _ = Work.Spaces.w z := mul_one _
  rw [HkIntegrand_zero_eq]
  have habs : |f z θ * Work.Spaces.w z|
      ≤ |f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw,
      abs_of_nonneg (div_nonneg hw (le_of_lt hs0))]
    exact mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f z θ * Work.Spaces.w z)) habs 2

/-! ## Almost-everywhere strong measurability of the angular slices -/

theorem aesm_slice_of_continuousOn_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact hg.aestronglyMeasurable measurableSet_Ioo

theorem continuousOn_pz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pz u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pz).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pz u) (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem continuousOn_pth_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pth u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry (Work.Spaces.pth u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pth).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pth u) (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem aesm_slice_gradW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aesm_slice_of_continuousOn_Ioo (continuousOn_pz_slice hu hz)
  exact ((h.const_mul z).mul_const (Work.Spaces.w z)).pow 2

theorem aesm_slice_pthW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aesm_slice_of_continuousOn_Ioo (continuousOn_pth_slice hu hz)
  exact (h.mul_const (Work.Spaces.w z)).pow 2

theorem continuousOn_w_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2) (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

theorem continuousOn_pz_uncurry {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pz).continuousOn

theorem continuousOn_pth_uncurry {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pth).continuousOn

theorem aesm_prod_gradW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((continuousOn_fst.mul (continuousOn_pz_uncurry hu)).mul continuousOn_w_fst).pow 2)

theorem aesm_prod_pthW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((continuousOn_pth_uncurry hu).mul continuousOn_w_fst).pow 2)

/-! ## The per-fibre integrability of the two weighted squares -/

theorem integrableOn_gradW_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hI := (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h).1 z hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2‖
        ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine Filter.Eventually.of_forall fun θ => ?_
      simp only [w_zero, HkIntegrand_zero_eq, mul_zero, zero_mul, zero_div, zero_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, norm_zero, le_refl]
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_mul_w_sq_le_HkIntegrand α (Work.FTS.EllipticEst.H2W.Ae.grad u) hθ
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hzero : (fun θ : ℝ => (0 * Work.Spaces.pz u 0 θ * Work.Spaces.w 0) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ; rw [w_zero]; ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact aesm_slice_gradW_sq h.smooth hzpos
  exact hI.mono' haesm hbound

theorem integrableOn_pthW_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => (Work.Spaces.pth u 0 θ * Work.Spaces.w 0) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ; rw [w_zero]; ring
    rw [hzero]
    exact integrableOn_zero
  · obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hzpos
    have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖(Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2‖ ≤ (C * Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hb : |Work.Spaces.pth u z θ| ≤ C := by
        simpa only [Work.Spaces.pth] using (hC θ hθ).2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
          = (Work.Spaces.pth u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ C ^ 2 * (Work.Spaces.w z) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = (C * Work.Spaces.w z) ^ 2 := by ring
    exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) (C := (C * Work.Spaces.w z) ^ 2) volume_Iθ_ne_top).mono'
      (aesm_slice_pthW_sq h.smooth hzpos) hbound

theorem ae_integrableOn_pth_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(Work.Spaces.pth u z θ) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hb : |Work.Spaces.pth u z θ| ≤ C := by
      simpa only [Work.Spaces.pth] using (hC θ hθ).2
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
    (s := Work.Spaces.Iθ) (C := C ^ 2) volume_Iθ_ne_top).mono'
    ((aesm_slice_of_continuousOn_Ioo (continuousOn_pth_slice h.smooth hz)).pow 2) hbound


theorem continuousOn_u_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall hu).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry u (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem ae_integrableOn_u_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(u z θ) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hb : |u z θ| ≤ C := (hC θ hθ).1
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
    (s := Work.Spaces.Iθ) (C := C ^ 2) volume_Iθ_ne_top).mono'
    ((aesm_slice_of_continuousOn_Ioo (continuousOn_u_slice h.smooth hz)).pow 2) hbound

/-! ## Finiteness of the `∫⁻`-norm from the weighted `H^0`-honesty -/

theorem lintegral_ne_top_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))) ≠ ⊤ := by
  have hkey1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((f z θ * Work.Spaces.w z) ^ 2) := by
    refine lintegral_congr fun z => ?_
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (fun θ => ENNReal.ofReal ((f z θ) ^ 2)) ENNReal.ofReal_ne_top]
    refine lintegral_congr fun θ => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    congr 1
    ring
  have hkey2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f z θ * Work.Spaces.w z) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f z θ) := by
    refine lintegral_mono fun z => ?_
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact ENNReal.ofReal_le_ofReal (sq_mul_w_sq_le_HkIntegrand α f hθ)
  have hkey3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f z θ))
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)).symm
  have hkey4 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf.2
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)).symm
  have hle : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)))
      ≤ ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
    rw [hkey1]
    exact hkey2.trans (hkey3.trans hkey4).le
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Work.FTS.EllipticEst.AeS1
