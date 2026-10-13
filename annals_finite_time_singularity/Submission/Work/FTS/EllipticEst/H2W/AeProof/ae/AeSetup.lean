import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.ThetaEnergy1Inf
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound
import Submission.Work.FTS.EllipticEst.remov.ibpZ
import Submission.Work.FTS.EllipticEst.remov.ibpZZ
import Submission.Work.FTS.LocData.exists_bound_of_continuous_of_vanishes_off_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeSetup` — the shared measure/weight/integrability toolkit for `devInfOpen`

This module holds the parts of the proof of `Work.FTS.EllipticEst.H2W.AeProof.ae.devInfOpen`
that are *shared* between that theorem and the auxiliary lemmas proved for it in sibling
modules (`ae/AeJointTheta.lean`, `ae/AeJointPz.lean`, `ae/AeSliceIdent.lean`, the chain
lemmas): the product measure `dν` and its identification with the iterated integrals over
`Iz × Iθ`, the elementary weight facts, the `Tonelli` lemma `hkMem_jointIntegrable`, the
bounds on the cutoff `W`, and the four joint-integrability statements of
`jointIntegrable_basic`.
-/

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The product measure `dz dθ` over the open quadrant `(0,∞) × (0,π/2)`.  All the `a.e.`
statements of this file are stated for this measure; `dν_eq` identifies it with the product of
the restricted measures on the closed sets `Iz`, `Iθ` which occur in the statement. -/
def dν : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))

/-- `dν` is the product of the restricted measures over `Iz = [0,∞)` and `Iθ = [0,π/2]`
(the two endpoints are null). -/
theorem dν_eq : dν = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : MeasureTheory.volume.restrict (Set.Ioi 0)
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have h2 : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [dν, h1, h2]

/-- `dν` is the restriction of `volume × volume` to the open quadrant. -/
theorem dν_quad : dν = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  rw [dν, ← MeasureTheory.Measure.prod_restrict]

/-- Almost every point of `dν` lies in the open quadrant. -/
theorem ae_mem_quad : ∀ᵐ p ∂dν, p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := by
  rw [dν_quad]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)

/-! ## Elementary facts about the weights -/

/-- The radial weight satisfies `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The angular weight satisfies `thEta θ ≥ 1` on the open interval. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hpos hle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `thEta` is nonnegative on the angular interval. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The level-`0` integrand is `w²·g²·thEta` on `Iθ`. -/
theorem hkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.thEta, Work.FTS.EllipticEst.sEta]
  ring

/-- **`HkMem` gives joint integrability of the `ℋ⁰`-integrand.**  The slices are integrable for
every `z ∈ Iz` by the first conjunct, so Tonelli applies. -/
theorem hkMem_jointIntegrable {α : ℝ} {g : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α 0 g)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) dν) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) dν := by
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 g p.1 p.2 := fun p =>
    Work.Spaces.HkIntegrand_nonneg α 0 g p.1 p.2
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
    intro z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))).symm
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (Work.Spaces.HkIntegrand α 0 g p.1 p.2)) dν :=
    haesm.aemeasurable.ennreal_ofReal
  have hkey : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂dν)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
    have hprod : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂dν)
        = ∫⁻ z, (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [dν_eq]
      exact MeasureTheory.lintegral_prod _ (by
        simpa only [dν_eq] using haesm.aemeasurable.ennreal_ofReal)
    rw [hprod]
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ))
          = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hm.1 z hz)
        (ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))).symm
    rw [MeasureTheory.lintegral_congr_ae hinner]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hm.2
      (ae_restrict_of_forall_mem measurableSet_Ici (fun z _ =>
        MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)))).symm
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  calc (∫⁻ p, ‖Work.Spaces.HkIntegrand α 0 g p.1 p.2‖ₑ ∂dν)
      = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂dν :=
        MeasureTheory.lintegral_congr_ae
          (by filter_upwards with p; exact Real.enorm_of_nonneg (hnn p))
    _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) := hkey
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The endpoint `0` is the only point of `Iz` where `w` vanishes. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z :=
  lt_of_lt_of_le zero_lt_one (one_le_w hz)

/-! ## Uniform bounds for the cutoff `W` -/

theorem W_zero_of_nonpos {W : ℝ → ℝ} (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∀ z, z ≤ 0 → W z = 0 := by
  intro z hz
  by_contra hne
  exact absurd (hWpos z hne) (not_lt.mpr hz)

theorem W_abs_bdd {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W)
    (hWs : HasCompactSupport W) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |W z| ≤ C := by
  obtain ⟨C, hC⟩ := hWs.exists_bound_of_continuousOn hW.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ tsupport W
  · have h := hC z hz
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have h0 : W z = 0 := by
      by_contra hne
      exact hz (subset_tsupport W hne)
    simp [h0]

theorem W_sq_le_w_sq {W : ℝ → ℝ} {CW : ℝ} (hCW : ∀ z, |W z| ≤ CW) (hCW0 : 0 ≤ CW)
    (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∀ z, (W z) ^ 2 ≤ CW ^ 2 * (Work.Spaces.w z) ^ 2 := by
  intro z
  rcases lt_trichotomy z 0 with h | h | h
  · have h0 : W z = 0 := W_zero_of_nonpos hWpos z h.le
    rw [h0]
    have : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [this]
    exact mul_nonneg (sq_nonneg CW) (sq_nonneg _)
  · subst h
    have h0 : W 0 = 0 := by
      by_contra hne
      exact absurd (hWpos 0 hne) (lt_irrefl 0)
    rw [h0]
    have : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [this]
    exact mul_nonneg (sq_nonneg CW) (sq_nonneg _)
  · have h1 : (W z) ^ 2 ≤ CW ^ 2 := by
      calc (W z) ^ 2 = |W z| ^ 2 := by rw [sq_abs]
        _ ≤ CW ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCW z) 2
    have h2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
      have := one_le_w h
      nlinarith
    calc (W z) ^ 2 ≤ CW ^ 2 := h1
      _ = CW ^ 2 * 1 := by ring
      _ ≤ CW ^ 2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg CW)

/-- A compactly supported function vanishes for large arguments. -/
theorem W_eq_zero_ge {W : ℝ → ℝ} (hWs : HasCompactSupport W) :
    ∃ b : ℝ, ∀ z, b ≤ z → W z = 0 := by
  obtain ⟨b, hb⟩ := hWs.bddAbove
  refine ⟨b + 1, fun z hz => ?_⟩
  by_contra hne
  have h1 : z ≤ b := hb (subset_tsupport W hne)
  linarith

/-! ## Continuity and measurability of the weights -/

theorem continuousOn_thEta_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.continuousOn.rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (x := 2 * θ) (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuous_snd.continuousOn
  exact h1.comp h2 (fun p hp => hp.2)

theorem continuousOn_w_sq_fst :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

/-- Joint continuity on the open quadrant gives a.e. strong measurability for `dν`. -/
theorem aesm_of_continuousOn {f : ℝ × ℝ → ℝ}
    (h : ContinuousOn f (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable f dν := by
  rw [dν_quad]
  exact h.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioo)

/-- The level-`0` `ℋ⁰`-integrand is a.e. strongly measurable for `dν` when the underlying
function is continuous on the open quadrant. -/
theorem aesm_hkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ}
    (h : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2) dν := by
  refine aesm_of_continuousOn ?_
  refine (continuousOn_w_sq_fst.mul ((h.pow 2).mul continuousOn_thEta_snd)).congr ?_
  intro p hp
  exact hkIntegrand_zero α g ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩

/-! ## Cauchy–Schwarz -/

/-- The product of two functions with square-integrable squares is integrable. -/
theorem integrable_mul_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MeasureTheory.Integrable (fun x => (f x) ^ 2) μ)
    (hg : MeasureTheory.Integrable (fun x => (g x) ^ 2) μ)
    (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ) :
    MeasureTheory.Integrable (fun x => f x * g x) μ := by
  have h1 : MeasureTheory.Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf.add hg
  refine MeasureTheory.Integrable.mono' (h1.const_mul (1 / 2))
    ((hfm.mul hgm).aestronglyMeasurable) ?_
  filter_upwards with x
  have h2 : |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := by
    have h := sq_nonneg (|f x| - |g x|)
    rw [sub_sq, sq_abs, sq_abs] at h
    linarith
  rw [Real.norm_eq_abs, abs_mul]
  calc |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := h2
    _ = (1 / 2) * ((f x) ^ 2 + (g x) ^ 2) := by ring

/-- On `Iz × (0,π/2)` the weight `w z ^ 2 * thEta θ` is at least `1`. -/
theorem one_le_w_sq_mul_thEta {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have h2 : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta hθ
  have h3 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [h1]
  have h4 : (0 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := by linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul h3 h2 (by norm_num) (by positivity)

/-- A function vanishing off an interval, with continuous derivative, has bounded derivative. -/
theorem bdd_deriv_of_vanishes_off_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Continuous (deriv g)) (hvan : ∀ z, z ∉ Set.Icc a b → g z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |deriv g z| ≤ C := by
  refine Work.FTS.LocData.exists_bound_of_continuous_of_vanishes_off_Icc hab hg ?_
  intro z hz
  have hmem : (Set.Icc a b)ᶜ ∈ 𝓝 z := isClosed_Icc.isOpen_compl.mem_nhds hz
  have hloc : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [hmem] with y hy
    exact hvan y hy
  rw [hloc.deriv_eq]
  simp

/-- The cutoff `W` vanishes off a compact interval contained in `[0,∞)`. -/
theorem W_vanishes_off {W : ℝ → ℝ} (hWs : HasCompactSupport W)
    (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∃ a b : ℝ, a ≤ b ∧ ∀ z, z ∉ Set.Icc a b → W z = 0 := by
  obtain ⟨b₀, hb₀⟩ := W_eq_zero_ge hWs
  refine ⟨0, max b₀ 0 + 1, by positivity, fun z hz => ?_⟩
  rcases lt_or_ge z 0 with h | h
  · exact W_zero_of_nonpos hWpos z h.le
  · have hz1 : max b₀ 0 + 1 < z := by
      by_contra hcon
      exact hz ⟨h, le_of_not_gt hcon⟩
    exact hb₀ z (by linarith [le_max_left b₀ 0])

/-- The derivative of `z ↦ z W(z)²` is bounded. -/
theorem g2_deriv_bdd {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W)
    (hWs : HasCompactSupport W) (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |deriv (fun z => z * (W z) ^ 2) z| ≤ C := by
  obtain ⟨a, b, hab, hvan⟩ := W_vanishes_off hWs hWpos
  have hsm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ => z * (W z) ^ 2) := by
    fun_prop
  refine bdd_deriv_of_vanishes_off_Icc hab (hsm.continuous_deriv (by norm_num)) ?_
  intro z hz
  simp [hvan z hz]

/-- The second derivative of `z ↦ z² W(z)²` is bounded. -/
theorem g1_dderiv_bdd {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W)
    (hWs : HasCompactSupport W) (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |deriv (deriv (fun z => z ^ 2 * (W z) ^ 2)) z| ≤ C := by
  obtain ⟨a, b, hab, hvan⟩ := W_vanishes_off hWs hWpos
  have hsm : ContDiff ℝ 2 (fun z : ℝ => z ^ 2 * (W z) ^ 2) :=
    ((by fun_prop : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ => z ^ 2 * (W z) ^ 2))).of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv (fun z : ℝ => z ^ 2 * (W z) ^ 2)) := by
    simpa using hsm.iterate_deriv' 1 1
  refine bdd_deriv_of_vanishes_off_Icc hab (hd.continuous_deriv (by norm_num)) ?_
  intro z hz
  have hz0 : (fun y : ℝ => y ^ 2 * (W y) ^ 2) =ᶠ[𝓝 z] 0 := by
    have hmem : (Set.Icc a b)ᶜ ∈ 𝓝 z := isClosed_Icc.isOpen_compl.mem_nhds hz
    filter_upwards [hmem] with y hy
    have hWy : W y = 0 := hvan y hy
    simp [hWy]
  rw [hz0.deriv_eq]
  simp

/-- **Joint integrability of `W²·u²`, `W²·z²∂_z²u·u` and the two weight-derivative terms.** -/
theorem jointIntegrable_basic (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (W : ℝ → ℝ) (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W) (hWs : HasCompactSupport W)
    (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (W p.1) ^ 2 * (u p.1 p.2) ^ 2) dν ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (p.1) ^ 2 * (W p.1) ^ 2 * (Work.Spaces.pzIter 2 u p.1 p.2 * u p.1 p.2)) dν ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      deriv (fun z => z * (W z) ^ 2) p.1 * (u p.1 p.2) ^ 2) dν ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      deriv (deriv (fun z => z ^ 2 * (W z) ^ 2)) p.1 * (u p.1 p.2) ^ 2) dν := by
  obtain ⟨CW, hCW0, hCW⟩ := W_abs_bdd hW hWs
  have hWsq : ∀ z, (W z) ^ 2 ≤ CW ^ 2 * (Work.Spaces.w z) ^ 2 :=
    W_sq_le_w_sq hCW hCW0 hWpos
  have hu := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G hA
  have hrad2 := hA.memRad2
  have hquad : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_all_iff_nat.mpr hA.smooth (⊤ : ℕ∞)
  have hcontu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsmooth.continuousOn
  have hpz2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContDiffOn.mul (contDiffOn_fst.pow 2)
      (Work.FTS.LocData.contDiffOn_pz hquad
        (Work.FTS.LocData.contDiffOn_pz hquad hsmooth))
  have hcontrad2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hpz2.continuousOn
  have hcontW2 : ContinuousOn (fun p : ℝ × ℝ => (W p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hW.continuous.comp continuous_fst).pow 2).continuousOn
  have hcontpz2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.LocData.contDiffOn_pz hquad
      (Work.FTS.LocData.contDiffOn_pz hquad hsmooth)).continuousOn
  have hcontW2rad2 : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 ^ 2 * (W p.1) ^ 2 * (Work.Spaces.pzIter 2 u p.1 p.2 * u p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((continuousOn_fst.pow 2).mul hcontW2).mul hcontpz2).mul hcontu).congr ?_
    intro p hp
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have hg2cont : Continuous (fun z : ℝ => deriv (fun z => z * (W z) ^ 2) z) :=
    ((contDiff_id.mul (hW.pow 2)).continuous_deriv (by norm_num))
  have hg1ddcont : Continuous (fun z : ℝ => deriv (deriv (fun z => z ^ 2 * (W z) ^ 2)) z) := by
    have h1 : ContDiff ℝ 2 (fun z : ℝ => z ^ 2 * (W z) ^ 2) :=
      ((by fun_prop : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ => z ^ 2 * (W z) ^ 2))).of_le (by norm_num)
    have h2 : ContDiff ℝ 1 (deriv (fun z : ℝ => z ^ 2 * (W z) ^ 2)) := by
      simpa using h1.iterate_deriv' 1 1
    exact h2.continuous_deriv (by norm_num)
  have haesm_g2d : AEMeasurable (fun p : ℝ × ℝ =>
      deriv (fun z => z * (W z) ^ 2) p.1) dν :=
    (hg2cont.comp continuous_fst).aemeasurable
  have haesm_g1dd : AEMeasurable (fun p : ℝ × ℝ =>
      deriv (deriv (fun z => z ^ 2 * (W z) ^ 2)) p.1) dν :=
    (hg1ddcont.comp continuous_fst).aemeasurable
  have haesm_u : AEMeasurable (fun p : ℝ × ℝ => u p.1 p.2) dν :=
    (aesm_of_continuousOn hcontu).aemeasurable
  have haesm_u2 : AEMeasurable (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2) dν :=
    (aesm_of_continuousOn (hcontu.pow 2)).aemeasurable
  have hθI_of : ∀ᵐ p ∂dν, p.2 ∈ Work.Spaces.Iθ :=
    ae_mem_quad.mono fun p hp => ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  have hσ_one : ∀ᵐ p ∂dν,
      (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 :=
    ae_mem_quad.mono fun p hp => one_le_w_sq_mul_thEta hp.1 hp.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine MeasureTheory.Integrable.mono'
      ((hkMem_jointIntegrable hu (aesm_hkIntegrand hcontu)).const_mul (CW ^ 2))
      (aesm_of_continuousOn ((hcontW2.mul (hcontu.pow 2)).congr
        (fun p _ => by simp only [Pi.mul_apply, Pi.pow_apply]))) ?_
    filter_upwards [ae_mem_quad, hθI_of, hσ_one] with p hp hθI hσ
    have hσ2 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta p.2 := one_le_thEta hp.2
    have h1 := hWsq p.1
    have hnn : (0 : ℝ) ≤ (u p.1 p.2) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hkIntegrand_zero α u hθI]
    calc (W p.1) ^ 2 * (u p.1 p.2) ^ 2
        ≤ (CW ^ 2 * (Work.Spaces.w p.1) ^ 2) * (u p.1 p.2) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = CW ^ 2 * ((Work.Spaces.w p.1) ^ 2 * (u p.1 p.2) ^ 2) := by ring
      _ ≤ CW ^ 2 * ((Work.Spaces.w p.1) ^ 2 *
            ((u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CW)
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          nlinarith [hσ2, hnn]
  · have hmain := hkMem_jointIntegrable hrad2 (aesm_hkIntegrand hcontrad2)
    have hmainu := hkMem_jointIntegrable hu (aesm_hkIntegrand hcontu)
    have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        CW ^ 2 / 2 * Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
          + CW ^ 2 / 2 * Work.Spaces.HkIntegrand α 0 u p.1 p.2) dν := by
      refine ((hmain.const_mul (CW ^ 2 / 2)).add (hmainu.const_mul (CW ^ 2 / 2))).congr ?_
      filter_upwards with p
      simp only [Pi.add_apply, Pi.mul_apply]
    refine MeasureTheory.Integrable.mono' hdom
      (aesm_of_continuousOn hcontW2rad2) ?_
    filter_upwards [ae_mem_quad, hθI_of, hσ_one] with p hp hθI hσ
    have hσ2 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta p.2 := one_le_thEta hp.2
    have h1 := hWsq p.1
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs]
    have habs1 : |p.1 ^ 2 * (W p.1) ^ 2 * (Work.Spaces.pzIter 2 u p.1 p.2 * u p.1 p.2)|
        = (W p.1) ^ 2
          * (|p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2| * |u p.1 p.2|) := by
      rw [show p.1 ^ 2 * (W p.1) ^ 2 * (Work.Spaces.pzIter 2 u p.1 p.2 * u p.1 p.2)
            = (W p.1) ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2)
              * u p.1 p.2) by ring]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (W p.1) ^ 2)]
    rw [habs1, hkIntegrand_zero α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) hθI,
      hkIntegrand_zero α u hθI]
    set A : ℝ := p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2 with hAdef
    set B : ℝ := u p.1 p.2 with hBdef
    have hAM : |A| * |B| ≤ (A ^ 2 + B ^ 2) / 2 := by
      nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
    calc (W p.1) ^ 2 * (|A| * |B|)
        ≤ (W p.1) ^ 2 * ((A ^ 2 + B ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hAM (sq_nonneg _)
      _ ≤ (CW ^ 2 * (Work.Spaces.w p.1) ^ 2) * ((A ^ 2 + B ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (CW ^ 2 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
            * ((A ^ 2 + B ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [hσ2, hw2]
      _ = (CW ^ 2 / 2) * ((Work.Spaces.w p.1) ^ 2 *
            (A ^ 2 * Work.FTS.EllipticEst.thEta p.2))
          + (CW ^ 2 / 2) * ((Work.Spaces.w p.1) ^ 2
            * (B ^ 2 * Work.FTS.EllipticEst.thEta p.2)) := by ring
  · obtain ⟨C2, hC20, hC2⟩ := g2_deriv_bdd hW hWs hWpos
    refine MeasureTheory.Integrable.mono'
      ((hkMem_jointIntegrable hu (aesm_hkIntegrand hcontu)).const_mul C2)
      ((haesm_g2d.mul haesm_u2).aestronglyMeasurable) ?_
    filter_upwards [ae_mem_quad, hθI_of, hσ_one] with p hp hθI hσ
    have h3 := hC2 p.1
    have hnn : (0 : ℝ) ≤ (u p.1 p.2) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, hkIntegrand_zero α u hθI]
    calc |deriv (fun z => z * (W z) ^ 2) p.1| * (u p.1 p.2) ^ 2
        ≤ C2 * (u p.1 p.2) ^ 2 := mul_le_mul_of_nonneg_right h3 hnn
      _ ≤ C2 * ((Work.Spaces.w p.1) ^ 2 *
            ((u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)) := by
          have hw1 : (1 : ℝ) ≤ Work.Spaces.w p.1 := one_le_w hp.1
          have hσ2 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta p.2 := one_le_thEta hp.2
          refine mul_le_mul_of_nonneg_left ?_ hC20
          nlinarith [hσ2, hw1, hnn, sq_nonneg (Work.Spaces.w p.1)]
  · obtain ⟨C2, hC20, hC2⟩ := g1_dderiv_bdd hW hWs hWpos
    refine MeasureTheory.Integrable.mono'
      ((hkMem_jointIntegrable hu (aesm_hkIntegrand hcontu)).const_mul C2)
      ((haesm_g1dd.mul haesm_u2).aestronglyMeasurable) ?_
    filter_upwards [ae_mem_quad, hθI_of, hσ_one] with p hp hθI hσ
    have h3 := hC2 p.1
    have hnn : (0 : ℝ) ≤ (u p.1 p.2) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, hkIntegrand_zero α u hθI]
    calc |deriv (deriv (fun z => z ^ 2 * (W z) ^ 2)) p.1| * (u p.1 p.2) ^ 2
        ≤ C2 * (u p.1 p.2) ^ 2 := mul_le_mul_of_nonneg_right h3 hnn
      _ ≤ C2 * ((Work.Spaces.w p.1) ^ 2 *
            ((u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)) := by
          have hw1 : (1 : ℝ) ≤ Work.Spaces.w p.1 := one_le_w hp.1
          have hσ2 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta p.2 := one_le_thEta hp.2
          refine mul_le_mul_of_nonneg_left ?_ hC20
          nlinarith [hσ2, hw1, hnn, sq_nonneg (Work.Spaces.w p.1)]

/-- Continuity of `z ↦ W z²` on the open quadrant. -/
theorem continuousOn_Wsq {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W) :
    ContinuousOn (fun p : ℝ × ℝ => (W p.1) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((hW.continuous.comp continuous_fst).pow 2).continuousOn
/-- The derivative of the cutoff is bounded (it is continuous with compact support). -/
theorem W_deriv_bdd {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W)
    (hWs : HasCompactSupport W) (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |deriv W z| ≤ C := by
  obtain ⟨a, b, hab, hvan⟩ := W_vanishes_off hWs hWpos
  exact bdd_deriv_of_vanishes_off_Icc hab (hW.continuous_deriv (by norm_num)) hvan
theorem integrableOn_theta_le (α : ℝ) {g : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  have hw : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := pow_pos (w_pos_of_pos hz) 2
  refine (h.const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  show (Work.Spaces.w z ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
  rw [hkIntegrand_zero α g hθ, inv_mul_cancel_left₀ (ne_of_gt hw)]

/-- A cutoff with `W 0 = 0` grows at most linearly: `|W z| ≤ C|z|`. -/
theorem W_abs_le_mul {W : ℝ → ℝ} (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W)
    (hWs : HasCompactSupport W) (hWpos : ∀ z, W z ≠ 0 → 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |W z| ≤ C * |z| := by
  obtain ⟨C, hC0, hC⟩ := W_deriv_bdd hW hWs hWpos
  have hW0 : W 0 = 0 := by
    by_contra hne
    exact absurd (hWpos 0 hne) (lt_irrefl 0)
  have hdiff : Differentiable ℝ W := hW.differentiable (by simp)
  have hbnd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv W x‖ ≤ C := fun x _ => by
    rw [Real.norm_eq_abs]; exact hC x
  refine ⟨C, hC0, fun z => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => hdiff x) hbnd
    (Set.mem_univ 0) (Set.mem_univ z)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, hW0, sub_zero] at h
  exact h

end

end Work.FTS.EllipticEst.H2W.AeProof.ae
