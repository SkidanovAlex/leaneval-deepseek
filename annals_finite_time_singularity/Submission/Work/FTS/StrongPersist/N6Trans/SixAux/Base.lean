import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Level-6 per-slot `T2` transport bound: base helpers

Helpers for the assembly of `Work.FTS.StrongPersist.N6Trans.slotT2Six`: the product measure
`pm` on the quadrant, the arithmetic conversion of the angular Hardy loss
`(γ-1)^{-1/2} = √10 · α^{-1/2}`, the pointwise AM–GM pairings of `ℋ⁶`-slots, and the two
integral lemmas that convert a pointwise domination into a product-measure bound.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## 0. The product measure `pm` on `Iz × Iθ` -/


/-- The product measure on the quadrant used throughout: the product of the restricted
Lebesgue measures on `Iz` and `Iθ`.  Its product integral of a product-integrable integrand
equals the iterated integral (`MeasureTheory.integral_integral`). -/
abbrev pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-! ## 1. Arithmetic helpers -/

theorem one_div_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h1 : Real.sqrt (α / 10) = Real.sqrt α / Real.sqrt 10 := Real.sqrt_div hα.le 10
  rw [hgam, h1, one_div_div, div_eq_mul_inv]
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_neg hα.le (1 / 2 : ℝ)]

theorem one_le_alpha_rpow_neg_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    1 ≤ α ^ (-(1 / 2 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
  rw [Real.rpow_zero] at h
  exact h

theorem le_alpha_rpow_neg_half_mul {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ α ^ (-(1 / 2 : ℝ)) * x := by
  calc x = 1 * x := by ring
    _ ≤ α ^ (-(1 / 2 : ℝ)) * x :=
        mul_le_mul_of_nonneg_right (one_le_alpha_rpow_neg_half hα hα1) hx

theorem alpha_rpow_neg_half_pos {α : ℝ} (hα : 0 < α) : 0 < α ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos hα _

/-- `canonW 0` is dominated, on the open angular interval, by any `canonW q`, `q > 0`. -/
theorem canonW_zero_le_of_pos {q : ℝ} (hq : 0 < q) {z θ : ℝ} (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    canonW 0 z θ ≤ canonW q z θ := by
  have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
    simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
  rw [h1, canonW]
  exact le_mul_of_one_le_right (sq_nonneg _)
    (Work.FTS.TransportS.one_le_rpow_neg hq.le ⟨hθ, hθ2⟩)

/-- The square of `canonW q`-weighted slot is a summand of the `ℋ⁶`-integrand.  Two such
slots satisfy the pointwise AM–GM bound. -/
theorem slotW6_pair_le {α q : ℝ} {g S₁ S₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (h₁ : SlotW6 α q S₁ g) (h₂ : SlotW6 α q S₂ g) :
    canonW q z θ * |S₁ z θ| * |S₂ z θ| ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hA : canonW q z θ * (S₁ z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    h₁.le z hz θ hθ
  have hB : canonW q z θ * (S₂ z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    h₂.le z hz θ hθ
  have hnn : 0 ≤ canonW q z θ := canonW_nonneg hθ
  have habs : |S₁ z θ| * |S₂ z θ|
      ≤ ((S₁ z θ) ^ 2 + (S₂ z θ) ^ 2) / 2 := by
    rw [← abs_mul]
    exact Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add _ _
  calc canonW q z θ * |S₁ z θ| * |S₂ z θ|
      = canonW q z θ * (|S₁ z θ| * |S₂ z θ|) := by ring
    _ ≤ canonW q z θ * (((S₁ z θ) ^ 2 + (S₂ z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left habs hnn
    _ = (canonW q z θ * (S₁ z θ) ^ 2) / 2 + (canonW q z θ * (S₂ z θ) ^ 2) / 2 := by
        ring
    _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := by linarith

/-! ## 2. Two integral lemmas over `pm` -/

theorem integrable_of_pointwise {α M : ℝ} {F g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 6 g)
    (hM : 0 ≤ M)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) pm)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) pm ∧
      (∫ p, F p.1 p.2 ∂pm) ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, hval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hg hmemg
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) pm :=
    hint.const_mul M
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) pm := by
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      |F p.1 p.2| ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) hpt] with p hp
    simpa only [Real.norm_eq_abs] using hp
  refine ⟨hFint, ?_⟩
  have habs : (∫ p, F p.1 p.2 ∂pm) ≤ ∫ p, |F p.1 p.2| ∂pm :=
    MeasureTheory.integral_mono_ae hFint hFint.abs
      (Filter.Eventually.of_forall fun p => le_abs_self _)
  have hstep : (∫ p, |F p.1 p.2| ∂pm)
      ≤ ∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂pm :=
    MeasureTheory.integral_mono_ae hFint.abs hmaj
      (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        |F p.1 p.2| ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) hpt)
  have hfin : (∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂pm)
      = M * Work.Spaces.HkSq α 6 g := by
    rw [MeasureTheory.integral_const_mul]
    exact congrArg (M * ·) hval
  linarith [habs, hstep, hfin.le, hfin.ge]

theorem integrable_of_pointwise_sqrt {α M : ℝ} {F f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmemf : Work.Spaces.HkMem α 6 f) (hmemg : Work.Spaces.HkMem α 6 g)
    (hM : 0 ≤ M)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) pm)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ))) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) pm ∧
      (∫ p, F p.1 p.2 ∂pm) ≤ M * (Real.sqrt (Work.Spaces.HkSq α 6 f)
        * Real.sqrt (Work.Spaces.HkSq α 6 g)) := by
  obtain ⟨hintf, hvalf⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hf hmemf
  obtain ⟨hintg, hvalg⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hg hmemg
  -- the pointwise majorant `M * (√Hf * √Hg)`
  set Hf : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α 6 f p.1 p.2 with hHf
  set Hg : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α 6 g p.1 p.2 with hHg
  have hHfnn : ∀ p, 0 ≤ Hf p := fun p => Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2
  have hHgnn : ∀ p, 0 ≤ Hg p := fun p => Work.Spaces.HkIntegrand_nonneg α 6 g p.1 p.2
  have hmajnn : ∀ p : ℝ × ℝ,
      0 ≤ Real.sqrt (Hf p) * Real.sqrt (Hg p) :=
    fun p => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Hölder (`p = q = 2`) for the square-root factors
  have hHölder : (∫ p, Real.sqrt (Hf p) * Real.sqrt (Hg p) ∂pm)
      ≤ Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
    have hmeasf : AEStronglyMeasurable Hf pm :=
      Work.FTS.StrongPersist.N6Trans.Hon.aesm_HkIntegrand_prod_open (k := 6) hf
    have hmeasg : AEStronglyMeasurable Hg pm :=
      Work.FTS.StrongPersist.N6Trans.Hon.aesm_HkIntegrand_prod_open (k := 6) hg
    have hLp_f : MeasureTheory.MemLp (fun p : ℝ × ℝ => Real.sqrt (Hf p))
        (ENNReal.ofReal 2) pm := by
      rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from ENNReal.ofReal_ofNat 2]
      rw [MeasureTheory.memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeasf)]
      exact hintf.congr (Filter.Eventually.of_forall fun p => (Real.sq_sqrt (hHfnn p)).symm)
    have hLp_g : MeasureTheory.MemLp (fun p : ℝ × ℝ => Real.sqrt (Hg p))
        (ENNReal.ofReal 2) pm := by
      rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from ENNReal.ofReal_ofNat 2]
      rw [MeasureTheory.memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeasg)]
      exact hintg.congr (Filter.Eventually.of_forall fun p => (Real.sq_sqrt (hHgnn p)).symm)
    have hH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := pm)
      (p := 2) (q := 2) (f := fun p : ℝ × ℝ => Real.sqrt (Hf p))
      (g := fun p : ℝ × ℝ => Real.sqrt (Hg p)) Real.HolderConjugate.two_two hLp_f hLp_g
    have h1 : (∫ p, Real.sqrt (Hf p) * Real.sqrt (Hg p) ∂pm)
        ≤ (∫ p, Real.sqrt (Hf p) ^ (2 : ℝ) ∂pm) ^ (1 / (2 : ℝ))
          * (∫ p, Real.sqrt (Hg p) ^ (2 : ℝ) ∂pm) ^ (1 / (2 : ℝ)) := by
      have h1' := hH
      simpa only [Real.norm_eq_abs, abs_of_nonneg, Real.sqrt_nonneg] using h1'
    have h2 : (∫ p, Real.sqrt (Hf p) ^ (2 : ℝ) ∂pm) = Work.Spaces.HkSq α 6 f := by
      have h2' : (∫ p, Real.sqrt (Hf p) ^ (2 : ℝ) ∂pm) = ∫ p, Hf p ∂pm := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        have : Real.sqrt (Hf p) ^ (2 : ℝ) = Hf p := by
          rw [Real.rpow_two]
          exact Real.sq_sqrt (hHfnn p)
        exact this
      rw [h2', hvalf]
    have h3 : (∫ p, Real.sqrt (Hg p) ^ (2 : ℝ) ∂pm) = Work.Spaces.HkSq α 6 g := by
      have h3' : (∫ p, Real.sqrt (Hg p) ^ (2 : ℝ) ∂pm) = ∫ p, Hg p ∂pm := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        have : Real.sqrt (Hg p) ^ (2 : ℝ) = Hg p := by
          rw [Real.rpow_two]
          exact Real.sq_sqrt (hHgnn p)
        exact this
      rw [h3', hvalg]
    rw [h2, h3] at h1
    have h4 : (Work.Spaces.HkSq α 6 f) ^ (1 / (2 : ℝ))
        = Real.sqrt (Work.Spaces.HkSq α 6 f) := (Real.sqrt_eq_rpow _).symm
    have h5 : (Work.Spaces.HkSq α 6 g) ^ (1 / (2 : ℝ))
        = Real.sqrt (Work.Spaces.HkSq α 6 g) := (Real.sqrt_eq_rpow _).symm
    rw [h4, h5] at h1
    exact h1
  -- integrability
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => M * (Real.sqrt (Hf p) * Real.sqrt (Hg p))) pm := by
    refine MeasureTheory.Integrable.mono'
      ((hintf.add hintg).const_mul (M / 2)) ?_ ?_
    · exact ((Real.continuous_sqrt.comp_aestronglyMeasurable
        (Work.FTS.StrongPersist.N6Trans.Hon.aesm_HkIntegrand_prod_open (k := 6) hf)).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Work.FTS.StrongPersist.N6Trans.Hon.aesm_HkIntegrand_prod_open (k := 6) hg))).const_mul M
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (hmajnn p))]
      have hAB : Real.sqrt (Hf p) * Real.sqrt (Hg p) ≤ (Hf p + Hg p) / 2 := by
        have := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add
          (Real.sqrt (Hf p)) (Real.sqrt (Hg p))
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (hHfnn p), Real.sq_sqrt (hHgnn p)] at this
        exact this
      calc M * (Real.sqrt (Hf p) * Real.sqrt (Hg p))
          ≤ M * ((Hf p + Hg p) / 2) := mul_le_mul_of_nonneg_left hAB hM
        _ = (M / 2) * (Hf p + Hg p) := by ring
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) pm := by
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      |F p.1 p.2| ≤ M * (Real.sqrt (Hf p) * Real.sqrt (Hg p))) hpt] with p hp
    simpa only [Real.norm_eq_abs, hHf, hHg] using hp
  refine ⟨hFint, ?_⟩
  have habs : (∫ p, F p.1 p.2 ∂pm) ≤ ∫ p, |F p.1 p.2| ∂pm :=
    MeasureTheory.integral_mono_ae hFint hFint.abs
      (Filter.Eventually.of_forall fun p => le_abs_self _)
  have hstep : (∫ p, |F p.1 p.2| ∂pm)
      ≤ ∫ p, M * (Real.sqrt (Hf p) * Real.sqrt (Hg p)) ∂pm :=
    MeasureTheory.integral_mono_ae hFint.abs hmaj
      (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        |F p.1 p.2| ≤ M * (Real.sqrt (Hf p) * Real.sqrt (Hg p))) hpt)
  have hfin : (∫ p, M * (Real.sqrt (Hf p) * Real.sqrt (Hg p)) ∂pm)
      = M * (∫ p, Real.sqrt (Hf p) * Real.sqrt (Hg p) ∂pm) := by
    rw [MeasureTheory.integral_const_mul]
  have : (∫ p, M * (Real.sqrt (Hf p) * Real.sqrt (Hg p)) ∂pm)
      ≤ M * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g)) := by
    rw [hfin]
    exact mul_le_mul_of_nonneg_left hHölder hM
  linarith [habs, hstep, this]



/-! ## 3. Measurability and the AM–GM pairings -/

theorem aesm_canonW_abs_mul {q : ℝ} {S₁ S₂ S₃ : ℝ → ℝ → ℝ}
    (h₁ : ContinuousOn (Function.uncurry S₁) Work.FTS.EllipticEst.Q0)
    (h₂ : ContinuousOn (Function.uncurry S₂) Work.FTS.EllipticEst.Q0)
    (h₃ : ContinuousOn (Function.uncurry S₃) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |S₁ p.1 p.2| * |S₂ p.1 p.2| * |S₃ p.1 p.2|) pm := by
  refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
  have hc : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.TransportS.SlotT2.continuousOn_canonW q
  exact ((hc.mul h₁.abs).mul h₂.abs).mul h₃.abs

/-- The cross-slot AM–GM: a `q`-slot of `f` and a `q`-slot of `g` pair to the product of the
square roots of the two integrands. -/
theorem pair_cross_le {α q : ℝ} {f g S₁ S₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (h₁ : SlotW6 α q S₁ f) (h₂ : SlotW6 α q S₂ g) :
    canonW q z θ * |S₁ z θ| * |S₂ z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
  have hc : 0 ≤ canonW q z θ := canonW_nonneg hθ
  calc canonW q z θ * |S₁ z θ| * |S₂ z θ|
      = (Real.sqrt (canonW q z θ) * |S₁ z θ|) * (Real.sqrt (canonW q z θ) * |S₂ z θ|) := by
        rw [show (Real.sqrt (canonW q z θ) * |S₁ z θ|) * (Real.sqrt (canonW q z θ) * |S₂ z θ|)
            = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * (|S₁ z θ| * |S₂ z θ|)
            from by ring, Real.mul_self_sqrt hc]
        ring
    _ = Real.sqrt (canonW q z θ * (S₁ z θ) ^ 2)
          * Real.sqrt (canonW q z θ * (S₂ z θ) ^ 2) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) :=
        mul_le_mul (Real.sqrt_le_sqrt (h₁.le z hz θ hθ))
          (Real.sqrt_le_sqrt (h₂.le z hz θ hθ)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)



/-- The product `canonW q · |A| · |B| · |C|` is nonnegative. -/
theorem canonW_mul_abs3_nonneg {q z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (A B C : ℝ) :
    0 ≤ canonW q z θ * |A| * |B| * |C| :=
  mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg A)) (abs_nonneg B))
    (abs_nonneg C)


end Work.FTS.StrongPersist.N6Trans.SixAux
