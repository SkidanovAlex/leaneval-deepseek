/-
# `ZmollTTB1` — differentiation under the logarithmic mollification, the slice bundle and the
folded integrals.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTAux1
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c

/-! ## Differentiation under the logarithmic mollification -/

/-- **Differentiation under the logarithmic mollification.** -/
theorem conv_t_step (J J' : ℝ → ℝ → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cj : ℝ → ℝ} (hCj : LocallyIntegrable Cj volume) {σ : ℝ}
    (hJmem : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => J x t) volume)
    (hJ'mem : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => J' x t) volume)
    (hJint : ∀ x : ℝ, ∀ p q : ℝ, IntegrableOn (fun t : ℝ => J x t) (Set.Icc p q))
    (hJdiff : ∀ t x : ℝ, HasDerivAt (fun x' : ℝ => J x' t) (J' x t) x)
    (hJbound : ∀ x t : ℝ, ‖J' x t‖ ≤ Cj t)
    (θ : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ t : ℝ, sKer δ (σ - t) * J x t)
      (∫ t : ℝ, sKer δ (σ - t) * J' θ t) θ := by
  have hKδ0 : (0 : ℝ) ≤ (δ * sMass)⁻¹ := by
    have := sMass_pos; positivity
  have hKδ : ∀ x : ℝ, |sKer δ x| ≤ (δ * sMass)⁻¹ := fun x => by
    rw [abs_of_nonneg (sKer_nonneg hδ0 x)]
    exact Work.FTS.EllSol.K5cAux.sKer_le_inv hδ0 x
  have hkercont : Continuous (fun t : ℝ => sKer δ (σ - t)) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 0)).continuous.comp
      (continuous_const.sub continuous_id)
  have hvan : ∀ x : ℝ, δ < |x| → sKer δ x = 0 :=
    fun x hx => sKer_eq_zero_of_le_abs hδ0 (le_of_lt hx)
  set a : ℝ := σ - 1 with ha
  set b : ℝ := σ + 1 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have haσ : a ≤ σ - δ := by rw [ha]; linarith
  have hbσ : σ + δ ≤ b := by rw [hb]; linarith
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable
      (fun t : ℝ => sKer δ (σ - t) * J x t) (volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun x => (hkercont.aestronglyMeasurable.mul (hJmem x)).restrict
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => sKer δ (σ - t) * J' θ t)
      (volume.restrict (Set.uIoc a b)) :=
    (hkercont.aestronglyMeasurable.mul (hJ'mem θ)).restrict
  have hF_int : IntervalIntegrable (fun t : ℝ => sKer δ (σ - t) * J θ t) volume a b := by
    have h1 : IntegrableOn (fun t : ℝ => J θ t * sKer δ (σ - t)) (Set.Icc a b) :=
      (hJint θ a b).mul_continuousOn hkercont.continuousOn isCompact_Icc
    have h2 : IntegrableOn (fun t : ℝ => sKer δ (σ - t) * J θ t) (Set.Icc a b) :=
      h1.congr_fun (fun t _ => mul_comm _ _) measurableSet_Icc
    exact intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc hab h2)
  have hbound_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      ‖sKer δ (σ - t) * J' x t‖ ≤ (δ * sMass)⁻¹ * Cj t := by
    refine Filter.Eventually.of_forall fun t _ x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |sKer δ (σ - t)| ≤ (δ * sMass)⁻¹ := hKδ _
    have h2 : |J' x t| ≤ Cj t := by
      simpa only [Real.norm_eq_abs] using hJbound x t
    exact mul_le_mul h1 h2 (abs_nonneg _) hKδ0
  have hCj_int : IntervalIntegrable (fun t : ℝ => (δ * sMass)⁻¹ * Cj t) volume a b := by
    have h1 : IntegrableOn (fun t : ℝ => Cj t) (Set.Icc a b) :=
      hCj.integrableOn_isCompact isCompact_Icc
    exact intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc hab (h1.const_mul _))
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => sKer δ (σ - t) * J y t) (sKer δ (σ - t) * J' x t) x :=
    Filter.Eventually.of_forall fun t _ x _ => (hJdiff t x).const_mul _
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (bound := fun t : ℝ => (δ * sMass)⁻¹ * Cj t)
    (F := fun x t : ℝ => sKer δ (σ - t) * J x t)
    (F' := fun x t : ℝ => sKer δ (σ - t) * J' x t)
    (x₀ := θ) (s := Set.univ) Filter.univ_mem hF_meas hF_int hF'_meas hbound_ae hCj_int hdiff
  have hleft : (fun x : ℝ => ∫ t in a..b, sKer δ (σ - t) * J x t)
      = fun x : ℝ => ∫ t : ℝ, sKer δ (σ - t) * J x t :=
    funext fun x => (full_eq_interval_zmoll (sKer δ) (fun t => J x t) (le_of_lt hδ0) hvan haσ hbσ).symm
  have hright : (∫ t in a..b, sKer δ (σ - t) * J' θ t)
      = ∫ t : ℝ, sKer δ (σ - t) * J' θ t :=
    (full_eq_interval_zmoll (sKer δ) (fun t => J' θ t) (le_of_lt hδ0) hvan haσ hbσ).symm
  rw [hleft, hright] at hmain
  exact hmain

/-! ## The slice data supplied by `TraceClass` -/

structure SliceData (G : ℝ → ℝ → ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen G
  val0 : ∀ w : ℝ, G w 0 = 0
  valpi : ∀ w : ℝ, G w (Real.pi / 2) = 0
  tr0 : ∀ w : ℝ, 0 < w → Tendsto (fun s : ℝ => G w s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0)
  trpi : ∀ w : ℝ, 0 < w →
    Tendsto (fun s : ℝ => G w s) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0)
  cont : ∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => G w s) Iθ
  deriv_bdd : ∀ w : ℝ, 0 < w → ∃ M : ℝ, 0 ≤ M ∧
    ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun s' : ℝ => G w s') s| ≤ M
  deriv2_int : ∀ w : ℝ, 0 < w →
    IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s) Iθ
  deriv2_weighted : ∀ w : ℝ, 0 < w →
    IntegrableOn (fun s : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) s) ^ 2
      * Work.FTS.EllipticEst.thEta s) Iθ

theorem slice_hasDerivAt (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w s : ℝ} (hw : 0 < w) (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s' : ℝ => G w s') (deriv (fun s' : ℝ => G w s') s) s := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => G w θ)
      (Set.Ioo 0 (Real.pi / 2)) := hsm.curry_θ hw
  exact ((h.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt

theorem slice_hasDerivAt2 (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w s : ℝ} (hw : 0 < w) (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s' : ℝ => deriv (fun s'' : ℝ => G w s'') s')
      (deriv (deriv (fun s'' : ℝ => G w s'')) s) s := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.pth G w θ)
      (Set.Ioo 0 (Real.pi / 2)) := hsm.pth.curry_θ hw
  have h2 := ((h.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  simpa only [Work.Spaces.pth] using h2

theorem aesm_slice_deriv (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w : ℝ} (hw : 0 < w) :
    AEStronglyMeasurable (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (volume.restrict Iθ) := by
  have h : ContinuousOn (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.pth] using (hsm.pth.curry_θ hw).continuousOn
  have h2 := h.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [← Work.FTS.EllSol.EllPkgAux.restrict_Iθ_eq_restrict_Ioo] at h2

/-! ## The three folded integrals -/

def JA (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, km ε x s * G (Real.exp t) s

def JB (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, kmθ ε x s * G (Real.exp t) s

def JC (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, kmθθ ε x s * G (Real.exp t) s

theorem aesm_JA (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JA G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => km ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_km ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => km ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

theorem aesm_JB (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JB G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => kmθ ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_kmθ ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => kmθ ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

theorem aesm_JC (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JC G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => kmθθ ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_kmθθ ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => kmθθ ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

/-! ## Bounds for the folded integrals -/

/-- The slice functional `t ↦ ∫_{Iθ} |G (eᵗ) s| ds`. -/
def SNg (G : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Iθ, |G (Real.exp t) s|

/-- A kernel bounded by `C` gives a folded integral bounded by `C · SNg`. -/
theorem abs_fold_le (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x s : ℝ, |K x s| ≤ C) (x t : ℝ) :
    |∫ s in Iθ, K x s * G (Real.exp t) s| ≤ C * SNg G t := by
  have h1 : |∫ s in Iθ, K x s * G (Real.exp t) s|
      ≤ ∫ s in Iθ, |K x s * G (Real.exp t) s| :=
    MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
      (fun s : ℝ => K x s * G (Real.exp t) s)
  have hint : IntegrableOn (fun s : ℝ => C * |G (Real.exp t) s|) Iθ :=
    ((hsl.cont (Real.exp t) (Real.exp_pos t)).abs.integrableOn_compact isCompact_Icc).const_mul C
  have h2 : (∫ s in Iθ, |K x s * G (Real.exp t) s|)
      ≤ ∫ s in Iθ, C * |G (Real.exp t) s| := by
    refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hint ?_
    exact Filter.Eventually.of_forall fun s => by
      show |K x s * G (Real.exp t) s| ≤ C * |G (Real.exp t) s|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x s) (abs_nonneg _)
  calc |∫ s in Iθ, K x s * G (Real.exp t) s|
      ≤ ∫ s in Iθ, |K x s * G (Real.exp t) s| := h1
    _ ≤ ∫ s in Iθ, C * |G (Real.exp t) s| := h2
    _ = C * SNg G t := by rw [SNg]; exact MeasureTheory.integral_const_mul _ _

/-- Integrability of the slice functional `∫_{Iθ} KJ ε θ s |∂_θ²G (eᵗ) s| ds`. -/
theorem integrableOn_KJ_pth2 (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {ε : ℝ} (hε0 : 0 < ε)
    (θ t : ℝ) :
    IntegrableOn (fun s : ℝ => KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) Iθ := by
  have hC0 : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ := by have := sMass_pos; positivity
  have hbnd : IntegrableOn
      (fun s : ℝ => (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) Iθ :=
    (hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).abs.const_mul _
  have hQ''aesm : AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) (volume.restrict Iθ) :=
    (hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).aestronglyMeasurable
  have hQ''abs : AEStronglyMeasurable
      (fun s : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) (volume.restrict Iθ) := by
    simpa only [Real.norm_eq_abs] using hQ''aesm.norm
  have hKaesm : AEStronglyMeasurable (fun s : ℝ => KJ ε θ s) (volume.restrict Iθ) :=
    ((continuous_KJ ε).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine Integrable.mono' hbnd (AEStronglyMeasurable.mul hKaesm hQ''abs) ?_
  · exact Filter.Eventually.of_forall fun s => by
      show ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      rw [Real.norm_eq_abs, abs_mul, abs_abs,
        abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
      exact mul_le_mul_of_nonneg_right
        (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) (abs_nonneg _)

/-- The pointwise domination of the inner `s`-integral by the `KJ`-functional. -/
theorem abs_inner_le_KJ (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {ε : ℝ} (hε0 : 0 < ε) (θ t : ℝ) :
    |∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      ≤ ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
  have h1 : |∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      ≤ ∫ s in Iθ, |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| :=
    MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
      (fun s : ℝ => km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)
  have h2 : (∫ s in Iθ, |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
      ≤ ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
    refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (integrableOn_KJ_pth2 G hsl hε0 θ t) ?_
    exact Filter.Eventually.of_forall fun s => by
      show |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
        ≤ KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_km_le_KJ hε0 θ s) (abs_nonneg _)
  linarith [h1, h2]

end Work.FTS.EllSol.EllPkgAux.MollDom
