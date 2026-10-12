import Mathlib
import Submission.Work.BoseSym.MollifyAux.enorm_sub_convC_le
import Submission.Work.BoseSym.MollifyAux.integral_sq_sub_translate_le
import Submission.Work.BoseSym.MollifyAux.sq_lintegral_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Mollify — the mollification error estimate `‖f - ρ ⋆ f‖₂ ≤ δ ‖∇f‖₂`

For a `C¹` compactly supported `f` on configuration space and a nonnegative smooth
compactly supported `ρ` of total mass `1` whose topological support lies in the ball
of radius `δ`, the `L²` norm of the mollification error `f - ρ ⋆ f` is at most
`δ ‖∇f‖₂`.

The proof averages the translation difference over `ρ`:

* `f x - (ρ ⋆ f) x = ∫ y, ρ y * (f x - f (x - y)) dy`;
* Cauchy–Schwarz against the probability density `ρ dy` turns the square of this
  integral into `∫ y, ρ y * (f x - f (x - y))² dy`;
* integrating in `x` and exchanging the order of integration (Tonelli) reduces the
  claim to the `L²` translation bound `∫ x, (f x - f (x - y))² ≤ ‖y‖² ∫ x, ‖fderiv f x‖²`
  and to `∫ y, ρ y ‖y‖² ≤ δ²`, which follows from `∫ ρ = 1` and `tsupport ρ ⊆ ball 0 δ`.

## Main statement

* `Work.BoseSym.Mollify.conv_sub_eLpNorm_le`
-/

namespace Work.BoseSym

open MeasureTheory Filter
open scoped Topology Real ContDiff ENNReal NNReal MeasureTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mollify

/-! ## Auxiliary facts -/

/-- `fderiv` of a function vanishing off a closed set is supported in that set: if
`x ∉ tsupport g` then `g` is zero on a neighbourhood of `x`, hence `fderiv g x = 0`. -/
lemma convSub_support_fderiv_subset_tsupport {N : ℕ} {g : Conf N → ℝ} :
    Function.support (fderiv ℝ g) ⊆ tsupport g := by
  intro x hx
  by_contra hx'
  have hmem : (tsupport g)ᶜ ∈ 𝓝 x := (isClosed_tsupport g).isOpen_compl.mem_nhds hx'
  have heq : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with y hy
    by_contra hy'
    exact hy (subset_tsupport g (Function.mem_support.2 hy'))
  have hz : fderiv ℝ g x = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
  exact hx (by simpa [Function.mem_support] using hz)

/-- `‖fderiv f‖²` is integrable for a `C¹` compactly supported `f`. -/
lemma convSub_integrable_fderiv_sq {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f)
    (hcs : HasCompactSupport f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) (volC N) := by
  have hcont : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) :=
    (hf.continuous_fderiv (by norm_num)).norm.pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine IsCompact.of_isClosed_subset hcs.isCompact (isClosed_tsupport _) ?_
  refine closure_minimal ?_ (isClosed_tsupport f)
  intro x hx
  have hx' : x ∈ Function.support (fderiv ℝ f) := by
    rw [Function.mem_support] at hx ⊢
    intro hzero
    exact hx (by rw [hzero]; norm_num)
  exact convSub_support_fderiv_subset_tsupport hx'

/-- A convenient form of `eLp2`: the square root of the lower integral of the square. -/
lemma convSub_eLp2_eq (N : ℕ) (g : Conf N → ℝ) (hg : AEStronglyMeasurable g (volC N)) :
    eLp2 N g = (∫⁻ x, (‖g x‖ₑ) ^ 2 ∂(volC N)) ^ (1 / 2 : ℝ) := by
  rw [eLp2, eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hg]
  norm_num

/-- A convenient form of `gradNorm`: the square root of the lower integral of
`ofReal (‖fderiv f‖²)`. -/
lemma convSub_gradNorm_eq (N : ℕ) (f : Conf N → ℝ) :
    gradNorm N f
      = (∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N)) ^ (1 / 2 : ℝ) := by
  rw [gradNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
    (measurable_fderiv ℝ f).norm.aestronglyMeasurable]
  norm_num

/-- Integrability of `ρ y * ‖y‖²`. -/
lemma convSub_integrable_rho_mul_norm_sq {N : ℕ} {ρ : Conf N → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) :
    Integrable (fun y => ρ y * ‖y‖ ^ 2) (volC N) := by
  refine (hρc.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport ?_
  exact hρs.mono (fun y hy => by
    rw [Function.mem_support] at hy ⊢
    exact left_ne_zero_of_mul hy)

/-- The weighted integral bound `∫ y, ρ y * ‖y‖² ≤ δ²`. -/
lemma convSub_integral_rho_mul_norm_sq_le {N : ℕ} {ρ : Conf N → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρ1 : intC N ρ = 1) {δ : ℝ}
    (hδ : tsupport ρ ⊆ Metric.ball 0 δ) (hδ0 : 0 < δ) :
    ∫ y, ρ y * ‖y‖ ^ 2 ∂(volC N) ≤ δ ^ 2 := by
  have hpt : ∀ y, ρ y * ‖y‖ ^ 2 ≤ ρ y * δ ^ 2 := by
    intro y
    by_cases hy : y ∈ tsupport ρ
    · refine mul_le_mul_of_nonneg_left ?_ (hρ0 y)
      have h1 : ‖y‖ ≤ δ := by
        have h1' : dist y (0 : Conf N) < δ := by simpa using hδ hy
        rw [dist_zero_right] at h1'
        exact le_of_lt h1'
      have h2 : ‖y‖ ^ 2 ≤ δ ^ 2 := by
        have h3 := mul_self_le_mul_self (norm_nonneg y) h1
        simpa only [pow_two] using h3
      exact h2
    · have hz : ρ y = 0 := by
        by_contra hne
        exact hy (subset_tsupport ρ (Function.mem_support.2 hne))
      simp [hz]
  have hInt1 : Integrable (fun y => ρ y * ‖y‖ ^ 2) (volC N) :=
    convSub_integrable_rho_mul_norm_sq hρc hρs
  have hInt2 : Integrable (fun y => ρ y * δ ^ 2) (volC N) :=
    (hρc.integrable_of_hasCompactSupport hρs).mul_const (δ ^ 2)
  have hmain : ∫ y, ρ y * ‖y‖ ^ 2 ∂(volC N) ≤ ∫ y, ρ y * δ ^ 2 ∂(volC N) :=
    integral_mono_ae hInt1 hInt2 (ae_of_all (volC N) hpt)
  have hρ1' : (∫ y, ρ y ∂(volC N)) = 1 := hρ1
  calc ∫ y, ρ y * ‖y‖ ^ 2 ∂(volC N)
      ≤ ∫ y, ρ y * δ ^ 2 ∂(volC N) := hmain
    _ = (∫ y, ρ y ∂(volC N)) * δ ^ 2 := integral_mul_const (δ ^ 2) _
    _ = δ ^ 2 := by rw [hρ1', one_mul]

/-- The `ℝ≥0∞` form of the weighted integral bound. -/
lemma convSub_lintegral_rho_mul_norm_sq_le {N : ℕ} {ρ : Conf N → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρ1 : intC N ρ = 1) {δ : ℝ}
    (hδ : tsupport ρ ⊆ Metric.ball 0 δ) (hδ0 : 0 < δ) :
    ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖y‖ ^ 2) ∂(volC N)
      ≤ (ENNReal.ofReal δ) ^ 2 := by
  have hInt : Integrable (fun y => ρ y * ‖y‖ ^ 2) (volC N) :=
    convSub_integrable_rho_mul_norm_sq hρc hρs
  have h1 : ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖y‖ ^ 2) ∂(volC N)
      = ∫⁻ y, ENNReal.ofReal (ρ y * ‖y‖ ^ 2) ∂(volC N) :=
    lintegral_congr (fun y => (ENNReal.ofReal_mul (hρ0 y)).symm)
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hInt
        (ae_of_all _ (fun y => mul_nonneg (hρ0 y) (sq_nonneg _))),
    ← ENNReal.ofReal_pow (le_of_lt hδ0) 2]
  exact ENNReal.ofReal_le_ofReal
    (convSub_integral_rho_mul_norm_sq_le hρc hρs hρ0 hρ1 hδ hδ0)

/-! ## The main estimate -/

theorem conv_sub_eLpNorm_le {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f)
    (hcs : HasCompactSupport f) {ρ : Conf N → ℝ} (hρ : Smooth ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρ1 : intC N ρ = 1) {δ : ℝ}
    (hδ : tsupport ρ ⊆ Metric.ball 0 δ) :
    eLp2 N (fun x => f x - convC N f ρ x) ≤ ofRealENN δ * gradNorm N f := by
  have hfcont : Continuous f := hf.continuous
  have hρcont : Continuous ρ := hρ.continuous
  have hρint : Integrable ρ (volC N) := hρcont.integrable_of_hasCompactSupport hρs
  -- `δ` must be positive: otherwise `tsupport ρ = ∅`, so `ρ = 0`, contradicting `∫ ρ = 1`
  have hδpos : 0 < δ := by
    by_contra h
    push Not at h
    have hball : Metric.ball (0 : Conf N) δ = ∅ := Metric.ball_eq_empty.2 h
    have hz : ∀ y, ρ y = 0 := by
      intro y
      by_contra hy
      have hy' : y ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.2 hy)
      have hmem : y ∈ Metric.ball (0 : Conf N) δ := hδ hy'
      rwa [hball] at hmem
    have h0 : intC N ρ = 0 := by
      simp only [intC]
      rw [show (fun x => ρ x) = (0 : Conf N → ℝ) from funext hz]
      simp
    rw [hρ1] at h0
    exact absurd h0 (by norm_num)
  set G : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂(volC N) with hGdef
  -- the lower integral of `ofReal ∘ ρ` is `1`
  have hlintρ : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(volC N) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ hρ0)
    have hρ1' : (∫ y, ρ y ∂(volC N)) = 1 := hρ1
    rw [hρ1'] at h
    simpa using h.symm
  have hkey : ∫⁻ x, (‖f x - convC N f ρ x‖ₑ) ^ 2 ∂(volC N) ≤ (ENNReal.ofReal δ) ^ 2 * G := by
    -- (1) pointwise bound
    have hpt : ∀ x, ‖f x - convC N f ρ x‖ₑ ≤
        ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |f x - f (x - y)| ∂(volC N) :=
      fun x => MollifyAux.enorm_sub_convC_le hfcont hcs hρcont hρs hρ0 hρ1 x
    -- (2) Cauchy–Schwarz against the probability density `ρ`
    have hcs_x : ∀ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |f x - f (x - y)|
          ∂(volC N)) ^ 2
        ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N) := by
      intro x
      refine MollifyAux.sq_lintegral_mul_le (μ := volC N) ?_ ?_ hlintρ
      · exact hρcont.measurable.ennreal_ofReal.aemeasurable
      · exact (((continuous_const : Continuous fun _ : Conf N => f x).sub
          (hfcont.comp (continuous_const.sub continuous_id))).abs.measurable.ennreal_ofReal).aemeasurable
    -- (3) integrate in `x`
    have hsq : ∫⁻ x, (‖f x - convC N f ρ x‖ₑ) ^ 2 ∂(volC N)
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N) := by
      refine lintegral_mono (fun x => ?_)
      have h2 : (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |f x - f (x - y)|
            ∂(volC N)) * (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |f x - f (x - y)|
            ∂(volC N))
          ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N) := by
        simpa only [pow_two] using hcs_x x
      exact (by simpa only [pow_two] using
        (mul_self_le_mul_self zero_le (hpt x)).trans h2)
    -- (4) exchange the order of integration
    have hswap : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N)
        = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N) := by
      have hmeas : Measurable (fun p : Conf N × Conf N =>
          ENNReal.ofReal (ρ p.2) * (ENNReal.ofReal |f p.1 - f (p.1 - p.2)|) ^ 2) :=
        Measurable.mul ((hρcont.measurable.comp measurable_snd).ennreal_ofReal)
          (((((hfcont.measurable.comp measurable_fst).sub
            ((hfcont.measurable.comp (measurable_fst.sub measurable_snd)))).abs).ennreal_ofReal).pow_const 2)
      refine lintegral_lintegral_swap (μ := volC N) (ν := volC N)
        (f := fun x y => ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2) ?_
      show AEMeasurable (fun p : Conf N × Conf N =>
        ENNReal.ofReal (ρ p.2) * (ENNReal.ofReal |f p.1 - f (p.1 - p.2)|) ^ 2)
        ((volC N).prod (volC N))
      exact hmeas.aemeasurable
    -- (5) pull out the weight in the inner integral
    have hpull : ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N)
        = ∫⁻ y, ENNReal.ofReal (ρ y) *
            (∫⁻ x, (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N)) ∂(volC N) := by
      refine lintegral_congr (fun y => ?_)
      refine lintegral_const_mul (ENNReal.ofReal (ρ y)) ?_
      exact (((hfcont.measurable.sub
        (hfcont.measurable.comp (measurable_id.sub measurable_const)))).abs.ennreal_ofReal).pow_const 2
    -- (6) the `L²` translation bound, in lower-integral form
    have htrans : ∀ y, ∫⁻ x, (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N)
        ≤ ENNReal.ofReal (‖y‖ ^ 2) * G := by
      intro y
      have hcontw : Continuous (fun x => (f x - f (x - y)) ^ 2) :=
        ((hfcont.sub (hfcont.comp (continuous_id.sub continuous_const))).pow 2)
      have hcsw : HasCompactSupport (fun x => (f x - f (x - y)) ^ 2) :=
        (hcs.sub (hcs.comp_homeomorph (Homeomorph.subRight y))).comp_left
          (g := fun t : ℝ => t ^ 2) (by norm_num)
      have hIntw : Integrable (fun x => (f x - f (x - y)) ^ 2) (volC N) :=
        hcontw.integrable_of_hasCompactSupport hcsw
      have hIntg : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) (volC N) :=
        convSub_integrable_fderiv_sq hf hcs
      have h1 : ∫⁻ x, (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N)
          = ∫⁻ x, ENNReal.ofReal ((f x - f (x - y)) ^ 2) ∂(volC N) :=
        lintegral_congr (fun x => by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs])
      rw [hGdef, h1, ← ofReal_integral_eq_lintegral_ofReal hIntw (ae_of_all _ (fun x => sq_nonneg _)),
        ← ofReal_integral_eq_lintegral_ofReal hIntg (ae_of_all _ (fun x => sq_nonneg _)),
        ← ENNReal.ofReal_mul (sq_nonneg (‖y‖))]
      exact ENNReal.ofReal_le_ofReal (MollifyAux.integral_sq_sub_translate_le hf hcs y)
    -- (7) assemble
    calc ∫⁻ x, (‖f x - convC N f ρ x‖ₑ) ^ 2 ∂(volC N)
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N) := hsq
      _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ y) * (ENNReal.ofReal |f x - f (x - y)|) ^ 2
            ∂(volC N) ∂(volC N) := hswap
      _ = ∫⁻ y, ENNReal.ofReal (ρ y) *
            (∫⁻ x, (ENNReal.ofReal |f x - f (x - y)|) ^ 2 ∂(volC N)) ∂(volC N) := hpull
      _ ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal (‖y‖ ^ 2) * G) ∂(volC N) := by
        refine lintegral_mono (fun y => ?_)
        exact mul_le_mul_right (htrans y) _
      _ = (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖y‖ ^ 2) ∂(volC N)) * G := by
        calc ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal (‖y‖ ^ 2) * G) ∂(volC N)
            = ∫⁻ y, (ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖y‖ ^ 2)) * G ∂(volC N) :=
              lintegral_congr (fun y => (mul_assoc _ _ _).symm)
          _ = (∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (‖y‖ ^ 2) ∂(volC N)) * G :=
              lintegral_mul_const G
                ((hρcont.measurable.ennreal_ofReal).mul
                  (continuous_norm.pow 2).measurable.ennreal_ofReal)
      _ ≤ (ENNReal.ofReal δ) ^ 2 * G :=
        mul_le_mul_left (convSub_lintegral_rho_mul_norm_sq_le hρcont hρs hρ0 hρ1 hδ hδpos) G
  -- the endgame: extract the square root
  have hconvC : Continuous (convC N f ρ) :=
    hρs.continuous_convolution_right _ hfcont.locallyIntegrable hρcont
  rw [convSub_eLp2_eq N (fun x => f x - convC N f ρ x) (hfcont.sub hconvC).aestronglyMeasurable,
    convSub_gradNorm_eq, ofRealENN]
  have hkey' := hkey
  rw [hGdef] at hkey'
  refine (ENNReal.rpow_le_rpow hkey' (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [← ENNReal.rpow_natCast (ENNReal.ofReal δ) 2, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

end Mollify

end

end Work.BoseSym
