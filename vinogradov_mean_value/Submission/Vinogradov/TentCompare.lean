/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymFine
import Submission.Vinogradov.LocalisedDecoupling
import Submission.Vinogradov.SymFromAsym

/-!
# The tent comparison `|f_J|^{p_l} ∗ Φ_I ≲ |f_J|^{p_l} ∗ Φ_J` of GLYZ Lemma 3.8

... (docstring)
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. Boundedness of a member of the class -/

/-- A member of the Fourier class is bounded. -/
lemma IsFourierRep.exists_bound {k : ℕ} {U : Set (E k)} {F : E k → ℂ}
    (hF : IsFourierRep k U F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖F x‖ ≤ M := by
  obtain ⟨ι, m, Γ, ν, d, hν, hd, hΓ, hdm, hU, hfd⟩ := hF
  letI : MeasurableSpace ι := m
  haveI : IsFiniteMeasure ν := hν
  have hFeq : F = repFun k Γ ν d := funext fun y => (hfd y).trans rfl
  refine ⟨∫ u, ‖d u‖ ∂ν, integral_nonneg fun u => norm_nonneg _, fun x => ?_⟩
  rw [hFeq]; exact norm_repFun_le Γ ν (φ := d) x

/-! ## 2. The convolution: commutativity and associativity -/

/-- **Commutativity of the `ℝ≥0∞`-convolution** (a pure substitution). -/
lemma lintegral_mul_sub_comm {k : ℕ} {Φ₁ Φ₂ : E k → ℝ≥0∞} (x : E k) :
    (∫⁻ y, Φ₁ (x - y) * Φ₂ y) = ∫⁻ y, Φ₂ (x - y) * Φ₁ y := by
  have h : (∫⁻ y, Φ₁ (x - y) * Φ₂ y) = ∫⁻ t, Φ₁ t * Φ₂ (x - t) := by
    rw [← MeasureTheory.lintegral_sub_left_eq_self (fun t : E k => Φ₁ t * Φ₂ (x - t)) x]
    refine lintegral_congr fun y => ?_
    show Φ₁ (x - y) * Φ₂ y = Φ₁ (x - y) * Φ₂ (x - (x - y))
    rw [show x - (x - y) = y from by abel]
  rw [h]
  exact lintegral_congr fun t => mul_comm _ _

/-- **Associativity of the convolution with a power**: for a nonnegative measurable `H` and
measurable weights `Φ₁`, `Φ₂`,

  `(|H| ∗ Φ₁) ∗ Φ₂ = |H| ∗ (Φ₁ ∗ Φ₂)`.

This is Tonelli plus the translation substitution `u ↦ u + w`. -/
lemma lintegral_convPow_assoc {k : ℕ} {Φ₁ Φ₂ : E k → ℝ≥0∞} (hΦ₁ : Measurable Φ₁)
    (hΦ₂ : Measurable Φ₂) {H : E k → ℝ≥0∞} (hH : Measurable H) (x : E k) :
    (∫⁻ u, (∫⁻ w, H (x - u - w) * Φ₂ w) * Φ₁ u)
      = ∫⁻ t, H (x - t) * (∫⁻ w, Φ₁ (t - w) * Φ₂ w) := by
  have hmeas_inner : ∀ u : E k, Measurable (fun w : E k => H (x - u - w) * Φ₂ w) := by
    intro u
    exact (hH.comp (((measurable_const.sub measurable_const).sub measurable_id))).mul hΦ₂
  have step1 : (∫⁻ u, (∫⁻ w, H (x - u - w) * Φ₂ w) * Φ₁ u)
      = ∫⁻ u, ∫⁻ w, H (x - u - w) * Φ₂ w * Φ₁ u := by
    refine lintegral_congr fun u => ?_
    exact (lintegral_mul_const (Φ₁ u) (hmeas_inner u)).symm
  have hswap2 : AEMeasurable (Function.uncurry
      (fun u w : E k => H (x - u - w) * Φ₂ w * Φ₁ u)) (volume.prod volume) := by
    have h : Measurable (fun p : E k × E k => H (x - p.1 - p.2) * Φ₂ p.2 * Φ₁ p.1) :=
      ((hH.comp ((measurable_const.sub measurable_fst).sub measurable_snd)).mul
        (hΦ₂.comp measurable_snd)).mul (hΦ₁.comp measurable_fst)
    exact h.aemeasurable
  have step2 : (∫⁻ u, ∫⁻ w, H (x - u - w) * Φ₂ w * Φ₁ u)
      = ∫⁻ w, ∫⁻ u, H (x - u - w) * Φ₂ w * Φ₁ u :=
    lintegral_lintegral_swap hswap2
  have step3 : (∫⁻ w, ∫⁻ u, H (x - u - w) * Φ₂ w * Φ₁ u)
      = ∫⁻ w, ∫⁻ t, H (x - t) * Φ₂ w * Φ₁ (t - w) := by
    refine lintegral_congr fun w => ?_
    have h2 : (∫⁻ u, H (x - u - w) * Φ₂ w * Φ₁ u)
        = ∫⁻ u, (fun u' : E k => H (x - u') * Φ₂ w * Φ₁ (u' - w)) (u + w) := by
      refine lintegral_congr fun u => ?_
      simp only
      rw [add_sub_cancel_right, sub_add_eq_sub_sub]
    rw [h2]
    simp only []
    exact lintegral_add_right_eq_self (fun u : E k => H (x - u) * Φ₂ w * Φ₁ (u - w)) w
  have hswap4 : AEMeasurable (Function.uncurry
      (fun w t : E k => H (x - t) * Φ₂ w * Φ₁ (t - w))) (volume.prod volume) := by
    have h1 : Measurable (fun p : E k × E k => H (x - p.2) * Φ₂ p.1 * Φ₁ (p.2 - p.1)) :=
      ((hH.comp (measurable_const.sub measurable_snd)).mul (hΦ₂.comp measurable_fst)).mul
        (hΦ₁.comp (measurable_snd.sub measurable_fst))
    exact h1.aemeasurable
  have step4 : (∫⁻ w, ∫⁻ t, H (x - t) * Φ₂ w * Φ₁ (t - w))
      = ∫⁻ t, ∫⁻ w, H (x - t) * Φ₂ w * Φ₁ (t - w) :=
    lintegral_lintegral_swap hswap4
  have hmeas_t : ∀ t : E k, Measurable (fun w : E k => Φ₂ w * Φ₁ (t - w)) := fun t =>
    hΦ₂.mul (hΦ₁.comp (measurable_const.sub measurable_id))
  have step5 : (∫⁻ t, ∫⁻ w, H (x - t) * Φ₂ w * Φ₁ (t - w))
      = ∫⁻ t, H (x - t) * ∫⁻ w, Φ₂ w * Φ₁ (t - w) := by
    refine lintegral_congr fun t => ?_
    rw [show (fun w : E k => H (x - t) * Φ₂ w * Φ₁ (t - w))
        = fun w : E k => H (x - t) * (Φ₂ w * Φ₁ (t - w)) from by funext w; ring]
    exact lintegral_const_mul (H (x - t)) (hmeas_t t)
  rw [step1, step2, step3, step4, step5]
  refine lintegral_congr fun t => ?_
  congr 1
  exact lintegral_congr fun w => mul_comm _ _

/-- **The convolution comparison.**  Let `Φ₁`, `Φ₂` be measurable `ℝ≥0∞`-valued weights with
`Φ₁ ∗ Φ₂ ≤ C Φ₂` (i.e. GLYZ Lemma A.1).  Then for every nonnegative measurable `H`,
`(|H| ∗ Φ₁) ∗ Φ₂ ≤ C · |H| ∗ Φ₂`, i.e.

  `∫⁻ u, (∫⁻ w, H (x − u − w) Φ₂ w) Φ₁ u ≤ C ∫⁻ w, H (x − w) Φ₂ w`. -/
lemma lintegral_convPow_le_of_conv_le {k : ℕ}
    {Φ₁ Φ₂ : E k → ℝ≥0∞} (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂) {C : ℝ}
    (hC : ∀ x : E k, (∫⁻ y, Φ₁ (x - y) * Φ₂ y) ≤ ENNReal.ofReal C * Φ₂ x)
    {H : E k → ℝ≥0∞} (hH : Measurable H) (x : E k) :
    (∫⁻ u, (∫⁻ w, H (x - u - w) * Φ₂ w) * Φ₁ u)
      ≤ ENNReal.ofReal C * ∫⁻ w, H (x - w) * Φ₂ w := by
  rw [lintegral_convPow_assoc hΦ₁ hΦ₂ hH x]
  have step6 : (∫⁻ t, H (x - t) * ∫⁻ w, Φ₁ (t - w) * Φ₂ w)
      ≤ ∫⁻ t, H (x - t) * (ENNReal.ofReal C * Φ₂ t) :=
    lintegral_mono fun t => mul_le_mul' le_rfl (hC t)
  refine step6.trans (le_of_eq ?_)
  rw [show (fun t : E k => H (x - t) * (ENNReal.ofReal C * Φ₂ t))
      = fun t : E k => ENNReal.ofReal C * (H (x - t) * Φ₂ t) from by funext t; ring]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **The commutation of the two convolutions**: `(|H| ∗ Φ₁) ∗ Φ₂ = (|H| ∗ Φ₂) ∗ Φ₁`. -/
lemma lintegral_convPow_swap {k : ℕ} {Φ₁ Φ₂ : E k → ℝ≥0∞} (hΦ₁ : Measurable Φ₁)
    (hΦ₂ : Measurable Φ₂) {H : E k → ℝ≥0∞} (hH : Measurable H) (x : E k) :
    (∫⁻ u, (∫⁻ w, H (x - u - w) * Φ₂ w) * Φ₁ u)
      = ∫⁻ u, (∫⁻ w, H (x - u - w) * Φ₁ w) * Φ₂ u := by
  rw [lintegral_convPow_assoc hΦ₁ hΦ₂ hH x,
    lintegral_convPow_assoc hΦ₂ hΦ₁ hH x]
  refine lintegral_congr fun t => ?_
  rw [lintegral_mul_sub_comm]

/-! ## 3. The uncertainty step in the general form -/

/-- **The uncertainty principle in the general form used by §3.4**: the `r`-th power of a
function of the class of the `8`-enlarged plate is dominated by its convolved `r`-th power
against the canonical bump of the plate itself. -/
theorem norm_rpow_le_convPow_of_isFourierRep {k : ℕ} (hk : 1 ≤ k)
    {δ c : ℝ} (hδ : 0 < δ) {F : E k → ℂ} (hF : IsFourierRep k (plate k (8 * δ) c) F)
    {r : ℝ} (hr : 1 ≤ r) (x : E k) :
    ((‖F x‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ (uncConst k hk) ^ (r - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k r F (platePhi k hk δ c) x := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrpow0 : 0 ≤ r - 1 := by linarith
  have hδP : 0 < 8 * δ := by linarith
  have hδPne : 8 * δ ≠ 0 := hδP.ne'
  have hFcont : Continuous F := hF.continuous
  obtain ⟨M, hM0, hbdd⟩ := hF.exists_bound
  set φ : E k → ℝ := fun y => phiPlate k hk (8 * δ) c (gaugeExp k) (gaugeAmp k hk) y with hφdef
  have hφint : Integrable φ := platePhi_integrable k hk hδPne c
  have hφnn : ∀ y, 0 ≤ φ y :=
    fun y => phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le y
  have hψint : Integrable (platePsi k hk (8 * δ) c) := integrable_platePsi k hk hδPne c
  have hψhat : ∀ ξ ∈ plate k (8 * δ) c,
      (∫ y, platePsi k hk (8 * δ) c y * chat k (-y) ξ) = 1 :=
    fun ξ hξ => platePsi_hat k hk hδP hξ
  have hψφ : ∀ y, ‖platePsi k hk (8 * δ) c y‖ ≤ φ y := fun y => norm_platePsi_le k hk _ _ y
  have hcont1 : Continuous (fun y : E k => ‖F (x - y)‖) :=
    (hFcont.comp (continuous_const.sub continuous_id)).norm
  have hint1 : Integrable (fun y : E k => ‖F (x - y)‖ * φ y) :=
    hφint.bdd_mul hcont1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hbdd (x - y))
  have hint : Integrable (fun y : E k => ‖F (x - y)‖ ^ r * φ y) :=
    hφint.bdd_mul (hcont1.rpow_const (fun _ => Or.inr hr0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbdd (x - y)) hr0)
  have hunc := hF.uncertainty hψint hψhat hφnn hψφ hr x hφint hint1 hint
  have hnn : ∀ y : E k, 0 ≤ ‖F (x - y)‖ ^ r * φ y :=
    fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) r) (hφnn y)
  have hW0 : 0 ≤ ∫ y, φ y := integral_nonneg hφnn
  have hscale : convPow k r F (platePhi k hk (8 * δ) c) x
      ≤ ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)) * convPow k r F (platePhi k hk δ c) x :=
    convPow_scale k hk r F (δ := δ) (t := c) (c := 8) (by norm_num) x
  calc ((‖F x‖₊ : NNReal) : ℝ≥0∞) ^ r
      = ENNReal.ofReal (‖F x‖ ^ r) := coe_nnnorm_rpow (F x) hr0
    _ ≤ ENNReal.ofReal ((∫ y, φ y) ^ (r - 1) * ∫ y, ‖F (x - y)‖ ^ r * φ y) :=
        ENNReal.ofReal_le_ofReal hunc
    _ = ENNReal.ofReal (∫ y, φ y) ^ (r - 1)
          * ENNReal.ofReal (∫ y, ‖F (x - y)‖ ^ r * φ y) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hW0 _),
          ENNReal.ofReal_rpow_of_nonneg hW0 hrpow0]
    _ = (uncConst k hk) ^ (r - 1)
          * convPow k r F (platePhi k hk (8 * δ) c) x := by
        rw [ofReal_integral_phiPlate k hk hδPne c,
          ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
        congr 1
        rw [convPow]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) r),
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (F (x - y))) hr0]
        have h2 : ENNReal.ofReal ‖F (x - y)‖ = ((‖F (x - y)‖₊ : NNReal) : ℝ≥0∞) := by
          simp [ENNReal.ofReal]
        rw [h2, hφdef, platePhi_apply]
    _ ≤ (uncConst k hk) ^ (r - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
          * convPow k r F (platePhi k hk δ c) x := by
        rw [mul_assoc]
        exact mul_le_mul_right hscale _

/-! ## 4. The comparison of the convolutions -/

/-- **The tent comparison `|G|^r ∗ Φ_I ≲ |G|^r ∗ Φ_J` of GLYZ Lemma 3.8** (the `p_l`-side of
the last step of the proof of (3.10)).  If `J` is a refined piece of `I` and `G` is of the class
of the (eight times) enlarged plate of `J`, then convolving the `r`-th power of `G` with the
*coarse* bump `Φ_I` costs a constant compared with convolving with the *fine* bump `Φ_J`. -/
theorem convPow_platePhi_le_of_plate {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 1 ≤ r)
    {δ_J δ_I c_J c_I : ℝ} (hδJ : 0 < δ_J) (hJI : δ_J ≤ δ_I) (hI1 : δ_I ≤ 1)
    (hcI : c_I ∈ Set.Icc (0 : ℝ) 1) (hcJ : c_J ∈ Set.Icc (0 : ℝ) 1) (hcc : |c_J - c_I| ≤ δ_I)
    {G : E k → ℂ} (hG : IsFourierRep k (plate k (8 * δ_J) c_J) G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E k,
      convPow k r G (platePhi k hk δ_I c_I) x
        ≤ ENNReal.ofReal C * convPow k r G (platePhi k hk δ_J c_J) x := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrpow0 : 0 ≤ r - 1 := by linarith
  have hδP0 : 0 < 8 * δ_J := by linarith
  -- the constant `K` of the uncertainty step, as a real
  set K : ℝ := (gaugeAmp k hk * ∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k))) ^ (r - 1)
    with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg (mul_nonneg (gaugeAmp_pos k hk).le
      (integral_nonneg fun z => Real.rpow_nonneg
        (le_trans zero_le_one (le_max_left (1:ℝ) _)) _)) _
  have hKunc : (uncConst k hk) ^ (r - 1) = ENNReal.ofReal K := by
    rw [hKdef]
    have hI : (0:ℝ) ≤ ∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k)) :=
      integral_nonneg fun z => Real.rpow_nonneg
        (le_trans zero_le_one (le_max_left (1:ℝ) _)) _
    rw [uncConst, ← ENNReal.ofReal_mul (gaugeAmp_pos k hk).le]
    exact ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (gaugeAmp_pos k hk).le hI) hrpow0
  -- the A.1 constant
  obtain ⟨CA, hCA0, hCA⟩ := platePhi_conv_le k hk
  have hP : ∀ z : E k, ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k r G (platePhi k hk δ_J c_J) z := by
    intro z
    refine (norm_rpow_le_convPow_of_isFourierRep hk hδJ hG hr z).trans (le_of_eq ?_)
    rw [hKunc, ← ENNReal.ofReal_mul hK0]
  have hH : Measurable (fun z : E k => ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r) :=
    (((hG.continuous.nnnorm).measurable).coe_nnreal_ennreal).pow_const r
  refine ⟨K * (8 : ℝ) ^ (k * (k + 1) / 2) * CA, by positivity, fun x => ?_⟩
  have hmono : convPow k r G (platePhi k hk δ_I c_I) x
      ≤ ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * ∫⁻ u : E k, convPow k r G (platePhi k hk δ_J c_J) (x - u)
            * platePhi k hk δ_I c_I u := by
    rw [convPow]
    have hcongr : (∫⁻ u : E k, (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * convPow k r G (platePhi k hk δ_J c_J) (x - u)) * platePhi k hk δ_I c_I u)
        = ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * ∫⁻ u : E k, convPow k r G (platePhi k hk δ_J c_J) (x - u)
              * platePhi k hk δ_I c_I u := by
      rw [show (fun u : E k => (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
            * convPow k r G (platePhi k hk δ_J c_J) (x - u)) * platePhi k hk δ_I c_I u)
          = fun u : E k => ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
            * (convPow k r G (platePhi k hk δ_J c_J) (x - u)
                * platePhi k hk δ_I c_I u) from by funext u; ring]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact (lintegral_mono fun u => mul_le_mul' (hP (x - u)) le_rfl).trans (le_of_eq hcongr)
  refine hmono.trans ?_
  have hL := lintegral_convPow_le_of_conv_le (k := k) (hΦ₁ := (continuous_platePhi k hk δ_I c_I).measurable)
    (hΦ₂ := (continuous_platePhi k hk δ_J c_J).measurable)
    (C := CA) (hC := fun y => hCA δ_I δ_J c_I c_J y hδJ hJI hI1 hcI hcJ hcc)
    (H := fun z => ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r) hH x
  rw [show (∫⁻ w : E k, ((‖G (x - w)‖₊ : NNReal) : ℝ≥0∞) ^ r
        * platePhi k hk δ_J c_J w) = convPow k r G (platePhi k hk δ_J c_J) x from rfl] at hL
  have hconst : ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * (ENNReal.ofReal CA * convPow k r G (platePhi k hk δ_J c_J) x)
      = ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2) * CA)
        * convPow k r G (platePhi k hk δ_J c_J) x := by
    rw [show ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * (ENNReal.ofReal CA * convPow k r G (platePhi k hk δ_J c_J) x)
        = (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * ENNReal.ofReal CA) * convPow k r G (platePhi k hk δ_J c_J) x from by ring]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ K * (8 : ℝ) ^ (k * (k + 1) / 2))]
  exact (mul_le_mul' le_rfl hL).trans (le_of_eq hconst)

/-! ## 5. The reflected form of `convPow` and the shift comparison -/

/-- **The reflected form of `convPow`**: `(|F|^s ∗ Φ)(x) = ∫ t, ‖F t‖^s Φ (x - t)`.  This is
the substitution `y ↦ x - y` (invariance of Lebesgue measure under reflection). -/
lemma convPow_eq_lintegral_sub (k : ℕ) (s : ℝ) (F : E k → ℂ) (Φ : E k → ℝ≥0∞) (x : E k) :
    convPow k s F Φ x = ∫⁻ t, ((‖F t‖₊ : ℝ≥0∞) ^ s) * Φ (x - t) := by
  rw [convPow]
  rw [← MeasureTheory.lintegral_sub_left_eq_self
    (fun t : E k => ((‖F t‖₊ : ℝ≥0∞) ^ s) * Φ (x - t)) x]
  refine lintegral_congr fun y => ?_
  show ((‖F (x - y)‖₊ : ℝ≥0∞) ^ s) * Φ y
    = ((‖F (x - y)‖₊ : ℝ≥0∞) ^ s) * Φ (x - (x - y))
  rw [show x - (x - y) = y from by abel]

/-- **The canonical tent of a plate is comparable under shifts of small gauge.** -/
lemma platePhi_shift_le_of_gauge {k : ℕ} (hk : 1 ≤ k) (δ c : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x h : E k} (hh : gauge k hk (plateGaugeLin k δ c h) ≤ ρ) :
    platePhi k hk δ c (x + h)
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk δ c x := by
  have hA : (0:ℝ) < gaugeExp k := lt_of_le_of_lt (Nat.cast_nonneg k) (gaugeExp_gt hk)
  have h := phiPlate_shift_le k hk δ c (gaugeExp k) (gaugeAmp k hk) hA hρ (gaugeAmp_pos k hk).le
    (x := x) (h := h) hh
  have h0 : (0:ℝ) ≤ (1 + ρ) ^ gaugeExp k := Real.rpow_nonneg (by linarith) _
  have hx0 : (0:ℝ) ≤ phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x :=
    phiPlate_nonneg k hk δ c (gaugeExp k) (gaugeAmp k hk) (gaugeAmp_pos k hk).le x
  rw [platePhi_apply, platePhi_apply, ← ENNReal.ofReal_mul h0]
  exact ENNReal.ofReal_le_ofReal h

/-- **The sup comparison of the `I'`-side on the `H`-ball** (the second step of GLYZ
Lemma 3.8): the convolved power of the `I'` factor is essentially constant on the `H`-ball of
the critical radius. -/
theorem convPow_platePhi_shift_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ (F : E k → ℂ) (z : E k) (w : E l),
      ‖w‖ ≤ hBallR k l m' →
      convPow k s F (platePhi k hk (plateHalf m') c')
          (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal C * convPow k s F (platePhi k hk (plateHalf m') c') z := by
  obtain ⟨ρ, hρ0, hρ⟩ := gauge_plateGaugeLin_projEmbed_le hk hl hlk hξ'
  refine ⟨(1 + ρ) ^ gaugeExp k, Real.rpow_nonneg (by linarith) _, ?_⟩
  intro m' c' hc' hsep F z w hw
  have hshift : ∀ t : E k, platePhi k hk (plateHalf m') c'
      ((z - t) + projEmbedLin k l (torsionVec k l hlk ξ') w)
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t) :=
    fun t => platePhi_shift_le_of_gauge hk (plateHalf m') c' hρ0 (hρ m' c' hc' hsep w hw)
  rw [convPow_eq_lintegral_sub, convPow_eq_lintegral_sub]
  have hcongr : (∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s)
        * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t)))
      = ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
        * ∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk (plateHalf m') c' (z - t) := by
    rw [show (fun t : E k => ((‖F t‖₊ : ℝ≥0∞) ^ s)
          * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t)))
        = fun t : E k => ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
          * (((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk (plateHalf m') c' (z - t)) from by
      funext t; ring]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine (lintegral_mono fun t => ?_).trans (le_of_eq hcongr)
  have : z + projEmbedLin k l (torsionVec k l hlk ξ') w - t
      = (z - t) + projEmbedLin k l (torsionVec k l hlk ξ') w := by abel
  rw [this]
  exact mul_le_mul' le_rfl (hshift t)

end Submission.Vinogradov
