import Mathlib
import Submission.Work.FIArea2.FintDefs
import Submission.Work.FIArea2.biquadratic_ellipse_bounds
import Submission.Work.FIArea2.lemma_7_1_aux
import Submission.Work.FIArea2.lemma_7_1_volume

set_option maxHeartbeats 1000000

namespace Work.FIArea2

open scoped BigOperators
open scoped FourierTransform
open scoped Topology

open MeasureTheory Filter

noncomputable section

/-! ## Helper lemmas for the proof of Lemma 7.1 -/

/-- The region of integration (7.4): `M/4 ≤ g(t₁,t₂) ≤ 4M`. -/
def reg (M γ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | M / 4 ≤ gq γ p.1 p.2 ∧ gq γ p.1 p.2 ≤ 4 * M}

/-- The integrand of (7.1). -/
def FintInt (f : ℝ → ℝ) (γ u₁ u₂ : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((f (gq γ p.1 p.2) : ℝ) : ℂ)
    * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))

lemma isClosed_reg (M γ : ℝ) : IsClosed (reg M γ) := by
  have hcont : Continuous (fun p : ℝ × ℝ => gq γ p.1 p.2) := by
    simp only [gq]
    fun_prop
  exact IsClosed.inter (isClosed_le continuous_const hcont) (isClosed_le hcont continuous_const)

lemma reg_subset (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    reg M γ ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)} :=
  fun _p hp => (region_bounds M γ _p.1 _p.2 hM hγ0 hγ1 hp.1 hp.2).2.2

lemma reg_subset_sqBox (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    reg M γ ⊆ Set.Icc (-Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)))
        (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) ×ˢ
      Set.Icc (-Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)))
        (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) := by
  intro p hp
  have hδ : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr (one_sub_gamma_sq_pos γ hγ0 hγ1)
  have h4δ : 0 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by positivity
  set R : ℝ := Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) with hR
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := Real.sq_sqrt h4δ
  have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) :=
    reg_subset M γ hM hγ0 hγ1 hp
  have key : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) → |a| ≤ R := by
    intro a b hab
    have h1 : a ^ 2 ≤ R ^ 2 := by rw [hR2]; nlinarith [sq_nonneg b]
    calc |a| = Real.sqrt (a ^ 2) := (Real.sqrt_sq_eq_abs a).symm
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h1
      _ = R := Real.sqrt_sq hRnn
  have h1 := key p.1 p.2 hp'
  have h2 := key p.2 p.1 (by linarith)
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
         ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩

lemma notMem_reg_of_gt (M γ t₁ t₂ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h : 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < t₁ ^ 2 + t₂ ^ 2) :
    ¬ (M / 4 ≤ gq γ t₁ t₂ ∧ gq γ t₁ t₂ ≤ 4 * M) :=
  fun hreg => absurd (region_bounds M γ t₁ t₂ hM hγ0 hγ1 hreg.1 hreg.2).2.2 (not_le.mpr h)

lemma f_gq_eq_zero (M γ : ℝ) (f : ℝ → ℝ)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) {t₁ t₂ : ℝ}
    (h : ¬ (M / 4 ≤ gq γ t₁ t₂ ∧ gq γ t₁ t₂ ≤ 4 * M)) : f (gq γ t₁ t₂) = 0 := by
  rcases not_and_or.mp h with h1 | h2
  · exact f_eq_zero_of_lt M f hfsupp (not_le.mp h1)
  · exact f_eq_zero_of_gt M f hfsupp (not_le.mp h2)

lemma volume_sqBox_lt_top (R : ℝ) :
    volume (Set.Icc (-R) R ×ˢ Set.Icc (-R) R : Set (ℝ × ℝ)) < ⊤ := by
  change (volume.prod volume : Measure (ℝ × ℝ)) (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) < ⊤
  simp only [Measure.prod_prod, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma volume_reg_lt_top (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    volume (reg M γ) < ⊤ :=
  lt_of_le_of_lt (measure_mono (reg_subset_sqBox M γ hM hγ0 hγ1))
    (volume_sqBox_lt_top (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))))

lemma integrable_indicator_reg (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Integrable (Set.indicator (reg M γ) (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff (isClosed_reg M γ).measurableSet]
  exact integrableOn_const (ne_of_lt (volume_reg_lt_top M γ hM hγ0 hγ1))

lemma integrable_indicator_sqBox (R : ℝ) :
    Integrable (Set.indicator (Set.Icc (-R) R ×ˢ Set.Icc (-R) R : Set (ℝ × ℝ))
      (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff (isCompact_Icc.prod isCompact_Icc).isClosed.measurableSet]
  exact integrableOn_const (ne_of_lt (volume_sqBox_lt_top R))

/-- The elementary bound `‖𝓕 g x‖ ≤ ∫ ‖g‖`. -/
lemma norm_fourier_le (g : ℝ → ℂ) (x : ℝ) : ‖𝓕 g x‖ ≤ ∫ t : ℝ, ‖g t‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with t
  simp only [Circle.norm_smul]

/-- **The one-dimensional integration by parts** behind Lemma 7.1: for a `C⁴` function `h` with
integrable derivatives and `u ≠ 0`,
`‖∫ h(t)e(ut)dt‖ ≤ (2π|u|)^{-4}∫‖h^{(4)}‖`. -/
theorem fourier_decay (h : ℝ → ℂ) (u : ℝ) (hu : u ≠ 0) (hcd : ContDiff ℝ 4 h)
    (hint : ∀ n : ℕ, n ≤ 4 → Integrable (iteratedDeriv n h)) :
    ‖∫ t : ℝ, h t * Complex.exp (2 * Real.pi * Complex.I * (u * t))‖
      ≤ (2 * Real.pi * |u|)⁻¹ ^ 4 * ∫ t : ℝ, ‖iteratedDeriv 4 h t‖ := by
  have hint' : ∀ n : ℕ, ((n : ℕ∞) ≤ (4 : ℕ∞)) → Integrable (iteratedDeriv n h) := by
    intro n hn
    exact hint n (by exact_mod_cast hn)
  have hF : 𝓕 h (-u) = ∫ t : ℝ, h t * Complex.exp (2 * Real.pi * Complex.I * (u * t)) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with t
    rw [smul_eq_mul, Real.inner_apply]
    rw [mul_comm (Complex.exp _) (h t)]
    congr 1
    push_cast
    ring
  have hdiff : 𝓕 (iteratedDeriv 4 h) = fun x : ℝ => (2 * ↑Real.pi * Complex.I * ↑x) ^ 4 • 𝓕 h x :=
    Real.fourier_iteratedDeriv hcd hint' (by norm_num)
  have hnorm : ∀ x : ℝ, ‖(2 * ↑Real.pi * Complex.I * ↑x : ℂ)‖ = 2 * Real.pi * |x| := by
    intro x
    simp only [norm_mul, Complex.norm_two, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h1 : ∀ x : ℝ, ‖𝓕 (iteratedDeriv 4 h) x‖ = (2 * Real.pi * |x|) ^ 4 * ‖𝓕 h x‖ := by
    intro x
    rw [hdiff]
    simp only [norm_smul, norm_pow]
    rw [hnorm x]
  have h2 : ‖𝓕 (iteratedDeriv 4 h) (-u)‖ ≤ ∫ t : ℝ, ‖iteratedDeriv 4 h t‖ := norm_fourier_le _ _
  have h3 : (2 * Real.pi * |u|) ^ 4 * ‖𝓕 h (-u)‖ ≤ ∫ t : ℝ, ‖iteratedDeriv 4 h t‖ := by
    have h3' := h1 (-u)
    rw [abs_neg] at h3'
    rw [← h3']
    exact h2
  have hpos : 0 < (2 * Real.pi * |u|) ^ 4 := by
    have : 0 < |u| := abs_pos.mpr hu
    positivity
  rw [← hF]
  calc ‖𝓕 h (-u)‖
      = ((2 * Real.pi * |u|) ^ 4)⁻¹ * ((2 * Real.pi * |u|) ^ 4 * ‖𝓕 h (-u)‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ ≤ ((2 * Real.pi * |u|) ^ 4)⁻¹ * ∫ t : ℝ, ‖iteratedDeriv 4 h t‖ :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hpos.le)
    _ = (2 * Real.pi * |u|)⁻¹ ^ 4 * ∫ t : ℝ, ‖iteratedDeriv 4 h t‖ := by rw [inv_pow]

/-- The derivative of the cast to `ℂ` of a real function. -/
lemma deriv_ofReal_comp (ψ : ℝ → ℝ) {x : ℝ} (hψ : DifferentiableAt ℝ ψ x) :
    deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)) x = ((deriv ψ x : ℝ) : ℂ) := by
  simpa using (hψ.hasDerivAt.ofReal_comp).deriv

lemma iteratedDeriv_ofReal_comp_stmt (φ : ℝ → ℝ) {N : ℕ} (hφ : ContDiff ℝ N φ) (m : ℕ) :
    m ≤ N → ∀ x : ℝ,
      iteratedDeriv m (fun y : ℝ => ((φ y : ℝ) : ℂ)) x = ((iteratedDeriv m φ x : ℝ) : ℂ) := by
  induction m with
  | zero => intro _ x; simp [iteratedDeriv_zero]
  | succ m ih =>
      intro hm x
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have heq : iteratedDeriv m (fun z : ℝ => ((φ z : ℝ) : ℂ))
          = fun y : ℝ => ((iteratedDeriv m φ y : ℝ) : ℂ) := by
        funext y
        exact ih (by omega) y
      rw [heq]
      have hdiffm : DifferentiableAt ℝ (iteratedDeriv m φ) x :=
        (hφ.differentiable_iteratedDeriv m (by exact_mod_cast (by omega : m < N))).differentiableAt
      rw [deriv_ofReal_comp _ hdiffm]

/-- Iterated derivatives commute with the cast `ℝ → ℂ`. -/
lemma iteratedDeriv_ofReal_comp (φ : ℝ → ℝ) {N : ℕ} (hφ : ContDiff ℝ N φ) {m : ℕ}
    (hm : m ≤ N) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => ((φ y : ℝ) : ℂ)) x = ((iteratedDeriv m φ x : ℝ) : ℂ) :=
  iteratedDeriv_ofReal_comp_stmt φ hφ m hm x

/-- If a function agrees with `0` near `x`, all its iterated derivatives vanish at `x`. -/
lemma iteratedDeriv_eq_zero_of_eventuallyEq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : ℝ → F) (n : ℕ) (x : ℝ) (h : φ =ᶠ[𝓝 x] 0) :
    iteratedDeriv n φ x = 0 := by
  have h2 := (Filter.EventuallyEq.iteratedDeriv h n).eq_of_nhds
  simpa only [iteratedDeriv_const_zero] using h2

/-- **The support statement of step (ii)**: where `g(t₁,t₂) ∉ [M/4,4M]`, the function
`s ↦ f(g(s,t₂))` vanishes near `t₁` and hence all its derivatives vanish at `t₁`. -/
lemma iteratedDeriv4_biquadratic_eq_zero (M γ : ℝ) (f : ℝ → ℝ)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (t₁ t₂ : ℝ)
    (hout : ¬ (M / 4 ≤ t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 ∧
               t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 ≤ 4 * M)) :
    iteratedDeriv 4 (fun s : ℝ => f (s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)) t₁ = 0 := by
  have hcont : Continuous (fun s : ℝ => gq γ s t₂) := by
    simp only [gq]; fun_prop
  rcases not_and_or.mp hout with h1 | h2
  · have hlt : gq γ t₁ t₂ < M / 4 := not_le.mp h1
    refine iteratedDeriv_eq_zero_of_eventuallyEq_zero _ 4 t₁ ?_
    filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hlt] with s hs
    exact f_eq_zero_of_lt M f hfsupp hs
  · have hlt : 4 * M < gq γ t₁ t₂ := not_le.mp h2
    refine iteratedDeriv_eq_zero_of_eventuallyEq_zero _ 4 t₁ ?_
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hlt] with s hs
    exact f_eq_zero_of_gt M f hfsupp hs

/-- A `C^n` function vanishing outside a compact interval has integrable iterated derivatives. -/
lemma integrable_iteratedDeriv_of_eq_zero_outside (h : ℝ → ℂ) (a b : ℝ) {n : ℕ}
    (hcd : ContDiff ℝ n h) (hsupp : ∀ x, x < a → h x = 0) (hsupp' : ∀ x, b < x → h x = 0)
    {k : ℕ} (hk : k ≤ n) : Integrable (iteratedDeriv k h) := by
  have hcont : Continuous (iteratedDeriv k h) :=
    hcd.continuous_iteratedDeriv k (by exact_mod_cast hk)
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) ?_)
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact iteratedDeriv_eq_zero_of_eventuallyEq_zero _ k x (by
      filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds hx] with y hy
      exact hsupp y hy)
  · exact iteratedDeriv_eq_zero_of_eventuallyEq_zero _ k x (by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
      exact hsupp' y hy)

/-- The functions `s ↦ f(g(s,t₂))` for `f` supported in `[M/4,4M]` vanish for `|s|` beyond
`√(4√M/√(1−γ²))`. -/
lemma hfun_eq_zero_outside (M γ : ℝ) (f : ℝ → ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (t₂ : ℝ) :
    (∀ x : ℝ, x < -Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) →
        (f (gq γ x t₂) : ℂ) = 0) ∧
    (∀ x : ℝ, Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) < x →
        (f (gq γ x t₂) : ℂ) = 0) := by
  have hδ : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr (one_sub_gamma_sq_pos γ hγ0 hγ1)
  have h4δ : 0 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by positivity
  have hRnn : 0 ≤ Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) := Real.sqrt_nonneg _
  have hR2 : (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) ^ 2
      = 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := Real.sq_sqrt h4δ
  have hsq : ∀ x : ℝ, Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) < |x| →
      4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < x ^ 2 := by
    intro x hx
    nlinarith [hR2, hRnn, sq_abs x]
  constructor
  · intro x hx
    have hx2 : 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < x ^ 2 :=
      hsq x (by rw [abs_of_neg (by linarith : x < 0)]; linarith)
    have hgt : 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < x ^ 2 + t₂ ^ 2 := by
      linarith [sq_nonneg t₂]
    simp only [Complex.ofReal_eq_zero]
    exact f_gq_eq_zero M γ f hfsupp (notMem_reg_of_gt M γ x t₂ hM hγ0 hγ1 hgt)
  · intro x hx
    have hx2 : 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < x ^ 2 := hsq x (by rwa [abs_of_pos (by linarith)])
    have hgt : 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) < x ^ 2 + t₂ ^ 2 := by
      linarith [sq_nonneg t₂]
    simp only [Complex.ofReal_eq_zero]
    exact f_gq_eq_zero M γ f hfsupp (notMem_reg_of_gt M γ x t₂ hM hγ0 hγ1 hgt)

/-- The inner functions `s ↦ f(g(s,t₂))` are `C⁴` with integrable derivatives. -/
lemma contDiff_integrable_hfun (M γ : ℝ) (f : ℝ → ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (t₂ : ℝ) :
    ContDiff ℝ 4 (fun s : ℝ => (f (gq γ s t₂) : ℂ)) ∧
    (∀ n : ℕ, n ≤ 4 → Integrable (iteratedDeriv n (fun s : ℝ => (f (gq γ s t₂) : ℂ)))) := by
  have h1 : ContDiff ℝ 4 (fun s : ℝ => gq γ s t₂) := by
    simp only [gq]; fun_prop
  have hcd : ContDiff ℝ 4 (fun s : ℝ => (f (gq γ s t₂) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp h1)
  obtain ⟨hleft, hright⟩ := hfun_eq_zero_outside M γ f hM hγ0 hγ1 hfsupp t₂
  exact ⟨hcd, fun n hn => integrable_iteratedDeriv_of_eq_zero_outside _ _ _ hcd hleft hright hn⟩

/-- The integrand of (7.1) is integrable: it is continuous, bounded by `1` and supported in the
region (7.4), a set of finite measure. -/
lemma integrable_Fint_integrand (M γ : ℝ) (f : ℝ → ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hf : Continuous f) (hfb : ∀ u, |f u| ≤ 1)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (u₁ u₂ : ℝ) :
    Integrable (fun p : ℝ × ℝ => ((f (gq γ p.1 p.2) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))) := by
  set R : ℝ := Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) with hR
  have hcont : Continuous (fun p : ℝ × ℝ => ((f (gq γ p.1 p.2) : ℝ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (hf.comp (by simp only [gq]; fun_prop))
    · fun_prop
  refine Integrable.mono' (integrable_indicator_sqBox R) hcont.aestronglyMeasurable ?_
  filter_upwards with p
  rw [norm_mul]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2) : ℂ)
        = ((2 * Real.pi * (u₁ * p.1 + u₂ * p.2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  by_cases hp : p ∈ Set.Icc (-R) R ×ˢ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hp, Complex.norm_real]
    exact hfb _
  · rw [Set.indicator_of_notMem hp]
    have hzero : f (gq γ p.1 p.2) = 0 := by
      apply f_gq_eq_zero M γ f hfsupp
      apply notMem_reg_of_gt M γ p.1 p.2 hM hγ0 hγ1
      have h4δ : 0 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by
        have := Real.sqrt_pos.mpr (one_sub_gamma_sq_pos γ hγ0 hγ1); positivity
      have hRnn : 0 ≤ R := Real.sqrt_nonneg _
      have hR2 : R ^ 2 = 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := Real.sq_sqrt h4δ
      have hnot : ¬ (|p.1| ≤ R ∧ |p.2| ≤ R) := by
        intro h
        exact hp (by
          rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
          exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
                 ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩)
      rw [not_and_or, not_le, not_le] at hnot
      rcases hnot with h | h
      · have hs : R ^ 2 < p.1 ^ 2 := by
          nlinarith [sq_abs p.1, abs_nonneg p.1, hRnn, h]
        rw [hR2] at hs
        linarith [sq_nonneg p.2]
      · have hs : R ^ 2 < p.2 ^ 2 := by
          nlinarith [sq_abs p.2, abs_nonneg p.2, hRnn, h]
        rw [hR2] at hs
        linarith [sq_nonneg p.1]
    rw [hzero, Complex.ofReal_zero, norm_zero]

/-- Fubini for (7.1): the double integral is an iterated integral with the `t₂`-integration
outside. -/
lemma Fint_eq_iterated (f : ℝ → ℝ) (γ u₁ u₂ : ℝ)
    (hint : Integrable (fun p : ℝ × ℝ => ((f (gq γ p.1 p.2) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2)))) :
    Fint f γ u₁ u₂ = ∫ t₂ : ℝ, ∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂)) := by
  rw [Fint]
  simp only [gq]
  exact integral_prod_symm _ hint

/-- The exchange of the two variables of an integral over `ℝ × ℝ`. -/
lemma integral_swap_prod (F : ℝ × ℝ → ℂ) :
    ∫ p : ℝ × ℝ, F p.swap = ∫ q : ℝ × ℝ, F q := by
  change (∫ p, F (Prod.swap p) ∂(volume.prod volume : Measure (ℝ × ℝ)))
      = (∫ q, F q ∂(volume.prod volume : Measure (ℝ × ℝ)))
  exact MeasurePreserving.integral_comp' (f := (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ))
    Measure.measurePreserving_swap F

/-- The invariance of (7.1) under exchanging the two frequencies. -/
lemma Fint_swap (f : ℝ → ℝ) (γ u₁ u₂ : ℝ) :
    Fint f γ u₁ u₂ = Fint f γ u₂ u₁ := by
  have h1 : Fint f γ u₁ u₂ = ∫ p : ℝ × ℝ, FintInt f γ u₁ u₂ p := by
    rw [Fint]; rfl
  have h2 : Fint f γ u₂ u₁ = ∫ p : ℝ × ℝ, FintInt f γ u₁ u₂ p.swap := by
    rw [Fint]
    apply integral_congr_ae
    filter_upwards with p
    simp only [FintInt, Prod.fst_swap, Prod.snd_swap, gq]
    rw [show p.2 ^ 4 - 2 * γ * p.2 ^ 2 * p.1 ^ 2 + p.1 ^ 4
          = p.1 ^ 4 - 2 * γ * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4 by ring,
      show (2 * ↑Real.pi * Complex.I * (↑u₁ * ↑p.2 + ↑u₂ * ↑p.1))
        = 2 * ↑Real.pi * Complex.I * (↑u₂ * ↑p.1 + ↑u₁ * ↑p.2) by ring]

  rw [h1, h2]
  exact (integral_swap_prod (FintInt f γ u₁ u₂)).symm

/-- The final arithmetic of Lemma 7.1: from the trivial bound `F ≤ A` and the two
integration-by-parts bounds `x²F ≤ B`, `y²F ≤ C` with `x = u₁²√(1−γ²)√M`, `y = u₂²√(1−γ²)√M`,
one gets `F ≤ 4·max(A,B,C)/((1+x)(1+y))`. -/
lemma combine_bounds (x y A B C F : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hF : 0 ≤ F)
    (hA : F ≤ A) (hB : x ^ 2 * F ≤ B) (hC : y ^ 2 * F ≤ C) :
    F ≤ 4 * max A (max B C) / ((1 + x) * (1 + y)) := by
  set M : ℝ := max A (max B C) with hM
  have hAM : A ≤ M := le_max_left _ _
  have hBM : B ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCM : C ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0 : 0 ≤ M := le_trans hA0 hAM
  have hFx : F * x ^ 2 ≤ M := by
    rw [mul_comm F (x ^ 2)]; linarith [hB, hBM]
  have hFy : F * y ^ 2 ≤ M := by
    rw [mul_comm F (y ^ 2)]; linarith [hC, hCM]
  have hF1 : F * 1 ≤ M := by linarith [hA, hAM]
  have hkey : F * max 1 (max (x ^ 2) (y ^ 2)) ≤ M := by
    rw [mul_max_of_nonneg _ _ hF, mul_max_of_nonneg _ _ hF]
    exact max_le hF1 (max_le hFx hFy)
  have hgeom : (1 + x) * (1 + y) ≤ 4 * max 1 (max (x ^ 2) (y ^ 2)) := by
    have hm1 : (1 : ℝ) ≤ max 1 (max (x ^ 2) (y ^ 2)) := le_max_left _ _
    have hmx : x ^ 2 ≤ max 1 (max (x ^ 2) (y ^ 2)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hmy : y ^ 2 ≤ max 1 (max (x ^ 2) (y ^ 2)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1x : 1 + x ≤ 2 := by linarith
      rcases le_or_gt y 1 with hy1 | hy1
      · have h1y : 1 + y ≤ 2 := by linarith
        nlinarith [h1x, h1y, hm1, hx, hy]
      · have h1y : 1 + y ≤ 2 * y := by linarith
        have hy2 : y ≤ y ^ 2 := by nlinarith
        nlinarith [h1x, h1y, hmy, hx, hy, hy2]
    · have h1x : 1 + x ≤ 2 * x := by linarith
      have hx2 : x ≤ x ^ 2 := by nlinarith
      rcases le_or_gt y 1 with hy1 | hy1
      · have h1y : 1 + y ≤ 2 := by linarith
        nlinarith [h1x, h1y, hmx, hx, hy, hx2]
      · have h1y : 1 + y ≤ 2 * y := by linarith
        nlinarith [h1x, h1y, hmx, hmy, hx, hy, sq_nonneg (x - y)]
  have hden : 0 < (1 + x) * (1 + y) := by positivity
  rw [le_div_iff₀ hden]
  calc F * ((1 + x) * (1 + y)) ≤ F * (4 * max 1 (max (x ^ 2) (y ^ 2))) :=
        mul_le_mul_of_nonneg_left hgeom hF
    _ = 4 * (F * max 1 (max (x ^ 2) (y ^ 2))) := by ring
    _ ≤ 4 * M := by linarith [hkey]


/-! ### The pointwise fourth-derivative bound and the volume bound -/

/-- **Faà di Bruno bound** (delegated to `Submission.Work.FIArea2.lemma_7_1_deriv4_bound` once
available): on the region, `|∂₁⁴(f∘g)| ≤ 10^7 M⁻¹(1−γ²)⁻¹`. -/
lemma deriv4_bound_aux (M γ : ℝ) (f : ℝ → ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ)))
    (t₁ t₂ : ℝ) (hreg : M / 4 ≤ gq γ t₁ t₂ ∧ gq γ t₁ t₂ ≤ 4 * M) :
    |iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁| ≤ 10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹ := by
  have hMpos : 0 < M := by linarith
  have hγsq : 0 < 1 - γ ^ 2 := one_sub_gamma_sq_pos γ hγ0 hγ1
  have hsM0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hsδ0 : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr hγsq
  have hsM2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
  have hsδ2 : Real.sqrt (1 - γ ^ 2) ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt hγsq.le
  have hsδle1 : Real.sqrt (1 - γ ^ 2) ≤ 1 := by
    calc Real.sqrt (1 - γ ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg γ])
      _ = 1 := Real.sqrt_one
  obtain ⟨h12, hsumlo, hsumhi⟩ := region_bounds M γ t₁ t₂ hMpos hγ0 hγ1 hreg.1 hreg.2
  have hdiff_j : ∀ j : ℕ, j < 4 → Differentiable ℝ (iteratedDeriv j f) := fun j hj =>
    hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  set a : ℝ → ℝ := fun y : ℝ => 4 * y ^ 3 - 4 * γ * y * t₂ ^ 2 with hadef
  set b : ℝ → ℝ := fun y : ℝ => 12 * y ^ 2 - 4 * γ * t₂ ^ 2 with hbdef
  set c : ℝ → ℝ := fun y : ℝ => 24 * y with hcdef
  set G1 : ℝ → ℝ := fun y : ℝ => iteratedDeriv 1 f (gq γ y t₂) with hG1def
  set G2 : ℝ → ℝ := fun y : ℝ => iteratedDeriv 2 f (gq γ y t₂) with hG2def
  set G3 : ℝ → ℝ := fun y : ℝ => iteratedDeriv 3 f (gq γ y t₂) with hG3def
  set G4 : ℝ → ℝ := fun y : ℝ => iteratedDeriv 4 f (gq γ y t₂) with hG4def
  have hGd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => gq γ y t₂) (a x) x := by
    intro x
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
      simpa using hasDerivAt_pow 4 x
    have h2 : HasDerivAt (fun y : ℝ => 2 * γ * y ^ 2 * t₂ ^ 2) (2 * γ * (2 * x) * t₂ ^ 2) x := by
      have h := ((hasDerivAt_pow 2 x).const_mul (2 * γ)).mul_const (t₂ ^ 2)
      simpa using h
    have h5 : HasDerivAt (fun _ : ℝ => t₂ ^ 4) 0 x := hasDerivAt_const x (t₂ ^ 4)
    have h6 := (h4.sub h2).add h5
    have hval : 4 * x ^ 3 - 2 * γ * (2 * x) * t₂ ^ 2 + 0 = a x := by
      rw [hadef]; ring
    rw [hval] at h6
    exact h6
  have had : ∀ x : ℝ, HasDerivAt a (b x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 4 * y ^ 3) (4 * (3 * x ^ 2)) x :=
      (hasDerivAt_pow 3 x).const_mul 4
    have h2 : HasDerivAt (fun y : ℝ => 4 * γ * y * t₂ ^ 2) (4 * γ * t₂ ^ 2) x := by
      have h := ((hasDerivAt_id x).const_mul (4 * γ)).mul_const (t₂ ^ 2)
      have hval : (4 * γ * 1) * t₂ ^ 2 = 4 * γ * t₂ ^ 2 := by ring
      rw [hval] at h
      exact h
    have h3 := h1.sub h2
    have hval : 4 * (3 * x ^ 2) - 4 * γ * t₂ ^ 2 = b x := by
      rw [hbdef]; ring
    rw [hval] at h3
    exact h3
  have hbd : ∀ x : ℝ, HasDerivAt b (c x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 12 * y ^ 2) (12 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul 12
    have h2 : HasDerivAt (fun _ : ℝ => 4 * γ * t₂ ^ 2) 0 x :=
      hasDerivAt_const x (4 * γ * t₂ ^ 2)
    have h3 := h1.sub h2
    have hval : 12 * (2 * x) - 0 = c x := by
      rw [hcdef]; ring
    rw [hval] at h3
    exact h3
  have hcd : ∀ x : ℝ, HasDerivAt c 24 x := by
    intro x
    have h := (hasDerivAt_id x).const_mul 24
    have hval : 24 * 1 = (24 : ℝ) := by norm_num
    rw [hval] at h
    exact h
  have hG' : ∀ j : ℕ, j < 4 → ∀ x : ℝ, HasDerivAt (fun y : ℝ => iteratedDeriv j f (gq γ y t₂))
      (iteratedDeriv (j + 1) f (gq γ x t₂) * a x) x := by
    intro j hj x
    have h1 : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f (gq γ x t₂))
        (gq γ x t₂) := by
      have h := (hdiff_j j hj (gq γ x t₂)).hasDerivAt
      have hval : deriv (iteratedDeriv j f) (gq γ x t₂)
          = iteratedDeriv (j + 1) f (gq γ x t₂) :=
        congrFun (iteratedDeriv_succ (n := j) (f := f)).symm (gq γ x t₂)
      rwa [hval] at h
    exact h1.comp x (hGd x)
  have hD1 : deriv (fun y : ℝ => f (gq γ y t₂)) = G1 * a := by
    funext x
    have h1 : HasDerivAt f (iteratedDeriv 1 f (gq γ x t₂)) (gq γ x t₂) := by
      have hd : DifferentiableAt ℝ f (gq γ x t₂) :=
        (hf.differentiable (by norm_num)).differentiableAt
      have h := hd.hasDerivAt
      rwa [← iteratedDeriv_one] at h
    have h2 : HasDerivAt (fun y : ℝ => f (gq γ y t₂)) (iteratedDeriv 1 f (gq γ x t₂) * a x) x :=
      h1.comp x (hGd x)
    have h3 := h2.deriv
    rw [h3]
    simp only [hG1def, hadef, Pi.mul_apply]
  have hD2 : deriv (G1 * a) = G2 * (a * a) + G1 * b := by
    funext x
    have h := (hG' 1 (by norm_num) x).mul (had x)
    have h2 := h.deriv
    rw [h2]
    simp only [hG1def, hG2def, hadef, hbdef, Pi.mul_apply, Pi.add_apply]
    ring
  have hD3 : deriv (G2 * (a * a) + G1 * b)
      = G3 * ((a * a) * a) + (fun y : ℝ => 3 * (((G2 * a) * b) y)) + G1 * c := by
    funext x
    have hA2 : HasDerivAt (a * a) (b x * a x + a x * b x) x := (had x).mul (had x)
    have h := ((hG' 2 (by norm_num) x).mul hA2).add ((hG' 1 (by norm_num) x).mul (hbd x))
    have h2 := h.deriv
    rw [h2]
    simp only [hG1def, hG2def, hG3def, hadef, hbdef, hcdef, Pi.mul_apply, Pi.add_apply]
    ring
  have hD4 : deriv (G3 * ((a * a) * a) + (fun y : ℝ => 3 * (((G2 * a) * b) y)) + G1 * c)
      = G4 * (((a * a) * a) * a) + (fun y : ℝ => 6 * (((G3 * (a * a)) * b) y))
        + (fun y : ℝ => 3 * ((G2 * (b * b)) y)) + (fun y : ℝ => 4 * (((G2 * a) * c) y))
        + (fun y : ℝ => 24 * G1 y) := by
    funext x
    have hA2 : HasDerivAt (a * a) (b x * a x + a x * b x) x := (had x).mul (had x)
    have hA3 : HasDerivAt ((a * a) * a) ((b x * a x + a x * b x) * a x + (a x * a x) * b x) x :=
      hA2.mul (had x)
    have hAB : HasDerivAt ((G2 * a) * b) ((((G3 x * a x) * a x + G2 x * b x)) * b x + (G2 x * a x) * c x) x :=
      (((hG' 2 (by norm_num) x).mul (had x)).mul (hbd x))
    have h3 : HasDerivAt (G3 * ((a * a) * a)) ((G4 x * a x) * ((a * a) * a) x
        + G3 x * ((b x * a x + a x * b x) * a x + (a x * a x) * b x)) x :=
      (hG' 3 (by norm_num) x).mul hA3
    have h2 := ((h3.add (hAB.const_mul 3)).add ((hG' 1 (by norm_num) x).mul (hcd x)))
    have h2' := h2.deriv
    rw [h2']
    simp only [hG1def, hG2def, hG3def, hG4def, hadef, hbdef, hcdef, Pi.mul_apply, Pi.add_apply]
    ring
  have hL4 : iteratedDeriv 4 (fun y : ℝ => f (gq γ y t₂))
      = G4 * (((a * a) * a) * a) + (fun y : ℝ => 6 * (((G3 * (a * a)) * b) y))
        + (fun y : ℝ => 3 * ((G2 * (b * b)) y)) + (fun y : ℝ => 4 * (((G2 * a) * c) y))
        + (fun y : ℝ => 24 * G1 y) := by
    rw [iteratedDeriv_eq_iterate]
    show deriv (deriv (deriv (deriv (fun y : ℝ => f (gq γ y t₂))))) = _
    rw [hD1, hD2, hD3, hD4]
  set S : ℝ := t₁ ^ 2 + t₂ ^ 2 with hSdef
  set A1 : ℝ := 4 * t₁ ^ 3 - 4 * γ * t₁ * t₂ ^ 2 with hA1def
  set B1 : ℝ := 12 * t₁ ^ 2 - 4 * γ * t₂ ^ 2 with hB1def
  set C1 : ℝ := 24 * t₁ with hC1def
  set P1 : ℝ := iteratedDeriv 1 f (gq γ t₁ t₂) with hP1def
  set P2 : ℝ := iteratedDeriv 2 f (gq γ t₁ t₂) with hP2def
  set P3 : ℝ := iteratedDeriv 3 f (gq γ t₁ t₂) with hP3def
  set P4 : ℝ := iteratedDeriv 4 f (gq γ t₁ t₂) with hP4def
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  have hSlo : Real.sqrt M / 2 ≤ S := hsumlo
  have hShi : S ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := hsumhi
  have ht1le : |t₁| ≤ Real.sqrt S := by
    calc |t₁| = Real.sqrt (t₁ ^ 2) := (Real.sqrt_sq_eq_abs t₁).symm
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt (by rw [hSdef]; linarith [sq_nonneg t₂])
  have hSk : S ^ 2 * (1 - γ ^ 2) ≤ 16 * M := by
    have h2 : S * Real.sqrt (1 - γ ^ 2) ≤ 4 * Real.sqrt M := (le_div_iff₀ hsδ0).mp hShi
    have h3 : (S * Real.sqrt (1 - γ ^ 2)) ^ 2 ≤ (4 * Real.sqrt M) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, hsδ2, mul_pow, hsM2] at h3
    nlinarith [h3]
  have hSk' : S * (1 - γ ^ 2) ≤ 4 * Real.sqrt M := by
    have h2 : S * Real.sqrt (1 - γ ^ 2) ≤ 4 * Real.sqrt M := (le_div_iff₀ hsδ0).mp hShi
    have h3 : (1 - γ ^ 2) ≤ Real.sqrt (1 - γ ^ 2) := by nlinarith [hsδ2, hsδ0, hsδle1]
    calc S * (1 - γ ^ 2) ≤ S * Real.sqrt (1 - γ ^ 2) := by
          exact mul_le_mul_of_nonneg_left h3 hSnn
      _ ≤ 4 * Real.sqrt M := h2
  have hsq : |t₁ ^ 2 - γ * t₂ ^ 2| ≤ 6 * Real.sqrt M := by
    have h1γ : 1 - γ ≤ 1 - γ ^ 2 := by nlinarith [hγ0]
    have h2 : (1 - γ) * t₂ ^ 2 ≤ 6 * Real.sqrt M - 2 * Real.sqrt M := by
      have h4 : (1 - γ) * t₂ ^ 2 ≤ (1 - γ ^ 2) * S := by
        have : t₂ ^ 2 ≤ S := by rw [hSdef]; linarith [sq_nonneg t₁]
        nlinarith [h1γ, this, hγsq, sq_nonneg t₂]
      have h5 : (1 - γ ^ 2) * S ≤ 4 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M := by
        have hsq : Real.sqrt (1 - γ ^ 2) * Real.sqrt (1 - γ ^ 2) = 1 - γ ^ 2 := by
          rw [← pow_two, hsδ2]
        have h3 : (1 - γ ^ 2) * S = (S * Real.sqrt (1 - γ ^ 2)) * Real.sqrt (1 - γ ^ 2) := by
          conv_lhs => rw [← hsq]
          ring
        rw [h3]
        calc (S * Real.sqrt (1 - γ ^ 2)) * Real.sqrt (1 - γ ^ 2)
            ≤ (4 * Real.sqrt M) * Real.sqrt (1 - γ ^ 2) :=
              mul_le_mul_of_nonneg_right ((le_div_iff₀ hsδ0).mp hShi) (by positivity)
          _ = 4 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M := by ring
      nlinarith [h4, h5, hsδle1, hsM0]
    have h6 : |t₁ ^ 2 - γ * t₂ ^ 2| ≤ |t₁ ^ 2 - t₂ ^ 2| + (1 - γ) * t₂ ^ 2 := by
      have he : t₁ ^ 2 - γ * t₂ ^ 2 = (t₁ ^ 2 - t₂ ^ 2) + (1 - γ) * t₂ ^ 2 := by ring
      rw [he]
      calc |(t₁ ^ 2 - t₂ ^ 2) + (1 - γ) * t₂ ^ 2|
          ≤ |t₁ ^ 2 - t₂ ^ 2| + |(1 - γ) * t₂ ^ 2| := abs_add_le _ _
        _ = |t₁ ^ 2 - t₂ ^ 2| + (1 - γ) * t₂ ^ 2 := by
            rw [abs_of_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - γ) (sq_nonneg t₂))]
    linarith [h6, h12, h2]
  have hA1b : |A1| ≤ 24 * Real.sqrt S * Real.sqrt M := by
    have hfac : A1 = 4 * t₁ * (t₁ ^ 2 - γ * t₂ ^ 2) := by rw [hA1def]; ring
    rw [hfac, abs_mul, abs_mul]
    have h4 : |(4 : ℝ)| = 4 := by norm_num
    rw [h4]
    calc 4 * |t₁| * |t₁ ^ 2 - γ * t₂ ^ 2| ≤ 4 * Real.sqrt S * (6 * Real.sqrt M) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left ht1le (by norm_num)) hsq (abs_nonneg _) (by positivity)
      _ = 24 * Real.sqrt S * Real.sqrt M := by ring
  have hA1sq : A1 ^ 2 ≤ 576 * S * M := by
    have h2 : A1 ^ 2 ≤ (24 * Real.sqrt S * Real.sqrt M) ^ 2 := by
      rw [← sq_abs A1]; exact pow_le_pow_left₀ (abs_nonneg _) hA1b 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hSnn, Real.sq_sqrt hMpos.le] at h2
    nlinarith [h2]
  have hA1q : A1 ^ 4 ≤ 331776 * S ^ 2 * M ^ 2 := by
    have h2 : (A1 ^ 2) ^ 2 ≤ (576 * S * M) ^ 2 := pow_le_pow_left₀ (by positivity) hA1sq 2
    nlinarith [h2]
  have hB1b : |B1| ≤ 12 * S := by
    rw [hB1def]
    have h1 : |12 * t₁ ^ 2 - 4 * γ * t₂ ^ 2| ≤ 12 * t₁ ^ 2 + 4 * γ * t₂ ^ 2 := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [hγ0, sq_nonneg t₁, sq_nonneg t₂]
    have h2 : t₁ ^ 2 ≤ S := by rw [hSdef]; linarith [sq_nonneg t₂]
    have h3 : t₂ ^ 2 ≤ S := by rw [hSdef]; linarith [sq_nonneg t₁]
    nlinarith [h1, h2, h3, hγ0, hγ1]
  have hB1sq : B1 ^ 2 ≤ 144 * S ^ 2 := by
    have h2 : B1 ^ 2 ≤ (12 * S) ^ 2 := by
      rw [← sq_abs B1]; exact pow_le_pow_left₀ (abs_nonneg _) hB1b 2
    nlinarith [h2]
  have hC1b : |C1| ≤ 24 * Real.sqrt S := by
    rw [hC1def, abs_mul]
    have h4 : |(24 : ℝ)| = 24 := by norm_num
    rw [h4]
    calc 24 * |t₁| ≤ 24 * Real.sqrt S := mul_le_mul_of_nonneg_left ht1le (by norm_num)
      _ = 24 * Real.sqrt S := by ring
  have hACb : |A1| * |C1| ≤ 576 * S * Real.sqrt M := by
    calc |A1| * |C1| ≤ (24 * Real.sqrt S * Real.sqrt M) * (24 * Real.sqrt S) :=
          mul_le_mul hA1b hC1b (abs_nonneg _) (by positivity)
      _ = 576 * S * Real.sqrt M := by
          rw [show (24 * Real.sqrt S * Real.sqrt M) * (24 * Real.sqrt S)
              = 576 * (Real.sqrt S * Real.sqrt S) * Real.sqrt M by ring,
            ← pow_two, Real.sq_sqrt hSnn, mul_assoc]
  have hPj : ∀ j : ℕ, j ≤ 4 → |iteratedDeriv j f (gq γ t₁ t₂)| * M ^ j ≤ 1 := by
    intro j hj
    have h := hfd j hj (gq γ t₁ t₂)
    rw [show M ^ (-(j : ℝ)) = M⁻¹ ^ j by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]] at h
    calc |iteratedDeriv j f (gq γ t₁ t₂)| * M ^ j ≤ M⁻¹ ^ j * M ^ j :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = (M⁻¹ * M) ^ j := by rw [mul_pow]
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hMpos), one_pow]
  have hfab : iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁
      = P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2) + 4 * (P2 * A1 * C1) + 24 * P1 := by
    have h := congrFun hL4 t₁
    simp only [Pi.mul_apply, Pi.add_apply] at h
    have hAt1 : a t₁ = A1 := by rw [hA1def, hadef]
    have hBt1 : b t₁ = B1 := by rw [hB1def, hbdef]
    have hCt1 : c t₁ = C1 := by rw [hC1def, hcdef]
    have hG1t : G1 t₁ = P1 := by rw [hG1def, hP1def]
    have hG2t : G2 t₁ = P2 := by rw [hG2def, hP2def]
    have hG3t : G3 t₁ = P3 := by rw [hG3def, hP3def]
    have hG4t : G4 t₁ = P4 := by rw [hG4def, hP4def]
    rw [hAt1, hBt1, hCt1, hG1t, hG2t, hG3t, hG4t] at h
    rw [h]
    ring
  have hP1' : |P1| * M ≤ 1 := by rw [hP1def]; simpa using hPj 1 (by norm_num)
  have hP2' : |P2| * M ^ 2 ≤ 1 := by rw [hP2def]; simpa using hPj 2 (by norm_num)
  have hP3' : |P3| * M ^ 3 ≤ 1 := by rw [hP3def]; simpa using hPj 3 (by norm_num)
  have hP4' : |P4| * M ^ 4 ≤ 1 := by rw [hP4def]; simpa using hPj 4 (by norm_num)
  have hT1 : |P4 * A1 ^ 4| * M * (1 - γ ^ 2) ≤ 5308416 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A1 ^ 4)]
    have h5 : |P4| * A1 ^ 4 * M ^ 4 ≤ 331776 * S ^ 2 * M ^ 2 := by
      calc |P4| * A1 ^ 4 * M ^ 4 = (|P4| * M ^ 4) * A1 ^ 4 := by ring
        _ ≤ 1 * (331776 * S ^ 2 * M ^ 2) :=
            mul_le_mul hP4' hA1q (by positivity) (by norm_num)
        _ = 331776 * S ^ 2 * M ^ 2 := by ring
    have hX : (|P4| * A1 ^ 4 * M * (1 - γ ^ 2)) * M ^ 3 ≤ 5308416 * M ^ 3 := by
      rw [show (|P4| * A1 ^ 4 * M * (1 - γ ^ 2)) * M ^ 3
          = |P4| * A1 ^ 4 * M ^ 4 * (1 - γ ^ 2) by ring]
      calc |P4| * A1 ^ 4 * M ^ 4 * (1 - γ ^ 2)
          ≤ (331776 * S ^ 2 * M ^ 2) * (1 - γ ^ 2) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = 331776 * (S ^ 2 * (1 - γ ^ 2)) * M ^ 2 := by ring
        _ ≤ 331776 * (16 * M) * M ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSk (by norm_num)) (by positivity)
        _ = 5308416 * M ^ 3 := by ring
    exact le_of_mul_le_mul_right hX (by positivity)
  have hT2 : 6 * |P3 * A1 ^ 2 * B1| * M * (1 - γ ^ 2) ≤ 663552 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A1 ^ 2)]
    have h5 : |P3| * A1 ^ 2 * |B1| * M ^ 3 ≤ 6912 * S ^ 2 * M := by
      calc |P3| * A1 ^ 2 * |B1| * M ^ 3 = (|P3| * M ^ 3) * (A1 ^ 2 * |B1|) := by ring
        _ ≤ 1 * ((576 * S * M) * (12 * S)) :=
            mul_le_mul hP3' (mul_le_mul hA1sq hB1b (abs_nonneg _) (by positivity))
              (by positivity) (by norm_num)
        _ = 6912 * S ^ 2 * M := by ring
    have hX : (6 * (|P3| * A1 ^ 2 * |B1|) * M * (1 - γ ^ 2)) * M ^ 3 ≤ 663552 * M ^ 3 := by
      rw [show (6 * (|P3| * A1 ^ 2 * |B1|) * M * (1 - γ ^ 2)) * M ^ 3
          = 6 * (|P3| * A1 ^ 2 * |B1| * M ^ 3) * M * (1 - γ ^ 2) by ring]
      calc 6 * (|P3| * A1 ^ 2 * |B1| * M ^ 3) * M * (1 - γ ^ 2)
          ≤ 6 * (6912 * S ^ 2 * M) * M * (1 - γ ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h5 (by norm_num)) (by positivity)) (by positivity)
        _ = 41472 * (S ^ 2 * (1 - γ ^ 2)) * M ^ 2 := by ring
        _ ≤ 41472 * (16 * M) * M ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSk (by norm_num)) (by positivity)
        _ = 663552 * M ^ 3 := by ring
    exact le_of_mul_le_mul_right hX (by positivity)
  have hT3 : 3 * |P2 * B1 ^ 2| * M * (1 - γ ^ 2) ≤ 6912 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ B1 ^ 2)]
    have h5 : |P2| * B1 ^ 2 * M ^ 2 ≤ 144 * S ^ 2 := by
      calc |P2| * B1 ^ 2 * M ^ 2 = (|P2| * M ^ 2) * B1 ^ 2 := by ring
        _ ≤ 1 * (144 * S ^ 2) := mul_le_mul hP2' hB1sq (by positivity) (by norm_num)
        _ = 144 * S ^ 2 := by ring
    have hX : (3 * (|P2| * B1 ^ 2) * M * (1 - γ ^ 2)) * M ^ 2 ≤ 6912 * M ^ 2 := by
      rw [show (3 * (|P2| * B1 ^ 2) * M * (1 - γ ^ 2)) * M ^ 2
          = 3 * (|P2| * B1 ^ 2 * M ^ 2) * M * (1 - γ ^ 2) by ring]
      calc 3 * (|P2| * B1 ^ 2 * M ^ 2) * M * (1 - γ ^ 2) ≤ 3 * (144 * S ^ 2) * M * (1 - γ ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h5 (by norm_num)) (by positivity)) (by positivity)
        _ = 432 * (S ^ 2 * (1 - γ ^ 2)) * M := by ring
        _ ≤ 432 * (16 * M) * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSk (by norm_num)) (by positivity)
        _ = 6912 * M ^ 2 := by ring
    exact le_of_mul_le_mul_right hX (by positivity)
  have hT4 : 4 * |P2 * A1 * C1| * M * (1 - γ ^ 2) ≤ 9216 := by
    rw [abs_mul, abs_mul]
    have h5 : |P2| * |A1| * |C1| * M ^ 2 ≤ 576 * S * Real.sqrt M := by
      calc |P2| * |A1| * |C1| * M ^ 2 = (|P2| * M ^ 2) * (|A1| * |C1|) := by ring
        _ ≤ 1 * (576 * S * Real.sqrt M) :=
            mul_le_mul hP2' hACb (by positivity) (by norm_num)
        _ = 576 * S * Real.sqrt M := by ring
    have hX : (4 * (|P2| * |A1| * |C1|) * M * (1 - γ ^ 2)) * M ≤ 9216 * M := by
      rw [show (4 * (|P2| * |A1| * |C1|) * M * (1 - γ ^ 2)) * M
          = 4 * (|P2| * |A1| * |C1| * M ^ 2) * (1 - γ ^ 2) by ring]
      calc 4 * (|P2| * |A1| * |C1| * M ^ 2) * (1 - γ ^ 2)
          ≤ 4 * (576 * S * Real.sqrt M) * (1 - γ ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) (by positivity)
        _ = 2304 * (S * (1 - γ ^ 2)) * Real.sqrt M := by ring
        _ ≤ 2304 * (4 * Real.sqrt M) * Real.sqrt M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSk' (by norm_num)) (by positivity)
        _ = 9216 * M := by
          have h2 : Real.sqrt M * Real.sqrt M = M := by rw [← pow_two, Real.sq_sqrt hMpos.le]
          rw [show 2304 * (4 * Real.sqrt M) * Real.sqrt M = 9216 * (Real.sqrt M * Real.sqrt M) by ring,
            h2]
    exact le_of_mul_le_mul_right hX (by positivity)
  have hT5 : 24 * |P1| * M * (1 - γ ^ 2) ≤ 24 := by
    have h5 : |P1| * M * (1 - γ ^ 2) ≤ 1 := by
      calc |P1| * M * (1 - γ ^ 2) = (|P1| * M) * (1 - γ ^ 2) := by ring
        _ ≤ 1 * 1 := mul_le_mul hP1' (by nlinarith [sq_nonneg γ]) (by positivity) (by norm_num)
        _ = 1 := by ring
    calc 24 * |P1| * M * (1 - γ ^ 2) = 24 * (|P1| * M * (1 - γ ^ 2)) := by ring
      _ ≤ 24 * 1 := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = 24 := by ring
  have htri : |P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2) + 4 * (P2 * A1 * C1) + 24 * P1|
      ≤ |P4 * A1 ^ 4| + 6 * |P3 * A1 ^ 2 * B1| + 3 * |P2 * B1 ^ 2| + 4 * |P2 * A1 * C1| + 24 * |P1| := by
    have h6 : |6 * (P3 * A1 ^ 2 * B1)| = 6 * |P3 * A1 ^ 2 * B1| := by
      rw [abs_mul]; norm_num
    have h7 : |3 * (P2 * B1 ^ 2)| = 3 * |P2 * B1 ^ 2| := by rw [abs_mul]; norm_num
    have h8 : |4 * (P2 * A1 * C1)| = 4 * |P2 * A1 * C1| := by rw [abs_mul]; norm_num
    have h9 : |24 * P1| = 24 * |P1| := by rw [abs_mul]; norm_num
    calc |P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2) + 4 * (P2 * A1 * C1) + 24 * P1|
        ≤ |P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2) + 4 * (P2 * A1 * C1)| + |24 * P1| :=
          abs_add_le _ _
      _ ≤ (|P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2)| + |4 * (P2 * A1 * C1)|) + |24 * P1| := by
          gcongr; exact abs_add_le _ _
      _ ≤ ((|P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1)| + |3 * (P2 * B1 ^ 2)|) + |4 * (P2 * A1 * C1)|) + |24 * P1| := by
          gcongr; exact abs_add_le _ _
      _ ≤ (((|P4 * A1 ^ 4| + |6 * (P3 * A1 ^ 2 * B1)|) + |3 * (P2 * B1 ^ 2)|) + |4 * (P2 * A1 * C1)|) + |24 * P1| := by
          gcongr; exact abs_add_le _ _
      _ = |P4 * A1 ^ 4| + 6 * |P3 * A1 ^ 2 * B1| + 3 * |P2 * B1 ^ 2| + 4 * |P2 * A1 * C1| + 24 * |P1| := by
          rw [h6, h7, h8, h9]
  have hfinal : |iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁| * M * (1 - γ ^ 2) ≤ 10 ^ 7 := by
    rw [hfab]
    calc |P4 * A1 ^ 4 + 6 * (P3 * A1 ^ 2 * B1) + 3 * (P2 * B1 ^ 2) + 4 * (P2 * A1 * C1) + 24 * P1| * M * (1 - γ ^ 2)
        ≤ (|P4 * A1 ^ 4| + 6 * |P3 * A1 ^ 2 * B1| + 3 * |P2 * B1 ^ 2| + 4 * |P2 * A1 * C1| + 24 * |P1|) * M * (1 - γ ^ 2) := by
          gcongr
      _ = |P4 * A1 ^ 4| * M * (1 - γ ^ 2) + 6 * |P3 * A1 ^ 2 * B1| * M * (1 - γ ^ 2)
            + 3 * |P2 * B1 ^ 2| * M * (1 - γ ^ 2) + 4 * |P2 * A1 * C1| * M * (1 - γ ^ 2)
            + 24 * |P1| * M * (1 - γ ^ 2) := by ring
      _ ≤ 5308416 + 663552 + 6912 + 9216 + 24 := by linarith [hT1, hT2, hT3, hT4, hT5]
      _ ≤ 10 ^ 7 := by norm_num
  calc |iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁|
      = (|iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁| * M * (1 - γ ^ 2)) * (M * (1 - γ ^ 2))⁻¹ := by
        field_simp
    _ ≤ 10 ^ 7 * (M * (1 - γ ^ 2))⁻¹ := mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = 10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹ := by rw [mul_inv]; ring




/-- **The volume of the region** (delegated to `Submission.Work.FIArea2.lemma_7_1_volume` once
available). -/
lemma volume_reg_le_aux (M γ : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∫ p : ℝ × ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) p
      ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
  lemma_7_1_volume M γ hM hγ0 hγ1

/-- The pointwise bound `‖∂₁⁴(f∘g)‖ ≤ 10^7 M⁻¹(1−γ²)⁻¹·1_{(7.4)}`. -/
lemma deriv4_pointwise (M γ : ℝ) (f : ℝ → ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ))) (t₁ t₂ : ℝ) :
    ‖iteratedDeriv 4 (fun s : ℝ => (f (gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹ * Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂) := by
  have hφ : ContDiff ℝ 4 (fun s : ℝ => f (gq γ s t₂)) := by
    simp only [gq]; fun_prop
  rw [iteratedDeriv_ofReal_comp (fun s : ℝ => f (gq γ s t₂)) hφ (le_refl 4) t₁,
    Complex.norm_real, Real.norm_eq_abs]
  by_cases hmem : (t₁, t₂) ∈ reg M γ
  · rw [Set.indicator_of_mem hmem, mul_one]
    exact deriv4_bound_aux M γ f hM hγ0 hγ1 hf hfd t₁ t₂ hmem
  · rw [Set.indicator_of_notMem hmem, mul_zero]
    have hz := iteratedDeriv4_biquadratic_eq_zero M γ f hfsupp t₁ t₂ (fun h => hmem h)
    have hz' : iteratedDeriv 4 (fun s : ℝ => f (gq γ s t₂)) t₁ = 0 := hz
    rw [hz', abs_zero]

lemma integrable_indicator_Icc (R : ℝ) :
    Integrable (Set.indicator (Set.Icc (-R) R) (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne)

lemma reg_slice_subset (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (t₂ : ℝ) :
    {t₁ : ℝ | (t₁, t₂) ∈ reg M γ} ⊆
      Set.Icc (-Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)))
        (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) := by
  intro t₁ ht
  have h4δ : 0 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by
    have := Real.sqrt_pos.mpr (one_sub_gamma_sq_pos γ hγ0 hγ1); positivity
  have hRnn : 0 ≤ Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) := Real.sqrt_nonneg _
  have hR2 : (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) ^ 2
      = 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := Real.sq_sqrt h4δ
  have hsum : t₁ ^ 2 + t₂ ^ 2 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) :=
    reg_subset M γ hM hγ0 hγ1 ht
  have h1 : t₁ ^ 2 ≤ (Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) ^ 2 := by
    rw [hR2]; linarith [sq_nonneg t₂]
  have habs : |t₁| ≤ Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) :=
    calc |t₁| = Real.sqrt (t₁ ^ 2) := (Real.sqrt_sq_eq_abs t₁).symm
      _ ≤ Real.sqrt ((Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2))) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) := Real.sqrt_sq hRnn
  simp only [Set.mem_Icc]
  exact ⟨by linarith [neg_abs_le t₁], by linarith [le_abs_self t₁]⟩

lemma integrable_indicator_reg_slice (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (t₂ : ℝ) :
    Integrable (fun t₁ : ℝ => Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
  have hmeas : MeasurableSet {t₁ : ℝ | (t₁, t₂) ∈ reg M γ} :=
    (isClosed_reg M γ).measurableSet.preimage (by fun_prop)
  have hfin : volume {t₁ : ℝ | (t₁, t₂) ∈ reg M γ} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (reg_slice_subset M γ hM hγ0 hγ1 t₂)) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  exact (integrable_indicator_iff hmeas).mpr (integrableOn_const (C := (1 : ℝ)) (ne_of_lt hfin))

lemma norm_FintInt_le_indicator (M γ : ℝ) (f : ℝ → ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hfb : ∀ u, |f u| ≤ 1)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (u₁ u₂ : ℝ) (p : ℝ × ℝ) :
    ‖FintInt f γ u₁ u₂ p‖ ≤ Set.indicator (reg M γ) (fun _ => (1 : ℝ)) p := by
  rw [FintInt, norm_mul]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2) : ℂ)
        = ((2 * Real.pi * (u₁ * p.1 + u₂ * p.2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  by_cases hp : p ∈ reg M γ
  · rw [Set.indicator_of_mem hp, Complex.norm_real]
    exact hfb _
  · rw [Set.indicator_of_notMem hp]
    have hzero : f (gq γ p.1 p.2) = 0 :=
      f_gq_eq_zero M γ f hfsupp (fun h => hp ⟨h.1, h.2⟩)
    rw [hzero, Complex.ofReal_zero, norm_zero]

/-- The integrand of (7.1) is integrable: continuous, bounded by the indicator of (7.4). -/
lemma integrable_FintInt (M γ : ℝ) (f : ℝ → ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : Continuous f) (hfb : ∀ u, |f u| ≤ 1)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) (u₁ u₂ : ℝ) :
    Integrable (FintInt f γ u₁ u₂) := by
  have hcont : Continuous (fun p : ℝ × ℝ => ((f (gq γ p.1 p.2) : ℝ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * (u₁ * p.1 + u₂ * p.2))) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (hf.comp (by simp only [gq]; fun_prop))
    · fun_prop
  have hcont' : Continuous (FintInt f γ u₁ u₂) := hcont
  refine Integrable.mono' (integrable_indicator_reg M γ hM hγ0 hγ1) hcont'.aestronglyMeasurable ?_
  filter_upwards with p
  exact norm_FintInt_le_indicator M γ f hM hγ0 hγ1 hfb hfsupp u₁ u₂ p

/-! ### The three bounds on `F` -/

/-- Bound (i): the trivial bound `‖F‖ ≤ 30√M log(2 + δ⁻²)`. -/
lemma Fint_le_trivial (M γ : ℝ) (f : ℝ → ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ)))
    (u₁ u₂ : ℝ) :
    ‖Fint f γ u₁ u₂‖ ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have hint := integrable_FintInt M γ f hM0 hγ0 hγ1 hf.continuous (abs_f_le_one M f hfd) hfsupp u₁ u₂
  have hFeq : Fint f γ u₁ u₂ = ∫ p : ℝ × ℝ, FintInt f γ u₁ u₂ p := by
    rw [Fint]; rfl
  calc ‖Fint f γ u₁ u₂‖ = ‖∫ p : ℝ × ℝ, FintInt f γ u₁ u₂ p‖ := by rw [hFeq]
    _ ≤ ∫ p : ℝ × ℝ, ‖FintInt f γ u₁ u₂ p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) p := by
        refine integral_mono hint.norm (integrable_indicator_reg M γ hM0 hγ0 hγ1) ?_
        exact fun p => norm_FintInt_le_indicator M γ f hM0 hγ0 hγ1 (abs_f_le_one M f hfd) hfsupp u₁ u₂ p
    _ ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := volume_reg_le_aux M γ hM hγ0 hγ1

/-- Bound (ii): the four-fold integration by parts in `t₁`. -/
lemma Fint_le_deriv (M γ : ℝ) (f : ℝ → ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ)))
    (u₁ u₂ : ℝ) (hu₁ : u₁ ≠ 0) :
    ‖Fint f γ u₁ u₂‖ ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4
      * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
      * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
  have hM0 : 0 < M := by linarith
  have hC0 : 0 ≤ 10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹ := by
    have := one_sub_gamma_sq_pos γ hγ0 hγ1; positivity
  have hint := integrable_FintInt M γ f hM0 hγ0 hγ1 hf.continuous (abs_f_le_one M f hfd) hfsupp u₁ u₂
  have hFint := Fint_eq_iterated f γ u₁ u₂ hint
  -- pointwise bound for the inner sections
  have hinner : ∀ t₂ : ℝ, ‖∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖
      ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4
        * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹) * ∫ t₁ : ℝ,
            Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
    intro t₂
    obtain ⟨hcd, hintd⟩ := contDiff_integrable_hfun M γ f hM0 hγ0 hγ1 hf hfsupp t₂
    have hsplit : (∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂)))
        = (∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁)))
          * Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂)) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with t₁
      rw [show Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))
          = Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁))
            * Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂)) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    have hexp2 : ‖Complex.exp (2 * Real.pi * Complex.I * (u₂ * t₂))‖ = 1 := by
      rw [show (2 * Real.pi * Complex.I * (u₂ * t₂) : ℂ)
          = ((2 * Real.pi * (u₂ * t₂) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hsplit, norm_mul, hexp2, mul_one]
    refine (fourier_decay _ u₁ hu₁ hcd hintd).trans ?_
    gcongr
    refine (integral_mono (hintd 4 (le_refl 4)).norm
      ((integrable_indicator_reg_slice M γ hM0 hγ0 hγ1 t₂).const_mul
        (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)) ?_).trans (le_of_eq ?_)
    · intro t₁
      exact deriv4_pointwise M γ f hM hγ0 hγ1 hf hfsupp hfd t₁ t₂
    · rw [integral_const_mul]
  -- integrability of the majorant
  have hmaj : Integrable (fun t₂ : ℝ => (2 * Real.pi * |u₁|)⁻¹ ^ 4
      * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
        * ∫ t₁ : ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂))) := by
    have hsec : Integrable (fun t₂ : ℝ => ∫ t₁ : ℝ,
        Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂)) :=
      Integrable.integral_prod_right (integrable_indicator_reg M γ hM0 hγ0 hγ1)
    exact (hsec.const_mul _).const_mul _
  calc ‖Fint f γ u₁ u₂‖
      = ‖∫ t₂ : ℝ, ∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖ := by rw [hFint]
    _ ≤ ∫ t₂ : ℝ, ‖∫ t₁ : ℝ, ((f (gq γ t₁ t₂) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t₁ + u₂ * t₂))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t₂ : ℝ, (2 * Real.pi * |u₁|)⁻¹ ^ 4
          * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
            * ∫ t₁ : ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hmaj
          (Filter.Eventually.of_forall fun t₂ => hinner t₂)
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4 * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * ∫ t₂ : ℝ, ∫ t₁ : ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) (t₁, t₂)) := by
        rw [integral_const_mul, integral_const_mul]
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4 * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * ∫ p : ℝ × ℝ, Set.indicator (reg M γ) (fun _ => (1 : ℝ)) p) := by
        congr 2
        exact (integral_prod_symm (fun p : ℝ × ℝ => Set.indicator (reg M γ) (fun _ => (1 : ℝ)) p)
          (integrable_indicator_reg M γ hM0 hγ0 hγ1)).symm
    _ ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4 * ((10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) := by
        have hvol := volume_reg_le_aux M γ hM hγ0 hγ1
        have hK0 : 0 ≤ (2 * Real.pi * |u₁|)⁻¹ ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol hC0) hK0
    _ = (2 * Real.pi * |u₁|)⁻¹ ^ 4 * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by ring

/-- The algebra converting the integration-by-parts bound into the shape `B/x²`: multiplying by
`(u²√(1−γ²)√M)²` turns the factor `(2π|u|)^{-4}M^{-1}(1−γ²)^{-1}` into `(2π)^{-4}`. -/
lemma sq_mul_le (M γ u F : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hu : u ≠ 0)
    (h : F ≤ (2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
        * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) :
    (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 * F
      ≤ (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 7 * 30) * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have h1γ : 0 < 1 - γ ^ 2 := one_sub_gamma_sq_pos γ hγ0 hγ1
  have hsq : (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 = u ^ 4 * (1 - γ ^ 2) * M := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h1γ.le, Real.sq_sqrt hM0.le]
    ring
  have habs : (|u| : ℝ) ^ 4 = u ^ 4 := by
    rw [show (|u| : ℝ) ^ 4 = ((|u| : ℝ) ^ 2) ^ 2 by ring,
      show u ^ 4 = (u ^ 2) ^ 2 by ring, sq_abs]
  have hkey : (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
      * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹))
      = (2 * Real.pi)⁻¹ ^ 4 * 10 ^ 7 := by
    rw [hsq, inv_pow, mul_pow, habs, inv_pow]
    field_simp
  have hnonneg : 0 ≤ (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 := sq_nonneg _
  calc (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2 * F
      ≤ (u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
        * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))) :=
        mul_le_mul_of_nonneg_left h hnonneg
    _ = ((u ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M) ^ 2
          * ((2 * Real.pi * |u|)⁻¹ ^ 4 * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)))
        * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by ring
    _ = ((2 * Real.pi)⁻¹ ^ 4 * 10 ^ 7) * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
        rw [hkey]
    _ = (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 7 * 30) * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
        ring

/-- **Lemma 7.1 of FI** ((7.5)), for the Fourier integral (7.1)
`F(u₁,u₂) = ∫∫ f(t₁⁴−2γt₁²t₂²+t₂⁴)e(u₁t₁+u₂t₂)dt₁dt₂` (`Work.FIArea2.Fint`) and a `C⁴` function
`f` supported in `[M/4,4M]` with `|f^{(j)}| ≤ M^{-j}` (`j ≤ 4`), which is exactly what the paper
assumes in §7:

  `‖F(u₁,u₂)‖ ≤ C·(1 + u₁²δ√M)^{−1}(1 + u₂²δ√M)^{−1}·√M·log(2 + δ^{−2})`,  `δ² = 1 − γ²`.

For `u_j = h_j|Δz_j|^{−1/2}` and `z_j` in the polar box (`|z_j|² ≍ N`, `|Δ| = δ|z₁z₂|`) the factor
is the paper's `(1 + h_j²H^{−2})^{−1}` with `H = M^{−1/4}N^{3/4}`, since
`u_j²δ√M = h_j²√M/(|z_j||z₁z₂|) = h_j²/H²`; the log `log N` of (7.5) is replaced by the
equivalent `log(2+δ^{−2})` (by (7.3), `δ ≥ (2N)^{−1}`), which is `≥ log δ^{−2}`.  The constant
`10^6` is deliberately generous; any explicit absolute constant is acceptable and the statement
may be weakened to `∃ C` if the explicit constant is the only obstruction (keep the shape
`(1+u₁²δ√M)^{−1}(1+u₂²δ√M)^{−1}√M log(2+δ^{−2})`).

Route (§7): (i) `supp(f∘g)` is contained in the region bounded in
`Work.FIArea2.biquadratic_ellipse_bounds`, of area `O(√M log δ^{−2})`, giving
`‖F‖ ≤ C√M log(2+δ^{−2})`; (ii) four integrations by parts in `t₁` give
`F = (2πi u₁)^{−4}∫∫ (∂⁴/∂t₁⁴)(f∘g)·e(·)`, and Faà di Bruno for the quartic `g` together with
`|f^{(j)}| ≤ M^{−j}` and the region bounds give `|∂⁴_{t₁}(f∘g)| ≤ C δ^{−2}M^{−1}` there, hence
`‖F‖ ≤ C u₁^{−4}δ^{−2}M^{−1/2}log(2+δ^{−2})`; (iii) the same in `t₂`, and the geometric mean of
the three bounds gives the product form. -/
theorem lemma_7_1 (M : ℝ) (hM : 1 ≤ M) (f : ℝ → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ)))
    (u₁ u₂ : ℝ) :
    ‖Work.FIArea2.Fint f γ u₁ u₂‖
      ≤ 10 ^ 6 * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
          * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
          * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have h1γ : 0 < 1 - γ ^ 2 := one_sub_gamma_sq_pos γ hγ0 hγ1
  set L : ℝ := Real.log (2 + 1 / (1 - γ ^ 2)) with hL
  have hLpos : 0 < L := by
    rw [hL]
    apply Real.log_pos
    have : 0 < 1 / (1 - γ ^ 2) := by positivity
    linarith
  set x : ℝ := u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M with hx
  set y : ℝ := u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M with hy
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  set A : ℝ := 30 * Real.sqrt M * L with hAdef
  set B : ℝ := (2 * Real.pi)⁻¹ ^ 4 * (10 ^ 7 * 30) * Real.sqrt M * L with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hF0 : 0 ≤ ‖Fint f γ u₁ u₂‖ := norm_nonneg _
  have hAbound : ‖Fint f γ u₁ u₂‖ ≤ A := by
    rw [hAdef, hL]
    exact Fint_le_trivial M γ f hM hγ0 hγ1 hf hfsupp hfd u₁ u₂
  have hBbound : x ^ 2 * ‖Fint f γ u₁ u₂‖ ≤ B := by
    rcases eq_or_ne u₁ 0 with h0 | h0
    · have hx0' : x = 0 := by rw [hx, h0]; ring
      have hzero : x ^ 2 * ‖Fint f γ u₁ u₂‖ = 0 := by rw [hx0']; ring
      rw [hzero]
      exact hB0
    · have h1 := Fint_le_deriv M γ f hM hγ0 hγ1 hf hfsupp hfd u₁ u₂ h0
      rw [hx, hBdef, hL]
      exact sq_mul_le M γ u₁ _ hM hγ0 hγ1 h0 h1
  have hCbound : y ^ 2 * ‖Fint f γ u₁ u₂‖ ≤ B := by
    rcases eq_or_ne u₂ 0 with h0 | h0
    · have hy0' : y = 0 := by rw [hy, h0]; ring
      have hzero : y ^ 2 * ‖Fint f γ u₁ u₂‖ = 0 := by rw [hy0']; ring
      rw [hzero]
      exact hB0
    · have h1 := Fint_le_deriv M γ f hM hγ0 hγ1 hf hfsupp hfd u₂ u₁ h0
      have h2 : ‖Fint f γ u₁ u₂‖ ≤ (2 * Real.pi * |u₂|)⁻¹ ^ 4
          * (10 ^ 7 * M⁻¹ * (1 - γ ^ 2)⁻¹)
          * (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
        rw [Fint_swap f γ u₁ u₂]
        exact h1
      rw [hy, hBdef, hL]
      exact sq_mul_le M γ u₂ _ hM hγ0 hγ1 h0 h2
  have hcomb := combine_bounds x y A B B ‖Fint f γ u₁ u₂‖ hx0 hy0 hA0 hB0 hB0 hF0
    hAbound hBbound hCbound
  have hden : 0 < (1 + x) * (1 + y) := by positivity
  have hBsmall : B ≤ 25 * 10 ^ 4 * Real.sqrt M * L := by
    rw [hBdef]
    have hinv : (2 * Real.pi)⁻¹ ^ 4 ≤ (1200 : ℝ)⁻¹ := by
      rw [inv_pow]
      refine (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 1200)).mpr ?_
      have h3 : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 :=
        pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 4
      nlinarith
    nlinarith [hinv, hLpos, hsqrtM]
  have hA' : A ≤ 25 * 10 ^ 4 * Real.sqrt M * L := by
    rw [hAdef]
    nlinarith [hLpos, hsqrtM]
  have hmax : 4 * max A (max B B) ≤ 10 ^ 6 * Real.sqrt M * L := by
    have h1 : max B B ≤ 25 * 10 ^ 4 * Real.sqrt M * L := le_of_eq_of_le (max_self B) hBsmall
    have h2 : max A (max B B) ≤ 25 * 10 ^ 4 * Real.sqrt M * L := max_le hA' h1
    linarith
  calc ‖Fint f γ u₁ u₂‖ ≤ 4 * max A (max B B) / ((1 + x) * (1 + y)) := hcomb
    _ ≤ 10 ^ 6 * Real.sqrt M * L / ((1 + x) * (1 + y)) :=
        div_le_div_of_nonneg_right hmax hden.le
    _ = 10 ^ 6 * (1 + x)⁻¹ * (1 + y)⁻¹ * Real.sqrt M * L := by
        rw [div_eq_mul_inv, mul_inv]
        ring

end

end Work.FIArea2
