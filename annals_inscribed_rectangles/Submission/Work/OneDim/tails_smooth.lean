import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.ift_real

/-!
# Gluing two parametrisations of the ends of `ℝ` into a diffeomorphism of `ℝ`

Given a `C^∞` strictly increasing map `f` on `[T₀,∞)` with `f → +∞` at `+∞` and a `C^∞`
strictly increasing map `g` on `(-∞,-T₀]` with `g → -∞` at `-∞`, we construct a diffeomorphism
`Φ` of `ℝ` which agrees with `f` far to the right and with `g` far to the left.

The construction is by a convex combination `Φ = F·θ + G·(1-θ)` where `F, G` are smooth
non-decreasing *global* extensions of `f` and `g` obtained by composing with a smooth
"saturation" map, and `θ` is a smooth step.  All the analytic content sits in
`deriv_smoothTransition_pos_sm`.
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace Work.OneDim

noncomputable section

/-- `Real.smoothTransition` has strictly positive derivative on `(0,1)`. -/
theorem deriv_smoothTransition_pos_sm {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    0 < deriv Real.smoothTransition x := by
  have h1x : 0 < 1 - x := by linarith
  have hformula : Real.smoothTransition =ᶠ[𝓝 x]
      (fun y => 1 / (1 + Real.exp (y⁻¹ - (1-y)⁻¹))) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := hy.2
    have h1y : 0 < 1 - y := by linarith
    have hyy : expNegInvGlue y = Real.exp (-(y⁻¹)) := by
      simp only [expNegInvGlue, if_neg (not_le.mpr hy0)]
    have h1yy : expNegInvGlue (1 - y) = Real.exp (-((1-y)⁻¹)) := by
      simp only [expNegInvGlue, if_neg (not_le.mpr h1y)]
    rw [Real.smoothTransition, hyy, h1yy,
      show Real.exp (-(y⁻¹)) = (Real.exp y⁻¹)⁻¹ from Real.exp_neg y⁻¹,
      show Real.exp (-((1-y)⁻¹)) = (Real.exp ((1-y)⁻¹))⁻¹ from Real.exp_neg ((1-y)⁻¹),
      Real.exp_sub]
    rw [div_eq_iff (by positivity)]
    field_simp
  rw [hformula.deriv_eq]
  have hA : HasDerivAt (fun y : ℝ => y⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv h0.ne'
  have hB : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (1/(1-x)^2) x := by
    have h2 : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (-(-1)/(1-x)^2) x := by
      have h3 : HasDerivAt (fun y : ℝ => (1 - y)) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1:ℝ)
      exact h3.inv (by linarith : (1 - x) ≠ 0)
    convert h2 using 1
    ring
  have hAB : HasDerivAt (fun y : ℝ => y⁻¹ - (1 - y)⁻¹)
      (-(x^2)⁻¹ - 1/(1-x)^2) x := hA.sub hB
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (y⁻¹ - (1 - y)⁻¹))
      (Real.exp (x⁻¹ - (1-x)⁻¹) * (-(x^2)⁻¹ - 1/(1-x)^2)) x := hAB.exp
  have hadd : HasDerivAt (fun y : ℝ => 1 + Real.exp (y⁻¹ - (1 - y)⁻¹))
      (Real.exp (x⁻¹ - (1-x)⁻¹) * (-(x^2)⁻¹ - 1/(1-x)^2)) x := hexp.const_add 1
  have hpos : (0:ℝ) < 1 + Real.exp (x⁻¹ - (1-x)⁻¹) := by positivity
  have hinv := hadd.inv hpos.ne'
  have hgoal : (fun y => 1 / (1 + Real.exp (y⁻¹ - (1-y)⁻¹)))
      = ((fun y => 1 + Real.exp (y⁻¹ - (1-y)⁻¹)))⁻¹ := by
    funext y; rw [one_div]; rfl
  rw [hgoal, hinv.deriv]
  have hB' : -(x^2)⁻¹ - 1/(1-x)^2 < 0 := by
    have h1 : (0:ℝ) < (x^2)⁻¹ := inv_pos.mpr (pow_pos h0 2)
    have h2 : (0:ℝ) < (1/(1-x)^2) := by positivity
    linarith
  apply div_pos
  · rw [neg_pos]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) hB'
  · positivity

/-- **Gluing the two ends of `ℝ`.** -/
theorem exists_diffeomorph_tails_smooth {T₀ : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ sm f (Set.Ici T₀))
    (hg : ContDiffOn ℝ sm g (Set.Iic (-T₀)))
    (hfderiv : ∀ t, T₀ ≤ t → 0 < deriv f t)
    (hgderiv : ∀ t, t ≤ -T₀ → 0 < deriv g t)
    (hftop : Filter.Tendsto f Filter.atTop Filter.atTop)
    (hgbot : Filter.Tendsto g Filter.atBot Filter.atBot) :
    ∃ (Φ : Diffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ
        Work.OneDim.sm) (T : ℝ),
      T₀ ≤ T ∧ (∀ t, T ≤ t → Φ t = f t) ∧ (∀ t, t ≤ -T → Φ t = g t) := by
  classical
  -- ### Step 1: choose a point `c` far out on both sides at once
  obtain ⟨c, hc_gt, hfc, hgc⟩ : ∃ c : ℝ, T₀ < c ∧ 0 < f c ∧ g (-c) < 0 := by
    obtain ⟨C₁, hC₁⟩ := Filter.eventually_atTop.mp
      (hftop.eventually (eventually_gt_atTop 0))
    obtain ⟨C₂, hC₂⟩ := Filter.eventually_atBot.mp
      (hgbot.eventually (eventually_lt_atBot 0))
    refine ⟨max (T₀ + 1) (max C₁ (-C₂ + 1)), ?_, ?_, ?_⟩
    · have : T₀ + 1 ≤ max (T₀ + 1) (max C₁ (-C₂ + 1)) := le_max_left _ _
      linarith
    · exact hC₁ _ (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact hC₂ _ (by
        have h : -C₂ + 1 ≤ max (T₀ + 1) (max C₁ (-C₂ + 1)) :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        linarith)
  -- ### Step 2: the transition radius `A`
  set A : ℝ := max (c + 1) 0 + 1 with hAdef
  have hA_pos : 0 < A := by
    have := le_max_right (c + 1) (0:ℝ); rw [hAdef]; linarith
  have hA_gt_c : c + 1 < A := by
    rw [hAdef]
    by_cases h : 0 ≤ c + 1
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right (le_of_lt (not_le.mp h))]; linarith
  have hA_ge_T : T₀ ≤ A := by linarith
  -- ### Step 3: the two saturation maps and the two extended functions
  let φ : ℝ → ℝ := fun t => c + (t - c) * Real.smoothTransition (t - c)
  let ψ : ℝ → ℝ := fun t => -φ (-t)
  let F : ℝ → ℝ := fun t => f (φ t)
  let G : ℝ → ℝ := fun t => g (ψ t)
  let θ : ℝ → ℝ := fun t => Real.smoothTransition ((t + A) / (2 * A))
  let Φ : ℝ → ℝ := fun t => F t * θ t + G t * (1 - θ t)
  have htwoA : (0:ℝ) < 2 * A := by linarith
  -- facts about `φ`
  have hφmono : Monotone φ := by
    intro t s hts
    simp only [φ]
    have h1 : Real.smoothTransition (t - c) ≤ Real.smoothTransition (s - c) :=
      Real.smoothTransition.monotone (by linarith)
    by_cases h : 0 ≤ t - c
    · have h2 : 0 ≤ Real.smoothTransition (s - c) := Real.smoothTransition.nonneg _
      have h3 : t - c ≤ s - c := by linarith
      have h4 : (t - c) * Real.smoothTransition (t - c)
          ≤ (s - c) * Real.smoothTransition (s - c) :=
        calc (t - c) * Real.smoothTransition (t - c)
            ≤ (t - c) * Real.smoothTransition (s - c) := mul_le_mul_of_nonneg_left h1 h
          _ ≤ (s - c) * Real.smoothTransition (s - c) := mul_le_mul_of_nonneg_right h3 h2
      linarith
    · have h0 : Real.smoothTransition (t - c) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp h])
      rw [h0, mul_zero]
      have h4 : 0 ≤ (s - c) * Real.smoothTransition (s - c) := by
        by_cases hv : 0 ≤ s - c
        · exact mul_nonneg hv (Real.smoothTransition.nonneg _)
        · have h5 : Real.smoothTransition (s - c) = 0 :=
            Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp hv])
          rw [h5, mul_zero]
      linarith
  have hφ_ge : ∀ t, c ≤ φ t := by
    intro t
    simp only [φ]
    by_cases h : c ≤ t
    · have h1 : 0 ≤ t - c := by linarith
      have h2 : 0 ≤ Real.smoothTransition (t - c) := Real.smoothTransition.nonneg _
      linarith [mul_nonneg h1 h2]
    · have h0 : Real.smoothTransition (t - c) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp h])
      rw [h0, mul_zero]
      linarith
  have hφ_eq_self : ∀ t, c + 1 ≤ t → φ t = t := by
    intro t ht
    simp only [φ]
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - c)]
    ring
  have hφ_contDiff : ContDiff ℝ ∞ φ := by
    simp only [φ]; fun_prop
  have hφ_mem : ∀ t, φ t ∈ Ici T₀ := fun t => mem_Ici.mpr (by linarith [hφ_ge t, hc_gt])
  -- facts about `ψ`
  have hψ_contDiff : ContDiff ℝ ∞ ψ := by
    simp only [ψ]; fun_prop
  have hψ_mono : Monotone ψ := by
    intro t s hts
    simp only [ψ]
    have := hφmono (by linarith : -s ≤ -t)
    linarith
  have hψ_eq_self : ∀ t, t ≤ -c - 1 → ψ t = t := by
    intro t ht
    simp only [ψ]
    rw [hφ_eq_self (-t) (by linarith)]
    ring
  have hψ_le : ∀ t, ψ t ≤ -c := by
    intro t
    simp only [ψ]
    linarith [hφ_ge (-t)]
  have hψ_mem : ∀ t, ψ t ∈ Iic (-T₀) := fun t => mem_Iic.mpr (by linarith [hψ_le t, hc_gt])
  -- monotonicity of `f` and `g` on their half-lines (from the derivative hypotheses)
  have hfmono : MonotoneOn f (Ici T₀) :=
    (strictMonoOn_of_deriv_pos (convex_Ici T₀) hf.continuousOn (fun x hx => by
      rw [interior_Ici] at hx
      exact hfderiv x (le_of_lt hx))).monotoneOn
  have hgmono : MonotoneOn g (Iic (-T₀)) :=
    (strictMonoOn_of_deriv_pos (convex_Iic (-T₀)) hg.continuousOn (fun x hx => by
      rw [interior_Iic] at hx
      exact hgderiv x (le_of_lt hx))).monotoneOn
  -- ### Step 4: smoothness of `F = f ∘ φ` and `G = g ∘ ψ`
  have hF_contDiff : ContDiff ℝ ∞ F := by
    have h := ContDiffOn.comp (f := φ) (g := f) (s := univ) (t := Ici T₀)
      hf hφ_contDiff.contDiffOn (fun t _ => hφ_mem t)
    rw [contDiffOn_univ] at h
    convert h using 1
    exact (Function.comp_def f φ).symm
  have hG_contDiff : ContDiff ℝ ∞ G := by
    have h := ContDiffOn.comp (f := ψ) (g := g) (s := univ) (t := Iic (-T₀))
      hg hψ_contDiff.contDiffOn (fun t _ => hψ_mem t)
    rw [contDiffOn_univ] at h
    convert h using 1
    exact (Function.comp_def g ψ).symm
  have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hFdiff : ∀ x, DifferentiableAt ℝ F x :=
    fun x => (hF_contDiff.differentiable hne).differentiableAt
  have hGdiff : ∀ x, DifferentiableAt ℝ G x :=
    fun x => (hG_contDiff.differentiable hne).differentiableAt
  have hFmono : Monotone F := by
    intro t s hts
    exact hfmono (hφ_mem t) (hφ_mem s) (hφmono hts)
  have hGmono : Monotone G := by
    intro t s hts
    exact hgmono (hψ_mem t) (hψ_mem s) (hψ_mono hts)
  have hF_ge : ∀ t, f c ≤ F t := fun t =>
    hfmono (mem_Ici.mpr (le_of_lt hc_gt)) (hφ_mem t) (hφ_ge t)
  have hG_le : ∀ t, G t ≤ g (-c) := fun t =>
    hgmono (hψ_mem t) (mem_Iic.mpr (by linarith [hc_gt])) (hψ_le t)
  have hFG : ∀ t, G t < F t := by
    intro t
    have h1 : G t ≤ g (-c) := hG_le t
    have h2 : f c ≤ F t := hF_ge t
    linarith
  have hF_eq : ∀ t, c + 1 ≤ t → F t = f t := by
    intro t ht; simp only [F]; rw [hφ_eq_self t ht]
  have hG_eq : ∀ t, t ≤ -c - 1 → G t = g t := by
    intro t ht; simp only [G]; rw [hψ_eq_self t ht]
  -- `F` agrees with `f` near `A`, and `G` agrees with `g` near `-A`
  have hFf : F =ᶠ[𝓝 A] f := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (c+1:ℝ) < A by linarith)] with y hy
    exact hF_eq y (le_of_lt hy)
  have hGg : G =ᶠ[𝓝 (-A)] g := by
    filter_upwards [isOpen_Iio.mem_nhds (show (-A:ℝ) < -c-1 by linarith)] with y hy
    exact hG_eq y (le_of_lt hy)
  -- ### Step 5: the step function `θ`
  have hθ_contDiff : ContDiff ℝ ∞ θ := by simp only [θ]; fun_prop
  have hθdiff : ∀ x, DifferentiableAt ℝ θ x :=
    fun x => (hθ_contDiff.differentiable hne).differentiableAt
  have hθ_mono : Monotone θ := by
    intro x y hxy
    simp only [θ]
    apply Real.smoothTransition.monotone
    apply div_le_div_of_nonneg_right _ (le_of_lt htwoA)
    linarith
  have hθ_nonneg : ∀ x, 0 ≤ θ x := fun x => Real.smoothTransition.nonneg _
  have hθ_le_one : ∀ x, θ x ≤ 1 := fun x => Real.smoothTransition.le_one _
  have hθ_zero : ∀ t, t ≤ -A → θ t = 0 := by
    intro t ht
    simp only [θ]
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hθ_one : ∀ t, A ≤ t → θ t = 1 := by
    intro t ht
    simp only [θ]
    exact Real.smoothTransition.one_of_one_le (by
      rw [one_le_div htwoA]; linarith)
  -- ### Step 6: `Φ` and its derivative
  have hΦ_contDiff : ContDiff ℝ ∞ Φ := by
    simp only [Φ]
    fun_prop
  have hdΦ : ∀ x, deriv Φ x
      = deriv F x * θ x + deriv G x * (1 - θ x) + (F x - G x) * deriv θ x := by
    intro x
    have h1 : deriv (fun t => F t * θ t) x = deriv F x * θ x + F x * deriv θ x :=
      deriv_mul (hFdiff x) (hθdiff x)
    have h2 : deriv (fun t => G t * (1 - θ t)) x
        = deriv G x * (1 - θ x) + G x * deriv (fun t => 1 - θ t) x :=
      deriv_mul (hGdiff x) ((differentiableAt_const (1:ℝ)).sub (hθdiff x))
    have h3 : deriv (fun t => 1 - θ t) x = - deriv θ x := deriv_const_sub 1
    have hc1 : DifferentiableAt ℝ (fun t => F t * θ t) x := (hFdiff x).mul (hθdiff x)
    have hc2 : DifferentiableAt ℝ (fun t => G t * (1 - θ t)) x :=
      (hGdiff x).mul ((differentiableAt_const (1:ℝ)).sub (hθdiff x))
    have hΦeq : Φ = (fun t => F t * θ t) + (fun t => G t * (1 - θ t)) := rfl
    rw [hΦeq, deriv_add hc1 hc2, h1, h2, h3]
    ring
  -- positivity of the derivative of `θ` in the open transition interval
  have hdθ_pos : ∀ x, -A < x → x < A → 0 < deriv θ x := by
    intro x hxA hxA'
    have hu : deriv (fun t : ℝ => (t + A) / (2*A)) x = 1/(2*A) := by
      have h1 : HasDerivAt (fun t : ℝ => (t + A) / (2*A)) (1/(2*A)) x := by
        simpa using ((hasDerivAt_id x).add_const A).div_const (2*A)
      exact h1.deriv
    have hu0 : (0:ℝ) < (x + A)/(2*A) := div_pos (by linarith) htwoA
    have hu1 : (x + A)/(2*A) < 1 := by rw [div_lt_one htwoA]; linarith
    have hst : 0 < deriv Real.smoothTransition ((x + A)/(2*A)) :=
      deriv_smoothTransition_pos_sm hu0 hu1
    have hdiffst : DifferentiableAt ℝ Real.smoothTransition ((x + A)/(2*A)) := by fun_prop
    have hdiffu : DifferentiableAt ℝ (fun t : ℝ => (t + A)/(2*A)) x := by fun_prop
    have hcomp : deriv θ x = deriv Real.smoothTransition ((x + A)/(2*A))
        * deriv (fun t : ℝ => (t + A)/(2*A)) x := by
      have h := deriv_comp (x := x) (h := fun t : ℝ => (t + A)/(2*A))
        (h₂ := Real.smoothTransition) hdiffst hdiffu
      rw [Function.comp_def] at h
      exact h
    rw [hcomp, hu]
    positivity
  -- ### Step 7: `deriv Φ > 0` everywhere
  have hderiv_pos : ∀ x, 0 < deriv Φ x := by
    intro x
    rcases lt_trichotomy x (-A) with hx | hx | hx
    · -- x < -A: near x, Φ coincides with g
      have hΦg : Φ =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        have hyA : y ≤ -A := le_of_lt hy
        have hyc : y ≤ -c - 1 := by linarith
        simp only [Φ, hθ_zero y hyA, mul_zero, sub_zero, mul_one, zero_add, G,
          hG_eq y hyc]
      rw [hΦg.deriv_eq]
      exact hgderiv x (by linarith)
    · -- x = -A
      subst hx
      rw [hdΦ (-A), hθ_zero (-A) le_rfl]
      simp only [mul_zero, sub_zero, mul_one, zero_add]
      have hdG0 : 0 < deriv G (-A) := by
        rw [hGg.deriv_eq]
        exact hgderiv (-A) (by linarith)
      have h1 : 0 ≤ (F (-A) - G (-A)) * deriv θ (-A) :=
        mul_nonneg (by linarith [hFG (-A)]) hθ_mono.deriv_nonneg
      linarith
    · -- -A < x
      rcases lt_trichotomy x A with hx' | hx' | hx'
      · -- -A < x < A
        rw [hdΦ x]
        have h3 : 0 < (F x - G x) * deriv θ x :=
          mul_pos (by linarith [hFG x]) (hdθ_pos x hx hx')
        have h1 : 0 ≤ deriv F x * θ x := mul_nonneg hFmono.deriv_nonneg (hθ_nonneg x)
        have h2 : 0 ≤ deriv G x * (1 - θ x) :=
          mul_nonneg hGmono.deriv_nonneg (by linarith [hθ_le_one x])
        linarith
      · -- x = A
        subst hx'
        rw [hdΦ A, hθ_one A le_rfl]
        simp only [mul_one, sub_self, mul_zero, add_zero]
        have hdF0 : 0 < deriv F A := by
          rw [hFf.deriv_eq]
          exact hfderiv A (by linarith)
        have h1 : 0 ≤ (F A - G A) * deriv θ A :=
          mul_nonneg (by linarith [hFG A]) hθ_mono.deriv_nonneg
        linarith
      · -- A < x: near x, Φ coincides with f
        have hΦf : Φ =ᶠ[𝓝 x] f := by
          filter_upwards [isOpen_Ioi.mem_nhds hx'] with y hy
          have hyA : A ≤ y := le_of_lt hy
          have hyc : c + 1 ≤ y := by linarith
          simp only [Φ, hθ_one y hyA, mul_one, sub_self, mul_zero, add_zero, F,
            hF_eq y hyc]
        rw [hΦf.deriv_eq]
        exact hfderiv x (by linarith)
  -- ### Step 8: surjectivity and bijectivity of `Φ`
  have hΦ_strict : StrictMono Φ := by
    have h := strictMonoOn_of_deriv_pos (D := univ) convex_univ
      hΦ_contDiff.continuous.continuousOn (fun x _ => hderiv_pos x)
    simpa only [strictMonoOn_univ] using h
  have hΦ_bot : Tendsto Φ atBot atBot := by
    refine hgbot.congr' ?_
    filter_upwards [eventually_le_atBot (-A)] with y hy
    have hyc : y ≤ -c - 1 := by linarith
    simp only [Φ, hθ_zero y hy, mul_zero, sub_zero, mul_one, zero_add, G, hG_eq y hyc]
  have hΦ_top : Tendsto Φ atTop atTop := by
    refine hftop.congr' ?_
    filter_upwards [eventually_ge_atTop A] with y hy
    have hyc : c + 1 ≤ y := by linarith
    simp only [Φ, hθ_one y hy, mul_one, sub_self, mul_zero, add_zero, F, hF_eq y hyc]
  have hΦ_surj : Surjective Φ := by
    intro y
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp (hΦ_bot.eventually (eventually_lt_atBot y))
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp (hΦ_top.eventually (eventually_gt_atTop y))
    have ha' : Φ a < y := ha a le_rfl
    have hb' : y < Φ b := hb b le_rfl
    have hab : a ≤ b := by
      by_contra h
      have hba : b < a := not_le.mp h
      have := hΦ_strict hba
      linarith
    obtain ⟨t, _, hty⟩ := intermediate_value_Icc hab hΦ_contDiff.continuous.continuousOn
      ⟨le_of_lt ha', le_of_lt hb'⟩
    exact ⟨t, hty⟩
  -- ### Step 9: assemble the diffeomorphism
  have hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      Work.OneDim.sm Φ :=
    ift_real hΦ_contDiff (fun x => ne_of_gt (hderiv_pos x))
  have hbij : Function.Bijective Φ := ⟨hΦ_strict.injective, hΦ_surj⟩
  refine ⟨hld.diffeomorphOfBijective hbij, A, hA_ge_T, ?_, ?_⟩
  · intro t ht
    change Φ t = f t
    have htc : c + 1 ≤ t := by linarith
    have h1 : Φ t = F t := by
      simp only [Φ, hθ_one t ht, mul_one, sub_self, mul_zero, add_zero]
    rw [h1, hF_eq t htc]
  · intro t ht
    change Φ t = g t
    have htc : t ≤ -c - 1 := by linarith
    have h1 : Φ t = G t := by
      simp only [Φ, hθ_zero t ht, mul_zero, sub_zero, mul_one, zero_add]
    rw [h1, hG_eq t htc]

end

end Work.OneDim
