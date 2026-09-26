import Mathlib
import Submission.Work.Drive.KnotDefs
import Submission.Work.Drive.smallCorrectionKnot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology

/-! ## A uniform perturbation radius for an analytic family of knots

For an analytic family `R` whose slices `R · s`, `s ∈ [0,1]`, are smooth knots,
there is a radius `ρ > 0` such that perturbing *any* slice by an analytic
`period`-periodic correction smaller than `ρ` in `C⁰` and in `C¹` again gives a
smooth knot.  The proof combines the fixed-knot criterion `smallCorrectionKnot`
with the `C¹`-continuity of the family in the slice parameter. -/

/-- The velocity of a sum of curves. -/
private lemma velocity_add' {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u + g u) t = velocity f t + velocity g t := by
  have h : (fun u : ℝ => f u + g u) = f + g := rfl
  unfold velocity
  rw [h, deriv_add hf hg]

/-- The velocity of a difference of curves. -/
private lemma velocity_sub' {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u - g u) t = velocity f t - velocity g t := by
  have h : (fun u : ℝ => f u - g u) = f - g := rfl
  unfold velocity
  rw [h, deriv_sub hf hg]

/-- The canonical representative of `t` in the fundamental interval `[0, period]`. -/
private noncomputable def fwRed (t : ℝ) : ℝ := t - (⌊t / period⌋ : ℝ) * period

private lemma fwRed_mem (t : ℝ) : fwRed t ∈ Set.Icc (0 : ℝ) period := by
  have hT : 0 < period := period_pos
  have hk1 : ((⌊t / period⌋ : ℤ) : ℝ) ≤ t / period := Int.floor_le _
  have hk2 : t / period < ((⌊t / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have h : ((⌊t / period⌋ : ℤ) : ℝ) * period ≤ (t / period) * period :=
      mul_le_mul_of_nonneg_right hk1 (le_of_lt hT)
    have ht : (t / period) * period = t := by rw [div_mul_cancel₀ _ (ne_of_gt hT)]
    simp only [fwRed]
    linarith
  · have h : t < (((⌊t / period⌋ : ℤ) : ℝ) + 1) * period := by
      have := mul_lt_mul_of_pos_right hk2 hT
      rwa [div_mul_cancel₀ _ (ne_of_gt hT)] at this
    simp only [fwRed]
    linarith

/-- The `t`-derivative of a slice is the partial derivative of the two-variable map. -/
private lemma deriv_slice_eq_fderiv {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) (t s : ℝ) :
    deriv (fun u : ℝ => R u s) t =
      fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s) (1, 0) := by
  have hφ : HasFDerivAt (fun u : ℝ => (u, s)) (ContinuousLinearMap.inl ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_left t s
  have hF : HasFDerivAt (fun p : ℝ × ℝ => R p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s)) (t, s) :=
    ((hR.differentiable (by decide)).differentiableAt).hasFDerivAt
  have hfd := (hF.comp t hφ).fderiv
  rw [← fderiv_apply_one_eq_deriv (f := fun u : ℝ => R u s) (x := t)]
  change (fderiv ℝ ((fun p : ℝ × ℝ => R p.1 p.2) ∘ fun u : ℝ => (u, s)) t) 1
      = (fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s)) (1, 0)
  rw [hfd]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The partial `t`-derivative of an analytic two-variable map is continuous. -/
private lemma continuous_fderiv_partial {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) p (1, 0)) := by
  have h := hR.continuous_fderiv_apply (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
  exact h.comp (continuous_id.prodMk continuous_const)

/-- The velocity of a slice, identified with the partial derivative. -/
private lemma velocity_slice_eq {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) (t s : ℝ) :
    velocity (fun u : ℝ => R u s) t
      = fderiv ℝ (fun p : ℝ × ℝ => R p.1 p.2) (t, s) (1, 0) := by
  show deriv (fun u : ℝ => R u s) t = _
  exact deriv_slice_eq_fderiv hR t s

/-- The derivative of a periodic map is periodic. -/
private lemma periodic_deriv {f : ℝ → Space} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have hx : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by
    rw [show (fun y : ℝ => f (y + c)) = f from funext h]
  rwa [deriv_comp_add_const f c x] at hx

/-- **Two-sided `C¹`-window at an interior parameter.**  For every `s₀ ∈ [0,1]`
and every `γ > 0` the slices of the family are uniformly `C¹`-close to the slice
at `s₀` for slice parameters in a neighbourhood of `s₀`. -/
theorem familyWindowAt {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsSmoothKnot (fun t : ℝ => R t s))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, |s - s₀| ≤ δ → ∀ t : ℝ,
      ‖R t s - R t s₀‖ ≤ γ ∧
      ‖velocity (fun u : ℝ => R u s) t - velocity (fun u : ℝ => R u s₀) t‖ ≤ γ := by
  set F : ℝ × ℝ → Space := fun p => R p.1 p.2 with hF
  have hFcont : Continuous F := hR.continuous
  have hDcont : Continuous fun p : ℝ × ℝ => fderiv ℝ F p (1, 0) :=
    continuous_fderiv_partial hR
  have hKcomp : IsCompact (Set.Icc (0 : ℝ) period ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKcomp.uniformContinuousOn_of_continuous hFcont.continuousOn) γ hγ
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKcomp.uniformContinuousOn_of_continuous hDcont.continuousOn) γ hγ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro s hs hsδ t
  have hδ1 : |s - s₀| ≤ δ₁ := le_trans hsδ (min_le_left _ _)
  have hδ2 : |s - s₀| ≤ δ₂ := le_trans hsδ (min_le_right _ _)
  set t₀ : ℝ := fwRed t with ht₀
  have ht₀mem : t₀ ∈ Set.Icc (0 : ℝ) period := fwRed_mem t
  have ht₀b : t₀ = t - (⌊t / period⌋ : ℝ) * period := by rw [ht₀]; rfl
  have hper_s : R t s = R t₀ s := by
    rw [ht₀b]
    exact ((hslice s hs).periodic.sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_s₀ : R t s₀ = R t₀ s₀ := by
    rw [ht₀b]
    exact ((hslice s₀ hs₀).periodic.sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_vs : velocity (fun u : ℝ => R u s) t = velocity (fun u : ℝ => R u s) t₀ := by
    rw [ht₀b]
    show deriv (fun u : ℝ => R u s) t
      = deriv (fun u : ℝ => R u s) (t - (⌊t / period⌋ : ℝ) * period)
    exact ((periodic_deriv (hslice s hs).periodic).sub_int_mul_eq (⌊t / period⌋)).symm
  have hper_vs₀ : velocity (fun u : ℝ => R u s₀) t = velocity (fun u : ℝ => R u s₀) t₀ := by
    rw [ht₀b]
    show deriv (fun u : ℝ => R u s₀) t
      = deriv (fun u : ℝ => R u s₀) (t - (⌊t / period⌋ : ℝ) * period)
    exact ((periodic_deriv (hslice s₀ hs₀).periodic).sub_int_mul_eq (⌊t / period⌋)).symm
  have hdist1 : dist (t₀, s) (t₀, s₀) ≤ δ₁ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
    exact hδ1
  have hdist2 : dist (t₀, s) (t₀, s₀) ≤ δ₂ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
    exact hδ2
  constructor
  · rw [hper_s, hper_s₀, ← dist_eq_norm]
    exact hδ₁b (t₀, s) ⟨ht₀mem, hs⟩ (t₀, s₀) ⟨ht₀mem, hs₀⟩ hdist1
  · rw [hper_vs, hper_vs₀, velocity_slice_eq hR t₀ s, velocity_slice_eq hR t₀ s₀,
      ← dist_eq_norm]
    exact hδ₂b (t₀, s) ⟨ht₀mem, hs⟩ (t₀, s₀) ⟨ht₀mem, hs₀⟩ hdist2

/-- **Uniform perturbation radius for a family of knots.** -/
theorem uniformRadiusAlt {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsSmoothKnot (fun t : ℝ => R t s)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℝ → Space,
      ContDiff ℝ ⊤ z → Function.Periodic z period →
      (∀ t : ℝ, ‖z t‖ < ρ) → (∀ t : ℝ, ‖velocity z t‖ < ρ) →
      IsSmoothKnot (fun t : ℝ => R t s + z t) := by
  by_contra hneg
  have hseq : ∀ n : ℕ, ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ z : ℝ → Space,
      ContDiff ℝ ⊤ z ∧ Function.Periodic z period ∧
      (∀ t : ℝ, ‖z t‖ < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      (∀ t : ℝ, ‖velocity z t‖ < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      ¬ IsSmoothKnot (fun t : ℝ => R t s + z t) := by
    intro n
    by_contra hcon
    apply hneg
    refine ⟨(1 : ℝ) / ((n : ℝ) + 1), by positivity, ?_⟩
    intro s hs z hzsm hzp hzn hzv
    by_contra hnk
    exact hcon ⟨s, hs, z, hzsm, hzp, hzn, hzv, hnk⟩
  choose s hs z hrest using hseq
  have hzs : ∀ n, ContDiff ℝ ⊤ (z n) := fun n => (hrest n).1
  have hzp : ∀ n, Function.Periodic (z n) period := fun n => (hrest n).2.1
  have hzn : ∀ n, ∀ t : ℝ, ‖z n t‖ < (1 : ℝ) / ((n : ℝ) + 1) :=
    fun n => (hrest n).2.2.1
  have hzv : ∀ n, ∀ t : ℝ, ‖velocity (z n) t‖ < (1 : ℝ) / ((n : ℝ) + 1) :=
    fun n => (hrest n).2.2.2.1
  have hznk : ∀ n, ¬ IsSmoothKnot (fun t : ℝ => R t (s n) + z n t) :=
    fun n => (hrest n).2.2.2.2
  obtain ⟨sstar, hsstar, φ, hφmono, hφtend⟩ := isCompact_Icc.tendsto_subseq hs
  obtain ⟨ε, hεpos, hε⟩ := smallCorrectionKnot (hslice sstar hsstar)
  obtain ⟨δ, hδpos, hδb⟩ := familyWindowAt hR hslice hsstar (γ := ε / 4) (by positivity)
  have hfin : ∀ᶠ n : ℕ in Filter.atTop, |s (φ n) - sstar| ≤ δ := by
    have h2 : ∀ᶠ n : ℕ in Filter.atTop, dist (s (φ n)) sstar < δ :=
      Metric.tendsto_nhds.mp hφtend δ hδpos
    filter_upwards [h2] with n hn
    rw [Real.dist_eq] at hn
    exact le_of_lt hn
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / ((n : ℝ) + 1) < 3 * ε / 4 := by
    have htend : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := Metric.tendsto_nhds.mp htend (3 * ε / 4) (by positivity)
    filter_upwards [h2] with n hn
    rwa [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hn
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hfin
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hsmall
  set n : ℕ := max N₁ N₂ with hn
  have hn1 : |s (φ n) - sstar| ≤ δ := hN₁ n (le_max_left _ _)
  have hn2 : (1 : ℝ) / ((n : ℝ) + 1) < 3 * ε / 4 := hN₂ n (le_max_right _ _)
  have hwin := hδb (s (φ n)) (hs (φ n)) hn1
  set w : ℝ → Space := fun t => (R t (s (φ n)) - R t sstar) + z (φ n) t with hw
  have hwsm : ContDiff ℝ ⊤ w :=
    (((hslice (s (φ n)) (hs (φ n))).smooth).sub ((hslice sstar hsstar).smooth)).add (hzs (φ n))
  have hwper : Function.Periodic w period := by
    intro t
    have h1 : R (t + period) (s (φ n)) = R t (s (φ n)) :=
      (hslice (s (φ n)) (hs (φ n))).periodic t
    have h2 : R (t + period) sstar = R t sstar := (hslice sstar hsstar).periodic t
    have h3 : z (φ n) (t + period) = z (φ n) t := hzp (φ n) t
    simp only [hw, h1, h2, h3]
  have hfrac : (1 : ℝ) / (((φ n : ℕ) : ℝ) + 1) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have h' : ((n : ℕ) : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hφmono.id_le n
    linarith
  have hwn : ∀ t : ℝ, ‖w t‖ < ε := by
    intro t
    have h1 : ‖R t (s (φ n)) - R t sstar‖ ≤ ε / 4 := (hwin t).1
    have h2 : ‖z (φ n) t‖ < (1 : ℝ) / (((φ n : ℕ) : ℝ) + 1) := hzn (φ n) t
    calc ‖w t‖ = ‖(R t (s (φ n)) - R t sstar) + z (φ n) t‖ := by rw [hw]
      _ ≤ ‖R t (s (φ n)) - R t sstar‖ + ‖z (φ n) t‖ := norm_add_le _ _
      _ ≤ ε / 4 + (1 : ℝ) / ((n : ℝ) + 1) := by linarith
      _ < ε := by linarith
  have hwv : ∀ t : ℝ, ‖velocity w t‖ < ε := by
    intro t
    have hd1 : DifferentiableAt ℝ (fun u : ℝ => R u (s (φ n))) t :=
      ((hslice (s (φ n)) (hs (φ n))).smooth.differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun u : ℝ => R u sstar) t :=
      ((hslice sstar hsstar).smooth.differentiable (by decide)).differentiableAt
    have hd3 : DifferentiableAt ℝ (fun u : ℝ => R u (s (φ n)) - R u sstar) t := hd1.sub hd2
    have hd4 : DifferentiableAt ℝ (z (φ n)) t :=
      ((hzs (φ n)).differentiable (by decide)).differentiableAt
    have hvel : velocity w t =
        (velocity (fun u : ℝ => R u (s (φ n))) t - velocity (fun u : ℝ => R u sstar) t)
          + velocity (z (φ n)) t := by
      simp only [hw]
      rw [velocity_add' hd3 hd4, velocity_sub' hd1 hd2]
    have h1 : ‖velocity (fun u : ℝ => R u (s (φ n))) t - velocity (fun u : ℝ => R u sstar) t‖
        ≤ ε / 4 := (hwin t).2
    have h2 : ‖velocity (z (φ n)) t‖ < (1 : ℝ) / (((φ n : ℕ) : ℝ) + 1) := hzv (φ n) t
    calc ‖velocity w t‖ = ‖(velocity (fun u : ℝ => R u (s (φ n))) t -
            velocity (fun u : ℝ => R u sstar) t) + velocity (z (φ n)) t‖ := by rw [hvel]
      _ ≤ ‖velocity (fun u : ℝ => R u (s (φ n))) t - velocity (fun u : ℝ => R u sstar) t‖
            + ‖velocity (z (φ n)) t‖ := norm_add_le _ _
      _ ≤ ε / 4 + (1 : ℝ) / ((n : ℝ) + 1) := by linarith
      _ < ε := by linarith
  have hknot := hε w hwsm hwper (fun t => ⟨hwn t, hwv t⟩)
  have heq : (fun t : ℝ => R t sstar + w t)
      = fun t : ℝ => R t (s (φ n)) + z (φ n) t := by
    funext t
    simp only [hw]
    abel
  rw [heq] at hknot
  exact hznk (φ n) hknot

end Work.Drive
