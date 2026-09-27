import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces

namespace Work.Drive

open MeasureTheory
open scoped ContDiff Topology Convolution Interval

/-! # Guidance (parent agent `orderSplit_chains`) — exists_secant_dir_contDiff

The paper's configuration map `μ` on unordered pairs of a smooth Jordan curve is a *smooth embedding*
onto a Möbius strip.  The only non-obvious point is the diagonal of `Circle × Circle`: the naive formula
`dirC (γ x - γ y)` has the limit `dirC 0 = 0` there, whereas the correct (paper's) value at the diagonal
is the doubled *tangent* direction.  The reason the correct value is the right one is that the chord is
`γ x - γ y = (x - y) · W(x,y)` with `W` smooth and non-zero near the diagonal, and `dirC` is insensitive
to the scalar factor (it records the direction of an *unoriented* line).

This statement is the clean real-analytic form of that fact.  The curve is presented through its
`Circle.exp`-parametrisation `F = fun t => γ (Circle.exp t)`: `F` is `C^∞` because `γ` is a smooth
embedding of `Circle`, and `deriv F t ≠ 0` because `γ` is an immersion; both are *hypotheses* here so
that no manifold API is needed in the proof.

The divided difference used below is

  `secantW F (s,t) = ∫ w in 0..1, deriv F (t + w * (s - t))`   (and `secantW F (t,t) = deriv F t`).

For `s ≠ t` the Newton–Leibniz formula gives `F s - F t = (s - t) • secantW F (s,t)`; `dirC` is
insensitive to the non-zero real factor `s - t`, which turns that into the fourth conjunct.  The
smoothness of `secantW F` on the whole plane is obtained by writing it as a convolution with the
indicator of `(0,1]` (Mathlib's `contDiffOn_convolution_right_with_param_comp`), which is the
`C^n`-parametric-integral fact that Mathlib does not otherwise provide. -/

open Submission.Collision in
/-- `dirC` records the direction of an **unoriented** line (`arg / π ∈ ℝ/ℤ`, a *doubled* direction),
so it is invariant under `p ↦ -p`.  Concretely: `dirC (-p) = dirC p`. -/
lemma dirC_neg (p : ℝ × ℝ) : dirC (-p) = dirC p := by
  have hz : (⟨(-p).1, (-p).2⟩ : ℂ) = -(⟨p.1, p.2⟩ : ℂ) := by simp [Complex.ext_iff]
  rw [dirC, dirC, hz, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  rcases eq_or_ne (⟨p.1, p.2⟩ : ℂ) 0 with h0 | h0
  · refine ⟨0, ?_⟩
    rw [zero_zsmul, h0, neg_zero]
    ring
  · rcases lt_trichotomy (⟨p.1, p.2⟩ : ℂ).im 0 with hi | hi | hi
    · refine ⟨1, ?_⟩
      rw [one_zsmul, Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inl hi)]
      field_simp
      ring
    · rcases lt_trichotomy (⟨p.1, p.2⟩ : ℂ).re 0 with hr | hr | hr
      · refine ⟨-1, ?_⟩
        rw [zsmul_one, Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨hi, hr⟩)]
        field_simp
        ring
      · exact absurd (Complex.ext hr hi) h0
      · refine ⟨1, ?_⟩
        rw [one_zsmul, Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨hi, hr⟩)]
        field_simp
        ring
    · refine ⟨-1, ?_⟩
      rw [zsmul_one, Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inl hi)]
      field_simp
      ring

open Submission.Collision in
/-- `dirC` is insensitive to a non-zero real scalar factor. -/
lemma dirC_smul_ne_zero {c : ℝ} (hc : c ≠ 0) (p : ℝ × ℝ) : dirC (c • p) = dirC p := by
  rcases lt_trichotomy c 0 with h | h | h
  · have h1 : c • p = (-c) • (-p) := by ext <;> simp
    rw [h1, Submission.Configuration.dirC_smul_pos (by linarith : 0 < -c), dirC_neg]
  · exact absurd h hc
  · exact Submission.Configuration.dirC_smul_pos h p

/-- The **divided difference** (secant slope) of a curve `F : ℝ → ℝ × ℝ`, written as the mean of
`deriv F` over the chord joining `p.2` and `p.1`:
`secantW F (s,t) = ∫ w in 0..1, deriv F (t + w * (s - t))`. -/
noncomputable def secantW (F : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ∫ w in (0:ℝ)..1, deriv F (p.2 + w * (p.1 - p.2))

/-- On the diagonal, the divided difference is the derivative. -/
lemma secantW_self (F : ℝ → ℝ × ℝ) (t : ℝ) : secantW F (t, t) = deriv F t := by
  unfold secantW
  simp

/-- **Newton–Leibniz in affine form**: `F s - F t = (s - t) • secantW F (s,t)`. -/
lemma sub_eq_smul_secantW {F : ℝ → ℝ × ℝ} (hF : ContDiff ℝ 1 F) (s t : ℝ) :
    F s - F t = (s - t) • secantW F (s, t) := by
  have hcont : ContinuousOn (fun w : ℝ => deriv F (t + w • (s - t))) (Set.Icc 0 1) :=
    ((hF.continuous_deriv le_rfl).comp
      (by fun_prop : Continuous fun w : ℝ => t + w • (s - t))).continuousOn
  have hderiv : ∀ w ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt F (deriv F (t + w • (s - t))) (t + w • (s - t)) := by
    intro w _
    exact (hF.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub hcont hderiv
  simpa [secantW] using h.symm

/-- The derivative of a `C^∞` curve is `C^∞`. -/
lemma contDiff_deriv_of_contDiff {F : ℝ → ℝ × ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv F) := by
  rw [contDiff_infty] at hF ⊢
  intro n
  have h1 : ContDiff ℝ ((↑n : WithTop ℕ∞) + 1) F := by simpa using hF (n+1)
  simpa using h1.deriv'

/-- **The divided difference is `C^∞`.**  It is written as the convolution of the indicator of the
interval `(0,1]` with `(p, w) ↦ ψ w • deriv F (p.2 + w * (p.1 - p.2))` (`ψ` a bump function equal to
`1` on `[0,1]`), evaluated at `0`; smoothness then follows from
`MeasureTheory.contDiffOn_convolution_right_with_param_comp`. -/
lemma contDiff_secantW {F : ℝ → ℝ × ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secantW F) := by
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv F) := contDiff_deriv_of_contDiff hF
  -- a smooth bump function which is `1` on `[0,1]` and vanishes outside the ball of radius `1`
  let f₀ : ContDiffBump (1/2 : ℝ) := ContDiffBump.mk (1/2) 1 (by norm_num) (by norm_num)
  have hψcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑f₀) := ContDiffBump.contDiff f₀
  have hψ1 : ∀ t ∈ Set.Icc (0:ℝ) 1, f₀ t = 1 := by
    intro t ht
    rw [Set.mem_Icc] at ht
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall]
    show dist t (1/2 : ℝ) ≤ 1/2
    rw [Real.dist_eq, abs_sub_le_iff]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hψ0 : ∀ t : ℝ, 1 ≤ dist t (1/2 : ℝ) → f₀ t = 0 := fun t ht =>
    ContDiffBump.zero_of_le_dist (f := f₀) ht
  set f : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) 1) (fun _ => (1:ℝ)) with hfdef
  have hf : LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine IntegrableOn.of_bound hk.measure_lt_top ?_ 1 ?_
    · exact (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
      · rw [hfdef, Set.indicator_of_mem hx (fun _ => (1:ℝ))]
        simp
      · rw [hfdef, Set.indicator_of_notMem hx (fun _ => (1:ℝ))]
        simp
  set G : (ℝ × ℝ) → ℝ → (ℝ × ℝ) := fun p y => f₀ (-y) • deriv F (p.2 + (-y) * (p.1 - p.2))
    with hGdef
  set L : ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hGcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿G) := by
    have hfun : (↿G) = fun q : (ℝ × ℝ) × ℝ =>
        f₀ (-q.2) • deriv F (q.1.2 + (-q.2) * (q.1.1 - q.1.2)) := rfl
    rw [hfun]
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × ℝ => f₀ (-q.2)) :=
      hψcd.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × ℝ) × ℝ => deriv F (q.1.2 + (-q.2) * (q.1.1 - q.1.2))) :=
      hd.comp (by fun_prop)
    exact h1.smul h2
  have hk : IsCompact (-(Metric.closedBall (1/2 : ℝ) 1)) := (isCompact_closedBall _ _).neg
  have hgs : ∀ p y, p ∈ (Set.univ : Set (ℝ × ℝ)) →
      y ∉ -(Metric.closedBall (1/2 : ℝ) 1) → G p y = 0 := by
    intro p y _ hy
    have hy' : -(y) ∉ Metric.closedBall (1/2 : ℝ) 1 := fun h => hy (Set.mem_neg.mpr h)
    have hdist : 1 ≤ dist (-y) (1/2 : ℝ) := by
      rw [Metric.mem_closedBall, not_le] at hy'
      exact hy'.le
    show f₀ (-y) • deriv F (p.2 + (-y) * (p.1 - p.2)) = 0
    rw [hψ0 (-y) hdist, zero_smul]
  have hconv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (f ⋆[L, volume] G p) (0:ℝ)) Set.univ :=
    contDiffOn_convolution_right_with_param_comp L
      (v := fun _ : ℝ × ℝ => (0:ℝ)) (by fun_prop) isOpen_univ hk hgs hf
      (by rw [Set.univ_prod_univ]; exact hGcd.contDiffOn)
  rw [contDiffOn_univ] at hconv
  have hident : ∀ p : ℝ × ℝ, (f ⋆[L, volume] G p) 0 = secantW F p := by
    intro p
    rw [MeasureTheory.convolution_def]
    have h1 : (fun t : ℝ => L (f t) (G p (0 - t)))
        = fun t : ℝ => (Set.Ioc (0:ℝ) 1).indicator (fun t => deriv F (p.2 + t * (p.1 - p.2))) t := by
      funext t
      by_cases ht : t ∈ Set.Ioc (0:ℝ) 1
      · rw [Set.indicator_of_mem ht (fun t => deriv F (p.2 + t * (p.1 - p.2)))]
        have hft : f t = 1 := by rw [hfdef, Set.indicator_of_mem ht (fun _ => (1:ℝ))]
        have hψt : f₀ t = 1 := hψ1 t ⟨le_of_lt ht.1, ht.2⟩
        simp only [zero_sub, hGdef, neg_neg, hft, hψt, hLdef,
          ContinuousLinearMap.lsmul_apply, one_smul]
      · rw [Set.indicator_of_notMem ht (fun t => deriv F (p.2 + t * (p.1 - p.2)))]
        have hft : f t = 0 := by rw [hfdef, Set.indicator_of_notMem ht (fun _ => (1:ℝ))]
        simp [hft]
    rw [h1, MeasureTheory.integral_indicator measurableSet_Ioc, secantW]
    exact (intervalIntegral.integral_of_le zero_le_one).symm
  have hfun : (fun p : ℝ × ℝ => (f ⋆[L, volume] G p) 0) = secantW F := funext hident
  rw [hfun] at hconv
  exact hconv

open scoped ContDiff Topology in
/-- The divided difference of a smooth non-vanishing curve is smooth and non-vanishing near the
diagonal, and the doubled direction of a chord equals the doubled direction of the divided difference. -/
theorem exists_secant_dir_contDiff {F : ℝ → ℝ × ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hder : ∀ t, deriv F t ≠ 0) (t₀ : ℝ) :
    ∃ ε > 0, ∃ W : ℝ × ℝ → ℝ × ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W
        (Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ Set.Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), W (t, t) ≠ 0) ∧
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        Submission.Collision.dirC (W (t, t)) = Submission.Collision.dirC (deriv F t)) ∧
      (∀ s t, s ∈ Set.Ioo (t₀ - ε) (t₀ + ε) → t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) → s ≠ t →
        Submission.Collision.dirC (F s - F t) = Submission.Collision.dirC (W (s, t))) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  refine ⟨1, one_pos, secantW F, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_secantW hF).contDiffOn
  · intro t _
    rw [secantW_self]
    exact hder t
  · intro t _
    rw [secantW_self]
  · intro s t _ _ hst
    rw [sub_eq_smul_secantW hF1 s t, dirC_smul_ne_zero (sub_ne_zero.mpr hst)]

end Work.Drive
