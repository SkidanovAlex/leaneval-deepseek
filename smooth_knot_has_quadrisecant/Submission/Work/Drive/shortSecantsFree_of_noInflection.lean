import Mathlib
import Submission.Work.Drive.noInflectionAPI
import Submission.Work.Drive.separation_of_far_parameters

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 2000000

noncomputable section

/-!
# No short trisecants under the no-inflection hypothesis

`Work.Drive.shortSecantsFree_of_noInflection`: for a smooth knot `r` whose velocity and
acceleration are linearly independent at every parameter (no inflection point), the lifted
trisecant locus `liftedTrisecant r` is bounded away from both edges of the strip.

The mathematical content is the *engine* `Work.Drive.noShortMiddlePoint`: no knot point of
parameter `a + u`, `|u| < ρ`, lies strictly inside the chord joining the knot points of
parameters `a` and `a + y` (`0 < y < ρ`), uniformly in the base point `a ∈ [0, period]`.
It is proved with the osculating frame `(frameT r a, frameN r a)` and the two-by-two
determinant `det2` of the `(T,N)`-components of two vectors:

* `det2 (frameT r a) (frameN r a) (deriv r a) (deriv (deriv r) a) = ‖deriv r a‖ * ‖frameW r a‖`
  is bounded below by `m * c₀ > 0`, where `m` is the minimal speed and `c₀` the minimal
  normal curvature factor on one period;
* uniform continuity of `deriv r` and `deriv (deriv r)` on the compact window
  `[-(period+1), period+1]` therefore gives `det2 (deriv r (a+s)) (deriv (deriv r) (a+x)) > 0`
  for `0 ≤ s ≤ x ≤ ρ` (this is (E1) below), hence by the mean-value principle
  `det2 (deriv r (a+s)) (deriv r (a+t)) > 0` for `0 ≤ s < t ≤ ρ` ((L1)), and by two further
  mean-value steps `det2 (r (a+u) - r a) (r (a+y) - r a) > 0` for `0 < u < y < ρ` ((KEY));
* the middle-point relation writes `r (a+u) - r a = β • (r (a+y) - r a)` with `0 < β < 1`,
  which forces `det2 = 0`, and the first component `⟪r (a+t) - r a, frameT r a⟫` (strictly
  increasing on `[-ρ,ρ]`, with the sign of `t`) then forces `0 < u < y`.

The second ingredient is `Work.Drive.middleLiftOfShortTrisecant`: the middle point of a short
trisecant chord is realized by a parameter `p.1 + w` with `|w| < ρ` (separation of far
parameters + a lift of a circle point to the reals).

The module is complete: every step is proved below.
-/

def frameT (r : ℝ → Space) (a : ℝ) : Space := (‖deriv r a‖)⁻¹ • deriv r a

/-- The `T`-orthogonal part of the acceleration `deriv (deriv r) a`. -/
def frameW (r : ℝ → Space) (a : ℝ) : Space :=
  deriv (deriv r) a - (inner ℝ (deriv (deriv r) a) (frameT r a)) • frameT r a

/-- Unit normal vector of `r` at `a`, along `frameW r a`. -/
def frameN (r : ℝ → Space) (a : ℝ) : Space := (‖frameW r a‖)⁻¹ • frameW r a

/-- The determinant of the `(T,N)`-components of `f` and `g`, written as a single inner
product against the vector `⟨f,T⟩•N - ⟨f,N⟩•T` (so that differentiating in either slot is a
plain inner-product derivative). -/
def det2 (T N f g : Space) : ℝ := inner ℝ g (inner ℝ f T • N - inner ℝ f N • T)

lemma det2_expand (T N f g : Space) :
    det2 T N f g = inner ℝ f T * inner ℝ g N - inner ℝ f N * inner ℝ g T := by
  simp only [det2, real_inner_smul_right, inner_sub_right]

lemma det2_self (T N f : Space) : det2 T N f f = 0 := by
  rw [det2_expand]
  ring

lemma det2_antisymm (T N f g : Space) : det2 T N f g = -det2 T N g f := by
  rw [det2_expand, det2_expand]
  ring

lemma det2_add_right (T N f g h : Space) :
    det2 T N f (g + h) = det2 T N f g + det2 T N f h := by
  rw [det2_expand, det2_expand, det2_expand, inner_add_left, inner_add_left]
  ring

lemma det2_smul_right (T N f g : Space) (c : ℝ) :
    det2 T N f (c • g) = c * det2 T N f g := by
  rw [det2_expand, det2_expand, real_inner_smul_left, real_inner_smul_left]
  ring

lemma det2_add_left (T N f g h : Space) :
    det2 T N (f + g) h = det2 T N f h + det2 T N g h := by
  rw [det2_expand, det2_expand, det2_expand, inner_add_left, inner_add_left]
  ring

lemma det2_smul_left (T N f g : Space) (c : ℝ) :
    det2 T N (c • f) g = c * det2 T N f g := by
  rw [det2_expand, det2_expand, real_inner_smul_left, real_inner_smul_left]
  ring

lemma abs_det2_le (T N f g : Space) (hT : ‖T‖ = 1) (hN : ‖N‖ = 1) :
    |det2 T N f g| ≤ 2 * ‖f‖ * ‖g‖ := by
  have h1 : |inner ℝ f T| ≤ ‖f‖ := by simpa [hT] using abs_real_inner_le_norm f T
  have h2 : |inner ℝ g N| ≤ ‖g‖ := by simpa [hN] using abs_real_inner_le_norm g N
  have h3 : |inner ℝ f N| ≤ ‖f‖ := by simpa [hN] using abs_real_inner_le_norm f N
  have h4 : |inner ℝ g T| ≤ ‖g‖ := by simpa [hT] using abs_real_inner_le_norm g T
  have h5 : |inner ℝ f T * inner ℝ g N| ≤ ‖f‖ * ‖g‖ := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg f)
  have h6 : |inner ℝ f N * inner ℝ g T| ≤ ‖f‖ * ‖g‖ := by
    rw [abs_mul]
    exact mul_le_mul h3 h4 (abs_nonneg _) (norm_nonneg f)
  calc |det2 T N f g|
      = |inner ℝ f T * inner ℝ g N - inner ℝ f N * inner ℝ g T| := by rw [det2_expand]
    _ ≤ |inner ℝ f T * inner ℝ g N| + |inner ℝ f N * inner ℝ g T| := abs_sub _ _
    _ ≤ ‖f‖ * ‖g‖ + ‖f‖ * ‖g‖ := add_le_add h5 h6
    _ = 2 * ‖f‖ * ‖g‖ := by ring

lemma hasDerivAt_shift {f : ℝ → Space} (hf : Differentiable ℝ f) (a v : ℝ) :
    HasDerivAt (fun w : ℝ => f (a + w)) (deriv f (a + v)) v :=
  ((hf (a + v)).hasDerivAt).comp_const_add a v

lemma hasDerivAt_det2_right (T N F : Space) {G : ℝ → Space} {G' : Space} {v : ℝ}
    (hG : HasDerivAt G G' v) :
    HasDerivAt (fun w : ℝ => det2 T N F (G w)) (det2 T N F G') v := by
  have h := HasDerivAt.inner ℝ hG (hasDerivAt_const v (inner ℝ F T • N - inner ℝ F N • T))
  rw [inner_zero_right, zero_add] at h
  simpa only [det2] using h

lemma hasDerivAt_det2_left (T N G : Space) {F : ℝ → Space} {F' : Space} {v : ℝ}
    (hF : HasDerivAt F F' v) :
    HasDerivAt (fun w : ℝ => det2 T N (F w) G) (det2 T N F' G) v := by
  have hφ : HasDerivAt (fun w : ℝ => inner ℝ (F w) T) (inner ℝ F' T) v := by
    have h := HasDerivAt.inner ℝ hF (hasDerivAt_const v T)
    rw [inner_zero_right, zero_add] at h
    exact h
  have hψ : HasDerivAt (fun w : ℝ => inner ℝ (F w) N) (inner ℝ F' N) v := by
    have h := HasDerivAt.inner ℝ hF (hasDerivAt_const v N)
    rw [inner_zero_right, zero_add] at h
    exact h
  have h1 : HasDerivAt (fun w : ℝ => inner ℝ (F w) T • N) (inner ℝ F' T • N) v :=
    hφ.smul_const N
  have h2 : HasDerivAt (fun w : ℝ => inner ℝ (F w) N • T) (inner ℝ F' N • T) v :=
    hψ.smul_const T
  have hK : HasDerivAt (fun w : ℝ => inner ℝ G (inner ℝ (F w) T • N - inner ℝ (F w) N • T))
      (inner ℝ G (inner ℝ F' T • N - inner ℝ F' N • T)) v := by
    have h := HasDerivAt.inner ℝ (hasDerivAt_const v G) (h1.sub h2)
    rw [inner_zero_left, add_zero] at h
    exact h
  simpa only [det2] using hK

/-! ### Frame properties -/

lemma inner_deriv_frameT (r : ℝ → Space) (a : ℝ) :
    inner ℝ (deriv r a) (frameT r a) = ‖deriv r a‖ := by
  simp only [frameT, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
  rcases eq_or_ne ‖deriv r a‖ 0 with h | h
  · simp [h]
  · field_simp

lemma norm_frameT (r : ℝ → Space) (a : ℝ) (h : deriv r a ≠ 0) : ‖frameT r a‖ = 1 := by
  simp only [frameT, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  rw [inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr h

lemma inner_frameT_frameW (r : ℝ → Space) (a : ℝ) (h : ‖frameT r a‖ = 1) :
    inner ℝ (frameT r a) (frameW r a) = 0 := by
  have hTT : inner ℝ (frameT r a) (frameT r a) = 1 := by
    rw [real_inner_self_eq_norm_sq, h]
    norm_num
  have hc : inner ℝ (deriv (deriv r) a) (frameT r a)
      = inner ℝ (frameT r a) (deriv (deriv r) a) := real_inner_comm _ _
  rw [frameW, inner_sub_right, real_inner_smul_right, hTT, hc]
  ring

lemma frameW_ne_zero {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a : ℝ) :
    frameW r a ≠ 0 := by
  intro hzero
  have hli := linearIndependent_fin2.mp (hinfl a)
  have hne : deriv (deriv r) a ≠ 0 := by simpa using hli.1
  have hli2 : ∀ c' : ℝ, c' • deriv (deriv r) a ≠ deriv r a := by
    intro c'
    simpa using hli.2 c'
  have hsub : deriv (deriv r) a
      = (inner ℝ (deriv (deriv r) a) (frameT r a)) • frameT r a := by
    simpa only [frameW] using sub_eq_zero.mp hzero
  set L := ‖deriv r a‖ with hL
  set c := inner ℝ (deriv (deriv r) a) (frameT r a) with hc
  have hr2 : deriv (deriv r) a = (c * L⁻¹) • deriv r a := by
    rw [hsub]
    simp only [frameT, smul_smul]
    rw [hL]
  rcases eq_or_ne (c * L⁻¹) 0 with h | h
  · rw [h, zero_smul] at hr2
    exact hne hr2
  · refine hli2 ((c * L⁻¹)⁻¹) ?_
    rw [hr2, smul_smul, inv_mul_cancel₀ h, one_smul]

lemma norm_frameN {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a : ℝ) :
    ‖frameN r a‖ = 1 := by
  have hw := frameW_ne_zero hr hinfl a
  simp only [frameN, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  rw [inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr hw

lemma inner_deriv2_frameN {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a : ℝ) :
    inner ℝ (deriv (deriv r) a) (frameN r a) = ‖frameW r a‖ := by
  have hw := frameW_ne_zero hr hinfl a
  have hperp : inner ℝ (frameT r a) (frameW r a) = 0 :=
    inner_frameT_frameW r a (norm_frameT r a (hr.regular a))
  have hinner : inner ℝ (deriv (deriv r) a) (frameW r a) = ‖frameW r a‖ ^ 2 := by
    have hdec : deriv (deriv r) a
        = frameW r a + (inner ℝ (deriv (deriv r) a) (frameT r a)) • frameT r a := by
      simp only [frameW]
      abel
    rw [hdec, inner_add_left, real_inner_smul_left, hperp, mul_zero, add_zero]
    rw [real_inner_self_eq_norm_sq]
  rw [frameN, real_inner_smul_right, hinner]
  rcases eq_or_ne ‖frameW r a‖ 0 with h | h
  · simp [h]
  · field_simp

lemma inner_deriv_frameN (r : ℝ → Space) (a : ℝ) (h : ‖frameT r a‖ = 1) :
    inner ℝ (deriv r a) (frameN r a) = 0 := by
  have h3 : inner ℝ (frameT r a) (frameW r a) = 0 := inner_frameT_frameW r a h
  have hderiv0 : deriv r a ≠ 0 := by
    intro h0
    have h' := h
    simp only [frameT, h0, norm_zero, inv_zero, zero_smul, norm_zero] at h'
    exact absurd h' (by norm_num)
  have h2 : deriv r a = ‖deriv r a‖ • frameT r a := by
    rw [frameT, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hderiv0), one_smul]
  rw [frameN, real_inner_smul_right, h2, real_inner_smul_left, h3, mul_zero]
  ring

lemma det2_base {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a : ℝ) :
    det2 (frameT r a) (frameN r a) (deriv r a) (deriv (deriv r) a)
      = ‖deriv r a‖ * ‖frameW r a‖ := by
  have hT : ‖frameT r a‖ = 1 := norm_frameT r a (hr.regular a)
  rw [det2_expand, inner_deriv_frameT, inner_deriv_frameN r a hT,
    inner_deriv2_frameN hr hinfl a]
  ring



/-- The determinant bound used for the uniform estimate: if `f` is `ε`-close to `f0`, `g` to `g0`,
`ε ≤ 1`, and `C ≤ det2 T N f0 g0`, then `C - 2ε(M₁+M₂+1) ≤ det2 T N f g`. -/
lemma det2_ge_sub {T N f0 g0 f g : Space} {ε M1 M2 C : ℝ}
    (hT : ‖T‖ = 1) (hN : ‖N‖ = 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hf : ‖f - f0‖ ≤ ε) (hg : ‖g - g0‖ ≤ ε)
    (hf0 : ‖f0‖ ≤ M1) (hg0 : ‖g0‖ ≤ M2) (hC : C ≤ det2 T N f0 g0) :
    C - 2 * ε * (M1 + M2 + 1) ≤ det2 T N f g := by
  have h1 : |det2 T N (f - f0) g0| ≤ 2 * ‖f - f0‖ * ‖g0‖ := abs_det2_le T N _ _ hT hN
  have h2 : |det2 T N f0 (g - g0)| ≤ 2 * ‖f0‖ * ‖g - g0‖ := abs_det2_le T N _ _ hT hN
  have h3 : |det2 T N (f - f0) (g - g0)| ≤ 2 * ‖f - f0‖ * ‖g - g0‖ := abs_det2_le T N _ _ hT hN
  have h1' : -(2 * ε * M2) ≤ det2 T N (f - f0) g0 := by
    have hlt : 2 * ‖f - f0‖ * ‖g0‖ ≤ 2 * ε * M2 := by
      have h := mul_le_mul hf hg0 (norm_nonneg g0) hε0
      linarith
    linarith [abs_le.mp h1]
  have h2' : -(2 * ε * M1) ≤ det2 T N f0 (g - g0) := by
    have hlt : 2 * ‖f0‖ * ‖g - g0‖ ≤ 2 * ε * M1 := by
      have h := mul_le_mul hf0 hg (norm_nonneg (g - g0)) (le_trans (norm_nonneg f0) hf0)
      linarith
    linarith [abs_le.mp h2]
  have h3' : -(2 * ε) ≤ det2 T N (f - f0) (g - g0) := by
    have hlt : 2 * ‖f - f0‖ * ‖g - g0‖ ≤ 2 * ε := by
      have h1'' : ‖f - f0‖ * ‖g - g0‖ ≤ ε * ε := mul_le_mul hf hg (norm_nonneg _) hε0
      nlinarith [hε0, hε1]
    linarith [abs_le.mp h3]
  have hexp : det2 T N f g
      = det2 T N f0 g0 + det2 T N (f - f0) g0 + det2 T N f0 (g - g0)
        + det2 T N (f - f0) (g - g0) := by
    conv_lhs => rw [show f = (f - f0) + f0 from (sub_add_cancel f f0).symm,
      show g = (g - g0) + g0 from (sub_add_cancel g g0).symm]
    rw [det2_add_left, det2_add_right, det2_add_right]
    ring
  rw [hexp]
  nlinarith [h1', h2', h3', hC]

/-! ## 2. Auxiliary calculus lemmas -/

/-- Mean-value principle: an inequality on the derivative gives a strict increase. -/
lemma sub_pos_of_deriv_pos_on {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn F (Set.Icc a b)) (hdiff : DifferentiableOn ℝ F (Set.Ioo a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, 0 < deriv F x) : F a < F b := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope F hab hcont hdiff
  have hba : b - a ≠ 0 := ne_of_gt (by linarith : 0 < b - a)
  have h1 : deriv F c * (b - a) = F b - F a := by
    rw [hcd]
    field_simp
  have h2 : 0 < deriv F c := hderiv c hc
  have h3 : 0 < b - a := by linarith
  have h4 : 0 < F b - F a := by
    rw [← h1]
    exact mul_pos h2 h3
  linarith

lemma det2_zero_left (T N g : Space) : det2 T N 0 g = 0 := by
  simp [det2]

/-! ## 3. The analytic engine -/

/-- **No short middle point on a knot without inflection points.** -/
theorem noShortMiddlePoint {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < period ∧ ∀ a : ℝ, a ∈ Set.Icc 0 period →
      ∀ u y : ℝ, 0 < y → y < ρ → |u| < ρ →
        r (a + u) ∉ openSegment ℝ (r a) (r (a + y)) := by
  have hper : 0 < period := period_pos
  have hd1 : ContDiff ℝ ⊤ (deriv r) := hr.smooth.deriv'
  have hd2 : ContDiff ℝ ⊤ (deriv (deriv r)) := hd1.deriv'
  have hc1 : Continuous (deriv r) := hd1.continuous
  have hc2 : Continuous (deriv (deriv r)) := hd2.continuous
  have hd1' : Differentiable ℝ (deriv r) := hd1.differentiable (by simp)
  have hdr : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hreg : ∀ t : ℝ, deriv r t ≠ 0 := fun t => hr.regular t
  -- the two windows
  set W : Set ℝ := Set.Icc (-(period + 1)) (period + 1) with hWdef
  have hWc : IsCompact W := isCompact_Icc
  have hWne : W.Nonempty :=
    ⟨0, by rw [hWdef]; exact ⟨by linarith [hper], by linarith [hper]⟩⟩
  set K0 : Set ℝ := Set.Icc 0 period with hK0def
  have hK0c : IsCompact K0 := isCompact_Icc
  have hK0ne : K0.Nonempty := ⟨0, by rw [hK0def]; exact ⟨le_rfl, hper.le⟩⟩
  have hK0W : K0 ⊆ W := by
    intro t ht
    rw [hK0def] at ht
    rw [hWdef]
    exact ⟨by linarith [ht.1], by linarith [ht.2, hper]⟩
  have hK0mem : ∀ t ∈ K0, 0 ≤ t ∧ t ≤ period := by
    intro t ht
    rw [hK0def] at ht
    exact ht
  -- minimal speed on one period
  obtain ⟨pm, hpmK, hpmmin⟩ := hK0c.exists_isMinOn hK0ne hc1.norm.continuousOn
  -- maximal norms on the window
  obtain ⟨p1, hp1W, hp1max⟩ := hWc.exists_isMaxOn hWne hc1.norm.continuousOn
  obtain ⟨p2, hp2W, hp2max⟩ := hWc.exists_isMaxOn hWne hc2.norm.continuousOn
  -- normal-curvature lower bound
  have hTcont : ContinuousOn (fun t : ℝ => frameT r t) K0 := by
    simp only [frameT]
    exact (hc1.norm.continuousOn.inv₀ (fun t _ => norm_ne_zero_iff.mpr (hreg t))).smul
      hc1.continuousOn
  have hWcont : ContinuousOn (fun t : ℝ => ‖frameW r t‖) K0 := by
    have h1 : ContinuousOn (fun t : ℝ => inner ℝ (deriv (deriv r) t) (frameT r t)) K0 :=
      hc2.continuousOn.inner hTcont
    have h2 : ContinuousOn (fun t : ℝ => deriv (deriv r) t
        - (inner ℝ (deriv (deriv r) t) (frameT r t)) • frameT r t) K0 :=
      hc2.continuousOn.sub (h1.smul hTcont)
    simpa only [frameW] using h2.norm
  obtain ⟨pc, hpcK, hpcmin⟩ := hK0c.exists_isMinOn hK0ne hWcont
  -- names for the constants
  set m : ℝ := ‖deriv r pm‖ with hmdef
  set M1 : ℝ := ‖deriv r p1‖ with hM1def
  set M2 : ℝ := ‖deriv (deriv r) p2‖ with hM2def
  set c0 : ℝ := ‖frameW r pc‖ with hc0def
  have hmpos : 0 < m := by rw [hmdef]; exact norm_pos_iff.mpr (hreg pm)
  have hc0pos : 0 < c0 := by
    rw [hc0def]; exact norm_pos_iff.mpr (frameW_ne_zero hr hinfl pc)
  have hmle : ∀ a ∈ K0, m ≤ ‖deriv r a‖ := fun a ha => by rw [hmdef]; exact hpmmin ha
  have hc0le : ∀ a ∈ K0, c0 ≤ ‖frameW r a‖ := fun a ha => by rw [hc0def]; exact hpcmin ha
  have hM1le : ∀ t ∈ W, ‖deriv r t‖ ≤ M1 := fun t ht => by rw [hM1def]; exact hp1max ht
  have hM2le : ∀ t ∈ W, ‖deriv (deriv r) t‖ ≤ M2 := fun t ht => by rw [hM2def]; exact hp2max ht
  have hM1nn : 0 ≤ M1 := by rw [hM1def]; exact norm_nonneg _
  have hM2nn : 0 ≤ M2 := by rw [hM2def]; exact norm_nonneg _
  set B : ℝ := M1 + M2 + 1 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; linarith
  set ε₁ : ℝ := min (1 / 2) (min (m / 2) (m * c0 / (8 * B))) with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (by norm_num)
      (lt_min (by linarith) (div_pos (mul_pos hmpos hc0pos) (by linarith)))
  have hε₁1 : ε₁ ≤ 1 := by
    rw [hε₁def]
    exact le_trans (min_le_left _ _) (by norm_num)
  have hε₁m : ε₁ ≤ m / 2 := by
    rw [hε₁def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₁c : ε₁ ≤ m * c0 / (8 * B) := by
    rw [hε₁def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- moduli of uniform continuity on the window
  have huc1 : UniformContinuousOn (deriv r) W :=
    hWc.uniformContinuousOn_of_continuous hc1.continuousOn
  have huc2 : UniformContinuousOn (deriv (deriv r)) W :=
    hWc.uniformContinuousOn_of_continuous hc2.continuousOn
  obtain ⟨η1, hη1pos, hη1⟩ := Metric.uniformContinuousOn_iff.mp huc1 ε₁ hε₁pos
  obtain ⟨η2, hη2pos, hη2⟩ := Metric.uniformContinuousOn_iff.mp huc2 ε₁ hε₁pos
  set ρ : ℝ := min (η1 / 2) (min (η2 / 2) (min (1 / 2) (period / 4))) with hρdef
  have hρle1 : ρ ≤ η1 / 2 := by rw [hρdef]; exact min_le_left _ _
  have hρle2 : ρ ≤ η2 / 2 := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρle3 : ρ ≤ 1 / 2 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρle4 : ρ ≤ period / 4 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by norm_num) (by linarith)))
  have hρlt1 : ρ < 1 := by linarith
  have hρκ1 : ρ < η1 := by linarith
  have hρκ2 : ρ < η2 := by linarith
  have hρper : ρ < period := by linarith
  -- smallness of the derivatives near the base point
  have hsmall1 : ∀ a ∈ K0, ∀ e : ℝ, |e| ≤ ρ →
      ‖deriv r (a + e) - deriv r a‖ ≤ ε₁ := by
    intro a ha e he
    have haW : a ∈ W := hK0W ha
    have haeW : a + e ∈ W := by
      have he1 : |e| ≤ 1 := le_trans he hρlt1.le
      rw [abs_le] at he1
      rw [hWdef]
      exact ⟨by linarith [(hK0mem a ha).1, he1.1], by linarith [(hK0mem a ha).2, he1.2, hper]⟩
    have hd : dist a (a + e) < η1 := by
      rw [Real.dist_eq, show a - (a + e) = -e from by ring, abs_neg]
      linarith
    have h := hη1 a haW (a + e) haeW hd
    rw [dist_eq_norm] at h
    simpa only [norm_sub_rev] using h.le
  have hsmall2 : ∀ a ∈ K0, ∀ e : ℝ, |e| ≤ ρ →
      ‖deriv (deriv r) (a + e) - deriv (deriv r) a‖ ≤ ε₁ := by
    intro a ha e he
    have haW : a ∈ W := hK0W ha
    have haeW : a + e ∈ W := by
      have he1 : |e| ≤ 1 := le_trans he hρlt1.le
      rw [abs_le] at he1
      rw [hWdef]
      exact ⟨by linarith [(hK0mem a ha).1, he1.1], by linarith [(hK0mem a ha).2, he1.2, hper]⟩
    have hd : dist a (a + e) < η2 := by
      rw [Real.dist_eq, show a - (a + e) = -e from by ring, abs_neg]
      linarith
    have h := hη2 a haW (a + e) haeW hd
    rw [dist_eq_norm] at h
    simpa only [norm_sub_rev] using h.le
  -- the determinant at the base point
  have hbase : ∀ a ∈ K0, m * c0 ≤
      det2 (frameT r a) (frameN r a) (deriv r a) (deriv (deriv r) a) := by
    intro a ha
    rw [det2_base hr hinfl a]
    exact mul_le_mul (hmle a ha) (hc0le a ha) (by rw [hc0def]; exact norm_nonneg _)
      (norm_nonneg _)
  -- (E1)
  have hE1 : ∀ a ∈ K0, ∀ s x : ℝ, 0 ≤ s → s ≤ x → x ≤ ρ →
      0 < det2 (frameT r a) (frameN r a) (deriv r (a + s)) (deriv (deriv r) (a + x)) := by
    intro a ha s x hs hsx hxρ
    have hT : ‖frameT r a‖ = 1 := norm_frameT r a (hreg a)
    have hN : ‖frameN r a‖ = 1 := norm_frameN hr hinfl a
    have hf : ‖deriv r (a + s) - deriv r a‖ ≤ ε₁ :=
      hsmall1 a ha s (by rw [abs_of_nonneg hs]; linarith)
    have hg : ‖deriv (deriv r) (a + x) - deriv (deriv r) a‖ ≤ ε₁ :=
      hsmall2 a ha x (by rw [abs_of_nonneg (le_trans hs hsx)]; exact hxρ)
    have hf0 : ‖deriv r a‖ ≤ M1 := hM1le a (hK0W ha)
    have hg0 : ‖deriv (deriv r) a‖ ≤ M2 := hM2le a (hK0W ha)
    have hmain := det2_ge_sub (T := frameT r a) (N := frameN r a)
      (f0 := deriv r a) (g0 := deriv (deriv r) a) (f := deriv r (a + s))
      (g := deriv (deriv r) (a + x)) (ε := ε₁) (M1 := M1) (M2 := M2) (C := m * c0)
      hT hN hε₁pos.le hε₁1 hf hg hf0 hg0 (hbase a ha)
    have hmain' : m * c0 - 2 * ε₁ * B ≤
        det2 (frameT r a) (frameN r a) (deriv r (a + s)) (deriv (deriv r) (a + x)) := by
      rw [hBdef]
      exact hmain
    have hpos : 0 < m * c0 - 2 * ε₁ * B := by
      have h4 : ε₁ * (8 * B) ≤ m * c0 := by
        have h := hε₁c
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * B)] at h
        exact h
      nlinarith [h4, hBpos, hmpos, hc0pos]
    linarith
  -- (L1)
  have hL1 : ∀ a ∈ K0, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ ρ →
      0 < det2 (frameT r a) (frameN r a) (deriv r (a + s)) (deriv r (a + t)) := by
    intro a ha s t hs hst ht
    set Ψ : ℝ → ℝ := fun w => det2 (frameT r a) (frameN r a) (deriv r (a + s)) (deriv r (a + w))
      with hΨ
    have hderiv : ∀ v : ℝ, HasDerivAt Ψ
        (det2 (frameT r a) (frameN r a) (deriv r (a + s)) (deriv (deriv r) (a + v))) v := by
      intro v
      have h := hasDerivAt_det2_right (frameT r a) (frameN r a) (deriv r (a + s))
        (hasDerivAt_shift hd1' a v)
      simpa only [hΨ] using h
    have hcont : ContinuousOn Ψ (Set.Icc s t) := fun x _ =>
      (hderiv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ Ψ (Set.Ioo s t) := fun x _ =>
      (hderiv x).differentiableAt.differentiableWithinAt
    have hderivpos : ∀ x ∈ Set.Ioo s t, 0 < deriv Ψ x := by
      intro x hx
      rw [(hderiv x).deriv]
      exact hE1 a ha s x hs (le_of_lt hx.1) (le_trans (le_of_lt hx.2) ht)
    have hΨs : Ψ s = 0 := by
      simp only [hΨ, det2_self]
    have := sub_pos_of_deriv_pos_on hst hcont hdiff hderivpos
    rw [hΨs] at this
    simpa only [hΨ] using this
  -- (KEY)
  have hKEY : ∀ a ∈ K0, ∀ u y : ℝ, 0 < u → u < y → y < ρ →
      0 < det2 (frameT r a) (frameN r a) (r (a + u) - r a) (r (a + y) - r a) := by
    intro a ha u y hu huy hyρ
    -- the inner mean-value step: `χ w = det2 (P w) (deriv r (a+ξ))`
    have hinner : ∀ ξ ∈ Set.Ioo u y, 0 < det2 (frameT r a) (frameN r a)
        (r (a + u) - r a) (deriv r (a + ξ)) := by
      intro ξ hξ
      set χ : ℝ → ℝ := fun w => det2 (frameT r a) (frameN r a) (r (a + w) - r a)
        (deriv r (a + ξ)) with hχ
      have hderiv : ∀ v : ℝ, HasDerivAt χ
          (det2 (frameT r a) (frameN r a) (deriv r (a + v)) (deriv r (a + ξ))) v := by
        intro v
        have h1 : HasDerivAt (fun w : ℝ => r (a + w) - r a) (deriv r (a + v)) v :=
          (hasDerivAt_shift hdr a v).sub_const (r a)
        have h := hasDerivAt_det2_left (frameT r a) (frameN r a) (deriv r (a + ξ)) h1
        simpa only [hχ] using h
      have hcont : ContinuousOn χ (Set.Icc 0 u) := fun x _ =>
        (hderiv x).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ χ (Set.Ioo 0 u) := fun x _ =>
        (hderiv x).differentiableAt.differentiableWithinAt
      have hderivpos : ∀ x ∈ Set.Ioo 0 u, 0 < deriv χ x := by
        intro x hx
        rw [(hderiv x).deriv]
        exact hL1 a ha x ξ (le_of_lt hx.1) (lt_trans hx.2 hξ.1)
          (le_of_lt (lt_of_lt_of_le hξ.2 hyρ.le))
      have hχ0 : χ 0 = 0 := by
        simp only [hχ, add_zero, sub_self, det2_zero_left]
      have := sub_pos_of_deriv_pos_on hu hcont hdiff hderivpos
      rw [hχ0] at this
      simpa only [hχ] using this
    -- the outer mean-value step: `Ψ v = det2 (P u) (P v)`
    set Ψ : ℝ → ℝ := fun w => det2 (frameT r a) (frameN r a) (r (a + u) - r a)
      (r (a + w) - r a) with hΨ
    have hderiv : ∀ v : ℝ, HasDerivAt Ψ
        (det2 (frameT r a) (frameN r a) (r (a + u) - r a) (deriv r (a + v))) v := by
      intro v
      have h1 : HasDerivAt (fun w : ℝ => r (a + w) - r a) (deriv r (a + v)) v :=
        (hasDerivAt_shift hdr a v).sub_const (r a)
      have h := hasDerivAt_det2_right (frameT r a) (frameN r a) (r (a + u) - r a) h1
      simpa only [hΨ] using h
    have hcont : ContinuousOn Ψ (Set.Icc u y) := fun x _ =>
      (hderiv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ Ψ (Set.Ioo u y) := fun x _ =>
      (hderiv x).differentiableAt.differentiableWithinAt
    have hderivpos : ∀ x ∈ Set.Ioo u y, 0 < deriv Ψ x := by
      intro x hx
      rw [(hderiv x).deriv]
      exact hinner x hx
    have hΨu : Ψ u = 0 := by
      simp only [hΨ, det2_self]
    have := sub_pos_of_deriv_pos_on huy hcont hdiff hderivpos
    rw [hΨu] at this
    simpa only [hΨ] using this
  -- the `T`-component of the chord is strictly increasing on `[-ρ,ρ]`
  have hAmono : ∀ a ∈ K0, ∀ t1 t2 : ℝ, -ρ ≤ t1 → t1 < t2 → t2 ≤ ρ →
      inner ℝ (r (a + t1) - r a) (frameT r a) < inner ℝ (r (a + t2) - r a) (frameT r a) := by
    intro a ha t1 t2 ht1 ht2 ht3
    set A : ℝ → ℝ := fun t => inner ℝ (r (a + t) - r a) (frameT r a) with hA
    have hderiv : ∀ v : ℝ, HasDerivAt A
        (inner ℝ (deriv r (a + v)) (frameT r a)) v := by
      intro v
      have h1 : HasDerivAt (fun t : ℝ => r (a + t) - r a) (deriv r (a + v)) v :=
        (hasDerivAt_shift hdr a v).sub_const (r a)
      have h := HasDerivAt.inner ℝ h1 (hasDerivAt_const v (frameT r a))
      rw [inner_zero_right, zero_add] at h
      simpa only [hA] using h
    have hcont : ContinuousOn A (Set.Icc t1 t2) := fun x _ =>
      (hderiv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ A (Set.Ioo t1 t2) := fun x _ =>
      (hderiv x).differentiableAt.differentiableWithinAt
    have hderivpos : ∀ x ∈ Set.Ioo t1 t2, 0 < deriv A x := by
      intro x hx
      rw [(hderiv x).deriv]
      have hv : x ∈ Set.Ioo (-ρ) ρ := ⟨by linarith [hx.1, ht1], by linarith [hx.2, ht3]⟩
      have hdecomp : deriv r (a + x) = deriv r a + (deriv r (a + x) - deriv r a) := by abel
      rw [hdecomp, inner_add_left, inner_deriv_frameT]
      have hb : |inner ℝ (deriv r (a + x) - deriv r a) (frameT r a)| ≤ ε₁ := by
        have h1 : |inner ℝ (deriv r (a + x) - deriv r a) (frameT r a)| ≤
            ‖deriv r (a + x) - deriv r a‖ * ‖frameT r a‖ :=
          abs_real_inner_le_norm _ _
        rw [norm_frameT r a (hreg a), mul_one] at h1
        exact le_trans h1 (hsmall1 a ha x (by
          rw [abs_le]; exact ⟨hv.1.le, hv.2.le⟩))
      have hba := (abs_le.mp hb).1
      have hm : m ≤ ‖deriv r a‖ := hmle a ha
      linarith [hε₁m]
    exact sub_pos_of_deriv_pos_on ht2 hcont hdiff hderivpos
  -- conclusion
  refine ⟨ρ, hρpos, hρper, ?_⟩
  intro a ha u y hy hyρ huρ hmem
  rcases hmem with ⟨α, β, hα, hβ, hαβ, hsum⟩
  have ht1 : β < 1 := by linarith
  have hA0 : inner ℝ (r (a + 0) - r a) (frameT r a) = 0 := by
    simp
  have hArel : inner ℝ (r (a + u) - r a) (frameT r a)
      = β * inner ℝ (r (a + y) - r a) (frameT r a) := by
    have h1 : r (a + u) - r a = β • (r (a + y) - r a) := by
      have h2 : r (a + u) = α • r a + β • r (a + y) := hsum.symm
      calc r (a + u) - r a = α • r a + β • r (a + y) - r a := by rw [h2]
        _ = β • (r (a + y) - r a) := by
            have : α = 1 - β := by linarith
            rw [this]
            module
    rw [h1, real_inner_smul_left]
  have hAy : 0 < inner ℝ (r (a + y) - r a) (frameT r a) := by
    have h := hAmono a ha 0 y (by linarith) hy hyρ.le
    rwa [hA0] at h
  have hAu : 0 < inner ℝ (r (a + u) - r a) (frameT r a) := by
    rw [hArel]
    exact mul_pos hβ hAy
  have huρ' : -ρ < u ∧ u < ρ := abs_lt.mp huρ
  have hu_gt0 : 0 < u := by
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt'
    · rw [heq, hA0] at hAu
      exact absurd hAu (lt_irrefl 0)
    · have h := hAmono a ha u 0 (by linarith [huρ'.1]) hlt' (by linarith [hρpos])
      rw [hA0] at h
      linarith [hAu]
  have hu_lty : u < y := by
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt'
    · rw [heq] at hArel
      have h2 : inner ℝ (r (a + u) - r a) (frameT r a) * (1 - β) = 0 := by linarith
      have h3 : (0 : ℝ) < 1 - β := by linarith
      rcases mul_eq_zero.mp h2 with h5 | h5
      · linarith [hAu, h5]
      · linarith [h3, h5]
    · have h := hAmono a ha y u (by linarith [hρpos, hy.le]) hlt'
          (by linarith [huρ'.2])
      have h3 : (0 : ℝ) < 1 - β := by linarith
      have h4 : 0 < inner ℝ (r (a + y) - r a) (frameT r a) * (1 - β) := mul_pos hAy h3
      have h5 : inner ℝ (r (a + y) - r a) (frameT r a) * (1 - β) < 0 := by linarith [h, hArel]
      linarith [h4, h5]
  have hdet : det2 (frameT r a) (frameN r a) (r (a + u) - r a) (r (a + y) - r a) = 0 := by
    have h1 : r (a + u) - r a = β • (r (a + y) - r a) := by
      have h2 : r (a + u) = α • r a + β • r (a + y) := hsum.symm
      calc r (a + u) - r a = α • r a + β • r (a + y) - r a := by rw [h2]
        _ = β • (r (a + y) - r a) := by
            have : α = 1 - β := by linarith
            rw [this]
            module
    rw [h1, det2_smul_left, det2_self, mul_zero]
  exact absurd (hKEY a ha u y hu_gt0 hu_lty hyρ) (by rw [hdet]; exact lt_irrefl 0)


/-! ## 4. Translating the pair of parameters, and lifting a circle point to `ℝ` -/

/-- Membership in `liftedTrisecant` only depends on the class of `p.1` in `AddCircle period`. -/
lemma liftedTrisecant_congr_fst (r : ℝ → Space) {x x' y : ℝ}
    (h : (x : AddCircle period) = (x' : AddCircle period)) :
    (x, y) ∈ liftedTrisecant r ↔ (x', y) ∈ liftedTrisecant r := by
  have hpair : ∀ (h0 : 0 < y) (h1 : y < period),
      stripSecantClass (x', y) h0 h1 = stripSecantClass (x, y) h0 h1 := by
    intro h0 h1
    have hsp : stripPair (x', y) h0 h1 = stripPair (x, y) h0 h1 := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · simpa only [stripPair] using h.symm
      · simpa only [stripPair, AddCircle.coe_add] using
          congrArg (fun z => z + ((y : ℝ) : AddCircle period)) h.symm
    rw [stripSecantClass_eq_mobiusCover, stripSecantClass_eq_mobiusCover, hsp]
  constructor
  · rintro ⟨h0, h1, hmem⟩
    exact ⟨h0, h1, by rw [hpair h0 h1]; exact hmem⟩
  · rintro ⟨h0, h1, hmem⟩
    exact ⟨h0, h1, by rw [← hpair h0 h1]; exact hmem⟩

/-- Every point of the parameter circle has a real representative `w` with `|w| = ‖z‖`. -/
lemma exists_coe_eq_norm (z : AddCircle period) :
    ∃ w : ℝ, (w : AddCircle period) = z ∧ |w| = ‖z‖ := by
  obtain ⟨t, ht, htz⟩ := AddCircle.eq_coe_Ico z
  refine ⟨t - (round (period⁻¹ * t) : ℝ) * period, ?_, ?_⟩
  · have hzero : (((round (period⁻¹ * t) : ℝ) * period : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round (period⁻¹ * t), by simp⟩
    rw [AddCircle.coe_sub, hzero, sub_zero, htz]
  · rw [← htz]
    exact (AddCircle.norm_eq period (x := t)).symm

/-! ## 5. The middle point of a short trisecant has a nearby parameter lift -/

theorem middleLiftOfShortTrisecant {r : ℝ → Space} (hr : IsSmoothKnot r) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ period / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ × ℝ, p ∈ liftedTrisecant r →
      p.1 ∈ Set.Ico 0 period → p.2 < δ →
        ∃ w : ℝ, |w| < ρ ∧ r (p.1 + w) ∈ openSegment ℝ (r p.1) (r (p.1 + p.2)) := by
  have hper : 0 < period := period_pos
  obtain ⟨ε, hεpos, hsep⟩ := separation_of_far_parameters hr
  obtain ⟨δsep, hδseppos, hδsep⟩ := hsep ρ hρ
  have hsep' : ∀ a b : AddCircle period, ρ ≤ dist a b →
      δsep ≤ ‖knotMap r a - knotMap r b‖ :=
    fun a b h => hδsep r hr (fun t => ⟨by simpa using hεpos, by simpa using hεpos⟩) a b h
  have hd1 : ContDiff ℝ ⊤ (deriv r) := hr.smooth.deriv'
  have hc1 : Continuous (deriv r) := hd1.continuous
  have hdr : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  -- a bound for the velocity on the window `[0, period + ρ]`
  set Wb : Set ℝ := Set.Icc 0 (period + ρ) with hWbdef
  have hWbc : IsCompact Wb := isCompact_Icc
  have hWbne : Wb.Nonempty :=
    ⟨0, by rw [hWbdef]; exact ⟨le_rfl, by linarith [hper, hρ]⟩⟩
  obtain ⟨pL, hpLW, hpLmax⟩ := hWbc.exists_isMaxOn hWbne hc1.norm.continuousOn
  set L : ℝ := ‖deriv r pL‖ with hLdef
  have hLnn : 0 ≤ L := by rw [hLdef]; exact norm_nonneg _
  have hchord : ∀ x : ℝ, x ∈ Set.Ico 0 period → ∀ y : ℝ, 0 < y → y < ρ →
      ‖r (x + y) - r x‖ ≤ L * y := by
    intro x hx y hy hyρ
    have hmem : ∀ t ∈ Set.Icc x (x + y), t ∈ Wb := by
      intro t ht
      rw [Set.mem_Icc] at ht
      rw [hWbdef, Set.mem_Icc]
      exact ⟨by linarith [hx.1, ht.1], by linarith [ht.2, hx.2, hyρ.le]⟩
    have hdiff : ∀ t ∈ Set.Icc x (x + y), DifferentiableAt ℝ r t := fun t _ => hdr t
    have hbdd : ∀ t ∈ Set.Icc x (x + y), ‖deriv r t‖ ≤ L := fun t ht => by
      rw [hLdef]
      exact hpLmax (hmem t ht)
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := r)
      (s := Set.Icc x (x + y)) (x := x) (y := x + y) (C := L) hdiff hbdd
      (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith))
      (Set.right_mem_Icc.mpr (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + y - x),
      add_sub_cancel_left] at hmvt
    simpa using hmvt
  set δ : ℝ := min ρ (δsep / (2 * (L + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hρ (div_pos hδseppos (by linarith))
  refine ⟨δ, hδpos, ?_⟩
  intro p hp hxmem hyp
  obtain ⟨h0, h1, hmid⟩ := mem_liftedTrisecant_iff.mp hp
  have hiff := (HasMiddleOnClass_iff r (stripPair p h0 h1)).mp hmid
  obtain ⟨m, hm⟩ := hiff
  have hmEM : knotMap r m ∈ openSegment ℝ (r p.1) (r (p.1 + p.2)) := by
    have h := hm
    simp only [IsMiddleOnChord, stripPair] at h
    rwa [knotMap_eq_of_periodic hr.periodic p.1,
      knotMap_eq_of_periodic hr.periodic (p.1 + p.2)] at h
  have hmEM2 := hmEM
  obtain ⟨α, β, hα, hβ, hαβ, hsum⟩ := hmEM2
  have hchord' : ‖r (p.1 + p.2) - r p.1‖ ≤ L * p.2 :=
    hchord p.1 hxmem p.2 h0 (lt_of_lt_of_le hyp (min_le_left _ _))
  have hbound : ‖knotMap r m - r p.1‖ ≤ L * p.2 := by
    have h1' : knotMap r m - r p.1 = β • (r (p.1 + p.2) - r p.1) := by
      rw [← hsum]
      have hα' : α = 1 - β := by linarith
      rw [hα']
      module
    rw [h1', norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    have h2'' : β * ‖r (p.1 + p.2) - r p.1‖ ≤ β * (L * p.2) :=
      mul_le_mul_of_nonneg_left hchord' hβ.le
    have h3'' : β * (L * p.2) ≤ L * p.2 :=
      mul_le_of_le_one_left (by nlinarith [hchord', hβ.le]) (by linarith : β ≤ 1)
    linarith
  have hsmall : ‖knotMap r m - r p.1‖ < δsep := by
    have hyδ : p.2 < δsep / (2 * (L + 1)) := lt_of_lt_of_le hyp (min_le_right _ _)
    have h1' : L * p.2 ≤ L * (δsep / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hyδ.le hLnn
    have h2' : L * (δsep / (2 * (L + 1))) ≤ δsep / 2 := by
      have hL1 : (0 : ℝ) < L + 1 := by linarith
      rw [show L * (δsep / (2 * (L + 1))) = δsep * (L / (2 * (L + 1))) by ring]
      have h3' : L / (2 * (L + 1)) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (L + 1))]
        linarith
      calc δsep * (L / (2 * (L + 1))) ≤ δsep * (1 / 2) :=
            mul_le_mul_of_nonneg_left h3' hδseppos.le
        _ = δsep / 2 := by ring
    linarith [hbound, h1', h2', hδseppos]
  have hdist : dist m (p.1 : AddCircle period) < ρ := by
    by_contra hcon
    push_neg at hcon
    have h1' := hsep' m (p.1 : AddCircle period) hcon
    rw [knotMap_eq_of_periodic hr.periodic p.1] at h1'
    linarith [hsmall, h1']
  obtain ⟨w, hw1, hw2⟩ := exists_coe_eq_norm (m - (p.1 : AddCircle period))
  have hwlt : |w| < ρ := by
    rw [hw2]
    simpa only [dist_eq_norm] using hdist
  refine ⟨w, hwlt, ?_⟩
  have hxw : ((p.1 + w : ℝ) : AddCircle period) = m := by
    rw [AddCircle.coe_add, hw1]
    abel
  have hxw' : r (p.1 + w) = knotMap r m := by
    rw [← knotMap_eq_of_periodic hr.periodic (p.1 + w), hxw]
  rwa [hxw']

open LeanEval.KnotTheory.Quadrisecant in
/-- **No short trisecants under the no-inflection hypothesis.**  For a smooth knot `r` whose
velocity and acceleration are linearly independent at every parameter (a knot without inflection
points), chords of *short* parameter length carry no knot point strictly inside: the lifted
trisecant locus is bounded away from both edges `y = 0` and `y = period` of the strip, i.e. there
is `δ > 0` with `δ ≤ p.2 ≤ period - δ` for every `p ∈ liftedTrisecant r`.

Proof sketch (C² suffices; `ψ'(0) ≠ 0` comes from `hinfl`, and the top edge follows from the
deck symmetry `stripFlip`, already in the library): suppose `(xₙ, yₙ) ∈ liftedTrisecant r` with
`yₙ → 0`.  Let `mₙ` be the middle parameter of the chord `{xₙ, xₙ+yₙ}`; the middle point is at
distance `O(|yₙ|)` from `K xₙ`, so by local injectivity of the knot `mₙ ≡ xₙ + wₙ` with `wₙ → 0`.
Fix the base point `aₙ = xₙ` and the orthonormal frame `(T, N, m)` with `T = r'(a)/‖r'(a)‖` and `N`
the unit vector along the `T`-normal component of `r''(a)` (nonzero by `hinfl`).  Writing
`A(u) = ⟨r(a+u) - r(a), T⟩`, `B(u) = ⟨r(a+u) - r(a), N⟩`, the parallelity
`(r(a+w)-r(a)) ∥ (r(a+h)-r(a))` forces `A(w)B(h) = B(w)A(h)`; with `α(u) = A(u)/u`,
`β(u) = B(u)/u²` (continuous at `0` with `α(0) = ‖r'(a)‖ ≠ 0`, `β(0) = ⟨r''(a),N⟩/2 ≠ 0`) this is
`ψ(w) = ψ(h)` for `ψ(u) = uβ(u)/α(u)`; `ψ` is differentiable at `0` with
`ψ'(0) = β(0)/α(0) ≠ 0`, hence injective near `0`, so `w = h`, contradicting that the middle point
is *strictly* between the chord endpoints.  Uniformity in the base point `a` follows from
compactness of the parameter circle. -/
theorem shortSecantsFree_of_noInflection {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ × ℝ, p ∈ liftedTrisecant r →
      δ ≤ p.2 ∧ p.2 ≤ period - δ := by
  have hper : 0 < period := period_pos
  obtain ⟨ρe, hρepos, hρeper, heng⟩ := noShortMiddlePoint hr hinfl
  set ρ : ℝ := min (ρe / 2) (period / 4) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith) (by linarith [hper])
  have hρle2 : ρ ≤ period / 2 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (by linarith [hper])
  have hρlt : ρ < ρe := by
    rw [hρdef]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨δr, hδrpos, hred⟩ := middleLiftOfShortTrisecant hr ρ hρpos hρle2
  set δ : ℝ := min δr ρ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδrpos hρpos
  have hδler : δ ≤ δr := by rw [hδdef]; exact min_le_left _ _
  have hδleρ : δ ≤ ρ := by rw [hδdef]; exact min_le_right _ _
  have hlower : ∀ q : ℝ × ℝ, q ∈ liftedTrisecant r → δ ≤ q.2 := by
    intro q hq
    by_contra hcon
    push_neg at hcon
    have hqy0 : 0 < q.2 := (mem_liftedTrisecant_iff.mp hq).1
    obtain ⟨x', hx'mem, hx'eq⟩ := AddCircle.eq_coe_Ico (q.1 : AddCircle period)
    have hq' : (x', q.2) ∈ liftedTrisecant r :=
      (liftedTrisecant_congr_fst r hx'eq.symm).mp hq
    obtain ⟨w, hw, hwmem⟩ := hred (x', q.2) hq' hx'mem (lt_of_lt_of_le hcon hδler)
    have hyρe : q.2 < ρe := lt_of_lt_of_le (lt_of_lt_of_le hcon hδleρ) hρlt.le
    have hwρe : |w| < ρe := lt_of_lt_of_le hw hρlt.le
    exact heng x' ⟨hx'mem.1, hx'mem.2.le⟩ w q.2 hqy0 hyρe hwρe hwmem
  have hupper : ∀ q : ℝ × ℝ, q ∈ liftedTrisecant r → q.2 ≤ period - δ := by
    intro q hq
    have hflip : stripFlip q ∈ liftedTrisecant r :=
      (stripFlip_mem_liftedTrisecant (r := r)).mpr hq
    have h := hlower (stripFlip q) hflip
    rw [stripFlip_snd] at h
    linarith
  exact ⟨δ, hδpos, fun p hp => ⟨hlower p hp, hupper p hp⟩⟩

end

end Work.Drive
