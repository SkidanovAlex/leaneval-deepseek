import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.Distortion.min_shift_zsmul

/-!
# Reparametrization invariance of knot distortion

The distortion of a smooth knot `K` is defined as the supremum, over pairs of
distinct parameters `s, t` in the fundamental interval `[0, 2π)`, of the
quotient `intrinsicDistance K s t / dist (K.curve s) (K.curve t)`.

Here we prove that this quantity only depends on the embedded curve and not on
the chosen parametrization: if `K'.curve t = K.curve (σ.f t)` for an
orientation-preserving smooth circle reparametrization `σ`, then
`distortion K' = distortion K`.

The proof has two ingredients.

* The substitution rule for the arclength integral: the arclength between the
  parameters `a` and `b` for `K'` equals the arclength between `σ.f a` and
  `σ.f b` for `K`.  Consequently the distortion ratio satisfies
  `distortionRatio K' s t = distortionRatio K (σ.f s) (σ.f t)`.

* The ratio only depends on the parameters modulo `2π`.  Passing to the
  representative in `[0, 2π)` of a parameter changes the signed arclength by an
  integer multiple of the total arclength, which leaves
  `min |z| (T - |z|)` unchanged as long as the parameter pair lies in a window
  of length `2π`.

Combining the two, the set of distortion ratios of `K'` is the set of
distortion ratios of `K`, hence the suprema coincide.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal

namespace Work.Distortion

noncomputable section

/-- The *signed* arclength of `K` between the parameters `s` and `t`. -/
noncomputable def arc (K : Knot) (s t : ℝ) : ℝ := ∫ u in s..t, speed K u

/-- The derivative of a `2π`-periodic curve is `2π`-periodic. -/
lemma deriv_curve_periodic (K : Knot) (t : ℝ) :
    deriv K.curve (t + 2 * Real.pi) = deriv K.curve t := by
  have hshift : HasDerivAt (fun x : ℝ => x + 2 * Real.pi) 1 t := by
    simpa using (hasDerivAt_id t).add_const (2 * Real.pi)
  have hd : DifferentiableAt ℝ K.curve (t + 2 * Real.pi) :=
    (K.smooth.differentiable (by simp)).differentiableAt
  have hcomp : HasDerivAt (K.curve ∘ fun x : ℝ => x + 2 * Real.pi)
      ((1 : ℝ) • deriv K.curve (t + 2 * Real.pi)) t :=
    (hasDerivAt_deriv_iff.mpr hd).scomp t hshift
  have hfun : (K.curve ∘ fun x : ℝ => x + 2 * Real.pi) = K.curve := by
    funext x; exact K.periodic x
  rw [hfun, one_smul] at hcomp
  exact hcomp.deriv.symm

/-- The speed of a `2π`-periodic curve is `2π`-periodic. -/
lemma speed_periodic (K : Knot) : Function.Periodic (speed K) (2 * Real.pi) := fun t => by
  simp only [speed, deriv_curve_periodic K t]

lemma speed_continuous (K : Knot) : Continuous (speed K) := by
  have h : Continuous (deriv K.curve) := K.smooth.continuous_deriv (by simp)
  exact h.norm

lemma speed_nonneg (K : Knot) (t : ℝ) : 0 ≤ speed K t := norm_nonneg _

lemma arc_nonneg (K : Knot) {a b : ℝ} (h : a ≤ b) : 0 ≤ arc K a b := by
  simp only [arc]
  exact intervalIntegral.integral_nonneg h (fun x _ => speed_nonneg K x)

/-- Shifting *both* endpoints of the arclength integral by an integral number of
periods does not change it. -/
lemma arc_shift (K : Knot) (s t : ℝ) (n : ℤ) :
    arc K (s + n * (2 * Real.pi)) (t + n * (2 * Real.pi)) = arc K s t := by
  have hp := speed_periodic K
  rw [arc, arc]
  rw [← intervalIntegral.integral_comp_add_right (speed K) (n * (2 * Real.pi))]
  apply intervalIntegral.integral_congr
  intro x _
  exact hp.int_mul n x

/-- The arclength over any full period is the total arclength. -/
lemma arc_period (K : Knot) (s : ℝ) : arc K s (s + 2 * Real.pi) = arc K 0 (2 * Real.pi) := by
  have h := (speed_periodic K).intervalIntegral_add_eq s 0
  simpa [arc] using h

lemma arc_period_n (K : Knot) (a : ℝ) (n : ℤ) :
    arc K a (a + (n:ℝ) * (2 * Real.pi)) = (n:ℝ) * arc K 0 (2 * Real.pi) := by
  have hint : ∀ t₁ t₂, IntervalIntegrable (speed K) volume t₁ t₂ :=
    fun t₁ t₂ => (speed_continuous K).intervalIntegrable t₁ t₂
  have hz := (speed_periodic K).intervalIntegral_add_zsmul_eq n a hint
  simp only [zsmul_eq_mul] at hz
  have hp := arc_period K a
  simp only [arc] at hp ⊢
  rw [hz, hp]

lemma arc_add_period (K : Knot) (a b : ℝ) (n : ℤ) :
    arc K a (b + (n:ℝ) * (2 * Real.pi))
      = arc K a b + (n:ℝ) * arc K 0 (2 * Real.pi) := by
  have hint : ∀ t₁ t₂, IntervalIntegrable (speed K) volume t₁ t₂ :=
    fun t₁ t₂ => (speed_continuous K).intervalIntegrable t₁ t₂
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint a b)
    (hint b (b + (n:ℝ) * (2 * Real.pi)))
  have hpn := arc_period_n K b n
  simp only [arc] at hadd hpn ⊢
  rw [← hadd, hpn]

lemma totalArcLength_eq (K : Knot) : totalArcLength K = arc K 0 (2 * Real.pi) := by
  have h : (0:ℝ) ≤ arc K 0 (2 * Real.pi) := arc_nonneg K (by positivity)
  simp only [totalArcLength, parameterArcLength, arc]
  exact abs_of_nonneg h

/-- The absolute value of a signed arclength is bounded by the total arclength
whenever the parameters are at most one period apart. -/
lemma arc_abs_le_total (K : Knot) {a b : ℝ} (h : |b - a| ≤ 2 * Real.pi) :
    |arc K a b| ≤ totalArcLength K := by
  have hint : ∀ t₁ t₂, IntervalIntegrable (speed K) volume t₁ t₂ :=
    fun t₁ t₂ => (speed_continuous K).intervalIntegrable t₁ t₂
  have hle : ∀ p q : ℝ, p ≤ q → q ≤ p + 2*Real.pi → arc K p q ≤ arc K 0 (2 * Real.pi) := by
    intro p q _ hq
    rw [← arc_period K p]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint p q)
      (hint q (p + 2*Real.pi))
    simp only [arc] at hadd ⊢
    rw [← hadd]
    have h0 : 0 ≤ ∫ x in q..p + 2*Real.pi, speed K x := by
      apply intervalIntegral.integral_nonneg hq
      intro x _; exact speed_nonneg K x
    linarith
  have h3 : a - b ≤ 2 * Real.pi := by linarith [(abs_le.mp h).1]
  rw [totalArcLength_eq K]
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (arc_nonneg K hab)]
    exact hle a b hab (by linarith [(abs_le.mp h).2])
  · have hsym : arc K a b = - arc K b a := by
      have hs : ∫ x in b..a, speed K x = -∫ x in a..b, speed K x :=
        intervalIntegral.integral_symm a b
      simp only [arc]; linarith
    rw [hsym, abs_neg, abs_of_nonneg (arc_nonneg K hba)]
    exact hle b a hba (by linarith)

/-! ### Substitution rule and reparametrization of the arclength -/

lemma speed_reparam (K K' : Knot) (σ : CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) (t : ℝ) :
    speed K' t = speed K (σ.f t) * deriv σ.f t := by
  have hderiv : deriv K'.curve t = deriv σ.f t • deriv K.curve (σ.f t) := by
    have hfun : K'.curve = K.curve ∘ σ.f := funext h
    have hσd : DifferentiableAt ℝ σ.f t := (σ.smooth.differentiable (by simp)).differentiableAt
    have hKd : DifferentiableAt ℝ K.curve (σ.f t) :=
      (K.smooth.differentiable (by simp)).differentiableAt
    have hcomp : HasDerivAt (K.curve ∘ σ.f) (deriv σ.f t • deriv K.curve (σ.f t)) t :=
      (hasDerivAt_deriv_iff.mpr hKd).scomp t (hasDerivAt_deriv_iff.mpr hσd)
    rw [hfun]; exact hcomp.deriv
  have hnn : 0 ≤ deriv σ.f t := Monotone.deriv_nonneg σ.mono.monotone
  rw [speed, hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, speed]
  ring

/-- The change of variables formula for the arclength integral. -/
lemma arc_reparam (K K' : Knot) (σ : CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) (a b : ℝ) :
    arc K' a b = arc K (σ.f a) (σ.f b) := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt σ.f (deriv σ.f x) x := fun x _ =>
    hasDerivAt_deriv_iff.mpr ((σ.smooth.differentiable (by simp)).differentiableAt)
  have hcont : Continuous fun x => deriv σ.f x := σ.smooth.continuous_deriv (by simp)
  have hsub := intervalIntegral.integral_comp_mul_deriv (a:=a) (b:=b) (f:=σ.f)
      (f':= fun x => deriv σ.f x) (g:= speed K) hderiv hcont.continuousOn (speed_continuous K)
  rw [arc, arc, ← hsub]
  apply intervalIntegral.integral_congr
  intro x _
  exact speed_reparam K K' σ h x

lemma totalArcLength_reparam (K K' : Knot) (σ : CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) : totalArcLength K' = totalArcLength K := by
  have hf2 : σ.f (2*Real.pi) = σ.f 0 + 2*Real.pi := by simpa using σ.periodic 0
  have h1 : arc K' 0 (2*Real.pi) = arc K 0 (2*Real.pi) := by
    rw [arc_reparam K K' σ h 0 (2*Real.pi), hf2, arc_period]
  simp only [arc] at h1
  simp only [totalArcLength, parameterArcLength]
  rw [h1]

lemma distortionRatio_reparam (K K' : Knot) (σ : CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) (s t : ℝ) :
    distortionRatio K' s t = distortionRatio K (σ.f s) (σ.f t) := by
  have hpa0 : arc K' s t = arc K (σ.f s) (σ.f t) := arc_reparam K K' σ h s t
  simp only [arc] at hpa0
  have hpa : parameterArcLength K' s t = parameterArcLength K (σ.f s) (σ.f t) := by
    simp only [parameterArcLength]; rw [hpa0]
  have hT := totalArcLength_reparam K K' σ h
  simp only [distortionRatio, intrinsicDistance]
  rw [hpa, hT, h s, h t]

/-! ### Reduction of an arbitrary parameter to `[0, 2π)` -/

/-- The representative of `t` in the half-open interval `[0, 2π)`. -/
noncomputable def res (t : ℝ) : ℝ := t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

lemma res_mem (t : ℝ) : res t ∈ Set.Ico 0 (2 * Real.pi) := by
  refine ⟨?_, ?_⟩
  · have h := Int.floor_le (t / (2 * Real.pi))
    have h2 : (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ t := by
      have hm := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      rwa [div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at hm
    simp only [res]; linarith
  · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
    have h2 : t < (⌊t/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) + 2*Real.pi := by
      have hm := mul_lt_mul_of_pos_right h (by positivity : (0:ℝ) < 2 * Real.pi)
      rw [div_mul_cancel₀ _ (by positivity : (2*Real.pi) ≠ 0)] at hm
      have hh : ((⌊t/(2*Real.pi)⌋:ℝ) + 1) * (2*Real.pi)
          = (⌊t/(2*Real.pi)⌋:ℝ) * (2*Real.pi) + 2*Real.pi := by ring
      linarith [hm, hh]
    simp only [res]; linarith

lemma curve_res (K : Knot) (t : ℝ) : K.curve (res t) = K.curve t := by
  have hp : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  have h : K.curve (t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) = K.curve t :=
    hp.sub_int_mul_eq (⌊t / (2 * Real.pi)⌋)
  simpa [res] using h

lemma res_injOn (c : ℝ) : Set.InjOn res (Set.Ico c (c + 2 * Real.pi)) := by
  intro u hu w hw h
  have hu2 : u < c + 2 * Real.pi := hu.2
  have hw1 : c ≤ w := hw.1
  have hw2 : w < c + 2 * Real.pi := hw.2
  have hu1 : c ≤ u := hu.1
  have hdiff : u - w = ((⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    have h3 : u - (⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi)
        = w - (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) := by
      have := h; simp only [res] at this; exact this
    calc u - w
      _ = (u - (⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi))
            - (w - (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi))
            + ((⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi)
                - (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi)) := by ring
      _ = ((⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi)
                - (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi)) := by rw [h3]; ring
      _ = ((⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  have hlt : |u - w| < 2 * Real.pi := by
    rw [abs_lt]; constructor <;> linarith
  have h1 : |((⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋ : ℤ) : ℝ)| < 1 := by
    have hm : |u - w| = |((⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋ : ℤ) : ℝ)| * (2*Real.pi) := by
      rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    rw [hm] at hlt
    nlinarith [Real.pi_pos]
  have h2 : ((|⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]; exact h1
  have h3 : |⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋| < 1 := by exact_mod_cast h2
  have hn : (⌊u/(2*Real.pi)⌋ - ⌊w/(2*Real.pi)⌋ : ℤ) = 0 := Int.abs_lt_one_iff.mp h3
  have : u - w = 0 := by rw [hdiff, hn]; push_cast; ring
  linarith

/-- Passing to the representative in `[0, 2π)` changes the signed arclength by
an integer multiple of the total arclength. -/
lemma arc_residue (K : Knot) (u w : ℝ) :
    arc K u w = arc K (res u) (res w)
      + ((⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋ : ℤ) : ℝ) * arc K 0 (2 * Real.pi) := by
  have hresu : res u = u - (⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) := by rw [res]
  have hresw : res w = w - (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) := by rw [res]
  have hu : u = res u + (⌊u/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) := by rw [hresu]; ring
  have hw : w = res w + (⌊w/(2*Real.pi)⌋ : ℝ) * (2*Real.pi) := by rw [hresw]; ring
  have key : arc K u w = arc K (res u)
      (res w + ((⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi)) := by
    conv_lhs => rw [hu, hw]
    have hs := arc_shift K (res u)
      (res w + ((⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi)) (⌊u/(2*Real.pi)⌋)
    rw [← hs]
    congr 1
    push_cast
    ring
  rw [key, arc_add_period]

/-- The intrinsic distance is unchanged by passing to representatives in
`[0, 2π)`, as long as the two parameters lie in a common window of length `2π`. -/
lemma intrinsicDistance_residue (K : Knot) {u w : ℝ} (h : |u - w| ≤ 2 * Real.pi) :
    intrinsicDistance K u w = intrinsicDistance K (res u) (res w) := by
  have hT : 0 ≤ totalArcLength K := by rw [totalArcLength_eq]; exact arc_nonneg K (by positivity)
  have hx : |arc K (res u) (res w)| ≤ totalArcLength K := by
    apply arc_abs_le_total
    have h1 := res_mem u; have h2 := res_mem w
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hy : |arc K u w| ≤ totalArcLength K := by
    apply arc_abs_le_total; rw [abs_sub_comm]; exact h
  have hres : arc K (res u) (res w)
      + ((⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋ : ℤ) : ℝ) * totalArcLength K = arc K u w := by
    rw [arc_residue K u w, totalArcLength_eq K]
  have hy' : |arc K (res u) (res w)
      + ((⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋ : ℤ) : ℝ) * totalArcLength K| ≤ totalArcLength K := by
    rw [hres]; exact hy
  have hmin := min_shift_zsmul (totalArcLength K) (arc K (res u) (res w))
    (⌊w/(2*Real.pi)⌋ - ⌊u/(2*Real.pi)⌋) hT hx hy'
  simp only [intrinsicDistance, parameterArcLength]
  change min |arc K u w| (totalArcLength K - |arc K u w|)
       = min |arc K (res u) (res w)| (totalArcLength K - |arc K (res u) (res w)|)
  rw [← hres, hmin]

lemma distortionRatio_residue (K : Knot) {u w : ℝ} (h : |u - w| ≤ 2 * Real.pi) :
    distortionRatio K u w = distortionRatio K (res u) (res w) := by
  simp only [distortionRatio]
  rw [intrinsicDistance_residue K h, ← curve_res K u, ← curve_res K w]

lemma abs_sub_le_of_mem_Ico {c u w : ℝ}
    (hu : u ∈ Set.Ico c (c + 2*Real.pi)) (hw : w ∈ Set.Ico c (c + 2*Real.pi)) :
    |w - u| ≤ 2*Real.pi := by
  rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hw.1, hw.2]

lemma reparam_mem (σ : CircleReparam) {s : ℝ} (hs : s ∈ Set.Ico 0 (2*Real.pi)) :
    σ.f s ∈ Set.Ico (σ.f 0) (σ.f 0 + 2*Real.pi) := by
  refine ⟨σ.mono.monotone hs.1, ?_⟩
  have h2π : σ.f (2*Real.pi) = σ.f 0 + 2*Real.pi := by simpa using σ.periodic 0
  rw [← h2π]
  exact σ.mono hs.2

/-- The inverse of an orientation-preserving circle reparametrization. -/
noncomputable def reparamInv (σ : CircleReparam) : CircleReparam where
  f := σ.finv
  finv := σ.f
  smooth := σ.smooth_inv
  smooth_inv := σ.smooth
  left_inv := σ.right_inv
  right_inv := σ.left_inv
  periodic := σ.periodic_inv
  periodic_inv := σ.periodic
  mono := fun a b hab => by
    rcases lt_trichotomy (σ.finv a) (σ.finv b) with hlt | heq | hgt
    · exact hlt
    · exfalso
      have := congrArg σ.f heq
      rw [σ.right_inv a, σ.right_inv b] at this
      exact absurd this (ne_of_lt hab)
    · exfalso
      have h' := σ.mono hgt
      rw [σ.right_inv a, σ.right_inv b] at h'
      exact absurd h' (not_lt.mpr hab.le)

/-! ### The distortion ratio sets -/

/-- The set of distortion ratios over the fundamental interval, whose supremum
is the distortion. -/
noncomputable def ratioSet (K : Knot) : Set ℝ≥0∞ :=
  {d | ∃ s ∈ Set.Ico (0:ℝ) (2*Real.pi), ∃ t ∈ Set.Ico (0:ℝ) (2*Real.pi),
    s ≠ t ∧ d = ENNReal.ofReal (distortionRatio K s t)}

lemma distortion_eq_sSup (K : Knot) : distortion K = sSup (ratioSet K) := rfl

theorem ratioSet_subset_of_reparam (K K' : Knot) (σ : CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) : ratioSet K' ⊆ ratioSet K := by
  rintro d ⟨s, hs, t, ht, hst, rfl⟩
  have hφs := reparam_mem σ hs
  have hφt := reparam_mem σ ht
  have hne : σ.f s ≠ σ.f t := fun heq => hst (σ.mono.injective heq)
  refine ⟨res (σ.f s), res_mem _, res (σ.f t), res_mem _, ?_, ?_⟩
  · intro heq
    exact hne (res_injOn (σ.f 0) hφs hφt heq)
  · rw [distortionRatio_reparam K K' σ h s t,
        distortionRatio_residue K (u := σ.f s) (w := σ.f t)
          (abs_sub_le_of_mem_Ico (c := σ.f 0) (u := σ.f t) (w := σ.f s) hφt hφs)]

theorem reparam_invariance (K K' : LeanEval.KnotTheory.PardonDistortion.Knot)
    (σ : LeanEval.KnotTheory.PardonDistortion.CircleReparam)
    (h : ∀ t, K'.curve t = K.curve (σ.f t)) :
    LeanEval.KnotTheory.PardonDistortion.distortion K' = LeanEval.KnotTheory.PardonDistortion.distortion K := by
  have h1 : ratioSet K' ⊆ ratioSet K := ratioSet_subset_of_reparam K K' σ h
  have h2 : ratioSet K ⊆ ratioSet K' := by
    apply ratioSet_subset_of_reparam K' K (reparamInv σ)
    intro t
    calc K.curve t = K.curve (σ.f (σ.finv t)) := by rw [σ.right_inv t]
      _ = K'.curve (σ.finv t) := (h (σ.finv t)).symm
  have hset : ratioSet K' = ratioSet K := Set.Subset.antisymm h1 h2
  rw [distortion_eq_sSup, distortion_eq_sSup, hset]

end

end Work.Distortion
