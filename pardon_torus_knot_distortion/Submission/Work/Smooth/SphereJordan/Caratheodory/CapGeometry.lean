import Mathlib

/-!
# The cap of the unit disc at the boundary point `1`

For `0 < s < 2` the circle of radius `s` centred at the boundary point `1` of the unit disc meets
the disc in a single arc.  With the parametrisation

  `capPt s θ = 1 - s * exp(θ * I)`

(for which `exp(θ * I)` points *away* from the origin) that arc is exactly the `θ`-interval
`(-arccos (s/2), arccos (s/2))`, and it bounds the "cap" `𝔻 ∩ B(1,s)`.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-- The point `1 - s * e^{iθ}` of the circle of radius `s` centred at `1`, parametrised so that
`θ = 0` gives the point `1 - s` closest to the origin. -/
def capPt (s θ : ℝ) : ℂ := 1 - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

@[simp] lemma capPt_zero (s : ℝ) : capPt s 0 = 1 - (s : ℂ) := by
  simp [capPt]

lemma continuous_capPt (s : ℝ) : Continuous (capPt s) := by
  unfold capPt
  fun_prop

lemma capPt_re (s θ : ℝ) : (capPt s θ).re = 1 - s * Real.cos θ := by
  simp [capPt, Complex.exp_ofReal_mul_I_re]

lemma capPt_im (s θ : ℝ) : (capPt s θ).im = -(s * Real.sin θ) := by
  simp [capPt, Complex.exp_ofReal_mul_I_im]

/-- `‖capPt s θ‖ ^ 2 = 1 + s ^ 2 - 2 * s * cos θ`. -/
lemma sq_norm_capPt (s θ : ℝ) : ‖capPt s θ‖ ^ 2 = 1 + s ^ 2 - 2 * s * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply, capPt_re, capPt_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma norm_capPt_sub_one (s θ : ℝ) : ‖capPt s θ - 1‖ = |s| := by
  have h : capPt s θ - 1 = -((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    simp [capPt]
  rw [h, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- The arc lies in the unit disc exactly on `|θ| < arccos (s/2)`. -/
lemma capPt_mem_ball_iff {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (θ : ℝ) :
    capPt s θ ∈ Metric.ball (0 : ℂ) 1 ↔ s / 2 < Real.cos θ := by
  rw [Metric.mem_ball, dist_zero_right]
  have h := sq_norm_capPt s θ
  constructor
  · intro hlt
    have h1 : ‖capPt s θ‖ ^ 2 < 1 := by nlinarith [norm_nonneg (capPt s θ)]
    rw [h] at h1
    nlinarith [hs, hs2]
  · intro hlt
    have h1 : ‖capPt s θ‖ ^ 2 < 1 := by rw [h]; nlinarith [hs]
    nlinarith [norm_nonneg (capPt s θ)]

/-- **The crossing angle**: the circle of radius `s` about `1` meets the unit circle exactly where
`cos θ = s / 2`. -/
def capAlpha (s : ℝ) : ℝ := Real.arccos (s / 2)

lemma capAlpha_pos {s : ℝ} (hs : s < 2) : 0 < capAlpha s := by
  rw [capAlpha, Real.arccos_pos]; linarith

lemma capAlpha_lt_pi_div_two {s : ℝ} (hs : 0 < s) : capAlpha s < Real.pi / 2 := by
  rw [capAlpha, Real.arccos_lt_pi_div_two]; linarith

lemma capAlpha_lt_pi {s : ℝ} (hs : 0 < s) : capAlpha s < Real.pi := by
  have := capAlpha_lt_pi_div_two hs; linarith [Real.pi_pos]

lemma cos_capAlpha {s : ℝ} (hs : 0 < s) (hs2 : s < 2) : Real.cos (capAlpha s) = s / 2 := by
  rw [capAlpha, Real.cos_arccos (by linarith) (by linarith)]

lemma capAlpha_nonneg (s : ℝ) : 0 ≤ capAlpha s := Real.arccos_nonneg (s / 2)

/-- The arc of the circle of radius `s` about `1` inside the unit disc, as a set of parameters. -/
lemma capArc_set {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (Set.Ioo (-Real.pi) Real.pi ∩ {θ : ℝ | s / 2 < Real.cos θ}) =
      Set.Ioo (-(capAlpha s)) (capAlpha s) := by
  have hα0 : 0 < capAlpha s := capAlpha_pos hs2
  have hαπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have hcos : Real.cos (capAlpha s) = s / 2 := cos_capAlpha hs hs2
  ext θ
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    have key : ∀ x : ℝ, -Real.pi < x → x < Real.pi → s / 2 < Real.cos x →
        -capAlpha s < x ∧ x < capAlpha s := by
      intro x hx1 hx2 hcx
      constructor
      · by_contra hcon
        push_neg at hcon
        have h3 : Real.cos (-x) ≤ Real.cos (capAlpha s) := by
          rcases lt_or_eq_of_le hcon with hlt | heq
          · exact le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi (x := capAlpha s) (y := -x)
              hα0.le (by linarith) (by linarith))
          · rw [heq]; simp
        rw [Real.cos_neg, hcos] at h3
        linarith
      · by_contra hcon
        push_neg at hcon
        have h3 : Real.cos x ≤ Real.cos (capAlpha s) := by
          rcases lt_or_eq_of_le hcon with hlt | heq
          · exact le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi (x := capAlpha s) (y := x)
              hα0.le (by linarith) hlt)
          · rw [heq]
        rw [hcos] at h3
        linarith
    exact key θ h1 h2 hc
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · by_cases h : 0 ≤ θ
      · have h3 : Real.cos (capAlpha s) < Real.cos θ :=
          Real.cos_lt_cos_of_nonneg_of_le_pi h hαπ.le h2
        rw [hcos] at h3; linarith
      · push_neg at h
        have h3 : Real.cos (capAlpha s) < Real.cos (-θ) :=
          Real.cos_lt_cos_of_nonneg_of_le_pi (x := -θ) (y := capAlpha s)
            (by linarith) hαπ.le (by linarith)
        rw [Real.cos_neg] at h3
        linarith [hcos]

/-- `capPt s` is injective on `(-π, π)`. -/
lemma capPt_injOn {s : ℝ} (hs : 0 < s) : Set.InjOn (capPt s) (Set.Ioo (-Real.pi) Real.pi) := by
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  intro θ hθ θ' hθ' heq
  have h3 : (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      (s : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
    have h2 : (1 : ℂ) - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
        (1 : ℂ) - (s : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
      simpa [capPt] using heq
    have h2' := congrArg (fun z : ℂ => (1 : ℂ) - z) h2
    rw [show (1 : ℂ) - (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring,
      show (1 : ℂ) - (1 - (s : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I)) =
        (s : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) from by ring] at h2'
    exact h2'
  have hE : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) :=
    mul_left_cancel₀ hsne h3
  have h1 : Complex.exp (((θ : ℂ) - (θ' : ℂ)) * Complex.I) = 1 := by
    rw [sub_mul, Complex.exp_sub, hE, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : ((θ : ℂ) - (θ' : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h4 : ((θ : ℂ) - (θ' : ℂ)) * Complex.I = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ hI h4
  have h5 : (θ : ℝ) - θ' = (n : ℝ) * (2 * Real.pi) := by
    have e1 : (((θ : ℝ) - θ' : ℝ) : ℂ) = ((θ : ℂ) - (θ' : ℂ)) := by push_cast; ring
    have e2 : ((θ : ℂ) - (θ' : ℂ)) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [h2]; push_cast; ring
    exact_mod_cast (e1.trans e2)
  rw [Set.mem_Ioo] at hθ hθ'
  have hlt1 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by
    rw [← h5]; linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hlt2 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    rw [← h5]; linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hn0 : (n : ℝ) = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have hle : (n : ℝ) ≤ -1 := by
        have : n ≤ -1 := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]
    · exact_mod_cast h
    · have hge : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℤ) ≤ n := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]
  have h6 : (n : ℝ) * (2 * Real.pi) = 0 := by rw [hn0]; ring
  linarith

/-- The derivative of the parametrisation. -/
lemma hasDerivAt_capPt (s θ : ℝ) :
    HasDerivAt (capPt s) (-(Complex.I * (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
  have h2 : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ :=
    (Complex.hasDerivAt_exp _).comp θ h1
  have h3 : HasDerivAt (fun x : ℝ => (s : ℂ) * Complex.exp ((x : ℂ) * Complex.I))
      ((s : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ := h2.const_mul (s : ℂ)
  have h4 : HasDerivAt (fun x : ℝ => 1 - (s : ℂ) * Complex.exp ((x : ℂ) * Complex.I))
      (-((s : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) θ := h3.const_sub 1
  have heq : (fun x : ℝ => 1 - (s : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) = capPt s := rfl
  rw [heq] at h4
  convert h4 using 1
  ring

lemma norm_deriv_capPt (s θ : ℝ) :
    ‖-(Complex.I * (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = |s| := by
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs]

end Work.Smooth.SphereJordan.Caratheodory
