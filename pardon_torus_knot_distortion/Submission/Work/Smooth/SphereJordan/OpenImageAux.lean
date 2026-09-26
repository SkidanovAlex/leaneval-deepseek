import Mathlib
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk

/-!
# Invariance of domain for an embedded disc in the plane

This file proves that a continuous injective map `𝔻 → ℂ` of the closed unit disc has open image
(restricted to the interior of the disc): the image of the open disc is open in `ℂ`.  This is
Brouwer's *invariance of domain* in dimension two, in the form needed by the sphere/Schoenflies
chapter.

The proof is the classical one, in the form in which it is cheapest to formalise:

* if `g` were not an embedding onto a neighbourhood of `g 0`, there would be a point `c` with
  `‖c - g 0‖ < min_{‖s‖ = 1} ‖g s - g 0‖` outside `g '' {‖z‖ < 1}`;
* then the loops `β` (the normalised `g (circlePoint ·) - c`), `γ` (the normalised
  `g (circlePoint ·) - g 0`) and `δ` (the normalised `g (circlePoint ·) - g (-circlePoint ·)`)
  are homotopic to one another, while `β` extends over the disc and `δ` is odd;
* a loop extending over the disc has *vanishing winding number*, while an odd loop has *nonzero*
  winding number — both statements about the lift of the loop to the universal cover
  `Circle.exp : ℝ → Circle`, which is what the three lemmas below provide.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Lifting loops of the circle to the line -/

/-- Every continuous loop of the circle has a continuous lift to the line. -/
theorem exists_continuous_lift (φ : C(ℝ, Circle)) :
    ∃ Λ : C(ℝ, ℝ), ∀ t : ℝ, Circle.exp (Λ t) = φ t := by
  obtain ⟨Λ, hspec, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts φ 0
    (Complex.arg (φ 0)) (Circle.exp_arg (φ 0))
  exact ⟨Λ, fun t => congr_fun hspec.2 t⟩

/-- Two continuous lifts of the same loop of the circle differ by a constant. -/
theorem lift_sub_eq_const {Λ₁ Λ₂ : ℝ → ℝ} (h₁ : Continuous Λ₁) (h₂ : Continuous Λ₂)
    (h : ∀ t : ℝ, Circle.exp (Λ₁ t) = Circle.exp (Λ₂ t)) (t : ℝ) :
    Λ₁ t - Λ₂ t = Λ₁ 0 - Λ₂ 0 := by
  have hc : Continuous fun t : ℝ => Λ₁ t - Λ₂ t := h₁.sub h₂
  refine Circle.isCoveringMap_exp.const_of_comp hc (fun a a' => ?_) t 0
  rw [Circle.exp_sub, Circle.exp_sub, h a, h a', div_self', div_self']

/-- `Circle.exp π = -1`, used to recognise the antipode in the circle. -/
theorem circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.coe_inj.mp
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
  exact Complex.exp_pi_mul_I

/-- **A loop extending over the disc has zero lift-difference.** -/
theorem lift_diff_eq_zero_of_extends (φ : ℝ → Circle) (hφ : Continuous φ)
    (hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t) (Φ : C(Disc, Circle))
    (hΦ : ∀ θ : ℝ, Φ (circlePoint θ) = φ θ) (Λ : ℝ → ℝ) (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = φ t) :
    Λ (2 * Real.pi) - Λ 0 = 0 := by
  rw [Work.CoreTopology.circle_lift_eq_of_extends_disk φ hφ hper Φ hΦ Λ hΛ hlift, sub_self]

/-- **An odd loop has nonzero lift-difference.**  Here `φ (t + π) = - φ t`. -/
theorem lift_diff_ne_zero_of_odd (φ : ℝ → Circle) (Λ : ℝ → ℝ) (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = φ t)
    (hodd : ∀ t : ℝ, φ (t + Real.pi) = - (φ t)) :
    Λ (2 * Real.pi) - Λ 0 ≠ 0 := by
  intro hzero
  -- `t ↦ Λ (t + π) - Λ t` is constant, because its exponential is constantly `-1`
  have hc : Continuous fun t : ℝ => Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ) := by fun_prop
  have hval : ∀ t : ℝ, Complex.exp (Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ)) = -1 := by
    intro t
    have hsplit : Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ)
        = ((Λ (t + Real.pi) : ℂ) * Complex.I) - ((Λ t : ℂ) * Complex.I) := by
      push_cast; ring
    have hφπ : Complex.exp ((Λ (t + Real.pi) : ℂ) * Complex.I) = ((φ (t + Real.pi) : Circle) : ℂ) := by
      rw [← Circle.coe_exp, hlift (t + Real.pi)]
    have hφ : Complex.exp ((Λ t : ℂ) * Complex.I) = ((φ t : Circle) : ℂ) := by
      rw [← Circle.coe_exp, hlift t]
    rw [hsplit, Complex.exp_sub, hφπ, hφ, hodd t, Circle.coe_neg, neg_div,
      div_self (Circle.coe_ne_zero (φ t))]
  have hconst := Complex.isCoveringMap_exp.const_of_comp hc
    (fun a a' => Subtype.ext (by
      show Complex.exp (Complex.I * ((Λ (a + Real.pi) - Λ a : ℝ) : ℂ))
          = Complex.exp (Complex.I * ((Λ (a' + Real.pi) - Λ a' : ℝ) : ℂ))
      rw [hval a, hval a'])) (0 : ℝ) Real.pi
  have hc0 : Λ Real.pi - Λ 0 = Λ (2 * Real.pi) - Λ Real.pi := by
    have h := mul_left_cancel₀ Complex.I_ne_zero hconst
    simp only [zero_add] at h
    rw [show Real.pi + Real.pi = 2 * Real.pi by ring] at h
    push_cast at h ⊢
    exact_mod_cast h
  -- the common value `Λ π - Λ 0` is `π + 2πk`
  have hpeak : Circle.exp (Λ Real.pi - Λ 0) = -1 := by
    apply Circle.coe_inj.mp
    rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
    have h := hval 0
    simpa [mul_comm] using h
  have hpe : Circle.exp (Λ Real.pi - Λ 0) = Circle.exp Real.pi := by
    rw [hpeak, circle_exp_pi]
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hpe
  have hD : Λ (2 * Real.pi) - Λ 0 = 2 * (Λ Real.pi - Λ 0) := by linarith
  have hzero' : 2 * (Real.pi + (k : ℝ) * (2 * Real.pi)) = 0 := by linarith [hzero, hD, hk]
  have h2 : (2 * Real.pi) * (1 + 2 * (k : ℝ)) = 0 := by linarith
  have h3 : (1 + 2 * (k : ℝ)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    · exact h
  have h4 : (2 * k + 1 : ℤ) = 0 := by
    have : ((2 * k + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  omega

/-- **The lift-difference is a homotopy invariant of loops.** -/
theorem lift_diff_eq_of_homotopy (K : C(ℝ × ℝ, Circle)) (Λ₀ Λ₁ : ℝ → ℝ)
    (hKper : ∀ t s : ℝ, K (t + 2 * Real.pi, s) = K (t, s))
    (h₀c : Continuous Λ₀) (h₀ : ∀ t : ℝ, Circle.exp (Λ₀ t) = K (t, 0))
    (h₁c : Continuous Λ₁) (h₁ : ∀ t : ℝ, Circle.exp (Λ₁ t) = K (t, 1)) :
    Λ₀ (2 * Real.pi) - Λ₀ 0 = Λ₁ (2 * Real.pi) - Λ₁ 0 := by
  obtain ⟨KL, hKspec, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts K (0, 0)
    (Complex.arg (K (0, 0))) (Circle.exp_arg (K (0, 0)))
  have hKL : ∀ p : ℝ × ℝ, Circle.exp (KL p) = K p := fun p => congr_fun hKspec.2 p
  have hW : Continuous fun p : ℝ × ℝ => KL (p.1 + 2 * Real.pi, p.2) - KL (p.1, p.2) := by fun_prop
  have hWval : ∀ p : ℝ × ℝ, Circle.exp (KL (p.1 + 2 * Real.pi, p.2) - KL (p.1, p.2)) = 1 := by
    intro p
    rw [Circle.exp_sub, hKL (p.1 + 2 * Real.pi, p.2), hKL (p.1, p.2), hKper, div_self']
  have hWconst (p q : ℝ × ℝ) :
      KL (p.1 + 2 * Real.pi, p.2) - KL (p.1, p.2)
        = KL (q.1 + 2 * Real.pi, q.2) - KL (q.1, q.2) :=
    Circle.isCoveringMap_exp.const_of_comp hW (fun a a' => by rw [hWval a, hWval a']) p q
  have hkl0 : Continuous fun t : ℝ => KL (t, 0) := by fun_prop
  have hkl1 : Continuous fun t : ℝ => KL (t, 1) := by fun_prop
  have key₀ (t : ℝ) : Λ₀ t - KL (t, 0) = Λ₀ 0 - KL (0, 0) :=
    lift_sub_eq_const h₀c hkl0 (fun s => by rw [h₀ s, hKL (s, 0)]) t
  have key₁ (t : ℝ) : Λ₁ t - KL (t, 1) = Λ₁ 0 - KL (0, 1) :=
    lift_sub_eq_const h₁c hkl1 (fun s => by rw [h₁ s, hKL (s, 1)]) t
  have e₀ : KL (2 * Real.pi, 0) - KL (0, 0) = Λ₀ (2 * Real.pi) - Λ₀ 0 := by
    linarith [key₀ (2 * Real.pi), key₀ 0]
  have e₁ : KL (2 * Real.pi, 1) - KL (0, 1) = Λ₁ (2 * Real.pi) - Λ₁ 0 := by
    linarith [key₁ (2 * Real.pi), key₁ 0]
  have e₂ : KL (2 * Real.pi, 0) - KL (0, 0) = KL (2 * Real.pi, 1) - KL (0, 1) := by
    simpa using hWconst (0, 0) (0, 1)
  linarith [e₀, e₁, e₂]


/-! ## The boundary circle of the model disc -/

/-- The boundary point `exp (i θ)`, as an element of the model disc. -/
abbrev cpt (θ : ℝ) : Disc := Work.CoreTopology.circlePoint θ

theorem norm_cpt (θ : ℝ) : ‖((cpt θ : Disc) : ℂ)‖ = 1 := by
  rw [show ((cpt θ : Disc) : ℂ) = Complex.exp (↑θ * Complex.I) from
    Work.CoreTopology.circlePoint_coe θ, Complex.norm_exp_ofReal_mul_I]

theorem cpt_add_two_pi (θ : ℝ) : cpt (θ + 2 * Real.pi) = cpt θ :=
  Work.CoreTopology.circlePoint_add_two_pi θ

theorem continuous_cpt : Continuous cpt := Work.CoreTopology.continuous_circlePoint

/-- The antipode `z ↦ -z` of the model disc. -/
def discAntipode (z : Disc) : Disc :=
  ⟨-(z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h⟩

@[simp] theorem discAntipode_coe (z : Disc) : ((discAntipode z : Disc) : ℂ) = -(z : ℂ) := rfl

theorem continuous_discAntipode : Continuous discAntipode := by
  refine Continuous.subtype_mk ?_ ?_
  show Continuous fun z : Disc => -((z : ℂ))
  exact continuous_neg.comp continuous_subtype_val

theorem discAntipode_involutive (z : Disc) : discAntipode (discAntipode z) = z := by
  apply Subtype.mk_eq_mk.mpr
  simp [discAntipode]

theorem discAntipode_cpt (θ : ℝ) : discAntipode (cpt θ) = cpt (θ + Real.pi) := by
  apply Subtype.mk_eq_mk.mpr
  show -((cpt θ : Disc) : ℂ) = ((cpt (θ + Real.pi) : Disc) : ℂ)
  rw [Work.CoreTopology.circlePoint_coe, Work.CoreTopology.circlePoint_coe]
  have h1 : ((θ + Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- The uniform normalisation in the circle: equal values give equal points. -/
theorem normCircle_congr {w : ℂ} (h₁ h₂ : w ≠ 0) :
    Work.CoreTopology.normCircle w h₁ = Work.CoreTopology.normCircle w h₂ :=
  Subtype.mk_eq_mk.mpr rfl

/-! ## Invariance of domain for the embedded disc -/

/-- **The image of the open model disc under an injective continuous map is a neighbourhood of the
image of the centre.** -/
theorem center_mem_interior_image (g : C(Disc, ℂ)) (hg : Function.Injective g) :
    g 0 ∈ interior (g '' {s : Disc | ‖(s : ℂ)‖ < 1}) := by
  classical
  set S : Set Disc := {s : Disc | ‖(s : ℂ)‖ = 1} with hSdef
  have hcpS : ∀ t : ℝ, cpt t ∈ S := fun t => by
    rw [hSdef]; exact norm_cpt t
  have hSne : S.Nonempty := ⟨cpt 0, hcpS 0⟩
  have hScomp : IsCompact S := by
    rw [hSdef]
    exact (isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const).isCompact
  have hcontmin : ContinuousOn (fun s : Disc => ‖g s - g 0‖) S :=
    (continuous_norm.comp (g.continuous.sub
      (continuous_const : Continuous fun _ : Disc => g 0))).continuousOn
  obtain ⟨s₀, hs₀S, hs₀min⟩ := hScomp.exists_isMinOn hSne hcontmin
  set m : ℝ := ‖g s₀ - g 0‖ with hmdef
  have hmin : ∀ s ∈ S, m ≤ ‖g s - g 0‖ := fun s hs => hs₀min hs
  have hmpos : 0 < m := by
    have hne : g s₀ ≠ g 0 := by
      intro hcon
      have hz : s₀ = 0 := hg hcon
      rw [hz] at hs₀S
      exact absurd hs₀S (by rw [hSdef]; simp)
    simpa [hmdef] using norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have key : ∀ c : ℂ, ‖c - g 0‖ < m → c ∈ g '' {s : Disc | ‖(s : ℂ)‖ < 1} := by
    intro c hc
    by_contra hnc
    have hcS : ∀ s ∈ S, g s ≠ c := by
      intro s hs hgs
      have h1 : m ≤ ‖g s - g 0‖ := hmin s hs
      have h2 : ‖g s - g 0‖ = ‖c - g 0‖ := by rw [hgs]
      linarith
    have hcmem : ∀ x : Disc, g x ≠ c := by
      intro x hx
      rcases lt_or_eq_of_le (by
        have h := x.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h) with h | h
      · exact hnc ⟨x, h, hx⟩
      · exact hcS x (by rw [hSdef]; exact h) hx
    have hpne : ∀ x : Disc, g x - c ≠ 0 := fun x => sub_ne_zero.mpr (hcmem x)
    -- `β` and its extension `Φ` over the disc
    let Φ : C(Disc, Circle) := ⟨fun x => Work.CoreTopology.normCircle (g x - c) (hpne x),
      Work.CoreTopology.continuous_normCircle (fun x : Disc => g x - c)
        (g.continuous.sub continuous_const) hpne⟩
    have hΦapply : ∀ x : Disc, Φ x = Work.CoreTopology.normCircle (g x - c) (hpne x) :=
      fun x => rfl
    have hβne : ∀ t : ℝ, g (cpt t) - c ≠ 0 := fun t => hpne _
    let β : C(ℝ, Circle) :=
      ⟨fun t => Work.CoreTopology.normCircle (g (cpt t) - c) (hβne t),
        Work.CoreTopology.continuous_normCircle (fun t : ℝ => g (cpt t) - c)
          ((g.continuous.comp continuous_cpt).sub continuous_const) hβne⟩
    have hβapply : ∀ t : ℝ, β t = Work.CoreTopology.normCircle (g (cpt t) - c) (hβne t) :=
      fun t => rfl
    have hΦβ : ∀ θ : ℝ, Φ (cpt θ) = β θ := by
      intro θ
      rw [hΦapply, hβapply]
    have hβper : ∀ t : ℝ, β (t + 2 * Real.pi) = β t := by
      intro t
      apply Circle.coe_inj.mp
      rw [hβapply (t + 2 * Real.pi), hβapply t, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe, cpt_add_two_pi]
    -- the loop `γ`
    have hγne : ∀ t : ℝ, g (cpt t) - g 0 ≠ 0 := by
      intro t
      rw [sub_ne_zero]
      intro hcon
      have hz : cpt t = 0 := hg hcon
      have h1 : ‖((cpt t : Disc) : ℂ)‖ = 1 := norm_cpt t
      rw [hz] at h1
      norm_num at h1
    let γ : C(ℝ, Circle) :=
      ⟨fun t => Work.CoreTopology.normCircle (g (cpt t) - g 0) (hγne t),
        Work.CoreTopology.continuous_normCircle (fun t : ℝ => g (cpt t) - g 0)
          ((g.continuous.comp continuous_cpt).sub continuous_const) hγne⟩
    have hγapply : ∀ t : ℝ, γ t = Work.CoreTopology.normCircle (g (cpt t) - g 0) (hγne t) :=
      fun t => rfl
    -- the odd loop `δ`
    have hδne : ∀ t : ℝ, g (cpt t) - g (discAntipode (cpt t)) ≠ 0 := by
      intro t
      rw [sub_ne_zero]
      intro hcon
      have hz : ((cpt t : Disc) : ℂ) = -((cpt t : Disc) : ℂ) := by
        have h := congrArg (fun z : Disc => (z : ℂ)) (hg hcon)
        simpa [discAntipode_coe] using h
      have h2 : (2 : ℂ) * ((cpt t : Disc) : ℂ) = 0 := by
        rw [eq_neg_iff_add_eq_zero] at hz
        linear_combination hz
      have h3 : ((cpt t : Disc) : ℂ) = 0 :=
        (mul_eq_zero.mp h2).resolve_left two_ne_zero
      have h4 : ‖((cpt t : Disc) : ℂ)‖ = 1 := norm_cpt t
      rw [h3] at h4
      norm_num at h4
    let δ : C(ℝ, Circle) :=
      ⟨fun t => Work.CoreTopology.normCircle
          (g (cpt t) - g (discAntipode (cpt t))) (hδne t),
        Work.CoreTopology.continuous_normCircle
          (fun t : ℝ => g (cpt t) - g (discAntipode (cpt t)))
          ((g.continuous.comp continuous_cpt).sub
            (g.continuous.comp (continuous_discAntipode.comp continuous_cpt))) hδne⟩
    have hδapply : ∀ t : ℝ, δ t =
        Work.CoreTopology.normCircle (g (cpt t) - g (discAntipode (cpt t))) (hδne t) :=
      fun t => rfl
    have hδodd : ∀ t : ℝ, δ (t + Real.pi) = - (δ t) := by
      intro t
      apply Circle.coe_inj.mp
      rw [hδapply (t + Real.pi), hδapply t, Circle.coe_neg, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe, ← discAntipode_cpt t, discAntipode_involutive]
      have hsub : g (discAntipode (cpt t)) - g (cpt t)
          = -(g (cpt t) - g (discAntipode (cpt t))) := by abel
      rw [hsub, norm_neg, neg_div]
    -- the homotopy from `β` to `γ`
    have hμcont : Continuous fun p : ℝ × ℝ => min (max p.2 0) 1 :=
      (continuous_snd.max continuous_const).min continuous_const
    have hK₁fun : Continuous fun p : ℝ × ℝ =>
        g (cpt p.1) - (c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c)) :=
      (g.continuous.comp (continuous_cpt.comp continuous_fst)).sub
        (continuous_const.add ((Complex.continuous_ofReal.comp hμcont).mul continuous_const))
    have hK₁ne : ∀ p : ℝ × ℝ,
        g (cpt p.1) - (c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c)) ≠ 0 := by
      intro p
      rw [sub_ne_zero]
      intro hcon
      have ht0 : 0 ≤ min (max p.2 0) 1 := le_min (le_max_right _ _) zero_le_one
      have ht1 : min (max p.2 0) 1 ≤ 1 := min_le_right _ _
      have hnorm : ‖c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c) - g 0‖
          = (1 - min (max p.2 0) 1) * ‖c - g 0‖ := by
        have hsplit : c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c) - g 0
            = ((1 - min (max p.2 0) 1 : ℝ) : ℂ) * (c - g 0) := by push_cast; ring
        rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      have h1 : m ≤ ‖g (cpt p.1) - g 0‖ := hmin _ (hcpS p.1)
      have h2 : ‖g (cpt p.1) - g 0‖ = (1 - min (max p.2 0) 1) * ‖c - g 0‖ := by
        rw [hcon, hnorm]
      have h3 : (1 - min (max p.2 0) 1) * ‖c - g 0‖ ≤ ‖c - g 0‖ := by
        nlinarith [norm_nonneg (c - g 0), ht0, ht1]
      linarith
    let K₁ : C(ℝ × ℝ, Circle) :=
      ⟨fun p => Work.CoreTopology.normCircle
          (g (cpt p.1) - (c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c))) (hK₁ne p),
        Work.CoreTopology.continuous_normCircle _ hK₁fun hK₁ne⟩
    have hK₁apply : ∀ p : ℝ × ℝ, K₁ p = Work.CoreTopology.normCircle
        (g (cpt p.1) - (c + ((min (max p.2 0) 1 : ℝ) : ℂ) * (g 0 - c))) (hK₁ne p) :=
      fun p => rfl
    have hμzero : min (max ((0 : ℝ)) 0) 1 = 0 := by norm_num
    have hμone : min (max ((1 : ℝ)) 0) 1 = 1 := by norm_num
    have hK₁per : ∀ t s : ℝ, K₁ (t + 2 * Real.pi, s) = K₁ (t, s) := by
      intro t s
      apply Circle.coe_inj.mp
      rw [hK₁apply (t + 2 * Real.pi, s), hK₁apply (t, s),
        Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, cpt_add_two_pi]
    have hK₁zero : ∀ t : ℝ, K₁ (t, 0) = β t := by
      intro t
      apply Circle.coe_inj.mp
      rw [hK₁apply (t, 0), hβapply t, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe, hμzero, Complex.ofReal_zero, zero_mul, add_zero]
    have hK₁one : ∀ t : ℝ, K₁ (t, 1) = γ t := by
      intro t
      apply Circle.coe_inj.mp
      rw [hK₁apply (t, 1), hγapply t, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe, hμone, Complex.ofReal_one, one_mul,
        show c + (g 0 - c) = g 0 by ring]
    -- the homotopy from `γ` to `δ`
    have hreflmem : ∀ p : ℝ × ℝ,
        (((min (max p.2 0) 1 - 1 : ℝ) : ℂ) * ((cpt p.1 : Disc) : ℂ))
          ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro p
      have hμ0 : 0 ≤ min (max p.2 0) 1 := le_min (le_max_right _ _) zero_le_one
      have hμ1 : min (max p.2 0) 1 ≤ 1 := min_le_right _ _
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith), norm_cpt, mul_one]
      linarith
    let refl : ℝ × ℝ → Disc := fun p =>
      ⟨((min (max p.2 0) 1 - 1 : ℝ) : ℂ) * ((cpt p.1 : Disc) : ℂ), hreflmem p⟩
    have hreflapply : ∀ p : ℝ × ℝ, refl p =
        (⟨((min (max p.2 0) 1 - 1 : ℝ) : ℂ) * ((cpt p.1 : Disc) : ℂ), hreflmem p⟩ : Disc) :=
      fun p => rfl
    have hreflcont : Continuous refl :=
      Continuous.subtype_mk
        ((Complex.continuous_ofReal.comp (hμcont.sub continuous_const)).mul
          (continuous_subtype_val.comp (continuous_cpt.comp continuous_fst))) hreflmem
    have hK₂fun : Continuous fun p : ℝ × ℝ => g (cpt p.1) - g (refl p) :=
      (g.continuous.comp (continuous_cpt.comp continuous_fst)).sub
        (g.continuous.comp hreflcont)
    have hK₂ne : ∀ p : ℝ × ℝ, g (cpt p.1) - g (refl p) ≠ 0 := by
      intro p
      rw [sub_ne_zero]
      intro hcon
      have hz : ((cpt p.1 : Disc) : ℂ)
          = ((min (max p.2 0) 1 - 1 : ℝ) : ℂ) * ((cpt p.1 : Disc) : ℂ) := by
        have h := congrArg (fun z : Disc => (z : ℂ)) (hg hcon)
        rw [hreflapply p] at h
        simpa using h
      have hμne : ((min (max p.2 0) 1 - 1 : ℝ) : ℂ) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have h' : (min (max p.2 0) 1 - 1 : ℝ) = 1 := by exact_mod_cast h
        linarith [min_le_right (max p.2 0) 1]
      have he : ((cpt p.1 : Disc) : ℂ) ≠ 0 := by
        intro h0
        have h4 : ‖((cpt p.1 : Disc) : ℂ)‖ = 1 := norm_cpt p.1
        rw [h0] at h4
        norm_num at h4
      refine absurd ?_ (mul_ne_zero hμne he)
      rw [sub_mul, one_mul, ← hz, sub_self]
    let K₂ : C(ℝ × ℝ, Circle) :=
      ⟨fun p => Work.CoreTopology.normCircle (g (cpt p.1) - g (refl p)) (hK₂ne p),
        Work.CoreTopology.continuous_normCircle _ hK₂fun hK₂ne⟩
    have hK₂apply : ∀ p : ℝ × ℝ, K₂ p =
        Work.CoreTopology.normCircle (g (cpt p.1) - g (refl p)) (hK₂ne p) := fun p => rfl
    have hK₂per : ∀ t s : ℝ, K₂ (t + 2 * Real.pi, s) = K₂ (t, s) := by
      intro t s
      apply Circle.coe_inj.mp
      have hreflper : refl (t + 2 * Real.pi, s) = refl (t, s) := by
        apply Subtype.mk_eq_mk.mpr
        show ((min (max s 0) 1 - 1 : ℝ) : ℂ) * ((cpt (t + 2 * Real.pi) : Disc) : ℂ)
            = ((min (max s 0) 1 - 1 : ℝ) : ℂ) * ((cpt t : Disc) : ℂ)
        rw [cpt_add_two_pi]
      rw [hK₂apply (t + 2 * Real.pi, s), hK₂apply (t, s),
        Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, hreflper,
        show ((t + 2 * Real.pi, s).1 : ℝ) = t + 2 * Real.pi from rfl,
        show ((t, s).1 : ℝ) = t from rfl, cpt_add_two_pi]
    have hK₂zero : ∀ t : ℝ, K₂ (t, 0) = δ t := by
      intro t
      apply Circle.coe_inj.mp
      rw [hK₂apply (t, 0), hδapply t, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe]
      have hpt : refl (t, 0) = discAntipode (cpt t) := by
        rw [hreflapply (t, 0)]
        apply Subtype.mk_eq_mk.mpr
        show ((min (max (0 : ℝ) 0) 1 - 1 : ℝ) : ℂ) * ((cpt t : Disc) : ℂ)
            = -((cpt t : Disc) : ℂ)
        rw [hμzero]
        norm_num
      rw [hpt]
    have hK₂one : ∀ t : ℝ, K₂ (t, 1) = γ t := by
      intro t
      apply Circle.coe_inj.mp
      rw [hK₂apply (t, 1), hγapply t, Work.CoreTopology.normCircle_coe,
        Work.CoreTopology.normCircle_coe]
      have hpt : refl (t, 1) = (0 : Disc) := by
        rw [hreflapply (t, 1)]
        apply Subtype.mk_eq_mk.mpr
        show ((min (max (1 : ℝ) 0) 1 - 1 : ℝ) : ℂ) * ((cpt t : Disc) : ℂ) = 0
        rw [hμone]
        norm_num
      rw [hpt]
    -- the degree argument
    obtain ⟨Λβ, hΛβ⟩ := exists_continuous_lift β
    obtain ⟨Λγ, hΛγ⟩ := exists_continuous_lift γ
    obtain ⟨Λδ, hΛδ⟩ := exists_continuous_lift δ
    have hβext : Λβ (2 * Real.pi) - Λβ 0 = 0 :=
      lift_diff_eq_zero_of_extends ⇑β β.continuous hβper Φ hΦβ Λβ Λβ.continuous hΛβ
    have hβγ : Λβ (2 * Real.pi) - Λβ 0 = Λγ (2 * Real.pi) - Λγ 0 :=
      lift_diff_eq_of_homotopy K₁ Λβ Λγ hK₁per Λβ.continuous
        (fun t => by rw [hΛβ t, hK₁zero t]) Λγ.continuous
        (fun t => by rw [hΛγ t, hK₁one t])
    have hγδ : Λδ (2 * Real.pi) - Λδ 0 = Λγ (2 * Real.pi) - Λγ 0 :=
      lift_diff_eq_of_homotopy K₂ Λδ Λγ hK₂per Λδ.continuous
        (fun t => by rw [hΛδ t, hK₂zero t]) Λγ.continuous
        (fun t => by rw [hΛγ t, hK₂one t])
    exact lift_diff_ne_zero_of_odd ⇑δ Λδ Λδ.continuous hΛδ hδodd (by linarith)
  refine interior_maximal ?_ Metric.isOpen_ball (Metric.mem_ball_self hmpos)
  intro c hc
  exact key c (by simpa [Metric.mem_ball, dist_eq_norm] using hc)

/-- **Invariance of domain, at an arbitrary interior point.** -/
theorem mem_interior_image_of_norm_lt_one (g : C(Disc, ℂ)) (hg : Function.Injective g)
    (x₀ : Disc) (hx₀ : ‖(x₀ : ℂ)‖ < 1) :
    g x₀ ∈ interior (g '' {s : Disc | ‖(s : ℂ)‖ < 1}) := by
  set ρ : ℝ := (1 - ‖(x₀ : ℂ)‖) / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρne : (ρ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hρpos
  have hTmem : ∀ u : Disc, ((x₀ : ℂ) + (ρ : ℂ) * (u : ℂ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro u
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu := u.2
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    calc ‖(x₀ : ℂ) + (ρ : ℂ) * (u : ℂ)‖
        ≤ ‖(x₀ : ℂ)‖ + ‖(ρ : ℂ) * (u : ℂ)‖ := norm_add_le _ _
      _ = ‖(x₀ : ℂ)‖ + ρ * ‖(u : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρpos.le]
      _ ≤ ‖(x₀ : ℂ)‖ + ρ * 1 := by
          have h := mul_le_mul_of_nonneg_left hu hρpos.le
          linarith
      _ = ‖(x₀ : ℂ)‖ + ρ := by ring
      _ ≤ 1 := by rw [hρdef]; linarith
  have hTcont : Continuous fun u : Disc => (x₀ : ℂ) + (ρ : ℂ) * (u : ℂ) :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  let T : C(Disc, Disc) := ⟨fun u => ⟨(x₀ : ℂ) + (ρ : ℂ) * (u : ℂ), hTmem u⟩,
    Continuous.subtype_mk hTcont hTmem⟩
  have hTapply : ∀ u : Disc, T u = (⟨(x₀ : ℂ) + (ρ : ℂ) * (u : ℂ), hTmem u⟩ : Disc) :=
    fun u => rfl
  have hTinj : Function.Injective T := by
    intro u v huv
    have h : (x₀ : ℂ) + (ρ : ℂ) * (u : ℂ) = (x₀ : ℂ) + (ρ : ℂ) * (v : ℂ) := by
      rw [hTapply u, hTapply v] at huv
      exact congrArg Subtype.val huv
    have h2 : (ρ : ℂ) * (u : ℂ) = (ρ : ℂ) * (v : ℂ) := add_left_cancel h
    exact Subtype.ext (mul_left_cancel₀ hρne h2)
  have hkey := center_mem_interior_image (g.comp T) (hg.comp hTinj)
  have hT0 : T 0 = x₀ := by
    rw [hTapply]
    apply Subtype.mk_eq_mk.mpr
    simp
  have hisub : (⇑(g.comp T)) '' {s : Disc | ‖(s : ℂ)‖ < 1}
      ⊆ g '' {s : Disc | ‖(s : ℂ)‖ < 1} := by
    rintro y ⟨u, hu, rfl⟩
    refine ⟨T u, ?_, rfl⟩
    rw [Set.mem_ofPred_eq] at hu ⊢
    calc ‖((T u : Disc) : ℂ)‖ = ‖(x₀ : ℂ) + (ρ : ℂ) * (u : ℂ)‖ := by
          rw [hTapply]
      _ ≤ ‖(x₀ : ℂ)‖ + ‖(ρ : ℂ) * (u : ℂ)‖ := norm_add_le _ _
      _ = ‖(x₀ : ℂ)‖ + ρ * ‖(u : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρpos.le]
      _ < ‖(x₀ : ℂ)‖ + ρ * 1 := by
          have h := mul_lt_mul_of_pos_left hu hρpos
          linarith
      _ = ‖(x₀ : ℂ)‖ + ρ := by ring
      _ < 1 := by rw [hρdef]; linarith
  rw [show (g.comp T) 0 = g x₀ by rw [ContinuousMap.comp_apply, hT0]] at hkey
  exact interior_mono hisub hkey

end

end Work.Smooth.SphereJordan
