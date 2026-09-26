import Mathlib
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.BoundedSide

/-!
# The open image of an embedded disc in the unit disc lies on the bounded side

Let `γ` be a simple closed plane curve whose trace lies in the open unit disc, `S` a planar
Jordan–Schoenflies datum for it (so `S.V` is the bounded side and `S.e : 𝔻 → ℂ` an embedded
spanning disc with image `closure S.V`), and `F : 𝔻 → 𝔻` a continuous injection whose boundary
circle is mapped to `γ` in the given parametrisation.  Then the image of the open disc lies on the
bounded side of `γ`.

## The proof

Write `f` for the `ℂ`-valued map underlying `F`.  Suppose `f z` were *not* in `S.V` for some
`z` of norm `< 1`.  Then `f z ∈ S.U`, the unbounded side; in particular `f z` is outside
`closure S.V = range S.e`, so the loop

  `θ ↦ (S.e (e^{iθ}) - f z) / ‖S.e (e^{iθ}) - f z‖`

of the unit circle extends over the disc `𝔻` by normalising `S.e · - f z`.  By the monodromy of
the universal cover `Circle.exp : ℝ → S¹` such a loop has **zero** winding (`hlp_lift_diff_eq_zero_of_extends`,
a form of `Work.CoreTopology.circle_lift_eq_of_extends_disk`).

On the other hand that loop *is* the loop `θ ↦ (f (e^{iθ}) - f z)/‖·‖` (because `S.e` and `f`
agree on the boundary circle), and for an injective `f` this loop has **nonzero** winding: it is
homotopic, through the straight segments `s ↦ z + s(e^{i(θ+π)} - z)` inside `𝔻`, to the *odd* loop
`θ ↦ (f (e^{iθ}) - f (e^{i(θ+π)}))/‖·‖`, whose winding is nonzero because its lift satisfies
`Λ (θ + π) = Λ θ + (2k+1) π` (`hlp_lift_diff_ne_zero_of_odd`).  The two computations contradict
each other.

This is the "outside case" excluded in `Work.Smooth.SphereJordan.disc_spans_schoenflies`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The monodromy of the universal cover of the circle -/

/-- The standard parametrisation of the boundary circle is `2π`-periodic. -/
theorem hlp_circlePoint_add_two_pi (θ : ℝ) :
    circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + 2 * ((Real.pi : ℂ)) * Complex.I from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The antipode of a boundary point, at the level of `ℂ`. -/
theorem hlp_circlePoint_neg_coe (t : ℝ) :
    (((circlePoint (t + Real.pi) : Disc)) : ℂ) = - (((circlePoint t : Disc)) : ℂ) := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show ((t + Real.pi : ℝ) : ℂ) * Complex.I
      = (t : ℂ) * Complex.I + ((Real.pi : ℂ)) * Complex.I from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The boundary parametrisation is continuous. -/
theorem hlp_continuous_circlePoint : Continuous (circlePoint : ℝ → Disc) :=
  Continuous.subtype_mk (by
    show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
    fun_prop) _

/-- Every continuous loop of the circle has a continuous lift to the line. -/
theorem hlp_exists_continuous_lift (φ : C(ℝ, Circle)) :
    ∃ Λ : C(ℝ, ℝ), ∀ t : ℝ, Circle.exp (Λ t) = φ t := by
  obtain ⟨Λ, hspec, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts φ 0
    (Complex.arg (φ 0)) (Circle.exp_arg (φ 0))
  exact ⟨Λ, fun t => congr_fun hspec.2 t⟩

/-- Two continuous lifts of the same loop differ by a constant. -/
theorem hlp_lift_sub_eq_const {Λ₁ Λ₂ : ℝ → ℝ} (h₁ : Continuous Λ₁) (h₂ : Continuous Λ₂)
    (h : ∀ t : ℝ, Circle.exp (Λ₁ t) = Circle.exp (Λ₂ t)) (t : ℝ) :
    Λ₁ t - Λ₂ t = Λ₁ 0 - Λ₂ 0 := by
  have hc : Continuous fun t : ℝ => Λ₁ t - Λ₂ t := h₁.sub h₂
  refine Circle.isCoveringMap_exp.const_of_comp hc (fun a a' => ?_) t 0
  simp only [Circle.exp_sub, h a, h a', div_self']

/-- **A loop of the circle extending over the disc has zero lift-difference.** -/
theorem hlp_lift_diff_eq_zero_of_extends (φ : ℝ → Circle) (hφ : Continuous φ)
    (hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t) (Φ : C(Disc, Circle))
    (hΦ : ∀ θ : ℝ, Φ (circlePoint θ) = φ θ) (Λ : ℝ → ℝ) (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = φ t) : Λ (2 * Real.pi) - Λ 0 = 0 := by
  rw [Work.CoreTopology.circle_lift_eq_of_extends_disk φ hφ hper Φ hΦ Λ hΛ hlift, sub_self]

/-- The lift of the antipode: `Circle.exp π = -1`. -/
theorem hlp_circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.coe_inj.mp
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
  exact Complex.exp_pi_mul_I

/-- **An odd loop of the circle has nonzero lift-difference.** -/
theorem hlp_lift_diff_ne_zero_of_odd (φ : ℝ → Circle) (Λ : ℝ → ℝ) (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = φ t)
    (hodd : ∀ t : ℝ, ((φ (t + Real.pi) : Circle) : ℂ) = - ((φ t : Circle) : ℂ)) :
    Λ (2 * Real.pi) - Λ 0 ≠ 0 := by
  intro hzero
  have hc : Continuous fun t : ℝ => Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ) := by fun_prop
  have hval : ∀ t : ℝ, Complex.exp (Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ)) = -1 := by
    intro t
    have e₁ : ((φ (t + Real.pi) : Circle) : ℂ)
        = Complex.exp (((Λ (t + Real.pi) : ℝ) : ℂ) * Complex.I) := by
      have h := congrArg (fun z : Circle => (z : ℂ)) (hlift (t + Real.pi))
      simpa [Circle.coe_exp] using h.symm
    have e₂ : ((φ t : Circle) : ℂ) = Complex.exp (((Λ t : ℝ) : ℂ) * Complex.I) := by
      have h := congrArg (fun z : Circle => (z : ℂ)) (hlift t)
      simpa [Circle.coe_exp] using h.symm
    have hsplit : Complex.I * ((Λ (t + Real.pi) - Λ t : ℝ) : ℂ)
        = ((Λ (t + Real.pi) : ℝ) : ℂ) * Complex.I - ((Λ t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hsplit, Complex.exp_sub, ← e₁, ← e₂, hodd t, neg_div,
      div_self (Circle.coe_ne_zero (φ t))]
  have hconst := Complex.isCoveringMap_exp.const_of_comp hc
    (fun a a' => by simpa using (hval a).trans (hval a').symm) (0 : ℝ) Real.pi
  have hc0 : Λ Real.pi - Λ 0 = Λ (2 * Real.pi) - Λ Real.pi := by
    have h := mul_left_cancel₀ Complex.I_ne_zero hconst
    have h' : ((Λ (Real.pi) - Λ 0 : ℝ) : ℂ) = ((Λ (2 * Real.pi) - Λ Real.pi : ℝ) : ℂ) := by
      simpa [two_mul] using h
    exact_mod_cast h'
  have hpeak : Circle.exp (Λ Real.pi - Λ 0) = -1 := by
    apply Circle.coe_inj.mp
    rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
    have h := hval 0
    simpa [mul_comm] using h
  have hexp : Circle.exp (Λ Real.pi - Λ 0) = Circle.exp Real.pi := by
    rw [hpeak, hlp_circle_exp_pi]
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
  have hdiff : Λ (2 * Real.pi) - Λ 0 = 2 * (Λ Real.pi - Λ 0) := by linarith
  have hzero' : Λ Real.pi - Λ 0 = 0 := by linarith [hdiff ▸ hzero]
  have h2 : (1 + 2 * (k : ℝ)) * Real.pi = 0 := by linarith
  have h3 : (1 + 2 * (k : ℝ)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h Real.pi_ne_zero
  have h4 : (2 * k + 1 : ℤ) = 0 := by
    have : ((2 * k + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  omega

/-- **The lift-difference is a homotopy invariant of loops.** -/
theorem hlp_lift_diff_eq_of_homotopy (K : C(ℝ × ℝ, Circle)) (Λ₀ Λ₁ : ℝ → ℝ)
    (hKper : ∀ t s : ℝ, K (t + 2 * Real.pi, s) = K (t, s))
    (h₀c : Continuous Λ₀) (h₀ : ∀ t : ℝ, Circle.exp (Λ₀ t) = K (t, 0))
    (h₁c : Continuous Λ₁) (h₁ : ∀ t : ℝ, Circle.exp (Λ₁ t) = K (t, 1)) :
    Λ₀ (2 * Real.pi) - Λ₀ 0 = Λ₁ (2 * Real.pi) - Λ₁ 0 := by
  obtain ⟨KL, hKLspec, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts K (0, 0)
    (Complex.arg (K (0, 0))) (Circle.exp_arg (K (0, 0)))
  have hKL : ∀ p : ℝ × ℝ, Circle.exp (KL p) = K p := fun p => congr_fun hKLspec.2 p
  have hrow0 : ∀ t : ℝ, Circle.exp (KL (t, 0)) = K (t, 0) := fun t => hKL (t, 0)
  have hrow1 : ∀ t : ℝ, Circle.exp (KL (t, 1)) = K (t, 1) := fun t => hKL (t, 1)
  have hcont0 : Continuous fun t : ℝ => KL (t, 0) :=
    KL.continuous.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)))
  have hcont1 : Continuous fun t : ℝ => KL (t, 1) :=
    KL.continuous.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)))
  have e0 : Λ₀ (2 * Real.pi) - Λ₀ 0 = KL (2 * Real.pi, 0) - KL (0, 0) := by
    have k2 := hlp_lift_sub_eq_const h₀c hcont0 (fun t => by rw [h₀ t, hrow0 t]) (2 * Real.pi)
    have k0 := hlp_lift_sub_eq_const h₀c hcont0 (fun t => by rw [h₀ t, hrow0 t]) 0
    linarith
  have e1 : Λ₁ (2 * Real.pi) - Λ₁ 0 = KL (2 * Real.pi, 1) - KL (0, 1) := by
    have k2 := hlp_lift_sub_eq_const h₁c hcont1 (fun t => by rw [h₁ t, hrow1 t]) (2 * Real.pi)
    have k0 := hlp_lift_sub_eq_const h₁c hcont1 (fun t => by rw [h₁ t, hrow1 t]) 0
    linarith
  have hWc : Continuous fun p : ℝ × ℝ => KL (p.1 + 2 * Real.pi, p.2) - KL (p.1, p.2) :=
    (KL.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub
      (KL.continuous.comp (continuous_fst.prodMk continuous_snd))
  have hWval : ∀ p : ℝ × ℝ,
      Circle.exp (KL (p.1 + 2 * Real.pi, p.2) - KL (p.1, p.2)) = 1 := by
    intro p
    rw [Circle.exp_sub, hKL (p.1 + 2 * Real.pi, p.2), hKL (p.1, p.2), hKper, div_self']
  have hWcst : KL (2 * Real.pi, 0) - KL (0, 0) = KL (2 * Real.pi, 1) - KL (0, 1) := by
    have h := Circle.isCoveringMap_exp.const_of_comp hWc
      (fun a a' => by simp only [hWval a, hWval a']) (0, 0) (0, 1)
    simpa using h
  linarith

/-! ## Elementary facts about `normCircle` -/

theorem hlp_normCircle_congr {w w' : ℂ} (h : w = w') (h1 : w ≠ 0) (h2 : w' ≠ 0) :
    Work.CoreTopology.normCircle w h1 = Work.CoreTopology.normCircle w' h2 := by
  subst h
  exact Subtype.ext rfl

theorem hlp_normCircle_irrel (w : ℂ) (h1 h2 : w ≠ 0) :
    Work.CoreTopology.normCircle w h1 = Work.CoreTopology.normCircle w h2 :=
  Subtype.ext rfl

/-! ## Nonvanishing of the loops of an injective disc map -/

theorem hlp_loop_ne_zero (g : C(Disc, ℂ)) (hg : Function.Injective g) {z₀ : Disc}
    (hz₀ : ‖(z₀ : ℂ)‖ < 1) : ∀ t : ℝ, g (circlePoint t) - g z₀ ≠ 0 := by
  intro t h
  have h1 : circlePoint t = z₀ := hg (sub_eq_zero.mp h)
  have h2 : ‖((circlePoint t : Disc) : ℂ)‖ = 1 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  rw [← congrArg (fun z : Disc => ‖(z : ℂ)‖) h1, h2] at hz₀
  exact lt_irrefl 1 hz₀

theorem hlp_odd_ne (g : C(Disc, ℂ)) (hg : Function.Injective g) :
    ∀ t : ℝ, g (circlePoint t) - g (circlePoint (t + Real.pi)) ≠ 0 := by
  intro t h
  have h1 : circlePoint t = circlePoint (t + Real.pi) := hg (sub_eq_zero.mp h)
  have h2 : (((circlePoint t : Disc)) : ℂ) = - (((circlePoint t : Disc)) : ℂ) :=
    (congrArg (fun z : Disc => (z : ℂ)) h1).trans (hlp_circlePoint_neg_coe t)
  have h3 : (2 : ℂ) * (((circlePoint t : Disc)) : ℂ) = 0 := by
    have h3a : (((circlePoint t : Disc)) : ℂ) + (((circlePoint t : Disc)) : ℂ) = 0 :=
      eq_neg_iff_add_eq_zero.mp h2
    simpa [two_mul] using h3a
  have h4 : (((circlePoint t : Disc)) : ℂ) = 0 := by
    rcases mul_eq_zero.mp h3 with hh | hh
    · norm_num at hh
    · exact hh
  have h5 : ‖((circlePoint t : Disc) : ℂ)‖ = 1 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  rw [h4] at h5; norm_num at h5

/-- **The boundary loop of an injective disc map winds nontrivially around an interior value.**

For an injective continuous `g : 𝔻 → ℂ` and `z₀` in the open disc, every lift `Λ` of the loop
`θ ↦ (g (e^{iθ}) - g z₀)/‖g (e^{iθ}) - g z₀‖` to the universal cover of the circle satisfies
`Λ (2π) ≠ Λ 0`. -/
theorem hlp_winding_ne_zero (g : C(Disc, ℂ)) (hg : Function.Injective g) {z₀ : Disc}
    (hz₀ : ‖(z₀ : ℂ)‖ < 1) (Λ : ℝ → ℝ) (hΛc : Continuous Λ)
    (hΛ : ∀ t : ℝ, Circle.exp (Λ t)
      = Work.CoreTopology.normCircle (g (circlePoint t) - g z₀)
          (hlp_loop_ne_zero g hg hz₀ t)) :
    Λ (2 * Real.pi) - Λ 0 ≠ 0 := by
  have hγne := hlp_loop_ne_zero g hg hz₀
  have hδne := hlp_odd_ne g hg
  let γ : ℝ → Circle := fun t =>
    Work.CoreTopology.normCircle (g (circlePoint t) - g z₀) (hγne t)
  let δ : ℝ → Circle := fun t =>
    Work.CoreTopology.normCircle (g (circlePoint t) - g (circlePoint (t + Real.pi))) (hδne t)
  have hδc : Continuous δ := by
    refine Work.CoreTopology.continuous_normCircle _ ?_ hδne
    exact (g.continuous.comp hlp_continuous_circlePoint).sub
      (g.continuous.comp (hlp_continuous_circlePoint.comp
        (continuous_id.add (continuous_const : Continuous fun _ : ℝ => Real.pi))))
  have hδodd : ∀ t : ℝ, ((δ (t + Real.pi) : Circle) : ℂ) = - ((δ t : Circle) : ℂ) := by
    intro t
    have hnum : g (circlePoint (t + Real.pi)) - g (circlePoint (t + Real.pi + Real.pi))
        = - (g (circlePoint t) - g (circlePoint (t + Real.pi))) := by
      rw [show t + Real.pi + Real.pi = t + 2 * Real.pi from by ring, hlp_circlePoint_add_two_pi t]
      ring
    have h1 : ((δ (t + Real.pi) : Circle) : ℂ)
        = (g (circlePoint (t + Real.pi)) - g (circlePoint (t + Real.pi + Real.pi)))
            / ((‖g (circlePoint (t + Real.pi)) - g (circlePoint (t + Real.pi + Real.pi))‖ : ℝ) : ℂ) := by
      simp only [δ, Work.CoreTopology.normCircle_coe]
    have h2 : ((δ t : Circle) : ℂ)
        = (g (circlePoint t) - g (circlePoint (t + Real.pi)))
            / ((‖g (circlePoint t) - g (circlePoint (t + Real.pi))‖ : ℝ) : ℂ) := by
      simp only [δ, Work.CoreTopology.normCircle_coe]
    rw [h1, h2, hnum, norm_neg, neg_div]
  obtain ⟨Λδ, hΛδ⟩ := hlp_exists_continuous_lift ⟨δ, hδc⟩
  have hΛδ' : ∀ t : ℝ, Circle.exp (Λδ t) = δ t := fun t => hΛδ t
  have hδnz : Λδ (2 * Real.pi) - Λδ 0 ≠ 0 :=
    hlp_lift_diff_ne_zero_of_odd δ Λδ Λδ.continuous hΛδ' hδodd
  -- the homotopy from `γ` to the odd loop `δ`
  set ψ : ℝ → ℝ := fun s => max 0 (min 1 s) with hψdef
  have hψ0 : ∀ s : ℝ, 0 ≤ ψ s := fun s => le_max_left 0 (min 1 s)
  have hψ1 : ∀ s : ℝ, ψ s ≤ 1 := fun s => max_le zero_le_one (min_le_left 1 s)
  have hψc : Continuous ψ := by rw [hψdef]; fun_prop
  have hψ_0 : ψ 0 = 0 := by simp [hψdef]
  have hψ_1 : ψ 1 = 1 := by simp [hψdef]
  have hnormcp : ∀ θ : ℝ, ‖(((circlePoint θ : Disc)) : ℂ)‖ = 1 := fun θ => by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  have hval : ∀ p : ℝ × ℝ,
      ‖(1 - ψ p.2) * (z₀ : ℂ) + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖
        ≤ (1 - ψ p.2) * ‖(z₀ : ℂ)‖ + ψ p.2 * 1 := by
    intro p
    calc ‖(1 - ψ p.2) * (z₀ : ℂ) + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖
        ≤ ‖(1 - ψ p.2) * (z₀ : ℂ)‖ + ‖ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖ :=
          norm_add_le _ _
      _ = |1 - ψ p.2| * ‖(z₀ : ℂ)‖
            + |ψ p.2| * ‖(((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖ := by
          rw [norm_mul, norm_mul,
            show (1 - (ψ p.2 : ℂ)) = ((1 - ψ p.2 : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      _ = (1 - ψ p.2) * ‖(z₀ : ℂ)‖ + ψ p.2 * 1 := by
          rw [hnormcp (p.1 + Real.pi), abs_of_nonneg (by linarith [hψ1 p.2]),
            abs_of_nonneg (hψ0 p.2)]
  have hBmem : ∀ p : ℝ × ℝ, ‖(1 - ψ p.2) * (z₀ : ℂ)
      + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖ ≤ 1 := by
    intro p
    nlinarith [hval p, hψ0 p.2, hψ1 p.2, norm_nonneg (z₀ : ℂ), hz₀.le]
  let B : ℝ × ℝ → Disc := fun p =>
    ⟨(1 - ψ p.2) * (z₀ : ℂ) + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ),
      by rw [Metric.mem_closedBall, dist_zero_right]; exact hBmem p⟩
  have hBc : Continuous B := by
    have hcp : Continuous (circlePoint : ℝ → Disc) := hlp_continuous_circlePoint
    have hfun : Continuous fun p : ℝ × ℝ =>
        (1 - (ψ p.2 : ℂ)) * (z₀ : ℂ)
          + (ψ p.2 : ℂ) * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ) := by
      fun_prop
    exact Continuous.subtype_mk hfun (fun p => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hBmem p)
  have hB0 : ∀ t : ℝ, B (t, 0) = z₀ := by
    intro t
    apply Subtype.ext
    simp only [B, hψ_0]
    push_cast
    ring
  have hB1 : ∀ t : ℝ, B (t, 1) = circlePoint (t + Real.pi) := by
    intro t
    apply Subtype.ext
    simp only [B, hψ_1]
    push_cast
    ring
  have hBper : ∀ t s : ℝ, B (t + 2 * Real.pi, s) = B (t, s) := by
    intro t s
    apply Subtype.ext
    simp only [B, show t + 2 * Real.pi + Real.pi = t + Real.pi + 2 * Real.pi from by ring,
      hlp_circlePoint_add_two_pi (t + Real.pi)]
  have hKne : ∀ p : ℝ × ℝ, g (circlePoint p.1) - g (B p) ≠ 0 := by
    intro p h
    have h1 : circlePoint p.1 = B p := hg (sub_eq_zero.mp h)
    rcases eq_or_lt_of_le (hψ1 p.2) with h2 | h2
    · have h3 : B p = circlePoint (p.1 + Real.pi) := by
        apply Subtype.ext
        simp only [B, h2]
        push_cast
        ring
      exact hδne p.1 (sub_eq_zero.mpr (by rw [h1, h3]))
    · have h3 : ‖((B p : Disc) : ℂ)‖ < 1 := by
        have h4 : ((B p : Disc) : ℂ)
            = (1 - ψ p.2) * (z₀ : ℂ) + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ) :=
          rfl
        rw [h4]
        have h6 : ‖(1 - ψ p.2) * (z₀ : ℂ) + ψ p.2 * (((circlePoint (p.1 + Real.pi) : Disc)) : ℂ)‖
            ≤ (1 - ψ p.2) * ‖(z₀ : ℂ)‖ + ψ p.2 * 1 := hval p
        have h7 : 0 < 1 - ψ p.2 := by linarith
        nlinarith [h6, hz₀, h7, hψ0 p.2, norm_nonneg (z₀ : ℂ)]
      have h4 : ‖(((circlePoint p.1 : Disc)) : ℂ)‖ = 1 := hnormcp p.1
      rw [← congrArg (fun z : Disc => ‖(z : ℂ)‖) h1, h4] at h3
      linarith
  let K : ℝ × ℝ → Circle := fun p =>
    Work.CoreTopology.normCircle (g (circlePoint p.1) - g (B p)) (hKne p)
  have hKc : Continuous K := by
    refine Work.CoreTopology.continuous_normCircle _ ?_ hKne
    exact (g.continuous.comp (hlp_continuous_circlePoint.comp continuous_fst)).sub
      (g.continuous.comp hBc)
  have hKper : ∀ t s : ℝ, K (t + 2 * Real.pi, s) = K (t, s) := by
    intro t s
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe,
      hlp_circlePoint_add_two_pi t, hBper t s]
  have hK0 : ∀ t : ℝ, K (t, 0) = γ t := by
    intro t
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, hB0 t]
  have hK1 : ∀ t : ℝ, K (t, 1) = δ t := by
    intro t
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, hB1 t]
  have hΛγ : ∀ t : ℝ, Circle.exp (Λ t) = K (t, 0) := fun t => by rw [hK0 t]; exact hΛ t
  have hΛδK : ∀ t : ℝ, Circle.exp (Λδ t) = K (t, 1) := fun t => by rw [hK1 t]; exact hΛδ' t
  have hmain : Λ (2 * Real.pi) - Λ 0 = Λδ (2 * Real.pi) - Λδ 0 :=
    hlp_lift_diff_eq_of_homotopy ⟨K, hKc⟩ Λ Λδ hKper hΛc hΛγ Λδ.continuous hΛδK
  exact fun h => hδnz (hmain ▸ h)

/-! ## The main theorem -/

theorem disc_openImage_subset_boundedSide {γ : Work.Smooth.Jordan.PlaneCurve}
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)}
    (hFinj : Function.Injective F)
    (hFbd : ∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.circlePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ)
    (hFint : ∀ z : Work.Smooth.SphereJordan.Disc,
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 → ‖((F z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1) :
    ∀ z : Work.Smooth.SphereJordan.Disc,
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 → ((F z : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ S.V := by
  set f : C(Disc, ℂ) :=
    ⟨fun z : Disc => ((F z : Disc) : ℂ), continuous_subtype_val.comp F.continuous⟩ with hfdef
  have hfinj : Function.Injective f := fun a b h => hFinj (Subtype.ext h)
  have hfb : ∀ θ : ℝ, f (circlePoint θ) = γ.γ θ := fun θ => hFbd θ
  intro z hz
  by_contra hmem
  have hztrace : f z ∉ γ.trace := by
    rintro ⟨θ, hθ⟩
    have h1 : f z = f (circlePoint θ) := by rw [hfb θ, hθ]
    have h2 : z = circlePoint θ := hfinj h1
    rw [h2] at hz
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at hz
    exact absurd hz (lt_irrefl 1)
  have hzU : f z ∈ S.U := by
    have h : f z ∈ S.U ∪ S.V := by
      rw [S.union_eq]
      simpa using hztrace
    rcases h with h | h
    · exact h
    · exact absurd h hmem
  have hnotrange : ∀ w : Disc, S.e w ≠ f z := by
    intro w hw
    have hw1 : ‖(w : ℂ)‖ ≤ 1 := by
      have h := w.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · have hV : S.e w ∈ S.V := by
        rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
        exact ⟨w, hlt, rfl⟩
      rw [hw] at hV
      exact Set.disjoint_left.mp S.disjoint_UV hzU hV
    · obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w heq
      have htr : f z ∈ γ.trace := ⟨θ, by rw [← S.boundary θ, hθ, hw]⟩
      exact hztrace htr
  have hLne : ∀ t : ℝ, S.e (circlePoint t) - f z ≠ 0 :=
    fun t => sub_ne_zero.mpr (hnotrange (circlePoint t))
  have hSb : ∀ t : ℝ, S.e (circlePoint t) = f (circlePoint t) := by
    intro t; rw [S.boundary t, hfb t]
  obtain ⟨Λ, hΛ⟩ := hlp_exists_continuous_lift
    ⟨fun t : ℝ => Work.CoreTopology.normCircle (S.e (circlePoint t) - f z) (hLne t), by
      refine Work.CoreTopology.continuous_normCircle _ ?_ hLne
      exact (S.e.continuous.comp hlp_continuous_circlePoint).sub continuous_const⟩
  have hΛ' : ∀ t : ℝ, Circle.exp (Λ t)
      = Work.CoreTopology.normCircle (S.e (circlePoint t) - f z) (hLne t) := fun t => hΛ t
  have hΦne : ∀ w : Disc, S.e w - f z ≠ 0 := fun w => sub_ne_zero.mpr (hnotrange w)
  let Φ : C(Disc, Circle) :=
    ⟨fun w : Disc => Work.CoreTopology.normCircle (S.e w - f z) (hΦne w), by
      refine Work.CoreTopology.continuous_normCircle _ ?_ hΦne
      exact S.e.continuous.sub continuous_const⟩
  have hΦb : ∀ θ : ℝ, Φ (circlePoint θ)
      = Work.CoreTopology.normCircle (S.e (circlePoint θ) - f z) (hLne θ) := by
    intro θ
    exact hlp_normCircle_irrel (S.e (circlePoint θ) - f z) (hΦne (circlePoint θ)) (hLne θ)
  have hper : ∀ t : ℝ, Work.CoreTopology.normCircle (S.e (circlePoint (t + 2 * Real.pi)) - f z)
        (hLne (t + 2 * Real.pi))
      = Work.CoreTopology.normCircle (S.e (circlePoint t) - f z) (hLne t) := by
    intro t
    exact hlp_normCircle_congr (w := S.e (circlePoint (t + 2 * Real.pi)) - f z)
      (w' := S.e (circlePoint t) - f z) (h := by rw [hlp_circlePoint_add_two_pi t])
      (h1 := hLne (t + 2 * Real.pi)) (h2 := hLne t)
  have hdiff0 : Λ (2 * Real.pi) - Λ 0 = 0 :=
    hlp_lift_diff_eq_zero_of_extends
      (fun t : ℝ => Work.CoreTopology.normCircle (S.e (circlePoint t) - f z) (hLne t))
      (by
        refine Work.CoreTopology.continuous_normCircle _ ?_ hLne
        exact (S.e.continuous.comp hlp_continuous_circlePoint).sub continuous_const)
      hper Φ hΦb Λ Λ.continuous hΛ'
  have hne_f : ∀ t : ℝ, f (circlePoint t) - f z ≠ 0 := hlp_loop_ne_zero f hfinj hz
  have hΛf : ∀ t : ℝ, Circle.exp (Λ t)
      = Work.CoreTopology.normCircle (f (circlePoint t) - f z) (hne_f t) := by
    intro t
    rw [hΛ' t]
    exact hlp_normCircle_congr (w := S.e (circlePoint t) - f z)
      (w' := f (circlePoint t) - f z) (h := by rw [hSb t]) (h1 := hLne t) (h2 := hne_f t)
  have hdiff1 : Λ (2 * Real.pi) - Λ 0 ≠ 0 := hlp_winding_ne_zero f hfinj hz Λ Λ.continuous hΛf
  exact hdiff1 hdiff0

end

end Work.Smooth.SphereJordan
