import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V

/-!
# Winding-number parity, in a module importable from `thetaFoundation`

This is a copy of `Submission/Work/SphereJordan/odd_windNumber_of_mem_V.lean` (which cannot be
imported here because it imports the later module
`Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane`), with the declarations placed
in the fresh namespace `Work.Smooth.SphereJordan.ThetaOdd` so that no name clashes with the
original arise.

Contents: the parity of the lift difference of an odd loop, the parity of the winding number about
a point of the bounded side of a Jordan curve, the winding-number dictionary
`x ∈ S.V ↔ windNumber ≠ 0`, and the resulting `0`-or-odd statement.
-/

namespace Work.Smooth.SphereJordan.ThetaOdd

open Set
open Work.Smooth.SphereJordan

noncomputable section

/-- **Odd loops have odd lift difference.**  If `φ : ℝ → S¹` is a loop of the circle which is
*odd* under the half-period shift, `φ (t + π) = - φ t`, then for every continuous lift
`Λ : ℝ → ℝ` of `φ` the increment over one period is an odd multiple of `2π`. -/
theorem odd_lift_diff_of_odd_loop {φ : ℝ → Circle} {Λ : ℝ → ℝ} (hΛc : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = φ t)
    (hodd : ∀ t : ℝ, ((φ (t + Real.pi) : Circle) : ℂ) = - ((φ t : Circle) : ℂ)) :
    ∃ m : ℤ, Λ (2 * Real.pi) - Λ 0 = (2 * (m : ℝ) + 1) * (2 * Real.pi) := by
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
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have hdiff : Λ (2 * Real.pi) - Λ 0 = 2 * (Λ Real.pi - Λ 0) := by linarith
  refine ⟨m, ?_⟩
  rw [hdiff, hm]; ring

/-- **The lift difference of the boundary loop of an injective disc map about an interior value is
an odd multiple of `2π`.**  This is the parity form of
`Work.Smooth.SphereJordan.hlp_winding_ne_zero`. -/
theorem odd_lift_diff_of_injective_disc (g : C(Disc, ℂ)) (hg : Function.Injective g)
    {z₀ : Disc} (hne : ∀ t : ℝ, g (circlePoint t) - g z₀ ≠ 0) (hz₀ : ‖(z₀ : ℂ)‖ < 1)
    (Λ : ℝ → ℝ) (hΛc : Continuous Λ)
    (hΛ : ∀ t : ℝ, Circle.exp (Λ t)
      = Work.CoreTopology.normCircle (g (circlePoint t) - g z₀) (hne t)) :
    ∃ m : ℤ, Λ (2 * Real.pi) - Λ 0 = (2 * (m : ℝ) + 1) * (2 * Real.pi) := by
  have hδne := hlp_odd_ne g hg
  let γ : ℝ → Circle := fun t =>
    Work.CoreTopology.normCircle (g (circlePoint t) - g z₀) (hne t)
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
  obtain ⟨m, hm⟩ := odd_lift_diff_of_odd_loop Λδ.continuous hΛδ' hδodd
  exact ⟨m, by rw [hmain, hm]⟩

/-- **The winding number vanishes at every point of the trace of the curve**: the index of a loop
passing through `0` is `0` by definition. -/
theorem windNumber_eq_zero_of_mem_range {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} (hz : z ∈ Set.range γ) :
    windNumber γ hγ z = 0 := by
  obtain ⟨s, hs⟩ := hz
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set k : ℤ := ⌊s / (2 * Real.pi)⌋ with hk
  have hk1 : ((k : ℝ)) ≤ s / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
  have hk2 : s / (2 * Real.pi) < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
  have ht₁ : 0 ≤ s / (2 * Real.pi) - (k : ℝ) := by linarith
  have ht₂ : s / (2 * Real.pi) - (k : ℝ) ≤ 1 := by linarith
  set t : unitInterval := ⟨s / (2 * Real.pi) - (k : ℝ), ⟨ht₁, ht₂⟩⟩ with ht
  have hkey : 2 * Real.pi * (s / (2 * Real.pi) - (k : ℝ))
      = s + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  have hz0 : (curveLoop (fun u : ℝ => γ u - z) (hγ.sub continuous_const)) t = 0 := by
    show γ (2 * Real.pi * (t : ℝ)) - z = 0
    rw [show ((t : unitInterval) : ℝ) = s / (2 * Real.pi) - (k : ℝ) from rfl, hkey,
      sub_eq_zero]
    exact (hper.int_mul (-k) s).trans hs
  unfold windNumber
  unfold loopIndex
  rw [dif_neg (by rintro ⟨hne, -⟩; exact hne t hz0)]

/-- **The winding number dictionary**: a point of the plane lies on the bounded side of a simple
closed plane curve exactly when the curve winds around it, for any Jordan--Schoenflies datum of the
curve. -/
theorem mem_V_iff_windNumber_ne_zero {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} :
    z ∈ S.V ↔ Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z ≠ 0 := by
  refine ⟨fun hz => windNumber_ne_zero_of_mem_V S hz, fun hz => ?_⟩
  by_contra hzV
  have hmem : z ∈ S.U ∪ S.V := by
    rw [S.union_eq]
    intro htr
    exact hz (windNumber_eq_zero_of_mem_range γ.cont γ.periodic htr)
  rcases hmem with hU | hV
  · exact hz (windNumber_eq_zero_of_mem_U S.toPlaneSeparation hU)
  · exact hzV hV

/-- **The winding number of a simple closed plane curve about a point of the bounded side is
odd.** -/
theorem odd_windNumber_of_mem_V {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} (hz : z ∈ S.V) :
    Odd (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z) := by
  have hz_trace : z ∉ γ.trace := by
    have hVsub : S.V ⊆ γ.traceᶜ := by
      intro y hy
      have h : y ∈ S.U ∪ S.V := Or.inr hy
      rwa [S.union_eq] at h
    exact hVsub hz
  have hz_trace' : ∀ t : ℝ, γ.γ t ≠ z := fun t h => hz_trace ⟨t, h⟩
  -- `z` is the image of an interior point of the model disc
  have hz_range : z ∈ Set.range S.e := by
    rw [S.range_e]; exact subset_closure hz
  obtain ⟨z₀, hz₀⟩ := hz_range
  have hz₀lt : ‖(z₀ : ℂ)‖ < 1 := by
    have hle : ‖(z₀ : ℂ)‖ ≤ 1 := by
      have h := z₀.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z₀ heq
      exact hz_trace ⟨θ, by rw [← S.boundary θ, hθ, hz₀]⟩
  -- a real lift of the normalised boundary loop, with nonzero increment
  have hne : ∀ θ : ℝ, S.e (circlePoint θ) - S.e z₀ ≠ 0 := hlp_loop_ne_zero S.e S.inj hz₀lt
  have hφc : Continuous fun θ : ℝ =>
      Work.CoreTopology.normCircle (S.e (circlePoint θ) - S.e z₀) (hne θ) :=
    Work.CoreTopology.continuous_normCircle _
      ((S.e.continuous.comp hlp_continuous_circlePoint).sub continuous_const) hne
  obtain ⟨Λ, hΛ⟩ := hlp_exists_continuous_lift
    ⟨fun θ : ℝ => Work.CoreTopology.normCircle (S.e (circlePoint θ) - S.e z₀) (hne θ), hφc⟩
  -- the parity form for the spanning disc, and the loop of the theorem
  obtain ⟨m, hm⟩ := odd_lift_diff_of_injective_disc S.e S.inj hne hz₀lt Λ Λ.continuous hΛ
  let c : C(unitInterval, ℂ) := curveLoop (fun t => γ.γ t - z) (γ.cont.sub continuous_const)
  have hc : ∀ t : unitInterval, c t ≠ 0 := by
    intro t
    exact sub_ne_zero.mpr (hz_trace' (2 * Real.pi * (t : ℝ)))
  have hloop : c 0 = c 1 := by
    show γ.γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ.γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_zero, mul_one]
    have hp : γ.γ (2 * Real.pi) = γ.γ 0 := by simpa using γ.periodic_apply 0
    rw [hp]
  have hlogc : Continuous fun t : unitInterval => Real.log ‖c t‖ :=
    c.continuous.norm.log (fun t => norm_ne_zero_iff.mpr (hc t))
  have hΛcont : Continuous fun t : unitInterval => ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Λ.continuous.comp (by fun_prop))
  let Λc : C(unitInterval, ℂ) :=
    ⟨fun t => (Real.log ‖c t‖ : ℂ) + ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I,
      (Complex.continuous_ofReal.comp hlogc).add (hΛcont.mul continuous_const)⟩
  have halg : ∀ w : ℂ, w ≠ 0 → ((‖w‖ : ℝ) : ℂ) * (w / ((‖w‖ : ℝ) : ℂ)) = w := by
    intro w hw
    rw [← mul_div_assoc,
      mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))]
  have hΛc : ∀ t : unitInterval, Complex.exp (Λc t) = c t := by
    intro t
    have h1 : Complex.exp ((Real.log ‖c t‖ : ℝ) : ℂ) = ((‖c t‖ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hc t))]
    have h2 : Complex.exp (((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (Work.CoreTopology.normCircle
            (S.e (circlePoint (2 * Real.pi * (t : ℝ))) - S.e z₀)
            (hne (2 * Real.pi * (t : ℝ))) : ℂ) := by
      rw [← Circle.coe_exp]
      exact congrArg (fun w : Circle => (w : ℂ)) (hΛ (2 * Real.pi * (t : ℝ)))
    show Complex.exp ((Real.log ‖c t‖ : ℂ)
        + ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = c t
    rw [Complex.exp_add, h1, h2, Work.CoreTopology.normCircle_coe, S.boundary, hz₀]
    exact halg (γ.γ (2 * Real.pi * (t : ℝ)) - z) (hc t)
  have hsub : Λc 1 - Λc 0 = (((Λ (2 * Real.pi) - Λ 0 : ℝ)) : ℂ) * Complex.I := by
    have hnorm : ‖c 1‖ = ‖c 0‖ := by rw [hloop]
    show ((Real.log ‖c 1‖ : ℂ)
        + ((Λ (2 * Real.pi * ((1 : unitInterval) : ℝ)) : ℝ) : ℂ) * Complex.I)
        - ((Real.log ‖c 0‖ : ℂ)
          + ((Λ (2 * Real.pi * ((0 : unitInterval) : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (((Λ (2 * Real.pi) - Λ 0 : ℝ)) : ℂ) * Complex.I
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_one, mul_zero, hnorm]
    push_cast
    ring
  have hspec := loopIndex_spec c hc hloop Λc hΛc
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcancel : (loopIndex c : ℂ) * (2 * (Real.pi : ℂ))
      = (((2 * (m : ℝ) + 1) * (2 * Real.pi) : ℝ) : ℂ) := by
    have h1 : (loopIndex c : ℂ) * (2 * ↑Real.pi * Complex.I)
        = (((Λ (2 * Real.pi) - Λ 0 : ℝ)) : ℂ) * Complex.I := hspec.symm.trans hsub
    have h2 : ((loopIndex c : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I
        = ((((2 * (m : ℝ) + 1) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I := by
      rw [mul_assoc, h1, hm]
    exact mul_right_cancel₀ Complex.I_ne_zero h2
  have hcast : loopIndex c = 2 * m + 1 := by
    refine Int.cast_inj.mp (mul_right_cancel₀ h2π ?_)
    rw [hcancel]
    push_cast
    ring
  show Odd (loopIndex c)
  rw [hcast]
  exact ⟨m, rfl⟩

/-- **Nonvanishing of the winding number forces oddness**: for any Jordan--Schoenflies datum of a
simple closed plane curve, the winding number about a point is odd as soon as it is nonzero (by
`mem_V_iff_windNumber_ne_zero` such a point lies on the bounded side). -/
theorem odd_windNumber_of_ne_zero {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ}
    (hz : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z ≠ 0) :
    Odd (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z) :=
  odd_windNumber_of_mem_V S ((mem_V_iff_windNumber_ne_zero S).mpr hz)

end

/-- **The winding number of a simple closed plane curve about a point off it is `0` or odd.** -/
theorem thetaWindZeroOrOdd (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (J : Work.Smooth.Jordan.PlaneCurve) (hJ : J.IsSimple) {x : ℂ} (hx : x ∉ J.trace) :
    Work.Smooth.SphereJordan.windNumber J.γ J.cont x = 0 ∨
      Odd (Work.Smooth.SphereJordan.windNumber J.γ J.cont x) := by
  obtain ⟨S⟩ := h J hJ
  rcases (show x ∈ S.U ∪ S.V by rw [S.union_eq]; exact hx) with hU | hV
  · exact Or.inl (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S.toPlaneSeparation hU)
  · exact Or.inr (odd_windNumber_of_mem_V S hV)

end Work.Smooth.SphereJordan.ThetaOdd
