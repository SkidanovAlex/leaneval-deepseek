import Mathlib
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide
import Submission.Work.Smooth.Jordan.wind_mem_int

/-!
# The winding integral of a curve that extends over the disc avoiding the point

For a `C¹` closed plane curve `c` and a point `x` off its trace, if the loop `γ` extends to a
continuous map `F : 𝔻 → ℂ` whose values avoid `x`, then the winding integral of `γ` around `x`
vanishes: `Work.Smooth.JordanSeparation.ind_eq_zero_of_avoiding_extension`.

This is one half of the classical theorem that for `C¹` curves the analytic winding integral agrees
with the topological degree: the loop is then null-homotopic in `ℂ ∖ {x}`, so its degree is `0`.
It is also the missing half of `Work.Smooth.Plane.PlaneJordanData` (the classical input of
`Submission/Work/Smooth/Plane`).

## The proof

Let `H = windingPrimitive c x` be the primitive of the winding integrand.  Two facts
(`wind_mem_int.lean`):

* `(γ t - x) * exp (-(H t)) = γ 0 - x`, i.e. `exp (H t) = (γ t - x)/(γ 0 - x)`;
* `H (2π) ∈ 2πi ℤ`.

Let `Λ` lift the normalised loop `t ↦ (γ t - x)/‖γ t - x‖` to the universal cover of the circle.
Since that loop extends over the disc avoiding `x`, monodromy gives `Λ (2π) = Λ 0`
(`hlp_lift_diff_eq_zero_of_extends`).

Comparing exponentials gives, for every `t`,

`exp (H t - i (Λ t - Λ 0)) = ‖γ t - x‖ / ‖γ 0 - x‖ > 0`,

so `t ↦ (H t).im - (Λ t - Λ 0)` has values in `2πℤ`.  Hence the set where it vanishes is both open
(the `2πℤ`-valuedness and continuity) and closed, and it contains `0`; by preconnectedness of `ℝ`
it is everything.  So `(H (2π)).im = Λ (2π) - Λ 0 = 0`; together with `H (2π) ∈ 2πiℤ` this gives
`H (2π) = 0`, hence `wind c x = 0` and `ind c x = 0`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The imaginary part of the primitive is the lift-difference of the normalised curve.**  If
`Λ` is a continuous lift of the argument of `γ · - x` (`exp (i Λ t) = (γ t - x)/‖γ t - x‖`), then
`(windingPrimitive c x (2π)).im = Λ (2π) - Λ 0`. -/
theorem im_windingPrimitive_eq_of_lift (c : Work.Smooth.Jordan.SmoothPlaneCurve) {x : ℂ}
    (hx : x ∉ c.trace) {Λ : ℝ → ℝ} (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Complex.exp ((Λ t : ℂ) * Complex.I)
      = (c.γ t - x) / ((‖c.γ t - x‖ : ℝ) : ℂ)) :
    (Work.Smooth.Jordan.windingPrimitive c x (2 * Real.pi)).im
      = Λ (2 * Real.pi) - Λ 0 := by
  have hγne : ∀ t : ℝ, c.γ t - x ≠ 0 := fun t h => hx (sub_eq_zero.mp h ▸ c.mem_trace t)
  -- the exponential of the primitive
  have hexp : ∀ t : ℝ, Complex.exp (Work.Smooth.Jordan.windingPrimitive c x t)
      = (c.γ t - x) / (c.γ 0 - x) := by
    intro t
    have h := Work.Smooth.Jordan.windingPrimitive_const_exp c hx t
    have h2 : Complex.exp (-(Work.Smooth.Jordan.windingPrimitive c x t))
        = (c.γ 0 - x) / (c.γ t - x) := by
      rw [eq_div_iff (hγne t), mul_comm]
      exact h
    have h3 : Complex.exp (Work.Smooth.Jordan.windingPrimitive c x t)
        = (Complex.exp (-(Work.Smooth.Jordan.windingPrimitive c x t)))⁻¹ := by
      rw [Complex.exp_neg, inv_inv]
    rw [h3, h2, inv_div]
  -- `exp (H t - i (Λ t - Λ 0))` is a positive real
  have hkey : ∀ t : ℝ, Complex.exp (Work.Smooth.Jordan.windingPrimitive c x t
      - ((Λ t - Λ 0 : ℝ) : ℂ) * Complex.I)
      = ((‖c.γ t - x‖ / ‖c.γ 0 - x‖ : ℝ) : ℂ) := by
    intro t
    have hA : Complex.exp (((Λ t - Λ 0 : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((Λ t : ℂ) * Complex.I) / Complex.exp ((Λ 0 : ℂ) * Complex.I) := by
      rw [show ((Λ t - Λ 0 : ℝ) : ℂ) * Complex.I
          = (Λ t : ℂ) * Complex.I - (Λ 0 : ℂ) * Complex.I from by push_cast; ring,
        Complex.exp_sub]
    rw [Complex.exp_sub, hA, hexp t, hlift t, hlift 0]
    have h1 : (‖c.γ t - x‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (hγne t)
    have h2 : (‖c.γ 0 - x‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (hγne 0)
    have hD : -(c.γ t * x) + c.γ t * c.γ 0 - x * c.γ 0 + x ^ 2 ≠ 0 := by
      rw [show -(c.γ t * x) + c.γ t * c.γ 0 - x * c.γ 0 + x ^ 2
          = (c.γ t - x) * (c.γ 0 - x) from by ring]
      exact mul_ne_zero (hγne t) (hγne 0)
    push_cast
    field_simp
    rw [← mul_inv_cancel₀ hD]
    ring
  -- the imaginary part is a multiple of `2π`
  have hmem : ∀ t : ℝ, ∃ n : ℤ,
      (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = n * (2 * Real.pi) := by
    intro t
    have h := hkey t
    set w : ℂ := Work.Smooth.Jordan.windingPrimitive c x t
      - ((Λ t - Λ 0 : ℝ) : ℂ) * Complex.I with hw
    have hwim : w.im = (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) := by
      rw [hw, Complex.sub_im, Complex.mul_im]
      simp
    have him0 : (Complex.exp w).im = 0 := by rw [h]; simp
    have hre0 : 0 < (Complex.exp w).re := by
      rw [h]
      simp only [Complex.ofReal_re]
      exact div_pos (norm_pos_iff.mpr (hγne t)) (norm_pos_iff.mpr (hγne 0))
    have hsin : Real.sin w.im = 0 := by
      have h1 : Real.exp w.re * Real.sin w.im = 0 := by
        rw [← Complex.exp_im]; exact him0
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (ne_of_gt (Real.exp_pos w.re))
      · exact h2
    have hcos : 0 < Real.cos w.im := by
      have h1 : 0 < Real.exp w.re * Real.cos w.im := by
        rw [← Complex.exp_re]; exact hre0
      nlinarith [Real.exp_pos w.re]
    have hcos1 : Real.cos w.im = 1 := by
      have h := Real.sin_sq_add_cos_sq w.im
      rw [hsin] at h
      nlinarith
    have hexpI : Complex.exp ((w.im : ℂ) * Complex.I) = 1 := by
      rw [Complex.exp_ofReal_mul_I, hsin, hcos1]
      simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      (by show Complex.exp ((w.im : ℂ) * Complex.I) = Complex.exp 0; rw [hexpI, Complex.exp_zero])
    have h4 : (w.im : ℂ) * Complex.I = (n : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I := by
      rw [hn]; ring
    have h5 : (w.im : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero h4
    refine ⟨n, ?_⟩
    have h5R : w.im = (n : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.re h5
      simpa using h
    rw [← hwim, h5R]
  -- `g` is continuous
  have hcont : Continuous fun t : ℝ =>
      (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) := by
    have hH : Continuous fun t : ℝ => Work.Smooth.Jordan.windingPrimitive c x t :=
      continuous_iff_continuousAt.mpr fun t =>
        (Work.Smooth.Jordan.windingPrimitive_hasDerivAt c hx t).continuousAt
    exact (Complex.continuous_im.comp hH).sub (hΛ.sub continuous_const)
  have hzero0 : (Work.Smooth.Jordan.windingPrimitive c x 0).im - (Λ 0 - Λ 0) = 0 := by
    simp [Work.Smooth.Jordan.windingPrimitive_zero]
  -- the vanishing set is clopen and non-empty
  have hSopen : IsOpen {t : ℝ |
      (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hct : ContinuousAt (fun t : ℝ =>
        (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0)) t := hcont.continuousAt
    rw [Metric.continuousAt_iff] at hct
    obtain ⟨δ, hδpos, hδ⟩ := hct (2 * Real.pi) (by positivity)
    filter_upwards [Metric.ball_mem_nhds t hδpos] with s hs
    have h1 : |(Work.Smooth.Jordan.windingPrimitive c x s).im - (Λ s - Λ 0)| < 2 * Real.pi := by
      have h2 := hδ hs
      rw [Real.dist_eq, ht, sub_zero] at h2
      exact h2
    obtain ⟨n, hn⟩ := hmem s
    have h1' : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      have h2 : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by rwa [hn] at h1
      rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h2
    have hn0 : n = 0 := by
      have h4 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos, h1']
      have h5 : |n| < (1 : ℤ) := by exact_mod_cast h4
      have h6 := abs_lt.mp h5
      omega
    rw [hn, hn0, Int.cast_zero, zero_mul]
  have hSclosed : IsClosed {t : ℝ |
      (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0} :=
    isClosed_eq hcont continuous_const
  have hall : (Set.univ : Set ℝ) ⊆ {t : ℝ |
      (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0} := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
        (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ)))
        {t : ℝ | (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0}
        {t : ℝ | (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0}ᶜ
        hSclosed hSopen.isClosed_compl
        (by intro t _; rcases Classical.em (t ∈ {t : ℝ |
              (Work.Smooth.Jordan.windingPrimitive c x t).im - (Λ t - Λ 0) = 0}) with h | h
            exacts [Or.inl h, Or.inr h])
        (by simp) with h | h
    · exact h
    · exfalso
      exact (h (Set.mem_univ 0)) hzero0
  have hfin : (Work.Smooth.Jordan.windingPrimitive c x (2 * Real.pi)).im
      - (Λ (2 * Real.pi) - Λ 0) = 0 := hall (Set.mem_univ _)
  rw [sub_eq_zero] at hfin
  exact hfin


/-- **The index vanishes for a curve that extends over the disc avoiding the point.**  For a `C¹`
closed plane curve `c` and `x` off its trace, if the loop `γ` extends to a continuous map
`F : 𝔻 → ℂ` avoiding `x`, then `ind c x = 0`.

This is the "winding number is a homotopy invariant" half of the classical identification of the
analytic winding integral with the topological degree.  It is also exactly the missing half of
`Work.Smooth.Plane.PlaneJordanData`. -/
theorem ind_eq_zero_of_avoiding_extension (c : Work.Smooth.Jordan.SmoothPlaneCurve) {x : ℂ}
    (hx : x ∉ c.trace) (F : C(Work.Smooth.Jordan.Disc, ℂ)) (hF : ∀ z, F z ≠ x)
    (hbd : ∀ θ : ℝ, F (Work.Smooth.Jordan.circlePoint θ) = c.γ θ) :
    Work.Smooth.Jordan.ind c x = 0 := by
  have hγne : ∀ θ : ℝ, c.γ θ - x ≠ 0 := fun θ h => hx (sub_eq_zero.mp h ▸ c.mem_trace θ)
  have hφc : Continuous fun θ : ℝ => Work.CoreTopology.normCircle (c.γ θ - x) (hγne θ) :=
    Work.CoreTopology.continuous_normCircle _ (c.cont.sub continuous_const) hγne
  have hφper : ∀ t : ℝ,
      Work.CoreTopology.normCircle (c.γ (t + 2 * Real.pi) - x) (hγne (t + 2 * Real.pi))
        = Work.CoreTopology.normCircle (c.γ t - x) (hγne t) := by
    intro t
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, c.periodic_apply]
  have hFne : ∀ z : Work.Smooth.Jordan.Disc, F z - x ≠ 0 := fun z h => hF z (sub_eq_zero.mp h)
  have hΦc : Continuous fun z : Work.Smooth.Jordan.Disc =>
      Work.CoreTopology.normCircle (F z - x) (hFne z) :=
    Work.CoreTopology.continuous_normCircle _ (F.continuous.sub continuous_const) hFne
  have hΦbd : ∀ θ : ℝ,
      Work.CoreTopology.normCircle (F (Work.Smooth.Jordan.circlePoint θ) - x) (hFne _)
        = Work.CoreTopology.normCircle (c.γ θ - x) (hγne θ) := by
    intro θ
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Work.CoreTopology.normCircle_coe, hbd θ]
  obtain ⟨Λ, hΛ⟩ := Work.Smooth.SphereJordan.hlp_exists_continuous_lift
    ⟨fun θ : ℝ => Work.CoreTopology.normCircle (c.γ θ - x) (hγne θ), hφc⟩
  have hlift : ∀ t : ℝ, Circle.exp (Λ t)
      = Work.CoreTopology.normCircle (c.γ t - x) (hγne t) := fun t => hΛ t
  have hcloses : Λ (2 * Real.pi) - Λ 0 = 0 :=
    Work.Smooth.SphereJordan.hlp_lift_diff_eq_zero_of_extends _ hφc hφper
      ⟨fun z : Work.Smooth.Jordan.Disc =>
        Work.CoreTopology.normCircle (F z - x) (hFne z), hΦc⟩ hΦbd Λ Λ.continuous hlift
  have hliftC : ∀ t : ℝ, Complex.exp ((Λ t : ℂ) * Complex.I)
      = (c.γ t - x) / ((‖c.γ t - x‖ : ℝ) : ℂ) := by
    intro t
    have h := congrArg (fun z : Circle => (z : ℂ)) (hlift t)
    rwa [Circle.coe_exp, Work.CoreTopology.normCircle_coe] at h
  have him := im_windingPrimitive_eq_of_lift c hx Λ.continuous hliftC
  obtain ⟨k, hk⟩ := Work.Smooth.Jordan.windingPrimitive_int c hx
  have him0 : (Work.Smooth.Jordan.windingPrimitive c x (2 * Real.pi)).im = 0 := by
    rw [him, hcloses]
  have hk0 : k = 0 := by
    have h1 : (Work.Smooth.Jordan.windingPrimitive c x (2 * Real.pi)).im
        = (k : ℝ) * (2 * Real.pi) := by
      have h2 := congrArg Complex.im hk
      simpa [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] using h2
    have h3 : (k : ℝ) * (2 * Real.pi) = 0 := by rw [← h1]; exact him0
    have h4 : (k : ℝ) = 0 := by nlinarith [Real.pi_pos]
    exact_mod_cast h4
  have hzero : Work.Smooth.Jordan.windingPrimitive c x (2 * Real.pi) = 0 := by
    rw [hk, hk0, Int.cast_zero, zero_mul]
  have hwind : Work.Smooth.Jordan.wind c x = 0 := by
    rw [Work.Smooth.Jordan.wind_def, hzero, mul_zero]
  have hcast : ((Work.Smooth.Jordan.ind c x : ℤ) : ℂ) = 0 := by
    rw [Work.Smooth.Jordan.ind_spec c (Work.Smooth.Jordan.wind_mem_int c hx), hwind]
  exact_mod_cast hcast

end

end Work.Smooth.JordanSeparation
