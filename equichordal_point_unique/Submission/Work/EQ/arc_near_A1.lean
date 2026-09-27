import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.normEqCurve_periodic_and_sum
import Submission.Work.EQ.polarPt_basic
import Submission.Work.EQ.polarPt_inj
import Submission.Work.EQ.arc_axis_points
import Submission.Work.EQ.arc_trichotomy
import Submission.Work.EQ.arc_covering

namespace Work.EQ

open Complex

/-- The point of the normalised curve at angle `θ`: `polarPt (-(a/2)) (ρ₁ θ) θ`.
Auxiliary (private) notation for this file. -/
private noncomputable def arcPtAux (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  polarPt (-(a/2)) (ρ₁ θ) θ

private lemma arcPtAux_eq (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    arcPtAux a ρ₁ θ = ((-(a/2) + ρ₁ θ * Real.cos θ : ℝ) : ℂ)
      + ((ρ₁ θ * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [arcPtAux, polarPt, Complex.exp_ofReal_mul_I]; push_cast; ring

private lemma arcPtAux_im (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    (arcPtAux a ρ₁ θ).im = ρ₁ θ * Real.sin θ := by
  rw [arcPtAux_eq, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma arcPtAux_add_period (a : ℝ) (ρ₁ : ℝ → ℝ)
    (hper : Function.Periodic ρ₁ (2 * Real.pi)) (n : ℤ) (x : ℝ) :
    arcPtAux a ρ₁ (x + n * (2 * Real.pi)) = arcPtAux a ρ₁ x := by
  have hρ : ρ₁ (x + n * (2 * Real.pi)) = ρ₁ x := (hper.int_mul n) x
  have hexp : Complex.exp (((x + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
    have harg : ((x + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (x : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [arcPtAux, polarPt, hρ, hexp]

/-- Every real point of the curve `{polarPt (-(a/2)) (ρ₁ θ) θ}` is the point at angle `0` or at
angle `π`: `(P θ).im = ρ₁ θ * sin θ` and `ρ₁ > 0` force `sin θ = 0`, and `2π`-periodicity then
reduces `θ` to `0` or `π` modulo `2π`. -/
private lemma arcPtAux_im_zero (a : ℝ) (ρ₁ : ℝ → ℝ) (hper : Function.Periodic ρ₁ (2 * Real.pi))
    (hpos : ∀ θ, 0 < ρ₁ θ) (θ : ℝ) (h : (arcPtAux a ρ₁ θ).im = 0) :
    arcPtAux a ρ₁ θ = arcPtAux a ρ₁ 0 ∨ arcPtAux a ρ₁ θ = arcPtAux a ρ₁ Real.pi := by
  have him : ρ₁ θ * Real.sin θ = 0 := by rw [arcPtAux_im] at h; exact h
  have hsin : Real.sin θ = 0 := (mul_eq_zero.mp him).resolve_left (ne_of_gt (hpos θ))
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have hθ : θ = (m : ℝ) * (2 * Real.pi) := by rw [← hn, hm]; push_cast; ring
    rw [hθ]; simpa using arcPtAux_add_period a ρ₁ hper m 0
  · right
    have hθ : θ = Real.pi + (m : ℝ) * (2 * Real.pi) := by rw [← hn, hm]; push_cast; ring
    rw [hθ]; simpa using arcPtAux_add_period a ρ₁ hper m Real.pi

/-- Geometry of the upper arc of a symmetric normalised equichordal curve near the fixed point
`A₁ = -1/2` of `eqU`.  Write `P θ = polarPt (-(a/2)) (ρ₁ θ) θ`, so that the curve is `P '' ℝ` and
the open upper arc is `{P θ : θ ∈ (0, π)}`.

Contents:
* **normalisation.** The two points where the curve meets the axis are `∓1/2`, i.e.
  `P π = -1/2`, `P 0 = 1/2`, `ρ₁ π = (1-a)/2`, `ρ₁ 0 = (1+a)/2`.  (Reason: `ρ₁ (θ+π) = 1 - ρ₁ θ`
  gives `P 0 - P π = 1`; `hs₁` gives `conj (P θ) = P (-θ)` and `hs₂` gives
  `-(conj (P θ)) = polarPt (a/2) (ρ₂ (π-θ)) (π-θ) ∈ c`, so the curve is invariant under
  `z ↦ -z`; hence `-P π` is a real point of the curve, i.e. `P 0` or `P π`, and `P π < 0`.)
* every real point of the curve is `A₁` or `A₂` (from `(P θ).im = ρ₁ θ * sin θ`);
* every point of the open upper arc is `P θ` with `θ ∈ (0,π)` (reduce `θ` mod `2π`);
* **trichotomy.** For `ρ' ∈ (0,1)` and `ε > 0` there is `η > 0` such that a point `P θ`,
  `θ ∈ (0,π)`, of height `≤ η` and with `|(P θ).re + 1/2| ≤ ρ'` must have `θ > π - ε`.
  (Indeed for `θ ≤ π - ε` either `θ` is near `0`, where `|(P θ).re + 1/2|` is near `1 > ρ'`, or
  it lies in the middle, where `(P θ).im ≥ m > 0`.)
* **covering.** For `ρ' ∈ (0,1)` there is `η > 0` such that every height `y ∈ (0,η)` is attained by
  a point `P θ`, `θ ∈ (0,π)`, with `|(P θ).re + 1/2| ≤ ρ'`.  (Continuity at `π` gives a small
  interval `(π-δ, π)` of points within `ρ'/2` of `A₁`; its heights form an interval with infimum
  `0`, so the intermediate value property provides `θ` at height `y`, and such `θ` is `> π - ε`
  for every `ε > 0`, hence inside that interval for `y` small enough.) -/
theorem arc_near_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) :
    polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi = (-(1/2) : ℂ) ∧
    polarPt (-(a/2)) (ρ₁ 0) 0 = ((1/2) : ℂ) ∧ ρ₁ Real.pi = (1 - a) / 2 ∧ ρ₁ 0 = (1 + a) / 2 ∧
    (∀ θ, (polarPt (-(a/2)) (ρ₁ θ) θ).im = 0 →
      polarPt (-(a/2)) (ρ₁ θ) θ = (-(1/2) : ℂ) ∨
        polarPt (-(a/2)) (ρ₁ θ) θ = ((1/2) : ℂ)) ∧
    (∀ z ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ), 0 < z.im →
      ∃ θ, 0 < θ ∧ θ < Real.pi ∧ z = polarPt (-(a/2)) (ρ₁ θ) θ) ∧
    (∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∀ ε : ℝ, 0 < ε → ε < Real.pi →
      ∃ η : ℝ, 0 < η ∧ ∀ θ, 0 < θ → θ < Real.pi →
        (polarPt (-(a/2)) (ρ₁ θ) θ).im ≤ η →
        |(polarPt (-(a/2)) (ρ₁ θ) θ).re + 1 / 2| ≤ ρ' → Real.pi - ε < θ) ∧
    (∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ η : ℝ, 0 < η ∧ ∀ y, 0 < y → y < η → ∃ θ, 0 < θ ∧ θ < Real.pi ∧
        (polarPt (-(a/2)) (ρ₁ θ) θ).im = y ∧
        |(polarPt (-(a/2)) (ρ₁ θ) θ).re + 1 / 2| ≤ ρ') := by
  -- the four normalisation facts (`arc_axis_points`)
  obtain ⟨hax1, hax2, hρπ, hρ0⟩ := arc_axis_points ha0 ha1 hC hs₁ hs₂
  -- `2π`-periodicity and the sum relation
  obtain ⟨hper₁, hper₂, hρ₂eq⟩ := normEqCurve_periodic_and_sum hC hs₁ hs₂
  obtain ⟨hcont₁, hcont₂, hρ₁pos, hρ₂pos, hsum₁, hsum₂, hrange⟩ := hC
  refine ⟨hax1, hax2, hρπ, hρ0, ?_, ?_, ?_, ?_⟩
  · -- every real point of the curve is `∓1/2`
    intro θ h
    have h' : (arcPtAux a ρ₁ θ).im = 0 := h
    rcases arcPtAux_im_zero a ρ₁ hper₁ hρ₁pos θ h' with h0 | hπ
    · right
      change arcPtAux a ρ₁ θ = ((1/2) : ℂ)
      rw [h0]; exact hax2
    · left
      change arcPtAux a ρ₁ θ = (-(1/2) : ℂ)
      rw [hπ]; exact hax1
  · -- every point of the open upper arc has an angle in `(0, π)`
    intro z hz hzim
    obtain ⟨ψ, rfl⟩ := hz
    have him : 0 < (polarPt (-(a/2)) (ρ₁ ψ) ψ - (((-(a/2)) : ℝ) : ℂ)).im := by
      have h1 : (polarPt (-(a/2)) (ρ₁ ψ) ψ - (((-(a/2)) : ℝ) : ℂ)).im
          = (polarPt (-(a/2)) (ρ₁ ψ) ψ).im := by simp
      rw [h1]; exact hzim
    exact exists_angle_of_mem_range hper₁ hρ₁pos ⟨ψ, rfl⟩ him
  · -- trichotomy
    intro ρ' hρ'0 hρ'1 ε hε0 hεπ
    exact arc_trichotomy (a := a) (ρ₁ := ρ₁) hcont₁ hρ₁pos hρ0 ρ' hρ'0 hρ'1 ε hε0 hεπ
  · -- covering
    intro ρ' hρ'0 hρ'1
    exact arc_covering (a := a) (ρ₁ := ρ₁) hcont₁ hρ₁pos hρπ ρ' hρ'0 hρ'1

end Work.EQ
