import Mathlib
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_basic
import Submission.Work.EQ.eqT_im_arc
import Submission.Work.EQ.eqT_angle_upper
import Submission.Work.EQ.eqT_angle_lower
import Submission.Work.EQ.eqT_continuousOn_D
import Submission.Work.EQ.eqT_axis_fixed

/-!
# The lifted angle map of a normalised two-point equichordal curve

Rychlik's map `T = eqT a` preserves the curve `{P θ}` and its restriction to the open upper
(resp. lower) arc is fixed-point free.  Here we lift `T` to the angle: there is an order
isomorphism `σ : ℝ ≃o ℝ` of the line, commuting with translation by `2π`, fixing `0` and `π`,
with `T (P θ) = P (σ θ)` and `σ θ ≠ θ` for `θ ∈ (0,π) ∪ (π,2π)`.

The definition of `σ` is the "unique lift with fundamental domain `[θ - π, θ + π)`": `σ θ` is
the unique `ψ ∈ [θ - π, θ + π)` with `P ψ = T (P θ)`.  Its continuity is proved by identifying
it (on `(-π, π)`, resp. on `(0, π)` and `(π, 2π)`) with the continuous function
`curveAngle θ = arccos (re w / ‖w‖)`, `w = T (P θ) - O₁`, applied with the appropriate
multiples of `2π`.
-/

namespace Work.EQ

open Complex

/-! ## The curve point and the auxiliary angle function. -/

/-- The point of the normalised equichordal curve at `O₁`-angle `θ`. -/
noncomputable def curvePt (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) : ℂ := polarPt (-(a/2)) (ρ₁ θ) θ

/-- The auxiliary angle function `θ ↦ arccos (re w / ‖w‖)` where `w = eqT a P θ - O₁`. -/
noncomputable def curveAngle (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.arccos ((eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
    ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖)

lemma curveAngle_def (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) :
    curveAngle a ρ₁ θ = Real.arccos ((eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
      ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖) := rfl

/-! ## Real-analysis helpers. -/

/-- If `t ∈ [-π, 2π)` and `sin t > 0` then `t ∈ (0, π)`. -/
lemma sin_pos_mem_Ioo {t : ℝ} (h1 : -Real.pi ≤ t) (h2 : t < 2 * Real.pi)
    (hs : 0 < Real.sin t) : 0 < t ∧ t < Real.pi := by
  constructor
  · rcases lt_or_eq_of_le h1 with h | h
    · rcases lt_or_ge 0 t with h' | h'
      · exact h'
      · rcases lt_or_eq_of_le h' with h'' | h''
        · exact absurd hs (not_lt.mpr (le_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt h'' h)))
        · rw [h''] at hs; rw [Real.sin_zero] at hs; exact absurd hs (lt_irrefl 0)
    · rw [← h] at hs
      have hz : Real.sin (-Real.pi) = 0 := by rw [Real.sin_neg, Real.sin_pi, neg_zero]
      rw [hz] at hs
      exact absurd hs (lt_irrefl 0)
  · rcases lt_or_ge t Real.pi with h | h
    · exact h
    · have hsp := Real.sin_sub_pi t
      have hs2 : Real.sin (t - Real.pi) < 0 := by linarith
      have h5 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ t - Real.pi)
        (by linarith : t - Real.pi ≤ Real.pi)
      linarith

/-- If `t ∈ (0, 3π)` and `sin t < 0` then `t ∈ (π, 2π)`. -/
lemma sin_neg_mem_Ioo {t : ℝ} (h1 : 0 < t) (h2 : t < 3 * Real.pi)
    (hs : Real.sin t < 0) : Real.pi < t ∧ t < 2 * Real.pi := by
  have h1' : -Real.pi ≤ t - Real.pi := by linarith [Real.pi_pos]
  have h2' : t - Real.pi < 2 * Real.pi := by linarith
  have hs' : 0 < Real.sin (t - Real.pi) := by
    have hsp := Real.sin_sub_pi t
    linarith
  have := sin_pos_mem_Ioo h1' h2' hs'
  constructor <;> linarith

/-! ## Basic properties of the parametrisation. -/

/-- Periodicity of the parametrisation in integer multiples of `2π`. -/
lemma curvePt_int_period {a : ℝ} {ρ₁ : ℝ → ℝ} (hper : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ)
    (θ : ℝ) (k : ℤ) :
    curvePt a ρ₁ (θ + (k : ℝ) * (2 * Real.pi)) = curvePt a ρ₁ θ := by
  have hp : Function.Periodic ρ₁ (2 * Real.pi) := hper
  have hρ : ρ₁ (θ + (k : ℝ) * (2 * Real.pi)) = ρ₁ θ := (hp.int_mul k) θ
  have hexp : Complex.exp ((((θ + (k : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    have h1 : ((((θ + (k : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I)
        = (θ : ℂ) * Complex.I + ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [curvePt, polarPt, hρ, hexp]

/-- Injectivity of the parametrisation modulo `2π`. -/
lemma curvePt_inj_mod {a : ℝ} {ρ₁ : ℝ → ℝ} {hpos : ∀ θ, 0 < ρ₁ θ} {θ θ' : ℝ}
    (h : curvePt a ρ₁ θ = curvePt a ρ₁ θ') : ∃ k : ℤ, θ' = θ + k * (2 * Real.pi) :=
  nec_polarPt_inj_mod_two_pi hpos h

lemma curvePt_add_two_pi {a : ℝ} {ρ₁ : ℝ → ℝ}
    (hper : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ) (θ : ℝ) :
    curvePt a ρ₁ (θ + 2 * Real.pi) = curvePt a ρ₁ θ := by
  have h := curvePt_int_period (a := a) (ρ₁ := ρ₁) hper θ 1
  simpa using h

section Main

variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂)

include ha0 ha1 hC

/-- **The lift of the angle map**: the unique `ψ ∈ [θ - π, θ + π)` with `P ψ = T (P θ)`. -/
lemma existsUnique_liftAngle (θ : ℝ) :
    ∃! ψ : ℝ, curvePt a ρ₁ ψ = eqT a (curvePt a ρ₁ θ) ∧
      θ - Real.pi ≤ ψ ∧ ψ < θ + Real.pi := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ, curvePt a ρ₁ ψ = eqT a (curvePt a ρ₁ θ) :=
    hc16 (Set.mem_range_self θ)
  set n : ℤ := ⌈(((θ - Real.pi) - ψ₁) / (2 * Real.pi))⌉ with hn
  have hnle : (((θ - Real.pi) - ψ₁) / (2 * Real.pi)) ≤ (n : ℝ) := by
    rw [hn]; exact Int.le_ceil _
  have hnlt : (n : ℝ) < (((θ - Real.pi) - ψ₁) / (2 * Real.pi)) + 1 := by
    rw [hn]; exact Int.ceil_lt_add_one _
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdiv : (((θ - Real.pi) - ψ₁) / (2 * Real.pi)) * (2 * Real.pi) = (θ - Real.pi) - ψ₁ := by
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)]
  have hwlo : θ - Real.pi ≤ ψ₁ + (n : ℝ) * (2 * Real.pi) := by
    have h := mul_le_mul_of_nonneg_right hnle (le_of_lt h2pi)
    rw [hdiv] at h
    linarith
  have hwup : ψ₁ + (n : ℝ) * (2 * Real.pi) < θ + Real.pi := by
    have h := mul_lt_mul_of_pos_right hnlt h2pi
    rw [add_mul, one_mul, hdiv] at h
    linarith
  refine ⟨ψ₁ + (n : ℝ) * (2 * Real.pi), ⟨?_, hwlo, hwup⟩, ?_⟩
  · rw [curvePt_int_period hc3 ψ₁ n]
    exact hψ₁
  · rintro ψ ⟨hψ, hlo, hhi⟩
    obtain ⟨k, hk⟩ := curvePt_inj_mod (a := a) (ρ₁ := ρ₁) (hpos := hpos₁) (hψ₁.trans hψ.symm)
    have hd : ((k : ℝ) - (n : ℝ)) * (2 * Real.pi) < 2 * Real.pi := by linarith
    have hd2 : -2 * Real.pi < ((k : ℝ) - (n : ℝ)) * (2 * Real.pi) := by linarith
    have hlt : ((k - n : ℤ) : ℝ) < 1 := by push_cast; nlinarith [Real.pi_pos]
    have hgt : (-1 : ℝ) < ((k - n : ℤ) : ℝ) := by push_cast; nlinarith [Real.pi_pos]
    have hlt' : (k - n : ℤ) < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < k - n := by exact_mod_cast hgt
    have hkn : k = n := by omega
    rw [hk, hkn]

noncomputable def liftAngle (θ : ℝ) : ℝ := Classical.choose (existsUnique_liftAngle ha0 ha1 hC θ)

lemma liftAngle_spec (θ : ℝ) :
    curvePt a ρ₁ (liftAngle ha0 ha1 hC θ) = eqT a (curvePt a ρ₁ θ) ∧
      θ - Real.pi ≤ liftAngle ha0 ha1 hC θ ∧ liftAngle ha0 ha1 hC θ < θ + Real.pi :=
  (Classical.choose_spec (existsUnique_liftAngle ha0 ha1 hC θ)).1

lemma liftAngle_unique (θ ψ : ℝ) (h1 : curvePt a ρ₁ ψ = eqT a (curvePt a ρ₁ θ))
    (h2 : θ - Real.pi ≤ ψ) (h3 : ψ < θ + Real.pi) : ψ = liftAngle ha0 ha1 hC θ :=
  (Classical.choose_spec (existsUnique_liftAngle ha0 ha1 hC θ)).2 ψ ⟨h1, h2, h3⟩


/-- `2π`-equivariance of the lifted angle map. -/
lemma liftAngle_add_two_pi (θ : ℝ) :
    liftAngle ha0 ha1 hC (θ + 2 * Real.pi) = liftAngle ha0 ha1 hC θ + 2 * Real.pi := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  refine (liftAngle_unique ha0 ha1 hC (θ + 2 * Real.pi)
    (liftAngle ha0 ha1 hC θ + 2 * Real.pi) ?_ ?_ ?_).symm
  · rw [curvePt_add_two_pi hc3, (liftAngle_spec ha0 ha1 hC θ).1, curvePt_add_two_pi hc3]
  · linarith [(liftAngle_spec ha0 ha1 hC θ).2.1]
  · linarith [(liftAngle_spec ha0 ha1 hC θ).2.2]

lemma liftAngle_sub_two_pi (θ : ℝ) :
    liftAngle ha0 ha1 hC (θ - 2 * Real.pi) = liftAngle ha0 ha1 hC θ - 2 * Real.pi := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hper : curvePt a ρ₁ (θ - 2 * Real.pi) = curvePt a ρ₁ θ := by
    have h := curvePt_int_period (a := a) (ρ₁ := ρ₁) hc3 θ (-1)
    have h2 : θ + ((-1 : ℤ) : ℝ) * (2 * Real.pi) = θ - 2 * Real.pi := by push_cast; ring
    rw [h2] at h
    exact h
  have hper2 : liftAngle ha0 ha1 hC θ - 2 * Real.pi
      = liftAngle ha0 ha1 hC θ + ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  refine (liftAngle_unique ha0 ha1 hC (θ - 2 * Real.pi)
    (liftAngle ha0 ha1 hC θ - 2 * Real.pi) ?_ ?_ ?_).symm
  · rw [hper2,
        curvePt_int_period (a := a) (ρ₁ := ρ₁) hc3 (liftAngle ha0 ha1 hC θ) (-1),
        (liftAngle_spec ha0 ha1 hC θ).1, hper]
  · linarith [(liftAngle_spec ha0 ha1 hC θ).2.1]
  · linarith [(liftAngle_spec ha0 ha1 hC θ).2.2]

/-- The lift commutes with translation by integer multiples of `2π`. -/
lemma liftAngle_per_int (θ : ℝ) (k : ℤ) :
    liftAngle ha0 ha1 hC (θ + (k : ℝ) * (2 * Real.pi))
      = liftAngle ha0 ha1 hC θ + (k : ℝ) * (2 * Real.pi) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      push_cast at ih
      have hcast : (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have harg : θ + ((n : ℝ) + 1) * (2 * Real.pi)
          = (θ + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by ring
      rw [harg, liftAngle_add_two_pi, ih]
      ring
  | pred n ih =>
      push_cast at ih
      have hcast : ((-(n : ℤ) - 1 : ℤ) : ℝ) = -(n : ℝ) - 1 := by push_cast; ring
      rw [hcast]
      have harg : θ + (-(n : ℝ) - 1) * (2 * Real.pi)
          = (θ + (-(n : ℝ)) * (2 * Real.pi)) - 2 * Real.pi := by ring
      rw [harg, liftAngle_sub_two_pi, ih]
      ring

lemma liftAngle_zero : liftAngle ha0 ha1 hC 0 = 0 := by
  have h1 : curvePt a ρ₁ 0 = eqT a (curvePt a ρ₁ 0) := by
    simp only [curvePt]
    exact (eqT_axis_fixed ha0 ha1 hC).1.symm
  exact (liftAngle_unique ha0 ha1 hC 0 0 h1 (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])).symm

lemma liftAngle_pi : liftAngle ha0 ha1 hC Real.pi = Real.pi := by
  have h1 : curvePt a ρ₁ Real.pi = eqT a (curvePt a ρ₁ Real.pi) := by
    simp only [curvePt]
    exact (eqT_axis_fixed ha0 ha1 hC).2.symm
  exact (liftAngle_unique ha0 ha1 hC Real.pi Real.pi h1 (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])).symm

lemma liftAngle_ne_self {θ : ℝ}
    (h : (0 < θ ∧ θ < Real.pi) ∨ (Real.pi < θ ∧ θ < 2 * Real.pi)) :
    liftAngle ha0 ha1 hC θ ≠ θ := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  intro hfix
  have hspec := liftAngle_spec ha0 ha1 hC θ
  have him : (curvePt a ρ₁ θ).im = 0 := by
    refine hc18 (curvePt a ρ₁ θ) (Set.mem_range_self θ) ?_
    show eqT a (curvePt a ρ₁ θ) = curvePt a ρ₁ θ
    rw [← hspec.1, hfix]
  have him2 : (curvePt a ρ₁ θ).im = ρ₁ θ * Real.sin θ := by
    simp only [curvePt, nec_polarPt_im]
  have hsin : Real.sin θ = 0 := by
    have h2 : ρ₁ θ * Real.sin θ = 0 := by rw [← him2, him]
    exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt (hpos₁ θ))
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd hsin (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  · have hneg : Real.sin θ < 0 := by
      have hsp := Real.sin_sub_pi θ
      have := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ - Real.pi)
        (by linarith : θ - Real.pi < Real.pi)
      linarith
    exact absurd hsin (ne_of_lt hneg)

lemma liftAngle_injective : Function.Injective (fun θ : ℝ => liftAngle ha0 ha1 hC θ) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  intro θ θ' h
  have hspec := liftAngle_spec ha0 ha1 hC θ
  have hspec' := liftAngle_spec ha0 ha1 hC θ'
  change liftAngle ha0 ha1 hC θ = liftAngle ha0 ha1 hC θ' at h
  have heq : curvePt a ρ₁ θ = curvePt a ρ₁ θ' :=
    hc17 (Set.mem_range_self θ) (Set.mem_range_self θ') (by
      show eqT a (curvePt a ρ₁ θ) = eqT a (curvePt a ρ₁ θ')
      rw [← hspec.1, ← hspec'.1, h])
  obtain ⟨k, hk⟩ := curvePt_inj_mod (a := a) (ρ₁ := ρ₁) (hpos := hpos₁) heq
  rw [hk] at h
  rw [liftAngle_per_int ha0 ha1 hC θ k] at h
  have hk0 : k = 0 := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    have hzero : (k : ℝ) * (2 * Real.pi) = 0 := by linarith
    have : (k : ℝ) = 0 := (mul_eq_zero.mp hzero).resolve_right h2pi
    exact_mod_cast this
  rw [hk0] at hk
  simpa using hk.symm


/-! ## Identification of the lift with the arccos angle. -/

omit ha0 ha1 hC in
lemma curveAngle_eq (θ : ℝ) :
    curveAngle a ρ₁ θ = Real.arccos ((eqT a (curvePt a ρ₁ θ) - O1_sym a).re /
      ‖eqT a (curvePt a ρ₁ θ) - O1_sym a‖) := rfl

omit ha0 ha1 hC in
lemma curvePt_zero {a : ℝ} {ρ₁ : ℝ → ℝ} : curvePt a ρ₁ 0 = ((-(a/2) + ρ₁ 0 : ℝ) : ℂ) := by
  simp only [curvePt]
  exact nec_polarPt_zero (-(a/2)) (ρ₁ 0)

omit ha0 ha1 hC in
lemma curvePt_pi {a : ℝ} {ρ₁ : ℝ → ℝ} : curvePt a ρ₁ Real.pi = ((-(a/2) - ρ₁ Real.pi : ℝ) : ℂ) := by
  simp only [curvePt]
  exact nec_polarPt_pi (-(a/2)) (ρ₁ Real.pi)

omit ha0 ha1 hC in
lemma curveAngle_add_two_pi {a : ℝ} {ρ₁ : ℝ → ℝ} {hper : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ} (θ : ℝ) :
    curveAngle a ρ₁ (θ + 2 * Real.pi) = curveAngle a ρ₁ θ := by
  rw [curveAngle_eq, curveAngle_eq, curvePt_add_two_pi hper θ]

omit ha0 ha1 hC in
lemma curveAngle_per_int {a : ℝ} {ρ₁ : ℝ → ℝ} {hper : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ} (x : ℝ) (m : ℤ) :
    curveAngle a ρ₁ (x + (m : ℝ) * (2 * Real.pi)) = curveAngle a ρ₁ x := by
  rw [curveAngle_eq, curveAngle_eq, curvePt_int_period hper x m]

lemma continuous_curveAngle : Continuous (fun θ : ℝ => curveAngle a ρ₁ θ) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hcontOn : ContinuousOn (fun θ : ℝ => curveAngle a ρ₁ θ)
      (Set.Icc (-Real.pi) (2 * Real.pi)) := by
    simpa only [curveAngle_def] using eqT_continuousOn_D ha0 ha1 hC
  rw [continuous_iff_continuousAt]
  intro x
  set m : ℤ := ⌈(x - Real.pi) / (2 * Real.pi)⌉ with hm
  set y : ℝ := x - (m : ℝ) * (2 * Real.pi) with hy
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdiv : ((x - Real.pi) / (2 * Real.pi)) * (2 * Real.pi) = x - Real.pi :=
    div_mul_cancel₀ _ (ne_of_gt h2pi)
  have hb1 : -Real.pi < y := by
    have h : (m : ℝ) < (x - Real.pi) / (2 * Real.pi) + 1 := by
      rw [hm]; exact Int.ceil_lt_add_one _
    have hmul := mul_lt_mul_of_pos_right h h2pi
    rw [add_mul, one_mul, hdiv] at hmul
    rw [hy]
    linarith
  have hb2 : y ≤ Real.pi := by
    have h : (x - Real.pi) / (2 * Real.pi) ≤ (m : ℝ) := by
      rw [hm]; exact Int.le_ceil _
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt h2pi)
    rw [hdiv] at hmul
    rw [hy]
    linarith
  have hmem : Set.Icc (-Real.pi) (2 * Real.pi) ∈ nhds y :=
    Icc_mem_nhds hb1 (by linarith [Real.pi_pos])
  have hycont : ContinuousAt (fun t : ℝ => curveAngle a ρ₁ t) y := hcontOn.continuousAt hmem
  have hbase' := hycont
  rw [hy] at hbase'
  have hcomp : ContinuousAt (fun t : ℝ => curveAngle a ρ₁ (t - (m : ℝ) * (2 * Real.pi))) x :=
    @ContinuousAt.comp ℝ ℝ ℝ _ _ _ (fun t : ℝ => t - (m : ℝ) * (2 * Real.pi)) x
      (fun t : ℝ => curveAngle a ρ₁ t) hbase'
      (continuousAt_id.sub continuousAt_const)
  have hfun : (fun t : ℝ => curveAngle a ρ₁ (t - (m : ℝ) * (2 * Real.pi)))
      = (fun t : ℝ => curveAngle a ρ₁ t) := by
    funext t
    have h := curveAngle_per_int (a := a) (ρ₁ := ρ₁) (hper := hc3) (t - (m : ℝ) * (2 * Real.pi)) m
    have harg : t - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = t := by ring
    rw [harg] at h
    exact h.symm
  rwa [hfun] at hcomp

lemma liftAngle_eq_curveAngle_of_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    liftAngle ha0 ha1 hC θ = curveAngle a ρ₁ θ := by
  have him : 0 < (eqT a (curvePt a ρ₁ θ)).im := by
    simpa only [curvePt] using (eqT_im_arc ha0 ha1 hC).1 θ h0 hπ
  have hspec := liftAngle_spec ha0 ha1 hC θ
  have him3 : 0 < ρ₁ (liftAngle ha0 ha1 hC θ) * Real.sin (liftAngle ha0 ha1 hC θ) := by
    have h2 : 0 < (curvePt a ρ₁ (liftAngle ha0 ha1 hC θ)).im := by rw [hspec.1]; exact him
    simpa only [curvePt, nec_polarPt_im] using h2
  have hsin : 0 < Real.sin (liftAngle ha0 ha1 hC θ) :=
    (mul_pos_iff_of_pos_left (hC.2.2.1 _)).mp him3
  obtain ⟨hpos, hlt⟩ := sin_pos_mem_Ioo (by linarith [hspec.2.1, h0])
    (by linarith [hspec.2.2, hπ]) hsin
  rw [curveAngle_eq]
  exact eqT_angle_upper ha0 ha1 hC hpos hlt hspec.1

lemma liftAngle_eq_of_pi_lt {θ : ℝ} (h0 : Real.pi < θ) (hπ : θ < 2 * Real.pi) :
    liftAngle ha0 ha1 hC θ = 2 * Real.pi - curveAngle a ρ₁ θ := by
  have him : (eqT a (curvePt a ρ₁ θ)).im < 0 := by
    simpa only [curvePt] using (eqT_im_arc ha0 ha1 hC).2 θ h0 hπ
  have hspec := liftAngle_spec ha0 ha1 hC θ
  have him3 : ρ₁ (liftAngle ha0 ha1 hC θ) * Real.sin (liftAngle ha0 ha1 hC θ) < 0 := by
    have h2 : (curvePt a ρ₁ (liftAngle ha0 ha1 hC θ)).im < 0 := by rw [hspec.1]; exact him
    simpa only [curvePt, nec_polarPt_im] using h2
  have hsin : Real.sin (liftAngle ha0 ha1 hC θ) < 0 := by
    rcases mul_neg_iff.mp him3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.mpr (le_of_lt (hC.2.2.1 _)))
  obtain ⟨hl, hu⟩ := sin_neg_mem_Ioo (by linarith [hspec.2.1, h0])
    (by linarith [hspec.2.2, hπ]) hsin
  rw [curveAngle_eq]
  exact eqT_angle_lower ha0 ha1 hC hl hu hspec.1

lemma liftAngle_eq_neg_of_neg {θ : ℝ} (h0 : -Real.pi < θ) (hπ : θ < 0) :
    liftAngle ha0 ha1 hC θ = - curveAngle a ρ₁ θ := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hper := liftAngle_add_two_pi ha0 ha1 hC θ
  have hlow := liftAngle_eq_of_pi_lt (θ := θ + 2 * Real.pi) ha0 ha1 hC (by linarith) (by linarith)
  have hA := curveAngle_add_two_pi (a := a) (ρ₁ := ρ₁) (hper := hc3) θ
  rw [hper, hA] at hlow
  linarith

lemma curveAngle_zero : curveAngle a ρ₁ 0 = 0 := by
  have h1 : eqT a (curvePt a ρ₁ 0) = curvePt a ρ₁ 0 := by
    simp only [curvePt]
    exact (eqT_axis_fixed ha0 ha1 hC).1
  have h2 : curvePt a ρ₁ 0 - O1_sym a = ((ρ₁ 0 : ℝ) : ℂ) := by
    simp only [curvePt_zero, O1_sym]
    push_cast
    ring
  rw [curveAngle_eq, h1, h2]
  rw [Complex.ofReal_re,
    show ‖((ρ₁ 0 : ℝ) : ℂ)‖ = |ρ₁ 0| from RCLike.norm_ofReal (ρ₁ 0),
    abs_of_pos (hC.2.2.1 0), div_self (ne_of_gt (hC.2.2.1 0))]
  exact Real.arccos_one

lemma curveAngle_pi : curveAngle a ρ₁ Real.pi = Real.pi := by
  have h1 : eqT a (curvePt a ρ₁ Real.pi) = curvePt a ρ₁ Real.pi := by
    simp only [curvePt]
    exact (eqT_axis_fixed ha0 ha1 hC).2
  have h2 : curvePt a ρ₁ Real.pi - O1_sym a = ((-(ρ₁ Real.pi) : ℝ) : ℂ) := by
    simp only [curvePt_pi, O1_sym]
    push_cast
    ring
  rw [curveAngle_eq, h1, h2]
  have hnorm : ‖((-(ρ₁ Real.pi) : ℝ) : ℂ)‖ = ρ₁ Real.pi := by
    rw [show ‖((-(ρ₁ Real.pi) : ℝ) : ℂ)‖ = |-(ρ₁ Real.pi)| from RCLike.norm_ofReal (-(ρ₁ Real.pi)),
      abs_of_neg (by linarith [hC.2.2.1 Real.pi]), neg_neg]
  rw [Complex.ofReal_re, hnorm,
    show -(ρ₁ Real.pi) / ρ₁ Real.pi = -1 by
      rw [neg_div, div_self (ne_of_gt (hC.2.2.1 Real.pi))]]
  exact Real.arccos_neg_one

/-! ## Continuity of the lift. -/

lemma continuousAt_liftAngle_zero : ContinuousAt (fun θ : ℝ => liftAngle ha0 ha1 hC θ) 0 := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · have hD : ContinuousWithinAt (fun θ : ℝ => -curveAngle a ρ₁ θ) (Set.Iio 0) 0 :=
      ((continuous_curveAngle ha0 ha1 hC).neg).continuousAt.continuousWithinAt
    refine hD.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show (-Real.pi:ℝ) < 0 by linarith [Real.pi_pos])] with θ hθ
      exact liftAngle_eq_neg_of_neg ha0 ha1 hC hθ.1 hθ.2
    · rw [liftAngle_zero ha0 ha1 hC, curveAngle_zero ha0 ha1 hC]; ring
  · have hD : ContinuousWithinAt (curveAngle a ρ₁) (Set.Ioi 0) 0 :=
      (continuous_curveAngle ha0 ha1 hC).continuousAt.continuousWithinAt
    refine hD.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi by positivity)] with θ hθ
      exact liftAngle_eq_curveAngle_of_pos ha0 ha1 hC hθ.1 hθ.2
    · rw [liftAngle_zero ha0 ha1 hC, curveAngle_zero ha0 ha1 hC]

lemma continuousAt_liftAngle_pi : ContinuousAt (fun θ : ℝ => liftAngle ha0 ha1 hC θ) Real.pi := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · have hD : ContinuousWithinAt (curveAngle a ρ₁) (Set.Iio Real.pi) Real.pi :=
      (continuous_curveAngle ha0 ha1 hC).continuousAt.continuousWithinAt
    refine hD.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < Real.pi by positivity)] with θ hθ
      exact liftAngle_eq_curveAngle_of_pos ha0 ha1 hC hθ.1 hθ.2
    · rw [liftAngle_pi ha0 ha1 hC, curveAngle_pi ha0 ha1 hC]
  · have hD : ContinuousWithinAt (fun θ : ℝ => 2 * Real.pi - curveAngle a ρ₁ θ)
        (Set.Ioi Real.pi) Real.pi :=
      (continuous_const.sub (continuous_curveAngle ha0 ha1 hC)).continuousAt.continuousWithinAt
    refine hD.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show Real.pi < 2 * Real.pi by linarith [Real.pi_pos])]
        with θ hθ
      exact liftAngle_eq_of_pi_lt ha0 ha1 hC hθ.1 hθ.2
    · rw [liftAngle_pi ha0 ha1 hC, curveAngle_pi ha0 ha1 hC]; ring

lemma continuous_liftAngle : Continuous (fun θ : ℝ => liftAngle ha0 ha1 hC θ) := by
  rw [continuous_iff_continuousAt]
  intro θ
  set m : ℤ := ⌊θ / (2 * Real.pi)⌋ with hm
  set θ₁ : ℝ := θ - (m : ℝ) * (2 * Real.pi) with hθ₁
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdiv : (θ / (2 * Real.pi)) * (2 * Real.pi) = θ :=
    div_mul_cancel₀ _ (ne_of_gt h2pi)
  have hb1 : 0 ≤ θ₁ := by
    have h : (m : ℝ) ≤ θ / (2 * Real.pi) := by rw [hm]; exact Int.floor_le _
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt h2pi)
    rw [hdiv] at hmul
    rw [hθ₁]
    linarith
  have hb2 : θ₁ < 2 * Real.pi := by
    have h : θ / (2 * Real.pi) < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_right h h2pi
    rw [add_mul, one_mul, hdiv] at hmul
    rw [hθ₁]
    linarith
  have hbase : ContinuousAt (fun x : ℝ => liftAngle ha0 ha1 hC x) θ₁ := by
    rcases lt_or_ge θ₁ Real.pi with h | h
    · rcases eq_or_lt_of_le hb1 with h0 | h0
      · rw [← h0]
        exact continuousAt_liftAngle_zero ha0 ha1 hC
      · have hcont : ContinuousOn (fun x : ℝ => liftAngle ha0 ha1 hC x) (Set.Ioo 0 Real.pi) :=
          (continuous_curveAngle ha0 ha1 hC).continuousOn.congr
            (fun x hx => liftAngle_eq_curveAngle_of_pos ha0 ha1 hC hx.1 hx.2)
        exact hcont.continuousAt (Ioo_mem_nhds h0 h)
    · rcases eq_or_lt_of_le h with hπ | hπ
      · rw [← hπ]
        change ContinuousAt (liftAngle ha0 ha1 hC) Real.pi
        exact continuousAt_liftAngle_pi ha0 ha1 hC
      · have hcont : ContinuousOn (fun x : ℝ => liftAngle ha0 ha1 hC x)
            (Set.Ioo Real.pi (2 * Real.pi)) :=
          (continuous_const.sub (continuous_curveAngle ha0 ha1 hC)).continuousOn.congr
            (fun x hx => liftAngle_eq_of_pi_lt ha0 ha1 hC hx.1 hx.2)
        exact hcont.continuousAt (Ioo_mem_nhds hπ hb2)
  have hstep : ∀ x : ℝ, liftAngle ha0 ha1 hC (x - (m : ℝ) * (2 * Real.pi))
      = liftAngle ha0 ha1 hC x - (m : ℝ) * (2 * Real.pi) := by
    intro x
    have h := liftAngle_per_int ha0 ha1 hC (x - (m : ℝ) * (2 * Real.pi)) m
    have harg : x - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = x := by ring
    rw [harg] at h
    linarith
  have hbase' := hbase
  rw [hθ₁] at hbase'
  have hcomp : ContinuousAt (fun x : ℝ => liftAngle ha0 ha1 hC (x - (m : ℝ) * (2 * Real.pi))) θ :=
    @ContinuousAt.comp ℝ ℝ ℝ _ _ _ (fun x : ℝ => x - (m : ℝ) * (2 * Real.pi)) θ
      (fun y : ℝ => liftAngle ha0 ha1 hC y) hbase'
      (continuousAt_id.sub continuousAt_const)
  have hfun : (fun x : ℝ => liftAngle ha0 ha1 hC (x - (m : ℝ) * (2 * Real.pi)))
      = (fun x : ℝ => liftAngle ha0 ha1 hC x - (m : ℝ) * (2 * Real.pi)) := funext hstep
  rw [hfun] at hcomp
  have h1 : ContinuousAt (fun x : ℝ => (liftAngle ha0 ha1 hC x - (m : ℝ) * (2 * Real.pi))
      + (m : ℝ) * (2 * Real.pi)) θ := hcomp.add continuousAt_const
  have h2 : (fun x : ℝ => (liftAngle ha0 ha1 hC x - (m : ℝ) * (2 * Real.pi))
      + (m : ℝ) * (2 * Real.pi)) = (fun x : ℝ => liftAngle ha0 ha1 hC x) := by
    funext x; ring
  rwa [h2] at h1

end Main

theorem eqT_lift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    ∃ σ : ℝ ≃o ℝ,
      (∀ θ, σ (θ + 2 * Real.pi) = σ θ + 2 * Real.pi) ∧
      (∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (σ θ)) (σ θ)) ∧
      σ 0 = 0 ∧ σ Real.pi = Real.pi ∧
      (∀ θ, 0 < θ → θ < Real.pi → σ θ ≠ θ) ∧
      (∀ θ, Real.pi < θ → θ < 2 * Real.pi → σ θ ≠ θ) := by
  have hinj : Function.Injective (fun θ : ℝ => liftAngle ha0 ha1 hC θ) :=
    liftAngle_injective ha0 ha1 hC
  have hcont : Continuous (fun θ : ℝ => liftAngle ha0 ha1 hC θ) :=
    continuous_liftAngle ha0 ha1 hC
  have hmono : StrictMono (fun θ : ℝ => liftAngle ha0 ha1 hC θ) := by
    rcases hcont.strictMono_of_inj hinj with h | h
    · exact h
    · exfalso
      have hh := h (show (0 : ℝ) < Real.pi by positivity)
      change liftAngle ha0 ha1 hC Real.pi < liftAngle ha0 ha1 hC 0 at hh
      rw [liftAngle_zero ha0 ha1 hC, liftAngle_pi ha0 ha1 hC] at hh
      linarith [Real.pi_pos]
  have hsurj : Function.Surjective (fun θ : ℝ => liftAngle ha0 ha1 hC θ) := by
    intro y
    set k : ℤ := ⌊y / (2 * Real.pi)⌋ with hk
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hdiv : y / (2 * Real.pi) * (2 * Real.pi) = y := div_mul_cancel₀ _ (ne_of_gt h2pi)
    have hlo : (k : ℝ) * (2 * Real.pi) ≤ y := by
      have h : (k : ℝ) ≤ y / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
      have hh := mul_le_mul_of_nonneg_right h (le_of_lt h2pi)
      rw [hdiv] at hh
      exact hh
    have hhi : y ≤ ((k : ℝ) + 1) * (2 * Real.pi) := by
      have h : y / (2 * Real.pi) < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
      have hh := mul_lt_mul_of_pos_right h h2pi
      rw [add_mul, one_mul, hdiv] at hh
      linarith
    have hk2 : liftAngle ha0 ha1 hC ((k : ℝ) * (2 * Real.pi)) = (k : ℝ) * (2 * Real.pi) := by
      rw [show (k : ℝ) * (2 * Real.pi) = 0 + (k : ℝ) * (2 * Real.pi) by ring,
        liftAngle_per_int ha0 ha1 hC 0 k, liftAngle_zero ha0 ha1 hC, zero_add]
    have hk3 : liftAngle ha0 ha1 hC (((k : ℝ) + 1) * (2 * Real.pi)) = ((k : ℝ) + 1) * (2 * Real.pi) := by
      have hcast : (((k + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [← hcast, show (((k + 1 : ℤ)) : ℝ) * (2 * Real.pi) = 0 + (((k + 1 : ℤ)) : ℝ) * (2 * Real.pi) by ring,
        liftAngle_per_int ha0 ha1 hC 0 (k + 1), liftAngle_zero ha0 ha1 hC, zero_add, hcast]
    have hIcc : y ∈ Set.Icc (liftAngle ha0 ha1 hC ((k : ℝ) * (2 * Real.pi)))
        (liftAngle ha0 ha1 hC (((k : ℝ) + 1) * (2 * Real.pi))) := by
      rw [hk2, hk3]
      exact ⟨hlo, hhi⟩
    have hmem := intermediate_value_Icc (a := (k : ℝ) * (2 * Real.pi))
      (b := ((k : ℝ) + 1) * (2 * Real.pi)) (by linarith [h2pi]) hcont.continuousOn hIcc
    obtain ⟨θ, -, hθ⟩ := hmem
    exact ⟨θ, hθ⟩
  set σ : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective (fun θ : ℝ => liftAngle ha0 ha1 hC θ)
    hmono hsurj with hσ
  have hσcoe : ∀ θ : ℝ, σ θ = liftAngle ha0 ha1 hC θ := by
    intro θ
    rw [hσ]
    simp only [StrictMono.coe_orderIsoOfSurjective]
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    rw [hσcoe]
    exact liftAngle_add_two_pi ha0 ha1 hC θ
  · intro θ
    rw [hσcoe]
    simpa only [curvePt] using (liftAngle_spec ha0 ha1 hC θ).1.symm
  · rw [hσcoe]
    exact liftAngle_zero ha0 ha1 hC
  · rw [hσcoe]
    exact liftAngle_pi ha0 ha1 hC
  · intro θ h1 h2
    rw [hσcoe]
    exact liftAngle_ne_self ha0 ha1 hC (Or.inl ⟨h1, h2⟩)
  · intro θ h1 h2
    rw [hσcoe]
    exact liftAngle_ne_self ha0 ha1 hC (Or.inr ⟨h1, h2⟩)

end Work.EQ
