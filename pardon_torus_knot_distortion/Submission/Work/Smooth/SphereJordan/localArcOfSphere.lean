import Mathlib
import Submission.Work.Smooth.SphereJordan.sphereLocalArc

/-!
# A circle arc is the image of `(-1,1)` under an injective continuous map

`localArcOfSphere`: for `x ∈ Metric.sphere w ρ` (`0 < ρ`) and `0 < ε < 2ρ`, the arc
`Metric.sphere w ρ ∩ Metric.ball x ε` is the image of `(-1,1)` under a continuous injective map
`γ : ℝ → ℂ` with `γ 0 = x`.

The parametrisation is by the angle `g t = 2 * arctan (tan (δ/2) * t)`, where `δ > 0` is the angular
half-width of the arc given by `sphereLocalArc`; `g` is a strictly increasing homeomorphism
`ℝ → (-π, π)` with `g (±1) = ±δ`, so `t ↦ w + ρ e^{i(θ + g t)}` is injective (its argument has
diameter `< 2π`) and its restriction to `(-1,1)` has image exactly the arc.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

/-- The point of the circle `Metric.sphere w ρ` at angle `t`. -/
def circ (w : ℂ) (ρ t : ℝ) : ℂ := w + (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

theorem circ_expand (w : ℂ) (ρ t : ℝ) :
    circ w ρ t = w + (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := rfl

/-- **A circle arc is the trace of an injective continuous curve.** -/
theorem localArcOfSphere {w x : ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hxw : x ∈ Metric.sphere w ρ) (hε2 : ε < 2 * ρ) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧ γ 0 = x ∧
      γ '' Set.Ioo (-1 : ℝ) 1 = Metric.sphere w ρ ∩ Metric.ball x ε := by
  have hxw' : dist x w = ρ := Metric.mem_sphere.mp hxw
  obtain ⟨θ, hθ, δ, hδpos, himg⟩ := sphereLocalArc hρ hxw' hε hε2
  set s : ℝ := 2 * Real.arcsin (ε / (2 * ρ)) with hsdef
  have hslack : ε / (2 * ρ) < 1 := by
    rw [div_lt_one (by linarith)]
    exact hε2
  have hs1 : Real.arcsin (ε / (2 * ρ)) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hslack
  have hs0 : 0 < Real.arcsin (ε / (2 * ρ)) := Real.arcsin_pos.mpr (div_pos hε (by linarith))
  have hspos : 0 < s := by rw [hsdef]; linarith
  have hslt : s < Real.pi := by rw [hsdef]; linarith
  have hlt1 : ε / (2 * ρ) ≤ 1 := le_of_lt hslack
  have hge1 : -1 ≤ ε / (2 * ρ) := by
    have := div_pos hε (by linarith : (0:ℝ) < 2 * ρ)
    linarith
  have hsin : Real.sin (s / 2) = ε / (2 * ρ) := by
    have h2 : s / 2 = Real.arcsin (ε / (2 * ρ)) := by rw [hsdef]; ring
    rw [h2, Real.sin_arcsin hge1 hlt1]
  -- **δ ≤ s**: the point at angle `θ + s` is at distance exactly `ε` from `x`, so it is not in the
  -- arc (which is contained in the open ball).
  have hδle : δ ≤ s := by
    by_contra hcon
    rw [not_le] at hcon
    have hmem : circ w ρ (θ + s) ∈ Metric.sphere w ρ ∩ Metric.ball x ε := by
      rw [← himg]
      refine ⟨s, ⟨by linarith, hcon⟩, ?_⟩
      rfl
    have hdist : dist (circ w ρ (θ + s)) x = ε := by
      rw [circ_expand, dist_eq_norm, hθ]
      have h1 : (w + (ρ : ℂ) * Complex.exp (((θ + s : ℝ) : ℂ) * Complex.I))
          - (w + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
            * (Complex.exp ((s : ℂ) * Complex.I) - 1) := by
        rw [show (((θ + s : ℝ)) : ℂ) * Complex.I
            = (θ : ℂ) * Complex.I + (s : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
        ring
      rw [h1, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      have h2 : Complex.exp ((s : ℂ) * Complex.I) = Complex.exp (Complex.I * (s : ℂ)) := by
        rw [mul_comm]
      rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2), hsin]
      have hpos : 0 < ε / (2 * ρ) := div_pos hε (by linarith)
      rw [abs_of_pos hpos]
      field_simp
    have hball := hmem.2
    rw [Metric.mem_ball, hdist] at hball
    exact absurd hball (lt_irrefl ε)
  have hδlt : δ < Real.pi := lt_of_le_of_lt hδle hslt
  -- the reparametrisation
  set c : ℝ := Real.tan (δ / 2) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  set g : ℝ → ℝ := fun t => 2 * Real.arctan (c * t) with hgdef
  have hgcont : Continuous g := by rw [hgdef]; fun_prop
  have hgmono : StrictMono g := by
    rw [hgdef]
    have harctan : StrictMono Real.arctan := fun a b hab => (Real.arctan_lt_arctan_iff.mpr hab)
    have hlin : StrictMono fun t : ℝ => c * t := StrictMono.const_mul strictMono_id hcpos
    exact (harctan.comp hlin).const_mul (by norm_num : (0:ℝ) < 2)
  have hgc : Real.arctan c = δ / 2 := by
    rw [hcdef]
    exact Real.arctan_tan (by linarith) (by linarith)
  have hg_one : g 1 = δ := by
    rw [hgdef]; simp only [mul_one]; rw [hgc]; ring
  have hg_neg_one : g (-1) = -δ := by
    rw [hgdef]; simp only [mul_neg, mul_one, Real.arctan_neg]; rw [hgc]; ring
  have hg_zero : g 0 = 0 := by rw [hgdef]; simp
  have hgimg : g '' Set.Ioo (-1 : ℝ) 1 = Set.Ioo (-δ) δ := by
    have h := Continuous.image_Ioo_of_strictMono hgcont hgmono (a := (-1:ℝ)) (b := 1)
    rw [hg_neg_one, hg_one] at h
    exact h
  have hgbounds : ∀ t : ℝ, -Real.pi < g t ∧ g t < Real.pi := by
    intro t
    rw [hgdef]
    have h1 := Real.neg_pi_div_two_lt_arctan (c * t)
    have h2 := Real.arctan_lt_pi_div_two (c * t)
    constructor <;> linarith
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  refine ⟨fun t => circ w ρ (θ + g t), ?_, ?_, ?_, ?_⟩
  · rw [show (fun t => circ w ρ (θ + g t)) = fun t => w + (ρ : ℂ)
        * Complex.exp ((((θ + g t : ℝ)) : ℂ) * Complex.I) from rfl]
    fun_prop
  · intro t₁ t₂ ht
    have h2 : w + (ρ : ℂ) * Complex.exp (((θ + g t₁ : ℝ) : ℂ) * Complex.I)
        = w + (ρ : ℂ) * Complex.exp (((θ + g t₂ : ℝ) : ℂ) * Complex.I) := ht
    have h1 : Complex.exp (((θ + g t₁ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((θ + g t₂ : ℝ) : ℂ) * Complex.I) :=
      mul_left_cancel₀ hρne (add_left_cancel h2)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
    have h5 : (g t₁ - g t₂ : ℝ) = (n : ℝ) * (2 * Real.pi) := by
      have h4 : (((θ + g t₁ : ℝ)) : ℂ) * Complex.I
          - (((θ + g t₂ : ℝ)) : ℂ) * Complex.I
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by rw [hn]; ring
      have h4' : ((((θ + g t₁ : ℝ)) : ℂ) - (((θ + g t₂ : ℝ)) : ℂ)) * Complex.I
          = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        have e1 : ((((θ + g t₁ : ℝ)) : ℂ) - (((θ + g t₂ : ℝ)) : ℂ)) * Complex.I
            = (((θ + g t₁ : ℝ)) : ℂ) * Complex.I
              - (((θ + g t₂ : ℝ)) : ℂ) * Complex.I := by ring
        rw [e1, h4]
        ring
      have h4'' : (((θ + g t₁ : ℝ)) : ℂ) - (((θ + g t₂ : ℝ)) : ℂ)
          = (n : ℂ) * (2 * (Real.pi : ℂ)) := mul_right_cancel₀ Complex.I_ne_zero h4'
      have h7 : (((g t₁ - g t₂ : ℝ)) : ℂ) = ((((n : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) := by
        calc (((g t₁ - g t₂ : ℝ)) : ℂ)
            = (((θ + g t₁ : ℝ)) : ℂ) - (((θ + g t₂ : ℝ)) : ℂ) := by push_cast; ring
          _ = (n : ℂ) * (2 * (Real.pi : ℂ)) := h4''
          _ = ((((n : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) := by push_cast; ring
      exact Complex.ofReal_inj.mp h7
    have h6 : |g t₁ - g t₂| < 2 * Real.pi := by
      have h7 := hgbounds t₁
      have h8 := hgbounds t₂
      rw [abs_lt]
      constructor <;> linarith [h7.1, h7.2, h8.1, h8.2]
    rw [h5, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h6
    have h9 : |((n : ℝ))| < 1 := by nlinarith [Real.pi_pos]
    have hlt : n < 1 := by
      have := (abs_lt.mp h9).2
      exact_mod_cast this
    have hgt : (-1 : ℤ) < n := by
      have := (abs_lt.mp h9).1
      exact_mod_cast this
    have hn0 : n = 0 := by omega
    rw [hn0] at h5
    simp only [Int.cast_zero, zero_mul] at h5
    exact hgmono.injective (sub_eq_zero.mp h5)
  · change circ w ρ (θ + g 0) = x
    rw [hg_zero, add_zero]
    exact hθ.symm
  · have hcomp : (fun t => circ w ρ (θ + g t))
        = (fun u : ℝ => w + (ρ : ℂ) * Complex.exp (((θ + u : ℝ) : ℂ) * Complex.I)) ∘ g := rfl
    rw [hcomp, Set.image_comp, hgimg, himg]

end

end Work.Smooth.SphereJordan
