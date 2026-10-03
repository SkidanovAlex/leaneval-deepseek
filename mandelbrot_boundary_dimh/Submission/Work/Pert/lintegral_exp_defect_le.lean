import Mathlib
import Submission.Work.Pert.lintegral_comp_mul_add
import Submission.Work.Pert.lintegral_gate_density

namespace Work.Pert

/-!
## Bound on the `L¹`-mass of the "exp defect" weight

For `α : ℂ` with `0 < α.re`, a real `ξ > 0` and a vertical line `z = x + y·i` which keeps
distance at least `ξ/2` from the lattice `α⁻¹ ℤ`, we bound the Lebesgue integral of
`‖e^{-2πi α z}‖ / ‖1 - e^{-2πi α z}‖²` by `1/(α.re · ‖α‖ · ξ)`.

Writing `W = -(2πi α z)`, `T = α.re·y + α.im·x = Re W/(2π)` and `P = α.re·x - α.im·y = -Im W/(2π)`,
the exact identities are
* `‖e^W‖ = e^{2πT}`,
* `‖1 - e^W‖² = (1 - e^{2πT})² + 4 e^{2πT} sin²(πP) = 4 e^{2πT} (sinh²(πT) + sin²(πP))`,

so the integrand equals `1 / (4 (sinh²(πT) + sin²(πP)))`.  The hypothesis on the line gives
`sin²(πP) ≥ 4 max 0 (δ² - T²)` with `δ = ‖α‖ξ/2`, while `sinh²(πT) ≥ π²T²`; hence the integrand is
dominated by the "gate density" `u ↦ (if |u| ≤ δ then (16δ²)⁻¹ else (4π²u²)⁻¹)` at `u = T`.
Changing variables `u = α.re·y + α.im·x` and integrating in `u` gives the claim.
-/

/-- Distance from the integers controls `sin²`: if `δ² ≤ (P-k)² + T²` for every `k : ℤ`, then
`4 * max 0 (δ² - T²) ≤ sin(πP)²`. -/
private lemma lintexp_trig {P T δ : ℝ} (h : ∀ k : ℤ, δ^2 ≤ (P - (k:ℝ))^2 + T^2) :
    4*max 0 (δ^2 - T^2) ≤ Real.sin (Real.pi*P)^2 := by
  set k : ℤ := ⌊P + 1/2⌋ with hkdef
  have hkl : (k:ℝ) ≤ P + 1/2 := by rw [hkdef]; exact Int.floor_le _
  have hku : P + 1/2 < (k:ℝ) + 1 := by rw [hkdef]; exact Int.lt_floor_add_one _
  set s : ℝ := P - (k:ℝ) with hsdef
  have hsl : -(1/2:ℝ) ≤ s := by rw [hsdef]; linarith
  have hsu : s ≤ 1/2 := by rw [hsdef]; linarith
  have habs : |s| ≤ 1/2 := abs_le.mpr ⟨hsl, hsu⟩
  have hs2 : 4*s^2 ≤ Real.sin (Real.pi*s)^2 := by
    have hx0 : 0 ≤ Real.pi*|s| := by positivity
    have hx1 : Real.pi*|s| ≤ Real.pi/2 := by nlinarith [habs, Real.pi_pos]
    have h1 := Real.mul_le_sin hx0 hx1
    have h2 : (2:ℝ)*|s| ≤ Real.sin (Real.pi*|s|) := by
      have he : (2/Real.pi)*(Real.pi*|s|) = 2*|s| := by field_simp
      linarith [h1, he]
    have h3 : Real.sin (Real.pi*s)^2 = Real.sin (Real.pi*|s|)^2 := by
      rcases le_or_gt 0 s with hs | hs
      · rw [abs_of_nonneg hs]
      · rw [abs_of_neg hs, show Real.pi*s = -(Real.pi*(-s)) by ring, Real.sin_neg, neg_sq]
    rw [h3]
    nlinarith [h2, sq_abs s, abs_nonneg s]
  have hks : δ^2 - T^2 ≤ s^2 := by
    have hh := h k
    rw [hsdef.symm] at hh
    linarith
  have hmax : max 0 (δ^2 - T^2) ≤ s^2 := max_le (by positivity) hks
  have hsin_P : Real.sin (Real.pi*P)^2 = Real.sin (Real.pi*s)^2 := by
    have harg : Real.pi*P = Real.pi*s + (k:ℝ)*Real.pi := by rw [hsdef]; ring
    rw [harg, Real.sin_add_int_mul_pi, mul_pow]
    have h1 : ((-1:ℝ)^k)^2 = 1 := by
      rw [← sq_abs ((-1:ℝ)^k), abs_neg_one_zpow]; norm_num
    rw [h1, one_mul]
  rw [hsin_P]
  nlinarith [hs2, hmax]

/-- `π²T² ≤ sinh²(πT)`. -/
private lemma lintexp_sinh_sq_ge (T : ℝ) : Real.pi^2 * T^2 ≤ Real.sinh (Real.pi*T)^2 := by
  have hsq : Real.sinh (Real.pi * T)^2 = Real.sinh (Real.pi * |T|)^2 := by
    have habs : Real.pi * |T| = |Real.pi * T| := by rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [habs]
    rcases le_or_gt 0 (Real.pi*T) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sinh_neg, neg_sq]
  have h1 : Real.pi * |T| ≤ Real.sinh (Real.pi*|T|) := Real.self_le_sinh_iff.mpr (by positivity)
  have ha : 0 ≤ Real.pi * |T| := by positivity
  have h2 : (Real.pi*|T|)^2 ≤ Real.sinh (Real.pi*|T|)^2 := pow_le_pow_left₀ ha h1 2
  calc Real.pi^2 * T^2 = (Real.pi * |T|)^2 := by rw [mul_pow, sq_abs]
    _ ≤ Real.sinh (Real.pi*|T|)^2 := h2
    _ = Real.sinh (Real.pi*T)^2 := hsq.symm

/-- Exact squared modulus: `‖1 - e^{2πT - 2πiP}‖² = (1 - e^{2πT})² + 4 e^{2πT} sin²(πP)`. -/
private lemma lintexp_nsq (T P : ℝ) :
    Complex.normSq (1 - Complex.exp (⟨2*Real.pi*T, -(2*Real.pi*P)⟩ : ℂ))
      = (1 - Real.exp (2*Real.pi*T))^2 + 4*Real.exp (2*Real.pi*T) * Real.sin (Real.pi*P)^2 := by
  have hs : Real.sin (Real.pi*P)^2 = 1 - Real.cos (Real.pi*P)^2 := Real.sin_sq _
  have hc : Real.cos (Real.pi*P*2) = 2*Real.cos (Real.pi*P)^2 - 1 := by
    rw [show Real.pi*P*2 = 2*(Real.pi*P) by ring, Real.cos_two_mul]
  have hs2 : Real.sin (Real.pi*P*2)^2 = 4*Real.cos (Real.pi*P)^2 - 4*Real.cos (Real.pi*P)^4 := by
    rw [show Real.pi*P*2 = 2*(Real.pi*P) by ring, Real.sin_two_mul]
    have := Real.sin_sq (Real.pi*P)
    nlinarith
  rw [Complex.normSq_apply]
  simp only [Complex.exp_re, Complex.exp_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im]
  rw [Real.cos_neg, Real.sin_neg]
  ring_nf
  rw [hc, hs2, hs]
  ring

/-- `(1 - e^{2πT})² = 4 e^{2πT} sinh²(πT)`. -/
private lemma lintexp_one_sub_exp_sq (T : ℝ) :
    (1 - Real.exp (2*Real.pi*T))^2 = 4*Real.exp (2*Real.pi*T)*Real.sinh (Real.pi*T)^2 := by
  have hx : Real.exp (Real.pi*T) * Real.exp (-(Real.pi*T)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : Real.exp (2*Real.pi*T) = Real.exp (Real.pi*T)*Real.exp (Real.pi*T) := by
    rw [show (2:ℝ)*Real.pi*T = Real.pi*T + Real.pi*T by ring, Real.exp_add]
  have hbase : 2 * Real.exp (Real.pi*T) * Real.sinh (Real.pi*T) = Real.exp (2*Real.pi*T) - 1 := by
    rw [Real.sinh_eq, h2]
    field_simp
    nlinarith [hx]
  have hsq := congrArg (fun x : ℝ => x^2) hbase
  simp only [mul_pow] at hsq
  have hr : Real.exp (2*Real.pi*T) = Real.exp (Real.pi*T)^2 := by
    rw [show (2:ℝ)*Real.pi*T = Real.pi*T + Real.pi*T by ring, Real.exp_add, sq]
  rw [hr] at hsq ⊢
  nlinarith [hsq]

/-- Numeric core: `1/(4(sinh²(πT)+sin²(πP)))` is bounded by the gate density at `T`. -/
private lemma lintexp_gate_bound {T P δ : ℝ} (hδ : 0 < δ)
    (hlat : ∀ k : ℤ, δ^2 ≤ (P - (k:ℝ))^2 + T^2) :
    1/(4*(Real.sinh (Real.pi*T)^2 + Real.sin (Real.pi*P)^2))
      ≤ (if |T| ≤ δ then (16*δ^2)⁻¹ else (4*Real.pi^2*T^2)⁻¹) := by
  have hsin := lintexp_trig hlat
  have hsinh := lintexp_sinh_sq_ge T
  have hpi : (4:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  split_ifs with hcase
  · have hT2 : T^2 ≤ δ^2 := sq_le_sq' (abs_le.mp hcase).1 (abs_le.mp hcase).2
    have hmax : max 0 (δ^2 - T^2) = δ^2 - T^2 := max_eq_right (sub_nonneg.mpr hT2)
    rw [hmax] at hsin
    have hden : 16*δ^2 ≤ 4*(Real.sinh (Real.pi*T)^2 + Real.sin (Real.pi*P)^2) := by
      nlinarith [hsin, hsinh, hpi, sq_nonneg (Real.sin (Real.pi*P))]
    rw [show (16*δ^2)⁻¹ = 1/(16*δ^2) by rw [one_div]]
    exact one_div_le_one_div_of_le (by positivity) hden
  · have hle : δ^2 - T^2 ≤ 0 := by
      have hgt : δ < |T| := not_le.mp hcase
      nlinarith [hgt, hδ, abs_nonneg T, sq_abs T]
    have hmax : max 0 (δ^2 - T^2) = 0 := max_eq_left hle
    rw [hmax] at hsin
    have hden : 4*Real.pi^2*T^2 ≤ 4*(Real.sinh (Real.pi*T)^2 + Real.sin (Real.pi*P)^2) := by
      nlinarith [hsin, hsinh, sq_nonneg (Real.sin (Real.pi*P))]
    have hTne : T ≠ 0 := by
      intro h0; rw [h0] at hcase; simp at hcase; linarith [hδ]
    rw [show (4*Real.pi^2*T^2)⁻¹ = 1/(4*Real.pi^2*T^2) by rw [one_div]]
    exact one_div_le_one_div_of_le (by positivity) hden

/-- Pointwise domination of the exp defect weight by the gate density at `T`. -/
private lemma lintegral_exp_defect_pointwise {α : ℂ} {x ξ y : ℝ} (hξ : 0 < ξ) (hα : α ≠ 0)
    (hlat : ∀ k : ℤ, ‖α‖ * ξ / 2 ≤ ‖α * ((x : ℂ) + y * Complex.I) - (k : ℂ)‖) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
      / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2
    ≤ (if |α.re * y + α.im * x| ≤ ‖α‖ * ξ / 2
        then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
        else (4 * Real.pi ^ 2 * (α.re * y + α.im * x) ^ 2)⁻¹) := by
  have hδpos : 0 < ‖α‖ * ξ / 2 := by positivity
  have hW : -(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I))
      = (⟨2*Real.pi*(α.re*y+α.im*x), -(2*Real.pi*(α.re*x-α.im*y))⟩ : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]; ring
    · simp [Complex.mul_re, Complex.mul_im]; ring
  have hlat' : ∀ k : ℤ, (‖α‖*ξ/2)^2 ≤ (α.re*x - α.im*y - (k:ℝ))^2 + (α.re*y+α.im*x)^2 := by
    intro k
    have h1 : ‖α * ((x:ℂ) + y*Complex.I) - (k:ℂ)‖^2
        = (α.re*x - α.im*y - (k:ℝ))^2 + (α.re*y+α.im*x)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.mul_re, Complex.mul_im]
      ring
    have h2 : (‖α‖ * ξ / 2)^2 ≤ ‖α * ((x:ℂ) + y*Complex.I) - (k:ℂ)‖^2 := by
      have hk := hlat k
      nlinarith [hk, norm_nonneg (α * ((x:ℂ) + y*Complex.I) - (k:ℂ)), hδpos]
    rw [h1] at h2; exact h2
  have hnum : ‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
      = Real.exp (2*Real.pi*(α.re*y+α.im*x)) := by
    rw [Complex.norm_exp, hW]
  have hmain : ‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
      / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2
      = 1/(4*(Real.sinh (Real.pi*(α.re*y+α.im*x))^2
              + Real.sin (Real.pi*(α.re*x-α.im*y))^2)) := by
    rw [hnum, Complex.sq_norm, hW, lintexp_nsq, lintexp_one_sub_exp_sq]
    field_simp
  rw [hmain]
  exact lintexp_gate_bound hδpos hlat'

/-- Bound for the `L¹`-mass of the exp defect weight along a vertical line avoiding the lattice
`α⁻¹ ℤ`. -/
theorem lintegral_exp_defect_le {α : ℂ} {x ξ : ℝ} (ha : 0 < α.re) (hξ : 0 < ξ)
    (hlat : ∀ y : ℝ, ∀ k : ℤ, ξ / 2 ≤ ‖((x : ℂ) + y * Complex.I) - (k : ℂ) / α‖) :
    ∫⁻ y : ℝ, ENNReal.ofReal
        (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
          / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2)
      ≤ ENNReal.ofReal (1 / (α.re * ‖α‖ * ξ)) := by
  have hαne : α ≠ 0 := by
    rintro rfl
    simp at ha
  have hδpos : 0 < ‖α‖ * ξ / 2 := by positivity
  have hlat' : ∀ y : ℝ, ∀ k : ℤ, ‖α‖ * ξ / 2 ≤ ‖α * ((x : ℂ) + y * Complex.I) - (k : ℂ)‖ := by
    intro y k
    have h1 : ‖α‖ * (ξ / 2) ≤ ‖α‖ * ‖((x : ℂ) + y * Complex.I) - (k : ℂ) / α‖ :=
      mul_le_mul_of_nonneg_left (hlat y k) (norm_nonneg α)
    have h2 : α * (((x : ℂ) + y * Complex.I) - (k : ℂ) / α)
        = α * ((x : ℂ) + y * Complex.I) - (k : ℂ) := by
      field_simp
    calc ‖α‖ * ξ / 2 = ‖α‖ * (ξ / 2) := by ring
      _ ≤ ‖α‖ * ‖((x : ℂ) + y * Complex.I) - (k : ℂ) / α‖ := h1
      _ = ‖α * (((x : ℂ) + y * Complex.I) - (k : ℂ) / α)‖ := (norm_mul _ _).symm
      _ = ‖α * ((x : ℂ) + y * Complex.I) - (k : ℂ)‖ := by rw [h2]
  have hpt : ∀ y : ℝ, (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
          / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2)
      ≤ (if |α.re * y + α.im * x| ≤ ‖α‖ * ξ / 2 then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
          else (4 * Real.pi ^ 2 * (α.re * y + α.im * x) ^ 2)⁻¹) :=
    fun y => lintegral_exp_defect_pointwise hξ hαne (hlat' y)
  have hmeas : Measurable (fun u : ℝ => ENNReal.ofReal
      (if |u| ≤ ‖α‖ * ξ / 2 then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
        else (4 * Real.pi ^ 2 * u ^ 2)⁻¹)) := by
    apply ENNReal.continuous_ofReal.measurable.comp
    exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
      (by measurability)
  calc ∫⁻ y : ℝ, ENNReal.ofReal
        (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
          / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2)
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal
          (if |α.re * y + α.im * x| ≤ ‖α‖ * ξ / 2 then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
            else (4 * Real.pi ^ 2 * (α.re * y + α.im * x) ^ 2)⁻¹) :=
        MeasureTheory.lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hpt y))
    _ = ∫⁻ y : ℝ, (fun u : ℝ => ENNReal.ofReal
          (if |u| ≤ ‖α‖ * ξ / 2 then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
            else (4 * Real.pi ^ 2 * u ^ 2)⁻¹)) (α.re * y + α.im * x) := rfl
    _ = ENNReal.ofReal ((α.re)⁻¹) * ∫⁻ u : ℝ, ENNReal.ofReal
          (if |u| ≤ ‖α‖ * ξ / 2 then (16 * (‖α‖ * ξ / 2) ^ 2)⁻¹
            else (4 * Real.pi ^ 2 * u ^ 2)⁻¹) :=
        lintegral_comp_mul_add ha _ hmeas
    _ ≤ ENNReal.ofReal ((α.re)⁻¹) * ENNReal.ofReal (1 / (2 * (‖α‖ * ξ / 2))) :=
        mul_le_mul_right (lintegral_gate_density hδpos) _
    _ = ENNReal.ofReal (1 / (α.re * ‖α‖ * ξ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hnz : ‖α‖ * ξ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hαne) (ne_of_gt hξ)
        field_simp

end Work.Pert
