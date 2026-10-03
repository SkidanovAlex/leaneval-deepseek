import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Analysis.injEntireLowerBound
import Submission.Work.Fatou.Analysis.analyticOrderLowerBound
import Submission.Work.Fatou.Analysis.existsEntireOfBddPunctured
import Submission.Work.Fatou.Analysis.globalGrowthOfExterior
import Submission.Work.Fatou.Analysis.entireEqPolynomialOfGrowth
import Submission.Work.Fatou.Analysis.injPolynomialNatDegreeLeOne

namespace Work.Fatou.Analysis

/-- **An injective entire function without fixed points is a translation** (Shishikura's FX7).
If `A : ℂ → ℂ` is entire, injective and has no fixed point, then `A w = w + b` with `b ≠ 0`.

The proof: injecting `A` bounds `A` away from `A 0` outside the unit disc (open mapping theorem),
so `w ↦ (A (1/w) - A 0)⁻¹` is bounded near `0` and extends to an entire function `G`. The
vanishing order of `G` at `0` gives an exterior growth bound for `A`, hence (Cauchy estimates)
`A - A 0` is a polynomial, which by injectivity has degree at most `1`. Finally `A w = a w + c`
and `A w ≠ w` force `a = 1` and `c ≠ 0`. -/
theorem injEntireTranslation : MandelDim.InjEntireTranslation := by
  intro A hA hinj hfix
  obtain ⟨ρ, hρpos, hρ⟩ := injEntireLowerBound A hA hinj
  have hAnz : ∀ z : ℂ, z ≠ 0 → A z ≠ A 0 := fun z hz h => hz (hinj h)
  have hg_diff : DifferentiableOn ℂ (fun w : ℂ => (A w⁻¹ - A 0)⁻¹) {w : ℂ | w ≠ 0} := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => A w⁻¹ - A 0) w :=
      (hA.differentiableAt.comp w (differentiableAt_inv hw)).sub (differentiableAt_const (A 0))
    exact (h1.inv (sub_ne_zero_of_ne (hAnz w⁻¹ (inv_ne_zero hw)))).differentiableWithinAt
  have hg_bdd : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < 1 → ‖(A w⁻¹ - A 0)⁻¹‖ ≤ ρ⁻¹ := by
    intro w hw0 hw1
    have h1 : 1 ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      rw [one_le_inv₀ hw0]
      exact le_of_lt hw1
    have hρw : ρ ≤ ‖A w⁻¹ - A 0‖ := hρ w⁻¹ h1
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hρpos hρw
  obtain ⟨G, hG, hGeq⟩ :=
    existsEntireOfBddPunctured (fun w : ℂ => (A w⁻¹ - A 0)⁻¹) ρ⁻¹ hg_diff hg_bdd
  have hGne : ∀ w : ℂ, w ≠ 0 → G w ≠ 0 := by
    intro w hw
    rw [hGeq w hw]
    exact inv_ne_zero (sub_ne_zero_of_ne (hAnz w⁻¹ (inv_ne_zero hw)))
  obtain ⟨n, c, R, hc, hR, hbound⟩ := analyticOrderLowerBound G hG hGne
  have hgrowth : ∀ z : ℂ, R⁻¹ ≤ ‖z‖ → ‖A z - A 0‖ ≤ c⁻¹ * ‖z‖ ^ n := by
    intro z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (inv_pos.mpr hR) hz
    have hzne : z ≠ 0 := by simpa [norm_pos_iff] using hzpos
    have hzinvpos : 0 < ‖z⁻¹‖ := by rw [norm_inv]; exact inv_pos.mpr hzpos
    have hzR : ‖z⁻¹‖ ≤ R := by
      rw [norm_inv]
      exact (inv_le_comm₀ hzpos hR).mpr hz
    have hb := hbound z⁻¹ hzinvpos hzR
    have hGz : G z⁻¹ = (A z - A 0)⁻¹ := by
      rw [hGeq z⁻¹ (by simpa using hzne)]
      simp
    rw [hGz, norm_inv, norm_inv, inv_pow] at hb
    have hX : 0 < ‖z‖ ^ n := pow_pos hzpos n
    have hY : 0 < ‖A z - A 0‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (hAnz z hzne)
    have hXY : 0 < ‖z‖ ^ n * ‖A z - A 0‖ := mul_pos hX hY
    have hkey := mul_le_mul_of_nonneg_right hb (le_of_lt hXY)
    rw [show c * (‖z‖ ^ n)⁻¹ * (‖z‖ ^ n * ‖A z - A 0‖) = c * ‖A z - A 0‖ by
      field_simp] at hkey
    rw [show ‖A z - A 0‖⁻¹ * (‖z‖ ^ n * ‖A z - A 0‖) = ‖z‖ ^ n by field_simp] at hkey
    rw [mul_comm] at hkey
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    exact hkey
  obtain ⟨C, hC, hbd⟩ := globalGrowthOfExterior (fun z : ℂ => A z - A 0)
    (hA.continuous.sub continuous_const) n c⁻¹ R⁻¹ (inv_pos.mpr hc) (inv_pos.mpr hR) hgrowth
  obtain ⟨p, hp, hpdeg⟩ := entireEqPolynomialOfGrowth (fun z : ℂ => A z - A 0)
    (hA.sub (differentiable_const (A 0))) n C hC hbd
  have hinjp : ∀ z w : ℂ, p.eval z = p.eval w → z = w := by
    intro z w h
    have h1 : A z - A 0 = A w - A 0 := by rw [← hp z, ← hp w, h]
    exact hinj (sub_left_inj.mp h1)
  have hp1 : p.natDegree ≤ 1 := injPolynomialNatDegreeLeOne p hinjp
  obtain ⟨a, b, hab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp1
  have hAeq : ∀ z : ℂ, A z = a * z + b + A 0 := by
    intro z
    have h := hp z
    rw [hab] at h
    simp at h
    have h' : a * z + b + A 0 = A z := by rw [h]; simp
    exact h'.symm
  have ha1 : a = 1 := by
    by_contra ha
    have hden : a - 1 ≠ 0 := sub_ne_zero_of_ne ha
    have hcalc : a * (-(b + A 0) / (a - 1)) + b + A 0 = -(b + A 0) / (a - 1) := by
      field_simp
      ring
    exact (hfix (-(b + A 0) / (a - 1))) (by rw [hAeq]; exact hcalc)
  refine ⟨b + A 0, ?_, fun w => ?_⟩
  · have hb0 : b + A 0 = A 0 := by
      have h := hAeq 0
      rw [ha1] at h
      simpa using h
    rw [hb0]
    exact hfix 0
  · rw [hAeq w, ha1]
    ring

end Work.Fatou.Analysis
