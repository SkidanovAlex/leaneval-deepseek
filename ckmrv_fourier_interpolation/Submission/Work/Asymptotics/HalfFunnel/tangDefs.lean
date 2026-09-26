import Mathlib
import Submission.Work.Asymptotics.DomainD

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane ModularGroup

noncomputable section

/-! ## The tangency region and the two poles

The region of `lowRegion_tangency` is the part of the low strip `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}`
lying in the Euclidean ball of radius `1/8` about one of the two tangency points
`±1/2 + i/2 ∈ ∂𝒟`.

For `τ ∈ 𝒟` the two points of the `SL(2,ℤ)`-orbit of `τ` that accumulate at `i` are

`z₁(τ) = T (S τ) = 1 - 1/τ`   and   `z₂(τ) = S z₁(τ) = τ/(1-τ)`,

both with `j(zᵢ τ) = j τ`.  Since `𝒟` is contained in `{|τ|² > Re τ}`, the point `z₁` lies
strictly to the *right* of the imaginary axis and `z₂` strictly to its left.  The pole `z₁` is
the one that crosses the contour `z = i t` as `τ` approaches `∂𝒟`; the residue there is the
jump of the contour integral, and the signed integral stays bounded precisely because the pole
is *off* the contour and the contour is deformed around it.

## The plan of the proof

`kernelTransform K τ r = 4 sin²(πr²/2) ∫_0^∞ K(τ, it) e^{-πr²t} dt`.  For `τ` in the region
the divisors `K(τ,it)` are bounded on `(0, 3/4] ∪ [5/4, ∞)` (`tang_safe_bound`,
`tang_tail_bound`), while on the window `[3/4, 5/4]` — which contains the two poles `z₁`, `z₂`
of `z ↦ K(τ,z)`, at distance `~2‖τ - (±1/2 + i/2)‖` from the contour — the contour is deformed
around the poles.  The rectangle `[0,1/4] × [3/4,5/4]` contains `z₁` and only `z₁`
(`tang_orbit_rect`), and Cauchy's theorem (`Work.Asymptotics.residue_rectangle`) gives

  `∫_{i/2}^{3i/2…}`: the left edge integral `= 2πi·c(τ)·w(z₁) + [right/top/bottom edges]`,

where `|c(τ)| ≤ C` is the residue bound of `tang_pole_decomp` and the remaining edges are at
distance `≥ 1/4 - 1/8` from the poles, so the kernel is bounded there.  This is the signed
cancellation: the modulus `∫ 1/|it - z₁| dt` diverges like `log(1/‖τ-τ₀‖)`, the signed integral
does not.
-/

/-- The tangency point `1/2 + i/2 ∈ ∂𝒟`. -/
def ctanP : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I

/-- The tangency point `-1/2 + i/2 ∈ ∂𝒟`. -/
def ctanM : ℂ := ((-(1 / 2) : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I

/-- **The tangency region**: the target set of `lowRegion_tangency`. -/
def ctanRegion : Set ℍ :=
  {τ | τ ∈ DomainD ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧
    (‖(τ : ℂ) - ctanP‖ < 1 / 8 ∨ ‖(τ : ℂ) - ctanM‖ < 1 / 8)}

/-- The *closed* region containing `ctanRegion`, on which all the uniform estimates hold. -/
def ctanRegionCl : Set ℍ :=
  {τ | (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧
    (‖(τ : ℂ) - ctanP‖ ≤ 1 / 8 ∨ ‖(τ : ℂ) - ctanM‖ ≤ 1 / 8)}

/-- **The first pole.**  For `Re τ > 0` (the tangency point `1/2 + i/2`) it is
`z₁(τ) = T (S τ) = 1 - 1/τ`, for `Re τ < 0` (the tangency point `-1/2 + i/2`) it is
`z₁(τ) = T S T τ = τ/(1+τ)`.  In both cases `z₁ τ` is the point of the orbit of `τ` that
crosses the contour, to the *right* of the imaginary axis. -/
def poleOne (τ : ℍ) : ℍ :=
  if τ.re < 0 then (ModularGroup.T * ModularGroup.S * ModularGroup.T) • τ
  else (1 : ℝ) +ᵥ (ModularGroup.S • τ)

/-- **The second pole**: `z₂(τ) = S z₁(τ) = τ/(1-τ)`. -/
def poleTwo (τ : ℍ) : ℍ := ModularGroup.S • poleOne τ

lemma TST_coe (τ : ℍ) :
    (((ModularGroup.T * ModularGroup.S * ModularGroup.T) • τ : ℍ) : ℂ)
      = (τ : ℂ) / (1 + (τ : ℂ)) := by
  rw [mul_smul, mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul,
    UpperHalfPlane.modular_T_smul]
  have h1 : (1 : ℂ) + (τ : ℂ) ≠ 0 := by
    intro h
    have h2 : (τ : ℂ) = -1 := by linear_combination h
    have h3 : τ.im = 0 := by
      have hh := congrArg Complex.im h2
      simpa using hh
    have := τ.im_pos
    rw [h3] at this
    exact lt_irrefl 0 this
  simp only [UpperHalfPlane.coe_vadd]
  push_cast
  field_simp
  ring

/-- The complex coordinate of the first pole, in the two cases. -/
lemma poleOne_coe (τ : ℍ) :
    ((poleOne τ : ℍ) : ℂ)
      = (if τ.re < 0 then (τ : ℂ) / (1 + (τ : ℂ)) else 1 - 1 / (τ : ℂ)) := by
  rw [poleOne]
  split_ifs with h
  · rw [TST_coe]
  · rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    push_cast
    ring

/-- `j(z₁ τ) = j τ`: `z₁τ` is in the `SL(2,ℤ)`-orbit of `τ`, being the image of `τ` under the
Möbius map `TS` (resp. `TST`) attached to the tangency point. -/
theorem jInvariantFun_poleOne (τ : ℍ) :
    Work.Kernels.jInvariantFun (poleOne τ) = Work.Kernels.jInvariantFun τ := by
  rw [poleOne]
  split_ifs with h
  · rw [mul_smul, mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul,
      Work.Kernels.KernelFacts.jInvariantFun_vadd_one,
      Work.Kernels.KernelFacts.jInvariantFun_S_smul,
      Work.Kernels.KernelFacts.jInvariantFun_vadd_one]
  · rw [Work.Kernels.KernelFacts.jInvariantFun_vadd_one,
      Work.Kernels.KernelFacts.jInvariantFun_S_smul]

/-- `j(z₂ τ) = j τ`. -/
theorem jInvariantFun_poleTwo (τ : ℍ) :
    Work.Kernels.jInvariantFun (poleTwo τ) = Work.Kernels.jInvariantFun τ := by
  rw [poleTwo, Work.Kernels.KernelFacts.jInvariantFun_S_smul, jInvariantFun_poleOne]

/-- **`𝒟` lies in `{|τ|² > Re τ}`**: this is the condition `|τ - 1/2| > 1/2` expanded. -/
lemma re_lt_normSq_of_mem_DomainD {τ : ℍ} (hτ : τ ∈ DomainD) :
    (τ : ℂ).re < (τ : ℂ).normSq := by
  have h := hτ.2.2.1
  have h2 : (1/2 : ℝ)^2 < ‖(τ : ℂ) - (1/2 : ℂ)‖ ^ 2 := by
    have h0 : (0:ℝ) < ‖(τ:ℂ) - (1/2:ℂ)‖ := by
      rw [norm_pos_iff]
      intro hc
      have : (τ:ℂ).im = 0 := by
        have hh := congrArg Complex.im hc
        simpa using hh
      rw [UpperHalfPlane.coe_im] at this
      linarith [τ.im_pos]
    nlinarith
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h2
  rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num at h2
  nlinarith

/-- The real part of the first pole is strictly positive on `𝒟` (the pole is to the right of the
contour).  Both cases are elementary: `Re (1 - 1/τ) = 1 - Re τ/|τ|² > 0` uses `|τ - 1/2| > 1/2`,
i.e. `|τ|² > Re τ`, and `Re (τ/(1+τ)) = (Re τ + |τ|²)/|1+τ|² > 0` uses `|τ + 1/2| > 1/2`, i.e.
`|τ|² + Re τ > 0`. -/
theorem poleOne_re_pos {τ : ℍ} (hτ : τ ∈ DomainD) : 0 < (poleOne τ).re := by
  rw [poleOne]
  split_ifs with hneg
  · have hpos : 0 < ((1:ℂ) + (τ:ℂ)).normSq := by
      rw [Complex.normSq_pos]
      intro hc
      have h2 : ((1:ℂ) + (τ:ℂ)).im = 0 := by rw [hc]; simp
      simp at h2
      linarith [τ.im_pos]
    have h2 : ((((ModularGroup.T * ModularGroup.S * ModularGroup.T) • τ : ℍ) : ℂ)).re
        = ((τ:ℂ).re + (τ:ℂ).normSq) / ((1:ℂ) + (τ:ℂ)).normSq := by
      rw [TST_coe, Complex.div_re]
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      ring
    rw [← UpperHalfPlane.coe_re, h2]
    have h3 : 0 < (τ:ℂ).re + (τ:ℂ).normSq := by
      have h5 : (1/4:ℝ) < ((τ:ℂ) + (1/2:ℂ)).normSq := by
        have h1 : ((1/2:ℝ))^2 < ‖(τ:ℂ) + (1/2:ℂ)‖^2 := by
          nlinarith [norm_nonneg ((τ:ℂ) + (1/2:ℂ)), hτ.2.2.2]
        rw [← Complex.normSq_eq_norm_sq] at h1
        norm_num at h1
        exact h1
      have h6 : ((τ:ℂ) + (1/2:ℂ)).normSq = (τ:ℂ).normSq + (τ:ℂ).re + 1/4 := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
        norm_num
        ring
      linarith
    exact div_pos h3 hpos
  · have h2 : ((((1 : ℝ) +ᵥ (ModularGroup.S • τ) : ℍ) : ℂ)).re
        = 1 - (τ:ℂ).re / (τ:ℂ).normSq := by
      rw [UpperHalfPlane.coe_vadd]
      simp only [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
      rw [Complex.add_re, Complex.ofReal_re, Complex.inv_re, Complex.neg_re,
        Complex.normSq_neg]
      ring
    rw [← UpperHalfPlane.coe_re, h2]
    have hnorm : 0 < (τ : ℂ).normSq := by
      rw [Complex.normSq_pos]
      exact τ.ne_zero
    have h4 : (τ : ℂ).re / (τ : ℂ).normSq < 1 := by
      rw [div_lt_one hnorm]
      simpa using re_lt_normSq_of_mem_DomainD hτ
    linarith

/-- The complex coordinate of the Möbius action of `S`. -/
lemma S_coe_eq (w : ℍ) : ((ModularGroup.S • w : ℍ) : ℂ) = -1 / (w : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  ring_nf

/-- `Re (S w) = - Re w / |w|²`. -/
lemma re_S_smul (w : ℍ) : (ModularGroup.S • w).re = - w.re / (w : ℂ).normSq := by
  rw [← UpperHalfPlane.coe_re, S_coe_eq, Complex.div_re]
  simp

/-- For `τ ∈ 𝒟` the second pole lies strictly to the left of the imaginary axis. -/
theorem poleTwo_re_neg {τ : ℍ} (hτ : τ ∈ DomainD) : (poleTwo τ).re < 0 := by
  have hS : (poleTwo τ).re = - (poleOne τ).re / ((poleOne τ : ℍ) : ℂ).normSq := re_S_smul _
  rw [hS]
  have hpos : 0 < ((poleOne τ : ℍ) : ℂ).normSq := by
    rw [Complex.normSq_pos]
    exact (poleOne τ).ne_zero
  have := poleOne_re_pos hτ
  exact div_neg_of_neg_of_pos (neg_neg_of_pos this) hpos

end

end Work.Asymptotics.HalfFunnel
