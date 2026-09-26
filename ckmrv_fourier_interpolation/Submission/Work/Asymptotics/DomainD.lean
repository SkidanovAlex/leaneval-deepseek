/-
# The CKMRV fundamental domains `𝒟` and `𝓕`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the E8 and Leech
lattices and interpolation formulas*, Ann. of Math. 196 (2022)) define, in (3.12),

  `𝒟 = {z ∈ ℍ : -1 < Re z < 1, |z - 1/2| > 1/2, |z + 1/2| > 1/2}`,

the fundamental domain of the principal congruence subgroup `Γ(2)`, and, in (3.13),

  `𝓕 = {z ∈ ℍ : 0 < Re z < 1, |z| > 1, |z - 1| > 1}`,

the standard fundamental domain of `SL(2,ℤ)`.  These are the domains on which the contour
integral (5.2) converges directly, and from which the CKMRV generating function `F` is obtained
by analytic continuation (their Propositions 4.6 and 3.2).

This file contains the definitions and the elementary geometric API used by
`Work.Asymptotics.Propagate`.
-/
import Mathlib
import Submission.Work.Kernels.All

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- **CKMRV (3.12)**: the fundamental domain `𝒟` of `Γ(2)`, the open region bounded by the
lines `Re z = ±1` and the two semicircles of radius `1/2` centred at `±1/2`. -/
def DomainD : Set ℍ :=
  {z | -1 < z.re ∧ z.re < 1 ∧ (1 : ℝ) / 2 < ‖(z : ℂ) - (1 / 2 : ℂ)‖ ∧
    (1 : ℝ) / 2 < ‖(z : ℂ) + (1 / 2 : ℂ)‖}

/-- **CKMRV (3.13)**: the standard fundamental domain `𝓕` of `SL(2,ℤ)`. -/
def DomainF : Set ℍ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ 1 < ‖(z : ℂ)‖ ∧ 1 < ‖(z : ℂ) - 1‖}

variable {z : ℍ}

lemma mem_DomainD :
    z ∈ DomainD ↔ -1 < z.re ∧ z.re < 1 ∧ (1 : ℝ) / 2 < ‖(z : ℂ) - (1 / 2 : ℂ)‖ ∧
      (1 : ℝ) / 2 < ‖(z : ℂ) + (1 / 2 : ℂ)‖ := Iff.rfl

lemma mem_DomainF :
    z ∈ DomainF ↔ 0 < z.re ∧ z.re < 1 ∧ 1 < ‖(z : ℂ)‖ ∧ 1 < ‖(z : ℂ) - 1‖ := Iff.rfl

/-- Membership in `𝒟` gives the strip conditions. -/
lemma re_bounds_of_mem_DomainD (hz : z ∈ DomainD) : -1 < z.re ∧ z.re < 1 :=
  ⟨hz.1, hz.2.1⟩

/-- The imaginary part is positive on `ℍ`; useful to have in this namespace. -/
lemma im_pos (z : ℍ) : 0 < z.im := z.im_pos

/-- `𝒟` is contained in the vertical strip `-1 < Re z < 1`. -/
lemma DomainD_subset_strip : DomainD ⊆ {z : ℍ | -1 < z.re ∧ z.re < 1} :=
  fun _ hz => re_bounds_of_mem_DomainD hz

/-- `𝒟` is an open subset of `ℍ`. -/
theorem isOpen_DomainD : IsOpen DomainD := by
  have h1 : IsOpen {z : ℍ | -1 < z.re} :=
    isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have h2 : IsOpen {z : ℍ | z.re < 1} :=
    isOpen_lt UpperHalfPlane.continuous_re continuous_const
  have h3 : IsOpen {z : ℍ | (1 : ℝ) / 2 < ‖(z : ℂ) - (1 / 2 : ℂ)‖} :=
    isOpen_lt continuous_const (Continuous.norm (continuous_coe.sub continuous_const))
  have h4 : IsOpen {z : ℍ | (1 : ℝ) / 2 < ‖(z : ℂ) + (1 / 2 : ℂ)‖} :=
    isOpen_lt continuous_const (Continuous.norm (continuous_coe.add continuous_const))
  have : DomainD = {z : ℍ | -1 < z.re} ∩ {z : ℍ | z.re < 1} ∩
      {z : ℍ | (1 : ℝ) / 2 < ‖(z : ℂ) - (1 / 2 : ℂ)‖} ∩
      {z : ℍ | (1 : ℝ) / 2 < ‖(z : ℂ) + (1 / 2 : ℂ)‖} := by
    ext z; simp [DomainD, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

/-- `𝒟` is nonempty: `2i` belongs to it. -/
theorem DomainD_nonempty : DomainD.Nonempty := by
  refine ⟨⟨2 * Complex.I, by simp⟩, ?_⟩
  have hcoe : ((⟨2 * Complex.I, by simp⟩ : ℍ) : ℂ) = 2 * Complex.I := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [hcoe]
    have h2 : ‖(2 : ℂ) * Complex.I - (1 / 2 : ℂ)‖ ^ 2 = 2 ^ 2 + (1 / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im]
      norm_num
    nlinarith [norm_nonneg ((2 : ℂ) * Complex.I - (1 / 2 : ℂ))]
  · rw [hcoe]
    have h2 : ‖(2 : ℂ) * Complex.I + (1 / 2 : ℂ)‖ ^ 2 = 2 ^ 2 + (1 / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im]
      norm_num
    nlinarith [norm_nonneg ((2 : ℂ) * Complex.I + (1 / 2 : ℂ))]

/-- `𝓕 ⊆ 𝒟`: the standard fundamental domain of `SL(2,ℤ)` sits inside that of `Γ(2)`. -/
theorem DomainF_subset_DomainD : DomainF ⊆ DomainD := by
  rintro z ⟨h0, h1, h2, h3⟩
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · -- `|z| > 1` gives `|z - 1/2| > 1/2` by the reverse triangle inequality
    have hnorm : ‖((1 / 2 : ℂ))‖ = 1 / 2 := by norm_num
    have h := abs_norm_sub_norm_le (z : ℂ) ((1 / 2 : ℂ))
    rw [hnorm] at h
    rw [abs_le] at h
    linarith [h.1]
  · -- `Re z > 0` gives `|z + 1/2| ≥ Re z + 1/2 > 1/2`
    have h := Complex.abs_re_le_norm ((z : ℂ) + (1 / 2 : ℂ))
    have hre : (((z : ℂ) + (1 / 2 : ℂ)).re) = z.re + 1 / 2 := by
      simp [Complex.add_re]
    rw [hre] at h
    linarith [abs_of_pos (by linarith : (0:ℝ) < z.re + 1/2)]

/-- `𝓕` is nonempty: `1/2 + i` belongs to it. -/
theorem DomainF_nonempty : DomainF.Nonempty := by
  refine ⟨⟨(1 / 2 : ℂ) + Complex.I, by simp⟩, ?_⟩
  have hcoe : ((⟨(1 / 2 : ℂ) + Complex.I, by simp⟩ : ℍ) : ℂ) = (1 / 2 : ℂ) + Complex.I := rfl
  have hre : ((⟨(1 / 2 : ℂ) + Complex.I, by simp⟩ : ℍ)).re = 1 / 2 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hre]
  · simp only [hre]; norm_num
  · rw [hcoe]
    have h2 : ‖(1 / 2 : ℂ) + Complex.I‖ ^ 2 = (1 / 2) ^ 2 + 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      norm_num
    nlinarith [norm_nonneg ((1 / 2 : ℂ) + Complex.I)]
  · rw [hcoe]
    have h2 : ‖(1 / 2 : ℂ) + Complex.I - 1‖ ^ 2 = (1 / 2) ^ 2 + 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
    nlinarith [norm_nonneg ((1 / 2 : ℂ) + Complex.I - 1)]

end Work.Asymptotics
