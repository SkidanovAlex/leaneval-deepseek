import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Kernels.KernelFacts.KPlus_T2

namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

/-- The bottom-left entry of an element of `SL(2,ℤ)` that maps a funnel point `τ` to a point
`ζ` within distance `29/20` of `τ` vanishes.  Equivalently, such an element is a translation
(up to sign): the estimate shows that any non-trivial `c ≠ 0` would force `Im τ ≤ 20/11 < 2`,
against `Im τ ≥ 2`. -/
private lemma entries_zero_of_smul_close (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ ζ : ℍ}
    (hτ : 2 ≤ τ.im) (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) (hg : g • τ = ζ) : g 1 0 = 0 := by
  -- `Im ζ` cannot be too small
  have hζim : 11 / 20 ≤ ζ.im := by
    have h1 : |ζ.im - τ.im| ≤ 29 / 20 := by
      have h2 : |((ζ : ℂ) - (τ : ℂ)).im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := Complex.abs_im_le_norm _
      have h3 : ((ζ : ℂ) - (τ : ℂ)).im = ζ.im - τ.im := by simp
      rw [h3] at h2
      linarith
    have h4 := (abs_le.mp h1).1
    linarith
  have hζpos : 0 < ζ.im := by linarith
  set N : ℝ := Complex.normSq (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)) with hNdef
  -- imaginary part of the Möbius action
  have him : ζ.im = τ.im / N := by
    have h := ModularGroup.im_smul_eq_div_normSq g τ
    rw [hg] at h
    simpa [hNdef] using h
  have hNnonneg : 0 ≤ N := by rw [hNdef]; exact Complex.normSq_nonneg _
  have hNne : N ≠ 0 := by
    intro h0
    rw [h0, div_zero] at him
    linarith
  have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hNne)
  have hmul : ζ.im * N = τ.im := by rw [him, div_mul_cancel₀ _ hNne]
  have hNub : N ≤ (20 / 11) * τ.im := by
    have h3 : (11 / 20) * N ≤ τ.im := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hζim hNpos.le
    linarith
  have hcsq : (((g : GL (Fin 2) ℝ)) 1 0 * τ.im) ^ 2 ≤ N := by
    have := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g : GL (Fin 2) ℝ) τ
    simpa [hNdef] using this
  set x : ℝ := ((g : GL (Fin 2) ℝ)) 1 0 with hxdef
  have hb1 : (x * τ.im) ^ 2 ≤ (20 / 11) * τ.im := le_trans hcsq hNub
  have hy : 0 < τ.im := by linarith
  have hsq : (x * τ.im) ^ 2 = x ^ 2 * τ.im ^ 2 := by ring
  rw [hsq] at hb1
  have hb1' : x ^ 2 * τ.im ≤ 20 / 11 := by
    have h : x ^ 2 * τ.im * τ.im ≤ (20 / 11) * τ.im := by nlinarith [hb1]
    exact le_of_mul_le_mul_right h hy
  have hx2 : 2 * x ^ 2 ≤ 20 / 11 := by
    have h2 : 2 * x ^ 2 ≤ x ^ 2 * τ.im := by
      nlinarith [mul_le_mul_of_nonneg_left hτ (sq_nonneg x)]
    linarith
  have hxle : x ^ 2 ≤ 10 / 11 := by linarith
  have hxcast : x = ((g 1 0 : ℤ) : ℝ) := by rw [hxdef]; simp
  rw [hxcast] at hxle
  by_contra hc
  have h1 : (1 : ℝ) ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 := by
    have h2 : (1 : ℤ) ≤ |g 1 0| := Int.one_le_abs hc
    have h2' : (1 : ℝ) ≤ |((g 1 0 : ℤ) : ℝ)| := by exact_mod_cast h2
    have h3 : (1 : ℝ) ≤ |((g 1 0 : ℤ) : ℝ)| * |((g 1 0 : ℤ) : ℝ)| :=
      le_trans h2' (le_mul_of_one_le_left (abs_nonneg _) h2')
    rw [← sq] at h3
    rwa [sq_abs] at h3
  linarith

/-- An element of `SL(2,ℤ)` with vanishing bottom-left entry is (up to sign) a translation:
it maps `τ` to `τ + m` for the integer `m` determined by its entries. -/
private lemma exists_int_vadd_of_entries_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h10 : g 1 0 = 0) (τ : ℍ) : ∃ m : ℤ, g • τ = (m : ℝ) +ᵥ τ := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have hh := g.2
    rw [Matrix.det_fin_two] at hh
    exact hh
  rw [h10, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h00, h11⟩ | ⟨h00, h11⟩
  · refine ⟨g 0 1, ?_⟩
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd]
    simp only [h10, h00, h11, map_zero, map_one]
    push_cast
    ring_nf
    rfl
  · refine ⟨-(g 0 1), ?_⟩
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd]
    simp only [h10, h00, h11, map_zero, map_neg, map_one]
    push_cast
    ring_nf
    rfl

/-- **The `j`-invariant separates the disc of radius `29/20` around a funnel point.**
If `τ` lies in the funnel `𝒟 ∩ {Im ≥ 2}` and `ζ` is within distance `29/20` of `τ`, then
`j τ = j ζ` holds exactly for `ζ ∈ {τ, τ + 1, τ - 1}`. -/
theorem jInvariantFun_eq_iff_disc {τ ζ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) : (Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun ζ ↔ ζ = τ ∨ ζ = (1 : ℝ) +ᵥ τ ∨ ζ = (-1 : ℝ) +ᵥ τ) := by
  constructor
  · intro h
    -- `j τ = j ζ` makes the two points conjugate under `SL(2,ℤ)`
    obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
    have hg : γ⁻¹ • τ = ζ := by rw [← hγ]; simp
    have h10 := entries_zero_of_smul_close (γ⁻¹) hτ.2 hζ hg
    obtain ⟨m, hm⟩ := exists_int_vadd_of_entries_zero (γ⁻¹) h10 τ
    have hζm : ζ = (m : ℝ) +ᵥ τ := by rw [← hg, hm]
    -- the integer `m` is bounded by the distance
    have hcoe : (ζ : ℂ) - (τ : ℂ) = (m : ℂ) := by
      rw [hζm, UpperHalfPlane.coe_vadd]; push_cast; ring
    have hnorm : ‖(ζ : ℂ) - (τ : ℂ)‖ = |(m : ℝ)| := by rw [hcoe]; simp
    have hmabs : |(m : ℝ)| ≤ 29 / 20 := by rw [← hnorm]; exact hζ
    have hm2 : |m| < (2 : ℤ) := by
      have h1 : ((|m| : ℤ) : ℝ) < 2 := by rw [Int.cast_abs]; linarith
      exact_mod_cast h1
    have hmcases : m = 0 ∨ m = 1 ∨ m = -1 := by
      have := abs_lt.mp hm2
      omega
    rcases hmcases with h0 | h1 | h1
    · left; rw [hζm, h0]; simp
    · right; left; rw [hζm, h1]; norm_num
    · right; right; rw [hζm, h1]; norm_num
  · rintro (rfl | h | h)
    · rfl
    · rw [h]; exact (Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ).symm
    · rw [h]
      have hw : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
        rw [← vadd_assoc]; simp
      have h2 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
      rw [hw] at h2
      exact h2

end Work.Asymptotics.SpikeCircle
