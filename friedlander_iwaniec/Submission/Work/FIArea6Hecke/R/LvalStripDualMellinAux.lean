import Mathlib
import Submission.Work.FIArea6Hecke.R.A6HeckeDual
import Submission.Work.FIArea6Hecke.R.continuousOn_thetaDual
import Submission.Work.FIArea6Hecke.R.exists_completion_strict
import Submission.Work.FIArea6Hecke.R.latticeCubic_summable
import Submission.Work.FIArea5.S16Hecke.mellin_tsum_exp

namespace Work.FIArea6Hecke.R

open MeasureTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Mellin transform of the dual theta function.**  For `re s > 1`,
`mellin (thetaDual d χ) s = Γ(s)·π^{-s}·Σ_ξ ĝ(ξ)·λ_ξ^{-s}` with `λ_ξ = ξ₁² + ξ₂²` (the Mellin
transform of the exponential series, term by term, via `hasSum_mellin`). -/
theorem mellin_thetaDual (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0)
    {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable (fun ξ : ℤ × ℤ => (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-s.re)))) :
    mellin (thetaDual d chi) s =
      Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
        (∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
          ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s))) := by
  have hs0 : 0 < s.re := by linarith
  set a : ℤ × ℤ → ℂ := fun ξ => Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ with ha
  set p : ℤ × ℤ → ℝ := fun ξ => Real.pi * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) with hp
  have hbd : ∀ ξ : ℤ × ℤ, ‖a ξ‖ ≤ (4 * (d : ℝ)) ^ 2 := by
    intro ξ
    have h := thetaDualGaussBound_aux d hb ⟨ξ.1, ξ.2⟩
    have he : (((4 * d : ℕ) : ℝ)) ^ 2 = (4 * (d : ℝ)) ^ 2 := by push_cast; ring
    rw [ha]; rw [he] at h; exact h
  have hppos : ∀ ξ : ℤ × ℤ, ξ ≠ 0 → 0 < p ξ := by
    intro ξ hξ
    have hlampos : 0 < (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by
      have hz : ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) = 0 → ξ = 0 := by
        intro h
        have h1 : (ξ.1 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (ξ.1 : ℝ), sq_nonneg (ξ.2 : ℝ)]
        have h2 : (ξ.2 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (ξ.1 : ℝ), sq_nonneg (ξ.2 : ℝ)]
        have h1' : ξ.1 = 0 := by exact_mod_cast sq_eq_zero_iff.mp h1
        have h2' : ξ.2 = 0 := by exact_mod_cast sq_eq_zero_iff.mp h2
        exact Prod.ext h1' h2'
      rcases lt_trichotomy ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) 0 with h | h | h
      · nlinarith [sq_nonneg (ξ.1 : ℝ), sq_nonneg (ξ.2 : ℝ)]
      · exact absurd (hz h) hξ
      · exact h
    rw [hp]
    positivity
  have hz : ∀ ξ : ℤ × ℤ, a ξ = 0 ∨ 0 < p ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · left
      subst hξ
      rw [ha]
      exact h0
    · exact Or.inr (hppos ξ hξ)
  -- the `HasSum` representation of `thetaDual`
  have hHas : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun ξ : ℤ × ℤ => a ξ * (Real.exp (-p ξ * t) : ℂ)) (thetaDual d chi t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hdom : Summable (fun ξ : ℤ × ℤ =>
        Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * t))) :=
      thetaDualDominated_aux t ht0
    have hbb : ∀ ξ : ℤ × ℤ,
        ‖a ξ * (Real.exp (-p ξ * t) : ℂ)‖
          ≤ (4 * (d : ℝ)) ^ 2 *
              Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * t)) := by
      intro ξ
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      have hexp : Real.exp (-p ξ * t)
          = Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * t)) := by
        rw [hp]; congr 1; ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right (hbd ξ) (Real.exp_nonneg _)
    have hsummable : Summable (fun ξ : ℤ × ℤ => a ξ * (Real.exp (-p ξ * t) : ℂ)) :=
      Summable.of_norm_bounded (hdom.mul_left ((4 * (d : ℝ)) ^ 2)) hbb
    have htsum : (∑' ξ : ℤ × ℤ, a ξ * (Real.exp (-p ξ * t) : ℂ)) = thetaDual d chi t := by
      rw [thetaDual]
      refine tsum_congr (fun ξ => ?_)
      simp only [ha]
      congr 1
      rw [Complex.ofReal_exp, hp]
      congr 1
      push_cast
      ring
    rw [← htsum]
    exact hsummable.hasSum
  -- summability of `‖a ξ‖ / p ξ ^ s.re`
  have hsum2 : Summable (fun ξ : ℤ × ℤ => ‖a ξ‖ / p ξ ^ s.re) := by
    have hbase : Summable (fun ξ : ℤ × ℤ => ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-s.re)) := hsum
    have hbase' : Summable (fun ξ : ℤ × ℤ => (4 * (d : ℝ)) ^ 2 / p ξ ^ s.re) := by
      refine (hbase.mul_left ((4 * (d : ℝ)) ^ 2 * Real.pi ^ (-s.re))).congr (fun ξ => ?_)
      rcases eq_or_ne ξ 0 with hξ | hξ
      · subst hξ
        rw [hp]
        simp [Real.zero_rpow (ne_of_gt hs0), Real.zero_rpow (by linarith : (-s.re) ≠ 0)]
      · have hlamnn : (0 : ℝ) ≤ (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by positivity
        rw [hp, Real.mul_rpow Real.pi_pos.le hlamnn, div_eq_mul_inv, mul_inv,
          Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hlamnn]
        ring
    exact Summable.of_nonneg_of_le
      (fun ξ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (fun ξ => div_le_div_of_nonneg_right (hbd ξ) (Real.rpow_nonneg (by positivity) _))
      hbase'
  have hml := hasSum_mellin hz hs0 hHas hsum2
  have hml_eq : mellin (thetaDual d chi) s
      = (∑' ξ : ℤ × ℤ, Complex.Gamma s * a ξ / (↑(p ξ)) ^ s) := hml.tsum_eq.symm
  rw [hml_eq]
  have hterm : (∑' ξ : ℤ × ℤ, Complex.Gamma s * a ξ / (↑(p ξ)) ^ s)
      = (Complex.Gamma s * (Real.pi : ℂ) ^ (-s)) *
        (∑' ξ : ℤ × ℤ, a ξ * ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s))) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun ξ => ?_)
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      have ha0 : a 0 = 0 := by rw [ha]; exact h0
      have hp0 : p 0 = 0 := by rw [hp]; simp
      rw [ha0, hp0]
      simp
    · have hlamnn : (0 : ℝ) ≤ (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by positivity
      have hple : (↑(p ξ) : ℂ) = (Real.pi : ℂ) * ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ)) : ℂ) := by
        rw [hp]; push_cast; ring
      rw [hple, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hlamnn s, div_eq_mul_inv,
        mul_inv, Complex.cpow_neg, Complex.cpow_neg]
      ring
  rw [hterm]

/-- **Mellin transform of `thetaDualG`**, the rescaled dual theta function. -/
theorem mellin_thetaDualG' {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0)
    {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable (fun ξ : ℤ × ℤ => (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-s.re)))) :
    mellin (thetaDualG d chi) s =
      (Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
        (((16 * (d : ℝ) ^ 2 : ℝ)) : ℂ) ^ s *
        (Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
          (∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)))) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0; omega
  set A : ℝ := 16 * (d : ℝ) ^ 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set c : ℂ := (Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) with hc
  have h1 : thetaDualG d chi = fun x : ℝ => c * thetaDual d chi (x / A) := by
    funext x
    rw [thetaDualG, hc, hA]
  have hcA : ((((A⁻¹ : ℝ)) : ℂ) ^ (-s)) = (((A : ℝ) : ℂ) ^ s) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hApos.le]; exact Real.pi_ne_zero.symm),
      Complex.cpow_neg, inv_inv]
  have h2 : mellin (fun x : ℝ => c * thetaDual d chi (x / A)) s
      = c * (((A : ℝ) : ℂ) ^ s * mellin (thetaDual d chi) s) := by
    have hsm : (fun x : ℝ => c * thetaDual d chi (x / A))
        = fun x : ℝ => c • thetaDual d chi (x / A) := by
      funext x; rw [smul_eq_mul]
    rw [hsm, mellin_const_smul, smul_eq_mul]
    congr 1
    have hAinv : 0 < A⁻¹ := inv_pos.mpr hApos
    have h := mellin_comp_mul_left (thetaDual d chi) s (a := A⁻¹) hAinv
    have heq : (fun t : ℝ => thetaDual d chi (A⁻¹ * t))
        = fun x : ℝ => thetaDual d chi (x / A) := by
      funext t; congr 1; rw [inv_mul_eq_div]
    rw [heq, smul_eq_mul] at h
    rw [h, hcA]
  rw [h1, h2, mellin_thetaDual d hd hb h0 hs hsum]
  rw [hc, hA]
  ring

end

end Work.FIArea6Hecke.R
