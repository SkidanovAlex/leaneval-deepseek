import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs

namespace Work.FIChain

/-- Change of variables `t = c / u` in the truncated Möbius integral
`∫_X^c ρ(c; t) / t dt`: the substitution `t ↦ c / t` is an antitone diffeomorphism of
`(0, ∞)` mapping `[X, c]` onto `[1, c / X]`, and the Jacobian `-c / t²` together with the
factor `1 / t` produces exactly the factor `1 / u` on the other side.

This is the integral form of the reciprocity `ρ(c; c/u) = -μ(c) ρ(c; u)` (`rhoTrunc_recip`)
used in the `S3plusC` route, but here it is the *exact* identity of the reciprocal substitution. -/
lemma integral_rhoTrunc_recip_subst (c X : ℕ) (hX : 1 ≤ X) (hXc : X ≤ c) :
    ∫ t in (X : ℝ)..(c : ℝ), Submission.ASP.rhoTrunc c t / t
      = ∫ u in (1 : ℝ)..((c : ℝ) / (X : ℝ)), Submission.ASP.rhoTrunc c (c / u) / u := by
  have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hcpos : (0:ℝ) < (c:ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hXne : (X:ℝ) ≠ 0 := hXpos.ne'
  have hcne : (c:ℝ) ≠ 0 := hcpos.ne'
  have hqpos : (0:ℝ) < (c:ℝ)/(X:ℝ) := div_pos hcpos hXpos
  have hmem : ∀ u ∈ Set.uIcc (1:ℝ) ((c:ℝ)/(X:ℝ)), (0:ℝ) < u := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    have hm : (0:ℝ) < min (1:ℝ) ((c:ℝ)/(X:ℝ)) := lt_min one_pos hqpos
    rcases hu with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact lt_of_lt_of_le hm (le_trans (min_le_left _ _) h1)
    · exact lt_of_lt_of_le hm (le_trans (min_le_right _ _) h1)
  have hcont : ContinuousOn (fun u : ℝ => (c:ℝ)/u) (Set.uIcc (1:ℝ) ((c:ℝ)/(X:ℝ))) :=
    ContinuousOn.div continuousOn_const continuousOn_id (fun u hu => (hmem u hu).ne')
  have hderiv : ∀ x ∈ Set.Ioo (min (1:ℝ) ((c:ℝ)/(X:ℝ))) (max (1:ℝ) ((c:ℝ)/(X:ℝ))),
      HasDerivAt (fun u : ℝ => (c:ℝ)/u) (-((c:ℝ)/x^2)) x := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    have hxpos : (0:ℝ) < x := lt_trans (lt_min one_pos hqpos) hx.1
    have hxne : x ≠ 0 := hxpos.ne'
    have hd : HasDerivAt (fun u : ℝ => (c:ℝ)/u) ((0 * x - (c:ℝ) * 1)/x^2) x :=
      (hasDerivAt_const x (c:ℝ)).div (hasDerivAt_id x) hxne
    have heq : (0 * x - (c:ℝ) * 1)/x^2 = -((c:ℝ)/x^2) := by ring
    rw [heq] at hd
    exact hd
  have hnonpos : ∀ x ∈ Set.Ioo (min (1:ℝ) ((c:ℝ)/(X:ℝ))) (max (1:ℝ) ((c:ℝ)/(X:ℝ))),
      -((c:ℝ)/x^2) ≤ 0 := by
    intro x hx
    have : (0:ℝ) ≤ (c:ℝ)/x^2 := div_nonneg hcpos.le (sq_nonneg x)
    linarith
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (g := fun t : ℝ => Submission.ASP.rhoTrunc c t / t) hcont hderiv hnonpos
  simp only [Function.comp_apply] at hsub
  have hL : (∫ x in (1:ℝ)..((c:ℝ)/(X:ℝ)),
        (fun t : ℝ => Submission.ASP.rhoTrunc c t / t) ((c:ℝ)/x) * (-((c:ℝ)/x^2)))
      = -(∫ x in (1:ℝ)..((c:ℝ)/(X:ℝ)), Submission.ASP.rhoTrunc c ((c:ℝ)/x) / x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxne : x ≠ 0 := (hmem x hx).ne'
    field_simp
  have hR : (∫ u in (c:ℝ)/1..(c:ℝ)/((c:ℝ)/(X:ℝ)), Submission.ASP.rhoTrunc c u / u)
      = -(∫ t in (X:ℝ)..(c:ℝ), Submission.ASP.rhoTrunc c t / t) := by
    rw [show (c:ℝ)/1 = (c:ℝ) by simp]
    rw [show (c:ℝ)/((c:ℝ)/(X:ℝ)) = (X:ℝ) by field_simp]
    exact intervalIntegral.integral_symm (X:ℝ) (c:ℝ)
  rw [hL, hR] at hsub
  have hmain : (∫ x in (1:ℝ)..((c:ℝ)/(X:ℝ)), Submission.ASP.rhoTrunc c ((c:ℝ)/x) / x)
      = ∫ t in (X:ℝ)..(c:ℝ), Submission.ASP.rhoTrunc c t / t := neg_injective hsub
  exact hmain.symm

end Work.FIChain
