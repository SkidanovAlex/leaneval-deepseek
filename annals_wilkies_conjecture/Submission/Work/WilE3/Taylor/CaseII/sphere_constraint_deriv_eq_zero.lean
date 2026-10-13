import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem sphere_constraint_deriv_eq_zero {k : ℕ} {y : Fin k → ℝ} {δ : ℝ}
    {γ : ℝ → Fin k → ℝ} {c : ℝ}
    (hγc : DifferentiableAt ℝ γ c)
    (hev : Filter.Eventually (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2 = δ ^ 2) (nhds c)) :
    ∑ i, (γ c i - y i) * deriv γ c i = 0 := by
  -- The function `s ↦ ∑ i, (γ s i - y i)²` is eventually constant near `c`, hence has derivative `0` at `c`.
  have hconst : (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2) =ᶠ[nhds c] fun _ => δ ^ 2 := hev
  have hd0 : deriv (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2) c = 0 := by
    rw [hconst.deriv_eq]
    simp
  -- Coordinatewise differentiability of `γ` at `c`, via the projection `(Fin k → ℝ) →L[ℝ] ℝ`.
  have hcomp : ∀ i : Fin k, HasDerivAt (fun s : ℝ => γ s i) (deriv γ c i) c := by
    intro i
    have h2 := ((ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)).comp c hγc.hasFDerivAt).hasDerivAt
    have hfun : (⇑(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) ∘ γ)
        = fun s : ℝ => γ s i := by
      funext s; exact ContinuousLinearMap.proj_apply i (γ s)
    have hval : ((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) ∘SL (fderiv ℝ γ c)) 1
        = deriv γ c i := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]; rfl
    rw [hfun, hval] at h2
    exact h2
  -- Derivative of the summand `s ↦ (γ s i - y i)²`.
  have hsq : ∀ i : Fin k,
      HasDerivAt (fun s : ℝ => (γ s i - y i) ^ 2) (2 * (γ c i - y i) * deriv γ c i) c := by
    intro i
    have hs := ((hcomp i).sub (hasDerivAt_const c (y i))).pow 2
    have hfe : ((fun s : ℝ => γ s i) - fun _ => y i) ^ 2 = (fun s : ℝ => (γ s i - y i) ^ 2) := by
      funext s; simp
    rw [hfe] at hs
    simpa using hs
  -- Derivative of the whole sum.
  have hg : HasDerivAt (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2)
      (∑ i, 2 * (γ c i - y i) * deriv γ c i) c := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hsq i)
    have hfun : (∑ i : Fin k, (fun s : ℝ => (γ s i - y i) ^ 2))
        = (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2) := by
      funext s; simp
    rw [hfun] at h
    exact h
  -- Compare with `hd0` and cancel the factor `2`.
  have hsum : ∑ i, 2 * (γ c i - y i) * deriv γ c i = 0 := by
    rw [← hg.deriv]; exact hd0
  have h2 : 2 * (∑ i, (γ c i - y i) * deriv γ c i) = 0 := by
    rw [Finset.mul_sum]
    simpa [mul_assoc] using hsum
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end Work.WilE3.Taylor.CaseII
