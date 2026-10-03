import Mathlib

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory

/-- The complement of `Ioc c d` inside `Icc c d` is contained in the single point `c`. -/
private lemma torsionIcc_diff_Ioc_subset (c d : ℝ) : Set.Icc c d \ Set.Ioc c d ⊆ {c} := by
  intro x hx
  rw [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc] at hx
  simp only [Set.mem_singleton_iff]
  rcases hx with ⟨⟨h1, h2⟩, h3⟩
  by_contra hne
  exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩

/-- If `f` vanishes off the symmetric interval `Icc (-c) c` and that interval is contained in
`[a,b]`, then the interval integral of `f` over `[a,b]` agrees with the integral over `ℝ`.
(The only points of `Icc (-c) c` possibly missed by `Ioc a b` lie in the null set `{a}`.) -/
private lemma torsionIntervalIntegral_eq_integral {f : ℝ → ℂ} {c a b : ℝ}
    (hc : 0 ≤ c) (ha : a ≤ -c) (hb : c ≤ b)
    (h : ∀ x : ℝ, x ∉ Set.Icc (-c) c → f x = 0) :
    ∫ x in a..b, f x = ∫ x, f x := by
  have hab : a ≤ b := ha.trans ((by linarith : -c ≤ c).trans hb)
  rw [intervalIntegral.integral_of_le hab]
  have hvan : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc a b → f x = 0 := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (MeasureTheory.measure_singleton a)
    intro x hx
    rw [Set.mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxs, hfx⟩ := hx
    have hxIcc : x ∈ Set.Icc (-c) c := by
      by_contra hc'
      exact hfx (h x hc')
    have hxIcc2 : x ∈ Set.Icc a b := ⟨ha.trans hxIcc.1, hxIcc.2.trans hb⟩
    exact torsionIcc_diff_Ioc_subset a b ⟨hxIcc2, hxs⟩
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s := Set.Ioc a b) (f := f) hvan]

/-- **Change of variables for the torsion kernel.**  If `m` is supported in `[-(1/2Q), 1/2Q]`
(`Q ≥ 1`), then the Fourier-type integral of the dilated symbol `m(·/Q)` at frequency `N` on the
interval `[-1/2, 1/2]` equals `Q` times the integral of `m` itself at frequency `QN`:

`∫_{-1/2}^{1/2} m(ξ/Q) e^{2πi N ξ} dξ = Q · ∫_{-1/2}^{1/2} m(ξ) e^{2πi (QN) ξ} dξ`.

This is the substitution `ξ = Q u`, which moves the integration interval to `[-1/(2Q), 1/(2Q)]`
— on which `m` is exactly supported — and then the support condition lets that interval be
enlarged back to `[-1/2, 1/2]`. -/
theorem torsion_kernel_changevar {Q : ℕ} (hQ : 1 ≤ Q) (m : ℝ → ℂ) (hmi : MeasureTheory.Integrable m)
    (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m ξ = 0)
    (N : ℤ) :
    (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
        m (ξ / (Q : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * ((N : ℂ) * (ξ : ℂ))))
      = (Q : ℂ) * ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
          m ξ * Complex.exp (2 * Real.pi * Complex.I * (((Q : ℤ) * N : ℤ) : ℂ) * (ξ : ℂ)) := by
  have _hmi : MeasureTheory.Integrable m := hmi
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have hQc : (Q : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]
    exact_mod_cast hQne
  have hle : (1 : ℝ) / (2 * (Q : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set F : ℝ → ℂ := fun u =>
    m u * Complex.exp (2 * Real.pi * Complex.I * ((((Q : ℤ) * N : ℤ)) : ℂ) * (u : ℂ)) with hF
  have hL : (∫ x in (-(1 / (2 * (Q : ℝ))))..(1 / (2 * (Q : ℝ))), F x) = ∫ x, F x := by
    refine torsionIntervalIntegral_eq_integral (c := 1 / (2 * (Q : ℝ)))
      (a := -(1 / (2 * (Q : ℝ)))) (b := 1 / (2 * (Q : ℝ))) ?_ ?_ ?_ ?_
    · positivity
    · exact le_refl _
    · exact le_refl _
    · intro x hx
      simp only [hF, hmsupp x hx, zero_mul]
  have hR : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), F x) = ∫ x, F x := by
    refine torsionIntervalIntegral_eq_integral (c := 1 / (2 * (Q : ℝ)))
      (a := -(1 / 2)) (b := 1 / 2) ?_ ?_ ?_ ?_
    · positivity
    · exact neg_le_neg hle
    · exact hle
    · intro x hx
      have hx' : x ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) := by
        intro hmem
        exact hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      simp only [hF, hmsupp x hx', zero_mul]
  have hstep1 : (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
        m (ξ / (Q : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * ((N : ℂ) * (ξ : ℂ))))
      = ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), F (ξ / (Q : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hcore : (N : ℂ) * (x : ℂ)
        = ((((Q : ℤ) * N : ℤ)) : ℂ) * ((x / (Q : ℝ) : ℝ) : ℂ) := by
      push_cast
      field_simp
    have harg : 2 * Real.pi * Complex.I * ((N : ℂ) * (x : ℂ))
        = 2 * Real.pi * Complex.I * ((((Q : ℤ) * N : ℤ)) : ℂ) * ((x / (Q : ℝ) : ℝ) : ℂ) := by
      rw [hcore]; ring
    simp only [hF]
    rw [harg]
  rw [hstep1, intervalIntegral.integral_comp_div F hQne, Complex.real_smul,
    Complex.ofReal_natCast]
  rw [show (-(1 / 2 : ℝ)) / (Q : ℝ) = -(1 / (2 * (Q : ℝ))) by rw [neg_div, div_div],
      show ((1 / 2 : ℝ)) / (Q : ℝ) = 1 / (2 * (Q : ℝ)) by rw [div_div]]
  rw [hL, hR]

end Work.BourgainPlan.IonescuWainger
