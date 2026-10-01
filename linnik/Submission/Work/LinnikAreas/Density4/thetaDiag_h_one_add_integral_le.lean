import Mathlib

open MeasureTheory

namespace Work.LinnikAreas.Density4

/-- Splitting the integral of `x ^ (σ - 1) * exp (-x / A)` over `(0, ∞)` into the pieces
`(0, 1]` and `(1, ∞)`, and using that on `(0, 1]` the integrand is at least `exp (-1 / A)`. -/
theorem thetaDiag_h_one_add_integral_le (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 0 < A) :
    Real.exp (-(1:ℝ)/A) + ∫ x in Set.Ioi (1:ℝ), x^(σ-1) * Real.exp (-x/A)
      ≤ ∫ x in Set.Ioi (0:ℝ), x^(σ-1) * Real.exp (-x/A) := by
  set f : ℝ → ℝ := fun x => x ^ (σ - 1) * Real.exp (-x / A) with hf
  have hAinv : (0:ℝ) < 1/A := by positivity
  -- The full integral over `(0, ∞)` is a Gamma value, hence non-zero: this gives integrability.
  have hval : ∫ x in Set.Ioi (0:ℝ), f x = (1/(1/A))^σ * Real.Gamma σ := by
    rw [hf]
    have hcongr : (fun x : ℝ => x ^ (σ - 1) * Real.exp (-x / A))
        = fun x : ℝ => x ^ (σ - 1) * Real.exp (-((1/A) * x)) := by
      funext x
      congr 1
      ring_nf
    rw [hcongr]
    exact Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hAinv
  have hInt0 : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (by rw [hval]; positivity)
  have hInt01 : MeasureTheory.IntegrableOn f (Set.Ioc (0:ℝ) 1) :=
    hInt0.mono_set Set.Ioc_subset_Ioi_self
  have hInt1 : MeasureTheory.IntegrableOn f (Set.Ioi (1:ℝ)) :=
    hInt0.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hunion : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2) <;> linarith
    · intro hx
      rcases lt_or_ge (1:ℝ) x with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
  -- Decompose the integral over `(0, ∞)`.
  have hsplit : ∫ x in Set.Ioi (0:ℝ), f x
      = (∫ x in Set.Ioc (0:ℝ) 1, f x) + ∫ x in Set.Ioi (1:ℝ), f x := by
    have h := MeasureTheory.setIntegral_union (f := f) (s := Set.Ioc (0:ℝ) 1)
      (t := Set.Ioi (1:ℝ)) (μ := volume) hdisj measurableSet_Ioi hInt01 hInt1
    rwa [hunion] at h
  -- Pointwise lower bound on `(0, 1]`.
  have hb : ∀ x ∈ Set.Ioc (0:ℝ) 1, Real.exp (-(1:ℝ)/A) ≤ f x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxpos : 0 < x := hx0
    have hp : (1:ℝ) ≤ x ^ (σ - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hxpos hx1 (by linarith)
    have he : Real.exp (-(1:ℝ)/A) ≤ Real.exp (-x / A) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (neg_le_neg hx1) hA.le
    calc Real.exp (-(1:ℝ)/A) = 1 * Real.exp (-(1:ℝ)/A) := by ring
      _ ≤ x ^ (σ - 1) * Real.exp (-x / A) :=
          mul_le_mul hp he (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg hxpos.le _)
  have hge : Real.exp (-(1:ℝ)/A) ≤ ∫ x in Set.Ioc (0:ℝ) 1, f x := by
    have h := MeasureTheory.setIntegral_ge_of_const_le (μ := volume)
      (s := Set.Ioc (0:ℝ) 1) (f := f) (c := Real.exp (-(1:ℝ)/A))
      measurableSet_Ioc measure_Ioc_lt_top.ne hb hInt01
    rw [Real.volume_real_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
    simp only [sub_zero, one_smul] at h
    exact h
  linarith [hsplit, hge]

end Work.LinnikAreas.Density4
