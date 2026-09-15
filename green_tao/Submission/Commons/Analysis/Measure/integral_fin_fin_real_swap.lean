import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Measure

/-- Fubini–Tonelli type exchange of the order of integration for a function on
`(Fin m → ℝ) × (Fin m → ℝ) × ℝ` with respect to the Lebesgue measures. -/
theorem integral_fin_fin_real_swap {m : ℕ} (Ψ : (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℂ)
    (h : MeasureTheory.Integrable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
        Ψ p.1.1 p.1.2 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, ∫ t : ℝ, Ψ w w' t)
      = ∫ t : ℝ, ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, Ψ w w' t := by
  -- Integrability of the `w`-integral of `Ψ`, as a function of `(w, w')`.
  have key1 : MeasureTheory.Integrable
      (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ∫ t : ℝ, Ψ p.1 p.2 t)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) :=
    MeasureTheory.Integrable.integral_prod_left h
  -- Integrability of `Ψ` as a function of the pair `((w, w'), t)`.
  have key2 : MeasureTheory.Integrable
      (Function.uncurry (fun p : (Fin m → ℝ) × (Fin m → ℝ) => fun t : ℝ => Ψ p.1 p.2 t))
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    show MeasureTheory.Integrable (fun z : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
          Ψ z.1.1 z.1.2 z.2) _
    exact h
  -- The two iterated integrals over the pair `(w, w')` agree a.e. in `t`.
  have h_ae : (fun t : ℝ => ∫ p : (Fin m → ℝ) × (Fin m → ℝ), Ψ p.1 p.2 t
        ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
      =ᵐ[MeasureTheory.volume]
        (fun t : ℝ => ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, Ψ w w' t) := by
    filter_upwards [MeasureTheory.Integrable.prod_left_ae h] with t ht
    exact (MeasureTheory.integral_integral
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (f := fun w w' => Ψ w w' t) ht).symm
  -- Fubini on the pair `(w, w')`.
  have step1 :
      (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, ∫ t : ℝ, Ψ w w' t)
      = ∫ z : (Fin m → ℝ) × (Fin m → ℝ),
          (∫ t : ℝ, Ψ z.1 z.2 t)
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) :=
    MeasureTheory.integral_integral
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (f := fun w w' => ∫ t : ℝ, Ψ w w' t) key1
  -- Fubini swapping the pair `(w, w')` with `t`.
  have step2 :
      (∫ z : (Fin m → ℝ) × (Fin m → ℝ),
          (∫ t : ℝ, Ψ z.1 z.2 t)
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
      = ∫ t : ℝ,
          (∫ p : (Fin m → ℝ) × (Fin m → ℝ), Ψ p.1 p.2 t
            ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
              (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.integral_integral_swap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun p t => Ψ p.1 p.2 t) key2
  -- Replace the a.e. equal integrands.
  have step3 :
      (∫ t : ℝ,
          (∫ p : (Fin m → ℝ) × (Fin m → ℝ), Ψ p.1 p.2 t
            ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
              (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
      = ∫ t : ℝ, ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, Ψ w w' t :=
    MeasureTheory.integral_congr_ae h_ae
  exact step1.trans (step2.trans step3)

end Commons.Analysis.Measure