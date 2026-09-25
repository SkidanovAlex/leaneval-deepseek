import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function

namespace Work.BourgainPlan.IonescuWainger

/-- The Marcinkiewicz–Zygmund lift of a *single* operator bound to the square-function bound of its family: if a `ℂ`-linear, a.e.-measurable `T : (ℤ → ℂ) → (ℤ → ℂ)` obeys `‖T f‖_{ℓ^p} ≤ A‖f‖_{ℓ^p}` (in `eLpNorm`/counting-measure form), then for every finite family `F_t` the `ℓ^p(ℤ; ℓ²(κ))`-norms obey the same bound up to a constant: `‖(T(F_t))_t‖_{ℓ^p(ℓ²)} ≤ C A ‖(F_t)_t‖_{ℓ^p(ℓ²)}`.  This is `mz_square_function` with index type `ι := PUnit` (so that the Rademacher/sign average hypothesis `∫ ‖Σ_i ±T_i f‖^p ≤ A^p ∫‖f‖^p` reduces to the single-operator bound, the two signs giving `T f` and `-T f`), source and target both `ℤ` with the counting measure.  It is the `ℓ^{2r}` step of Tao's `main` ("hence by the Marcinkiewicz–Zygmund result one has `‖(Op_{m;Σ_{A₀}}F_α)_α‖_{ℓ^{2r}(ℤ;H^{Σ_{(A₀)}})} ≤ O(1)‖(F_α)_α‖`"). -/
theorem mz_family_lift {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type*} [Fintype κ]
      (T : (ℤ → ℂ) → (ℤ → ℂ)) (hlin : IsLinearMap ℂ T)
      (hmeas : ∀ f : ℤ → ℂ, AEMeasurable (T f) (MeasureTheory.Measure.count))
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ f : ℤ → ℂ, ∫⁻ n : ℤ, ‖T f n‖ₑ ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count)
      (F : κ → ℤ → ℂ),
      ∫⁻ n : ℤ, (∑ t : κ, ‖T (F t) n‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * A ^ p) *
          ∫⁻ n : ℤ, (∑ t : κ, ‖F t n‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count := by
  -- Apply the Marcinkiewicz–Zygmund square-function lemma with the one-point index type `PUnit`.
  obtain ⟨C, hCpos, hC⟩ :=
    mz_square_function (X := ℤ) (Y := ℤ) (MeasureTheory.Measure.count) (MeasureTheory.Measure.count)
      (le_of_lt hp)
  refine ⟨C, hCpos, ?_⟩
  intro κ _ T hlin hmeas A hA hT F
  -- The signed-combination hypothesis is exactly the single-operator bound: the sign is `±1`,
  -- which does not change the norm.
  have hsigned : ∀ (ε : PUnit.{1} → Bool) (f : ℤ → ℂ),
      ∫⁻ y, ‖∑ i : PUnit.{1}, (if ε i then (1 : ℂ) else -1) * (fun _ : PUnit.{1} => T) i f y‖ₑ ^ p
        ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    intro ε f
    have hfun : (fun y : ℤ => ‖∑ i : PUnit.{1}, (if ε i then (1 : ℂ) else -1)
          * (fun _ : PUnit.{1} => T) i f y‖ₑ ^ p) = fun y : ℤ => ‖T f y‖ₑ ^ p := by
      funext y
      simp only [Finset.univ_unique, Finset.sum_singleton]
      by_cases h : ε PUnit.unit = true <;> simp [h]
    rw [hfun]
    exact hT f
  have h := hC (ι := PUnit.{1}) (κ := κ) (fun _ : PUnit.{1} => T) (fun _ => hlin)
    (fun _ f => hmeas f) A hA hsigned F
  simpa only [Finset.univ_unique, Finset.sum_singleton] using h

end Work.BourgainPlan.IonescuWainger
