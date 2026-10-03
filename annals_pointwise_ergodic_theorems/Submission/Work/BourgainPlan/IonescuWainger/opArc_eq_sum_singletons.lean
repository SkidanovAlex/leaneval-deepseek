import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

noncomputable section

/-- The symbol identity behind `opArc_eq_sum_singletons`: the `L^∞(𝕋)`-class of the arc symbol
`Σ_{β ∈ E} φ(· − β)` is the sum of the classes of the single-frequency symbols `φ(· − β)`. -/
theorem arcSymbolLp_eq_sum_singletons (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) :
    arcSymbolLp φ hφ E = ∑ β ∈ E, arcSymbolLp φ hφ {β} := by
  have hcoe : (↑↑(∑ β ∈ E, arcSymbolLp φ hφ {β}) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ E := by
    refine (Lp.coeFn_finsetSum E (fun β => arcSymbolLp φ hφ {β})).trans ?_
    have hsum : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)), ∀ β ∈ E,
        (↑↑(arcSymbolLp φ hφ {β}) : Circle → ℂ) ξ = φ (ξ - β) :=
      (Finset.eventually_all E).mpr (fun β _ => by
        filter_upwards [arcSymbolLp_coeFn φ hφ {β}] with ξ h
        rw [h, arcSymbol_apply, Finset.sum_singleton])
    filter_upwards [hsum] with ξ hξ
    rw [Finset.sum_apply, arcSymbol_apply]
    exact Finset.sum_congr rfl fun β hβ => hξ β hβ
  exact Lp.ext ((arcSymbolLp_coeFn φ hφ E).trans hcoe.symm)

/-- The arc multipliers decompose over the elements of an arc set: `Op_{φ;E} = Σ_{β ∈ E} Op_{φ;{β}}`.  In the corpus's `ℓ²(ℤ) ≅ L²(𝕋)` picture `opArc φ hφ E` is the multiplier with symbol `Σ_{β ∈ E} φ(· − β) = Σ_{β ∈ E} arcSymbol φ {β}`, so this is the additivity of `opArc` in the *symbol* (`opMul_finset_sum`, already available) applied to the pointwise identity `arcSymbol φ E = Σ_{β ∈ E} arcSymbol φ {β}` (both sides are `Σ_{β ∈ E} φ(· − β)`, since `arcSymbol φ {β} = φ(· − β)` by `arcSymbol_apply` + `Finset.sum_singleton`).  The reusable intermediate is the `L^∞(𝕋)` identity `arcSymbolLp φ hφ E = Σ_{β ∈ E} (1 : ℂ) • arcSymbolLp φ hφ {β}` (proved as in `opArc_strata_incl_excl` via `Lp.ext`, `Lp.coeFn_fun_finsetSum` and `arcSymbolLp_coeFn`).  Needed for the step "apply the lower bound `ortho-apply`(i) to the hypersystem `ε_A Op_{m;Σ_A}f`": there the pieces are the single-frequency multipliers `Op_{m;α}f = opArc m hφ {α}` and the strata sums `Op_{m;Σ_A} = Σ_{α ∈ Σ_A} opArc m hφ {α}`. -/
theorem opArc_eq_sum_singletons (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf
      = ∑ β ∈ E, Work.BourgainPlan.IonescuWainger.opArc φ hφ {β} f hf := by
  have hLp := arcSymbolLp_eq_sum_singletons φ hφ E
  simp only [opArc]
  rw [hLp]
  have hsum := opMul_finset_sum E (fun _ => (1 : ℂ)) (fun β => arcSymbolLp φ hφ {β}) f hf
  simp only [one_smul] at hsum
  rw [hsum]

end

end Work.BourgainPlan.IonescuWainger
