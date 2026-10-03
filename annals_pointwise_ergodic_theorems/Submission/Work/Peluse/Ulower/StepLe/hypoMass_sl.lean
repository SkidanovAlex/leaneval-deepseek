import Mathlib
import Submission.Work.Peluse.Ulower.ss74.lemma74Dense

namespace Work.Peluse.Ulower.StepLe

open scoped BigOperators

/-- Reindexing the `Fin N`-sum `∑_{z : Fin N} g (z + 1)` as the interval sum `∑_{y ∈ [1,N]} g y`. -/
private lemma sum_fin_succ_eq_sum_Icc (N : ℕ) (g : ℕ → ℂ) :
    (∑ z : Fin N, g (z.1 + 1)) = ∑ y ∈ Finset.Icc 1 N, g y := by
  have h : ∀ n : ℕ, (∑ i ∈ Finset.range n, g (i + 1)) = ∑ y ∈ Finset.Icc 1 n, g y := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ (fun i => g (i + 1)) m,
            Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) g, ih]
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1)) N]
  exact h N

/-- The average of the slices `sl P f₀ f₁ y`, `y ∈ {1,…,N}`, is exactly the dual function
`dualFn N P f₀ f₁` (definitionally: `dualFn` is the average of its slices). -/
private lemma mean_sl_eq_dualFn (N : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) :
    (fun x : ℤ => ((N : ℂ))⁻¹ * ∑ z : Fin N, Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) x)
      = Work.Peluse.dualFn N P f₀ f₁ := by
  funext x
  simp only [Work.Peluse.dualFn]
  congr 1
  simp only [Work.Peluse.Ulower.sl]
  exact sum_fin_succ_eq_sum_Icc N
    (fun y => f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)))

/-- The hypothesis mass `hypoMass` of the interchange, specialised to the slices
`G z = sl P f₀ f₁ (z + 1)` of the dual function, is the sum over `p ∈ H₁` of the squares of the
cube amplitudes of `dualFn N P f₀ f₁`:
```
hypoMass σ B (fun z : Fin N => sl P f₀ f₁ (z.1+1)) H₁ β
  = ∑ p ∈ H₁, (cubeAmp B (dualFn N P f₀ f₁) β p.1 p.2)^2 .
```
This is purely a matter of the pointwise identity `mean_sl_eq_dualFn`. -/
theorem hypoMass_sl {σ N B : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) :
    Work.Peluse.Ulower.StepLe.hypoMass σ B
        (fun z : Fin N => Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) H₁ β =
      ∑ p ∈ H₁, (Work.Peluse.Ulower.StepLe.cubeAmp B (Work.Peluse.dualFn N P f₀ f₁) β p.1 p.2) ^ 2 := by
  have hfun : (fun y : ℤ => ((Fintype.card (Fin N) : ℂ))⁻¹ *
        ∑ z : Fin N, Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) y)
      = Work.Peluse.dualFn N P f₀ f₁ := by
    have := mean_sl_eq_dualFn N P f₀ f₁
    simpa [Fintype.card_fin] using this
  unfold Work.Peluse.Ulower.StepLe.hypoMass Work.Peluse.Ulower.StepLe.cubeAmp
  apply Finset.sum_congr rfl
  intro p hp
  show ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm p.1 p.2
        (fun y : ℤ => ((Fintype.card (Fin N) : ℂ))⁻¹ * ∑ z : Fin N,
          Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) y) x *
        Complex.exp (2 * Real.pi * Complex.I * (β p.1 p.2 : ℂ) * (x : ℂ))‖ ^ 2
      = ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm p.1 p.2
        (Work.Peluse.dualFn N P f₀ f₁) x *
        Complex.exp (2 * Real.pi * Complex.I * (β p.1 p.2 : ℂ) * (x : ℂ))‖ ^ 2
  rw [hfun]

end Work.Peluse.Ulower.StepLe
