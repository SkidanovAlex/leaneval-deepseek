import Mathlib
import Submission.Work.Peluse.Ulower.ss74.lemma74Dense

namespace Work.Peluse.Ulower.StepLe

/-- The conclusion mass `concMass` of the sharp dual--difference interchange, specialised to the
slice family `G z = sl P f₀ f₁ (z+1)` of Peluse's dual function, is the sum over the cube set
`□_σ(H₁) = ThetaSet σ D H₁` of the squared moduli of the `B⁻¹`-normalised correlations of the
*slice dual functions* `sliceDual σ N P f₀ f₁ (k.2.1, k.2.2)` at the cube-difference phase
`mixedPhase β k`.

This is purely the pointwise identity "the cube term of the average of the slices is the average of
the cube terms of the slices", i.e. `Work.Peluse.Ulower.ss74.mean_cubeTerm_eq_dualFn`
(`E_{y ∈ [N]} cubeTerm sh (sl · y) = dualFn N P (Δ'_sh f₀) (Δ'_sh f₁)`), applied inside the
`x`-sum and multiplied by the phase factor `e(ψ(k)x)`. -/
theorem concMass_sl {σ N D B : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) :
    Work.Peluse.Ulower.StepLe.concMass σ D B
        (fun z : Fin N => Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) H₁ β =
      ∑ k ∈ Work.Peluse.Ulower.ThetaSet σ D H₁,
        ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
          Work.Peluse.Ulower.StepLe.sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
            Complex.exp (2 * Real.pi * Complex.I * (Work.Peluse.Ulower.StepLe.mixedPhase β k : ℂ) * (x : ℂ))‖ ^ 2 := by
  rw [Work.Peluse.Ulower.StepLe.concMass]
  simp only [Fintype.card_fin]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  -- the pointwise identity `E_{y∈[N]} cubeTerm sh (sl · y) = sliceDual … sh`
  have hmean := Work.Peluse.Ulower.ss74.mean_cubeTerm_eq_dualFn (σ := σ) hN P f₀ f₁ k
  have hmean' : ∀ x : ℤ, ((N : ℂ))⁻¹ * ∑ z : Fin N,
      Work.Peluse.cubeTerm k.2.1 k.2.2 (Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) x
      = Work.Peluse.Ulower.StepLe.sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x := by
    intro x
    have h := congrFun hmean x
    simp only [Work.Peluse.Ulower.StepLe.sliceDual]
    exact h
  -- the whole `x`-summands agree, hence so do the sums and their norms
  have hfun : (fun x : ℤ => ((N : ℂ))⁻¹ * ∑ z : Fin N,
        (Work.Peluse.cubeTerm k.2.1 k.2.2 (Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) x *
          Complex.exp (2 * Real.pi * Complex.I *
            (Work.Peluse.Ulower.StepLe.mixedPhase β k : ℂ) * (x : ℂ))))
      = fun x : ℤ => Work.Peluse.Ulower.StepLe.sliceDual σ N P f₀ f₁
          (fun i => (k.2.1 i, k.2.2 i)) x *
          Complex.exp (2 * Real.pi * Complex.I *
            (Work.Peluse.Ulower.StepLe.mixedPhase β k : ℂ) * (x : ℂ)) := by
    funext x
    rw [← Finset.sum_mul, ← mul_assoc, hmean' x]
  rw [hfun]

end Work.Peluse.Ulower.StepLe
