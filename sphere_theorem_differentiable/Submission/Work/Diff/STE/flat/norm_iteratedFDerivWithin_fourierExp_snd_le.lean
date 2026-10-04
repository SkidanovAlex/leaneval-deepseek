import Mathlib
import Submission.Work.Diff.STE.contDiff_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Derivative bound for the Fourier character as a function of the second variable

`q ↦ fourierExp m q.2` is the Fourier character `fourierExp m` composed with the projection
`Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)`.  The projection is a linear contraction, so the
`k`-th iterated derivative of the composite is bounded by the `k`-th iterated derivative of
`fourierExp m`, which was estimated in `Work.Diff.STE.norm_iteratedFDeriv_fourierExp_le` by
`(2π Σᵢ |mᵢ|)^k`.  Since the function is smooth everywhere, its `within`-iterated derivative on a
set with `UniqueDiffOn` coincides with the iterated derivative.
-/

namespace Work.Diff.STE.flat

open ContinuousMultilinearMap ContinuousLinearMap

theorem norm_iteratedFDerivWithin_fourierExp_snd_le
    {n : ℕ} (m : Fin n → ℤ) (s : Set (ℝ × (Fin n → ℝ))) (hs : UniqueDiffOn ℝ s)
    (k : ℕ) (p : ℝ × (Fin n → ℝ)) (hp : p ∈ s) :
    ‖iteratedFDerivWithin ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) s p‖
      ≤ (2 * Real.pi * ∑ i, |((m i : ℤ) : ℝ)|) ^ k := by
  set g : ℝ × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ) with hg
  -- the composite is smooth everywhere
  have hgsmooth : ContDiff ℝ ⊤ (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) := by
    have h := (Work.Diff.STE.contDiff_fourierExp_top m).comp g.contDiff
    simpa [g, Function.comp_def] using h
  -- `within`-iterated derivative = iterated derivative at a smooth point
  have hwithin : iteratedFDerivWithin ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) s p
      = iteratedFDeriv ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) p :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs (hgsmooth.contDiffAt.of_le le_top) hp
  -- chain rule with the (contracting) projection
  have hcomp : iteratedFDeriv ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) p
      = (iteratedFDeriv ℝ k (Work.Diff.STE.fourierExp m) p.2).compContinuousLinearMap
          (fun _ : Fin k => g) := by
    have h := ContinuousLinearMap.iteratedFDeriv_comp_right g
      (Work.Diff.STE.contDiff_fourierExp_top m) p (i := k) le_top
    simpa [g, Function.comp_def] using h
  calc ‖iteratedFDerivWithin ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) s p‖
      = ‖iteratedFDeriv ℝ k
        (fun q : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp m q.2) p‖ := by rw [hwithin]
    _ = ‖(iteratedFDeriv ℝ k (Work.Diff.STE.fourierExp m) p.2).compContinuousLinearMap
          (fun _ : Fin k => g)‖ := by rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ k (Work.Diff.STE.fourierExp m) p.2‖ * ∏ _ : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k (Work.Diff.STE.fourierExp m) p.2‖ := by
        have hp1 : ∏ _ : Fin k, ‖g‖ ≤ 1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [hg]
          exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin n → ℝ))
        exact mul_le_of_le_one_right (norm_nonneg _) hp1
    _ ≤ (2 * Real.pi * ∑ i, |((m i : ℤ) : ℝ)|) ^ k :=
        Work.Diff.STE.norm_iteratedFDeriv_fourierExp_le m k p.2

end Work.Diff.STE.flat
