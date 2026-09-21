import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs
import Submission.Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv

namespace Work.Analysis.Abel

/-- **Joint smoothness of the parametrized `u`-derivatives.**
If the uncurried `(u,σ) ↦ A u σ` is `C^∞` on an open set `U ⊆ ℝ × ℝ`, then so is the map
`(u,σ) ↦ pder A j u σ`, the `j`-th iterated derivative of the slice `u ↦ A u σ` (taken in the
first variable, second variable held fixed), as a function of the pair `(u,σ)`.
Suggested route: apply `Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv`
(`import Submission.Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv`) to the
transpose `Ã x y = A y x` on the swapped open set, then compose with the coordinate swap,
noting `pder A j u σ = iteratedDeriv j (fun v => A v σ) u` and
`iteratedDeriv j (fun v => Ã σ v) u = iteratedDeriv j (fun v => A v σ) u`. -/
theorem contDiffOn_pder_param {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) U) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => pder A j q.1 q.2) U := by
  -- The coordinate swap, which is a linear (hence smooth) self-map of `ℝ × ℝ`.
  have hswap : ContDiff ℝ (⊤ : ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).contDiff
  -- The swapped open set on which the transposed kernel is smooth.
  have hV : IsOpen (Prod.swap ⁻¹' U : Set (ℝ × ℝ)) := hU.preimage continuous_swap
  have hA' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => A p.2 p.1) (Prod.swap ⁻¹' U) :=
    ContDiffOn.comp hA hswap.contDiffOn (fun p hp => hp)
  -- Smoothness of the parametrized iterated derivative on the swapped set.
  have hstep : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => iteratedDeriv j (fun v : ℝ => A v p.1) p.2) (Prod.swap ⁻¹' U) :=
    Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv (F := fun x y => A y x)
      (k := j) hV hA'
  -- Compose back with the coordinate swap.
  have hback : ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × ℝ => iteratedDeriv j (fun v : ℝ => A v p.1) p.2) ∘ Prod.swap) U :=
    ContDiffOn.comp hstep hswap.contDiffOn (fun p hp => hp)
  refine hback.congr (fun p _ => ?_)
  simp [pder, Function.comp]

end Work.Analysis.Abel
