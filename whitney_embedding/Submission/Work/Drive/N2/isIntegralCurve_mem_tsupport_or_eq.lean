import Mathlib
import Submission.Work.ODE.CompactSupportBounds

set_option autoImplicit false

/-!
# An integral curve of a compactly supported field never leaves the support

Let `Y : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)` be a smooth vector field with
compact support and let `γ : ℝ → EuclideanSpace ℝ (Fin N)` be a global integral curve of `Y`.
Then for every `t` the point `γ t` lies in the topological support of `Y`, unless `γ` is the
constant curve through `γ 0`.

The mathematical content is the uniqueness of solutions of the autonomous ODE `γ' = Y ∘ γ`:
* if `Y (γ t) ≠ 0` then `γ t ∈ Function.support Y ⊆ tsupport Y`;
* if `Y (γ t) = 0` then the constant curve `s ↦ γ t` is another integral curve passing through
  `γ t` at time `t`, so by uniqueness `γ` is constant and in particular `γ t = γ 0`.

Uniqueness in the form used below needs a global Lipschitz constant for `Y`, which is supplied by
`Work.ODE.exists_lipschitzWith_of_contDiff_hasCompactSupport` from the smoothness and the
compact support of `Y`.
-/

open scoped Topology

namespace Work.Drive.N2

/-- If an integral curve `γ` of an autonomous field `Y` passes through a zero of `Y` at time `t`,
then `γ` is the constant curve with value `γ t`. -/
theorem isIntegralCurve_eq_const_of_apply_eq_zero {N : ℕ}
    (Y : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hL : ∃ L : NNReal, LipschitzWith L Y)
    (γ : ℝ → EuclideanSpace ℝ (Fin N)) (hγ : IsIntegralCurve γ (fun _ z => Y z))
    (t : ℝ) (ht : Y (γ t) = 0) : γ = fun _ => γ t := by
  obtain ⟨L, hL⟩ := hL
  refine ODE_solution_unique_univ (v := fun _ z => Y z) (s := fun _ => Set.univ)
    (K := L) (f := γ) (g := fun _ => γ t) (t₀ := t) (fun s => hL.lipschitzOnWith) ?_ ?_ rfl
  · exact fun s => ⟨hγ s, trivial⟩
  · exact fun s => ⟨ht.symm ▸ hasDerivAt_const s (γ t), trivial⟩

theorem isIntegralCurve_mem_tsupport_or_eq {N : ℕ}
    (Y : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y) (hc : HasCompactSupport Y)
    (γ : ℝ → EuclideanSpace ℝ (Fin N)) (hγ : IsIntegralCurve γ (fun _ z => Y z)) :
    ∀ t, γ t ∈ tsupport Y ∨ γ t = γ 0 := by
  obtain ⟨L, hL⟩ :=
    Work.ODE.exists_lipschitzWith_of_contDiff_hasCompactSupport (hY.of_le (by simp)) hc
  intro t
  by_cases h : γ t ∈ tsupport Y
  · exact Or.inl h
  · refine Or.inr ?_
    have h0 : Y (γ t) = 0 :=
      Function.notMem_support.mp fun hmem => h (subset_closure hmem)
    have hconst := isIntegralCurve_eq_const_of_apply_eq_zero Y ⟨L, hL⟩ γ hγ t h0
    exact (congrFun hconst 0).symm

end Work.Drive.N2
