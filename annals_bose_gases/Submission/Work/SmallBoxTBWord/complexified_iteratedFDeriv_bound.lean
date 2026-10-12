import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open scoped ContDiff Topology

/--
Local boundedness of the iterated Fréchet derivatives (up to order `3`) of the
complexification of a smooth real-valued function on a finite product of
Euclidean spaces, uniformly on the box `{y | ∀ j, ‖y j‖ ≤ S}`.

The box is compact (a finite product of closed balls in a proper space) and each
`y ↦ iteratedFDeriv ℝ k F y` is continuous (as `F` is `C^∞`), so on the box the
norm of every iterated derivative is bounded by a constant `M k ≥ 0`. -/
theorem complexified_iteratedFDeriv_bound {N : ℕ} {S : ℝ} (hS : 0 ≤ S)
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ M : ℕ → ℝ, (∀ k, 0 ≤ M k) ∧ ∀ k ≤ 3, ∀ y : Fin N → EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin N, ‖y j‖ ≤ S) →
      ‖iteratedFDeriv ℝ k (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => (Φ y : ℂ)) y‖ ≤ M k := by
  have _hS := hS
  -- The complexification of `Φ` is still `C^∞` (it is `Φ` composed with the
  -- real-linear isometry `ℝ → ℂ`).
  have hF : ContDiff ℝ (⊤ : ENat) (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hΦ
  -- The box is a finite product of closed balls, hence compact.
  have hK : IsCompact
      (Set.univ.pi (fun _ : Fin N => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) S)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall 0 S)
  -- Every iterated derivative is continuous, so bounded on the compact box.
  have hbound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Set.univ.pi (fun _ : Fin N => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) S),
        ‖iteratedFDeriv ℝ k (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => (Φ y : ℂ)) y‖ ≤ C := by
    intro k
    have hcont : Continuous (fun y : Fin N → EuclideanSpace ℝ (Fin 3) =>
        iteratedFDeriv ℝ k (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => (Φ y : ℂ)) y) :=
      ContDiff.continuous_iteratedFDeriv (n := (⊤ : ENat)) (by exact_mod_cast le_top) hF
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hK hcont.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun y hy => le_trans (hC y hy) (le_max_left _ _)⟩
  choose M hM using hbound
  refine ⟨M, fun k => (hM k).1, ?_⟩
  intro k _hk y hy
  refine (hM k).2 y ?_
  rw [Set.mem_univ_pi]
  intro j
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa using hy j

end Work.SmallBoxTBWord
