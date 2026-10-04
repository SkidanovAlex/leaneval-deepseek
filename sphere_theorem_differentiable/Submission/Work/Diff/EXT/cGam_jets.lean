import Mathlib
import Submission.Work.Diff.EXT.chartData_step_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jet bounds for the chart Christoffel symbols at time `t`

`Work.Diff.EXT.cGam_jets`: the `k`-jets of the chart Christoffel symbols `cGam (G t)` (composed with
the chart coordinate `pt`) are bounded on `K` uniformly in `t ∈ Ico σ T`, given the `k`-jets of

* the background Christoffel symbols `cGam (G 0)`,
* the inverse Gram matrix `GramInv`,
* the chart array `aComp` of the lowered connection difference.

The proof is the pointwise algebraic identity (proved in `chartData_step_aux`, `cGam_eq_cGam0_add`)

`Γ^l_{ij}(G t) = Γ^l_{ij}(G 0) + ∑_k GramInv^{lk}(G t) · aComp_{kij}`,

valid on the whole chart target because `GramM` is always invertible there
(`gramM_det_ne_zero_target`), together with the Leibniz rule for iterated Fréchet derivatives.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem cGam_jets
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hdet : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det)
    (hcGam0 : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (hGInv : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (pt (I := I) x₀ y') i j) y‖ ≤ C)
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C)
    (hsm0 : ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y)
    (hsmGInv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramInv G x₀ t
        (pt (I := I) x₀ y') i j) y)
    (hsmA : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ C := by
  classical
  obtain ⟨C0, hC00, hC0⟩ := exists_uniform_bound_of_le
    (P := fun m C => ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (fun m C C' h hle y hy i j l => le_trans (h y hy i j l) hle) k hcGam0
  obtain ⟨CI, hCI0, hCI⟩ := hGInv
  obtain ⟨CA, hCA0, hCA⟩ := hA
  set B : ℝ := max CI CA with hBdef
  have hB0 : 0 ≤ B := le_trans hCI0 (le_max_left _ _)
  have hCIB : CI ≤ B := le_max_left _ _
  have hCAB : CA ≤ B := le_max_right _ _
  refine ⟨2 * max C0 ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B)), ?_, ?_⟩
  · have h1 : 0 ≤ (Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B) := by positivity
    have h2 : C0 ≤ max C0 ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B)) :=
      le_max_left _ _
    linarith
  · intro t ht y hy m hm i j l
    have hident : (fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') l i j)
        =ᶠ[𝓝 y] fun y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') l i j
          + ∑ k' : Fin (Module.finrank ℝ E), Work.Diff.GE.GramInv G x₀ t
              (pt (I := I) x₀ y') l k' * aComp (I := I) (M := M) G x₀ t y' i j k' := by
      filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds (hKt hy)] with y' hy'
      exact cGam_eq_cGam0_add G x₀ t y' (gramM_det_ne_zero_target G x₀ t hy') l i j
    have hsmg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ k' : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') l k'
          * aComp (I := I) (M := M) G x₀ t y' i j k') y :=
      ContDiffAt.sum fun k' _ => ContDiffAt.mul (hsmGInv t ht y hy l k') (hsmA t ht y hy i j k')
    have hsum : ‖iteratedFDeriv ℝ m (fun y' : E => ∑ k' : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') l k'
          * aComp (I := I) (M := M) G x₀ t y' i j k') y‖
        ≤ (Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B) := by
      refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (φ := fun k' y' => Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') l k'
          * aComp (I := I) (M := M) G x₀ t y' i j k')
        (x := y) (n := m) (C := (2 : ℝ) ^ k * B * B) ?_ ?_) ?_
      · intro k' _
        exact ContDiffAt.mul (hsmGInv t ht y hy l k') (hsmA t ht y hy i j k')
      · intro k' _
        exact norm_iteratedFDeriv_mul_le_at_le hm (hsmGInv t ht y hy l k') (hsmA t ht y hy i j k')
          hB0 (fun i' hi' => le_trans (hCI t ht y hy i' hi' l k') hCIB)
          (fun i' hi' => le_trans (hCA t ht y hy i' hi' i j k') hCAB)
      · simp
    have hconv : ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (pt (I := I) x₀ y') l i j) y‖
        = ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') l i j
            + ∑ k' : Fin (Module.finrank ℝ E), Work.Diff.GE.GramInv G x₀ t
                (pt (I := I) x₀ y') l k'
                * aComp (I := I) (M := M) G x₀ t y' i j k') y‖ := by
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hident m).eq_of_nhds]
    rw [hconv]
    refine norm_iteratedFDeriv_add_le_at (n := m)
      (C := max C0 ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B)))
      (hsm0 y hy i j l) hsmg ?_ ?_
    · calc ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
            (pt (I := I) x₀ y') l i j) y‖ ≤ C0 := hC0 m hm y hy i j l
        _ ≤ max C0 ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B)) := le_max_left _ _
    · calc ‖iteratedFDeriv ℝ m (fun y' : E => ∑ k' : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') l k'
                * aComp (I := I) (M := M) G x₀ t y' i j k') y‖
            ≤ (Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B) := hsum
        _ ≤ max C0 ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * B * B)) := le_max_right _ _

end Work.Diff.EXT
