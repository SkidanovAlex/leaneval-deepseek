import Mathlib
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.Diff.STE.B3.integrableOn_Rpair_term
import Submission.Work.Diff.STE.B3.Pair
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Work.Diff.STE.B3

/-- **`BPair` is additive in a sum of reconstructions.**  For continuous component families
`u i` and a section `k` whose chart matrices are continuous on `{χ j ≠ 0}`,

  `BPair (Σ_i R_i* (u i)) k = Σ_i CPair_i (u i) (R_i k)`.

This is the assembly step that lets the Friedrichs mollifier `J ρ ε h = Σ_i R_i* (S_ε (R_i h))` be
paired against a section `k`: `BPair` unfolds to `Σ_j CPair_j (R_j ·) (R_j k)`, `R_j` is pointwise
linear in its section argument, and each summand of the resulting double sum is integrable by
`Work.Diff.STE.B3.integrableOn_Rpair_term`; exchanging the two finite sums turns the outer sum over
`j` into `BPair (R_i* (u i)) k`, which the adjunction
`Work.Diff.STE.B3.BPair_Rstar` rewrites as `CPair_i (u i) (R_i k)`. -/
theorem BPair_J_lin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (u : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (u i a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0}) :
    D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ i, Work.Diff.STE.B3Data.CPair i (u i) (D.R i k) := by
  classical
  -- the uniform two-sided bound on the density, needed for the integrability inputs
  obtain ⟨c, C, hc, hC, hdens⟩ := dens_bound_sigma D
  -- (1) `R j` is pointwise linear in its section argument: the chart matrix is the evaluation of
  -- the section, and evaluation is additive.
  have hRlin : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      D.R j (∑ i, D.Rstar i (u i)) a b z = ∑ i, D.R j (D.Rstar i (u i)) a b z := by
    intro j a b z
    simp only [B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]
  -- (2) each summand of the resulting double sum is integrable on the centred cube
  have hint : ∀ (j i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      IntegrableOn (fun z => D.R j (D.Rstar i (u i)) a b z * D.R j k a b z)
        (B3Data.centreCube (E := E)) volume :=
    fun j i a b =>
      integrableOn_Rpair_term D i (u i) k (hu i) hk ⟨c, C, hc, hC, hdens⟩ j a b
  -- (3) additivity of `CPair` in its first argument
  have hlin : ∀ j : ι₀,
      B3Data.CPair j (D.R j (∑ i, D.Rstar i (u i))) (D.R j k)
        = ∑ i, B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) := by
    intro j
    simp only [B3Data.CPair]
    have h1 : ∀ a b : Fin (Module.finrank ℝ E),
        ∫ z in B3Data.centreCube,
            D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z
          = ∑ i, ∫ z in B3Data.centreCube,
              D.R j (D.Rstar i (u i)) a b z * D.R j k a b z := by
      intro a b
      rw [show (fun z => D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z)
            = (fun z => ∑ i, D.R j (D.Rstar i (u i)) a b z * D.R j k a b z) from by
          funext z; rw [hRlin j a b z, Finset.sum_mul]]
      exact integral_finsetSum Finset.univ (fun i _ => hint j i a b)
    calc ∑ a, ∑ b, ∫ z in B3Data.centreCube,
            D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z
        = ∑ a, ∑ b, ∑ i, ∫ z in B3Data.centreCube,
            D.R j (D.Rstar i (u i)) a b z * D.R j k a b z :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
      _ = ∑ i, ∑ a, ∑ b, ∫ z in B3Data.centreCube,
            D.R j (D.Rstar i (u i)) a b z * D.R j k a b z := by
          rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
          exact Finset.sum_comm
  -- (4) assemble: unfold `BPair`, apply (3), exchange the finite sums, fold `BPair` again and
  -- invoke the adjunction `BPair_Rstar` chart by chart.
  calc D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ j, B3Data.CPair j (D.R j (∑ i, D.Rstar i (u i))) (D.R j k) := rfl
    _ = ∑ j, ∑ i, B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) :=
          Finset.sum_congr rfl (fun j _ => hlin j)
    _ = ∑ i, ∑ j, B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) := Finset.sum_comm
    _ = ∑ i, D.BPair (D.Rstar i (u i)) k := rfl
    _ = ∑ i, B3Data.CPair i (u i) (D.R i k) :=
          Finset.sum_congr rfl (fun i _ => BPair_Rstar D i (u i) k (hu i) hk)

end Work.Diff.STE.B3
