import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.n0SpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Regrouping a sum over all finite subsets of `Fin N` by cardinality, with an arbitrary weight
`g` of the cardinality: the fibres `{S | S.card = k}`, `k ∈ range (N+1)`, partition the whole
`Finset.univ` (every subset of `Fin N` has at most `N` elements). -/
theorem n0FunOp_eq_sum_card_aux {N : ℕ} (g : ℝ → ℝ) (φ : Finset (Fin N) → ℝ) :
    (∑ k ∈ Finset.range (N + 1),
        g (k : ℝ) * (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => S.card = k), φ S))
      = ∑ S : Finset (Fin N), g (S.card : ℝ) * φ S := by
  have hcard : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))),
      S.card ∈ Finset.range (N + 1) := by
    intro S _
    rw [Finset.mem_range]
    have h1 : S.card ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact Nat.lt_succ_of_le h1
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N + 1))
        (g := fun S : Finset (Fin N) => S.card) (f := fun S => g (S.card : ℝ) * φ S) hcard]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [Finset.mem_filter] at hS
  rw [hS.2]

theorem n0FunOp_eq_sum_card {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : ℝ → ℝ) (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1S.n0FunOp volA A g Ψ
      = fun x => ∑ S : Finset (Fin N), g (S.card : ℝ) * (Work.BoseFixB1S.n0ProjOp volA A S Ψ x) := by
  funext x
  simp only [Work.BoseFixB1S.n0FunOp, Work.BoseFixB1S.n0LagrangeOp]
  exact n0FunOp_eq_sum_card_aux g (fun S => Work.BoseFixB1S.n0ProjOp volA A S Ψ x)

end Work.BoseFixB1S
