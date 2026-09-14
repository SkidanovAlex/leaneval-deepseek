import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Commons.Analysis.Calculus.contDiffOn_pairSum_inv_dist
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.Calculus

/-- The set of collision-free configurations `{x | ∀ i j, i ≠ j → xᵢ ≠ xⱼ}` is open in the
configuration space `EuclideanSpace E (Fin N)`. -/
theorem isOpen_setOf_pairwise_ne {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} :
    IsOpen {x : EuclideanSpace E (Fin N) | ∀ i j, i ≠ j → x i ≠ x j} := by
  have hp : ∀ i j : Fin N, IsOpen {x : EuclideanSpace E (Fin N) | x i ≠ x j} := by
    intro i j
    have hc : Continuous fun x : EuclideanSpace E (Fin N) => (x i, x j) := by fun_prop
    have ho : IsOpen {p : E × E | p.1 ≠ p.2} := isClosed_diagonal.isOpen_compl
    exact ho.preimage hc
  have hset : {x : EuclideanSpace E (Fin N) | ∀ i j, i ≠ j → x i ≠ x j}
      = ⋂ j : Fin N, ⋂ i ∈ Finset.Iio j, {x | x i ≠ x j} := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_Iio]
    constructor
    · intro h j i hij
      exact h i j (ne_of_lt hij)
    · intro h i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact h j i hlt
      · exact (h i j hgt).symm
  rw [hset]
  exact isOpen_iInter_of_finite (fun j => isOpen_biInter_finset (fun i _ => hp i j))

/-- The Fréchet derivative of the Newtonian pair potential is uniformly bounded on compact
collision-free sets. -/
theorem exists_bound_fderiv_pairSum_inv_dist {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ} {m : Fin N → ℝ}
    {K : Set (EuclideanSpace E (Fin N))} (hK : IsCompact K)
    (hK' : ∀ x ∈ K, ∀ i j, i ≠ j → x i ≠ x j) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖fderiv ℝ (fun y : EuclideanSpace E (Fin N) =>
        Finset.sum Finset.univ fun j => Finset.sum (Finset.Iio j) fun i =>
          m i * m j * (dist (y i) (y j))⁻¹) x‖ ≤ C := by
  let f : EuclideanSpace E (Fin N) → ℝ := fun y =>
    Finset.sum Finset.univ fun j => Finset.sum (Finset.Iio j) fun i =>
      m i * m j * (dist (y i) (y j))⁻¹
  let s : Set (EuclideanSpace E (Fin N)) := {x | ∀ i j, i ≠ j → x i ≠ x j}
  have hs : IsOpen s := isOpen_setOf_pairwise_ne
  have hKs : K ⊆ s := fun x hx => hK' x hx
  have hf : ContDiffOn ℝ (1 : WithTop ℕ∞) f s :=
    (contDiffOn_pairSum_inv_dist (E := E) (N := N) (m := m)).of_le (by simp)
  have hcont : ContinuousOn (fderiv ℝ f) s :=
    FDeriv.continuousOn_fderiv hs hf
  have hcontK : ContinuousOn (fderiv ℝ f) K := hcont.mono hKs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (E := EuclideanSpace E (Fin N) →L[ℝ] ℝ) hcontK
  exact ⟨C, fun x hx => hC x hx⟩

end Commons.Analysis.Calculus
