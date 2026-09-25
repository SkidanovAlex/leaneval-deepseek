import Mathlib
import Submission.Work.ConCohomology.Connecting
import Submission.Work.ConCohomology.exact_H2_A

set_option linter.unusedVariables false

namespace Work.ConCohomology

/-- The composite `H²(G,A) → H²(G,B)` is injective as soon as `H¹(G,C)` is trivial: by exactness
at `H²(G,A)` the kernel of the coefficient change map `H2Map S.f` is the image of the connecting
homomorphism `δ¹ : H¹(G,C) → H²(G,A)`, and the image of a trivial group is trivial.

(The hypothesis `Subsingleton (H¹(G,B))` is not needed for this particular statement; it is part of
the surrounding five-term exactness package.) -/
theorem kummer_H2_injective {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (hB : Subsingleton (H1 G B)) (hC : Subsingleton (H1 G C)) :
    Function.Injective (H2Map S.f) := by
  -- The image of the connecting map is a single point, and it contains `0` because the kernel of
  -- `H2Map S.f` does; hence it is `{0}`.
  have hzero : ∀ y : H1 G C, connecting1 S y = (0 : H2 G A) := by
    intro y
    obtain ⟨y', hy'⟩ := (exact_H2_A S (0 : H2 G A)).mp (map_zero (H2Map S.f))
    rwa [@Subsingleton.elim (H1 G C) hC y' y] at hy'
  intro x y hxy
  have hdiff : H2Map S.f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨c, hc⟩ := (exact_H2_A S (x - y)).mp hdiff
  rw [@Subsingleton.elim (H1 G C) hC c (0 : H1 G C), hzero 0] at hc
  exact sub_eq_zero.mp hc.symm

end Work.ConCohomology
