import Mathlib
import Submission.Work.Cohomology.Mesh

namespace Work.Cohomology

/-- **Support of the push-forward of affine chains.**

`pushLC n k C c` is the `ℤ`-linear combination `∑_{v ∈ C.support} C v • v_*(c)` of the `affComp v`
push-forwards of `c`.  Consequently its support is contained in the union, over `v ∈ C.support`
and `u ∈ c.support`, of the composed vertex families `affComp v u`. -/
theorem support_pushLC (n k : ℕ) (C : LinChain n n) (c : LinChain n k)
    (w : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (hw : w ∈ (pushLC n k C c).support) :
    ∃ v ∈ C.support, ∃ u ∈ c.support, w = affComp v u := by
  classical
  -- `pushLC n k C c` evaluates to the `Finsupp.sum` of the pushed-forward summands.
  have hpow : pushLC n k C c
      = C.sum (fun v a =>
          a • Finsupp.mapDomain (affComp (N := n) (k := n) (j := k) v) c) := by
    rw [pushLC, Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply]
  rw [hpow] at hw
  -- Support of a `Finsupp.sum` is contained in the union of the supports of the summands,
  -- and each summand is a scalar multiple of `mapDomain (affComp v) c`.
  have h1 : (C.sum (fun v a =>
        a • Finsupp.mapDomain (affComp (N := n) (k := n) (j := k) v) c)).support
      ⊆ C.support.biUnion (fun v =>
          c.support.image (affComp (N := n) (k := n) (j := k) v)) := by
    refine Finsupp.support_sum.trans ?_
    apply Finset.biUnion_mono
    intro v _
    exact (Finsupp.support_smul).trans Finsupp.mapDomain_support
  have hw2 := h1 hw
  rw [Finset.mem_biUnion] at hw2
  obtain ⟨v, hvC, hwim⟩ := hw2
  rw [Finset.mem_image] at hwim
  obtain ⟨u, hu, hwu⟩ := hwim
  exact ⟨v, hvC, u, hu, hwu.symm⟩

end Work.Cohomology
