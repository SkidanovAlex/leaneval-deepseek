import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

open Finsupp

/-- A finitely generated submodule of the free module `X →₀ R` is contained in the span of
the standard basis vectors indexed by a finite subset of `X`: take the union of the supports
of a finite generating set. -/
theorem exists_finset_span_finsupp {R : Type*} [Ring R] (X : Type*) [DecidableEq X]
    (W : Submodule R (X →₀ R)) (hW : W.FG) :
    ∃ X₀ : Finset X, W ≤ Submodule.span R {x | ∃ i ∈ X₀, x = Finsupp.single i (1 : R)} := by
  rw [Submodule.FG] at hW
  obtain ⟨S, hS⟩ := hW
  refine ⟨S.biUnion fun f => f.support, ?_⟩
  rw [← hS, Submodule.span_le]
  intro f hf
  have hmem : ∀ i ∈ f.support, Finsupp.single i (f i) ∈
      Submodule.span R {x : X →₀ R | ∃ i ∈ S.biUnion (fun f => f.support),
        x = Finsupp.single i 1} := by
    intro i hi
    have hiX : i ∈ S.biUnion (fun f => f.support) := Finset.mem_biUnion.mpr ⟨f, hf, hi⟩
    have : Finsupp.single i (f i) = (f i) • (Finsupp.single i (1 : R)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hiX, rfl⟩)
  have hsum : f.sum (fun i r => Finsupp.single i r) ∈
      Submodule.span R {x : X →₀ R | ∃ i ∈ S.biUnion (fun f => f.support),
        x = Finsupp.single i 1} := by
    apply Submodule.sum_mem
    intro i hi
    exact hmem i hi
  rwa [Finsupp.sum_single] at hsum

end Work.ORCoherence.Tensor
