import Mathlib
import Submission.Commons.Algebra.Lie.PBW.standardMonomial_spanning
import Submission.Commons.Algebra.Lie.PBW.standardMonomial_linearIndependent

universe u

namespace Commons.Algebra.Lie.PBW

/-- **Poincaré–Birkhoff–Witt: the standard-monomial basis of the universal enveloping
algebra.**

Let `L` be a Lie algebra over a field `K` of characteristic zero with an ordered basis
`e : ι → L` (`Module.Basis`, `ι` linearly ordered).  Writing `U = UniversalEnvelopingAlgebra
K L`, the standard monomials are the products, in `U`, of the images
`UniversalEnvelopingAlgebra.ι K (e i)` over the nondecreasing words `w : List ι`
(`w.Pairwise (fun a b : ι => a ≤ b)`).  They form a `K`-basis of `U`.

* spanning: `Commons.Algebra.Lie.PBW.standardMonomial_spanning`;
* linear independence: `Commons.Algebra.Lie.PBW.standardMonomial_linearIndependent`;
  assembled via `Module.Basis.mk`. -/
theorem standardMonomial_basis (K L ι : Type u) [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LinearOrder ι]
    (e : Module.Basis ι K L) :
    ∃ b : Module.Basis {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} K
          (UniversalEnvelopingAlgebra K L),
      ∀ w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)},
        b w = (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod := by
  let v : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} → UniversalEnvelopingAlgebra K L :=
    fun w => (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← standardMonomial_spanning K L ι e]
    refine le_of_eq ?_
    congr 1
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, hw.symm⟩
  refine ⟨Module.Basis.mk (v := v) (standardMonomial_linearIndependent K L ι e) hsp, ?_⟩
  intro w
  rw [Module.Basis.mk_apply]

end Commons.Algebra.Lie.PBW
