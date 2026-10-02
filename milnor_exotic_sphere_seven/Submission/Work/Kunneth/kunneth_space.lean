import Mathlib
import Submission.Work.Kunneth.kunneth_cohomology
import Submission.Work.Kunneth.kunneth_homology
import Submission.Work.Kunneth.cpn_kunneth_hypotheses
import Submission.Work.Cohomology.singularChains_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Künneth for the singular (co)homology of a space

The Künneth theorem of §3 of the chapter (`Work.Kunneth.kunneth_cohomology`,
`Work.Kunneth.kunneth_homology`) is stated for an arbitrary simplicial set `Y`, under the three
hypotheses

`(hYt : ∀ q, Projective ℤ ↥((sChain Y).X q))`, `(hYf : ∀ q, Free ℤ ↥((sChain Y).homology q))`,
`(hYn : ∀ q, Finite ℤ ↥((sChain Y).homology q))`.

For the singular simplicial set `Y = TopCat.toSSet.obj W` of a **topological space** `W` the first
of these is automatic: the singular chain modules are free (`Work.Cohomology.singularChains_free`,
degree by degree), hence projective.  These are the two statements a consumer of the theorem in
topological form will want: `H_*(W;ℤ)` free and finitely generated in each degree is *all* that is
assumed, and no hypothesis is imposed on the first factor `X`.

## Main results

* `Work.Kunneth.kunneth_cohomology_space`
* `Work.Kunneth.kunneth_homology_space`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- The chain modules of the singular simplicial set of a space are free, hence projective: the
hypothesis `hYt` of the Künneth theorems is automatic for a space. -/
theorem singularChains_projective (W : TopCat) (q : ℕ) :
    Module.Projective ℤ ↥((sChain (TopCat.toSSet.obj W)).X q) := by
  haveI : Module.Free ℤ ↥((sChain (TopCat.toSSet.obj W)).X q) :=
    Work.Cohomology.singularChains_free W q
  exact Module.Projective.of_free

/-- **Künneth for the singular cohomology of a space**: if `H_q(W;ℤ)` is a free, finitely
generated `ℤ`-module for every `q`, then for every simplicial set `X`

`Hⁿ(X × W; ℤ) ≅ ⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(W;ℤ)`.

No hypothesis is imposed on `X`. -/
theorem kunneth_cohomology_space (X : SSet) (W : TopCat)
    (hYf : ∀ q, Module.Free ℤ ↥((sChain (TopCat.toSSet.obj W)).homology q))
    (hYn : ∀ q, Module.Finite ℤ ↥((sChain (TopCat.toSSet.obj W)).homology q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso
      ((cochainC ℤ (sProd X (TopCat.toSSet.obj W))).homology n)
      (kunnethTarget X (TopCat.toSSet.obj W) n)) :=
  kunneth_cohomology X (TopCat.toSSet.obj W) n (fun q => singularChains_projective W q) hYf hYn

/-- **Künneth for the singular homology of a space**: if `H_q(W;ℤ)` is a free, finitely generated
`ℤ`-module for every `q`, then for every simplicial set `X`

`Hₙ(X × W; ℤ) ≅ ⨁_{p+q=n} H_p(X;ℤ) ⊗ H_q(W;ℤ)`.

No hypothesis is imposed on `X`. -/
theorem kunneth_homology_space (X : SSet) (W : TopCat)
    (hYf : ∀ q, Module.Free ℤ ↥((sChain (TopCat.toSSet.obj W)).homology q))
    (hYn : ∀ q, Module.Finite ℤ ↥((sChain (TopCat.toSSet.obj W)).homology q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso
      ((tpC (sChain X) (sChain (TopCat.toSSet.obj W))).homology n)
      ((tpC (homSum (sChain X)) (homSum (sChain (TopCat.toSSet.obj W)))).X n)) := by
  have hH : ∀ q, Module.Projective ℤ ↥((sChain (TopCat.toSSet.obj W)).homology q) := fun q => by
    haveI := hYf q
    exact Module.Projective.of_free
  exact kunneth_homology (sChain X) (sChain (TopCat.toSSet.obj W))
    (fun q => singularChains_projective W q) hH n

end

end Work.Kunneth
