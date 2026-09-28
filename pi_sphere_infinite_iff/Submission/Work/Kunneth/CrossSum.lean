import Mathlib
import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.Basic

/-!
# The source of the cohomological Künneth isomorphism

The cohomological Künneth theorem of this chapter says that `Hⁿ(X × Y; ℤ)` is
`⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)`, the isomorphism being the cross product
`a × b = π₁^* a ⌣ π₂^* b` (`Work.Kunneth.crossHLin`).  This file fixes the names for the
source of that isomorphism:

* `Work.Kunneth.cohomSummand X Y p q` — the summand `Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)`;
* `Work.Kunneth.kunnethTarget X Y n` — the source `⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)`, spelled as
  the finite product over the index type `tpIdx n`;
* `Work.Kunneth.tpIdx.instFintype` — finiteness of `tpIdx n` (it is in bijection with
  `Fin (n+1)`).

Both abbreviations are stated with the *tensor product of `ModuleCat`-objects* (the monoidal
structure of `ModuleCat`), matching the rest of the chapter (`TensorDefs`, `Tensor`, `TensorCo`).
See `Submission/Work/Kunneth/README.md` for the (delicate) instance conventions of the chapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct BigOperators

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The bidegree index set of total degree `n` is finite (it is in bijection with `Fin (n+1)`). -/
instance tpIdx.instFintype (n : ℕ) : Fintype (tpIdx n) :=
  Fintype.ofInjective (fun pq : tpIdx n => (⟨pq.1.1, by have h := pq.2; omega⟩ : Fin (n + 1)))
    (by
      intro a b hab
      have h1 : a.1.1 = b.1.1 := Fin.ext_iff.mp hab
      apply Subtype.ext
      apply Prod.ext
      · exact h1
      · have ha := a.2
        have hb := b.2
        omega)

/-- The `(p,q)`-summand `Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)` of the source of the cross product. -/
abbrev cohomSummand (X Y : SSet) (p q : ℕ) : Type :=
  ↥((Work.Cohomology.cochainC ℤ X).homology p
    ⊗ (Work.Cohomology.cochainC ℤ Y).homology q)

/-- The source of the cohomological Künneth isomorphism, `⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)`. -/
abbrev kunnethTarget (X Y : SSet) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (∀ pq : tpIdx n, cohomSummand X Y pq.1.1 pq.1.2)

end

end Work.Kunneth
