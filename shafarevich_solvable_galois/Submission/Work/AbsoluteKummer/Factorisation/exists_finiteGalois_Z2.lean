/-
Copyright (c) 2025. All rights reserved.

# The finite-level description of `H²`

A locally constant `2`-cochain `G_k × G_k → M` is constant on a neighbourhood of `(1,1)`, and the
Krull topology turns that neighbourhood into `fixingSubgroup L × fixingSubgroup L` for some finite
Galois `L ⊆ k̄` (`Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair`).  Hence:

* `Work.AbsoluteKummer.Factorisation.exists_finiteGalois_Z2` — **every class in `H²(G_k, M)` is
  represented by a continuous `2`-cocycle which is constant on `fixingSubgroup L × fixingSubgroup L`
  for some finite Galois `L`,** i.e. which descends to a `2`-cocycle of the finite quotient
  `Gal(L/k)`.

Together with `exists_finiteGalois_cocycle` (the `H¹` analogue) this is the "finite-level"
description of the continuous cohomology of `G_k` in low degrees: every class is visible on a
finite Galois quotient.
-/
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Factorisation

open scoped Classical
open Work.AbsoluteKummer

noncomputable section

/-- **The finite-level description of `H²(G_k, M)`**: every class is represented by a continuous
`2`-cocycle which is constant on `fixingSubgroup L × fixingSubgroup L` for a finite Galois
extension `L ⊆ k̄` of `k`. -/
theorem exists_finiteGalois_Z2 {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)]
    {M : Type*} [AddCommGroup M] [DistribMulAction (G k) M] (x : H2 (G k) M) :
    ∃ (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) (c : Z2 (G k) M),
      H2π (G k) M c = x ∧ ∀ p : G k × G k, p.1 ∈ L.fixingSubgroup →
        p.2 ∈ L.fixingSubgroup → (c : G k × G k → M) p = (c : G k × G k → M) 1 := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B2 (G k) M).comap (Z2 (G k) M).subtype) x
  obtain ⟨L, hL⟩ :=
    exists_finiteGalois_le_ker_pair (k := k) (M := M) ((mem_Z2_iff _).mp c.2).2
  exact ⟨L, c, hc, fun p hp hq => hL p hp hq⟩

end

end Work.AbsoluteKummer.Factorisation
