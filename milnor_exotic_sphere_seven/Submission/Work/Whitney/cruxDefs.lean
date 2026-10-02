import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.eSymDef
import Submission.Work.Thom.Cohomology
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# Small vocabulary for the crux of the Whitney sum formula

`Work.Whitney.skipIdx hN k : Fin (N-1) → Fin N` is the inclusion of `Fin (N-1)` into `Fin N` which
skips `k`.  It is the index embedding along which the family of the `N-1` summands *other* than the
`k`-th is indexed, in the "summand section" step of the crux argument (see `PLAN_crux_v2.md`).
-/

namespace Work.Whitney

/-! ## Note for the "summand section" step (`Work.Whitney.cruxSummandSection`)

The third conjunct of `cruxSummandSection` (for an **arbitrary** splitting `e : π^*W ≅ ℓ ⊕ Q`) is
provable as follows, and is *not* a strengthening of the crux:

* pulling `e` back along the section `s_k` gives `e' : W ≅ s_k^*ℓ ⊕ s_k^*Q`, and the *image* of the
  canonical embedding `s_k^*ℓ ↪ W` (the pullback of ℓ ↪ π^*W) is the `k`-th summand `M k ⊂ W`
  (fibrewise it is `ℓ_{s_k(x)} = ℂ·(the line s_k x) = (M k)_x`);
* so `s_k^*Q` is a complement of the *fixed* subbundle `M k` of `W`.  For a fixed `A ⊂ W` with two
  complements, `W = A ⊕ C = A ⊕ C'`, the projection `W → C` (kernel `A`) induces
  `W/A ≅ C`, so **all complements of `A` are isomorphic to `W/A`** — in particular
  `s_k^*Q ≅ W/(M k)`, independently of `e`;
* `W/(M k) ≅ lineSumCore (N-1) (M ∘ skipIdx k)` (split off the `k`-th summand of the iterated sum),
  whose top Chern class is the product `∏_{j≠k} t_j` (`Work.Gen.lineSumCore_top_chern`), and
  `∏_{j≠k} t_j = eSym (N-1) (M ∘ skipIdx k) (N-1)`.

So the clause only needs: "complements of a subbundle are isomorphic to the quotient" (a linear-algebra
fact about gluing data), the reindexing `W/(M k) ≅ lineSumCore (N-1) (M ∘ skipIdx k)`, and the top
class of a sum of line bundles. -/

/-- The inclusion `Fin (N-1) → Fin N` skipping `k` (for `1 ≤ N`). -/
def skipIdx {N : ℕ} (hN : 1 ≤ N) (k : Fin N) : Fin (N - 1) → Fin N :=
  fun i => (Fin.succAbove (n := N - 1) (k.cast (by omega)) i).cast (by omega)

open Work.TangentClasses Work.Thom in
/-- `δ ⌣ eSym N M (N-1)` (the right-hand side of the delta-form), with the degree cast collapsed. -/
noncomputable def deltaCup {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] (N : ℕ)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B) :
    Coh ℤ (2 * (N - 1)) B :=
  cohTransport (by omega : 0 + 2 * (N - 1) = 2 * (N - 1))
    (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 (2 * (N - 1)) δ (Work.Gen.eSym N M (N - 1)))

open Work.TangentClasses Work.Thom in
/-- The `j`-th Leray–Hirsch coefficient of `ψ` in the delta-form:
`(-1)^{j+1} δ ⌣ eSym N M (N-2-j)`. -/
noncomputable def psiCoeff {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {N : ℕ}
    (hN : 2 ≤ N)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B) :
    (j : {j : Fin N // (j : ℕ) ≤ N - 2}) → Coh ℤ (2 * (N - 2 - (j : ℕ))) B :=
  fun j => cohTransport (by omega : 0 + 2 * (N - 2 - (j : ℕ)) = 2 * (N - 2 - (j : ℕ)))
    (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 (2 * (N - 2 - (j : ℕ)))
      (((-1 : ℤ) ^ ((j : ℕ) + 1)) • δ) (Work.Gen.eSym N M (N - 2 - (j : ℕ))))

end Work.Whitney
