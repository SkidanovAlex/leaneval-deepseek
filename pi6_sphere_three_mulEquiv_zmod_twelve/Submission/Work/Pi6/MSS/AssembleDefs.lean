import Mathlib
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The interface of the assembly of the cohomological Serre spectral sequence

`Work.Pi6.MSS.Assembled 𝕜 W D` is the data produced by the assembly of the spectral sequence of a
filtered cochain complex with a product `W : CohFilt 𝕜` out of the page data `D : PagesData 𝕜 W`:

* a first-quadrant cohomological spectral sequence with a product `S : CohSS 𝕜` (the interface of
  `Submission/Work/Pi6/Interfaces.lean`), obtained by indexing the pages `pEraw 𝕜 W r s n` of
  `MSS/Pages.lean` by the bidegree `(s, q)` with total degree `n = s + q`;
* the identification `S.E r (s,q) ≅ pEraw 𝕜 W r s (s+q)` of the pages with the concrete ones;
* the compatibility of the products;
* the two convergence clauses (`IsSerreMSS`'s `conv_zero` and `conv_dim`, in terms of the finrank
  of the concrete pages / of the cohomology of `W.C`).

The bottom-row and column-0 maps `S.bot`/`S.col` are to be defined as the canonical geometric maps
(`S.bot r s` is the projection of the concrete page on the bottom row `q = 0`, i.e. the descents of
cycles modulo the growing denominators, and `S.col r q` is the canonical inclusion of the
subquotient `pEraw 𝕜 W (r+1) 0 q → pEraw 𝕜 W r 0 q`); this is needed by the edge computations and
must be recorded in the file as `bot`/`col` identification lemmas.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The assembly data of the spectral sequence of a filtered cochain complex with a product. -/
structure Assembled (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (D : PagesData 𝕜 W) where
  /-- the spectral sequence -/
  S : CohSS 𝕜
  /-- the identification of the pages with the concrete ones -/
  iso : ∀ (r s q : ℕ), 2 ≤ r → (S.E r ((s : ℤ), (q : ℤ)) ≅ pEraw 𝕜 W r s (s + q))
  /-- the compatibility of the products -/
  mul_compat : ∀ (r s q s' q' : ℕ) (hr : 2 ≤ r)
      (x : S.E r ((s : ℤ), (q : ℤ))) (y : S.E r ((s' : ℤ), (q' : ℤ))),
    (iso r (s + s') (q + q') (by omega)).hom
        (S.mul r ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
          (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y)
      = (pEcast 𝕜 W r (rfl : s + s' = s + s') (by omega)).hom
          (D.mul r s (s + q) s' (s' + q') ((iso r s q hr).hom x) ((iso r s' q' hr).hom y))
  /-- vanishing in total degree `n` on the page `E_{n+2}` -/
  zero : ∀ (n s : ℕ), s ≤ n → Subsingleton (pEraw 𝕜 W (n + 2) s n) →
      IsZero (S.E (n + 2) ((s : ℤ), ((n - s : ℕ) : ℤ)))
  /-- the dimension identity in total degree `n` -/
  finrank_sum : ∀ n : ℕ,
      (∑ s ∈ Finset.range (n + 1),
          Module.finrank 𝕜 (S.E (n + 2) ((s : ℤ), ((n - s : ℕ) : ℤ))))
        = ∑ s ∈ Finset.range (n + 1), Module.finrank 𝕜 (pEraw 𝕜 W (n + 2) s n)

end

end Work.Pi6.MSS
