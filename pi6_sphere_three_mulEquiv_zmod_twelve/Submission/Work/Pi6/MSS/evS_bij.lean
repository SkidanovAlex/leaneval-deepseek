import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.evSaux
import Submission.Work.Pi6.MSS.evZsurj
import Submission.Work.Pi6.MSS.evZkerle_proof
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The first page of the cohomological Serre spectral sequence over a field

`Work.Pi6.MSS.evS : E_1^{s,n}(p;𝕜) ⟶ Hom_𝕜(H_n(gr_s C_*(E)),𝕜)` is the map that evaluates a
`1`-cocycle of the Serre cochain filtration of `p : E → B` on the cycles of the `s`-th graded piece
of the Serre *chain* filtration.  Over a field it is an isomorphism: `E_1^{s,n}` is the cohomology
of the dual of the graded piece complex, and `Hom_𝕜(-,𝕜)` is exact.

The proof splits the two halves:

* `Work.Pi6.MSS.evZsurj` — surjectivity of the comparison map `evZ` on `Z_1^s`, which is equivalent
  to surjectivity of `evS` since `evS` is the descent of `evZ` to `E_1^s`;
* `Work.Pi6.MSS.evZkerle` — the kernel of `evZ` is contained in the denominator `pDen` of `E_1^s`
  (the reverse inclusion is `Work.Pi6.MSS.evZ_eq_zero_of_mem_pDen`), which gives injectivity.

Both halves are assembled here through `Submodule.ker_liftQ_eq_bot` and `Submodule.range_liftQ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

theorem evS_bij (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n) :
    Function.Bijective (Work.Pi6.MSS.evS 𝕜 p s n hann) := by
  have hker : LinearMap.ker (evZ 𝕜 p s n hann) ≤
      (pDen 𝕜 (Wc 𝕜 p) 1 s n).comap (pZ 𝕜 (Wc 𝕜 p) 1 s n).subtype :=
    evZkerle_proof 𝕜 E B p s n hann
  have hsurj : Function.Surjective (evZ 𝕜 p s n hann) := evZsurj 𝕜 E B p s n hann
  constructor
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
    exact hker
  · rw [← LinearMap.range_eq_top]
    show (Submodule.liftQ ((pDen 𝕜 (Wc 𝕜 p) 1 s n).comap
        (pZ 𝕜 (Wc 𝕜 p) 1 s n).subtype) (evZ 𝕜 p s n hann) _).range = ⊤
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.mpr hsurj

end

end Work.Pi6.MSS
