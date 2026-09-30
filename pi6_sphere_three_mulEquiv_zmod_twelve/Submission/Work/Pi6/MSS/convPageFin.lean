import Mathlib
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.Pages
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Finiteness of the pages is monotone in `r`

The pages `E_r^{s,n} = Z_r^s/(Z_{r-1}^{s+1} + B_r^s)` of the spectral sequence of a filtered
cochain complex with a product (`Work.Pi6.MSS.pEraw`) decrease in `r`: the projection
`ker d_r → E_{r+1}` (`Work.Pi6.MSS.pd_proj`) is surjective (`Work.Pi6.MSS.pd_proj_surj`), and
`ker d_r` is a submodule of `E_r^{s,n}`.  Hence `E_{r+1}^{s,n}` is a quotient of a submodule of
`E_r^{s,n}`, and `Module.Finite` propagates upwards in `r`.  This is the elementary step used by
`Work.Pi6.MSS.convFin` to transfer the finite-dimensionality of the `E_2` page (Künneth, `e2Add`)
to the `E_{r}` pages with `r ≥ 2`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

noncomputable section

/-- One step: `E_{r+1}^{s,n}` is a quotient of the submodule `ker d_r ≤ E_r^{s,n}` of `E_r^{s,n}`
(the projection `pd_proj` is surjective for `2 ≤ r`), so finiteness of `E_r^{s,n}` implies
finiteness of `E_{r+1}^{s,n}`. -/
theorem pEraw_fin_succ (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (r s n : ℕ)
    (hr : 2 ≤ r) (hfin : Module.Finite 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W r s n)) :
    Module.Finite 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W (r+1) s n) := by
  have hker : Module.Finite 𝕜 ↥(LinearMap.ker (Work.Pi6.MSS.pD 𝕜 W r s n).hom) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Module.Finite.of_surjective (Work.Pi6.MSS.pd_proj 𝕜 W r s n)
    (Work.Pi6.MSS.pd_proj_surj 𝕜 W r s n hr)

/-- **Finiteness of the pages is monotone in the page index.**  If the page `E_r^{s,n}` is a
finite-dimensional (finitely generated) `𝕜`-module and `2 ≤ r ≤ r'`, then so is `E_{r'}^{s,n}`. -/
theorem convPageFin (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (r r' s n : ℕ)
    (hr : 2 ≤ r) (hrr : r ≤ r')
    (h : Module.Finite 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W r s n)) :
    Module.Finite 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W r' s n) := by
  have hiter : ∀ k : ℕ, Module.Finite 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W (r + k) s n) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => exact pEraw_fin_succ 𝕜 W (r + k) s n (by omega) ih
  have hlast := hiter (r' - r)
  rwa [Nat.add_sub_cancel' hrr] at hlast

end

end Work.Pi6.MSS
