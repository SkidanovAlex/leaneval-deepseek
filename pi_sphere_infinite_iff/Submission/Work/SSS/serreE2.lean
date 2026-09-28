import Mathlib
import Submission.Work.SSS.serreE1
import Submission.Work.SSS.serreE2OfE1

/-!
# The E² page of the Serre spectral sequence

`Work.SSS.serreE2` is the third input of Serre's three-for-two theorem for a Serre fibration over a
simply connected base: the second page of the Serre filtration of `C_*(E)` is, in the Serre class of
finitely generated abelian groups, `H_s(B; H_t F)`, `F = p⁻¹(p e₀)` the fibre of `p` over `p e₀`.

It is assembled from the two (independent) inputs proved in the sibling files:

* `Work.SSS.serreE1` — the first page: the row complex of the Serre filtration at fibre degree `t`
  is isomorphic, as a chain complex, to the normalized singular chains of `B` tensored with
  `H_t(F)`; hence its homology (the E² page) is `H_s(N_* B ⊗ H_t F)`;
* `Work.SSS.serreE2OfE1` — the passage from that chain-level statement to the three Serre-class
  statements of `SerreE2Statement`, using the universal coefficient theorem
  (`Work.SSS.tensorHomology`), the fact that `H_0(F)` is a free module of positive rank, and the
  path connectedness of `B` furnished by `SimplyConn`.
-/

namespace Work.SSS

/-- **The E² page of the Serre spectral sequence** of a Serre fibration `p : E → B` over a simply
connected base: the Serre filtration of `C_*(E)` (by the skeleta of `Sing B`) has E² page
`H_s(B; H_t F)`, `F = p⁻¹(p e₀)`, read in the Serre class of finitely generated abelian groups. -/
theorem serreE2 : Work.SSS.SerreE2Statement :=
  serreE2OfE1 serreE1

end Work.SSS
