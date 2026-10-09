import Submission.NK.LocalCFT.Brauer.Basic
import Submission.NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `NK.BrauerHasse.LocalH2Input` from the local non-vanishing

The sibling area `Submission/Work/BrauerHasse/` consumes the local Brauer input in the transported
form

`NK.BrauerHasse.LocalH2Input p K K' κ κ'`:

for every closed subgroup `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` there is a non-zero class in
`H²(H, ℤ/p)`.

This file derives it from

* the **local** non-vanishing `NK.LocalCFT.LocalH2Nonvanishing p κ κ'`
  (equivalently `NK.LocalCFT.SurvivingH2Class p κ κ'`, by
  `NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving`), and
* the **openness input** `∀ U ≤ H, U.FiniteIndex → IsOpen U` for `H ≤ Gal(K'/K)` and for
  `Gal(κ'/κ)`: every finite-index subgroup is open.  For `H ≅ G_κ` with `κ` a `p`-adic field this
  is the classical Nikolov–Segal theorem (a finitely generated pro-`p` group is `p`-adic analytic,
  so all its finite-index subgroups are open); the workspace's
  `Submission/Work/LocalInputs/` isolates the index-`p` case as `open_of_index_prime`.

The transport itself (the isomorphism of the two Galois-colimit realisations of `H²(·, ℤ/p)`
induced by `H ≃* Gal(κ'/κ)`) is
`NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv`.
-/

open scoped Classical

namespace NK.LocalCFT

universe u

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
  [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The sibling area's local Brauer input, from the local non-vanishing plus openness of
finite-index subgroups.** -/
theorem localH2Input_of_nonvanishing
    (hopenH : ∀ H : Subgroup Gal(K'/K), IsClosed (H : Set Gal(K'/K)) →
      ∀ U : Subgroup ↥H, U.FiniteIndex → IsOpen (U : Set ↥H))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (h : NK.LocalCFT.LocalH2Nonvanishing p κ κ') :
    NK.BrauerHasse.LocalH2Input p K K' κ κ' := by
  intro H hH hκ
  obtain ⟨e⟩ := hκ
  exact NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv H hH e
    (hopenH H hH) hopenκ h

end NK.LocalCFT
