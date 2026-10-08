import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.LayersAlt.Assembly

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **D2 (dichotomy of `ξ`-invariant layers).**  Let `P` be a Suzuki 2-group and let `ξ` act with
`|P| = q ^ 3` (`q = |Z(P)|`), order `q - 1` and *semiregularly* on `P \ {1}` (all the data of
`FpfXi ξ`).  Then the number of `ξ`-invariant layers `Z(P) ≤ M` of order `q ^ 2` is either `2`
(the two constituents of `P / Z(P)` are non-isomorphic `𝔽₂⟨ξ⟩`-modules) or `q + 1` (they are
isomorphic, and `P / Z(P)` is a `2`-dimensional `𝔽_q`-space on which `ξ` acts as a scalar).

Route (Peterfalvi II, Ch. V §2; Higman 1963).  `V := P / Z(P)` is an elementary abelian
`𝔽₂`-space of order `q ^ 2` (`Additive (P ⧸ Subgroup.center P)` with its
`AddCommGroup.zmodModule` structure; `P' ≤ Ω₁(P) ≤ Z(P)` is
`Work.Higman.commutator_mem_omega1` and `x ^ 2 ∈ Z(P)` is `Work.Higman.sq_mem_center`, both
sorry-free).  The automorphism `σ` induced by `ξ` has order `q - 1` and is semiregular on
`V \ {0}`; layers correspond to `σ`-invariant subspaces of `𝔽₂`-dimension `n` (`q = 2 ^ n`).
The minimal polynomial of `σ` divides `Φ_{q-1}` (Euler's totient part: a nontrivial power
`σ ^ k`, `k < q - 1`, has no non-zero fixed vector), and every irreducible factor of `Φ_{q-1}`
over `𝔽₂` has degree `n = ord_{q-1}(2)` (`Work.Higman.Q3.irred_natDegree_dvd_of_dvd_X_pow_sub_one`,
`…finrank_dvd_of_irreducible_pow_sub_one`).  Maschke (the order `q - 1` is odd) gives
`V = V₁ ⊕ V₂` with each `Vᵢ` of dimension exactly `n`; if `V₁ ≇ V₂` the only invariant
`n`-subspaces are `V₁`, `V₂`, while if `V₁ ≅ V₂` then `End_ξ(V₁) = 𝔽_q`, `V ≅ 𝔽_q²` with `ξ`
scalar, and the invariant lines number `q + 1`.  This is the same statement as
`Submission.Work.Higman.layers_card_dichotomy` (a backup copy). -/
theorem layers_card_dichotomy_alt {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) :
    Nat.card {M : Subgroup P // Work.Higman.IsXiLayer ξ M} = 2 ∨
      Nat.card {M : Subgroup P // Work.Higman.IsXiLayer ξ M} =
        Nat.card ↥(Subgroup.center P) + 1 :=
  Work.Higman.LayersAlt.layers_card_dichotomy_aux h hξ

end Work.Higman
