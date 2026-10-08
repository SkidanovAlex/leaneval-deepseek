import Submission.Work.Hering.Config

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The hard core of Hering's theorem (Peterfalvi I Ch. IV §3–§4)

`Work.Hering.no_reduced_config` (the target of this area's hard core) says that no finite group
carries the reduced configuration `ReducedConfig` of Peterfalvi I §2. Its proof splits, exactly as
in the source, into

* the **abelian case** `Work.Hering.HardCore.abelian_case` (§3 Prop. 2, p. 193): if `C = C_G(V)`
  is abelian there is an involution of `G` outside `C`, contradicting `Inv(G) = V#`; this case is
  elementary and is proved in `Submission/Work/Hering/HardCore/abelian_case.lean`;
* the **non-abelian case** `NonAbelianCaseProp` below (§4, pp. 197–198): `C = C_G(V)` cannot be
  non-abelian.

The non-abelian case is the only place in Chapter IV where a heavy external input is needed:
G. Higman's classification of Suzuki 2-groups (Illinois J. Math. 7 (1963) 79–96) together with
Peterfalvi I App. VIII (automorphism groups of the Suzuki 2-groups `A(n,φ)`, `B(n,1)`, `C(n,ε)`,
pp. 221–229) and App. IX (the irreducible `F₂`-representations of `GL(3,F₂)` have degrees
`1,3,3,8`, pp. 230–233). The version of Higman's classification available in this workspace as
`Submission.Blueprint.HigmanProp` covers the order-`q²` types `A(n,θ)` and the general facts
(`Z(P) = Ω₁(P) = P'`, `x² ∈ Z(P)`, `|P| ∈ {q²,q³}`) but *not* the order-`q³` types `B`, `C`, `D`
(the handoff `Submission/Blueprint/HANDOFF.md` records this gap). `NonAbelianCaseProp` is
therefore left as an explicitly named hypothesis; it is the single missing ingredient of
`HeringProp` in this development.
-/

set_option autoImplicit false

namespace Work.Hering

/-- A **Suzuki 2-group** in Higman's sense: a non-abelian 2-group with more than one involution
admitting a cyclic group of automorphisms transitive on its involutions. This is a local copy of
`Submission.Blueprint.IsSuzukiTwoGroup` (kept here so that this module, and the lemmas about it,
do not need the blueprint's heavy imports); `Work.Hering.Main` records that the two definitions
are equal. -/
def IsSuzukiTwoGroup (P : Type) [Group P] [Finite P] : Prop :=
  IsPGroup 2 P ∧ (∃ x y : P, x * y ≠ y * x) ∧
    (∃ x y : P, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y) ∧
    ∃ ξ : MulAut P, ∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y

variable {G : Type*} [Group G]

/-- **The non-abelian case of the hard core** (Peterfalvi I Ch. IV §4, pp. 197–198): in the
reduced configuration `V ⊴ G` elementary abelian of order `8`, `C = C_G(V)` a 2-group with
`Inv(C) = V#`, `G/C ≅ Aut(V)`, the centraliser `C` cannot be non-abelian.

Proof route (source): `C` is a Suzuki 2-group with `Ω₁(C) = Z(C) = V`; Higman's classification
gives `|C| ∈ {q²,q³}`, `q = 8`. Both cases are excluded: the order-`q²` case is ruled out because
`Aut(A(3,φ))` is solvable for `φ⁴ ≠ 1` (App. VIII Prop. 1) while `Aut(C)` is not solvable
(`G/Z(C) ≅ G/C_G(C)` has the non-solvable quotient `G/C ≅ GL(3,2)`); in the order-`q³` case `C/V`
is a 6-dimensional `F₂[GL(3,2)]`-module with no 1-dimensional submodule, App. IX produces a
3-dimensional simple submodule `C₁/V` with `C₁` of type `A(3,φ)`, and the same solvability
argument with App. VIII Props. 3 and 4 (types `B(3,1,ε)`, `C(3,ε)`) gives the contradiction. -/
def NonAbelianCaseProp : Prop :=
  ∀ (V C : Subgroup G) (hV : V.Normal) (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) (hAut : ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x), False

end Work.Hering
