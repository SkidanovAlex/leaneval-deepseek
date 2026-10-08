import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.even_card_centralizer_of_fixes_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Supporting lemmas for `even_card_centralizer_fixes_three_aux`

`Situation G` gives a four-group, so by Theorem A (`hA`) `G` acts `2`-transitively on
`Ω = G ⧸ H`; hence every point stabiliser — in particular every conjugate `M` of `H` — is a
**maximal** subgroup of `G` (`isCoatom_stabilizer_of_twoTransitive`).  Together with Theorem C
(`hC`, `involution_centralizes_of_mem_normalizer`) this reduces the goal to: the normaliser
`N_M(X)` contains an involution.

## Why the target is not provable from the stated hypotheses

Given `hC`, the target is *equivalent* to "there is an involution `u ∈ M` normalising `X`"
(`X ≤ M ⊓ M₁` for a second fixed point `M₁ ≠ M`, so Theorem C sends every involution of
`N_M(X)` into `C_M(X)`).  That equivalence is already proved, hole-free, in this area as
`Work.ThreePoints.prop1a_of_involution_normalizing`
(`Submission/Work/ThreePoints/prop1a_even_card_centralizer.lean`).

The only available way to produce that involution is the source's Ch. I §4 Prop. 2 applied
inside `F₁ = C_G(O^p(X))·P` (Peterfalvi I Ch. II §4, p. 168, proof of Prop. 1(a)).  Its
Ch. I §3 Prop. 1, *Case 2* (Astérisque 142–143, p. 154; `REFS/pdf/ast_141.pdf`) invokes the
Brauer–Suzuki theorem verbatim ("`M/O_{2'}(M)` a une seule involution"), and `BrauerSuzukiProp`
is neither among `hFT, hC, hA, hS` nor proved in the workspace.  Accordingly the area's own
formalisation of that ingredient
(`Submission/Work/ThreePoints/even_card_normalizer_of_maximal_p_subgroup.lean`) carries the
hypothesis `(hBrSz : Submission.Blueprint.BrauerSuzukiProp)` — exactly the hypothesis the
requested statement omits — and its `2`-rank-`1` sub-case is recorded in
`Submission/Work/ThreePoints/twoTransitive_stabilizer_even.lean` as being at least as strong as
that black box.  The note `Submission/Work/ThreePoints/NOTES_Prop1a_roadmap.md` reaches the same
conclusion and proposes adding `hBrSz` to the statement.

## Status

This file's statement is exactly `Work.ThreePoints.even_card_centralizer_of_fixes_three`, which is
now **proved** by the source's strong induction on `|X|`
(`Work.ThreePoints.prop1a_aux`, whose step is `prop1a_descent`).  The older note below explains why
the naive route through Ch. I §3 Prop. 1, Case 2 ("`M/O_{2'}(M)` a une seule involution") needs
Brauer–Suzuki; the descent instead isolates that case in Ch. I §4 Prop. 2, which is available from
the `𝓡_p`-dichotomy (`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_brsz`) together
with the pass-15 chain for Ch. I §4 Prop. 1(b) (`Work.ThreePoints.S4Prop2.no_two_fixed_pts`).  So
no extra hypothesis is needed after all; the theorem below is a re-export.
-/

/-- A proper subgroup has a nontrivial quotient `G ⧸ H`. -/
theorem nontrivial_quotient_of_ne_top {H : Subgroup G} (hH : H ≠ ⊤) : Nontrivial (G ⧸ H) := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    push_neg at h
    exact hH ((Subgroup.eq_top_iff' H).mpr h)
  refine ⟨((1 : G) : G ⧸ H), ((g : G) : G ⧸ H), fun hcon => hg ?_⟩
  have hmem : (1 : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hcon
  simpa using hmem

/-- **A `2`-transitive action has maximal point stabilisers** (Mathlib: a `2`-transitive action
is preprimitive, and in a preprimitive action point stabilisers are coatoms). -/
theorem isCoatom_stabilizer_of_twoTransitive {Ω : Type} [MulAction G Ω] [Nontrivial Ω]
    (h2 : MulAction.IsMultiplyPretransitive G Ω 2) (ω : Ω) :
    IsCoatom (MulAction.stabilizer G ω) := by
  haveI : MulAction.IsPreprimitive G Ω := MulAction.isPreprimitive_of_is_two_pretransitive h2
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G ω

/-- **Theorem C** (Peterfalvi I Ch. II, p. 163) in the form used here: if `M` is strongly
embedded, `M₁ ≠ M` is a conjugate of `M`, `X ≤ M ⊓ M₁`, and the involution `u ∈ M` normalises
`X`, then `u` centralises `X`. -/
theorem involution_centralizes_of_mem_normalizer (hC : ThmCProp) (hS : Situation G)
    {M : Subgroup G} (hM : IsStronglyEmbedded M) {M₁ : Subgroup G}
    (hM₁ : ∃ g : G, M₁ = conj g M) (hne : M ≠ M₁)
    {X : Subgroup G} (hXM : X ≤ M) (hXM₁ : X ≤ M₁)
    {u : G} (hu : u ∈ M) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huN : u ∈ Subgroup.normalizer (X : Set G)) :
    ∀ x ∈ X, u * x = x * u := by
  obtain ⟨g, hg⟩ := hM₁
  have hgM : g ∉ M := by
    intro hgin
    exact hne (hg.trans (conj_eq_self_of_mem hgin)).symm
  have huord : orderOf u = 2 := by
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hu2)
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf u) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  exact hC G hS M hM g hgM u ⟨hu, huord⟩ X
    (le_inf hXM (hg ▸ hXM₁)) huN

/-- Peterfalvi I Ch. II §4 Prop. 1(a) (p.168): under (B0)–(B2), if a subgroup `X ≤ G` fixes at
least three points of `Ω = G ⧸ H` and `M = conj g H ∈ Ω` is one of them (`X ≤ M`), then the
centraliser `C_M(X)` of `X` in `M` has even order.  Proved as
`Work.ThreePoints.even_card_centralizer_of_fixes_three`. -/
theorem even_card_centralizer_fixes_three_aux {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  even_card_centralizer_of_fixes_three hFT hC hA hS hH hX3 hM hXM

end Work.ThreePoints
