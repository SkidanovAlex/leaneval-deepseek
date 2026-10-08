import Submission.Work.ThmF.ChV3.Ctx

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The App. XI near-field input of Ch. V §3 step (2)

Peterfalvi II Ch. V §3 step (2) applies Appendix XI Prop. 1 (p. 284) to
`(C_G(P), C_H(P)) ∈ 𝓕` with kernel `N`, and then reads off only a *shadow* of the near-field `F`:
its characteristic `f = o(st)`, its size `|F| = f^m = |C_Q(P)| + 1`, and the preimage `R` of `F`
in `C_G(P)`, on which `C_Q(P) ≅ F^*` acts regularly.

Since the repository builds no near-field (and per the project lead, App. XI is not to be proved
yet), the shadow is recorded here as the named external input `NearFieldAppXIProp`, to be taken
as a hypothesis by the steps of §3 that consume (2).  It is stated exactly in the form step (2)
consumes; see `_design/chV3_steps.lean` step (2) and `NOTES_LEAD_probe1945.md`.

(This module cannot live in `Tools/External.lean`: it needs `ChV3.Ctx`, which imports
`Tools/External`.  It is the `NearFieldAppXIProp` of the lead's message of 2026-10-05 01:44.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- The kernel `N = D ⊓ C_G(C_Q(P)) ⊓ C_G(P)` of step (2). -/
abbrev Ker (H Q P : Subgroup G) (t : G) : Subgroup G :=
  twoPoint H t ⊓ Subgroup.centralizer ((CQ Q P : Subgroup G) : Set G) ⊓
    Subgroup.centralizer (P : Set G)

/-- **App. XI Prop. 1 (near-field shadow), external input.**

In the context `CtxF H Q t s r P` of §3, with `f = o(st)` prime, `(C_G(P), C_H(P)) ∈ 𝓕` and
kernel `N = D ⊓ C_G(C_Q(P)) ⊓ C_G(P)`, there are `m ≥ 1` and a subgroup `R` (the preimage of the
near-field `F`) with `N ≤ R`, `R` normalised by `C_G(P)`, `|R : N| = f^m`, `|C_Q(P)| = f^m - 1`
and `C_Q(P)` acting fixed-point-freely on `(R/N)^#`.

**Repair (recorded by the agent proving `Work.ThmF.Prove.step3`, Ch. V §3 step (3)).**  As first
written this `Prop` listed only `N ≤ R` and the elementwise clause
`y x y⁻¹ x⁻¹ ∈ N → y = 1`, with no assertion making `R/N` *be* a group carrying a `C_Q(P)`-action
— although the sentence above (and the source, where `C_G(P)/N ≅ (F ⋊ C_Q(P)) ⋊ Σ`) clearly does
make `N` normal in `C_G(P)`.  The missing clause `C_G(P) ≤ N_G(N)` is not derivable from the other
conjuncts together with `CtxF`: `C_G(P) ≤ N_G(D)` (`D = H ∩ Hᵗ`) forces `C_G(P) ≤ D`, while
`C_Q(P) = Q ⊓ C_G(P)` is non-trivial by `|C_Q(P)| + 1 = f^m ≥ 2` and meets `D` trivially.  Step
(3) needs to apply Burnside's theorem on Frobenius complements to the action of `C_Q(P)` on
`(R/N)^#` (to see that every odd `ℓ`-subgroup of `C_Q(P)` is cyclic, whence `dim C_M(P) = 1`), so
the clause is added here.  It is additive: every existing consumer of `NearFieldAppXIProp` uses it
only as a hypothesis, so all of them remain valid. -/
def NearFieldAppXIProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t s r : G) (P : Subgroup G),
    CtxF H Q t s r P →
    ∃ (m : ℕ) (R N : Subgroup G), N = Ker H Q P t ∧
      1 ≤ m ∧ (orderOf (s * t)).Prime ∧ N ≤ R ∧
      R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (N : Set G) ∧
      Nat.card R = Nat.card N * orderOf (s * t) ^ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      ∀ x ∈ R, x ∉ N → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ N → y = 1

/-- **App. XI Prop. 1 (2)b, the field/Galois shadow), external input.**

In the standing context of §3, in the case where `C_Q(P)` is **abelian** (`F` a field, by step
(5)), the near-field `F` of (2)b) is a finite field of cardinality `f^m = |C_Q(P)| + 1`
(`f = o(st)`), `C_Q(P) ≅ Fˣ`, and `Σ = C_W(P)` is identified with a group of automorphisms of
`F`, compatibly with the conjugation action on `C_Q(P)`: for `w ∈ Σ` and `y ∈ C_Q(P)`,
`e (w y w⁻¹) = act w (e y)`, and every `w ≠ 1` acts faithfully.  The fixed field of `w` is
`C_{C_Q(P)}(w)` together with one: `|C_F(w)| = |C_{C_Q(P)}(w)| + 1`.

This is the part of App. XI Prop. 1 that §3 uses in steps (6), (7) and (8) and that
`NearFieldAppXIProp` (the step (2) shadow) does not record.  Like `NearFieldAppXIProp` it is an
external input (App. XI is not built here) and it is *additive*: it only ever occurs as a
hypothesis.  The near-field case `F ≅ F_{9,2}` (where `C_Q(P)` is *not* abelian) is handled by
`AppXIProp2` instead. -/
def NearFieldFieldProp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ},
    CtxF H Q t s r P →
    1 ≤ m →
    Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m →
    IsMulCommutative ↥(CQ Q P) →
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (_ : CharP F (orderOf (s * t))) (_ : Fact (orderOf (s * t)).Prime)
      (act : ↥(Sig H t P) →* (F ≃+* F)),
      Nat.card F = orderOf (s * t) ^ m ∧
      Function.Injective act ∧
      (∀ w : ↥(Sig H t P), w ≠ 1 →
        Nat.card (Function.fixedPoints (act w)) =
          Nat.card ↥(CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G)) + 1)

end Work.ThmF.ChV3
