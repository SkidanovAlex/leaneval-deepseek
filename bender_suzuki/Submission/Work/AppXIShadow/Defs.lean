import Mathlib
import Submission.Work.ThmF.ChV3.NearField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.Defs` — App. XI Prop. 1, the "shadow" of the near-field

This area (BS design pass 17, Brief 3) builds the group-theoretic content of

* Peterfalvi I **Appendix III (2)** (the structure of a group of 2-rank 1 with a maximal
  proper Bender subgroup, in the *non-faithful* form needed here), and
* Peterfalvi II **Ch. V §3 step (2)** = **Appendix XI Prop. 1**, i.e. the existence of the
  "near-field shadow" `NearFieldAppXIPropPlus` in the standing context `CtxF` of Ch. V §3.

The statements are copied verbatim from the design file `_design17/ThmF17_AppXI.lean`
(namespace `Design17.XI`), relocated to `Work.AppXIShadow`.

## Main definitions

* `Work.AppXIShadow.fixP H P` — the fixed points of `P` on `Ω = G ⧸ H`
  (equal to `Submission.Blueprint.fixedPts H P`).
* `Work.AppXIShadow.NearFieldAppXIPropPlus` — the step-(2) shadow plus the `[R,R] ≤ N` clause
  that App. III (2) actually yields (`NearFieldAppXIProp` of `ThmF/ChV3/NearField.lean` is the
  same statement without that clause; `NearFieldAppXIPropPlus.toShadow` recovers it).

## Main result

`Work.AppXIShadow.nearFieldAppXIPropPlus_of` (in `Work.AppXIShadow.Main`) proves
`NearFieldAppXIPropPlus` from `hFT hBrSz hC4 hTh`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3

variable {G : Type} [Group G]

/-- The fixed points of `P` on `Ω = G ⧸ H`.  (Verbatim from `Design17.XI.fixP`; propositionally
the same as `Submission.Blueprint.fixedPts H P`.) -/
def fixP (H P : Subgroup G) : Set (G ⧸ H) := {ω | ∀ x ∈ P, x • ω = ω}

@[simp]
theorem mem_fixP {H P : Subgroup G} {ω : G ⧸ H} :
    ω ∈ fixP H P ↔ ∀ x ∈ P, x • ω = ω := Iff.rfl

theorem fixP_eq_fixedPts (H P : Subgroup G) : fixP H P = Submission.Blueprint.fixedPts H P := rfl

/-- **The step-(2) shadow of App. XI Prop. 1, plus the `[R,R] ≤ N` clause of App. III (2).**

In the standing context `CtxF H Q t s r P` of Ch. V §3, with `f = o(st)` prime,
`(C_G(P), C_H(P)) ∈ 𝓕` and kernel `N = Ker H Q P t`, there are `m ≥ 1` and a subgroup `R`
(the preimage of the near-field `F`) with `N ≤ R`, `R ≤ C_G(P)`, `C_G(P) ≤ N_G(R)`,
`C_G(P) ≤ N_G(N)`, `|R : N| = f^m`, `|C_Q(P)| = f^m - 1`, `C_Q(P)` acting fixed-point-freely on
`(R/N)^#`, and `[R,R] ≤ N`.

(Verbatim from `Design17.XI.NearFieldAppXIPropPlus`.) -/
def NearFieldAppXIPropPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t s r : G) (P : Subgroup G),
    CtxF H Q t s r P →
    ∃ (m : ℕ) (R N : Subgroup G), N = Ker H Q P t ∧
      1 ≤ m ∧ (orderOf (s * t)).Prime ∧ N ≤ R ∧
      R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (N : Set G) ∧
      Nat.card R = Nat.card N * orderOf (s * t) ^ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      (∀ x ∈ R, x ∉ N → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ N → y = 1) ∧
      (∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N)

/-- Forgetting the `[R,R] ≤ N` clause gives the step-(2) shadow `NearFieldAppXIProp`.
(Verbatim from `Design17.XI.NearFieldAppXIPropPlus.toShadow`.) -/
theorem NearFieldAppXIPropPlus.toShadow (h : NearFieldAppXIPropPlus) : NearFieldAppXIProp := by
  intro G _ _ H Q t s r P c
  obtain ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h G H Q t s r P c
  exact ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Work.AppXIShadow
